/******************************************************************************
 * Top contributors (to current version):
 *   Daisuke Ishii
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriter implementation for the fp-to-real-related operators.
 */

#include "theory/arith/arith_rewriter.h"

#include <optional>
#include <set>
#include <sstream>
#include <stack>
#include <vector>

#include "expr/algorithm/flatten.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/operator_elim.h"
#include "theory/arith/rewriter/addition.h"
#include "theory/arith/rewriter/node_utils.h"
#include "theory/arith/rewriter/ordering.h"
#include "theory/arith/rewriter/rewrite_atom.h"
#include "theory/theory.h"
#include "util/floatingpoint.h"
#include "util/real_floatingpoint.h"
#include "util/real_floatingpoint.h"

using namespace cvc5::internal::kind;

namespace RFP = cvc5::internal::RealFloatingPoint;

namespace cvc5::internal {
namespace theory {
namespace arith {

RewriteResponse ArithRewriter::postRewriteRfpToFP(TNode t)
{
  Assert(t.getKind() == kind::RFP_TO_FP);
  uint32_t eb = t.getOperator().getConst<RfpToFP>().getSize().exponentWidth();
  uint32_t sb = t.getOperator().getConst<RfpToFP>().getSize().significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.to_fp is only supported for real values
    Assert(t[0].getType().isReal());
    Rational v = t[0].getConst<Rational>();
    Node ret = nm->mkConst(RFP::convertToFP(eb,sb, v));
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpToReal(TNode t)
{
  Assert(t.getKind() == kind::RFP_TO_REAL);
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.to_real is only supported for floating-point numbers
    Assert(t[0].getType().isFloatingPoint());
    FloatingPoint v = t[0].getConst<FloatingPoint>();
    Node ret = nm->mkConstReal(RFP::convertFPToReal(v));
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpRound(TNode t)
{
  Assert(t.getKind() == kind::RFP_ROUND);
  FloatingPointSize sz = t.getOperator().getConst<RfpRound>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst())
  {
    // rfp.round is only supported for integer rms and real values
    Assert(t[0].getType().isInteger());
    Assert(t[1].getType().isReal());
    Integer rm = t[0].getConst<Rational>().getNumerator();
    Rational v = t[1].getConst<Rational>();
    Rational rounded = RealFloatingPoint::round(eb,sb, rm.getUnsignedInt(), v);
    Node ret = nm->mkConstReal(rounded);
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpAdd(TNode t)
{
  Assert(t.getKind() == kind::RFP_ADD);
  FloatingPointSize sz = t.getOperator().getConst<RfpRound>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst() && t[2].isConst())
  {
    // rfp.round is only supported for integer rms and real values
    Assert(t[0].getType().isInteger());
    Assert(t[1].getType().isReal());
    Assert(t[2].getType().isReal());
    uint8_t rm = t[0].getConst<Rational>().getNumerator().getUnsignedInt();
    Rational x = t[1].getConst<Rational>();
    Rational y = t[2].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb, sb, x) && !RFP::isZero(eb, sb, x) &&
        RFP::isFinite(eb, sb, y) && !RFP::isZero(eb, sb, y) &&
        // TODO RFP::noOverflow(eb, sb, rm, x + y)
        RFP::isFinite(eb, sb, x + y)
        )
    {
      Node op = nm->mkConst(RfpRound(eb, sb));
      Node sum = nm->mkNode(kind::ADD, t[1], t[2]);
      Node ret = nm->mkNode(RFP_ROUND, op, t[0], sum);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    // zero cases
    if (RFP::isZero(eb, sb, x) && RFP::isFinite(eb, sb, y) && !RFP::isZero(eb, sb, y))
    {
      return RewriteResponse(REWRITE_DONE, t[2]);
    }
    if (RFP::isFinite(eb, sb, x) && !RFP::isZero(eb, sb, x) && RFP::isZero(eb, sb, y))
    {
      return RewriteResponse(REWRITE_DONE, t[1]);
    }
    if (RFP::isZero(eb, sb, x) && RFP::isZero(eb, sb, y) && x == y)
    {
      return RewriteResponse(REWRITE_DONE, t[1]);
    }
    if (x == RFP::plusZero(eb,sb) && y == RFP::minusZero(eb,sb))
    {
      if (rm == IntRoundingMode::TN)
        return RewriteResponse(REWRITE_DONE, t[2]);
      else
        return RewriteResponse(REWRITE_DONE, t[1]);
    }
    if (x == RFP::minusZero(eb,sb) && y == RFP::plusZero(eb,sb))
    {
      if (rm == IntRoundingMode::TN)
        return RewriteResponse(REWRITE_DONE, t[1]);
      else
        return RewriteResponse(REWRITE_DONE, t[2]);
    }

    // special cases
    if (x == RFP::notANumber(eb,sb) && y == RFP::notANumber(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isInfinite(eb,sb, y))
    {
      if (y == RFP::minusInfinity(eb,sb))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
    }
    if (RFP::isInfinite(eb,sb, x) && RFP::isFinite(eb,sb, y))
    {
      if (x == RFP::minusInfinity(eb,sb))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
    }
    if (RFP::isInfinite(eb,sb, x) && RFP::isInfinite(eb,sb, y))
    {
      if (x == RFP::minusInfinity(eb,sb) && y == RFP::minusInfinity(eb,sb))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      else if (x == RFP::plusInfinity(eb,sb) && y == RFP::plusInfinity(eb,sb))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && !RFP::isFinite(eb,sb, x + y))
    {
      if (x + y < 0)
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
    }
  }

  return RewriteResponse(REWRITE_DONE, t);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
