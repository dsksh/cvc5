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

#include <limits>

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

RewriteResponse ArithRewriter::postRewriteRfpIsNormal(TNode t)
{
  Assert(t.getKind() == kind::RFP_IS_NORMAL);
  FloatingPointSize sz = t.getOperator().getConst<RfpIsNormal>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.isNormal is only supported for real values
    Assert(t[0].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Node ret = nm->mkConst(RFP::isNormal(eb,sb, x));
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpIsSubnormal(TNode t)
{
  Assert(t.getKind() == kind::RFP_IS_SUBNORMAL);
  FloatingPointSize sz = t.getOperator().getConst<RfpIsSubnormal>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.isSubnormal is only supported for real values
    Assert(t[0].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Node ret = nm->mkConst(RFP::isSubnormal(eb,sb, x));
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpIsZero(TNode t)
{
  Assert(t.getKind() == kind::RFP_IS_ZERO);
  FloatingPointSize sz = t.getOperator().getConst<RfpIsZero>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.isZero is only supported for real values
    Assert(t[0].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Node ret = nm->mkConst(RFP::isZero(eb,sb, x));
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpIsInf(TNode t)
{
  Assert(t.getKind() == kind::RFP_IS_INF);
  FloatingPointSize sz = t.getOperator().getConst<RfpIsInf>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.isInfiniteis only supported for real values
    Assert(t[0].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Node ret = nm->mkConst(RFP::isInfinite(eb,sb, x));
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpIsNan(TNode t)
{
  Assert(t.getKind() == kind::RFP_IS_NAN);
  FloatingPointSize sz = t.getOperator().getConst<RfpIsNan>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.isNaN is only supported for real values
    Assert(t[0].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Node ret = nm->mkConst(x == RFP::notANumber(eb,sb));
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpIsNeg(TNode t)
{
  Assert(t.getKind() == kind::RFP_IS_NEG);
  FloatingPointSize sz = t.getOperator().getConst<RfpIsNeg>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.isNegative is only supported for real values
    Assert(t[0].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Node ret = nm->mkConst(x < 0);
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpIsPos(TNode t)
{
  Assert(t.getKind() == kind::RFP_IS_POS);
  FloatingPointSize sz = t.getOperator().getConst<RfpIsPos>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.isPositive is only supported for real values
    Assert(t[0].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Node ret = nm->mkConst(x >= 0);
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpToRfpFromRfp(TNode t)
{
  Assert(t.getKind() == kind::RFP_TO_RFP_FROM_RFP);
  FloatingPointSize srcSz = t.getOperator().getConst<RfpToRfpFromRfp>().getSrcSize();
  FloatingPointSize sz = t.getOperator().getConst<RfpToRfpFromRfp>().getSize();
  uint32_t eb0 = srcSz.exponentWidth();
  uint32_t sb0 = srcSz.significandWidth();
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
    Rational x = t[1].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb0,sb0, x) && !RFP::isZero(eb0,sb0, x))
    {
      Rational rounded = RFP::round(eb,sb, rm.getUnsignedInt(), x);
      Node ret = nm->mkConstReal(rounded);
      return RewriteResponse(REWRITE_DONE, ret);
    }

    // zero cases
    if (x == RFP::minusZero(eb0,sb0))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusZero(eb,sb)));
    }
    if (x == RFP::plusZero(eb0,sb0))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusZero(eb,sb)));
    }

    // special cases
    if (x == RFP::notANumber(eb0,sb0))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (x == RFP::minusInfinity(eb0,sb0))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }
    if (x == RFP::plusInfinity(eb0,sb0))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
    }
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
    Rational rounded = RFP::round(eb,sb, rm.getUnsignedInt(), v);
    Node ret = nm->mkConstReal(rounded);
    return RewriteResponse(REWRITE_DONE, ret);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

bool sameSign(const Rational& x, const Rational& y)
{
  return (x >= 0 && y >= 0) || (x < 0 && y < 0);
}

RewriteResponse signZeroResult(uint32_t eb, uint32_t sb, NodeManager* nm, uint8_t rm)
{
  if (rm == IntRoundingMode::TN)
    return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusZero(eb,sb)));
  else
    return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusZero(eb,sb)));
}

double toDouble(uint32_t eb, uint32_t sb, const Rational& x)
{
  if (x == RFP::minusZero(eb,sb))
    return -0.0;
  else if (x == RFP::plusZero(eb,sb))
    return 0.0;
  else if (x == RFP::minusInfinity(eb,sb))
    return -std::numeric_limits<double>::infinity();
  else if (x == RFP::plusInfinity(eb,sb))
    return std::numeric_limits<double>::infinity();
  else if (x == RFP::notANumber(eb,sb))
    return std::numeric_limits<double>::quiet_NaN();
  else if (x < 0)
    return -1.0;
  else 
    return 1.0;
}

RewriteResponse ArithRewriter::postRewriteRfpAdd(TNode t)
{
  Assert(t.getKind() == kind::RFP_ADD);
  FloatingPointSize sz = t.getOperator().getConst<RfpAdd>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst() && t[2].isConst())
  {
    // rfp.add is only supported for integer rms and real values
    Assert(t[0].getType().isInteger());
    Assert(t[1].getType().isReal());
    Assert(t[2].getType().isReal());
    uint8_t rm = t[0].getConst<Rational>().getNumerator().getUnsignedInt();
    Rational x = t[1].getConst<Rational>();
    Rational y = t[2].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
        RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
        RFP::isFinite(eb,sb, RFP::round(eb,sb, rm, x + y)))
    {
      Node op = nm->mkConst(RfpRound(eb, sb));
      Node sum = nm->mkNode(kind::ADD, t[1], t[2]);
      Node ret = nm->mkNode(RFP_ROUND, op, t[0], sum);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    // zero cases
    if (RFP::isZero(eb,sb, x) && RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y))
    {
      return RewriteResponse(REWRITE_DONE, t[2]);
    }
    if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      return RewriteResponse(REWRITE_DONE, t[1]);
    }
    if (RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y) && x == y)
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
    if (RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      return signZeroResult(eb,sb, nm, rm);
    }

    // special cases
    if (x == RFP::notANumber(eb,sb) || y == RFP::notANumber(eb,sb))
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
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && 
        !RFP::isFinite(eb,sb, RFP::round(eb,sb, rm, x + y)))
    {
      if (x + y < 0)
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
    }
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpSub(TNode t)
{
  Assert(t.getKind() == kind::RFP_SUB);
  FloatingPointSize sz = t.getOperator().getConst<RfpSub>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst() && t[2].isConst())
  {
    // rfp.sub is only supported for integer rms and real values
    Assert(t[0].getType().isInteger());
    Assert(t[1].getType().isReal());
    Assert(t[2].getType().isReal());
    uint8_t rm = t[0].getConst<Rational>().getNumerator().getUnsignedInt();
    Rational x = t[1].getConst<Rational>();
    Rational y = t[2].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
        RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
        RFP::isFinite(eb,sb, RFP::round(eb,sb, rm, x - y)))
    {
      Node op = nm->mkConst(RfpRound(eb, sb));
      Node sub = nm->mkNode(kind::SUB, t[1], t[2]);
      Node ret = nm->mkNode(RFP_ROUND, op, t[0], sub);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    // zero cases
    if (RFP::isZero(eb,sb, x) && RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y))
    {
      Node neg = nm->mkNode(kind::NEG, t[2]);
      return RewriteResponse(REWRITE_AGAIN_FULL, neg);
    }
    if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      return RewriteResponse(REWRITE_DONE, t[1]);
    }
    if (RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y) && x != y)
    {
      return RewriteResponse(REWRITE_DONE, t[1]);
    }
    if (RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      return signZeroResult(eb,sb, nm, rm);
    }

    // special cases
    if (x == RFP::notANumber(eb,sb) || y == RFP::notANumber(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isInfinite(eb,sb, y))
    {
      if (y == RFP::minusInfinity(eb,sb))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
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
      if (x == RFP::minusInfinity(eb,sb) && y == RFP::plusInfinity(eb,sb))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      else if (x == RFP::plusInfinity(eb,sb) && y == RFP::minusInfinity(eb,sb))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && 
        !RFP::isFinite(eb,sb, RFP::round(eb,sb, rm, x - y)))
    {
      if (x - y < 0)
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
    }
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpNeg(TNode t)
{
  Assert(t.getKind() == kind::RFP_NEG);
  FloatingPointSize sz = t.getOperator().getConst<RfpNeg>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst())
  {
    // rfp.neg is only supported real values
    Assert(t[0].getType().isReal());
    Rational x = t[0].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb, sb, x) && !RFP::isZero(eb, sb, x))
    {
      Node neg = nm->mkNode(kind::NEG, t[0]);
      return RewriteResponse(REWRITE_AGAIN_FULL, neg);
    }

    // zero cases
    if (x == RFP::minusZero(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusZero(eb,sb)));
    }
    if (x == RFP::plusZero(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusZero(eb,sb)));
    }

    // special cases
    if (x == RFP::notANumber(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (x == RFP::minusInfinity(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
    }
    if (x == RFP::plusInfinity(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }

    return RewriteResponse(REWRITE_DONE, t[0]);
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpMul(TNode t)
{
  Assert(t.getKind() == kind::RFP_MUL);
  FloatingPointSize sz = t.getOperator().getConst<RfpMul>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst() && t[2].isConst())
  {
    // rfp.mul is only supported for integer rms and real values
    Assert(t[0].getType().isInteger());
    Assert(t[1].getType().isReal());
    Assert(t[2].getType().isReal());
    uint8_t rm = t[0].getConst<Rational>().getNumerator().getUnsignedInt();
    Rational x = t[1].getConst<Rational>();
    Rational y = t[2].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
        RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
        RFP::isFinite(eb,sb, RFP::round(eb,sb, rm, x * y)))
    {
      Node op = nm->mkConst(RfpRound(eb, sb));
      Node mult = nm->mkNode(kind::MULT, t[1], t[2]);
      Node ret = nm->mkNode(RFP_ROUND, op, t[0], mult);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    // zero cases
    if (RFP::isZero(eb,sb, x) && RFP::isFinite(eb,sb, y))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusZero(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusZero(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusZero(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusZero(eb,sb)));
    }

    // special cases
    if (x == RFP::notANumber(eb,sb) || y == RFP::notANumber(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isInfinite(eb,sb, y))
    {
      if (RFP::isZero(eb,sb, x))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
      else if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }
    if (RFP::isInfinite(eb,sb, x) && RFP::isFinite(eb,sb, y))
    {
      if (RFP::isZero(eb,sb, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
      else if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }
    if (RFP::isInfinite(eb,sb, x) && RFP::isInfinite(eb,sb, y))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && 
        !RFP::isFinite(eb,sb, RFP::round(eb,sb, rm, x * y)))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpDiv(TNode t)
{
  Assert(t.getKind() == kind::RFP_DIV);
  FloatingPointSize sz = t.getOperator().getConst<RfpDiv>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst() && t[2].isConst())
  {
    // rfp.div is only supported for integer rms and real values
    Assert(t[0].getType().isInteger());
    Assert(t[1].getType().isReal());
    Assert(t[2].getType().isReal());
    uint8_t rm = t[0].getConst<Rational>().getNumerator().getUnsignedInt();
    Rational x = t[1].getConst<Rational>();
    Rational y = t[2].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
        RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
        RFP::isFinite(eb,sb, RFP::round(eb,sb, rm, x / y)))
    {
      Node op = nm->mkConst(RfpRound(eb, sb));
      Node div = nm->mkNode(kind::DIVISION, t[1], t[2]);
      Node ret = nm->mkNode(RFP_ROUND, op, t[0], div);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    // zero cases
    if (RFP::isZero(eb,sb, x) && RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusZero(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusZero(eb,sb)));
    }

    //Trace("rfp-rewrite") << "div special case" << std::endl;

    // special cases
    if (x == RFP::notANumber(eb,sb) || y == RFP::notANumber(eb,sb))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isInfinite(eb,sb, y))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusZero(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusZero(eb,sb)));
    }
    if (RFP::isInfinite(eb,sb, x) && RFP::isFinite(eb,sb, y))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }
    if (RFP::isInfinite(eb,sb, x) && RFP::isInfinite(eb,sb, y))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
        !RFP::isFinite(eb,sb, RFP::round(eb,sb, rm, x / y)))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }
    if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      if (sameSign(x, y))
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      else
        return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
    }
    if (RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstReal(RFP::notANumber(eb,sb)));
    }
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpEq(TNode t)
{
  Assert(t.getKind() == kind::RFP_EQ);
  FloatingPointSize sz = t.getOperator().getConst<RfpEq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst())
  {
    // rfp.lt is only supported for real values
    Assert(t[0].getType().isReal());
    Assert(t[1].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Rational y = t[1].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) &&
        x == y) 
    {
      //Node ret = nm->mkConst(true);
      Node ret = nm->mkConstInt(1);
      return RewriteResponse(REWRITE_DONE, ret);
    }
    else if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
             RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y))
    {
      //Node ret = nm->mkConst(x == y);
      Node ret = x == y ? nm->mkConstInt(1) : nm->mkConstInt(0);
      return RewriteResponse(REWRITE_DONE, ret);
    }
    //// zero cases
    //else if (RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    //{
    //  //Node ret = nm->mkConst(true);
    //  Node ret = nm->mkConstInt(1);
    //  return RewriteResponse(REWRITE_DONE, ret);
    //}
    else
    {
      double dx = toDouble(eb,sb, x);
      double dy = toDouble(eb,sb, y);
      Node ret = nm->mkConstInt(dx == dy);
      return RewriteResponse(REWRITE_DONE, ret);
    }
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpLt(TNode t)
{
  Assert(t.getKind() == kind::RFP_LT);
  FloatingPointSize sz = t.getOperator().getConst<RfpLt>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst())
  {
    // rfp.lt is only supported for real values
    Assert(t[0].getType().isReal());
    Assert(t[1].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Rational y = t[1].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && 
        (!RFP::isZero(eb,sb, x) || !RFP::isZero(eb,sb, y)))
    {
      //Node ret = nm->mkConst(x < y);
      Node ret = x < y ? nm->mkConstInt(1): nm->mkConstInt(0);
      return RewriteResponse(REWRITE_DONE, ret);
    }
    //// zero cases
    //else if (RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    //{
    //  //Node ret = nm->mkConst(false);
    //  Node ret = nm->mkConstInt(0);
    //  return RewriteResponse(REWRITE_DONE, ret);
    //}
    else
    {
      double dx = toDouble(eb,sb, x);
      double dy = toDouble(eb,sb, y);
      Node ret = nm->mkConstInt(dx < dy);
      return RewriteResponse(REWRITE_DONE, ret);
    }
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpLeq(TNode t)
{
  Assert(t.getKind() == kind::RFP_LEQ);
  FloatingPointSize sz = t.getOperator().getConst<RfpLeq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  // if constant, can be eliminated
  if (t[0].isConst() && t[1].isConst())
  {
    // rfp.leq is only supported for real values
    Assert(t[0].getType().isReal());
    Assert(t[1].getType().isReal());
    Rational x = t[0].getConst<Rational>();
    Rational y = t[1].getConst<Rational>();

    // finite case
    if (RFP::isFinite(eb,sb, y) && RFP::isFinite(eb,sb, x) && 
        (!RFP::isZero(eb,sb, y) || !RFP::isZero(eb,sb, y))) 
    {
      Node ret = x <= y ? nm->mkConstInt(1) : nm->mkConstInt(0);
      return RewriteResponse(REWRITE_DONE, ret);
    }
    else
    {
      double dx = toDouble(eb,sb, x);
      double dy = toDouble(eb,sb, y);
      Node ret = nm->mkConstInt(dx <= dy);
      return RewriteResponse(REWRITE_DONE, ret);
    }
  }

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewriteRfpGt(TNode t)
{
  Assert(t.getKind() == kind::RFP_GT);
  FloatingPointSize sz = t.getOperator().getConst<RfpGt>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  Node op = nm->mkConst(RfpLt(eb, sb));
  Node ret = nm->mkNode(kind::RFP_LT, op, t[1], t[0]);
  return RewriteResponse(REWRITE_AGAIN_FULL, ret);
}

RewriteResponse ArithRewriter::postRewriteRfpGeq(TNode t)
{
  Assert(t.getKind() == kind::RFP_GEQ);
  FloatingPointSize sz = t.getOperator().getConst<RfpGeq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();
  Node op = nm->mkConst(RfpLeq(eb, sb));
  Node ret = nm->mkNode(kind::RFP_LEQ, op, t[1], t[0]);
  return RewriteResponse(REWRITE_AGAIN_FULL, ret);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
