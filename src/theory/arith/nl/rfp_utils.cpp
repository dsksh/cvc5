/******************************************************************************
 * Top contributors (to current version):
 *   Daisuke Ishii
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the RFP utility functions.
 */

#include "theory/arith/nl/rfp_utils.h"

#include "theory/arith/nl/nl_model.h"
#include "util/int_roundingmode.h"
#include "util/real_floatingpoint.h"

using namespace cvc5::internal::kind;

using IRM = typename cvc5::internal::IntRoundingMode;
namespace RFP = cvc5::internal::RealFloatingPoint;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

namespace RfpUtils {

Node mkFalse(TNode i)
{
  NodeManager* nm = NodeManager::currentNM();
  return i.eqNode(nm->mkConstInt(0));
}

Node mkTrue(TNode i)
{
  NodeManager* nm = NodeManager::currentNM();
  return i.eqNode(nm->mkConstInt(0)).notNode();
  //Node one = nm->mkConstInt(1);
  //return nm->mkNode(EQUAL, i, one);
}

Node mkIsFinite(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lb = nm->mkNode(LEQ, nm->mkConstReal(-Rational(RFP::maxValue(eb,sb))), x);
  Node ub = nm->mkNode(LEQ, x, nm->mkConstReal(Rational(RFP::maxValue(eb,sb))));
  return nm->mkNode(AND, lb, ub);
}

Node mkIsZero(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nz = nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::minusZero(eb,sb)));
  Node pz = nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::plusZero(eb,sb)));
  return nm->mkNode(OR, nz, pz);
}

Node mkIsZeroWeak(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nz = nm->mkNode(LEQ, nm->mkConstReal(RFP::minusZero(eb,sb)), x);
  Node pz = nm->mkNode(LEQ, x, nm->mkConstReal(RFP::plusZero(eb,sb)));
  return nm->mkNode(AND, nz, pz);
}

Node mkIsInf(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNinf = x.eqNode(nm->mkConstReal(RFP::minusInfinity(eb,sb)));
  Node isPinf = x.eqNode(nm->mkConstReal(RFP::plusInfinity(eb,sb)));
  return isNinf.orNode(isPinf);
}

Node mkIsNeg(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  //Node isFinite = mkIsFinite(eb,sb, x);
  //Node isInf = mkIsInf(eb,sb, x);
  //Node finOrInf = nm->mkNode(OR, isFinite, isInf);
  Node isNotNan = mkIsNan(eb,sb, x).notNode();
  Node isNeg = nm->mkNode(LT, x, nm->mkConstReal(Rational(0)));
  //return nm->mkNode(AND, finOrInf, isNeg);
  return isNotNan.andNode(isNeg);
}

Node mkIsPos(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  //Node isFinite = mkIsFinite(eb,sb, x);
  //Node isInf = mkIsInf(eb,sb, x);
  //Node finOrInf = nm->mkNode(OR, isFinite, isInf);
  Node isNotNan = mkIsNan(eb,sb, x).notNode();
  Node isPos = nm->mkNode(GT, x, nm->mkConstReal(Rational(0)));
  //return nm->mkNode(AND, finOrInf, isPos);
  return isNotNan.andNode(isPos);
}

Node mkSameSign(uint32_t eb, uint32_t sb, TNode x, TNode y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node positive = nm->mkNode(AND, mkIsPos(eb,sb, x), mkIsPos(eb,sb, y));
  Node negative = nm->mkNode(AND, mkIsNeg(eb,sb, x), mkIsNeg(eb,sb, y));
  return nm->mkNode(OR, positive, negative);
}

Node mkDiffSign(uint32_t eb, uint32_t sb, TNode x, TNode y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node pos_neg = nm->mkNode(AND, mkIsPos(eb,sb, x), mkIsNeg(eb,sb, y));
  Node neg_pos = nm->mkNode(AND, mkIsNeg(eb,sb, x), mkIsPos(eb,sb, y));
  return nm->mkNode(OR, pos_neg, neg_pos);
}

Node mkIsNegInf(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
}
Node mkIsPosInf(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
}
Node mkIsNan(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::notANumber(eb,sb)));
}

Node mkSignZeroResult(uint32_t eb, uint32_t sb, TNode rm, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isZero = mkIsZero(eb,sb, x);
  Node isRTN = nm->mkNode(EQUAL, rm, nm->mkConstInt(IRM::TZ), rm);
  Node isNegative = nm->mkNode(LEQ, nm->mkConstInt(Rational(0)), x);
  Node isPositive = nm->mkNode(LEQ, x, nm->mkConstInt(Rational(1)));
  Node concl = isRTN.iteNode(isNegative, isPositive);
  return nm->mkNode(IMPLIES, isZero, concl);
}

}  // namespace RfpUtils

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
