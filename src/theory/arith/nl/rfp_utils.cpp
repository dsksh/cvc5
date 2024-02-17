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
  return nm->mkNode(LEQ, mkAbs(x), nm->mkConstReal(Rational(RFP::maxValue(eb,sb))));
}

Node mkAbs(TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(kind::ABS, x);
}

Node mkIsNormal(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isFinite = mkIsFinite(eb,sb, x);
  Node minNormal = nm->mkConstReal(RFP::minNormal(eb,sb));
  Node lbAbs = nm->mkNode(kind::LEQ, minNormal, mkAbs(x));
  return isFinite.andNode(lbAbs);
}

Node mkIsSubnormal(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node minSubnormal = nm->mkConstReal(RFP::minSubnormal(eb,sb));
  Node minNormal = nm->mkConstReal(RFP::minNormal(eb,sb));
  Node abs = mkAbs(x);
  Node lbAbs = nm->mkNode(LEQ, minSubnormal, abs);
  Node ubAbs = nm->mkNode(LT, abs, minNormal);
  return lbAbs.andNode(ubAbs);
}

Node mkIsSubnormalWeak(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node minNormal = nm->mkConstReal(RFP::minNormal(eb,sb));
  Node abs = mkAbs(x);
  return nm->mkNode(LT, abs, minNormal);
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

Node mkIsNegZero(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::minusZero(eb,sb)));
}

Node mkIsPosZero(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::plusZero(eb,sb)));
}

Node mkIsInf(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNinf = x.eqNode(nm->mkConstReal(RFP::minusInfinity(eb,sb)));
  Node isPinf = x.eqNode(nm->mkConstReal(RFP::plusInfinity(eb,sb)));
  return isNinf.orNode(isPinf);
}

Node mkIsNan(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::notANumber(eb,sb)));
}

Node mkIsNeg(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNotNan = mkIsNan(eb,sb, x).notNode();
  Node isNeg = nm->mkNode(LT, x, nm->mkConstReal(Rational(0)));
  return isNotNan.andNode(isNeg);
}

Node mkIsPos(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNotNan = mkIsNan(eb,sb, x).notNode();
  Node isPos = nm->mkNode(GT, x, nm->mkConstReal(Rational(0)));
  return isNotNan.andNode(isPos);
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

Node mkSignZeroResult(uint32_t eb, uint32_t sb, TNode rm, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node assumption = mkIsZero(eb,sb, x);
  Node isRTN = nm->mkNode(EQUAL, rm, nm->mkConstInt(IRM::TZ), rm);
  Node isNegative = nm->mkNode(LEQ, nm->mkConstInt(Rational(0)), x);
  Node isPositive = nm->mkNode(LEQ, x, nm->mkConstInt(Rational(1)));
  Node conclusion = isRTN.iteNode(isNegative, isPositive);
  return assumption.impNode(conclusion);
}

Node mkProductSign(uint32_t eb, uint32_t sb, TNode z, TNode x, TNode y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node l1 = mkSameSign(eb,sb, x, y).impNode(mkIsPos(eb,sb, z));
  Node l2 = mkDiffSign(eb,sb, x, y).impNode(mkIsNeg(eb,sb, z));
  return l1.andNode(l2);
}

Node mkIsOverflowValue(uint32_t eb, uint32_t sb, TNode rm, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node rmTN = rm.eqNode(nm->mkConstInt(IRM::TN));
  Node rmTP = rm.eqNode(nm->mkConstInt(IRM::TP));
  Node rmTZ = rm.eqNode(nm->mkConstInt(IRM::TZ));
  Node rmNE = rm.eqNode(nm->mkConstInt(IRM::NE));
  Node rmNA = rm.eqNode(nm->mkConstInt(IRM::NA));
  Node isPos = mkIsPos(eb,sb, x);
  Node isFinite = mkIsFinite(eb,sb, x);
  Node isInf = mkIsInf(eb,sb, x);
  Node isMax = x.eqNode(nm->mkConstReal(RFP::maxValue(eb,sb)));
  Node isMin = x.eqNode(nm->mkConstReal(-RFP::maxValue(eb,sb)));
  Node l1 = rmTN.impNode(isPos.iteNode(isMax, isInf));
  Node l2 = rmTP.impNode(isPos.iteNode(isInf, isMin));
  Node l3 = rmTZ.impNode(isPos.iteNode(isMax, isMin));
  Node l4 = (rmNE.orNode(rmNA)).impNode(isInf);
  return l1.andNode(l2).andNode(l3).andNode(l4);
}

Node mkRangeConstraint(uint32_t eb, uint32_t sb, TNode node)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNan = mkIsNan(eb,sb, node);
  //Node isInf  = mkIsInf(eb,sb, node);
  Node isNegInf  = node.eqNode(nm->mkConstReal(RFP::minusInfinity(eb,sb)));
  Node isPosInf = node.eqNode(nm->mkConstReal(RFP::plusInfinity(eb,sb)));
  //Node isZero = mkIsZero(eb,sb, node);
  Node isNegZero = node.eqNode(nm->mkConstReal(RFP::minusZero(eb,sb)));
  Node isPosZero = node.eqNode(nm->mkConstReal(RFP::plusZero(eb,sb)));
  Node isFinite = mkIsFinite(eb,sb, node);
  Node isNormal = mkIsNormal(eb,sb, node);
  Node isSubnormal = mkIsSubnormal(eb,sb, node);
  //Node eqRounded = mkIsRounded(eb,sb, node);
  return 
    isNan
    .orNode(isNegZero).orNode(isPosZero)
    .orNode(isNegInf).orNode(isPosInf)
    .orNode(isNormal)
    .orNode(isSubnormal)
    ;
}

Node mkIsRounded(uint32_t eb, uint32_t sb, TNode node)
{
  NodeManager* nm = NodeManager::currentNM();
  Node op = nm->mkConst(RfpRound(eb, sb));
  Node rm = nm->mkConstInt(0);
  Node rounded = nm->mkNode(kind::RFP_ROUND, op, rm, node);
  return node.eqNode(rounded);
}

/** Relation between node1 and node2, where node2 = round(node1).
 * 
 */
Node mkRoundCases(uint32_t eb1, uint32_t sb1, TNode node1,
  uint32_t eb2, uint32_t sb2, TNode node2)
{
  Node isZero1 = mkIsZero(eb1,sb1, node1);
  Node isZero2 = mkIsZero(eb2,sb2, node2);
  Node l1 = isZero1.impNode(isZero2);
  Node isInf1 = mkIsInf(eb1,sb1, node1);
  Node isInf2 = mkIsInf(eb2,sb2, node2);
  Node l2 = isInf1.impNode(isInf2);
  Node isNan1 = mkIsNan(eb1,sb1, node1);
  Node isNan2 = mkIsNan(eb2,sb2, node2);
  Node l3 = isNan1.eqNode(isNan2);
  Node isNeg1 = mkIsNeg(eb1,sb1, node1);
  Node isNeg2 = mkIsNeg(eb2,sb2, node2);
  Node l4 = isNeg1.eqNode(isNeg2);
  Node isNormal1 = mkIsNormal(eb1,sb1, node1);
  Node isNormal2 = mkIsNormal(eb2,sb2, node2);
  Node isSN1 = mkIsSubnormal(eb1,sb1, node1);
  Node isSN2 = mkIsSubnormal(eb2,sb2, node2);
  Node l5 = (isNormal2.orNode(isSN2))
    .impNode(isNormal1.orNode(isSN1));
  return l1.andNode(l2).andNode(l3).andNode(l4).andNode(l5);
}

}  // namespace RfpUtils

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
