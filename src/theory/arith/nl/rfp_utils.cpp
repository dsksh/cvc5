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
  return (i.eqNode(nm->mkConstInt(0))).notNode();
  //return i.eqNode(nm->mkConstInt(1));
}

Node mkIsOne(TNode i)
{
  NodeManager* nm = NodeManager::currentNM();
  //return (i.eqNode(nm->mkConstInt(0))).notNode();
  return i.eqNode(nm->mkConstInt(1));
}

Node mkBoolIntConstraint(TNode i)
{
  NodeManager* nm = NodeManager::currentNM();
  //Node lb = nm->mkNode(Kind::LEQ, nm->mkConstInt(0), i);
  //Node ub = nm->mkNode(Kind::LEQ, i, nm->mkConstInt(1));
  //return lb.andNode(ub);
  Node zero = i.eqNode(nm->mkConstInt(0));
  Node one = i.eqNode(nm->mkConstInt(1));
  return zero.orNode(one);
  //return nm->mkConst(true);
}

Node mkIsFinite(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node maxN = nm->mkConstReal(-RFP::maxValue(eb,sb));
  Node maxP = nm->mkConstReal(RFP::maxValue(eb,sb));
  Node maxNB = nm->mkNode(Kind::LEQ, maxN, x);
  Node maxPB = nm->mkNode(Kind::LEQ, x, maxP);
  return maxNB.andNode(maxPB);
}

Node mkNoOverflow(uint32_t eb, uint32_t sb, TNode rm, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  //Node op = nm->mkConst(RfpRound(eb, sb));
  //Node rounded = nm->mkNode(Kind::RFP_ROUND, op, rm, x);
  //return mkIsFinite(eb,sb, rounded);

  Node isTN = rm.eqNode(nm->mkConstInt(IRM::TN));
  Node isTP = rm.eqNode(nm->mkConstInt(IRM::TP));
  Node isNE = rm.eqNode(nm->mkConstInt(IRM::NE));
  Node isNA = rm.eqNode(nm->mkConstInt(IRM::NA));

  Rational max = RFP::maxValue(eb,sb);
  Node bTN = nm->mkNode(Kind::LEQ, nm->mkConstReal(-max), x);
  Node lTN = isTN.impNode(bTN);
  Node bTP = nm->mkNode(Kind::LEQ, x, nm->mkConstReal(max));
  Node lTP = isTP.impNode(bTP);
  Node bN = nm->mkNode(Kind::AND,
    nm->mkNode(Kind::LT, nm->mkConstReal(-RFP::maxValueExt(eb,sb)), x),
    nm->mkNode(Kind::LT, x, nm->mkConstReal(RFP::maxValueExt(eb,sb))));
  Node lN = (isNE.orNode(isNA)).impNode(bN);
  return lTN.andNode(lTP).andNode(lN);
}

Node mkAbs(TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(Kind::ABS, x);
}

Node mkIsNormal(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isFinite = mkIsFinite(eb,sb, x);
  Node minNormalN = nm->mkConstReal(-RFP::minNormal(eb,sb));
  Node minNormalP = nm->mkConstReal(RFP::minNormal(eb,sb));
  Node minNNB = nm->mkNode(Kind::LEQ, x, minNormalN);
  Node minNPB = nm->mkNode(Kind::LEQ, minNormalP, x);
  return isFinite.andNode( minNNB.orNode(minNPB) );
}

Node mkIsSubnormal(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node minSubnormalN = nm->mkConstReal(-RFP::minSubnormal(eb,sb));
  Node minNormalN = nm->mkConstReal(-RFP::minNormal(eb,sb));
  Node minSNB = nm->mkNode(Kind::LEQ, x, minSubnormalN);
  Node minNNB = nm->mkNode(Kind::LT, minNormalN, x);
  Node nB = minSNB.andNode(minNNB);

  Node minSubnormalP = nm->mkConstReal(RFP::minSubnormal(eb,sb));
  Node minNormalP = nm->mkConstReal(RFP::minNormal(eb,sb));
  Node minSPB = nm->mkNode(Kind::LEQ, minSubnormalP, x);
  Node minNPB = nm->mkNode(Kind::LT, x, minNormalP);
  Node pB = minSPB.andNode(minNPB);

  return nB.orNode(pB);
}

Node mkIsSubnormalWeak(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node minNormalN = nm->mkConstReal(-RFP::minNormal(eb,sb));
  Node minNormalP = nm->mkConstReal(RFP::minNormal(eb,sb));
  Node minNNB = nm->mkNode(Kind::LT, minNormalN, x);
  Node minNPB = nm->mkNode(Kind::LT, x, minNormalP);
  return minNNB.andNode(minNPB);
}

Node mkIsZero(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nz = x.eqNode(nm->mkConstReal(RFP::minusZero(eb,sb)));
  Node pz = x.eqNode(nm->mkConstReal(RFP::plusZero(eb,sb)));
  return nm->mkNode(Kind::OR, nz, pz);
}

Node mkIsZeroWeak(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nz = nm->mkNode(Kind::LEQ, nm->mkConstReal(RFP::minusZero(eb,sb)), x);
  Node pz = nm->mkNode(Kind::LEQ, x, nm->mkConstReal(RFP::plusZero(eb,sb)));
  return nm->mkNode(Kind::AND, nz, pz);
}

Node mkIsNegZero(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(Kind::EQUAL, x, nm->mkConstReal(RFP::minusZero(eb,sb)));
}

Node mkIsPosZero(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(Kind::EQUAL, x, nm->mkConstReal(RFP::plusZero(eb,sb)));
}

Node mkIsInf(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNinf = x.eqNode(nm->mkConstReal(RFP::minusInfinity(eb,sb)));
  Node isPinf = x.eqNode(nm->mkConstReal(RFP::plusInfinity(eb,sb)));
  return isNinf.orNode(isPinf);
}
Node mkIsInfWeak(uint32_t eb, uint32_t sb, TNode x)
{
  Node c1 = mkIsFinite(eb,sb, x).notNode();
  Node c2 = mkIsNan(eb,sb, x).notNode();
  return c1.andNode(c2);
}

Node mkIsNan(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  x.eqNode(nm->mkConstReal(RFP::notANumber(eb,sb)));
}

Node mkIsNeg(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNotNan = mkIsNan(eb,sb, x).notNode();
  Node isNeg = nm->mkNode(Kind::LT, x, nm->mkConstReal(Rational(0)));
  //return isNotNan.impNode(isNeg);
  return isNeg;
}

Node mkIsPos(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNotNan = mkIsNan(eb,sb, x).notNode();
  Node isPos = nm->mkNode(Kind::GEQ, x, nm->mkConstReal(Rational(0)));
  //return isNotNan.impNode(isPos);
  return isPos;
}

Node mkIsNegInf(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return x.eqNode(nm->mkConstReal(RFP::minusInfinity(eb,sb)));
}

Node mkIsPosInf(uint32_t eb, uint32_t sb, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  return x.eqNode(nm->mkConstReal(RFP::plusInfinity(eb,sb)));
}

Node mkSameSign(uint32_t eb, uint32_t sb, TNode x, TNode y)
{
  //NodeManager* nm = NodeManager::currentNM();
  Node isPosPos = mkIsPos(eb,sb, x).andNode(mkIsPos(eb,sb, y));
  Node isNegNeg = mkIsNeg(eb,sb, x).andNode(mkIsNeg(eb,sb, y));
  return isPosPos.orNode(isNegNeg);
}

Node mkDiffSign(uint32_t eb, uint32_t sb, TNode x, TNode y)
{
  //NodeManager* nm = NodeManager::currentNM();
  Node isPosNeg = mkIsPos(eb,sb, x).andNode(mkIsNeg(eb,sb, y));
  Node isNegPos = mkIsNeg(eb,sb, x).andNode(mkIsPos(eb,sb, y));
  return isPosNeg.orNode(isNegPos);
}

Node mkSignZeroResult(uint32_t eb, uint32_t sb, TNode rm, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node assumption = mkIsZero(eb,sb, x);
  Node isRTN = rm.eqNode(nm->mkConstInt(IRM::TN));
  Node conclusion = isRTN.iteNode(mkIsNeg(eb,sb, x), mkIsPos(eb,sb, x));
  return assumption.impNode(conclusion);
}

Node mkProductSign(uint32_t eb, uint32_t sb, TNode z, TNode x, TNode y)
{
  //NodeManager* nm = NodeManager::currentNM();
  Node l1 = mkSameSign(eb,sb, x, y).impNode(mkIsPos(eb,sb, z));
  Node l2 = mkDiffSign(eb,sb, x, y).impNode(mkIsNeg(eb,sb, z));
  return l1.andNode(l2);
}

Node mkIsOverflowValue(uint32_t eb, uint32_t sb, TNode rm, TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isTN = rm.eqNode(nm->mkConstInt(IRM::TN));
  Node isTP = rm.eqNode(nm->mkConstInt(IRM::TP));
  Node isTZ = rm.eqNode(nm->mkConstInt(IRM::TZ));
  Node isNE = rm.eqNode(nm->mkConstInt(IRM::NE));
  Node isNA = rm.eqNode(nm->mkConstInt(IRM::NA));
  Node isPos = mkIsPos(eb,sb, x);
  Node isFinite = mkIsFinite(eb,sb, x);
  Node isInf = mkIsInf(eb,sb, x);
  Node isMax = x.eqNode(nm->mkConstReal(RFP::maxValue(eb,sb)));
  Node isMin = x.eqNode(nm->mkConstReal(-RFP::maxValue(eb,sb)));
  Node l1 = isTN.impNode(isPos.iteNode(isMax, isInf));
  Node l2 = isTP.impNode(isPos.iteNode(isInf, isMin));
  Node l3 = isTZ.impNode(isPos.iteNode(isMax, isMin));
  Node l4 = (isNE.orNode(isNA)).impNode(isInf);
  return l1.andNode(l2).andNode(l3).andNode(l4);
}

Node mkIsToNearest(TNode rm)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isNE = rm.eqNode(nm->mkConstInt(IRM::NE));
  Node isNA = rm.eqNode(nm->mkConstInt(IRM::NA));
  return isNE.orNode(isNA);
}

Node mkRangeConstraint(uint32_t eb, uint32_t sb, TNode node)
{
  NodeManager* nm = NodeManager::currentNM();

  //Node isNan = mkIsNan(eb,sb, node);
  ////Node isInf  = mkIsInf(eb,sb, node);
  //Node isNegInf  = node.eqNode(nm->mkConstReal(RFP::minusInfinity(eb,sb)));
  //Node isPosInf = node.eqNode(nm->mkConstReal(RFP::plusInfinity(eb,sb)));
  ////Node isZero = mkIsZero(eb,sb, node);
  //Node isNegZero = node.eqNode(nm->mkConstReal(RFP::minusZero(eb,sb)));
  //Node isPosZero = node.eqNode(nm->mkConstReal(RFP::plusZero(eb,sb)));
  //Node isFinite = mkIsFinite(eb,sb, node);
  //Node isNormal = mkIsNormal(eb,sb, node);
  //Node isSubnormal = mkIsSubnormal(eb,sb, node);
  ////Node eqRounded = mkIsRounded(eb,sb, node);
  //return 
  //  isNan
  //  .orNode(isNegZero).orNode(isPosZero)
  //  .orNode(isNegInf).orNode(isPosInf)
  //  .orNode(isNormal)
  //  .orNode(isSubnormal);

  return nm->mkConst(true);
}

Node mkIsRounded(uint32_t eb, uint32_t sb, TNode node)
{
  NodeManager* nm = NodeManager::currentNM();

  Node op = nm->mkConst(RfpRound(eb, sb));
  Node rm1 = nm->mkConstInt(IRM::NE);
  Node rd1 = nm->mkNode(Kind::RFP_ROUND, op, rm1, node);
  return node.eqNode(rd1);
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
  Node l3 = isNan1.impNode(isNan2);
  Node isNeg1 = mkIsNeg(eb1,sb1, node1);
  Node isNeg2 = mkIsNeg(eb2,sb2, node2);
  Node l4 = isNeg1.eqNode(isNeg2);
  Node isPos1 = mkIsPos(eb1,sb1, node1);
  Node isPos2 = mkIsPos(eb2,sb2, node2);
  Node l5 = isPos1.eqNode(isPos2);
  //Node isNormal1 = mkIsNormal(eb1,sb1, node1);
  //Node isNormal2 = mkIsNormal(eb2,sb2, node2);
  //Node isSN1 = mkIsSubnormal(eb1,sb1, node1);
  //Node isSN2 = mkIsSubnormal(eb2,sb2, node2);
  return l1.andNode(l2).andNode(l3).andNode(l4).andNode(l5);
}

}  // namespace RfpUtils

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
