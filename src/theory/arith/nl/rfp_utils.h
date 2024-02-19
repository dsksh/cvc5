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
 * Utility function for the rfp terms.
 */

#ifndef CVC5__THEORY__ARITH__NL__RFP_UTILS_H
#define CVC5__THEORY__ARITH__NL__RFP_UTILS_H

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

namespace RfpUtils {

Node mkAbs(TNode x);
Node mkFalse(TNode i);
Node mkTrue(TNode i);
Node mkIsFinite(uint32_t eb, uint32_t sb, TNode x);
Node mkNoOverflow(uint32_t eb, uint32_t sb, TNode rm, TNode x);
Node mkIsNormal(uint32_t eb, uint32_t sb, TNode x);
Node mkIsSubnormal(uint32_t eb, uint32_t sb, TNode x);
Node mkIsSubnormalWeak(uint32_t eb, uint32_t sb, TNode x);
Node mkIsZero(uint32_t eb, uint32_t sb, TNode x);
Node mkIsZeroWeak(uint32_t eb, uint32_t sb, TNode x);
Node mkIsNegZero(uint32_t eb, uint32_t sb, TNode x);
Node mkIsPosZero(uint32_t eb, uint32_t sb, TNode x);
Node mkIsInf(uint32_t eb, uint32_t sb, TNode x);
Node mkIsNan(uint32_t eb, uint32_t sb, TNode x);
Node mkIsNeg(uint32_t eb, uint32_t sb, TNode x);
Node mkIsPos(uint32_t eb, uint32_t sb, TNode x);
Node mkIsNegInf(uint32_t eb, uint32_t sb, TNode x);
Node mkIsPosInf(uint32_t eb, uint32_t sb, TNode x);
Node mkSameSign(uint32_t eb, uint32_t sb, TNode x, TNode y);
Node mkDiffSign(uint32_t eb, uint32_t sb, TNode x, TNode y);
Node mkSignZeroResult(uint32_t eb, uint32_t sb, TNode rm, TNode x);
Node mkProductSign(uint32_t eb, uint32_t sb, TNode z, TNode x, TNode y);
Node mkIsOverflowValue(uint32_t eb, uint32_t sb, TNode rm, TNode x);

Node mkIsToNearest(TNode rm);

Node mkRangeConstraint(uint32_t eb, uint32_t sb, TNode x);
Node mkIsRounded(uint32_t eb, uint32_t sb, TNode x);
Node mkRoundCases(uint32_t eb1, uint32_t sb1, TNode n1, 
  uint32_t eb2, uint32_t sb2, TNode n2);

}; /* namespace RfpUtils */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_UTILS_H */
