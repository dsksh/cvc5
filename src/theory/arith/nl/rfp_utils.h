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

Node mkFalse(TNode i);
Node mkTrue(TNode i);
Node mkIsFinite(uint32_t eb, uint32_t sb, TNode x);
Node mkIsZero(uint32_t eb, uint32_t sb, TNode x);
Node mkIsZeroWeak(uint32_t eb, uint32_t sb, TNode x);
Node mkIsInf(uint32_t eb, uint32_t sb, TNode x);
Node mkIsPos(uint32_t eb, uint32_t sb, TNode x);
Node mkIsNeg(uint32_t eb, uint32_t sb, TNode x);
Node mkSameSign(uint32_t eb, uint32_t sb, TNode x, TNode y);
Node mkDiffSign(uint32_t eb, uint32_t sb, TNode x, TNode y);
Node mkIsNegInf(uint32_t eb, uint32_t sb, TNode x);
Node mkIsPosInf(uint32_t eb, uint32_t sb, TNode x);
Node mkIsNan(uint32_t eb, uint32_t sb, TNode x);
Node mkSignZeroResult(uint32_t eb, uint32_t sb, TNode rm, TNode x);

}; /* namespace RfpUtils */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_UTILS_H */
