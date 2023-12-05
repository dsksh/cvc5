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
 * Utilities for real encoding of floating-point values.
 */
#include "cvc5_public.h"

#ifndef CVC5__REAL_FLOATINGPOINT_H
#define CVC5__REAL_FLOATINGPOINT_H

#include <memory>

#include "util/bitvector.h"
#include "util/integer.h"
#include "util/rational.h"
#include "util/int_roundingmode.h"
#include "util/floatingpoint.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

/* -------------------------------------------------------------------------- */

class FloatingPointLiteral;

class FloatingPoint;

class RealFloatingPoint
{
 public:
  /**
   * Get the maximum value of exponent.
   */
  static Integer maxExponent(uint32_t& size)
  {
    return Integer((2<<(size-2)) - 1);
  }
  /**
   * Get the minimum value of exponent.
   */
  static Integer minExponent(uint32_t& size)
  {
    return Integer(Integer(2) - maxExponent(size));
  }

  /**
   * Rounding operator.
   */
  static Rational round(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& value);
  static Integer roundToInteger(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& value);

}; /* class RealFloatingPoint */

}  // namespace cvc5::internal

#endif /* CVC5__REAL_FLOATINGPOINT_H */
