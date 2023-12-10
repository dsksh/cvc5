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

namespace RealFloatingPoint {

/** Get the maximum value of exponent.
 */
static Integer maxExponent(uint32_t size)
{
  return Integer((2<<(size-2)) - 1);
}
/** Get the minimum value of exponent.
 */
static Integer minExponent(uint32_t size)
{
  return Integer(Integer(2) - maxExponent(size));
}

/** Get the maximum normal value.
 */
Integer maxValue(uint32_t eb, uint32_t sb);

/** Get the negative zero.
 */
Rational minusZero(uint32_t eb, uint32_t sb);

/** Get the possitive zero.
 */
Rational plusZero(uint32_t eb, uint32_t sb);

/** Get the negative infinity.
 */
Rational minusInfinity(uint32_t eb, uint32_t sb);

/** Get the possitive infinity.
 */
Rational plusInfinity(uint32_t eb, uint32_t sb);

/** Get the NaN.
 */
Rational notANumber(uint32_t eb, uint32_t sb);

bool isNormal(uint32_t eb, uint32_t sb, const Rational& arg);
bool isSubnormal(uint32_t eb, uint32_t sb, const Rational& arg);
bool isZero(uint32_t eb, uint32_t sb, const Rational& arg);
//bool inRange(uint32_t eb, uint32_t sb, const Rational& arg);
bool isFinite(uint32_t eb, uint32_t sb, const Rational& arg);
bool isInfinite(uint32_t eb, uint32_t sb, const Rational& arg);
bool noOverflow(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& arg);

/**
 * Rounding operator.
 */
Rational round(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& arg);
Integer roundToInteger(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& arg);

///**
// * Addition.
// */
//Rational add(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& arg1, const Rational& arg2);

}  // namespace RealFloatingPoint

}  // namespace cvc5::internal

#endif /* CVC5__REAL_FLOATINGPOINT_H */
