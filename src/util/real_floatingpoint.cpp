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
 * The integer representation of FP rounding modes.
 */

#include <math.h>

#include <limits>
#include <unordered_map>

#include "base/check.h"
#include "base/output.h"
#include "util/integer.h"
#include "util/real_floatingpoint.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

namespace RealFloatingPoint {

/* -------------------------------------------------------------------------- */

uint32_t hash(uint32_t eb, uint32_t sb)
{
  return 19*eb + sb;
}

Integer maxValue(uint32_t eb, uint32_t sb)
{
  static std::unordered_map<uint32_t, Integer> cache;

  uint32_t h = hash(eb, sb);
  if (!cache.count(h)){
    uint64_t emax = maxExponent(eb).getUnsigned64();
    cache[h] = (Integer::pow2(sb)-1) * Integer::pow2(emax-sb+1);
  }
  return cache[h];
}

Rational plusZero(uint32_t eb, uint32_t sb)
{
  return Rational(0);
}
Rational minusZero(uint32_t eb, uint32_t sb)
{
  static std::unordered_map<uint32_t, Rational> cache;

  uint32_t h = hash(eb, sb);
  if (!cache.count(h)){
    uint64_t emax = maxExponent(eb).getUnsigned64();
    Integer d = Integer::pow2(emax+sb);
    cache[h] = -Rational(d).inverse();
  }
  return cache[h];
}

bool isNormal(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return false;
}

bool isSubnormal(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return false;
}

bool isZero(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return (arg == minusZero(eb, sb)) || (arg == plusZero(eb, sb));
}

bool inRange(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return Rational(-maxValue(eb,sb)) <= arg && arg <= Rational(maxValue(eb,sb));
}

bool isFinite(uint32_t eb, uint32_t sb, const Rational& arg)
{
  // TODO: isSubnormal
  return inRange(eb, sb, arg);
}

bool noOverflow(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& arg)
{
  // TODO
  return true;
}

//

Rational roundInternal(bool toInt, uint32_t eb, uint32_t sb, uint8_t rm, const Rational& value)
{
  Integer mMax = Integer::pow2(sb-1);
  Assert(eb < 34);
  uint32_t eMax = (2<<(eb-2)) - 1;
  Integer eeMax = Integer::pow2(eMax);
  Rational eeMin = Rational(1, Integer::pow2(eMax-1));

  Rational normalMax = (Rational(2)-Rational(1)/mMax)*eeMax;
  Rational snMin = Rational(1, Integer::pow2(eMax-2+sb));
  Rational minusZero = -snMin / 4;

  if (value.isZero())
    return Rational(0);
  else if (toInt && value == minusZero) // -0
    return value;
  else if (value.abs() == normalMax)
    return value;
  else if (toInt && value.abs() > normalMax) // -+oo, NaN
    return value;
  else if (value.abs() > normalMax){
    if (value.sgn() > 0){
      if (rm == IntRoundingMode::TN || rm == IntRoundingMode::TZ)
        return normalMax;
      else
        return normalMax+1; //value;
    }else{ // value.sgn() < 0
      if (rm == IntRoundingMode::TP || rm == IntRoundingMode::TZ)
        return -normalMax;
      else
        return -normalMax-1; //value;
    }
  }else if ( value.sgn() > 0 && (
             (rm == IntRoundingMode::NE && value <= snMin/2)
          || (rm == IntRoundingMode::NA && value < snMin/2)
          || (rm == IntRoundingMode::TN && value < snMin)
          || (rm == IntRoundingMode::TZ && value < snMin) )){
    return Rational(0);
  }else if ( value.sgn() < 0 && (
             (rm == IntRoundingMode::NE && value >= -snMin/2)
          || (rm == IntRoundingMode::NA && value > -snMin/2)
          || (rm == IntRoundingMode::TP && value > -snMin)
          || (rm == IntRoundingMode::TZ && value > -snMin) )){
    return minusZero;
  }else if ( (rm == IntRoundingMode::TP && value.sgn() > 0 && value <= snMin)
          || value == snMin ){
    return snMin;
  }else if ( (rm == IntRoundingMode::TN && value.sgn() <  0 && value >= -snMin)
          || value == -snMin ){
    return -snMin;
  }

  Assert(value.abs() < normalMax);

  Rational r = value;
  Trace("rfp-round-eval") << "r0: " << r << std::endl;
  Rational ee = r.pow2Lower();
  if (!toInt){
    if (ee < eeMin) ee = eeMin;
    r /= ee;
    r *= mMax;
  }

  if (rm == IntRoundingMode::TP){
    r = r.ceiling();
  }else if (rm == IntRoundingMode::TN){
    r = r.floor();
  }else if (rm == IntRoundingMode::TZ){
    if (r.sgn() >= 0)
      r = r.floor();
    else
      r = -((-r).floor());
  }else if (rm == IntRoundingMode::NE){
    Integer i1 = (r+Rational(1,2)).floor();
    Integer i2 = (r-Rational(1,2)).ceiling();
    if (i1 == i2 || i1.modByPow2(1) == 0)
      r = i1;
    else
      r = i2;
  }else if (rm == IntRoundingMode::NA){
    r += Rational(1,2);
    if (r.sgn() >= 0)
      r = r.floor();
    else
      r = -((-r).floor());
  }

  Trace("rfp-round-eval") << "r_: " << r << std::endl;

  if (!toInt){
    r /= mMax;
    r *= ee;
  }else if (toInt && r.isZero() && value.sgn() < 0){
    r = minusZero;
  }
  Trace("rfp-round-eval") << "rv: " << r << std::endl;
  return r;
}

/** Round to real representation of FP numbers.
 */
Rational round(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& value)
{
  return roundInternal(false, eb, sb, rm, value);
}
/** Round to integer.
 */
Integer roundToInteger(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& value)
{
  return roundInternal(true, eb, sb, rm, value).getNumerator();
}

}  // namespace RealFloatingPoint

}  // namespace cvc5::internal
