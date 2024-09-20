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
 * The implementation of the utilities for real encoding of floating-point values.
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

using IRM = typename cvc5::internal::IntRoundingMode;

/* -------------------------------------------------------------------------- */

uint32_t hash(uint32_t eb, uint32_t sb)
{
  return 7*eb + sb;
}

Integer maxValue(uint32_t eb, uint32_t sb)
{
  static std::unordered_map<uint32_t, Integer> cache;

  uint32_t h = hash(eb, sb);
  if (!cache.count(h)){
    uint64_t emax = maxExponent(eb).getUnsigned64();
    cache[h] = (Integer::pow2(sb)-1) * Integer::pow2(emax-sb+1);
    // = (2-pow2(1-sb) * pow2(emax)
  }
  return cache[h];
}

// Cf. HoFPA(2nd) Prop. 2.1
Integer maxValueExt(uint32_t eb, uint32_t sb)
{
  static std::unordered_map<uint32_t, Integer> cache;

  uint32_t h = hash(eb, sb);
  if (!cache.count(h)){
    uint64_t emax = maxExponent(eb).getUnsigned64();
    cache[h] = (Integer::pow2(sb+1)-1) * Integer::pow2(emax-sb);
    // = (2-pow2(1-sb-1) * pow2(emax)
  }
  return cache[h];
}

/** Return the smallest positive normal number.
 */
Rational minNormal(uint32_t eb, uint32_t sb)
{
  static std::unordered_map<uint32_t, Rational> cache;

  uint32_t h = hash(eb, sb);
  if (!cache.count(h)){
    uint64_t eminNeg = (-minExponent(eb)).getUnsigned64();
    Integer d = Integer::pow2(eminNeg);
    cache[h] = Rational(d).inverse();
  }
  return cache[h];
}

/** Return the smallest positive subnormal number.
 */
Rational minSubnormal(uint32_t eb, uint32_t sb)
{
  static std::unordered_map<uint32_t, Rational> cache;

  uint32_t h = hash(eb, sb);
  if (!cache.count(h)){
    uint64_t eminNeg = (-minExponent(eb)).getUnsigned64();
    Integer d = Integer::pow2(eminNeg+sb-1);
    cache[h] = Rational(d).inverse();
  }
  return cache[h];
}

/** Get the negative zero.
 */
Rational minusZero(uint32_t eb, uint32_t sb)
{
  Rational v = minSubnormal(eb,sb);
  return Rational(-v.getNumerator(), v.getDenominator() + 1);
}

/** Get the possitive zero.
 */
Rational plusZero(uint32_t eb, uint32_t sb)
{
  return Rational(0);
}

/** Get the negative infinity.
 */
Rational minusInfinity(uint32_t eb, uint32_t sb)
{
  Rational v = maxValue(eb,sb);
  return Rational(-v.getNumerator() * 3 - 1, 3);
}

/** Get the possitive infinity.
 */
Rational plusInfinity(uint32_t eb, uint32_t sb)
{
  Rational v = maxValue(eb,sb);
  return Rational(v.getNumerator() * 3 + 1, 3);
}

/** Get the NaN.
 */
Rational notANumber(uint32_t eb, uint32_t sb)
{
  Rational v = maxValue(eb,sb);
  return Rational(-v.getNumerator() * 3 - 2, 3);
}

bool isNormal(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return isFinite(eb, sb, arg) && arg.abs() >= minNormal(eb,sb);
}

bool isSubnormal(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return minSubnormal(eb,sb) <= arg.abs() && arg.abs() < minNormal(eb,sb);
}

bool isZero(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return (arg == minusZero(eb, sb)) || (arg == plusZero(eb, sb));
}

//bool inRange(uint32_t eb, uint32_t sb, const Rational& arg)
//{
//  return Rational(-maxValue(eb,sb)) <= arg && arg <= Rational(maxValue(eb,sb));
//}

bool isFinite(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return Rational(-maxValue(eb,sb)) <= arg && arg <= Rational(maxValue(eb,sb));
}

/** Check if the infinity values.
 */
bool isInfinite(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return arg == minusInfinity(eb,sb) || plusInfinity(eb,sb) == arg;
}

/** Check weakly if the infinity values.
 */
bool isInfiniteWeak(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return (arg < Rational(-maxValue(eb,sb)) || Rational(maxValue(eb,sb)) < arg)
    && arg != notANumber(eb,sb);
}

/** Check weakly if the negative infinity.
 */
bool isNegInfWeak(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return arg < Rational(-maxValue(eb,sb)) && arg != notANumber(eb,sb);
}

/** Check weakly if the possitive infinity.
 */
bool isPosInfWeak(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return arg > Rational(maxValue(eb,sb)) && arg != notANumber(eb,sb);
}

bool isNan(uint32_t eb, uint32_t sb, const Rational& arg)
{
  return arg == notANumber(eb,sb);
}

bool noOverflow(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& arg)
{
  // TODO
  //return isFinite(eb,sb, round(eb,sb, rm, arg));

  if (arg == notANumber(eb,sb)){
    return false;
  } else if (rm == IRM::TN){
    return Rational(-maxValue(eb,sb)) <= arg;
  } else if (rm == IRM::TP){
    return arg <= Rational(maxValue(eb,sb));
  } else if (rm == IRM::NE || rm == IRM::NA){
    Rational max = maxValueExt(eb,sb);
    return -max < arg && arg < max;
  } else if (rm == IRM::TZ){
    return true;
  }
  Assert(false) << "unreachable branch";
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

  Trace("rfp-round-eval") << "rm: " << int(rm) << std::endl;
  Trace("rfp-round-eval") << "v0: " << value << std::endl;

  //if (value.isZero())
  if (isZero(eb,sb, value) || isInfinite(eb,sb, value) || isNan(eb,sb, value))
    return value;
  else if (toInt && value == minusZero(eb,sb)) // -0
    return value;
  else if (value.abs() == normalMax)
    return value;
  else if (toInt && value.abs() > normalMax) // -+oo, NaN
    return value;
  else if (value.abs() > normalMax){
    if (value.sgn() > 0){
      if (rm == IRM::TN || rm == IRM::TNS || rm == IRM::TZ)
        return normalMax;
      else if (rm == IRM::TPS && value > plusInfinity(eb,sb))
        return value;
      else
        //return normalMax+1; //value;
        return plusInfinity(eb,sb);
    }else{ // value.sgn() < 0
      if (rm == IRM::TP || rm == IRM::TPS || rm == IRM::TZ)
        return -normalMax;
      else if (rm == IRM::TNS && value < minusInfinity(eb,sb))
        return value;
      else
        //return -normalMax-1; //value;
        return minusInfinity(eb,sb); //value;
    }
  }else if ( value.sgn() > 0 && (
             (rm == IRM::NE && value <= snMin/2)
          || (rm == IRM::NA && value < snMin/2)
          || (rm == IRM::TN && value < snMin)
          || (rm == IRM::TNS && value < snMin)
          || (rm == IRM::TZ && value < snMin) )){
    return Rational(0);
  }else if ( value.sgn() < 0 && (
             (rm == IRM::NE && value >= -snMin/2)
          || (rm == IRM::NA && value > -snMin/2)
          || (rm == IRM::TP && value > -snMin)
          || (rm == IRM::TZ && value > -snMin) )){
    return minusZero(eb,sb);
  }else if ( value.sgn() < 0 && 
             (rm == IRM::TPS && value > -snMin) ){
    return Rational(0);
  }else if ( ( (rm == IRM::TP || rm == IRM::TPS) 
               && value.sgn() > 0 && value <= snMin )
             || value == snMin ){
    return snMin;
  }else if ( ( (rm == IRM::TN || rm == IRM::TNS) 
               && value.sgn() <  0 && value >= -snMin )
             || value == -snMin ){
    return -snMin;
  }

  Assert(value.abs() < normalMax);

  Rational r = value;
  Trace("rfp-round-eval") << "r0: " << r << std::endl;

  //Rational ee = r.pow2Lower();

  int l2r = r.ilog2();
  Rational ee;
  if (l2r >= 0){
    ee = Integer::pow2(l2r);
  }else{
    ee = Rational(1, Integer::pow2(-l2r));
  }

  Trace("rfp-round-eval") << "ee: " << ee << std::endl;

  if (!toInt){
    if (ee < eeMin) ee = eeMin;
    r /= ee;
    r *= mMax;
  }

  if (rm == IRM::TP || rm == IRM::TPS){
    r = r.ceiling();
  }else if (rm == IRM::TN || rm == IRM::TNS){
    r = r.floor();
  }else if (rm == IRM::TZ){
    if (r.sgn() >= 0)
      r = r.floor();
    else
      r = -((-r).floor());
  }else if (rm == IRM::NE){
    Integer i1 = (r+Rational(1,2)).floor();
    Integer i2 = (r-Rational(1,2)).ceiling();
    if (i1 == i2 || i1.modByPow2(1) == 0)
      r = i1;
    else
      r = i2;
  }else if (rm == IRM::NA){
    if (r.sgn() >= 0){
      r += Rational(1,2);
      r = r.floor();
    }else{
      r -= Rational(1,2);
      r = r.ceiling();
    }
  }

  if (!toInt){
    r /= mMax;
    r *= ee;
  // TODO }else if (toInt && r.isZero() && value.sgn() < 0){
  }else if (r.isZero() && value.sgn() < 0){
    r = minusZero(eb,sb);
  }
  return r;
}

/** Round to real representation of FP numbers.
 */
Rational round(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& value)
{
  Rational r = roundInternal(false, eb, sb, rm, value);
  Trace("rfp-round-eval") << "rv: " << r << std::endl;
  return r;
}
/** Round to integer.
 */
Integer roundToInteger(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& value)
{
  return roundInternal(true, eb, sb, rm, value).getNumerator();
}

/** Convert a FloatingPoint value to the corresponding real representation.
 */
Rational convertFPToReal(const FloatingPoint& arg)
{
  uint32_t eb = arg.getSize().exponentWidth();
  uint32_t sb = arg.getSize().significandWidth();

  if (arg.isZero())
  {
    if (arg.isNegative())
      return minusZero(eb,sb);
    else
      return plusZero(eb,sb);
  }
  else if (arg.isInfinite())
  {
    if (arg.isNegative())
      return minusInfinity(eb,sb);
    else
      return plusInfinity(eb,sb);
  }
  else if (arg.isNaN())
  {
    return notANumber(eb,sb);
  }

  // delegate to the standard implementation
  return arg.convertToRationalTotal(0);
}

/** Convert a real representation to a FloatingPoint value.
 */
FloatingPoint convertToFP(uint32_t eb, uint32_t sb, const Rational& arg)
{
  FloatingPointSize size(eb, sb);

  if (isZero(eb,sb, arg))
  {
    return FloatingPoint::makeZero(size, arg < 0);
  }
  else if (isInfinite(eb,sb, arg))
  {
    return FloatingPoint::makeInf(size, arg < 0);
  }
  else if (arg == notANumber(eb,sb))
  {
    return FloatingPoint::makeNaN(size);
  }

  // Construct a finite floating-point number.
  return FloatingPoint(size, RoundingMode::ROUND_NEAREST_TIES_TO_EVEN, arg);
}

}  // namespace RealFloatingPoint

namespace RFP = RealFloatingPoint;

std::ostream& operator<<(std::ostream& os, const AbstractRFP& v)
{
  if (v == RFP::notANumber(v.d_eb, v.d_sb))
    return os << "NaN";
  else
  {
    os << (v < 0 ? '-' : '+');

    if (RFP::isInfinite(v.d_eb, v.d_sb, v))
      return os << "oo";
    else if (!RFP::isFinite(v.d_eb, v.d_sb, v))
      return os << "L";
    else if (v.abs() == RFP::maxValue(v.d_eb, v.d_sb))
      return os << "M";
    else if (v.abs() > RFP::maxValue(v.d_eb, v.d_sb))
      return os << "MW";
    else if (RFP::isZero(v.d_eb, v.d_sb, v))
      return os << "0";
    else if (RFP::isSubnormal(v.d_eb, v.d_sb, v))
      return os << "SN";
    else if (-RFP::minSubnormal(v.d_eb,v.d_sb) < v && 
             v < RFP::minSubnormal(v.d_eb,v.d_sb))
      return os << "SNW";
    else if (RFP::isSubnormal(v.d_eb, v.d_sb, v))
      return os << "SN";
    else // isNormal
      return os << "N";
  }
}

}  // namespace cvc5::internal
