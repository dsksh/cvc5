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
inline static Integer maxExponent(uint32_t size)
{
  return Integer((2<<(size-2)) - 1);
}
/** Get the minimum value of exponent.
 */
inline static Integer minExponent(uint32_t size)
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

/**
 * Convert a FloatingPoint value to the corresponding real representation.
 */
Rational convertFPToReal(const FloatingPoint& arg);
/** 
 * Convert a real representation to a FloatingPoint value.
 */
FloatingPoint convertToFP(uint32_t eb, uint32_t sb, const Rational& arg);

///**
// * Addition.
// */
//Rational add(uint32_t eb, uint32_t sb, uint8_t rm, const Rational& arg1, const Rational& arg2);

}  // namespace RealFloatingPoint

/**
 * The parameter type for the operations on RFP values.
 */
class RfpOperation
{
 public:
  /** Constructors. */
  RfpOperation(uint32_t _e, uint32_t _s) : d_fp_size(_e, _s) {}
  RfpOperation(const FloatingPointSize& fps) : d_fp_size(fps) {}
  virtual ~RfpOperation() {}

  /** Operator overload for comparison of conversion sorts. */
  bool operator==(const RfpOperation& t) const
  {
    return d_fp_size == t.d_fp_size;
  }

  operator size_t() const 
  { 
    FloatingPointSizeHashFunction f;
    //return f(d_fp_size) ^ (0x00005300 | (key << 24));
    return f(d_fp_size);
  }

  /** Return the size of this RFP convert sort. */
  FloatingPointSize getSize() const { return d_fp_size; }

  /** Return the name. */
  virtual std::string getName() const = 0;

  /** Print the operator. */
  std::ostream& print(std::ostream& os) const
  {
    return os << "(_ rfp." << getName() << " " 
              << d_fp_size.exponentWidth() 
              << d_fp_size.significandWidth() << ")";
  }

 private:
  /** The floating-point size of this sort. */
  FloatingPointSize d_fp_size;
}; /* class RfpOperation*/

class RfpToFP : public RfpOperation
{
// public:
  //RfpToFP(uint32_t _e, uint32_t _s) : RfpOperation(_e, _s) {}
  //RfpToFP(const FloatingPointSize& fps) : RfpOperation(fps) {}
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "to_fp"; }
};

class RfpRound : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "round"; }
};

class RfpAdd : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "add"; }
};

/** Output stream operator overloading for RFP operation sorts. */
inline std::ostream& operator<<(std::ostream& os, const RfpOperation& t)
{
  return t.print(os);
}

}  // namespace cvc5::internal

#endif /* CVC5__REAL_FLOATINGPOINT_H */
