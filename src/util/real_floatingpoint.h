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
  return Integer(Integer(1) - maxExponent(size));
}

/** Get the maximum normal value.
 */
Integer maxValue(uint32_t eb, uint32_t sb);

Integer maxValueExt(uint32_t eb, uint32_t sb);

/** Return the smallest positive normal number.
 */
Rational minNormal(uint32_t eb, uint32_t sb);

/** Return the smallest positive subnormal number.
 */
Rational minSubnormal(uint32_t eb, uint32_t sb);

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

/** Check if the infinity values.
 */
bool isInfinite(uint32_t eb, uint32_t sb, const Rational& arg);
bool isInfiniteWeak(uint32_t eb, uint32_t sb, const Rational& arg);

/** Check weakly if the negative infinity.
 */
bool isNegInfWeak(uint32_t eb, uint32_t sb, const Rational& arg);

/** Check weakly if the possitive infinity.
 */
bool isPosInfWeak(uint32_t eb, uint32_t sb, const Rational& arg);

bool isNan(uint32_t eb, uint32_t sb, const Rational& arg);
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

}  // namespace RealFloatingPoint

/**
 * The parameter type for the accurate operations on RFP values.
 */
class RfpOperation
{
 public:
  /** Constructors. */
  /** Constructors. */
  RfpOperation(uint32_t _e, uint32_t _s) : d_fpSize(_e, _s) {}
  RfpOperation(const FloatingPointSize& fps) : d_fpSize(fps) {}
  virtual ~RfpOperation() {}

  /** Operator overload for comparison of conversion sorts. */
  virtual bool operator==(const RfpOperation& t) const
  {
    return getSize() == t.getSize();
  }

  virtual operator size_t() const
  { 
    FloatingPointSizeHashFunction f;
    //return f(d_fpSize) ^ (0x00005300 | (key << 24));
    return f(d_fpSize);
  }

  /** Return the size of this RFP convert sort. */
  FloatingPointSize getSize() const { return d_fpSize; }

  /** Return the name. */
  virtual std::string getName() const = 0;

  /** Print the operator. */
  std::ostream& print(std::ostream& os) const
  {
    return os << "(_ rfp." << getName() << " " 
              << d_fpSize.exponentWidth() << " "
              << d_fpSize.significandWidth() << ") ";
  }

 private:
  /** The floating-point size of this sort. */
  FloatingPointSize d_fpSize;
}; /* class RfpOperation*/

class RfpToRfpFromRfp : public RfpOperation
{
 public:
  RfpToRfpFromRfp(uint32_t _e0, uint32_t _s0, uint32_t _e, uint32_t _s) 
  : RfpOperation(_e, _s), d_srcFpSize(_e0, _s0) {}
  virtual ~RfpToRfpFromRfp() {}

  /** Operator overload for comparison of conversion sorts. */
  bool operator==(const RfpToRfpFromRfp& t) const
  {
    return RfpOperation::operator==(t) 
      && getSrcSize() == t.getSrcSize();
  }

  operator size_t() const override
  { 
    // TODO
    FloatingPointSizeHashFunction f;
    return f(getSize()) + 7 * f(d_srcFpSize);
  }

  /** Return the size of this RFP convert sort. */
  FloatingPointSize getSrcSize() const
  { 
    return d_srcFpSize; 
  }

  /** Return the name. */
  std::string getName() const override { return "to_rfp"; }

 private:
  /** The size of the source floating-point sort. */
  FloatingPointSize d_srcFpSize;
};

class RfpToFP : public RfpOperation
{
// public:
  //RfpToFP(uint32_t _e, uint32_t _s) : RfpOperation(_e, _s) {}
  //RfpToFP(const FloatingPointSize& fps) : RfpOperation(fps) {}
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "to_fp"; }
};

class RfpToReal : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "to_real"; }
};

class RfpIsNormal : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "isNormal"; }
};

class RfpIsSubnormal : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "isSubnormal"; }
};

class RfpIsZero : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "isZero"; }
};

class RfpIsInf : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "isInfinite"; }
};

class RfpIsNan : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "isNaN"; }
};

class RfpIsNeg : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "isNegative"; }
};

class RfpIsPos : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "isPositive"; }
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

class RfpSub : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "sub"; }
};

class RfpNeg : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "neg"; }
};

class RfpMult : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "mul"; }
};

class RfpDiv : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "div"; }
};

class RfpEq : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "eq"; }
};

class RfpLt : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "lt"; }
};

class RfpLeq : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "leq"; }
};

class RfpGt : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "gt"; }
};

class RfpGeq : public RfpOperation
{
  using RfpOperation::RfpOperation;

  /** Return the name. */
  std::string getName() const override { return "geq"; }
};

/** Output stream operator overloading for RFP operation sorts. */
inline std::ostream& operator<<(std::ostream& os, const RfpOperation& t)
{
  return t.print(os);
}

/**
 * 
 */
class AbstractRFP : public Rational
{
 public:
  AbstractRFP(uint32_t eb, uint32_t sb, const Rational& v) 
  : Rational(v), d_eb(eb), d_sb(sb) {}

  friend std::ostream& operator<<(std::ostream& os, const AbstractRFP& v);

 private:
  uint32_t d_eb;
  uint32_t d_sb;
};

std::ostream& operator<<(std::ostream& os, const AbstractRFP& v);

}  // namespace cvc5::internal

#endif /* CVC5__REAL_FLOATINGPOINT_H */
