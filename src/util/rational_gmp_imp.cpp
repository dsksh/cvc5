/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Christopher L. Conway, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A multi-precision rational constant.
 */
#include <cmath>
#include <sstream>
#include <string>

#include "base/cvc5config.h"
#include "util/rational.h"

#ifndef CVC5_GMP_IMP  // Make sure this comes after base/cvc5config.h
#error "This source should only ever be built if CVC5_GMP_IMP is on !"
#endif /* CVC5_GMP_IMP */

#include "base/check.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& os, const Rational& q){
  return os << q.toString();
}


/* Computes a rational given a decimal string. The rational
 * version of <code>xxx.yyy</code> is <code>xxxyyy/(10^3)</code>.
 */
Rational Rational::fromDecimal(const std::string& dec) {
  using std::string;
  // Find the decimal point, if there is one
  string::size_type i( dec.find(".") );
  if( i != string::npos ) {
    /* Erase the decimal point, so we have just the numerator. */
    Integer numerator( string(dec).erase(i,1) );

    /* Compute the denominator: 10 raise to the number of decimal places */
    int decPlaces = dec.size() - (i + 1);
    Integer denominator( Integer(10).pow(decPlaces) );

    return Rational( numerator, denominator );
  } else {
    /* No decimal point, assume it's just an integer. */
    return Rational( dec );
  }
}



/** Equivalent to calling (this->abs()).cmp(b.abs()) */
int Rational::absCmp(const Rational& q) const{
  const Rational& r = *this;
  int rsgn = r.sgn();
  int qsgn = q.sgn();
  if(rsgn == 0){
    return (qsgn == 0) ? 0 : -1;
  }else if(qsgn == 0){
    Assert(rsgn != 0);
    return 1;
  }else if((rsgn > 0) && (qsgn > 0)){
    return r.cmp(q);
  }else if((rsgn < 0) && (qsgn < 0)){
    // if r < q < 0, q.cmp(r) = +1, (r.abs()).cmp(q.abs()) = +1
    // if q < r < 0, q.cmp(r) = -1, (r.abs()).cmp(q.abs()) = -1
    // if q = r < 0, q.cmp(r) =  0, (r.abs()).cmp(q.abs()) =  0
    return q.cmp(r);
  }else if((rsgn < 0) && (qsgn > 0)){
    Rational rpos = -r;
    return rpos.cmp(q);
  }else {
    Assert(rsgn > 0 && (qsgn < 0));
    Rational qpos = -q;
    return r.cmp(qpos);
  }
}


Rational Rational::pow2Lower() const
{
  size_t l2_num = getNumerator().length();
  size_t l2_den = getDenominator().length();
  Rational res;
  if (l2_num == l2_den){
    Assert(sgn() != 0);
    if (abs() >= 1)
      res = 1; 
    else
      res = Rational(1,2);
  }else if (l2_num > l2_den){
    size_t e = l2_num - l2_den - 1;
    mpq_class v;
    mpq_mul_2exp(v.get_mpq_t(), mpq_class(1).get_mpq_t(), e);
    for (res = v; res * 2 < abs(); res *= 2) {}
  }else{ // l2_num < l2_den
    size_t e = l2_den - l2_num + 1;
    mpq_class v;
    mpq_div_2exp(v.get_mpq_t(), mpq_class(1).get_mpq_t(), e);
    for (res = v; res * 2 < abs(); res *= 2) {}
  }
  return res;
}


/** Return an exact rational for a double d. */
std::optional<Rational> Rational::fromDouble(double d)
{
  using namespace std;
  if(isfinite(d)){
    Rational q;
    mpq_set_d(q.d_value.get_mpq_t(), d);
    return q;
  }
  return std::optional<Rational>();
}

}  // namespace cvc5::internal
