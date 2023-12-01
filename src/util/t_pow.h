/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A trial pow operator.
 */

#include "cvc5_public.h"

#ifndef CVC5__T_POW_H
#define CVC5__T_POW_H

#include <iosfwd>

#include "base/exception.h"
#include "util/rational.h"

namespace cvc5::internal {

struct TPow
{
  uint32_t d_exp;
  TPow(uint32_t exp) : d_exp(exp) {}
  operator uint32_t() const { return d_exp; }
}; /* struct TPow */

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os, const TPow& ia);
inline std::ostream& operator<<(std::ostream& os, const TPow& ia)
{
  return os << "(_ t.pow " << ia.d_exp << ")";
}

}  // namespace cvc5::internal

#endif /* CVC5__T_POW_H */
