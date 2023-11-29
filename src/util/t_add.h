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
 * A trial add operator.
 */

#include "cvc5_public.h"

#ifndef CVC5__T_ADD_H
#define CVC5__T_ADD_H

#include <iosfwd>

#include "base/exception.h"
#include "util/rational.h"

namespace cvc5::internal {

struct TAdd
{
  Rational d_arg;
  TAdd(Rational arg) : d_arg(arg) {}
  operator uint32_t() const { return d_arg.hash(); }
}; /* struct TAdd */

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os, const TAdd& ia);
inline std::ostream& operator<<(std::ostream& os, const TAdd& ia)
{
  return os << "(_ t.add " << ia.d_arg << ")";
}

}  // namespace cvc5::internal

#endif /* CVC5__T_ADD_H */
