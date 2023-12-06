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
 * The real version of the fp.add operator.
 */

#include "cvc5_public.h"

#ifndef CVC5__RFP_ADD_H
#define CVC5__RFP_ADD_H

#include <iosfwd>

#include "base/exception.h"

namespace cvc5::internal {

struct RfpAdd
{
  uint32_t d_eb;
  uint32_t d_sb;
  RfpAdd(uint32_t eb, uint32_t sb) : d_eb(eb), d_sb(sb) {}
  uint32_t hash() const { return d_eb * 19 + d_sb; }
  operator uint32_t() const { return hash(); }
}; /* struct RfpAdd */

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os, const RfpAdd& t);
inline std::ostream& operator<<(std::ostream& os, const RfpAdd& t)
{
  return os << "(_ rfp.add " << t.d_eb << " " << t.d_sb << ")";
}

}  // namespace cvc5::internal

#endif /* CVC5__RFP_ADD_H */
