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
 * The real version of the FP rounding operator.
 */

#include "cvc5_public.h"

#ifndef CVC5__RFP_ROUND_H
#define CVC5__RFP_ROUND_H

#include <iosfwd>

#include "base/exception.h"
//#include "util/integer.h"

namespace cvc5::internal {

struct RfpRound
{
  uint32_t d_eb;
  uint32_t d_sb;
  RfpRound(uint32_t eb, uint32_t sb) : d_eb(eb), d_sb(sb) {}
  uint32_t hash() const { return d_eb * 19 + d_sb; }
  operator uint32_t() const { return hash(); }
}; /* struct RfpRound */

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os, const RfpRound& t);
inline std::ostream& operator<<(std::ostream& os, const RfpRound& t)
{
  return os << "(_ rfp-round " << t.d_eb << " " << t.d_sb << ")";
}

}  // namespace cvc5::internal

#endif /* CVC5__RFP_ROUND_H */
