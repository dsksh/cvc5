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
 * The integer representation of FP rounding modes.
 */

#include "cvc5_public.h"

#ifndef CVC5__INT_ROUNDINGMODE_H
#define CVC5__INT_ROUNDINGMODE_H

#include <iosfwd>

#include "base/exception.h"
//#include "util/integer.h"
#include "util/roundingmode.h"

namespace cvc5::internal {

struct IntRoundingMode
{
  static const uint8_t NE = 0;
  static const uint8_t NA = 1;
  static const uint8_t TP = 2;
  static const uint8_t TN = 3;
  static const uint8_t TZ = 4;
  static const uint8_t TPS = 5;
  static const uint8_t TNS = 6;

  static uint8_t convert(const RoundingMode& rm)
  {
    if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_EVEN)
      return 0;
    else if (rm == RoundingMode::ROUND_NEAREST_TIES_TO_AWAY)
      return 1;
    else if (rm == RoundingMode::ROUND_TOWARD_POSITIVE)
      return 2;
    else if (rm == RoundingMode::ROUND_TOWARD_NEGATIVE)
      return 3;
    else if (rm == RoundingMode::ROUND_TOWARD_ZERO)
      return 4;
    Assert(false);
  }
};

}  // namespace cvc5::internal

#endif /* CVC5__INT_ROUNDINGMODE_H */
