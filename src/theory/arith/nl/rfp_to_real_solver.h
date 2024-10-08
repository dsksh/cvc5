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
 * Solver class for the rfp.to_real operator.
 */

#ifndef CVC5__THEORY__ARITH__NL__RFP_TO_REAL_SOLVER_H
#define CVC5__THEORY__ARITH__NL__RFP_TO_REAL_SOLVER_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/theory_state.h"
#include "theory/arith/nl/rfp_solver.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;

namespace nl {

class NlModel;

/** RFP solver class for rfp.to_real
 */
class RfpToRealSolver : public RfpSolver 
{
 public:
  RfpToRealSolver(Env& env, InferenceManager& im, NlModel& model);
  virtual ~RfpToRealSolver();

  /** is target ?
   * 
   * Return if the node is a target of the solver.
   */
  bool isTarget(const Node& node) override;

 protected:
  void checkInitialRefineToReal(Node n) override;
  void checkAuxRefineToReal(Node n) override;

}; /* class RfpToRealSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_TO_REAL_SOLVER_H */
