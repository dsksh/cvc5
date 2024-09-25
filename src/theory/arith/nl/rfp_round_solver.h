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
 * Solver class for the rfp.round operator.
 */

#ifndef CVC5__THEORY__ARITH__NL__RFP_ROUND_SOLVER_H
#define CVC5__THEORY__ARITH__NL__RFP_ROUND_SOLVER_H

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
class ExtState;

/** RFP solver class for rfp.round
 */
class RfpRoundSolver : public RfpSolver 
{
 public:
  RfpRoundSolver(Env& env, InferenceManager& im, NlModel& model, ExtState* data);
  virtual ~RfpRoundSolver();

  /** is target ?
   * 
   * Return if the node is a target of the solver.
   */
  bool isTarget(const Node& node) override;

 protected:
  void checkInitialRefineRound(Node n) override;
  void checkAuxRefineRound(Node n) override;
  void checkInitialRefineToRfp(Node n) override;
  void checkAuxRefineToRfp(Node n) override;
  void checkFullRefineRound(const FloatingPointSize& sz, Node n) override;

 private:
  /** Basic data of monomials shared with other checks */
  ExtState* d_data;

  /**
   * 
   */
  void checkRoundError(Rational err0,
                       Integer rm, Rational arg, Rational round, 
                       Node node, Node aRange,
                       bool isRelational = false);

}; /* class RfpRoundSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_ROUND_SOLVER_H */
