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
 * Basic solver class for rfp comparison operators.
 */

#ifndef CVC5__THEORY__ARITH__NL__RFP_COMP_SOLVER_H
#define CVC5__THEORY__ARITH__NL__RFP_COMP_SOLVER_H

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

/** Basic RFP solver class for comparison operators
 */
class RfpCompSolver : public RfpSolver
{
  //typedef context::CDHashSet<Node> NodeSet;

 public:
  RfpCompSolver(Env& env, InferenceManager& im, NlModel& model);
  virtual ~RfpCompSolver() override;

  /** is target ?
   * 
   * Return if the node is a target of the solver.
   */
  bool isTarget(const Node& node) override;

 protected:
  void checkInitialRefineGt(Node n) override;
  void checkAuxRefineGt(Node n) override;
  void checkInitialRefineGeq(Node n) override;
  void checkAuxRefineGeq(Node n) override;
  void checkFullRefineRelOp(const FloatingPointSize& sz, Node node) override;

  /** Value-based refinement lemma for the comparison operators.
   */
  //Node relValueBasedLemma(TNode i);

}; /* class RfpCompSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_COMP_SOLVER_H */
