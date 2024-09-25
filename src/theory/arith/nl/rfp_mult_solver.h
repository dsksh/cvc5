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
 * Basic solver class for rfp mult and div operators.
 */

#ifndef CVC5__THEORY__ARITH__NL__RFP_MULT_SOLVER_H
#define CVC5__THEORY__ARITH__NL__RFP_MULT_SOLVER_H

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

/** RFP solver class for mult and div
 */
class RfpMultSolver : public RfpSolver
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  RfpMultSolver(Env& env, InferenceManager& im, NlModel& model);
  virtual ~RfpMultSolver() override;

  /** is target ?
   * 
   * Return if the node is a target of the solver.
   */
  bool isTarget(const Node& node) override;

  ///** init last call
  // *
  // * This is called at the beginning of last call effort check, where
  // * assertions are the set of assertions belonging to arithmetic,
  // * false_asserts is the subset of assertions that are false in the current
  // * model, and xts is the set of extended function terms that are active in
  // * the current context.
  // */
  //void initLastCall(const std::vector<Node>& assertions,
  //                  const std::vector<Node>& false_asserts,
  //                  const std::vector<Node>& xts) override;
  //-------------------------------------------- lemma schemas
  ///** check initial refine
  // *
  // * This should be a heuristic incomplete check that only introduces a
  // * small number of new terms in the lemmas it returns.
  // */
  //void checkInitialRefine() override;
  ///** check full refine
  // *
  // * This should be a complete check that returns at least one lemma to
  // * rule out the current model.
  // */
  //void checkFullRefine() override;

  ///** check value refine
  // */
  //void checkValueRefine();

  //-------------------------------------------- end lemma schemas
 protected:
  //// The inference manager that we push conflicts and lemmas to.
  //InferenceManager& d_im;
  ///** Reference to the non-linear model object */
  //NlModel& d_model;

  ///** Terms that have been given initial refinement lemmas */
  //NodeSet d_initRefine;
  ///** Term data */
  //std::map<Kind, std::map<unsigned, std::vector<Node> > > d_terms;

  //void checkFullRefineValue(Node n);

  void checkInitialRefineMult(Node n) override;
  void checkAuxRefineMult(Node n) override;
  //void checkValueRefineMult(Node n);
  void checkInitialRefineDiv(Node n) override;
  void checkAuxRefineDiv(Node n) override;

  bool optionalValueRefineCond(const Node& n) override;

}; /* class RfpMultSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_MULT_SOLVER_H */
