/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for t.pow constraints.
 */

#ifndef CVC5__THEORY__ARITH__NL__T_POW_SOLVER_H
#define CVC5__THEORY__ARITH__NL__T_POW_SOLVER_H

#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;

namespace nl {

class NlModel;

/** t.pow solver class
 *
 */
class TPowSolver : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  TPowSolver(Env& env, InferenceManager& im, NlModel& model);
  ~TPowSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   */
  void initLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts);
  //-------------------------------------------- lemma schemas
  /** check initial refine
   *
   * Returns a set of valid theory lemmas, based on simple facts about t.pow.
   *
   * Examples
   *
   * x >= 1 --> x <= t.pow(x)
   *
   * This should be a heuristic incomplete check that only introduces a
   * small number of new terms in the lemmas it returns.
   */
  void checkInitialRefine();
  /** check full refine
   *
   * This should be a complete check that returns at least one lemma to
   * rule out the current model.
   */
  void checkFullRefine();

  /** sort d_terms according to their values in the current model */
  void sortTermsBasedOnModel();

  //-------------------------------------------- end lemma schemas
 private:
  // The inference manager that we push conflicts and lemmas to.
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** commonly used terms */
  Node d_false;
  Node d_true;
  Node d_zero;
  Node d_one;
  Node d_two;

  NodeSet d_initRefine;
  /** all t.pow terms
   * Cleared at each last call effort check.
   * */
  std::vector<Node> d_terms;

  /**
   * Value-based refinement lemma for i of the form ((_ t.pow n) x). Returns:
   *   x = M(x) /\ x >= 0 ---->
   *     ((_ t.pow n) x) = rewrite(((_ t.pow n) M(x)))
   */
  Node valueBasedLemma(Node i);
}; /* class TPowSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__T_POW_SOLVER_H */
