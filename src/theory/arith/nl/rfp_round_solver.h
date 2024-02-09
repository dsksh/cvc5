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
 * Solver for real-valued FP rounding operators.
 */

#ifndef CVC5__THEORY__ARITH__NL__RFP_ROUND_SOLVER_H
#define CVC5__THEORY__ARITH__NL__RFP_ROUND_SOLVER_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;

namespace nl {

class NlModel;

/** Real-valued FP round solver class
 *
 */
class RfpRoundSolver : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  RfpRoundSolver(Env& env, InferenceManager& im, NlModel& model);
  ~RfpRoundSolver();

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
   * Returns a set of valid theory lemmas, based on simple facts about RFP_ROUND.
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

  /** RFP_ROUND terms that have been given initial refinement lemmas */
  NodeSet d_initRefine;
  /** all RFP_ROUND terms */
  std::map<unsigned, std::vector<Node> > d_rounds;
  /** all RFP_TO_RFP terms */
  std::map<unsigned, std::vector<Node> > d_toRfps;

  /**
   * 
   */
  void checkFullRefineRound(TNode node, 
    const Integer& rm, const Rational& arg, const Rational& round);

  /**
   * 
   */
  void checkFullRefineRoundPair(TNode node1, 
    const Integer& rm1, const Rational& arg1, const Rational& round1,
    TNode node2, 
    const Integer& rm2, const Rational& arg2, const Rational& round2);

  /**
   * Value-based refinement lemma for t of the form ((_ rfp.round eb sb) rm arg). Returns:
   *   rm = M(rm) ^ arg = M(arg) =>
   *     ((_ rfp.round eb sb) rm arg) = rewrite(((_ rfp.round eb sb) M(rm) M(arg)))
   */
  Node valueBasedLemma(Node i);

}; /* class RfpRoundSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_ROUND_SOLVER_H */
