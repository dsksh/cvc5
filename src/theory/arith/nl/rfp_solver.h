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
 * Basic solver class for rfp operators.
 */

#ifndef CVC5__THEORY__ARITH__NL__RFP_SOLVER_H
#define CVC5__THEORY__ARITH__NL__RFP_SOLVER_H

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

/** Basic RFP solver class
 */
class RfpSolver : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  RfpSolver(Env& env, InferenceManager& im, NlModel& model);
  virtual ~RfpSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   */
  virtual void initLastCall(const std::vector<Node>& assertions,
                            const std::vector<Node>& false_asserts,
                            const std::vector<Node>& xts);
  //-------------------------------------------- lemma schemas
  /** check initial refine
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
 protected:
  // The inference manager that we push conflicts and lemmas to.
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** commonly used terms */
  Node d_false;
  Node d_true;
  Node d_zero;
  Node d_one;

  /** Terms that have been given initial refinement lemmas */
  NodeSet d_initRefine;
  /** Term data */
  std::map<Kind, std::map<unsigned, std::vector<Node> > > d_terms;

  //template<Kind K>
  //void checkFullRefineBody(Node n);

  ///** RFP kind */
  //virtual kind::Kind_t kind() = 0;
  ///** Size of the FP data. */
  //virtual FloatingPointSize getSize(TNode n) = 0;

  /** Value-based refinement lemma for the arithmetic operators.
   */
  Node opValueBasedLemma(Node i);
  /** Value-based refinement lemma for the relational operators.
   */
  Node relValueBasedLemma(Node i);

 //private:
  //Node mkFalse(Node i);
  //Node mkTrue(Node i);
  //Node mkIsFinite(uint32_t eb, uint32_t sb, Node x);
  //Node mkIsInf(uint32_t eb, uint32_t sb, Node x);
  //Node mkIsPos(uint32_t eb, uint32_t sb, Node x);
  //Node mkIsNeg(uint32_t eb, uint32_t sb, Node x);
  //Node mkSameSign(uint32_t eb, uint32_t sb, Node x, Node y);
  //Node mkDiffSign(uint32_t eb, uint32_t sb, Node x, Node y);
  //Node mkIsNegInf(uint32_t eb, uint32_t sb, Node x);
  //Node mkIsPosInf(uint32_t eb, uint32_t sb, Node x);
  //Node mkIsNan(uint32_t eb, uint32_t sb, Node x);

  void checkFullRefineValue(Node n);

  void checkInitialRefineAdd(Node n);
  void checkFullRefineAdd(Node n);
  void checkInitialRefineMult(Node n);
  void checkFullRefineMult(Node n);
  void checkInitialRefineLt(Node n);
  void checkFullRefineLt(Node n);
  void checkInitialRefineLeq(Node n);
  void checkFullRefineLeq(Node n);

}; /* class RfpSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_SOLVER_H */
