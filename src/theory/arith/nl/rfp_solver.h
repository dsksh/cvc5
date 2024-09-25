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

  enum InferKind { INITIAL, AUX, FULL };

 public:
  RfpSolver(Env& env, InferenceManager& im, NlModel& model);
  virtual ~RfpSolver();

  /** is target ?
   * 
   * Return if the node is a target of the solver.
   */
  virtual bool isTarget(const Node& node);

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
  virtual void checkInitialRefine();
  /** check aux refine
   */
  virtual void checkAuxRefine();
  /** check full refine
   *
   * This should be a complete check that returns at least one lemma to
   * rule out the current model.
   */
  virtual void checkFullRefine();

  //-------------------------------------------- end lemma schemas
 protected:
  // The inference manager that we push conflicts and lemmas to.
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;

  /** Terms that have been given initial refinement lemmas */
  NodeSet d_initRefine;
  /** Term data */
  std::map<Kind, std::map<unsigned, std::vector<Node> > > d_terms;

  //template<Kind K>
  //void checkFullRefineBody(Node n);

  /** process terms
   * 
   * Main loop of the checking process.
   */
  void processTerms(InferKind iKind);
  void checkInitialRefineBody(Node node);
  void checkAuxRefineBody(Node node);
  void checkFullRefineBody(Node node);

  virtual void checkInitialRefineAdd(Node n);
  virtual void checkAuxRefineAdd(Node n);
  virtual void checkInitialRefineNeg(Node n);
  virtual void checkAuxRefineNeg(Node n);
  virtual void checkInitialRefineSub(Node n);
  virtual void checkAuxRefineSub(Node n);
  virtual void checkInitialRefineMult(Node n);
  virtual void checkAuxRefineMult(Node n);
  virtual void checkValueRefineMult(Node n) {}
  virtual void checkInitialRefineDiv(Node n);
  virtual void checkAuxRefineDiv(Node n);
  virtual void checkInitialRefineGt(Node n);
  virtual void checkAuxRefineGt(Node n);
  virtual void checkInitialRefineGeq(Node n);
  virtual void checkAuxRefineGeq(Node n);
  virtual void checkInitialRefineRound(Node n);
  virtual void checkAuxRefineRound(Node n);
  virtual void checkInitialRefineToReal(Node n);
  virtual void checkAuxRefineToReal(Node n);
  virtual void checkInitialRefineToRfp(Node n);
  virtual void checkAuxRefineToRfp(Node n);

  virtual void checkFullRefineUnOp(const FloatingPointSize& sz, Node n);
  virtual void checkFullRefineBinOp(const FloatingPointSize& sz, Node n);
  virtual void checkFullRefineRound(const FloatingPointSize& sz, Node n);
  virtual void checkFullRefineRelOp(const FloatingPointSize& sz, Node n);
  virtual bool optionalValueRefineCond(const Node& n);

  ///** Value-based refinement lemma for the arithmetic operators.
  // */
  //Node opValueBasedLemma(TNode i);
  ///** Value-based refinement lemma for the relational operators.
  // */
  //virtual Node relValueBasedLemma(TNode i);

  template<class K>
  FloatingPointSize getSize(const Node& n)
  {
    return n.getOperator().getConst<K>().getSize();
  }

}; /* class RfpSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__RFP_SOLVER_H */
