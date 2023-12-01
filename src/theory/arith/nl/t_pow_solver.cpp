/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of t.pow solver.
 */

#include "theory/arith/nl/t_pow_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
//#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/t_pow.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

TPowSolver::TPowSolver(Env& env,
                       InferenceManager& im,
                       NlModel& model)
    : EnvObj(env), d_im(im), d_model(model), d_initRefine(userContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstReal(Rational(0));
  d_one = nm->mkConstReal(Rational(1));
  d_two = nm->mkConstReal(Rational(2));
}

TPowSolver::~TPowSolver() {}

void TPowSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  d_terms.clear();
  Trace("t.pow-mv") << "T_POW terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != T_POW)
    {
      // don't care about other terms
      continue;
    }
    d_terms.push_back(a);
  }
  Trace("t.pow") << "We have " << d_terms.size() << " t.pow terms." << std::endl;
}

void TPowSolver::checkInitialRefine()
{
  Trace("t.pow-check") << "TPowSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& i : d_terms)
  {
    if (d_initRefine.find(i) != d_initRefine.end())
    {
      // already sent initial axioms for i in this user context
      continue;
    }
    d_initRefine.insert(i);

    // initial refinement lemmas
    std::vector<Node> conj;

    // e = 0 -> x^e = 1
    uint32_t exp = i.getOperator().getConst<TPow>().d_exp;
    if (exp == 0)
      conj.push_back(nm->mkNode(EQUAL, i, d_one));
    else if (exp == 1)
      conj.push_back(nm->mkNode(EQUAL, i, i[0]));
    else
    {
      // lemma: x <= x^e whenever x >= 1
      Node assumption = nm->mkNode(LEQ, d_one, i[0]);
      Node conclusion = nm->mkNode(LEQ, i[0], i);
      conj.push_back(nm->mkNode(IMPLIES, assumption, conclusion));

      // lemmas: 0 <= x^e <= x whenever 0 <= x <= 1
      Node a1 = nm->mkNode(LEQ, d_zero, i[0]);
      Node a2 = nm->mkNode(LEQ, i[0], d_one);
      Node c1 = nm->mkNode(LEQ, i, i[0]);
      Node c2 = nm->mkNode(LEQ, d_zero, i);
      conj.push_back(nm->mkNode(IMPLIES, nm->mkNode(AND, a1, a2), nm->mkNode(AND, c1, c2)));

      if (exp > 0)
      {
        // lemma: x <= x^e whenever x <= -1
        assumption = nm->mkNode(LEQ, i[0], nm->mkNode(NEG, d_one));
        conclusion = nm->mkNode(LEQ, i[0], i);
        conj.push_back(nm->mkNode(IMPLIES, assumption, conclusion));

        // lemmas: 0 <= x^e <= x whenever -1 <= x <= 0
        a1 = nm->mkNode(LEQ, i[0], d_zero);
        a2 = nm->mkNode(LEQ, nm->mkNode(NEG, d_one), i[0]);
        c1 = nm->mkNode(LEQ, i, i[0]);
        c2 = nm->mkNode(LEQ, d_zero, i);
        conj.push_back(nm->mkNode(IMPLIES, nm->mkNode(AND, a1, a2), nm->mkNode(AND, c1, c2)));
      }
      else
      {
        // lemma: x^e <= x whenever x <= -1
        assumption = nm->mkNode(LEQ, i[0], nm->mkNode(NEG, d_one));
        conclusion = nm->mkNode(LEQ, i, i[0]);
        conj.push_back(nm->mkNode(IMPLIES, assumption, conclusion));

        // lemmas: x <= x^e <= 0 whenever -1 <= x <= 0
        a1 = nm->mkNode(LEQ, i[0], d_zero);
        a2 = nm->mkNode(LEQ, nm->mkNode(NEG, d_one), i[0]);
        c1 = nm->mkNode(LEQ, i[0], i);
        c2 = nm->mkNode(LEQ, i, d_zero);
        conj.push_back(nm->mkNode(IMPLIES, nm->mkNode(AND, a1, a2), nm->mkNode(AND, c1, c2)));
      }
    }

    Node lem = nm->mkAnd(conj);
    Trace("t.pow-lemma") << "TPowSolver::Lemma: " << lem << " ; INIT_REFINE"
                         << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_T_POW_INIT_REFINE);
  }
}

void TPowSolver::sortTermsBasedOnModel()
{
  struct
  {
    bool operator()(Node a, Node b, NlModel& model) const
    {
      return model.computeConcreteModelValue(a[0])
             < model.computeConcreteModelValue(b[0]);
    }
  } modelSort;
  using namespace std::placeholders;
  std::sort(
      d_terms.begin(), d_terms.end(), std::bind(modelSort, _1, _2, d_model));
}

void TPowSolver::checkFullRefine()
{
  Trace("t.pow-check") << "TPowSolver::checkFullRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  sortTermsBasedOnModel();
  // add lemmas for each t.pow term
  for (uint64_t i = 0, size = d_terms.size(); i < size; i++)
  {
    Node n = d_terms[i];
    Node valPowXAbstract = d_model.computeAbstractModelValue(n);
    Node valPowXConcrete = d_model.computeConcreteModelValue(n);
    Node valXConcrete = d_model.computeConcreteModelValue(n[0]);
    if (TraceIsOn("t.pow-check"))
    {
      Trace("t.pow-check") << "* " << i << ", value = " << valPowXAbstract
                           << std::endl;
      Trace("t.pow-check") << "  actual " << valXConcrete << " = "
                           << valPowXConcrete << std::endl;
    }
    if (valPowXAbstract == valPowXConcrete)
    {
      Trace("t.pow-check") << "...already correct" << std::endl;
      continue;
    }

    Integer x = valXConcrete.getConst<Rational>().getNumerator();
    Integer powX = valPowXAbstract.getConst<Rational>().getNumerator();
    // add monotinicity lemmas
    for (uint64_t j = i + 1; j < size; j++)
    {
      Node m = d_terms[j];
      Node valPowYAbstract = d_model.computeAbstractModelValue(m);
      Node valYConcrete = d_model.computeConcreteModelValue(m[0]);

      Integer y = valYConcrete.getConst<Rational>().getNumerator();
      Integer powY = valPowYAbstract.getConst<Rational>().getNumerator();

      if (x < y && powX >= powY)
      {
        Node assumption = nm->mkNode(LEQ, n[0], m[0]);
        Node conclusion = nm->mkNode(LEQ, n, m);
        Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
        d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_T_POW_MONOTONE_REFINE, nullptr, true);
        }
    }

    // Place holder for additional lemma schemas

    // End of additional lemma schemas

    // this is the most naive model-based schema based on model values
    Node lem = valueBasedLemma(n);
    Trace("t.pow-lemma") << "TPowSolver::Lemma: " << lem << " ; VALUE_REFINE"
                         << std::endl;
    // send the value lemma
    d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_T_POW_VALUE_REFINE, nullptr, true);
  }
}

Node TPowSolver::valueBasedLemma(Node i)
{
  Assert(i.getKind() == T_POW);
  Node x = i[0];

  Node valX = d_model.computeConcreteModelValue(x);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(T_POW, i.getOperator(), valX);
  valC = rewrite(valC);

  return nm->mkNode(IMPLIES, x.eqNode(valX), i.eqNode(valC));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
