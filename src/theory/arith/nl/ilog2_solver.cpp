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
 * Implementation of ilog2 solver.
 */

#include "theory/arith/nl/ilog2_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

Ilog2Solver::Ilog2Solver(Env& env,
                         InferenceManager& im,
                         NlModel& model)
    : EnvObj(env), d_im(im), d_model(model), d_initRefine(userContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
}

Ilog2Solver::~Ilog2Solver() {}

void Ilog2Solver::initLastCall(const std::vector<Node>& assertions,
                               const std::vector<Node>& false_asserts,
                               const std::vector<Node>& xts)
{
  d_ilog2s.clear();
  Trace("ilog2-mv") << "ILOG2 terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != ILOG2)
    {
      // don't care about other terms
      continue;
    }
    d_ilog2s.push_back(a);
  }
  Trace("ilog2") << "We have " << d_ilog2s.size() << " ilog2 terms." << std::endl;
}

void Ilog2Solver::checkInitialRefine()
{
  Trace("ilog2-check") << "Ilog2Solver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& i : d_ilog2s)
  {
    if (d_initRefine.find(i) != d_initRefine.end())
    {
      // already sent initial axioms for i in this user context
      continue;
    }
    d_initRefine.insert(i);
    // initial refinement lemmas
    {
      Node isGtZero = nm->mkNode(kind::GT, i[0], nm->mkConstReal(0));
      Node isGeqOne = nm->mkNode(kind::GEQ, i[0], nm->mkConstReal(1));
      Node isPos = nm->mkNode(kind::GEQ, i, nm->mkConstInt(0));
      Node lem = nm->mkNode(kind::ITE, isGeqOne, isPos, 
        isGtZero.impNode(isPos.notNode()));
      Trace("ilog2-lemma") << "Ilog2Solver::Lemma: " << lem << " ; INIT_REFINE"
                           << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_ILOG2_INIT_REFINE);
    }
    {
      Node isGtZero = nm->mkNode(kind::GT, i[0], nm->mkConstReal(0));
      Node abs = nm->mkNode(kind::ABS, i[0]);
      Node cond = nm->mkNode(GEQ, abs, nm->mkConstReal(1));
      Node pow2 = nm->mkNode(kind::POW2, i);
      Node neg = nm->mkNode(kind::NEG, i);
      Node pow2Neg = nm->mkNode(kind::POW2, neg);
      Node arg = nm->mkNode(kind::TO_INTEGER, i[0]);
      Node invArg = nm->mkNode(kind::DIVISION, nm->mkConstReal(1), i[0]);
      invArg = nm->mkNode(kind::TO_INTEGER, invArg);
      Node lem = isGtZero.impNode(
        nm->mkNode(kind::ITE, cond, 
        pow2.eqNode(arg), pow2Neg.eqNode(invArg)));
      Trace("ilog2-lemma") << "Ilog2Solver::Lemma: " << lem << " ; INIT_REFINE"
                           << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_ILOG2_INIT_REFINE);
    }
  }
}

void Ilog2Solver::sortIlog2sBasedOnModel()
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
      d_ilog2s.begin(), d_ilog2s.end(), std::bind(modelSort, _1, _2, d_model));
}

void Ilog2Solver::checkFullRefine()
{
  Trace("ilog2-check") << "Ilog2Solver::checkFullRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  sortIlog2sBasedOnModel();
  // add lemmas for each ilog2 term
  for (uint64_t i = 0, size = d_ilog2s.size(); i < size; i++)
  {
    Node n = d_ilog2s[i];
    Node valIlog2xAbstract = d_model.computeAbstractModelValue(n);
    Node valIlog2xConcrete = d_model.computeConcreteModelValue(n);
    Node valXConcrete = d_model.computeConcreteModelValue(n[0]);
    if (TraceIsOn("ilog2-check"))
    {
      Trace("ilog2-check") << "* " << i << ", value = " << valIlog2xAbstract
                           << std::endl;
      Trace("ilog2-check") << "  actual " << valXConcrete << " = "
                           << valIlog2xConcrete << std::endl;
    }
    if (valIlog2xAbstract == valIlog2xConcrete)
    {
      Trace("ilog2-check") << "...already correct" << std::endl;
      continue;
    }

    Integer x = valXConcrete.getConst<Rational>().getNumerator();
    Integer ilog2x = valIlog2xAbstract.getConst<Rational>().getNumerator();
    // add monotinicity lemmas
    for (uint64_t j = i + 1; j < size; j++)
    {
      Node m = d_ilog2s[j];
      Node valIlog2yAbstract = d_model.computeAbstractModelValue(m);
      Node valYConcrete = d_model.computeConcreteModelValue(m[0]);

      Integer y = valYConcrete.getConst<Rational>().getNumerator();
      Integer ilog2y = valIlog2yAbstract.getConst<Rational>().getNumerator();

      if (x < y && ilog2x >= ilog2y)
      {
        Node assumption = nm->mkNode(LEQ, n[0], m[0]);
        Node conclusion = nm->mkNode(LEQ, n, m);
        Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
        d_im.addPendingLemma(
            lem, InferenceId::ARITH_NL_ILOG2_MONOTONE_REFINE, nullptr, true);
        }
    }

    // Place holder for additional lemma schemas

    // End of additional lemma schemas

    // this is the most naive model-based schema based on model values
    Node lem = valueBasedLemma(n);
    Trace("ilog2-lemma") << "Ilog2Solver::Lemma: " << lem << " ; VALUE_REFINE"
                         << std::endl;
    // send the value lemma
    d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_ILOG2_VALUE_REFINE, nullptr, true);
  }
}

Node Ilog2Solver::valueBasedLemma(Node i)
{
  Assert(i.getKind() == ILOG2);
  Node x = i[0];

  Node valX = d_model.computeConcreteModelValue(x);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(ILOG2, valX);
  valC = rewrite(valC);

  return nm->mkNode(IMPLIES, x.eqNode(valX), i.eqNode(valC));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
