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
 * Implementation of RFP_ROUND solver.
 */

#include "theory/arith/nl/rfp_round_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/rfp_round.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

RfpRoundSolver::RfpRoundSolver(Env& env,
                               InferenceManager& im,
                               NlModel& model)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_initRefine(userContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_false = nm->mkConst(false);
  d_true = nm->mkConst(true);
  d_zero = nm->mkConstReal(Rational(0));
  d_one = nm->mkConstReal(Rational(1));
}

RfpRoundSolver::~RfpRoundSolver() {}

void RfpRoundSolver::initLastCall(const std::vector<Node>& assertions,
                                  const std::vector<Node>& false_asserts,
                                  const std::vector<Node>& xts)
{
  d_terms.clear();

  Trace("rfp-round-mv") << "RFP_ROUND terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != RFP_ROUND)
    {
      // don't care about other terms
      continue;
    }
    u_int32_t hash = a.getOperator().getConst<RfpRound>();
    d_terms[hash].push_back(a);
    Trace("rfp-round-mv") << "- " << a << std::endl;
  }
}

void RfpRoundSolver::checkInitialRefine()
{
  Trace("rfp-round-check") << "RfpRoundSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_terms)
  {
    // the reference bitwidth
    //unsigned k = is.first;
    for (const Node& node : is.second)
    {
      if (d_initRefine.find(node) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(node);

      Node op = node.getOperator();
      // L2-4 w/ same rm
      Node dbl = nm->mkNode(kind::RFP_ROUND, op, node[0], node);
      Node lem = nm->mkNode(EQUAL, dbl, node);
      Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem << " ; INIT_REFINE"
                               << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
    }
  }
}

void RfpRoundSolver::checkFullRefine()
{
  Trace("rfp-round-check") << "RfpRoundSolver::checkFullRefine";
  Trace("rfp-round-check") << "RFP_ROUND terms: " << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& ts : d_terms)
  {
    // the reference bitwidth
    //unsigned k = ts.first;
    //for (const Node& t : ts.second)
    for (std::vector<Node>::const_iterator it = ts.second.begin(); 
         it != ts.second.end(); ++it)
    {
      const Node& node = *it;
      Node valRound = d_model.computeAbstractModelValue(node);
      Node valRoundC = d_model.computeConcreteModelValue(node);

      Node valRm = d_model.computeConcreteModelValue(node[0]);
      Node valArg = d_model.computeConcreteModelValue(node[1]);

      Integer rm = valRm.getConst<Rational>().getNumerator();
      Rational arg = valArg.getConst<Rational>();
      Rational round = valRound.getConst<Rational>();

      if (TraceIsOn("rfp-round-check"))
      {
        Trace("rfp-round-check") << "* " << node << ", value = " << valRound 
                                 << std::endl;
        Trace("rfp-round-check") << "  actual (" << rm << ", " << arg
                                 << ") = " << valRoundC << std::endl;
      }
      if (valRound == valRoundC)
      {
        Trace("rfp-round-check") << "...already correct" << std::endl;
        continue;
      }

      // TODO: interval lemmas

      // monotone lemmas
      //for (uint64_t j = i + 1; j < size; j++)
      for (std::vector<Node>::const_iterator it1 = it + 1; 
           it1 != ts.second.end(); ++it1)
      {
        const Node& node1 = *it1;
        Node valRound1 = d_model.computeAbstractModelValue(node1);

        Node valRm1 = d_model.computeConcreteModelValue(node1[0]);
        Node valArg1 = d_model.computeConcreteModelValue(node1[1]);

        Integer rm1 = valRm1.getConst<Rational>().getNumerator();
        Rational arg1 = valArg1.getConst<Rational>();
        Rational round1 = valRound1.getConst<Rational>();

        if (rm == rm1)
        {
          if (arg <= arg1 && round > round1){
            // L2-5
            Node a1 = nm->mkNode(EQUAL, node[0], node1[0]);
            Node a2 = nm->mkNode(LEQ, node[1], node1[1]);
            Node assumption = nm->mkNode(AND, a1, a2);
            Node conclusion = nm->mkNode(LEQ, node, node1);
            Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
            Trace("rfp-round-lemma")
                << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
            d_im.addPendingLemma(
                lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
          }
          if (round < round1 && arg >= round1){
            // L2-6
            Node a1 = nm->mkNode(EQUAL, node[0], node1[0]);
            Node a2 = nm->mkNode(LT, node, node1);
            Node assumption = nm->mkNode(AND, a1, a2);
            Node conclusion = nm->mkNode(LT, node[1], node1);
            Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
            Trace("rfp-round-lemma")
                << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
            d_im.addPendingLemma(
                lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
          }
          if (round < round1 && round >= arg1){
            // L2-7
            Node a1 = nm->mkNode(EQUAL, node[0], node1[0]);
            Node a2 = nm->mkNode(LT, node, node1);
            Node assumption = nm->mkNode(AND, a1, a2);
            Node conclusion = nm->mkNode(LT, node, node1[1]);
            Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
            Trace("rfp-round-lemma")
                << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
            d_im.addPendingLemma(
                lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
          }

          // TODO: L2-10, L2-11, L2-12
        }

        // this is the most naive model-based schema based on model values
        Node lem = valueBasedLemma(node);
        Trace("rfp-round-lemma")
            << "RfpRoundSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
        // send the value lemma
        d_im.addPendingLemma(lem,
                             InferenceId::ARITH_NL_RFP_ROUND_VALUE_REFINE,
                             nullptr,
                             true);
      }
    }
  }
}

Node RfpRoundSolver::valueBasedLemma(Node n)
{
  Assert(n.getKind() == RFP_ROUND);
  Node rm = n[0];
  Node arg = n[1];

  Node valRm = d_model.computeConcreteModelValue(rm);
  Node valArg = d_model.computeConcreteModelValue(arg);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(RFP_ROUND, n.getOperator(), valRm, valArg);
  valC = rewrite(valC);

  Node assumption = nm->mkNode(AND, rm.eqNode(valRm), arg.eqNode(valArg));
  return nm->mkNode(IMPLIES, assumption, n.eqNode(valC));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
