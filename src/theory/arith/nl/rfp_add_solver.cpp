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
 * Implementation of rfp.add solver.
 */

#include "theory/arith/nl/rfp_add_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/int_roundingmode.h"
#include "util/real_floatingpoint.h"

using namespace cvc5::internal::kind;

namespace RFP = cvc5::internal::RealFloatingPoint;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

RfpAddSolver::RfpAddSolver(Env& env,
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

RfpAddSolver::~RfpAddSolver() {}

void RfpAddSolver::initLastCall(const std::vector<Node>& assertions,
                                  const std::vector<Node>& false_asserts,
                                  const std::vector<Node>& xts)
{
  d_terms.clear();

  Trace("rfp-add-mv") << "RFP_ADD terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != RFP_ADD)
    {
      // don't care about other terms
      continue;
    }
    u_int32_t hash = a.getOperator().getConst<RfpAdd>();
    d_terms[hash].push_back(a);
    Trace("rfp-add-mv") << "- " << a << std::endl;
  }
}

void RfpAddSolver::checkInitialRefine()
{
  Trace("rfp-add-check") << "RfpAddSolver::checkInitialRefine" << std::endl;
  //NodeManager* nm = NodeManager::currentNM();
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

      //Node op = node.getOperator();
      //// L2-4 w/ same rm
      //Node dbl = nm->mkNode(kind::RFP_ROUND, op, node[0], node);
      //Node lem = nm->mkNode(EQUAL, dbl, node);
      //Trace("rfp-round-lemma") << "RfpAddSolver::Lemma: " << lem << " ; INIT_REFINE"
      //                         << std::endl;
      //d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
    }
  }
}

Node mkIsFinite(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lb = nm->mkNode(LEQ, nm->mkConstReal(-Rational(RFP::maxValue(eb,sb))), x);
  Node ub = nm->mkNode(LEQ, x, nm->mkConstReal(-Rational(RFP::maxValue(eb,sb))));
  return nm->mkNode(AND, lb, ub);
}

Node mkIsInfinite(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node is_ninf = nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
  Node is_pinf = nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
  return nm->mkNode(OR, is_ninf, is_pinf);
}

Node mkIsPositive(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node is_finite = mkIsFinite(eb,sb, x);
  Node is_infinite = mkIsInfinite(eb,sb, x);
  Node fin_or_inf = nm->mkNode(OR, is_finite, is_infinite);
  Node positive = nm->mkNode(GT, x, nm->mkConstReal(Rational(0)));
  return nm->mkNode(AND, fin_or_inf, positive);
}

Node mkIsNegative(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node is_finite = mkIsFinite(eb,sb, x);
  Node is_infinite = mkIsInfinite(eb,sb, x);
  Node fin_or_inf = nm->mkNode(OR, is_finite, is_infinite);
  Node negative = nm->mkNode(LT, x, nm->mkConstReal(Rational(0)));
  return nm->mkNode(AND, fin_or_inf, negative);
}

Node mkSameSign(uint32_t eb, uint32_t sb, Node x, Node y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node positive = nm->mkNode(AND, mkIsPositive(eb,sb, x), mkIsPositive(eb,sb, y));
  Node negative = nm->mkNode(AND, mkIsNegative(eb,sb, x), mkIsNegative(eb,sb, y));
  return nm->mkNode(OR, positive, negative);
}

Node mkDiffSign(uint32_t eb, uint32_t sb, Node x, Node y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node pos_neg = nm->mkNode(AND, mkIsPositive(eb,sb, x), mkIsNegative(eb,sb, y));
  Node neg_pos = nm->mkNode(AND, mkIsNegative(eb,sb, x), mkIsPositive(eb,sb, y));
  return nm->mkNode(OR, pos_neg, neg_pos);
}

void RfpAddSolver::checkFullRefine()
{
  Trace("rfp-add-check") << "RfpAddSolver::checkFullRefine";
  Trace("rfp-add-check") << "RFP_ADD terms: " << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& ts : d_terms)
  {
    // the reference bitwidth
    //unsigned k = ts.first;
    for (const Node& node : ts.second)
    {
      FloatingPointSize sz = node.getOperator().getConst<RfpAdd>().getSize();
      uint32_t eb = sz.exponentWidth();
      uint32_t sb = sz.significandWidth();

      Node valAdd = d_model.computeAbstractModelValue(node);
      Node valAddC = d_model.computeConcreteModelValue(node);

      Node valRm = d_model.computeConcreteModelValue(node[0]);
      Node valX = d_model.computeConcreteModelValue(node[1]);
      Node valY = d_model.computeConcreteModelValue(node[2]);

      Integer rm = valRm.getConst<Rational>().getNumerator();
      Rational x = valX.getConst<Rational>();
      Rational y = valY.getConst<Rational>();
      Rational add = valAdd.getConst<Rational>();

      if (TraceIsOn("rfp-add-check"))
      {
        Trace("rfp-add-check") << "* " << node << ", value = " << valAdd
                               << std::endl;
        Trace("rfp-add-check") << "  actual (" << rm << ", " << x << ", " << y
                               << ") = " << valAddC << std::endl;
      }
      if (valAdd == valAddC)
      {
        Trace("rfp-add-check") << "...already correct" << std::endl;
        continue;
      }

      if (RFP::isFinite(eb,sb, add) && (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y)))
      {
        Node assumption = mkIsFinite(eb,sb, node);
        Node is_finite_x = mkIsFinite(eb,sb, node[1]);
        Node is_finite_y = mkIsFinite(eb,sb, node[2]);
        Node conclution = nm->mkNode(AND, is_finite_x, is_finite_y);
        Node lem = nm->mkNode(IMPLIES, assumption, conclution);
        Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                               << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ADD_AUX_REFINE);
      }

      if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && 
          ((x >= 0 && y < 0) || (x < 0 && y >= 0)) && x + y == 0)
      {
        std::vector<Node> conj;
        conj.push_back(mkIsFinite(eb,sb, node[1]));
        conj.push_back(mkIsFinite(eb,sb, node[2]));
        conj.push_back(mkDiffSign(eb,sb, node[1], node[2]));
        conj.push_back(node.eqNode(d_zero));
        Node assumption = nm->mkAnd(conj);
        Node rtn = node[0].eqNode(nm->mkConstInt(IntRoundingMode::TN));
        Node conclusion = nm->mkNode(ITE, rtn, 
                                     mkIsNegative(eb,sb, node), 
                                     mkIsPositive(eb,sb, node));
        Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
        Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                               << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ADD_AUX_REFINE);
      }

      // this is the most naive model-based schema based on model values
      Node lem = valueBasedLemma(node);
      Trace("rfp-add-lemma")
          << "RfpAddSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
      // send the value lemma
      d_im.addPendingLemma(lem,
                           InferenceId::ARITH_NL_RFP_ADD_VALUE_REFINE,
                           nullptr,
                           true);
    }
  }
}

Node RfpAddSolver::valueBasedLemma(Node n)
{
  Assert(n.getKind() == RFP_ADD);
  Node rm = n[0];
  Node x = n[1];
  Node y = n[2];

  Node valRm = d_model.computeConcreteModelValue(rm);
  Node valX = d_model.computeConcreteModelValue(x);
  Node valY = d_model.computeConcreteModelValue(y);

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> cs;
  cs.push_back(n.getOperator());
  cs.push_back(valRm);
  cs.push_back(valX);
  cs.push_back(valY);
  Node valC = nm->mkNode(RFP_ADD, cs);
  valC = rewrite(valC);

  Node assumption = nm->mkNode(AND, rm.eqNode(valRm), x.eqNode(valX), y.eqNode(valY));
  return nm->mkNode(IMPLIES, assumption, n.eqNode(valC));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
