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
 * Implementation of the basic RFP solver.
 */

#include "theory/arith/nl/rfp_solver.h"

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

RfpSolver::RfpSolver(Env& env,
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

RfpSolver::~RfpSolver() {}

void RfpSolver::initLastCall(const std::vector<Node>& assertions,
                             const std::vector<Node>& false_asserts,
                             const std::vector<Node>& xts)
{
  d_terms.clear();
  Trace("rfp-solver") << "initLastCall" << std::endl;
  for (const Node& n : xts)
  {
    u_int32_t hash;
    switch (n.getKind())
    {
      case RFP_ADD: hash = n.getOperator().getConst<RfpAdd>(); break;
      case RFP_LT:  hash = n.getOperator().getConst<RfpLt>(); break;
      default: continue;
    }
    d_terms[n.getKind()][hash].push_back(n);
    Trace("rfp-solver-mv") << "- " << n << std::endl;
  }
}

void RfpSolver::checkInitialRefine()
{
  Trace("rfp-solver") << "RfpSolver::checkInitialRefine" << std::endl;
  //for (const std::pair<const unsigned, std::vector<Node> >& is : d_adds)
  for (const std::pair<const Kind, std::map<unsigned, std::vector<Node> > >& term : d_terms)
  {
    for (const std::pair<const unsigned, std::vector<Node> >& hNodes : term.second)
    {
      for (const Node& node : hNodes.second)
      {
        if (d_initRefine.find(node) != d_initRefine.end())
        {
          // already sent initial axioms for i in this user context
          continue;
        }
        d_initRefine.insert(node);
        switch(term.first)
        {
          case RFP_ADD: 
          {
            checkInitialRefineAdd(node); break;
          }
          case RFP_LT: 
          {
            checkInitialRefineLt(node); break;
          }
          default: {}
        }
      }
    }
  }
}

void RfpSolver::checkFullRefine()
{
  Trace("rfp-solver") << "RfpSolver::checkFullRefine" << std::endl;
  for (const std::pair<const Kind, std::map<unsigned, std::vector<Node> > >& term : d_terms)
  {
    for (const std::pair<const unsigned, std::vector<Node> >& hNodes : term.second)
    {
      // the reference bitwidth
      //unsigned k = ts.first;
      for (const Node& node : hNodes.second)
      {
        switch (term.first)
        {
          case RFP_ADD: 
          {
            checkFullRefineAdd(node); break;
          }
          case RFP_LT: 
          {
            checkFullRefineLt(node); break;
          }
          default:
            checkFullRefineValue(node);
        }
      }
    }
  }
}

void RfpSolver::checkFullRefineValue(TNode node)
{
  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valRm = d_model.computeConcreteModelValue(node[0]);
  Node valX = d_model.computeConcreteModelValue(node[1]);
  Node valY = d_model.computeConcreteModelValue(node[2]);

  Integer rm = valRm.getConst<Rational>().getNumerator();
  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Rational term = valTerm.getConst<Rational>();

  if (TraceIsOn("rfp-solver"))
  {
    Trace("rfp-solver") << "* " << node << ", value = " << valTerm
                        << std::endl;
    Trace("rfp-solver") << "  actual (" << rm << ", " << x << ", " << y
                        << ") = " << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-solver") << "...already correct" << std::endl;
    return;
  }

  // this is the most naive model-based schema based on model values
  Node lem = opValueBasedLemma(node);
  Trace("rfp-lemma")
      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem,
                       InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                       nullptr,
                       true);
}

Node RfpSolver::opValueBasedLemma(Node n)
{
  Assert(n.getKind() == RFP_ADD 
      || n.getKind() == RFP_SUB
      );
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
  Node valC = nm->mkNode(n.getKind(), cs);
  valC = rewrite(valC);

  Node assumption = nm->mkNode(AND, rm.eqNode(valRm), x.eqNode(valX), y.eqNode(valY));
  return nm->mkNode(IMPLIES, assumption, n.eqNode(valC));
}

Node RfpSolver::relValueBasedLemma(Node n)
{
  Assert(n.getKind() == RFP_LT 
      );
  Node x = n[0];
  Node y = n[1];

  Node valX = d_model.computeConcreteModelValue(n[0]);
  Node valY = d_model.computeConcreteModelValue(n[1]);

  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> cs;
  cs.push_back(n.getOperator());
  cs.push_back(valX);
  cs.push_back(valY);
  Node valC = nm->mkNode(n.getKind(), cs);
  valC = rewrite(valC);

  Node assumption = nm->mkNode(AND, x.eqNode(valX), y.eqNode(valY));
  return nm->mkNode(IMPLIES, assumption, n.eqNode(valC));
}

// utilities

Node mkFalse(Node i)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(EQUAL, i, nm->mkConstInt(0));
}

Node mkTrue(Node i)
{
  NodeManager* nm = NodeManager::currentNM();
  Node t = nm->mkNode(EQUAL, i, nm->mkConstInt(0));
  return nm->mkNode(NOT, t);
}

Node mkIsFinite(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lb = nm->mkNode(LEQ, nm->mkConstReal(-Rational(RFP::maxValue(eb,sb))), x);
  Node ub = nm->mkNode(LEQ, x, nm->mkConstReal(-Rational(RFP::maxValue(eb,sb))));
  return nm->mkNode(AND, lb, ub);
}

Node mkIsInf(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node is_ninf = nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
  Node is_pinf = nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
  return nm->mkNode(OR, is_ninf, is_pinf);
}

Node mkIsPos(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node is_finite = mkIsFinite(eb,sb, x);
  Node is_inf = mkIsInf(eb,sb, x);
  Node fin_or_inf = nm->mkNode(OR, is_finite, is_inf);
  Node positive = nm->mkNode(GT, x, nm->mkConstReal(Rational(0)));
  return nm->mkNode(AND, fin_or_inf, positive);
}

Node mkIsNeg(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node is_finite = mkIsFinite(eb,sb, x);
  Node is_inf = mkIsInf(eb,sb, x);
  Node fin_or_inf = nm->mkNode(OR, is_finite, is_inf);
  Node negative = nm->mkNode(LT, x, nm->mkConstReal(Rational(0)));
  return nm->mkNode(AND, fin_or_inf, negative);
}

Node mkSameSign(uint32_t eb, uint32_t sb, Node x, Node y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node positive = nm->mkNode(AND, mkIsPos(eb,sb, x), mkIsPos(eb,sb, y));
  Node negative = nm->mkNode(AND, mkIsNeg(eb,sb, x), mkIsNeg(eb,sb, y));
  return nm->mkNode(OR, positive, negative);
}

Node mkDiffSign(uint32_t eb, uint32_t sb, Node x, Node y)
{
  NodeManager* nm = NodeManager::currentNM();
  Node pos_neg = nm->mkNode(AND, mkIsPos(eb,sb, x), mkIsNeg(eb,sb, y));
  Node neg_pos = nm->mkNode(AND, mkIsNeg(eb,sb, x), mkIsPos(eb,sb, y));
  return nm->mkNode(OR, pos_neg, neg_pos);
}

Node mkIsMinusInf(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
}
Node mkIsPlusInf(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
}
Node mkIsNan(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::notANumber(eb,sb)));
}

Node mkLtSpecial(uint32_t eb, uint32_t sb, TNode node)
{
  NodeManager* nm = NodeManager::currentNM();
  Node assumption = mkTrue(node);
  Node is_finite_x = mkIsFinite(eb,sb, node[0]);
  Node is_finite_y = mkIsFinite(eb,sb, node[1]);
  Node c1 = nm->mkNode(AND, is_finite_x, is_finite_y);
  Node is_ninf_x = mkIsMinusInf(eb,sb, node[0]);
  Node is_not_nan_y = nm->mkNode(NOT, mkIsNan(eb,sb, node[1]));
  Node is_not_ninf_y = nm->mkNode(NOT, mkIsMinusInf(eb,sb, node[1]));
  Node c2 = nm->mkNode(AND, is_ninf_x, is_not_nan_y, is_not_ninf_y);
  Node is_not_nan_x = nm->mkNode(NOT, mkIsNan(eb,sb, node[0]));
  Node is_not_pinf_x = nm->mkNode(NOT, mkIsPlusInf(eb,sb, node[0]));
  Node is_pinf_y = mkIsPlusInf(eb,sb, node[1]);
  Node c3 = nm->mkNode(AND, is_not_nan_x, is_not_pinf_x, is_pinf_y);
  Node conclusion = nm->mkNode(OR, c1, c2, c3);
  return nm->mkNode(IMPLIES, assumption, conclusion);
}

// RfpAdd

void RfpSolver::checkInitialRefineAdd(TNode node) {}

void RfpSolver::checkFullRefineAdd(TNode node)
{
  Trace("rfp-add") << "RFP_ADD term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
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

  if (TraceIsOn("rfp-add"))
  {
    Trace("rfp-add") << "* " << node << ", value = " << valAdd
                     << std::endl;
    Trace("rfp-add") << "  actual (" << rm << ", " << x << ", " << y
                     << ") = " << valAddC << std::endl;
  }
  if (valAdd == valAddC)
  {
    Trace("rfp-add") << "...already correct" << std::endl;
    return;
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
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
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
                                 mkIsNeg(eb,sb, node), 
                                 mkIsPos(eb,sb, node));
    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  // this is the most naive model-based schema based on model values
  Node lem = opValueBasedLemma(node);
  Trace("rfp-add-lemma")
      << "RfpAddSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem,
                       InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                       nullptr,
                       true);
}

// RfpLt

void RfpSolver::checkInitialRefineLt(TNode node) 
{
  Trace("rfp-lt") << "RFP_LT term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpAdd>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node lem = mkLtSpecial(eb,sb, node);
  Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                         << std::endl;
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
}

void RfpSolver::checkFullRefineLt(TNode node) 
{
  Trace("rfp-lt") << "RFP_LT term: " << node << std::endl;
  //NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpLt>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valX = d_model.computeConcreteModelValue(node[0]);
  Node valY = d_model.computeConcreteModelValue(node[1]);

  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Integer t = valTerm.getConst<Rational>().getNumerator();

  if (TraceIsOn("rfp-lt"))
  {
    Trace("rfp-lt") << "* " << node << ", value = " << valTerm
                    << std::endl;
    Trace("rfp-lt") << "  actual (" << x << ", " << y << ") = " 
                    << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-lt") << "...already correct" << std::endl;
    return;
  }

  if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  {
    Node lem = mkLtSpecial(eb,sb, node);
    Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  // this is the most naive model-based schema based on model values
  Node lem = relValueBasedLemma(node);
  Trace("rfp-lt-lemma")
      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem,
                       InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                       nullptr,
                       true);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
