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
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/int_roundingmode.h"
#include "util/real_floatingpoint.h"

using namespace cvc5::internal::kind;

using IRM = typename cvc5::internal::IntRoundingMode;
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
      case RFP_MULT: hash = n.getOperator().getConst<RfpMult>(); break;
      case RFP_LT:  hash = n.getOperator().getConst<RfpLt>(); break;
      case RFP_LEQ: hash = n.getOperator().getConst<RfpLeq>(); break;
      default: continue;
    }
    d_terms[n.getKind()][hash].push_back(n);
    Trace("rfp-solver-mv") << "- " << n 
                           << " (" << n.getKind() << ")" << std::endl;
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
          case RFP_ADD: checkInitialRefineAdd(node); break;
          case RFP_MULT: checkInitialRefineMult(node); break;
          case RFP_LT:  checkInitialRefineLt(node); break;
          case RFP_LEQ: checkInitialRefineLeq(node); break;
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
        Trace("rfp-solver") << term.first << ", " << node << std::endl;
        switch (term.first)
        {
          case RFP_ADD: checkFullRefineAdd(node); break;
          case RFP_MULT: checkFullRefineMult(node); break;
          case RFP_LT:  checkFullRefineLt(node); break;
          case RFP_LEQ: checkFullRefineLeq(node); break;
          default:
            checkFullRefineValue(node);
        }
      }
    }
  }
}

void RfpSolver::checkFullRefineValue(Node node)
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
      || n.getKind() == RFP_MULT
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
      || n.getKind() == RFP_LEQ
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
  Node zero = nm->mkConstInt(0);
  return nm->mkNode(EQUAL, i, zero);
}

Node mkTrue(Node i)
{
  NodeManager* nm = NodeManager::currentNM();
  //Node zero = nm->mkConstInt(0);
  //Node t = nm->mkNode(EQUAL, i, zero);
  //return nm->mkNode(NOT, t);
  Node one = nm->mkConstInt(1);
  return nm->mkNode(EQUAL, i, one);
}

Node mkIsFinite(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lb = nm->mkNode(LEQ, nm->mkConstReal(-Rational(RFP::maxValue(eb,sb))), x);
  Node ub = nm->mkNode(LEQ, x, nm->mkConstReal(-Rational(RFP::maxValue(eb,sb))));
  return nm->mkNode(AND, lb, ub);
}

Node mkIsZero(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nz = nm->mkNode(EQUAL, nm->mkConstReal(RFP::minusZero(eb,sb)), x);
  Node pz = nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::plusZero(eb,sb)));
  return nm->mkNode(OR, nz, pz);
}

Node mkIsZeroWeak(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nz = nm->mkNode(LEQ, nm->mkConstReal(RFP::minusZero(eb,sb)), x);
  Node pz = nm->mkNode(LEQ, x, nm->mkConstReal(RFP::plusZero(eb,sb)));
  return nm->mkNode(AND, nz, pz);
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

Node mkIsNegInf(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
}
Node mkIsPosInf(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
}
Node mkIsNan(uint32_t eb, uint32_t sb, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  return  nm->mkNode(EQUAL, x, nm->mkConstReal(RFP::notANumber(eb,sb)));
}

Node mkSignZeroResult(uint32_t eb, uint32_t sb, Node rm, Node x)
{
  NodeManager* nm = NodeManager::currentNM();
  Node isZero = mkIsZero(eb,sb, x);
  Node isRTN = nm->mkNode(EQUAL, rm, nm->mkConstInt(IRM::TZ), rm);
  Node isNegative = nm->mkNode(LEQ, nm->mkConstInt(Rational(0)), x);
  Node isPositive = nm->mkNode(LEQ, x, nm->mkConstInt(Rational(1)));
  Node concl = isRTN.iteNode(isNegative, isPositive);
  return nm->mkNode(IMPLIES, isZero, concl);
}

Node mkRelConstr(Node node)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lb = nm->mkNode(LEQ, nm->mkConstInt(Rational(0)), node);
  Node ub = nm->mkNode(LEQ, node, nm->mkConstInt(Rational(1)));
  return nm->mkNode(AND, lb, ub);
}

Node mkLtSpecial(uint32_t eb, uint32_t sb, Node node)
{
  Node assumption = mkTrue(node);
  Node isFiniteX = mkIsFinite(eb,sb, node[0]);
  Node isFiniteY = mkIsFinite(eb,sb, node[1]);
  Node c1 = isFiniteX.andNode(isFiniteY);
  Node isNinfX = mkIsNegInf(eb,sb, node[0]);
  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  Node isNotNinfY = mkIsNegInf(eb,sb, node[1]).notNode();
  Node c2 = isNinfX.andNode(isNotNanY).andNode(isNotNinfY);
  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  Node isNotPinfX = mkIsPosInf(eb,sb, node[0]).notNode();
  Node isPinfY = mkIsPosInf(eb,sb, node[1]);
  Node c3 = isNotNanX.andNode(isNotPinfX).andNode(isPinfY);
  Node conclusion = c1.orNode(c2).orNode(c3);
  return assumption.impNode(conclusion);
}

Node mkLeqSpecial(uint32_t eb, uint32_t sb, Node node)
{
  Node assumption = mkTrue(node);
  Node isFiniteX = mkIsFinite(eb,sb, node[0]);
  Node isFiniteY = mkIsFinite(eb,sb, node[1]);
  Node c1 = isFiniteX.andNode(isFiniteY);
  Node isNinfX = mkIsNegInf(eb,sb, node[0]);
  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  Node c2 = isNinfX.andNode(isNotNanY);
  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  Node isPinfY = mkIsPosInf(eb,sb, node[1]);
  Node c3 = isNotNanX.andNode(isPinfY);
  Node conclusion = c1.orNode(c2).orNode(c3);
  return assumption.impNode(conclusion);
}

// RfpAdd

void RfpSolver::checkInitialRefineAdd(Node node) {}

void RfpSolver::checkFullRefineAdd(Node node)
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

  if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)) 
  {
    if (RFP::isFinite(eb,sb, x + y))
    {
      // add_finite
      Node isFiniteX = mkIsFinite(eb,sb, node[1]);
      Node isFiniteY = mkIsFinite(eb,sb, node[2]);
      //Node isZeroX = mkIsZero(eb,sb, node[1]);
      //Node isZeroY = mkIsZero(eb,sb, node[2]);
      //Node aX = isFiniteX.andNode(isZeroX.notNode());
      //Node aY = isFiniteY.andNode(isZeroY.notNode());
      Node addXY = nm->mkNode(kind::ADD, node[1], node[2]);
      Node noOverflow = mkIsFinite(eb,sb, addXY);
      Node assumption = isFiniteX.andNode(isFiniteY.andNode(noOverflow));

      Node isFinite = mkIsFinite(eb,sb, node);
      Node op = nm->mkConst(RfpRound(eb, sb));
      Node round = nm->mkNode(kind::RFP_ROUND, op, node[0], addXY);
      Node conclusion = isFinite.andNode(node.eqNode(round));

      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }

    if (add != y 
      && RFP::isZero(eb,sb, x) && !RFP::isZero(eb,sb, y))
    {
      // add_zero 1
      Node isZeroX = mkIsZero(eb,sb, node[1]);
      Node isFiniteY = mkIsFinite(eb,sb, node[2]);
      Node isZeroY = mkIsZero(eb,sb, node[2]);
      Node aY = isFiniteY.andNode(isZeroY.notNode());
      Node assumption = isZeroX.andNode(aY);
      Node conclusion = node.eqNode(node[2]);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
    if (add != x
      && !RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      // add_zero 2
      Node isFiniteX = mkIsFinite(eb,sb, node[1]);
      Node isZeroX = mkIsZero(eb,sb, node[1]);
      Node aX = isFiniteX.andNode(isZeroX.notNode());
      Node isZeroY = mkIsZero(eb,sb, node[2]);
      Node assumption = aX.andNode(isZeroY);
      Node conclusion = node.eqNode(node[1]);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
    // Covered by VALUE_REFINE.
    //if (!RFP::isZero(eb,sb, add) 
    //  && RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    //{
    //  // add_zero 3
    //  Node isZeroX = mkIsZero(eb,sb, node[1]);
    //  Node isZeroY = mkIsZero(eb,sb, node[2]);
    //  Node assumption = isZeroX.andNode(isZeroY);
    //  Node conclusion = mkIsZero(eb,sb, node);
    //  Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    //  Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
    //                         << std::endl;
    //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    //}

    if (!RFP::isFinite(eb,sb, add) && RFP::isFinite(eb,sb, x + y))
    {
      // add_finite_rev
      Node assumption = mkIsFinite(eb,sb, node);
      Node is_finite_x = mkIsFinite(eb,sb, node[1]);
      Node is_finite_y = mkIsFinite(eb,sb, node[2]);
      Node conclusion = nm->mkNode(AND, is_finite_x, is_finite_y);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
  }

  //if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && 
  //  (x >= RFP::plusZero(eb,sb) && y < RFP::minusZero(eb,sb) 
  //    || (x < RFP::minusZero(eb,sb) && y >= RFP::plusZero(eb,sb))) 
  //  && x + y == 0)
  //{
  //  std::vector<Node> conj;
  //  conj.push_back(mkIsFinite(eb,sb, node[1]));
  //  conj.push_back(mkIsFinite(eb,sb, node[2]));
  //  conj.push_back(mkDiffSign(eb,sb, node[1], node[2]));
  //  conj.push_back(node.eqNode(d_zero));
  //  Node assumption = nm->mkAnd(conj);
  //  Node rtn = node[0].eqNode(nm->mkConstInt(IntRoundingMode::TN));
  //  Node conclusion = nm->mkNode(ITE, rtn, 
  //                               mkIsNeg(eb,sb, node), 
  //                               mkIsPos(eb,sb, node));
  //  Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //  Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  // add_special 1--5: handled by VALUE_REFINE?

  if (!RFP::isInfinite(eb,sb, add)
    && RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)
    && !RFP::isFinite(eb,sb, x + y))
  {
    // add_special 6 weakened

    // add_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node addXY = nm->mkNode(kind::ADD, node[1], node[2]);
    Node overflow = mkIsFinite(eb,sb, addXY).notNode();
    Node assumption = isFiniteX.andNode(isFiniteY.andNode(overflow));
    Node conclusion = mkIsInf(eb,sb, node);
    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  if ((x >= 0 == y >= 0) && (add >= 0 != x >= 0)
    && RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y))
  {
    // add_special 7 weakened

    // add_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node sameSignXY = mkSameSign(eb,sb, node[1], node[2]);
    Node sameSignRX = mkSameSign(eb,sb, node[1], node[2]);
    Node assumption = isFiniteX.andNode(isFiniteY.andNode(sameSignXY));
    Node lem = nm->mkNode(IMPLIES, assumption, sameSignRX);
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

// RfpMult

void RfpSolver::checkInitialRefineMult(Node node) {}

void RfpSolver::checkFullRefineMult(Node node)
{
  Trace("rfp-mult") << "RFP_MULT term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpMult>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valMult = d_model.computeAbstractModelValue(node);
  Node valMultC = d_model.computeConcreteModelValue(node);

  Node valRm = d_model.computeConcreteModelValue(node[0]);
  Node valX = d_model.computeConcreteModelValue(node[1]);
  Node valY = d_model.computeConcreteModelValue(node[2]);

  Integer rm = valRm.getConst<Rational>().getNumerator();
  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Rational mult = valMult.getConst<Rational>();

  if (TraceIsOn("rfp-mult"))
  {
    Trace("rfp-mult") << "* " << node << ", value = " << valMult
                      << std::endl;
    Trace("rfp-mult") << "  actual (" << rm << ", " << x << ", " << y
                      << ") = " << valMultC << std::endl;
  }
  if (valMult == valMultC)
  {
    Trace("rfp-mult") << "...already correct" << std::endl;
    return;
  }

  if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)) 
  {
    if (RFP::isFinite(eb,sb, x * y))
    {
      // mul_finite
      Node isFiniteX = mkIsFinite(eb,sb, node[1]);
      Node isFiniteY = mkIsFinite(eb,sb, node[2]);
      Node isZeroX = mkIsZero(eb,sb, node[1]);
      Node isZeroY = mkIsZero(eb,sb, node[2]);
      Node aX = isFiniteX.andNode(isZeroX.notNode());
      Node aY = isFiniteY.andNode(isZeroY.notNode());
      Node multXY = nm->mkNode(kind::MULT, node[1], node[2]);
      Node noOverflow = mkIsFinite(eb,sb, multXY);
      Node assumption = aX.andNode(aY.andNode(noOverflow));

      Node isFinite = mkIsFinite(eb,sb, node);
      Node op = nm->mkConst(RfpRound(eb, sb));
      Node round = nm->mkNode(kind::RFP_ROUND, op, node[0], multXY);
      Node conclusion = isFinite.andNode(node.eqNode(round));

      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }

    if (!RFP::isZero(eb,sb, mult)
      && !RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      // mul_zero 1
      Node isFiniteX = mkIsFinite(eb,sb, node[1]);
      Node isZeroY = mkIsZero(eb,sb, node[2]);
      Node assumption = isFiniteX.andNode(isZeroY);
      Node conclusion = mkIsZero(eb,sb, node);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
    if (!RFP::isZero(eb,sb, mult)
      && RFP::isZero(eb,sb, x) && !RFP::isZero(eb,sb, y))
    {
      // mul_zero 2
      Node isZeroX = mkIsZero(eb,sb, node[1]);
      Node isFiniteY = mkIsFinite(eb,sb, node[2]);
      Node assumption = isZeroX.andNode(isFiniteY);
      Node conclusion = mkIsZero(eb,sb, node);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-add-lemma") << "RfpAddSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }

    if (!RFP::isFinite(eb,sb, mult) && RFP::isFinite(eb,sb, x * y))
    {
      // mul_finite_rev
      Node isFinite = mkIsFinite(eb,sb, node);
      Node isFiniteX = mkIsFinite(eb,sb, node[1]);
      Node isFiniteY = mkIsFinite(eb,sb, node[2]);
      Node conclusion = isFiniteX.andNode(isFiniteY);
      Node lem = nm->mkNode(IMPLIES, isFinite, conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
    }
  }

  // mul_special 1-2,4,6: delegate to VALUE_REFINE. 

  if (!RFP::isInfinite(eb,sb, mult)) 
  {
    if (RFP::isFinite(eb,sb, x) && RFP::isInfinite(eb,sb, y) && !RFP::isZero(eb,sb, y))
    {
      // mul_special 3
      Node isFiniteX = mkIsFinite(eb,sb, node[1]);
      Node isInfY = mkIsInf(eb,sb, node[2]);
      Node isNotZeroY = mkIsZero(eb,sb, node[2]).notNode();
      Node assumption = isFiniteX.andNode(isInfY.andNode(isNotZeroY));
      Node conclusion = mkIsInf(eb,sb, node);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
    }
    if (RFP::isInfinite(eb,sb, x) && !RFP::isZero(eb,sb, x) && RFP::isFinite(eb,sb, y))
    {
      // mul_special 5
      Node isInfX = mkIsInf(eb,sb, node[1]);
      Node isNotZeroX = mkIsZero(eb,sb, node[1]).notNode();
      Node isFiniteY = mkIsFinite(eb,sb, node[2]);
      Node assumption = isInfX.andNode(isNotZeroX.andNode(isFiniteY));
      Node conclusion = mkIsInf(eb,sb, node);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
    }
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)
      && !RFP::isFinite(eb,sb, x * y))
    {
      // mul_special 7
      Node isFiniteX = mkIsInf(eb,sb, node[1]);
      Node isFiniteY = mkIsFinite(eb,sb, node[2]);
      Node multXY = nm->mkNode(kind::MULT, node[1], node[2]);
      Node overflow = mkIsFinite(eb,sb, multXY).notNode();
      Node assumption = isFiniteX.andNode(isFiniteY.andNode(overflow));
      Node conclusion = mkIsInf(eb,sb, node);
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
    }
  }

  if ((mult == RFP::notANumber(eb,sb) || mult < 0)
    && (x >= 0 == y >= 0))
  {
    // mul_special 8 positive case
    Node isNotNan = mkIsNan(eb,sb, node).notNode();
    Node isSameSign = mkSameSign(eb,sb, node[1], node[2]);
    Node assumption = isNotNan.andNode(isSameSign);
    Node conclusion = mkIsPos(eb,sb, node);
    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
  }
  if ((mult == RFP::notANumber(eb,sb) || mult >= 0)
    && (x >= 0 != y >= 0))
  {
    // mul_special 8 negative case
    Node isNotNan = mkIsNan(eb,sb, node).notNode();
    Node isDiffSign = mkDiffSign(eb,sb, node[1], node[2]);
    Node assumption = isNotNan.andNode(isDiffSign);
    Node conclusion = mkIsNeg(eb,sb, node);
    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
  }

  // this is the most naive model-based schema based on model values
  Node lem = opValueBasedLemma(node);
  Trace("rfp-mult-lemma")
      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                       nullptr, true);
}

// RfpLt

void RfpSolver::checkInitialRefineLt(Node node) 
{
  //Trace("rfp-lt") << "RFP_LT term (init): " << node << std::endl;
  //NodeManager* nm = NodeManager::currentNM();
  //FloatingPointSize sz = node.getOperator().getConst<RfpLt>().getSize();
  //uint32_t eb = sz.exponentWidth();
  //uint32_t sb = sz.significandWidth();
}

void RfpSolver::checkFullRefineLt(Node node) 
{
  Trace("rfp-lt") << "RFP_LT term (full): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
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

  if (t < Integer(0) || Integer(1) < t)
  {
    Node lem = mkRelConstr(node);
    Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE0"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  if ((t != 0) != x < y
    && RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)
    && (!RFP::isZero(eb,sb, x) || !RFP::isZero(eb,sb, y)))
  {
    // lt_finite
    Node isFiniteX = mkIsInf(eb,sb, node[0]);
    Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isFiniteX.andNode(isFiniteY.andNode(
      isNotZeroX.orNode(isNotZeroY)));
    Node ltBool = node.eqNode(nm->mkConstInt(1));
    Node ltXY = nm->mkNode(kind::LT, node[0], node[1]);
    Node conclusion = ltBool.eqNode(ltXY);
    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  //if (x != RFP::notANumber(eb,sb) && y != RFP::notANumber(eb,sb))
  //{
  //  // not_lt_ge
  //  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  //  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  //  Node assumption = node.andNode(isNotNanX).andNode(isNotNanY);
  //  Node op = nm->mkConst(RfpGeq(eb,sb));
  //  Node geq = nm->mkNode(RFP_GEQ, op, node[0], node[1]);
  //  Node lem = nm->mkNode(IMPLIES, assumption, geq);
  //  Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  {
    // lt_special
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

// RfpLeq

void RfpSolver::checkInitialRefineLeq(Node node) {}

void RfpSolver::checkFullRefineLeq(Node node) 
{
  Trace("rfp-leq") << "RFP_LEQ term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpLeq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valX = d_model.computeConcreteModelValue(node[0]);
  Node valY = d_model.computeConcreteModelValue(node[1]);

  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Integer t = valTerm.getConst<Rational>().getNumerator();

  if (TraceIsOn("rfp-leq"))
  {
    Trace("rfp-leq") << "* " << node << ", value = " << valTerm
                     << std::endl;
    Trace("rfp-leq") << "  actual (" << x << ", " << y << ") = " 
                     << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-leq") << "...already correct" << std::endl;
    return;
  }

  if (t < Integer(0) || Integer(1) < t)
  {
    Node lem = mkRelConstr(node);
    Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE0"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  if ((t != 0) != x < y
    && RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)
    && (!RFP::isZero(eb,sb, x) || !RFP::isZero(eb,sb, y)))
  {
    // le_finite
    Node isFiniteX = mkIsInf(eb,sb, node[0]);
    Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isFiniteX.andNode(isFiniteY.andNode(
      isNotZeroX.orNode(isNotZeroY)));
    Node leqBool = node.eqNode(nm->mkConstInt(1));
    Node leqXY = nm->mkNode(kind::LEQ, node[0], node[1]);
    Node conclusion = leqBool.eqNode(leqXY);
    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  //if (x != RFP::notANumber(eb,sb) && y != RFP::notANumber(eb,sb))
  //{
  //  // not_gt_le
  //  Node op = nm->mkConst(RfpGt(eb,sb));
  //  Node gt = nm->mkNode(RFP_GT, op, node[0], node[1]);
  //  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  //  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  //  Node assumption = mkFalse(gt).andNode(isNotNanX).andNode(isNotNanY);
  //  Node lem = assumption.impNode(mkTrue(node));
  //  Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  {
    // leq_special
    Node lem = mkLeqSpecial(eb,sb, node);
    Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  // this is the most naive model-based schema based on model values
  Node lem = relValueBasedLemma(node);
  Trace("rfp-leq-lemma")
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
