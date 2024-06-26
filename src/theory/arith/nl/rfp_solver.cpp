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
#include "theory/arith/nl/rfp_utils.h"

using namespace cvc5::internal::kind;

using IRM = typename cvc5::internal::IntRoundingMode;
namespace RFP = cvc5::internal::RealFloatingPoint;
using namespace cvc5::internal::theory::arith::nl::RfpUtils;

namespace cvc5::internal {

using ARFP = class AbstractRFP;

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
      case RFP_TO_REAL: hash = n.getOperator().getConst<RfpToReal>(); break;
      case RFP_ADD: hash = n.getOperator().getConst<RfpAdd>(); break;
      case RFP_NEG: hash = n.getOperator().getConst<RfpNeg>(); break;
      case RFP_SUB: hash = n.getOperator().getConst<RfpSub>(); break;
      case RFP_MULT: hash = n.getOperator().getConst<RfpMult>(); break;
      case RFP_DIV: hash = n.getOperator().getConst<RfpDiv>(); break;
      case RFP_LT:  hash = n.getOperator().getConst<RfpLt>(); break;
      case RFP_LEQ: hash = n.getOperator().getConst<RfpLeq>(); break;
      case RFP_GT:  hash = n.getOperator().getConst<RfpGt>(); break;
      case RFP_GEQ: hash = n.getOperator().getConst<RfpGeq>(); break;
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
          case RFP_TO_REAL: checkInitialRefineToReal(node); break;
          case RFP_ADD: checkInitialRefineAdd(node); break;
          case RFP_NEG: checkInitialRefineNeg(node); break;
          case RFP_SUB: checkInitialRefineSub(node); break;
          case RFP_MULT: checkInitialRefineMult(node); break;
          case RFP_DIV: checkInitialRefineDiv(node); break;
          case RFP_LT:  checkInitialRefineLt(node); break;
          case RFP_LEQ: checkInitialRefineLeq(node); break;
          case RFP_GT:  checkInitialRefineGt(node); break;
          case RFP_GEQ: checkInitialRefineGeq(node); break;
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
          case RFP_TO_REAL: checkFullRefineToReal(node); break;
          case RFP_ADD: checkFullRefineAdd(node); break;
          case RFP_NEG: checkFullRefineNeg(node); break;
          case RFP_SUB: checkFullRefineSub(node); break;
          case RFP_MULT: checkFullRefineMult(node); break;
          case RFP_DIV: checkFullRefineDiv(node); break;
          case RFP_LT:  checkFullRefineLt(node); break;
          case RFP_LEQ: checkFullRefineLeq(node); break;
          case RFP_GT:
          case RFP_GEQ:
            // do nothing
            break;
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
    Trace("rfp-solver") << "* " << node << std::endl;
    Trace("rfp-solver") << "  value = " << valTerm << std::endl;
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

Node RfpSolver::opValueBasedLemma(TNode n)
{
  Assert(n.getKind() == RFP_ADD 
      || n.getKind() == RFP_SUB
      || n.getKind() == RFP_MULT
      || n.getKind() == RFP_DIV
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

Node RfpSolver::relValueBasedLemma(TNode n)
{
  Assert(n.getKind() == RFP_LT || n.getKind() == RFP_LEQ);
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

// RfpToReal

void RfpSolver::checkInitialRefineToReal(Node node) 
{
  Trace("rfp-to-real") << "RFP_TO_REAL term (init): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpToReal>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    Node isNotNan = mkIsNan(eb,sb, node[0]).notNode();
    Node isNotInf = mkIsInf(eb,sb, node[0]).notNode();
    Node assumption = isNotNan.andNode(isNotInf);
    Node conclusion = node.eqNode(node[0]);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-to-real-lemma")
        << "RfpSolver::Lemma: " << lem << " ; INIT_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

void RfpSolver::checkFullRefineToReal(Node node) 
{
  Trace("rfp-to-real") << "RFP_TO_REAL term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpToReal>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valXA = d_model.computeAbstractModelValue(node[0]);
  Node valX = d_model.computeConcreteModelValue(node[0]);

  Rational x = valX.getConst<Rational>();
  Rational t = valTerm.getConst<Rational>();

  if (TraceIsOn("rfp-to-real"))
  {
    Trace("rfp-to-real") << "* " << node 
                     << std::endl;
    Trace("rfp-to-real") << "  value  (" << valXA << ") = " 
                         << valTerm
                         << std::endl;
    Trace("rfp-to-real") << "  actual (" << x << ") = " 
                         << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-to-real") << "...already correct" << std::endl;
    return;
  }

  if (!RFP::isNan(eb,sb, x) && !RFP::isInfinite(eb,sb, x))
  {
    Node assumption = node[0].eqNode(valX);
    Node valC = nm->mkNode(kind::RFP_TO_REAL, node.getOperator(), valX);
    valC = rewrite(valC);
    Node lem = assumption.impNode(node.eqNode(valC));
    Trace("rfp-to-real-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
  if (RFP::isNan(eb,sb, x) || RFP::isInfinite(eb,sb, x))
  {
    Node assumption = node.eqNode(valTerm);
    Node c1 = node[0].eqNode(valTerm);
    Node c2 = mkIsNan(eb,sb, node[0]).orNode(mkIsInf(eb,sb, node[0]));
    Node conclusion = c1.orNode(c2);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-to-real-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE);
  }
}

// RfpAdd

void RfpSolver::checkInitialRefineAdd(Node node) {
  Assert(node.getKind() == RFP_ADD);
  Assert(node.getNumChildren() == 3);
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpAdd>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    // add_finite
    Node aX = mkIsNormal(eb,sb, node[1])
      .orNode(mkIsSubnormal(eb,sb, node[1]));
    Node aY = mkIsNormal(eb,sb, node[2])
      .orNode(mkIsSubnormal(eb,sb, node[2]));
    //Node aX = mkIsFinite(eb,sb, node[1])
    //  .andNode(mkIsZero(eb,sb, node[1]).notNode());
    //Node aY = mkIsFinite(eb,sb, node[2])
    //  .andNode(mkIsZero(eb,sb, node[2]).notNode());
    Node addXY = nm->mkNode(kind::ADD, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], addXY);
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    //Node isFinite = mkIsFinite(eb,sb, node);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], addXY);
    //Node conclusion = isFinite.andNode(node.eqNode(rounded));
    Node conclusion = node.eqNode(rounded);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; add_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // add_finite_rev
    Node assumption = mkIsFinite(eb,sb, node);
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node conclusion = isFiniteX.andNode(isFiniteY);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; add_finite_rev ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // add_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    Node assumption = mkIsFinite(eb,sb, node).andNode(isTN);
    Node addXY = nm->mkNode(kind::ADD, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], addXY);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], addXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; add_finite_rev_n ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // add_special
    std::vector<Node> conj;
    conj.push_back(
      mkIsNan(eb,sb, node[1]).orNode(mkIsNan(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[2])))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[1])))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
          .andNode(mkSameSign(eb,sb, node[1], node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[1])))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
          .andNode(mkDiffSign(eb,sb, node[1], node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    Node addXY = nm->mkNode(ADD, node[1], node[2]);
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(mkNoOverflow(eb,sb, node[0], addXY).notNode())
        .impNode(mkSameSign(eb,sb, node, addXY)
          .andNode(mkIsOverflowValue(eb,sb, node[0], node)))
      );
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
        .impNode(mkSameSign(eb,sb, node[1], node[2])
          .iteNode(mkSameSign(eb,sb, node, node[1]), 
                   mkSignZeroResult(eb,sb, node[0], node)))
      );
    Node lem = nm->mkAnd(conj);
    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; add_special ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // add_rounded
    Node lem = mkIsRounded(eb,sb, node);

    //Node range = mkRangeConstraint(eb,sb, node);
    ////Node rangeX = mkRangeConstraint(eb,sb, node[1]);
    ////Node rangeY = mkRangeConstraint(eb,sb, node[2]);
    ////Node lem = range.andNode(rangeX).andNode(rangeY);
    //Node lem = range;

    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; add_rounded ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

void RfpSolver::checkFullRefineAdd(Node node)
{
  Trace("rfp-add") << "RFP_ADD term: " << node << std::endl;
  Assert(node.getKind() == RFP_ADD);
  Assert(node.getNumChildren() == 3);
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpAdd>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valAdd = d_model.computeAbstractModelValue(node);
  Node valAddC = d_model.computeConcreteModelValue(node);

  Node valXA = d_model.computeAbstractModelValue(node[1]);
  Node valYA = d_model.computeAbstractModelValue(node[2]);
  Rational add = valAdd.getConst<Rational>();

  Node valRm = d_model.computeConcreteModelValue(node[0]);
  Node valX = d_model.computeConcreteModelValue(node[1]);
  Node valY = d_model.computeConcreteModelValue(node[2]);

  Integer rm = valRm.getConst<Rational>().getNumerator();
  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();

  if (TraceIsOn("rfp-add"))
  {
    Trace("rfp-add") << "* " << node << std::endl;
    //Trace("rfp-add") << "  value = " << valAdd << std::endl;
    Trace("rfp-add") << "  value  (" << valXA << ", " << valYA 
                     << ") = " << valAdd << std::endl;
    //Trace("rfp-add") << "          " << ARFP(eb,sb, add) << std::endl;
    Rational xA = valXA.getConst<Rational>();
    Rational yA = valYA.getConst<Rational>();
    Trace("rfp-add") << "         (" << rm << ", " 
                     << ARFP(eb,sb, xA) << ", " << ARFP(eb,sb, yA)
                     << ") = " << ARFP(eb,sb, add) << std::endl;
    Trace("rfp-add") << "  actual (" << rm << ", " << x << ", " << y
                     << ") = " << valAddC << std::endl;

    Rational tC = valAddC.getConst<Rational>();
    Trace("rfp-add") << "         (" << rm << ", " 
                     << ARFP(eb,sb, x) << ", " << ARFP(eb,sb, y)
                     << ") = " << ARFP(eb,sb, tC) << std::endl;
  }
  if (valAdd == valAddC)
  {
    Trace("rfp-add") << "...already correct" << std::endl;
    return;
  }

  if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)) 
  {
    if (add != y 
      && RFP::isZero(eb,sb, x) && !RFP::isZero(eb,sb, y))
    {
      // add_zero 1
      Node isZeroX = mkIsZero(eb,sb, node[1]);
      Node isFiniteY = mkIsFinite(eb,sb, node[2]);
      Node isNotZeroY = mkIsZero(eb,sb, node[2]).notNode();
      Node assumption = isZeroX.andNode(isFiniteY).andNode(isNotZeroY);
      Node conclusion = node.eqNode(node[2]);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_zero 1 ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
    if (add != x
      && !RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      // add_zero 2
      Node isFiniteX = mkIsFinite(eb,sb, node[1]);
      Node isNotZeroX = mkIsZero(eb,sb, node[1]).notNode();
      Node isZeroY = mkIsZero(eb,sb, node[2]);
      Node assumption = isFiniteX.andNode(isNotZeroX).andNode(isZeroY);
      Node conclusion = node.eqNode(node[1]);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_zero 2 ; AUX_REFINE"
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
    //  Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
    //                         << std::endl;
    //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    //}
  }

  //// add_special 1,4,5: handled by VALUE_REFINE?

  //if ((!RFP::isInfinite(eb,sb, add) || (add < 0) != (y < 0))
  //  && RFP::isFinite(eb,sb, x) && RFP::isInfinite(eb,sb, y))
  //{
  //  Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //  Node isInfY = mkIsInf(eb,sb, node[2]);
  //  Node assumption = isFiniteX.andNode(isInfY);
  //  Node isInf = mkIsInf(eb,sb, node);
  //  Node sameSignRY = mkSameSign(eb,sb, node, node[2]);
  //  Node conclusion = isInf.andNode(sameSignRY);
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
  //                         << " ; add_special 2 ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);

  //}
  //if ((!RFP::isInfinite(eb,sb, add) || (add < 0) != (x < 0))
  //  && RFP::isInfinite(eb,sb, x) && RFP::isFinite(eb,sb, y))
  //{
  //  Node isInfX = mkIsInf(eb,sb, node[1]);
  //  Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //  Node assumption = isInfX.andNode(isFiniteY);
  //  Node isInf = mkIsInf(eb,sb, node);
  //  Node sameSignRX = mkSameSign(eb,sb, node, node[1]);
  //  Node conclusion = isInf.andNode(sameSignRX);
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
  //                         << " ; add_special 3 ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  //if (!RFP::isInfinite(eb,sb, add)
  //  && RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)
  //  && !RFP::isFinite(eb,sb, x + y))
  //{
  //  // add_special 6 weakened

  //  Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //  Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //  Node addXY = nm->mkNode(kind::ADD, node[1], node[2]);
  //  Node overflow = mkNoOverflow(eb,sb, node[0], addXY).notNode();
  //  Node assumption = isFiniteX.andNode(isFiniteY).andNode(overflow);
  //  Node conclusion = mkIsOverflowValue(eb,sb, node[0], node);
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
  //                         << " ; add_special 6 ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  //if ((x >= 0 == y >= 0) && (add >= 0 != x >= 0)
  //  && RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y))
  //{
  //  // add_special 7 weakened

  //  Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //  Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //  Node sameSignXY = mkSameSign(eb,sb, node[1], node[2]);
  //  Node sameSignRX = mkSameSign(eb,sb, node, node[1]);
  //  Node assumption = isFiniteX.andNode(isFiniteY).andNode(sameSignXY);
  //  Node lem = nm->mkNode(IMPLIES, assumption, sameSignRX);
  //  Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
  //                         << " ; add_special 7 ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  // this is the most naive model-based schema based on model values
  Node lem = opValueBasedLemma(node);
  Trace("rfp-add-lemma")
      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
    nullptr, true);
}

// RfpNeg

void RfpSolver::checkInitialRefineNeg(Node node) {
  Assert(node.getKind() == RFP_NEG);
  Assert(node.getNumChildren() == 1);
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpNeg>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    // neg_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node assumption = isFiniteX.andNode(isNotZeroX);

    Node negX = nm->mkNode(kind::NEG, node[0]);
    Node conclusion = node.eqNode(negX);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-neg-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; neg_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // neg_zero
    Node assumption = mkIsZero(eb,sb, node[0]);

    Node isFinite = mkIsFinite(eb,sb, node);
    Node isZero = mkIsZero(eb,sb, node);
    //Node conclusion = isFinite.andNode(isZero);
    Node conclusion = isZero;

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-neg-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; neg_zero ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // neg_finite_rev
    Node isFinite = mkIsFinite(eb,sb, node);
    Node isNotZero = mkIsZero(eb,sb, node).notNode();
    Node assumption = isFinite.andNode(isNotZero);

    Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node negX = node.eqNode(nm->mkNode(kind::NEG, node[0]));
    Node conclusion = isFiniteX.andNode(negX);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-neg-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; neg_zero ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // neg_special
    // TODO
    Node l1 = mkIsNan(eb,sb, node[0]).eqNode(mkIsNan(eb,sb, node));
    Node l2 = mkIsInf(eb,sb, node[0]).eqNode(mkIsInf(eb,sb, node));
    Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
    Node isDiffSign = mkDiffSign(eb,sb, node[0], node);
    Node l3 = isNotNanX.impNode(isDiffSign);
    Node lem = l1.andNode(l2).andNode(l3);
    Trace("rfp-neg-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; neg_special ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // neg_rounded
    Node lem = mkIsRounded(eb,sb, node);
    //Node range = mkRangeConstraint(eb,sb, node);
    //Node rangeX = mkRangeConstraint(eb,sb, node[0]);
    //Node lem = range;
    Trace("rfp-neg-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; neg_range ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

void RfpSolver::checkFullRefineNeg(Node node)
{
  Trace("rfp-neg") << "RFP_NEG term: " << node << std::endl;
  Assert(node.getKind() == RFP_NEG);
  Assert(node.getNumChildren() == 1);
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpNeg>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valX = d_model.computeConcreteModelValue(node[0]);

  Rational x = valX.getConst<Rational>();
  Rational t = valTerm.getConst<Rational>();

  if (TraceIsOn("rfp-neg"))
  {
    Trace("rfp-neg") << "* " << node << ", value = " << valTerm
                     << std::endl;
    Trace("rfp-neg") << "  actual (" << x << ") = " << valTermC 
                     << std::endl;

    Rational tC = valTermC.getConst<Rational>();
    Trace("rfp-neg") << "         (" << ARFP(eb,sb, x)
                     << ") = " << ARFP(eb,sb, tC) << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-neg") << "...already correct" << std::endl;
    return;
  }

  // this is the most naive model-based schema based on model values
  Node valC = nm->mkNode(RFP_NEG, node.getOperator(), valX);
  valC = rewrite(valC);
  Node assumption = node[0].eqNode(valX);
  Node lem = assumption.impNode(node.eqNode(valC));
  Trace("rfp-neg-lemma") << "RfpSolver::Lemma: " << lem 
                         << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                       nullptr, true);
}

// RfpSub

void RfpSolver::checkInitialRefineSub(Node node) {
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpSub>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    // sub_finite
    Node aX = mkIsNormal(eb,sb, node[1])
      .orNode(mkIsSubnormal(eb,sb, node[1]));
    Node aY = mkIsNormal(eb,sb, node[2])
      .orNode(mkIsSubnormal(eb,sb, node[2]));
    Node subXY = nm->mkNode(kind::SUB, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], subXY);
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], subXY);
    Node conclusion = node.eqNode(rounded);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-sub-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; sub_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // sub_finite_rev
    Node assumption = mkIsFinite(eb,sb, node);
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node conclusion = isFiniteX.andNode(isFiniteY);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-sub-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; sub_finite_rev ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // sub_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    Node assumption = mkIsFinite(eb,sb, node).andNode(isTN);
    Node subXY = nm->mkNode(kind::SUB, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], subXY);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], subXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-sub-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; sub_finite_rev_n ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // sub_special
    std::vector<Node> conj;
    conj.push_back(
      mkIsNan(eb,sb, node[1]).orNode(mkIsNan(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkDiffSign(eb,sb, node, node[2])))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[1])))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
          .andNode(mkSameSign(eb,sb, node[1], node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
          .andNode(mkDiffSign(eb,sb, node[1], node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[1])))
      );
    Node subXY = nm->mkNode(SUB, node[1], node[2]);
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(mkNoOverflow(eb,sb, node[0], subXY).notNode())
        .impNode(mkSameSign(eb,sb, node, subXY)
          .andNode(mkIsOverflowValue(eb,sb, node[0], node)))
      );
    conj.push_back(
      mkIsZero(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
        .impNode(mkDiffSign(eb,sb, node[1], node[2])
          .iteNode(mkSameSign(eb,sb, node, node[1]), 
                   mkSignZeroResult(eb,sb, node[0], node)))
      );
    Node lem = nm->mkAnd(conj);
    Trace("rfp-sub-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; sub_special ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // sub_rounded
    Node lem = mkIsRounded(eb,sb, node);
    //Node lem = mkRangeConstraint(eb,sb, node);
    Trace("rfp-sub-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; sub_rounded ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

void RfpSolver::checkFullRefineSub(Node node)
{
  Trace("rfp-sub") << "RFP_SUB term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpSub>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valRm = d_model.computeConcreteModelValue(node[0]);
  Node valX = d_model.computeConcreteModelValue(node[1]);
  Node valY = d_model.computeConcreteModelValue(node[2]);

  Integer rm = valRm.getConst<Rational>().getNumerator();
  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Rational t = valTerm.getConst<Rational>();

  if (TraceIsOn("rfp-sub"))
  {
    Trace("rfp-sub") << "* " << node << ", value = " << valTerm
                     << std::endl;
    Trace("rfp-sub") << "  actual (" << rm << ", " << x << ", " << y
                     << ") = " << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-sub") << "...already correct" << std::endl;
    return;
  }

  // this is the most naive model-based schema based on model values
  Node lem = opValueBasedLemma(node);
  Trace("rfp-sub-lemma")
      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                       nullptr, true);
}

// RfpMult

void RfpSolver::checkInitialRefineMult(Node node) 
{
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpMult>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  //{
  //  // mul_finite
  //  Node aX = mkIsNormal(eb,sb, node[1])
  //    .orNode(mkIsSubnormal(eb,sb, node[1]));
  //  Node aY = mkIsNormal(eb,sb, node[2])
  //    .orNode(mkIsSubnormal(eb,sb, node[2]));
  //  Node multXY = nm->mkNode(kind::MULT, node[1], node[2]);
  //  multXY = rewrite(multXY);
  //  Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
  //  Node assumption = aX.andNode(aY).andNode(noOverflow);

  //  Node op = nm->mkConst(RfpRound(eb, sb));
  //  Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], multXY);
  //  Node conclusion = node.eqNode(rounded);

  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem 
  //                          << " ; mul_finite ; INIT_REFINE"
  //                          << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  //}

  //{
  //  // mul_finite_rev
  //  Node assumption = mkIsFinite(eb,sb, node);
  //  Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //  Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //  Node conclusion = isFiniteX.andNode(isFiniteY);
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
  //                          << " ; mul_finite_rev ; INIT_REFINE"
  //                          << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  //}
  //{
  //  // mul_finite_rev_n
  //  Node isTN = mkIsToNearest(node[0]);
  //  Node assumption = mkIsFinite(eb,sb, node).andNode(isTN);
  //  Node multXY = nm->mkNode(kind::MULT, node[1], node[2]);
  //  Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
  //  Node op = nm->mkConst(RfpRound(eb, sb));
  //  Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], multXY);
  //  Node conclusion = noOverflow.andNode(node.eqNode(rounded));
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
  //                          << " ; mul_finite_rev_n ; INIT_REFINE"
  //                          << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  //}

  // TODO
  {
    // mul_zero 1
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isZeroY = mkIsZero(eb,sb, node[2]);
    Node assumption = isFiniteX.andNode(isZeroY);
    Node conclusion = mkIsZero(eb,sb, node);
    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // mul_zero 2
    Node isZeroX = mkIsZero(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node assumption = isZeroX.andNode(isFiniteY);
    Node conclusion = mkIsZero(eb,sb, node);
    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }

  {
    // mul_special
    std::vector<Node> conj;
    conj.push_back(
      mkIsNan(eb,sb, node[1]).orNode(mkIsNan(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsZero(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
          .andNode(mkIsZero(eb,sb, node[1]).notNode())
        .impNode(mkIsInf(eb,sb, node))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsZero(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(mkIsZero(eb,sb, node[2]).notNode())
        .impNode(mkIsInf(eb,sb, node))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node))
      );
    Node multXY = nm->mkNode(MULT, node[1], node[2]);
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(mkNoOverflow(eb,sb, node[0], multXY).notNode())
        .impNode(mkIsOverflowValue(eb,sb, node[0], node))
      );
    conj.push_back(
      mkIsNan(eb,sb, node).notNode()
        .impNode(mkProductSign(eb,sb, node, node[1], node[2]))
      );
    Node lem = nm->mkAnd(conj);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
                            << " ; mul_special ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // mul_rounded
    Node lem = mkIsRounded(eb,sb, node);
    //Node lem = mkRangeConstraint(eb,sb, node);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; mul_range ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

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
  
  if ((RFP::isNormal(eb,sb, x) || RFP::isSubnormal(eb,sb, x))
    && (RFP::isNormal(eb,sb, y) || RFP::isSubnormal(eb,sb, y)) 
    && RFP::isFinite(eb,sb, x*y)
    //&& mult != RFP::round(eb,sb, rm.toUnsignedInt(), x*y)
    )
  {
    // mul_finite
    Node aX = mkIsNormal(eb,sb, node[1])
      .orNode(mkIsSubnormal(eb,sb, node[1]));
    Node aY = mkIsNormal(eb,sb, node[2])
      .orNode(mkIsSubnormal(eb,sb, node[2]));
    Node multXY = nm->mkNode(kind::MULT, node[1], node[2]);
    multXY = rewrite(multXY);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], multXY);
    Node conclusion = node.eqNode(rounded);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem 
                            << " ; mul_finite ; AUX_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }
  
  if (RFP::isFinite(eb,sb, mult) 
    && (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y)))
  {
    // mul_finite_rev
    Node assumption = mkIsFinite(eb,sb, node);
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node conclusion = isFiniteX.andNode(isFiniteY);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
                            << " ; mul_finite_rev ; AUX_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  if (RFP::isFinite(eb,sb, mult) 
    && RFP::isFinite(eb,sb, x*y))
  {
    // mul_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    Node assumption = mkIsFinite(eb,sb, node).andNode(isTN);
    Node multXY = nm->mkNode(kind::MULT, node[1], node[2]);
    multXY = rewrite(multXY);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], multXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
                            << " ; mul_finite_rev_n ; AUX_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  //if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)) 
  //{
  //  if (!RFP::isZero(eb,sb, mult)
  //    //&& !RFP::isZero(eb,sb, x) 
  //    && RFP::isZero(eb,sb, y))
  //  {
  //    // mul_zero 1
  //    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //    Node isZeroY = mkIsZero(eb,sb, node[2]);
  //    Node assumption = isFiniteX.andNode(isZeroY);
  //    Node conclusion = mkIsZero(eb,sb, node);
  //    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                           << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  //  }
  //  if (!RFP::isZero(eb,sb, mult)
  //    && RFP::isZero(eb,sb, x) 
  //    //&& !RFP::isZero(eb,sb, y)
  //    )
  //  {
  //    // mul_zero 2
  //    Node isZeroX = mkIsZero(eb,sb, node[1]);
  //    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //    Node assumption = isZeroX.andNode(isFiniteY);
  //    Node conclusion = mkIsZero(eb,sb, node);
  //    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                           << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  //  }
  //}

  //// mul_special 1-2,4,6: delegate to VALUE_REFINE. 

  //if (!RFP::isInfinite(eb,sb, mult)) 
  //{
  //  if (RFP::isFinite(eb,sb, x) && RFP::isInfinite(eb,sb, y) && !RFP::isZero(eb,sb, y))
  //  {
  //    // mul_special 3
  //    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //    Node isInfY = mkIsInf(eb,sb, node[2]);
  //    Node isNotZeroY = mkIsZero(eb,sb, node[2]).notNode();
  //    Node assumption = isFiniteX.andNode(isInfY.andNode(isNotZeroY));
  //    Node conclusion = mkIsInf(eb,sb, node);
  //    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                            << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
  //  }
  //  if (RFP::isInfinite(eb,sb, x) && !RFP::isZero(eb,sb, x) && RFP::isFinite(eb,sb, y))
  //  {
  //    // mul_special 5
  //    Node isInfX = mkIsInf(eb,sb, node[1]);
  //    Node isNotZeroX = mkIsZero(eb,sb, node[1]).notNode();
  //    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //    Node assumption = isInfX.andNode(isNotZeroX.andNode(isFiniteY));
  //    Node conclusion = mkIsInf(eb,sb, node);
  //    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                            << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
  //  }
  //  if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)
  //    && !RFP::isFinite(eb,sb, x * y))
  //  {
  //    // mul_special 7
  //    Node isFiniteX = mkIsInf(eb,sb, node[1]);
  //    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //    Node multXY = nm->mkNode(kind::MULT, node[1], node[2]);
  //    Node overflow = mkIsFinite(eb,sb, multXY).notNode();
  //    Node assumption = isFiniteX.andNode(isFiniteY.andNode(overflow));
  //    Node conclusion = mkIsInf(eb,sb, node);
  //    Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                            << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
  //  }
  //}

  //if ((mult == RFP::notANumber(eb,sb) || mult < 0)
  //  && (x >= 0 == y >= 0))
  //{
  //  // mul_special 8 positive case
  //  Node isNotNan = mkIsNan(eb,sb, node).notNode();
  //  Node isSameSign = mkSameSign(eb,sb, node[1], node[2]);
  //  Node assumption = isNotNan.andNode(isSameSign);
  //  Node conclusion = mkIsPos(eb,sb, node);
  //  Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //  Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                          << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
  //}
  //if ((mult == RFP::notANumber(eb,sb) || mult >= 0)
  //  && (x >= 0 != y >= 0))
  //{
  //  // mul_special 8 negative case
  //  Node isNotNan = mkIsNan(eb,sb, node).notNode();
  //  Node isDiffSign = mkDiffSign(eb,sb, node[1], node[2]);
  //  Node assumption = isNotNan.andNode(isDiffSign);
  //  Node conclusion = mkIsNeg(eb,sb, node);
  //  Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //  Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //                          << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE, nullptr, true);
  //}

  // this is the most naive model-based schema based on model values
  Node lem = opValueBasedLemma(node);
  Trace("rfp-mult-lemma")
      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                       nullptr, true);
}

// RfpDiv

void RfpSolver::checkInitialRefineDiv(Node node) {
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpDiv>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    // div_finite
    Node aX = mkIsNormal(eb,sb, node[1])
      .orNode(mkIsSubnormal(eb,sb, node[1]));
    Node aY = mkIsNormal(eb,sb, node[2])
      .orNode(mkIsSubnormal(eb,sb, node[2]));
    Node divXY = nm->mkNode(kind::DIVISION, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], divXY);
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    Node op = nm->mkConst(RfpRound(eb,sb));
    Node round = nm->mkNode(kind::RFP_ROUND, op, node[0], divXY);
    Node conclusion = node.eqNode(round);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; div_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // div_finite_rev
    Node assumption = mkIsFinite(eb,sb, node);
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node isNotZeroY = mkIsZero(eb,sb, node[2]).notNode();
    Node isInfY = mkIsInf(eb,sb, node[2]);
    Node isZero = mkIsZero(eb,sb, node);
    Node c1 = isFiniteX.andNode(isFiniteY).andNode(isNotZeroY);
    Node c2 = isFiniteX.andNode(isInfY).andNode(isZero);
    Node conclusion = c1.orNode(c2);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; div_finite_rev ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // div_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    Node assumption = mkIsFinite(eb,sb, node).andNode(isTN);
    Node divXY = nm->mkNode(kind::DIVISION, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], divXY);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], divXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
                            << " ; mul_finite_rev_n ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // div_special
    std::vector<Node> conj;
    //conj.push_back(
    //  mkIsNan(eb,sb, node[1]).orNode(mkIsNan(eb,sb, node[2]))
    //    .impNode(mkIsNan(eb,sb, node))
    //  );
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
        .impNode(mkIsZero(eb,sb, node))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node))
      );
    conj.push_back(
      mkIsInf(eb,sb, node[1]).andNode(mkIsInf(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    Node divXY = nm->mkNode(DIVISION, node[1], node[2]);
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(mkIsZero(eb,sb, node[2]).notNode())
          .andNode(mkNoOverflow(eb,sb, node[0], divXY).notNode())
        .impNode(mkIsOverflowValue(eb,sb, node[0], node))
      );
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsZero(eb,sb, node[2]))
          .andNode(mkIsZero(eb,sb, node[1]).notNode())
        .impNode(mkIsInf(eb,sb, node))
      );
    conj.push_back(
      mkIsZero(eb,sb, node[1]).andNode(mkIsZero(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsNan(eb,sb, node).notNode()
        .impNode(mkProductSign(eb,sb, node, node[1], node[2]))
      );
    Node lem = nm->mkAnd(conj);
    Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; div_special ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // div_rounded
    Node lem = mkIsRounded(eb,sb, node);
    //Node lem = mkRangeConstraint(eb,sb, node);
    Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; div_rounded ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

void RfpSolver::checkFullRefineDiv(Node node)
{
  Trace("rfp-div") << "RFP_DIV term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpDiv>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valRm = d_model.computeConcreteModelValue(node[0]);
  Node valX = d_model.computeConcreteModelValue(node[1]);
  Node valY = d_model.computeConcreteModelValue(node[2]);

  Integer rm = valRm.getConst<Rational>().getNumerator();
  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Rational t = valTerm.getConst<Rational>();

  if (TraceIsOn("rfp-div"))
  {
    Trace("rfp-div") << "* " << node << ", value = " << valTerm
                     << std::endl;
    Trace("rfp-div") << "  actual (" << rm << ", " << x << ", " << y
                     << ") = " << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-div") << "...already correct" << std::endl;
    return;
  }

  // this is the most naive model-based schema based on model values
  Node lem = opValueBasedLemma(node);
  Trace("rfp-div-lemma")
      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                       nullptr, true);
}

/* Handlers for relational operators. */

Node mkRelConstr(Node node)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lb = nm->mkNode(LEQ, nm->mkConstInt(Rational(0)), node);
  Node ub = nm->mkNode(LEQ, node, nm->mkConstInt(Rational(1)));
  return nm->mkNode(AND, lb, ub);
}

// RfpLt

Node mkLtSpecial(uint32_t eb, uint32_t sb, TNode node)
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

void RfpSolver::checkInitialRefineLt(Node node) 
{
  Trace("rfp-lt") << "RFP_LT term (init): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpLt>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    // lt_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isFiniteX.andNode(isFiniteY.andNode(
      isNotZeroX.orNode(isNotZeroY)));

    Node ltBool = mkTrue(node);
    Node ltXY = nm->mkNode(kind::LT, node[0], node[1]);
    Node conclusion = ltBool.eqNode(ltXY);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; lt_finite ; INIT_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // lt_zero
    Node isZeroX = mkIsZero(eb,sb, node[0]);
    Node isZeroY = mkIsZero(eb,sb, node[1]);
    Node assumption = isZeroX.andNode(isZeroY);
    Node conclusion = mkFalse(node);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; lt_zero ; INIT_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // lt_special
    Node lem = mkLtSpecial(eb,sb, node);
    Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; lt_special ; INIT_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
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

    Trace("rfp-lt") << "         ("
                     << ARFP(eb,sb, x) << ", " << ARFP(eb,sb, y)
                     << ") = " << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-lt") << "...already correct" << std::endl;
    return;
  }

  //if (t < Integer(0) || Integer(1) < t)
  //{
  //  Node lem = mkRelConstr(node);
  //  Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE0"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  //if ((t != 0) != x < y
  //  && RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)
  //  && (!RFP::isZero(eb,sb, x) || !RFP::isZero(eb,sb, y)))
  //{
  //  // lt_finite
  //  Node isFiniteX = mkIsFinite(eb,sb, node[0]);
  //  Node isFiniteY = mkIsFinite(eb,sb, node[1]);
  //  Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
  //  Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
  //  Node assumption = isFiniteX.andNode(isFiniteY.andNode(
  //    isNotZeroX.orNode(isNotZeroY)));
  //  Node ltBool = mkTrue(node);
  //  Node ltXY = nm->mkNode(kind::LT, node[0], node[1]);
  //  Node conclusion = ltBool.eqNode(ltXY);
  //  Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //  Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem 
  //                        << " ; lt_finite ; AUX_REFINE"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  //if (x != RFP::notANumber(eb,sb) && y != RFP::notANumber(eb,sb))
  //{
  //  // not_lt_ge
  //  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  //  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  //  Node assumption = mkFalse(node).andNode(isNotNanX).andNode(isNotNanY);
  //  Node op = nm->mkConst(RfpGeq(eb,sb));
  //  Node geq = nm->mkNode(RFP_GEQ, op, node[0], node[1]);
  //  Node lem = assumption.impNode(mkTrue(geq));
  //  Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem 
  //                        << " ; not_lt_ge ; AUX_REFINE"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  {
    // lt_special
    Node lem = mkLtSpecial(eb,sb, node);
    Trace("rfp-lt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; lt_special ; AUX_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }
  //else
  {
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
}

// RfpLeq

Node mkLeqSpecial(uint32_t eb, uint32_t sb, TNode node)
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

void RfpSolver::checkInitialRefineLeq(Node node) 
{
  Trace("rfp-leq") << "RFP_LEQ term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpLeq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    // le_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isFiniteX.andNode(isFiniteY).andNode(
      isNotZeroX.orNode(isNotZeroY));

    Node leqBool = mkTrue(node);
    Node leqXY = nm->mkNode(kind::LEQ, node[0], node[1]);
    Node conclusion = leqBool.eqNode(leqXY);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; le_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // le_zero
    Node isZeroX = mkIsZero(eb,sb, node[0]);
    Node isZeroY = mkIsZero(eb,sb, node[1]);
    Node assumption = isZeroX.andNode(isZeroY);
    Node conclusion = mkTrue(node);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; le_zero ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // le_special
    Node lem = mkLeqSpecial(eb,sb, node);
    Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; le_special ; AUX_INIT"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

void RfpSolver::checkFullRefineLeq(Node node) 
{
  Trace("rfp-leq") << "RFP_LEQ term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpLeq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valXA = d_model.computeAbstractModelValue(node[0]);
  Node valYA = d_model.computeAbstractModelValue(node[1]);
  Node valX = d_model.computeConcreteModelValue(node[0]);
  Node valY = d_model.computeConcreteModelValue(node[1]);

  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Integer t = valTerm.getConst<Rational>().getNumerator();

  if (TraceIsOn("rfp-leq"))
  {
    Trace("rfp-leq") << "* " << node 
                     //<< ", value = " << valTerm
                     << std::endl;
    Trace("rfp-leq") << "  value  (" << valXA << ", " << valYA << ") = " 
                     << valTerm
                     << std::endl;
    Trace("rfp-leq") << "  actual (" << x << ", " << y << ") = " 
                     << valTermC << std::endl;

    Trace("rfp-leq") << "         ("
                     << ARFP(eb,sb, x) << ", " << ARFP(eb,sb, y)
                     << ") = " << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-leq") << "...already correct" << std::endl;
    return;
  }

  //if (t < Integer(0) || Integer(1) < t)
  //{
  //  Node lem = mkRelConstr(node);
  //  Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE0"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  //if ((t != 0) != x < y
  //  && RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)
  //  && (!RFP::isZero(eb,sb, x) || !RFP::isZero(eb,sb, y)))
  //{
  //  // le_finite
  //  Node isFiniteX = mkIsFinite(eb,sb, node[0]);
  //  Node isFiniteY = mkIsFinite(eb,sb, node[1]);
  //  Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
  //  Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
  //  Node assumption = isFiniteX.andNode(isFiniteY.andNode(
  //    isNotZeroX.orNode(isNotZeroY)));

  //  //Node leqBool = mkTrue(node);
  //  Node leqXY = nm->mkNode(kind::LEQ, node[0], node[1]);
  //  //Node conclusion = leqBool.eqNode(leqXY);

  //  Node leqXYInt = nm->mkNode(kind::ITE, leqXY, nm->mkConstInt(1), nm->mkConstInt(0));
  //  Node conclusion = node.eqNode(leqXY);

  //  Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //  Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem 
  //                         << " ; le_finite ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  //if (x != RFP::notANumber(eb,sb) && y != RFP::notANumber(eb,sb))
  //{
  //  // not_gt_le
  //  Node op = nm->mkConst(RfpGt(eb,sb));
  //  Node gt = nm->mkNode(RFP_GT, op, node[0], node[1]);
  //  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  //  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  //  Node assumption = mkFalse(gt).andNode(isNotNanX).andNode(isNotNanY);
  //  Node lem = assumption.impNode(mkTrue(node));
  //  Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem 
  //                         << " ; not_gt_le ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  {
    // leq_special
    Node lem = mkLeqSpecial(eb,sb, node);
    Trace("rfp-leq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; leq_special ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }
  //else
  {
    // this is the most naive model-based schema based on model values
    Node lem = relValueBasedLemma(node);
    Trace("rfp-leq-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
}

// RfpGt

void RfpSolver::checkInitialRefineGt(Node node) 
{
  Trace("rfp-gt") << "RFP_GT term (init): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpGt>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  // convert to RFP_LT
  Node op = nm->mkConst(RfpLt(eb, sb));
  Node lt = nm->mkNode(kind::RFP_LT, op, node[1], node[0]);
  Node lem = node.eqNode(lt);
  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                        << " ; INIT_REFINE"
                        << std::endl;
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
}

// RfpGeq

void RfpSolver::checkInitialRefineGeq(Node node) 
{
  Trace("rfp-geq") << "RFP_GEQ term (init): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpGeq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  // convert to RFP_LEQ
  Node op = nm->mkConst(RfpLeq(eb, sb));
  Node leq = nm->mkNode(kind::RFP_LEQ, op, node[1], node[0]);
  Node lem = node.eqNode(leq);
  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                        << " ; INIT_REFINE"
                        << std::endl;
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
