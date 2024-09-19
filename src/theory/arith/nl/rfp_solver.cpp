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

#include "options/base_options.h"
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
      //case Kind::RFP_TO_REAL: hash = n.getOperator().getConst<RfpToReal>(); break;
      case Kind::RFP_ADD: hash = n.getOperator().getConst<RfpAdd>(); break;
      case Kind::RFP_NEG: hash = n.getOperator().getConst<RfpNeg>(); break;
      case Kind::RFP_SUB: hash = n.getOperator().getConst<RfpSub>(); break;
      case Kind::RFP_MULT: hash = n.getOperator().getConst<RfpMult>(); break;
      case Kind::RFP_DIV: hash = n.getOperator().getConst<RfpDiv>(); break;
      //case Kind::RFP_LT:  hash = n.getOperator().getConst<RfpLt>(); break;
      //case Kind::RFP_LEQ: hash = n.getOperator().getConst<RfpLeq>(); break;
      case Kind::RFP_GT:  hash = n.getOperator().getConst<RfpGt>(); break;
      case Kind::RFP_GEQ: hash = n.getOperator().getConst<RfpGeq>(); break;
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
          //case Kind::RFP_TO_REAL: checkInitialRefineToReal(node); break;
          case Kind::RFP_ADD: checkInitialRefineAdd(node); break;
          case Kind::RFP_NEG: checkInitialRefineNeg(node); break;
          case Kind::RFP_SUB: checkInitialRefineSub(node); break;
          case Kind::RFP_MULT: checkInitialRefineMult(node); break;
          case Kind::RFP_DIV: checkInitialRefineDiv(node); break;
          //case Kind::RFP_LT:  checkInitialRefineLt(node); break;
          //case Kind::RFP_LEQ: checkInitialRefineLeq(node); break;
          case Kind::RFP_GT:  checkInitialRefineGt(node); break;
          case Kind::RFP_GEQ: checkInitialRefineGeq(node); break;
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
          //case Kind::RFP_TO_REAL: checkFullRefineToReal(node); break;
          case Kind::RFP_ADD: checkFullRefineAdd(node); break;
          case Kind::RFP_NEG: checkFullRefineNeg(node); break;
          case Kind::RFP_SUB: checkFullRefineSub(node); break;
          case Kind::RFP_MULT: checkFullRefineMult(node); break;
          case Kind::RFP_DIV: checkFullRefineDiv(node); break;
          case Kind::RFP_GT:  checkFullRefineGt(node); break;
          case Kind::RFP_GEQ: checkFullRefineGeq(node); break;
          case Kind::RFP_LT:
          case Kind::RFP_LEQ:
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

  {
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
}

Node RfpSolver::opValueBasedLemma(TNode n)
{
  Assert(n.getKind() == Kind::RFP_ADD 
      || n.getKind() == Kind::RFP_SUB
      || n.getKind() == Kind::RFP_MULT
      || n.getKind() == Kind::RFP_DIV
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

  Node assumption = rm.eqNode(valRm).andNode(x.eqNode(valX)).andNode(y.eqNode(valY));
  return assumption.impNode(n.eqNode(valC));
}

Node RfpSolver::relValueBasedLemma(TNode n)
{
  Assert(n.getKind() == Kind::RFP_GT || n.getKind() == Kind::RFP_GEQ);
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

  Node assumption = x.eqNode(valX).andNode(y.eqNode(valY));
  return assumption.impNode(n.eqNode(valC));
}

// RfpToReal

//void RfpSolver::checkInitialRefineToReal(Node node) 
//{
//  Trace("rfp-to-real") << "RFP_TO_REAL term (init): " << node << std::endl;
//  NodeManager* nm = NodeManager::currentNM();
//  FloatingPointSize sz = node.getOperator().getConst<RfpToReal>().getSize();
//  uint32_t eb = sz.exponentWidth();
//  uint32_t sb = sz.significandWidth();
//
//  {
//    Node a1 = mkIsFinite(eb,sb, node[0]);
//    //Node a2 = mkIsFinite(eb,sb, node);
//    //Node assumption = a1.orNode(a2);
//    Node assumption = a1;
//    Node isZeroX = mkIsZero(eb,sb, node[0]);
//    Node isZero = node.eqNode(nm->mkConstReal(0)); 
//    Node eqX = node.eqNode(node[0]);
//    Node conclusion = isZeroX.iteNode(isZero, eqX);
//    Node lem = assumption.impNode(conclusion);
//    Trace("rfp-to-real-lemma")
//        << "RfpSolver::Lemma: " << lem << " ; INIT_REFINE" << std::endl;
//    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
//  }
//  {
//    Node isNormal = mkIsNormal(eb,sb, node);
//    Node isSubnormal = mkIsSubnormal(eb,sb, node);
//    Node isZero = mkIsZero(eb,sb, node);
//    Node isInf = mkIsInf(eb,sb, node);
//    Node isNan = mkIsNan(eb,sb, node);
//    Node lem = isNormal.orNode(isSubnormal).orNode(isZero).orNode(isInf).orNode(isNan);
//    Trace("rfp-to-real-lemma") << "RfpSolver::Lemma: " << lem
//                               << " ; round_cases ; INIT_REFINE"
//                               << std::endl;
//    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
//  }
//}

//void RfpSolver::checkFullRefineToReal(Node node) 
//{
//  Trace("rfp-to-real") << "RFP_TO_REAL term: " << node << std::endl;
//  NodeManager* nm = NodeManager::currentNM();
//  FloatingPointSize sz = node.getOperator().getConst<RfpToReal>().getSize();
//  uint32_t eb = sz.exponentWidth();
//  uint32_t sb = sz.significandWidth();
//
//  Node valTerm = d_model.computeAbstractModelValue(node);
//  Node valTermC = d_model.computeConcreteModelValue(node);
//
//  Node valXA = d_model.computeAbstractModelValue(node[0]);
//  Node valX = d_model.computeConcreteModelValue(node[0]);
//
//  Rational x = valX.getConst<Rational>();
//  Rational t = valTerm.getConst<Rational>();
//
//  if (TraceIsOn("rfp-to-real"))
//  {
//    Trace("rfp-to-real") << "* " << node 
//                     << std::endl;
//    Trace("rfp-to-real") << "  value  (" << valXA << ") = " 
//                         << valTerm
//                         << std::endl;
//    Trace("rfp-to-real") << "  actual (" << x << ") = " 
//                         << valTermC << std::endl;
//
//    //Rational tC = valTermC.getConst<Rational>();
//    //Trace("rfp-to-real") << "         ("
//    //                     << ARFP(eb,sb, x) << ") = " 
//    //                     << ARFP(eb,sb, tC) << std::endl;
//  }
//  if (valTerm == valTermC)
//  {
//    Trace("rfp-to-real") << "...already correct" << std::endl;
//    return;
//  }
//
//  if (RFP::isNan(eb,sb, x) || RFP::isInfiniteWeak(eb,sb, x))
//  {
//    Node assumption = node.eqNode(nm->mkConstReal(t));
//    Node c1 = node[0].eqNode(nm->mkConstReal(t));
//    Node c2 = mkIsNan(eb,sb, node[0]).orNode(mkIsInf(eb,sb, node[0]));
//    Node conclusion = c1.orNode(c2);
//    Node lem = assumption.impNode(conclusion);
//    Trace("rfp-to-real-lemma")
//        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
//    // send the value lemma
//    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE);
//  }
//}

// RfpAdd

void RfpSolver::checkInitialRefineAdd(Node node) {
  Assert(node.getKind() == Kind::RFP_ADD);
  Assert(node.getNumChildren() == 3);
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpAdd>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    // add_finite
    //Node aX = mkIsNormal(eb,sb, node[1])
    //  .orNode(mkIsSubnormal(eb,sb, node[1]));
    //Node aY = mkIsNormal(eb,sb, node[2])
    //  .orNode(mkIsSubnormal(eb,sb, node[2]));
    Node aX = mkIsFinite(eb,sb, node[1])
      .andNode(mkIsZero(eb,sb, node[1]).notNode());
    Node aY = mkIsFinite(eb,sb, node[2])
      .andNode(mkIsZero(eb,sb, node[2]).notNode());
    Node addXY = nm->mkNode(Kind::ADD, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], addXY);
    noOverflow = rewrite(noOverflow);
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    //Node isFinite = mkIsFinite(eb,sb, node);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], addXY);
    //Node conclusion = isFinite.andNode(node.eqNode(rounded));
    Node conclusion = node.eqNode(rounded);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; add_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // add_zero 1
    Node isZeroX = mkIsZero(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node isNotZeroY = mkIsZero(eb,sb, node[2]).notNode();
    Node assumption = isZeroX.andNode(isFiniteY).andNode(isNotZeroY);
    Node conclusion = node.eqNode(node[2]);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; add_zero 1 ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // add_zero 2
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isNotZeroX = mkIsZero(eb,sb, node[1]).notNode();
    Node isZeroY = mkIsZero(eb,sb, node[2]);
    Node assumption = isFiniteX.andNode(isNotZeroX).andNode(isZeroY);
    Node conclusion = node.eqNode(node[1]);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; add_zero 2 ; INIT_REFINE"
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
  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // add_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    Node isFinite = mkIsFinite(eb,sb, node);
    //Node aX = node[1].eqNode(nm->mkConstReal(RFP::minusZero(eb,sb))).notNode();
    //Node aY = node[2].eqNode(nm->mkConstReal(RFP::minusZero(eb,sb))).notNode();
    Node aX = node.eqNode(node[1]).notNode();
    Node aY = node.eqNode(node[2]).notNode();
    Node assumption = isTN.andNode(isFinite).andNode(aX).andNode(aY);
    Node addXY = nm->mkNode(Kind::ADD, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], addXY);
    noOverflow = rewrite(noOverflow);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], addXY);
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
      mkIsFinite(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[2])))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[1])))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
          .andNode(mkSameSign(eb,sb, node[1], node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[1])))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
          .andNode(mkDiffSign(eb,sb, node[1], node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    Node addXY = nm->mkNode(Kind::ADD, node[1], node[2]);
    Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], addXY));
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(noOverflow.notNode())
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
}

void RfpSolver::checkFullRefineAdd(Node node)
{
  Trace("rfp-add") << "RFP_ADD term: " << node << std::endl;
  Assert(node.getKind() == Kind::RFP_ADD);
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

  //if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) &&
  //    !RFP::isZero(eb,sb, x) && !RFP::isZero(eb,sb, y))
  //{
  //  // add_finite
  //  Node aX = mkIsNormal(eb,sb, node[1])
  //    .orNode(mkIsSubnormal(eb,sb, node[1]));
  //  Node aY = mkIsNormal(eb,sb, node[2])
  //    .orNode(mkIsSubnormal(eb,sb, node[2]));
  //  Node addXY = nm->mkNode(Kind::ADD, node[1], node[2]);
  //  addXY = rewrite(addXY);
  //  Node noOverflow = mkNoOverflow(eb,sb, node[0], addXY);
  //  noOverflow = rewrite(noOverflow);
  //  Node assumption = aX.andNode(aY).andNode(noOverflow);

  //  //Node isFinite = mkIsFinite(eb,sb, node);
  //  Node op = nm->mkConst(RfpRound(eb, sb));
  //  Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], addXY);
  //  Node conclusion = node.eqNode(rounded);

  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
  //                         << " ; add_finite ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  //if (RFP::isFinite(eb,sb, add) && 
  //    (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))) 
  //{
  //  // add_finite_rev
  //  Node assumption = mkIsFinite(eb,sb, node);
  //  Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //  Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //  Node conclusion = isFiniteX.andNode(isFiniteY);
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem
  //                         << " ; add_finite_rev ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG &&
      (rm == IRM::NE || rm == IRM::NA) &&
      RFP::isFinite(eb,sb, add) && add != x && add != y)
  {
    // add_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    Node isFinite = mkIsFinite(eb,sb, node);
    Node aX = node.eqNode(node[1]).notNode();
    Node aY = node.eqNode(node[2]).notNode();
    Node assumption = isTN.andNode(isFinite).andNode(aX).andNode(aY);
    Node addXY = nm->mkNode(Kind::ADD, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], addXY);
    noOverflow = rewrite(noOverflow);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], addXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; add_finite_rev_n ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  //if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)) 
  //{
  //  if (RFP::isZero(eb,sb, x) && !RFP::isZero(eb,sb, y) 
  //      //&& add != y
  //      )
  //  {
  //    // add_zero 1
  //    Node isZeroX = mkIsZero(eb,sb, node[1]);
  //    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //    Node isNotZeroY = mkIsZero(eb,sb, node[2]).notNode();
  //    Node assumption = isZeroX.andNode(isFiniteY).andNode(isNotZeroY);
  //    Node conclusion = node.eqNode(node[2]);
  //    Node lem = assumption.impNode(conclusion);
  //    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
  //                           << " ; add_zero 1 ; AUX_REFINE"
  //                           << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //  }
  //  if (!RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y) 
  //      //&& add != x
  //      )
  //  {
  //    // add_zero 2
  //    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //    Node isNotZeroX = mkIsZero(eb,sb, node[1]).notNode();
  //    Node isZeroY = mkIsZero(eb,sb, node[2]);
  //    Node assumption = isFiniteX.andNode(isNotZeroX).andNode(isZeroY);
  //    Node conclusion = node.eqNode(node[1]);
  //    Node lem = assumption.impNode(conclusion);
  //    Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
  //                           << " ; add_zero 2 ; AUX_REFINE"
  //                           << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //  }
  //  // Covered by VALUE_REFINE.
  //  //if (!RFP::isZero(eb,sb, add) 
  //  //  && RFP::isZero(eb,sb, x) && RFP::isZero(eb,sb, y))
  //  //{
  //  //  // add_zero 3
  //  //  Node isZeroX = mkIsZero(eb,sb, node[1]);
  //  //  Node isZeroY = mkIsZero(eb,sb, node[2]);
  //  //  Node assumption = isZeroX.andNode(isZeroY);
  //  //  Node conclusion = mkIsZero(eb,sb, node);
  //  //  Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
  //  //  Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
  //  //                         << std::endl;
  //  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //  //}
  //}

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
  //  Node addXY = nm->mkNode(Kind::ADD, node[1], node[2]);
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

  Node addXY = nm->mkNode(Kind::ADD, nm->mkConstReal(x), nm->mkConstReal(y));
  addXY = rewrite(addXY);
  Trace("rfp-add-debug") << "addXY: " << addXY << ", " << RFP::isFinite(eb,sb, addXY.getConst<Rational>()) << std::endl;

  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  {
    // this is the most naive model-based schema based on model values
    Node lem = opValueBasedLemma(node);
    Trace("rfp-add-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
      nullptr, true);
  }
}

// RfpNeg

void RfpSolver::checkInitialRefineNeg(Node node) {
  Assert(node.getKind() == Kind::RFP_NEG);
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

    Node negX = nm->mkNode(Kind::NEG, node[0]);
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
    Node negX = node.eqNode(nm->mkNode(Kind::NEG, node[0]));
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
}

void RfpSolver::checkFullRefineNeg(Node node)
{
  Trace("rfp-neg") << "RFP_NEG term: " << node << std::endl;
  Assert(node.getKind() == Kind::RFP_NEG);
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

  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) ))
  {
    // this is the most naive model-based schema based on model values
    Node valC = nm->mkNode(Kind::RFP_NEG, node.getOperator(), valX);
    valC = rewrite(valC);
    Node assumption = node[0].eqNode(valX);
    Node lem = assumption.impNode(node.eqNode(valC));
    Trace("rfp-neg-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
}

// RfpSub

void RfpSolver::checkInitialRefineSub(Node node) {
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpSub>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    // sub_finite
    //Node aX = mkIsNormal(eb,sb, node[1])
    //  .orNode(mkIsSubnormal(eb,sb, node[1]));
    //Node aY = mkIsNormal(eb,sb, node[2])
    //  .orNode(mkIsSubnormal(eb,sb, node[2]));
    Node aX = mkIsFinite(eb,sb, node[1])
      .andNode(mkIsZero(eb,sb, node[1]).notNode());
    Node aY = mkIsFinite(eb,sb, node[2])
      .andNode(mkIsZero(eb,sb, node[2]).notNode());
    Node subXY = nm->mkNode(Kind::SUB, node[1], node[2]);
    Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], subXY));
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], subXY);
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
  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // sub_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    Node isFinite = mkIsFinite(eb,sb, node);
    //Node aX = node[1].eqNode(nm->mkConstReal(RFP::minusZero(eb,sb))).notNode();
    //Node aY = node[2].eqNode(nm->mkConstReal(RFP::minusZero(eb,sb))).notNode();
    Node aX = node.eqNode(node[1]).notNode();
    Node aY = node.eqNode(node[2]).notNode();
    Node assumption = isTN.andNode(isFinite).andNode(aX).andNode(aY);
    Node subXY = nm->mkNode(Kind::SUB, node[1], node[2]);
    Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], subXY));
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], subXY);
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
      mkIsFinite(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkDiffSign(eb,sb, node, node[2])))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[1])))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
          .andNode(mkSameSign(eb,sb, node[1], node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
          .andNode(mkDiffSign(eb,sb, node[1], node[2]))
        .impNode(mkIsInf(eb,sb, node).andNode(mkSameSign(eb,sb, node, node[1])))
      );
    Node subXY = nm->mkNode(Kind::SUB, node[1], node[2]);
    Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], subXY));
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(noOverflow.notNode())
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
  Rational sub = valTerm.getConst<Rational>();

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

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG &&
      (rm == IRM::NE || rm == IRM::NA) &&
      RFP::isFinite(eb,sb, sub) && sub != x && sub != y)
  {
    // sub_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    Node isFinite = mkIsFinite(eb,sb, node);
    Node aX = node.eqNode(node[1]).notNode();
    Node aY = node.eqNode(node[2]).notNode();
    Node assumption = isTN.andNode(isFinite).andNode(aX).andNode(aY);
    Node subXY = nm->mkNode(Kind::SUB, node[1], node[2]);
    Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], subXY));
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], subXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-sub-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; sub_finite_rev_n ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  {
    // this is the most naive model-based schema based on model values
    Node lem = opValueBasedLemma(node);
    Trace("rfp-sub-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
}

// RfpMult

void RfpSolver::checkInitialRefineMult(Node node) 
{
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpMult>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // mul_finite
    //Node aX = mkIsNormal(eb,sb, node[1])
    //  .orNode(mkIsSubnormal(eb,sb, node[1]));
    //Node aY = mkIsNormal(eb,sb, node[2])
    //  .orNode(mkIsSubnormal(eb,sb, node[2]));
    Node aX = mkIsFinite(eb,sb, node[1])
      .andNode(mkIsZero(eb,sb, node[1]).notNode());
    Node aY = mkIsFinite(eb,sb, node[2])
      .andNode(mkIsZero(eb,sb, node[2]).notNode());
    Node multXY = nm->mkNode(Kind::MULT, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], multXY);
    Node conclusion = node.eqNode(rounded);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem 
                            << " ; mul_finite ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }

  {
    // mul_finite_rev
    Node assumption = mkIsFinite(eb,sb, node);
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node conclusion = isFiniteX.andNode(isFiniteY);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
                            << " ; mul_finite_rev ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }

  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // mul_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    //Node isFinite = mkIsFinite(eb,sb, node);
    Node isFinite = mkIsFinite(eb,sb, node)
      .andNode(mkIsZero(eb,sb, node).notNode());
    Node assumption = isTN.andNode(isFinite);
    Node multXY = nm->mkNode(Kind::MULT, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], multXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
                            << " ; mul_finite_rev_n ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }

  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // mul_zero
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node isZeroX = mkIsZero(eb,sb, node[1]);
    Node isZeroY = mkIsZero(eb,sb, node[2]);
    Node assumption = isFiniteX.andNode(isFiniteY)
      .andNode( isZeroX.orNode(isZeroY) );
    Node conclusion = mkIsZero(eb,sb, node);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; INIT_REFINE"
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
      mkIsZero(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
          .andNode(mkIsZero(eb,sb, node[1]).notNode())
        .impNode(mkIsInf(eb,sb, node))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsZero(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(mkIsZero(eb,sb, node[2]).notNode())
        .impNode(mkIsInf(eb,sb, node))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node))
      );
    Node multXY = nm->mkNode(Kind::MULT, node[1], node[2]);
    Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], multXY));
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(noOverflow.notNode())
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

    Rational tC = valMultC.getConst<Rational>();
    Trace("rfp-mult") << "         (" << rm << ", "
                      << ARFP(eb,sb, x) << ", " << ARFP(eb,sb, y) 
                      << ") = " << ARFP(eb,sb, tC) << std::endl;
  }
  if (valMult == valMultC)
  {
    Trace("rfp-mult") << "...already correct" << std::endl;
    return;
  }
  
  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG)
  {
    if (x == Rational(1) && !RFP::isNan(eb,sb, y) &&
        mult != y)
    {
      // mul_one1
      Node isOneX = node[1].eqNode(nm->mkConstReal(1));
      Node isNotNanY = mkIsNan(eb,sb, node[2]).notNode();
      Node assumption = isOneX.andNode(isNotNanY);
      Node conclusion = node.eqNode(node[2]);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
                           nullptr, true);
    }
    else if (x == Rational(-1) && !RFP::isNan(eb,sb, y) &&
             mult != -y)
    {
      // mul_one2
      Node isOneX = node[1].eqNode(nm->mkConstReal(-1));
      Node isNotNanY = mkIsNan(eb,sb, node[2]).notNode();
      Node assumption = isOneX.andNode(isNotNanY);
      Node negOp = nm->mkConst(RfpNeg(eb,sb));
      Node neg = nm->mkNode(Kind::RFP_NEG, negOp, node[2]);
      Node conclusion = node.eqNode(neg);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
                           nullptr, true);
    }
    else if (!RFP::isNan(eb,sb, x) && y == Rational(1) &&
             mult != x)
    {
      // mul_one3
      Node isNotNanX = mkIsNan(eb,sb, node[1]).notNode();
      Node isOneY = node[2].eqNode(nm->mkConstReal(1));
      Node assumption = isNotNanX.andNode(isOneY);
      Node conclusion = node.eqNode(node[1]);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
                           nullptr, true);
    }
    else if (!RFP::isNan(eb,sb, x) && y == Rational(-1) &&
             mult != -x)
    {
      // mul_one4
      Node isNotNanX = mkIsNan(eb,sb, node[1]).notNode();
      Node isOneY = node[2].eqNode(nm->mkConstReal(-1));
      Node assumption = isNotNanX.andNode(isOneY);
      Node negOp = nm->mkConst(RfpNeg(eb,sb));
      Node neg = nm->mkNode(Kind::RFP_NEG, negOp, node[1]);
      Node conclusion = node.eqNode(neg);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
                           nullptr, true);
    }
    else if (//(RFP::isNormal(eb,sb, x) || RFP::isSubnormal(eb,sb, x)) &&
             //(RFP::isNormal(eb,sb, y) || RFP::isSubnormal(eb,sb, y)) &&
             (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x)) &&
             (RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y)) &&
             RFP::noOverflow(eb,sb, rm.getUnsignedInt(), x*y) 
             //&& mult != RFP::round(eb,sb, rm, x*y)
             )
    {
      // mul_finite
      //Node aX = mkIsNormal(eb,sb, node[1])
      //  .orNode(mkIsSubnormal(eb,sb, node[1]));
      //Node aY = mkIsNormal(eb,sb, node[2])
      //  .orNode(mkIsSubnormal(eb,sb, node[2]));
      Node aX = mkIsFinite(eb,sb, node[1])
        .andNode(mkIsZero(eb,sb, node[1]).notNode());
      Node aY = mkIsFinite(eb,sb, node[2])
        .andNode(mkIsZero(eb,sb, node[2]).notNode());
      Node multXY = nm->mkNode(Kind::MULT, node[1], node[2]);
      multXY = rewrite(multXY);
      Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
      noOverflow = rewrite(noOverflow);
      Node assumption = aX.andNode(aY).andNode(noOverflow);

      Node op = nm->mkConst(RfpRound(eb, sb));
      Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], multXY);
      rounded = rewrite(rounded);
      Node conclusion = node.eqNode(rounded);

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem 
                              << " ; mul_finite ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
      //d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
      //                     nullptr, true);
    }
  }
  
  //if (RFP::isFinite(eb,sb, mult) && 
  //    (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y)))
  //{
  //  // mul_finite_rev
  //  Node assumption = mkIsFinite(eb,sb, node);
  //  Node isFiniteX = mkIsFinite(eb,sb, node[1]);
  //  Node isFiniteY = mkIsFinite(eb,sb, node[2]);
  //  Node conclusion = isFiniteX.andNode(isFiniteY);
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
  //                          << " ; mul_finite_rev ; AUX_REFINE"
  //                          << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
  //                       nullptr, true);
  //}

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG &&
      RFP::isFinite(eb,sb, mult) && !RFP::isZero(eb,sb, mult) && 
      RFP::isFinite(eb,sb, x*y))
  {
    // mul_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    //Node isFinite = mkIsFinite(eb,sb, node);
    Node isFinite = mkIsFinite(eb,sb, node)
      .andNode(mkIsZero(eb,sb, node).notNode());
    Node assumption = isTN.andNode(isFinite);
    Node multXY = nm->mkNode(Kind::MULT, node[1], node[2]);
    multXY = rewrite(multXY);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
    noOverflow = rewrite(noOverflow);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], multXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem
                            << " ; mul_finite_rev_n ; AUX_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
                         nullptr, true);
  }

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG &&
      RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) &&
      (RFP::isZero(eb,sb, x) || RFP::isZero(eb,sb, y)) && 
      !RFP::isZero(eb,sb, mult)
      )
  {
    // mul_zero
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node isZeroX = mkIsZero(eb,sb, node[1]);
    Node isZeroY = mkIsZero(eb,sb, node[2]);
    Node assumption = isFiniteX.andNode(isFiniteY)
      .andNode( isZeroX.orNode(isZeroY) );
    Node conclusion = mkIsZero(eb,sb, node);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      options().smt.rfpValueRefine == options::rfpVRMode::MID ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  {
    // this is the most naive model-based schema based on model values
    Node lem = opValueBasedLemma(node);
    Trace("rfp-mult-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
}

// RfpDiv

void RfpSolver::checkInitialRefineDiv(Node node) {
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpDiv>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // div_finite
    //Node aX = mkIsNormal(eb,sb, node[1])
    //  .orNode(mkIsSubnormal(eb,sb, node[1]));
    //Node aY = mkIsNormal(eb,sb, node[2])
    //  .orNode(mkIsSubnormal(eb,sb, node[2]));
    Node aX = mkIsFinite(eb,sb, node[1])
      .andNode(mkIsZero(eb,sb, node[1]).notNode());
    Node aY = mkIsFinite(eb,sb, node[2])
      .andNode(mkIsZero(eb,sb, node[2]).notNode());
    Node divXY = nm->mkNode(Kind::DIVISION, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], divXY);
    noOverflow = rewrite(noOverflow);
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    Node op = nm->mkConst(RfpRound(eb,sb));
    Node round = nm->mkNode(Kind::RFP_ROUND, op, node[0], divXY);
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
    Node isInfY = mkIsInfWeak(eb,sb, node[2]);
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

  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // div_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    //Node isFinite = mkIsFinite(eb,sb, node);
    Node isFinite = mkIsFinite(eb,sb, node)
      .andNode(mkIsZero(eb,sb, node).notNode());
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node assumption = isTN.andNode(isFinite).andNode(isFiniteY);
    Node divXY = nm->mkNode(Kind::DIVISION, node[1], node[2]);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], divXY);
    noOverflow = rewrite(noOverflow);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], divXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; div_finite_rev_n ; INIT_REFINE"
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
      mkIsFinite(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
        .impNode(mkIsZero(eb,sb, node))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
        .impNode(mkIsInf(eb,sb, node))
      );
    conj.push_back(
      mkIsInfWeak(eb,sb, node[1]).andNode(mkIsInfWeak(eb,sb, node[2]))
        .impNode(mkIsNan(eb,sb, node))
      );
    Node divXY = nm->mkNode(Kind::DIVISION, node[1], node[2]);
    Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], divXY));
    conj.push_back(
      mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
          .andNode(mkIsZero(eb,sb, node[2]).notNode())
          .andNode(noOverflow.notNode())
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
  Rational div = valTerm.getConst<Rational>();

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

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG)
  {
    if (!RFP::isNan(eb,sb, x) && y == Rational(1) &&
        div != x)
    {
      // div_one1
      Node isNotNanX = mkIsNan(eb,sb, node[1]).notNode();
      Node isOneY = node[2].eqNode(nm->mkConstReal(1));
      Node assumption = isNotNanX.andNode(isOneY);
      Node conclusion = node.eqNode(node[1]);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
                           nullptr, true);
    }
    else if (!RFP::isNan(eb,sb, x) && y == Rational(-1) &&
             div != -x)
    {
      // div_one2
      Node isNotNanX = mkIsNan(eb,sb, node[1]).notNode();
      Node isOneY = node[2].eqNode(nm->mkConstReal(-1));
      Node assumption = isNotNanX.andNode(isOneY);
      Node negOp = nm->mkConst(RfpNeg(eb,sb));
      Node neg = nm->mkNode(Kind::RFP_NEG, negOp, node[1]);
      Node conclusion = node.eqNode(neg);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE,
                           nullptr, true);
    }
    else if (//(RFP::isNormal(eb,sb, x) || RFP::isSubnormal(eb,sb, x)) &&
             //(RFP::isNormal(eb,sb, y) || RFP::isSubnormal(eb,sb, y)) &&
             RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
             RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
             RFP::noOverflow(eb,sb, rm.getUnsignedInt(), x/y) )
    {
      // div_finite
      //Node aX = mkIsNormal(eb,sb, node[1])
      //  .orNode(mkIsSubnormal(eb,sb, node[1]));
      //Node aY = mkIsNormal(eb,sb, node[2])
      //  .orNode(mkIsSubnormal(eb,sb, node[2]));
      Node aX = mkIsFinite(eb,sb, node[1])
        .andNode(mkIsZero(eb,sb, node[1]).notNode());
      Node aY = mkIsFinite(eb,sb, node[2])
        .andNode(mkIsZero(eb,sb, node[2]).notNode());
      Node divXY = nm->mkNode(Kind::DIVISION, node[1], node[2]);
      divXY = rewrite(divXY);
      Node noOverflow = mkNoOverflow(eb,sb, node[0], divXY);
      noOverflow = rewrite(noOverflow);
      Node assumption = aX.andNode(aY).andNode(noOverflow);

      Node op = nm->mkConst(RfpRound(eb,sb));
      Node round = nm->mkNode(Kind::RFP_ROUND, op, node[0], divXY);
      Node conclusion = node.eqNode(round);

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; div_finite ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
  }

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG &&
      RFP::isFinite(eb,sb, div) && !RFP::isZero(eb,sb, div) &&
      RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
      RFP::isFinite(eb,sb, x/y))
  {
    // div_finite_rev_n
    Node isTN = mkIsToNearest(node[0]);
    //Node isFinite = mkIsFinite(eb,sb, node);
    Node isFinite = mkIsFinite(eb,sb, node)
      .andNode(mkIsZero(eb,sb, node).notNode());
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node assumption = isTN.andNode(isFinite).andNode(isFiniteY);
    Node divXY = nm->mkNode(Kind::DIVISION, node[1], node[2]);
    divXY = rewrite(divXY);
    Node noOverflow = mkNoOverflow(eb,sb, node[0], divXY);
    noOverflow = rewrite(noOverflow);
    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], divXY);
    Node conclusion = noOverflow.andNode(node.eqNode(rounded));
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-div-lemma") << "RfpSolver::Lemma: " << lem
                           << " ; div_finite_rev_n ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      options().smt.rfpValueRefine == options::rfpVRMode::MID ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  {
    // this is the most naive model-based schema based on model values
    Node lem = opValueBasedLemma(node);
    Trace("rfp-div-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
}

/* Handlers for relational operators. */

Node mkRelConstr(Node node)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lb = nm->mkNode(Kind::LEQ, nm->mkConstInt(Rational(0)), node);
  Node ub = nm->mkNode(Kind::LEQ, node, nm->mkConstInt(Rational(1)));
  return lb.andNode(ub);
}

// RfpGt

Node mkGtSpecial(uint32_t eb, uint32_t sb, TNode node)
{
  Node assumption = mkIsOne(node);
  Node isFiniteX = mkIsFinite(eb,sb, node[0]);
  Node isFiniteY = mkIsFinite(eb,sb, node[1]);
  Node c1 = isFiniteX.andNode(isFiniteY);
  Node isPinfX = mkIsPosInf(eb,sb, node[0]);
  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  Node isNotPinfY = mkIsPosInf(eb,sb, node[1]).notNode();
  Node c2 = isPinfX.andNode(isNotNanY).andNode(isNotPinfY);
  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  Node isNotNinfX = mkIsNegInf(eb,sb, node[0]).notNode();
  Node isNinfY = mkIsNegInf(eb,sb, node[1]);
  Node c3 = isNotNanX.andNode(isNotNinfX).andNode(isNinfY);
  Node conclusion = c1.orNode(c2).orNode(c3);
  return assumption.impNode(conclusion);
}

void RfpSolver::checkInitialRefineGt(Node node) 
{
  Trace("rfp-gt") << "RFP_GT term (init): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpGt>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // gt_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isFiniteX.andNode(isFiniteY)
      .andNode( isNotZeroX.orNode(isNotZeroY) );

    //Node gtTrue = mkTrue(node);
    //Node gtXY = nm->mkNode(Kind::GT, node[0], node[1]);
    //Node conclusion = gtTrue.eqNode(gtXY);
    Node gtTrue = mkIsOne(node);
    Node gtFalse = mkFalse(node);
    Node gtXY = nm->mkNode(Kind::GT, node[0], node[1]);
    Node conclusion = gtXY.iteNode(gtTrue, gtFalse);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; gt_finite ; INIT_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  //{
  //  Node isPinfX = mkIsPosInf(eb,sb, node[0]);
  //  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  //  Node isNotPinfY = mkIsPosInf(eb,sb, node[1]).notNode();
  //  Node assumption = isPinfX
  //    .andNode(isNotNanY).andNode(isNotPinfY);

  //  Node conclusion = mkIsOne(node);

  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
  //                        << " ; gt_pinf ; INIT_REFINE"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  //}
  //{
  //  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  //  Node isNotNinfX = mkIsNegInf(eb,sb, node[0]).notNode();
  //  Node isNinfY = mkIsNegInf(eb,sb, node[1]);
  //  Node assumption = isNotNanX.andNode(isNotNinfX)
  //    .andNode(isNinfY);

  //  Node conclusion = mkIsOne(node);

  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
  //                        << " ; gt_ninf ; INIT_REFINE"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  //}
  //{
  //  // lt_finite_zero
  //  Node isFiniteX = mkIsFinite(eb,sb, node[0]);
  //  //Node isFiniteX = mkIsNan(eb,sb, node[0]).notNode();
  //  Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
  //  Node isZeroY = mkIsZero(eb,sb, node[1]);
  //  Node assumption = isFiniteX.andNode(isNotZeroX)
  //    .andNode(isZeroY);

  //  //Node gtTrue = mkTrue(node);
  //  //Node gtXY = nm->mkNode(Kind::GT, node[0], nm->mkConstReal(0));
  //  //Node conclusion = gtTrue.eqNode(gtXY);
  //  Node gtTrue = mkIsOne(node);
  //  Node gtFalse = mkFalse(node);
  //  Node gtXY = nm->mkNode(Kind::GT, node[0], nm->mkConstReal(0));
  //  Node conclusion = gtXY.iteNode(gtTrue, gtFalse);

  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
  //                        << " ; gt_non_zero_zero ; INIT"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  //}
  //{
    //  // gt_finite_zero
  //  Node isFiniteX = mkIsFinite(eb,sb, node[0]);
  //  //Node isFiniteX = mkIsNan(eb,sb, node[0]).notNode();
  //  Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
  //  Node isZeroY = mkIsZero(eb,sb, node[1]);
  //  Node assumption = isFiniteX.andNode(isNotZeroX)
  //    .andNode(isZeroY);

  //  Node gtTrue = mkTrue(node);
  //  Node gtXY = nm->mkNode(Kind::GT, node[0], nm->mkConstReal(0));
  //  Node conclusion = gtTrue.eqNode(gtXY);

  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
  //                        << " ; gt_non_zero_zero ; COMP"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  //}
  {
    // gt_special
    Node lem = mkGtSpecial(eb,sb, node);
    Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; gt_special ; INIT_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    Node lem = mkBoolIntConstraint(node);
  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
  << " ; gt_range ; INIT_REFINE"
  << std::endl;
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

void RfpSolver::checkFullRefineGt(Node node) 
{
  Trace("rfp-gt") << "RFP_GT term (full): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpGt>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valX = d_model.computeConcreteModelValue(node[0]);
  Node valY = d_model.computeConcreteModelValue(node[1]);

  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Integer t = valTerm.getConst<Rational>().getNumerator();

  if (TraceIsOn("rfp-gt"))
  {
    Trace("rfp-gt") << "* " << node << ", value = " << valTerm
                    << std::endl;
    Trace("rfp-gt") << "  actual (" << x << ", " << y << ") = " 
                    << valTermC << std::endl;

    Trace("rfp-gt") << "         ("
                     << ARFP(eb,sb, x) << ", " << ARFP(eb,sb, y)
                     << ") = " << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-gt") << "...already correct" << std::endl;
    return;
  }

  //if (t < Integer(0) || Integer(1) < t)
  //{
  //  Node a1 = node.eqNode(nm->mkConstInt(1)).notNode();
  //  Node assumption = mkTrue(node).andNode(a1);
  //  Node lem = assumption.impNode(node.eqNode(nm->mkConstInt(1)));
  //  //Node lem = mkRelConstr(node);
  //  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE0"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  //// TODO
  //{
  //  Node gtTrue = mkIsOne(node);
  //  Node gtFalse = mkFalse(node);
  //  Node gtXY = nm->mkNode(Kind::GT, node[0], node[1]);
  //  gtXY = rewrite(gtXY);
  //  Node lem = gtXY.iteNode(gtTrue, gtFalse);
  //  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
  //                        << " ; gt_finite ; COMP"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  //}

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG &&
      RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) &&
      //!RFP::isNan(eb,sb, x) && !RFP::isNan(eb,sb, y) &&
      (!RFP::isZero(eb,sb, x) || !RFP::isZero(eb,sb, y)) &&
      (t != 0) != (x > y))
  {
    // gt_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    //Node isFiniteX = mkIsNan(eb,sb, node[0]).notNode();
    //Node isFiniteY = mkIsNan(eb,sb, node[1]).notNode();
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isFiniteX.andNode(isNotZeroX)
      .andNode(isFiniteY).andNode(isNotZeroY);

    //Node gtTrue = mkTrue(node);
    //Node gtXY = nm->mkNode(Kind::GT, node[0], node[1]);
    ////gtXY = rewrite(gtXY);
    //Node conclusion = gtTrue.eqNode(gtXY);
    Node gtTrue = mkIsOne(node);
    Node gtFalse = mkFalse(node);
    Node gtXY = nm->mkNode(Kind::GT, node[0], node[1]);
    gtXY = rewrite(gtXY);
    Node conclusion = gtXY.iteNode(gtTrue, gtFalse);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; gt_finite ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if (x == RFP::plusInfinity(eb,sb) &&
      !RFP::isNan(eb,sb, y) && y != RFP::plusInfinity(eb,sb) &&
      t == 0)
  {
    // gt_pinf
    Node isPinfX = mkIsPosInf(eb,sb, node[0]);
    Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
    Node isNotPinfY = mkIsPosInf(eb,sb, node[1]).notNode();
    Node assumption = isPinfX
      .andNode(isNotNanY).andNode(isNotPinfY);
    Node lem = assumption.impNode(mkIsOne(node));
    Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; gt_pinf ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if (!RFP::isNan(eb,sb, x) && x != RFP::minusInfinity(eb,sb) &&
      y == RFP::minusInfinity(eb,sb) &&
      t == 0)
  {
    // gt_finite_pinf
    Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
    Node isNotNinfX = mkIsNegInf(eb,sb, node[0]).notNode();
    Node isNinfY = mkIsNegInf(eb,sb, node[1]);
    Node assumption = isNotNanX.andNode(isNotNinfX)
      .andNode(isNinfY);
    Node lem = assumption.impNode(mkIsOne(node));
    Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; gt_pinf ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if (RFP::isZero(eb,sb, x) &&
      //RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
      !RFP::isNan(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
      (t != 0) != (y < 0))
  {
    // lt_zero_non_zero
    Node isZeroX = mkIsZero(eb,sb, node[0]);
    //Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsNan(eb,sb, node[1]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isZeroX
      .andNode(isFiniteY).andNode(isNotZeroY);

    //Node gtTrue = mkTrue(node);
    //Node gtXY = nm->mkNode(Kind::GT, nm->mkConstReal(0), node[1]);
    //gtXY = rewrite(gtXY);
    //Node conclusion = gtTrue.eqNode(gtXY);
    Node gtTrue = mkIsOne(node);
    Node gtFalse = mkFalse(node);
    Node gtXY = nm->mkNode(Kind::GT, nm->mkConstReal(0), node[1]);
    gtXY = rewrite(gtXY);
    Node conclusion = gtXY.iteNode(gtTrue, gtFalse);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; gt_zero_non_zero ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if (//RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
      !RFP::isNan(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
      RFP::isZero(eb,sb, y) &&
      (t != 0) != (x > 0))
  {
    // gt_non_zero_zero
    //Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isFiniteX = mkIsNan(eb,sb, node[0]).notNode();
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isZeroY = mkIsZero(eb,sb, node[1]);
    Node assumption = isFiniteX.andNode(isNotZeroX)
      .andNode(isZeroY);

    //Node gtTrue = mkTrue(node);
    //Node gtXY = nm->mkNode(Kind::GT, node[0], nm->mkConstReal(0));
    ////gtXY = rewrite(gtXY);
    //Node conclusion = gtTrue.eqNode(gtXY);
    Node gtTrue = mkIsOne(node);
    Node gtFalse = mkFalse(node);
    Node gtXY = nm->mkNode(Kind::GT, node[0], nm->mkConstReal(0));
    gtXY = rewrite(gtXY);
    Node conclusion = gtXY.iteNode(gtTrue, gtFalse);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; gt_non_zero_zero ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if ((x == RFP::notANumber(eb,sb) || y == RFP::notANumber(eb,sb)) &&
      t != 0)
  {
    Node isNanX = mkIsNan(eb,sb, node[0]);
    Node isNanY = mkIsNan(eb,sb, node[1]);
    Node assumption = isNanX.orNode(isNanY);
    Node lem = assumption.impNode(mkFalse(node));
    Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
                          << " ; gt_nan ; AUX_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  //if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  //{
  //  // gt_special
  //  Node lem = mkGtSpecial(eb,sb, node);
  //  Trace("rfp-gt-lemma") << "RfpSolver::Lemma: " << lem 
  //                        << " ; gt_special ; AUX_REFINE"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}
  //else
  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  {
    // this is the most naive model-based schema based on model values
    Node lem = relValueBasedLemma(node);
    Trace("rfp-gt-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem,
                         InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr,
                         true);
  }
}

// RfpGeq

Node mkGeqSpecial(uint32_t eb, uint32_t sb, TNode node)
{
  Node assumption = mkTrue(node);
  Node isFiniteX = mkIsFinite(eb,sb, node[0]);
  Node isFiniteY = mkIsFinite(eb,sb, node[1]);
  Node c1 = isFiniteX.andNode(isFiniteY);
  Node isPinfX = mkIsPosInf(eb,sb, node[0]);
  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  Node c2 = isPinfX.andNode(isNotNanY);
  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  Node isNinfY = mkIsNegInf(eb,sb, node[1]);
  Node c3 = isNotNanX.andNode(isNinfY);
  Node conclusion = c1.orNode(c2).orNode(c3);
  return assumption.impNode(conclusion);
}

void RfpSolver::checkInitialRefineGeq(Node node) 
{
  Trace("rfp-geq") << "RFP_GEQ term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpGeq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    // ge_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isFiniteX.andNode(isNotZeroX)
      .andNode(isFiniteY).andNode(isNotZeroY);

    Node geqTrue = mkIsOne(node);
    Node geqFalse = mkFalse(node);
    Node geqXY = nm->mkNode(Kind::GEQ, node[0], node[1]);
    Node conclusion = geqXY.iteNode(geqTrue, geqFalse);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; ge_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    // ge_special
    Node lem = mkGeqSpecial(eb,sb, node);
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; ge_special ; AUX_INIT"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
  {
    Node lem = mkBoolIntConstraint(node);
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; geq_range ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
  }
}

void RfpSolver::checkFullRefineGeq(Node node) 
{
  Trace("rfp-geq") << "RFP_GEQ term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpGeq>().getSize();
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

  if (TraceIsOn("rfp-geq"))
  {
    Trace("rfp-geq") << "* " << node 
                     //<< ", value = " << valTerm
                     << std::endl;
    Trace("rfp-geq") << "  value  (" << valXA << ", " << valYA << ") = " 
                     << valTerm
                     << std::endl;
    Trace("rfp-geq") << "  actual (" << x << ", " << y << ") = " 
                     << valTermC << std::endl;

    Trace("rfp-geq") << "         ("
                     << ARFP(eb,sb, x) << ", " << ARFP(eb,sb, y)
                     << ") = " << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-geq") << "...already correct" << std::endl;
    return;
  }

  //if (t < Integer(0) || Integer(1) < t)
  //{
  //  Node lem = mkTrue(node).impNode(node.eqNode(nm->mkConstInt(1)));
  //  Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem << " ; AUX_REFINE0"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG &&
      RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) && 
      //!RFP::isNan(eb,sb, x) && !RFP::isNan(eb,sb, y) && 
      !RFP::isZero(eb,sb, x) && !RFP::isZero(eb,sb, y) &&
      (t != 0) != (x >= y))
  {
    // ge_finite
    Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    //Node isFiniteX = mkIsNan(eb,sb, node[0]).notNode();
    //Node isFiniteY = mkIsNan(eb,sb, node[1]).notNode();
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isFiniteX.andNode(isNotZeroX)
      .andNode(isFiniteY).andNode(isNotZeroY);

    Node geqTrue = mkIsOne(node);
    Node geqFalse = mkFalse(node);
    Node geqXY = nm->mkNode(Kind::GEQ, node[0], node[1]);
    geqXY = rewrite(geqXY);
    Node conclusion = geqXY.iteNode(geqTrue, geqFalse);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; ge_finite ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if (x == RFP::plusInfinity(eb,sb) && !RFP::isNan(eb,sb, y) &&
      t == 0)
  {
    // ge_pinf
    Node isPinfX = mkIsNegInf(eb,sb, node[0]);
    Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
    Node assumption = isPinfX.andNode(isNotNanY);
    Node lem = assumption.impNode(mkIsOne(node));
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; ge_pinf ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if (!RFP::isNan(eb,sb, x) && y == RFP::minusInfinity(eb,sb) &&
      t == 0)
  {
    // ge_ninf
    Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
    Node isNinfY = mkIsNegInf(eb,sb, node[1]);
    Node assumption = isNotNanX.andNode(isNinfY);
    Node lem = assumption.impNode(mkIsOne(node));
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; ge_ninf ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if (RFP::isZero(eb,sb, x) && 
      //RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
      !RFP::isNan(eb,sb, y) && !RFP::isZero(eb,sb, y) &&
      (t != 0) != (y <= 0))
  {
    // ge_zero_non_zero
    Node isZeroX = mkIsZero(eb,sb, node[0]);
    //Node isFiniteY = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsNan(eb,sb, node[1]).notNode();
    Node isNotZeroY = mkIsZero(eb,sb, node[1]).notNode();
    Node assumption = isZeroX
      .andNode(isFiniteY).andNode(isNotZeroY);

    Node geqTrue = mkIsOne(node);
    Node geqFalse = mkFalse(node);
    Node geqXY = nm->mkNode(Kind::GEQ, nm->mkConstReal(0), node[1]);
    geqXY = rewrite(geqXY);
    Node conclusion = geqXY.iteNode(geqTrue, geqFalse);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; ge_zero_non_zero ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if (//RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) && 
      !RFP::isNan(eb,sb, x) && !RFP::isZero(eb,sb, x) && 
      RFP::isZero(eb,sb, y) &&
      (t != 0) != (x >= 0))
  {
    // ge_non_zero_zero
    //Node isFiniteX = mkIsFinite(eb,sb, node[0]);
    Node isFiniteX = mkIsNan(eb,sb, node[0]).notNode();
    Node isNotZeroX = mkIsZero(eb,sb, node[0]).notNode();
    Node isZeroY = mkIsZero(eb,sb, node[1]);
    Node assumption = isFiniteX.andNode(isNotZeroX)
      .andNode(isZeroY);

    Node geqTrue = mkIsOne(node);
    Node geqFalse = mkFalse(node);
    Node geqXY = nm->mkNode(Kind::GEQ, node[0], nm->mkConstReal(0));
    geqXY = rewrite(geqXY);
    Node conclusion = geqXY.iteNode(geqTrue, geqFalse);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; ge_non_zero_zero ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP);
  }

  if ((x == RFP::notANumber(eb,sb) || y == RFP::notANumber(eb,sb)) &&
      t != 0)
  {
    Node isNanX = mkIsNan(eb,sb, node[0]);
    Node isNanY = mkIsNan(eb,sb, node[1]);
    Node assumption = isNanX.orNode(isNanY);
    Node lem = assumption.impNode(mkFalse(node));
    Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
                           << " ; ge_nan ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  }

  //if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  //{
  //  // geq_special
  //  Node lem = mkGeqSpecial(eb,sb, node);
  //  Trace("rfp-geq-lemma") << "RfpSolver::Lemma: " << lem 
  //                         << " ; geq_special ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
  //}
  //else
  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  {
    // this is the most naive model-based schema based on model values
    Node lem = relValueBasedLemma(node);
    Trace("rfp-geq-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
