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
{}

RfpSolver::~RfpSolver() {}

bool RfpSolver::isTarget(const Node& n)
{
  Kind k = n.getKind();
  return k == Kind::RFP_ADD || k == Kind::RFP_NEG || k == Kind::RFP_SUB;
}

void RfpSolver::initLastCall(const std::vector<Node>& assertions,
                             const std::vector<Node>& false_asserts,
                             const std::vector<Node>& xts)
{
  d_terms.clear();
  Trace("rfp-solver") << "initLastCall" << std::endl;
  for (const Node& n : xts)
  {
    if (!isTarget(n)) continue;

    u_int32_t hash;
    switch (n.getKind())
    {
      case Kind::RFP_ADD: hash = n.getOperator().getConst<RfpAdd>(); break;
      case Kind::RFP_NEG: hash = n.getOperator().getConst<RfpNeg>(); break;
      case Kind::RFP_SUB: hash = n.getOperator().getConst<RfpSub>(); break;
      case Kind::RFP_MULT: hash = n.getOperator().getConst<RfpMult>(); break;
      case Kind::RFP_DIV: hash = n.getOperator().getConst<RfpDiv>(); break;
      case Kind::RFP_LT:  hash = n.getOperator().getConst<RfpLt>(); break;
      case Kind::RFP_LEQ: hash = n.getOperator().getConst<RfpLeq>(); break;
      case Kind::RFP_GT:  hash = n.getOperator().getConst<RfpGt>(); break;
      case Kind::RFP_GEQ: hash = n.getOperator().getConst<RfpGeq>(); break;
      case Kind::RFP_ROUND: 
        hash = n.getOperator().getConst<RfpRound>(); break;
      case Kind::RFP_TO_RFP_FROM_RFP: 
        hash = n.getOperator().getConst<RfpToRfpFromRfp>(); break;
      case Kind::RFP_TO_REAL: 
        hash = n.getOperator().getConst<RfpToReal>(); break;
      default: continue;
    }
    d_terms[n.getKind()][hash].push_back(n);
    Trace("rfp-solver-mv") << "- " << n 
                           << " (" << n.getKind() << ")" << std::endl;
  }
}

void RfpSolver::processTerms(InferKind iKind)
{
  for (const std::pair<const Kind, std::map<unsigned, std::vector<Node> > >& term : d_terms)
  {
    for (const std::pair<const unsigned, std::vector<Node> >& hNodes : term.second)
    {
      for (const Node& node : hNodes.second)
      {
        switch (iKind)
        {
          case INITIAL: 
            if (d_initRefine.find(node) != d_initRefine.end())
            {
              // already sent initial axioms for i in this user context
              continue;
            }
            d_initRefine.insert(node);
            checkInitialRefineBody(node); 
            break;
          case AUX: checkAuxRefineBody(node); break;
          case FULL: checkFullRefineBody(node); break;
        }
      }
    }
  }
}

void RfpSolver::checkInitialRefine()
{
  Trace("rfp-solver") << "RfpSolver::checkInitialRefine" << std::endl;
  //for (const std::pair<const Kind, std::map<unsigned, std::vector<Node> > >& term : d_terms)
  //{
  //  for (const std::pair<const unsigned, std::vector<Node> >& hNodes : term.second)
  //  {
  //    for (const Node& node : hNodes.second)
  //    {
  //      if (d_initRefine.find(node) != d_initRefine.end())
  //      {
  //        // already sent initial axioms for i in this user context
  //        continue;
  //      }
  //      d_initRefine.insert(node);
  //      switch(term.first)
  //      {
  //        case Kind::RFP_TO_REAL: checkInitialRefineToReal(node); break;
  //        case Kind::RFP_ADD: checkInitialRefineAdd(node); break;
  //        case Kind::RFP_NEG: checkInitialRefineNeg(node); break;
  //        case Kind::RFP_SUB: checkInitialRefineSub(node); break;
  //        case Kind::RFP_MULT: checkInitialRefineMult(node); break;
  //        case Kind::RFP_DIV: checkInitialRefineDiv(node); break;
  //        case Kind::RFP_GT:  checkInitialRefineGt(node); break;
  //        case Kind::RFP_GEQ: checkInitialRefineGeq(node); break;
  //      }
  //    }
  //  }
  //}
  processTerms(InferKind::INITIAL);
}

void RfpSolver::checkInitialRefineBody(Node node)
{
  switch(node.getKind())
  {
    case Kind::RFP_ADD: checkInitialRefineAdd(node); break;
    case Kind::RFP_NEG: checkInitialRefineNeg(node); break;
    case Kind::RFP_SUB: checkInitialRefineSub(node); break;
    case Kind::RFP_MULT: checkInitialRefineMult(node); break;
    case Kind::RFP_DIV: checkInitialRefineDiv(node); break;
    case Kind::RFP_GT:  checkInitialRefineGt(node); break;
    case Kind::RFP_GEQ: checkInitialRefineGeq(node); break;
    case Kind::RFP_ROUND: checkInitialRefineRound(node); break;
    case Kind::RFP_TO_RFP_FROM_RFP: checkInitialRefineToRfp(node); break;
    case Kind::RFP_TO_REAL: checkInitialRefineToReal(node); break;
    default: Unreachable();
  }
}

void RfpSolver::checkAuxRefine()
{
  Trace("rfp-solver") << "RfpSolver::checkAuxRefine" << std::endl;
  processTerms(InferKind::AUX);
}

void RfpSolver::checkAuxRefineBody(Node node)
{
  switch(node.getKind())
  {
    case Kind::RFP_ADD: checkAuxRefineAdd(node); break;
    case Kind::RFP_NEG: checkAuxRefineNeg(node); break;
    case Kind::RFP_SUB: checkAuxRefineSub(node); break;
    case Kind::RFP_MULT: checkAuxRefineMult(node); break;
    case Kind::RFP_DIV: checkAuxRefineDiv(node); break;
    case Kind::RFP_GT:  checkAuxRefineGt(node); break;
    case Kind::RFP_GEQ: checkAuxRefineGeq(node); break;
    case Kind::RFP_ROUND: checkAuxRefineRound(node); break;
    case Kind::RFP_TO_RFP_FROM_RFP: checkAuxRefineToRfp(node); break;
    case Kind::RFP_TO_REAL: checkAuxRefineToReal(node); break;
    default: Unreachable();
  }
}

void RfpSolver::checkFullRefine()
{
  Trace("rfp-solver") << "RfpSolver::checkFullRefine" << std::endl;
  processTerms(InferKind::FULL);
}

void RfpSolver::checkFullRefineBody(Node node)
{
  switch(node.getKind())
  {
    case Kind::RFP_NEG: 
      checkFullRefineUnOp(getSize<RfpNeg>(node), node); break;
    case Kind::RFP_TO_REAL: 
      checkFullRefineUnOp(getSize<RfpToReal>(node), node); break;
    case Kind::RFP_ADD: 
      checkFullRefineBinOp(getSize<RfpAdd>(node), node); break;
    case Kind::RFP_SUB: 
      checkFullRefineBinOp(getSize<RfpSub>(node), node); break;
    case Kind::RFP_MULT:
      checkFullRefineBinOp(getSize<RfpMult>(node), node); break;
    case Kind::RFP_DIV: 
      checkFullRefineBinOp(getSize<RfpDiv>(node), node); break;
    case Kind::RFP_GT:
      checkFullRefineRelOp(getSize<RfpGt>(node), node); break;
    case Kind::RFP_GEQ: 
      checkFullRefineRelOp(getSize<RfpGeq>(node), node); break;
    case Kind::RFP_ROUND: 
      checkFullRefineRound(getSize<RfpRound>(node), node); break;
    case Kind::RFP_TO_RFP_FROM_RFP: 
      checkFullRefineRound(getSize<RfpToRfpFromRfp>(node), node); break;
    default: Unreachable();
  }
}

//

// RfpAdd

void RfpSolver::checkInitialRefineAdd(Node node) {
  Assert(node.getKind() == Kind::RFP_ADD);
  Assert(node.getNumChildren() == 3);
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpAdd>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
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
  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID)
  {
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

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK)
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
    if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
        || options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
    {
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
    }
    if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
        || options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
    {
      // add_overflow
      Node addXY = nm->mkNode(Kind::ADD, node[1], node[2]);
      Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], addXY));
      conj.push_back(
        mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
            .andNode(noOverflow.notNode())
          .impNode(mkSameSign(eb,sb, node, addXY)
            .andNode(mkIsOverflowValue(eb,sb, node[0], node)))
        );
    }
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

void RfpSolver::checkAuxRefineAdd(Node node)
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

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
  {
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) &&
        !RFP::isZero(eb,sb, x) && !RFP::isZero(eb,sb, y) &&
        RFP::noOverflow(eb,sb, rm.getUnsignedInt(), x+y) )
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
      addXY = rewrite(addXY);
      Node noOverflow = mkNoOverflow(eb,sb, node[0], addXY);
      noOverflow = rewrite(noOverflow);
      Node assumption = aX.andNode(aY).andNode(noOverflow);

      //Node isFinite = mkIsFinite(eb,sb, node);
      Node op = nm->mkConst(RfpRound(eb, sb));
      Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], addXY);
      Node conclusion = node.eqNode(rounded);

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_finite ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
  }
  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
  {
    // add_overflow
    if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y) &&
        !RFP::isZero(eb,sb, x) && !RFP::isZero(eb,sb, y) &&
        !RFP::noOverflow(eb,sb, rm.getUnsignedInt(), x+y) )
    {
      Node aX = mkIsFinite(eb,sb, node[1])
        .andNode(mkIsZero(eb,sb, node[1]).notNode());
      Node aY = mkIsFinite(eb,sb, node[2])
        .andNode(mkIsZero(eb,sb, node[2]).notNode());
      Node addXY = nm->mkNode(Kind::ADD, node[1], node[2]);
      addXY = rewrite(addXY);
      Node noOverflow = mkNoOverflow(eb,sb, node[0], addXY);
      noOverflow = rewrite(noOverflow);
      Node assumption = aX.andNode(aY).andNode(noOverflow.notNode());

      Node sameSign = mkSameSign(eb,sb, node, addXY);
      Node overflowV = mkIsOverflowValue(eb,sb, node[0], node);
      Node conclusion = sameSign.andNode(overflowV);

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_finite ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
  }
  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG)
  {
    if (RFP::isZero(eb,sb, x) && 
        RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y))
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
    else if (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x) &&
             RFP::isZero(eb,sb, y))
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
  }

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

  if (( options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
        || options().smt.rfpLazyLearn == options::rfpLLMode::MID
        //|| options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
       ) &&
      (rm == IRM::NE || rm == IRM::NA) &&
      RFP::isFinite(eb,sb, add) && 
      //x != RFP::minusZero(eb,sb) && y != RFP::minusZero(eb,sb)
      add != x && add != y
      )
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

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
  {
    if (RFP::isNan(eb,sb, x) || RFP::isNan(eb,sb, y))
    {
      Node isNanX = mkIsNan(eb,sb, node[1]);
      Node isNanY = mkIsNan(eb,sb, node[2]);
      Node assumption = isNanX.orNode(isNanY);
      Node conclusion = mkIsNan(eb,sb, node);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_special 1 ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);

    }
    if (RFP::isFinite(eb,sb, x) && RFP::isInfiniteWeak(eb,sb, y))
    {
      Node isFinX = mkIsFinite(eb,sb, node[1]);
      Node isInfY = mkIsInfWeak(eb,sb, node[2]);
      Node assumption = isFinX.andNode(isInfY);
      Node isInf = mkIsInf(eb,sb, node);
      Node sameSignRY = mkSameSign(eb,sb, node, node[2]);
      Node conclusion = isInf.andNode(sameSignRY);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_special 2 ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);

    }
    if (RFP::isInfiniteWeak(eb,sb, x) && RFP::isFinite(eb,sb, y))
    {
      Node isInfX = mkIsInfWeak(eb,sb, node[1]);
      Node isFinY = mkIsFinite(eb,sb, node[2]);
      Node assumption = isInfX.andNode(isFinY);
      Node isInf = mkIsInf(eb,sb, node);
      Node sameSignRX = mkSameSign(eb,sb, node, node[1]);
      Node conclusion = isInf.andNode(sameSignRX);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_special 3 ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
    else if (RFP::isInfiniteWeak(eb,sb, x) && RFP::isInfiniteWeak(eb,sb, y) &&
             x < 0 == y < 0)
    {
      Node isInfX = mkIsInfWeak(eb,sb, node[1]);
      Node isInfY = mkIsInfWeak(eb,sb, node[2]);
      Node sameSignXY = mkSameSign(eb,sb, node[1], node[2]);
      Node assumption = isInfX.andNode(isInfY).andNode(sameSignXY);
      Node sameSignRX = mkSameSign(eb,sb, node, node[1]);
      Node isInf = mkIsInf(eb,sb, node);
      Node conclusion = isInf.andNode(sameSignRX);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_special 4 ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
    else if (RFP::isInfiniteWeak(eb,sb, x) && RFP::isInfiniteWeak(eb,sb, y) &&
             x < 0 != y < 0)
    {
      Node isInfX = mkIsInfWeak(eb,sb, node[1]);
      Node isInfY = mkIsInfWeak(eb,sb, node[2]);
      Node diffSignXY = mkDiffSign(eb,sb, node[1], node[2]);
      Node assumption = isInfX.andNode(isInfY).andNode(diffSignXY);
      Node conclusion = mkIsNan(eb,sb, node);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-add-lemma") << "RfpSolver::Lemma: " << lem 
                             << " ; add_special 5 ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_AUX_REFINE);
    }
  }

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

  //if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
  //    ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
  //      (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  //{
  //  // this is the most naive model-based schema based on model values
  //  Node lem = opValueBasedLemma(node);
  //  Trace("rfp-add-lemma")
  //      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  //  // send the value lemma
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
  //    nullptr, true);
  //}
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

void RfpSolver::checkAuxRefineNeg(Node node) {}

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
  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK)
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

void RfpSolver::checkAuxRefineSub(Node node)
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

  if (( options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
        || options().smt.rfpLazyLearn == options::rfpLLMode::MID
        //|| options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
       ) &&
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

  //if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
  //    ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
  //      (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  //{
  //  // this is the most naive model-based schema based on model values
  //  Node lem = opValueBasedLemma(node);
  //  Trace("rfp-sub-lemma")
  //      << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  //  // send the value lemma
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
  //                       nullptr, true);
  //}
}

//
void RfpSolver::checkInitialRefineMult(Node node) {}
void RfpSolver::checkAuxRefineMult(Node node) {}
void RfpSolver::checkInitialRefineDiv(Node node) {}
void RfpSolver::checkAuxRefineDiv(Node node) {}
void RfpSolver::checkInitialRefineGt(Node node) {}
void RfpSolver::checkAuxRefineGt(Node node) {}
void RfpSolver::checkInitialRefineGeq(Node node) {}
void RfpSolver::checkAuxRefineGeq(Node node) {}
void RfpSolver::checkInitialRefineRound(Node node) {}
void RfpSolver::checkAuxRefineRound(Node node) {}
void RfpSolver::checkInitialRefineToRfp(Node node) {}
void RfpSolver::checkAuxRefineToRfp(Node node) {}
void RfpSolver::checkInitialRefineToReal(Node node) {}
void RfpSolver::checkAuxRefineToReal(Node node) {}

//

void RfpSolver::checkFullRefineUnOp(const FloatingPointSize& sz, Node node)
{
  Assert(node.getKind() == Kind::RFP_NEG
      || node.getKind() == Kind::RFP_TO_REAL
      );
  Assert(node.getNumChildren() == 1);
  NodeManager* nm = NodeManager::currentNM();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valX = d_model.computeConcreteModelValue(node[0]);

  Rational x = valX.getConst<Rational>();
  Rational t = valTerm.getConst<Rational>();

  if (TraceIsOn("rfp-solver"))
  {
    Trace("rfp-solver") << "* " << node << ", value = " << valTerm
                        << std::endl;
    Trace("rfp-solver") << "  actual (" << x << ") = " << valTermC 
                        << std::endl;

    Rational tC = valTermC.getConst<Rational>();
    Trace("rfp-solver") << "         (" << ARFP(eb,sb, x)
                        << ") = " << ARFP(eb,sb, tC) << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-solver") << "...already correct" << std::endl;
    return;
  }

  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) ||
      optionalValueRefineCond(node))
  {
    // this is the most naive model-based schema based on model values
    Node valC = nm->mkNode(node.getKind(), node.getOperator(), valX);
    valC = rewrite(valC);
    Node assumption = node[0].eqNode(valX);
    Node lem = assumption.impNode(node.eqNode(valC));
    Trace("rfp-lemma") << "RfpSolver::Lemma: " << lem 
                       << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
}

void RfpSolver::checkFullRefineBinOp(const FloatingPointSize& sz, Node node)
{
  Assert(node.getKind() == Kind::RFP_ADD 
      || node.getKind() == Kind::RFP_SUB
      || node.getKind() == Kind::RFP_MULT
      || node.getKind() == Kind::RFP_DIV
      );
  NodeManager* nm = NodeManager::currentNM();
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

  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ) ||
      optionalValueRefineCond(node))
  {
    // this is the most naive model-based schema based on model values
    Node assumption = node[0].eqNode(valRm)
      .andNode(node[1].eqNode(valX))
      .andNode(node[2].eqNode(valY));
    std::vector<Node> cs;
    cs.push_back(node.getOperator());
    cs.push_back(valRm);
    cs.push_back(valX);
    cs.push_back(valY);
    Node valC = nm->mkNode(node.getKind(), cs);
    valC = rewrite(valC);
    Node lem = assumption.impNode(node.eqNode(valC));
    Trace("rfp-lemma")
        << "RfpSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_VALUE_REFINE,
                         nullptr, true);
  }
}

void RfpSolver::checkFullRefineRelOp(const FloatingPointSize& sz, Node node) {}
void RfpSolver::checkFullRefineRound(const FloatingPointSize& sz, Node node) {}

//Node RfpSolver::relValueBasedLemma(TNode n)
//{
//  Assert(n.getKind() == Kind::RFP_GT || n.getKind() == Kind::RFP_GEQ);
//  Node x = n[0];
//  Node y = n[1];
//
//  Node valX = d_model.computeConcreteModelValue(n[0]);
//  Node valY = d_model.computeConcreteModelValue(n[1]);
//
//  NodeManager* nm = NodeManager::currentNM();
//  std::vector<Node> cs;
//  cs.push_back(n.getOperator());
//  cs.push_back(valX);
//  cs.push_back(valY);
//  Node valC = nm->mkNode(n.getKind(), cs);
//  valC = rewrite(valC);
//
//  Node assumption = x.eqNode(valX).andNode(y.eqNode(valY));
//  return assumption.impNode(n.eqNode(valC));
//}

bool RfpSolver::optionalValueRefineCond(const Node& node)
{
  return false;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
