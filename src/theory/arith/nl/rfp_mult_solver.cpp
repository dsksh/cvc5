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
 * Implementation of the RFP solver for mult and div.
 */

#include "theory/arith/nl/rfp_mult_solver.h"

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

typedef cvc5::internal::IntRoundingMode IRM;
namespace RFP = cvc5::internal::RealFloatingPoint;
using namespace cvc5::internal::theory::arith::nl::RfpUtils;

namespace cvc5::internal {

using ARFP = class AbstractRFP;

namespace theory {
namespace arith {
namespace nl {

RfpMultSolver::RfpMultSolver(Env& env,
                             InferenceManager& im,
                             NlModel& model)
    : RfpSolver(env, im, model)
{}

RfpMultSolver::~RfpMultSolver() {}

bool RfpMultSolver::isTarget(const Node& n)
{
  Kind k = n.getKind();
  return k == Kind::RFP_MULT || k == Kind::RFP_DIV;
}

//void RfpMultSolver::checkValueRefine()
//{
//  Trace("rfp-mult-solver") << "RfpMultSolver::checkValueRefine" << std::endl;
//  for (const std::pair<const Kind, std::map<unsigned, std::vector<Node> > >& term : d_terms)
//  {
//    for (const std::pair<const unsigned, std::vector<Node> >& hNodes : term.second)
//    {
//      // the reference bitwidth
//      //unsigned k = ts.first;
//      for (const Node& node : hNodes.second)
//      {
//        Trace("rfp-mult-solver") << term.first << ", " << node << std::endl;
//        switch (term.first)
//        {
//          case Kind::RFP_MULT: checkValueRefineMult(node); break;
//          case Kind::RFP_DIV: 
//          //checkFullRefineDiv(node); 
//          break;
//          default:
//            Unreachable();
//        }
//      }
//    }
//  }
//}

// RfpMult

void RfpMultSolver::checkInitialRefineMult(Node node) 
{
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpMult>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID
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
    Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
    Node assumption = aX.andNode(aY).andNode(noOverflow);

    Node op = nm->mkConst(RfpRound(eb, sb));
    Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], multXY);
    Node conclusion = node.eqNode(rounded);

    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem 
                            << " ; mul_finite ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);
  }

  {
    // mul_finite_rev
    Node assumption = mkIsFinite(eb,sb, node);
    Node isFiniteX = mkIsFinite(eb,sb, node[1]);
    Node isFiniteY = mkIsFinite(eb,sb, node[2]);
    Node conclusion = isFiniteX.andNode(isFiniteY);
    Node lem = assumption.impNode(conclusion);
    Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem
                            << " ; mul_finite_rev ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);
  }

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
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
    Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem
                            << " ; mul_finite_rev_n ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);
  }

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID
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
    Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);

    Trace("rfp-mult-debug") << "mul_zero: " << node << std::endl;
  }

  {
    // mul_special
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
    }
    if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
        || options().smt.rfpLazyLearn == options::rfpLLMode::MID
        )
    {
      Node multXY = nm->mkNode(Kind::MULT, node[1], node[2]);
      Node noOverflow = rewrite(mkNoOverflow(eb,sb, node[0], multXY));
      conj.push_back(
        mkIsFinite(eb,sb, node[1]).andNode(mkIsFinite(eb,sb, node[2]))
            .andNode(noOverflow.notNode())
          .impNode(mkIsOverflowValue(eb,sb, node[0], node))
        );
    }
    conj.push_back(
      mkIsNan(eb,sb, node).notNode()
        .impNode(mkProductSign(eb,sb, node, node[1], node[2]))
      );
    Node lem = nm->mkAnd(conj);
    Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem
                            << " ; mul_special ; INIT_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);
  }
}

void RfpMultSolver::checkAuxRefineMult(Node node)
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

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      )
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
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
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
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
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
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
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
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                           nullptr, true);
    }
  }
  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      )
  {
    if (//(RFP::isNormal(eb,sb, x) || RFP::isSubnormal(eb,sb, x)) &&
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
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem 
                              << " ; mul_finite ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX);
      //d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
      //                     nullptr, true);
    }
  }
  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      )
  {
    if (//(RFP::isNormal(eb,sb, x) || RFP::isSubnormal(eb,sb, x)) &&
        //(RFP::isNormal(eb,sb, y) || RFP::isSubnormal(eb,sb, y)) &&
        (RFP::isFinite(eb,sb, x) && !RFP::isZero(eb,sb, x)) &&
        (RFP::isFinite(eb,sb, y) && !RFP::isZero(eb,sb, y)) &&
        !RFP::noOverflow(eb,sb, rm.getUnsignedInt(), x*y) )
    {
      Node aX = mkIsFinite(eb,sb, node[1])
        .andNode(mkIsZero(eb,sb, node[1]).notNode());
      Node aY = mkIsFinite(eb,sb, node[2])
        .andNode(mkIsZero(eb,sb, node[2]).notNode());
      Node multXY = nm->mkNode(Kind::MULT, node[1], node[2]);
      multXY = rewrite(multXY);
      Node noOverflow = mkNoOverflow(eb,sb, node[0], multXY);
      noOverflow = rewrite(noOverflow);
      Node assumption = aX.andNode(aY).andNode(noOverflow.notNode());

      Node conclusion = mkIsOverflowValue(eb,sb, node[0], node);

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem 
                              << " ; mul_finite ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX);
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
  //  Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem
  //                          << " ; mul_finite_rev ; AUX_REFINE"
  //                          << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
  //                       nullptr, true);
  //}

  if (( options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
        || options().smt.rfpLazyLearn == options::rfpLLMode::MID 
        //|| options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
       ) &&
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
    Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem
                            << " ; mul_finite_rev_n ; AUX_REFINE"
                            << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                         nullptr, true);
  }

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
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                           nullptr, true);
    }
    else if (RFP::isZero(eb,sb, x) && RFP::isInfiniteWeak(eb,sb, y))
    {
      Node isZeroX = mkIsZero(eb,sb, node[1]);
      Node isInfY = mkIsInfWeak(eb,sb, node[2]);
      Node assumption = isZeroX.andNode(isInfY);
      Node conclusion = mkIsInf(eb,sb, node);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                           nullptr, true);
    }
    else if (RFP::isFinite(eb,sb, x) && RFP::isInfiniteWeak(eb,sb, y))
    {
      Node isFinX = mkIsFinite(eb,sb, node[1]);
      Node isInfY = mkIsInfWeak(eb,sb, node[2]);
      Node assumption = isFinX.andNode(isInfY);
      Node conclusion = mkIsInf(eb,sb, node);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                           nullptr, true);
    }
    else if (RFP::isInfiniteWeak(eb,sb, x) && RFP::isZero(eb,sb, y))
    {
      Node isInfX = mkIsInfWeak(eb,sb, node[1]);
      Node isZeroY = mkIsFinite(eb,sb, node[2]);
      Node assumption = isInfX.andNode(isZeroY);
      Node conclusion = mkIsInf(eb,sb, node);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                           nullptr, true);
    }
    else if (RFP::isInfiniteWeak(eb,sb, x) && RFP::isFinite(eb,sb, y))
    {
      Node isInfX = mkIsInfWeak(eb,sb, node[1]);
      Node isFinY = mkIsFinite(eb,sb, node[2]);
      Node assumption = isInfX.andNode(isFinY);
      Node conclusion = mkIsInf(eb,sb, node);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                           nullptr, true);
    }
    else if (RFP::isInfiniteWeak(eb,sb, x) && RFP::isInfiniteWeak(eb,sb, y))
    {
      Node isInfX = mkIsInfWeak(eb,sb, node[1]);
      Node isInfY = mkIsInfWeak(eb,sb, node[2]);
      Node assumption = isInfX.andNode(isInfY);
      Node conclusion = mkIsInf(eb,sb, node);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                              << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                           nullptr, true);
    }
  }

  if (( options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
        //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID 
        ) &&
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
    Trace("rfp-mult-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX);
  }

  //if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
  //    options().smt.rfpValueRefine == options::rfpVRMode::MID ||
  //    ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
  //      (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  //    //!f ||
  //    //( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
  //    //  (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  //{
  //  // this is the most naive model-based schema based on model values
  //  Node lem = opValueBasedLemma(node);
  //  Trace("rfp-mult-lemma")
  //      << "RfpMultSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  //  // send the value lemma
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_V,
  //                       nullptr, true);
  //}
}

//void RfpMultSolver::checkValueRefineMult(Node node)
//{
//  Trace("rfp-mult") << "RFP_MULT term: " << node << std::endl;
//  //NodeManager* nm = NodeManager::currentNM();
//  FloatingPointSize sz = node.getOperator().getConst<RfpMult>().getSize();
//  uint32_t eb = sz.exponentWidth();
//  uint32_t sb = sz.significandWidth();
//
//  Node valMult = d_model.computeAbstractModelValue(node);
//  Node valMultC = d_model.computeConcreteModelValue(node);
//
//  Node valRm = d_model.computeConcreteModelValue(node[0]);
//  Node valX = d_model.computeConcreteModelValue(node[1]);
//  Node valY = d_model.computeConcreteModelValue(node[2]);
//
//  Integer rm = valRm.getConst<Rational>().getNumerator();
//  Rational x = valX.getConst<Rational>();
//  Rational y = valY.getConst<Rational>();
//  Rational mult = valMult.getConst<Rational>();
//
//  if (valMult == valMultC)
//  {
//    Trace("rfp-mult") << "...already correct" << std::endl;
//    return;
//  }
//
//  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
//      options().smt.rfpValueRefine == options::rfpVRMode::MID ||
//      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
//        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
//      //!f ||
//      //( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
//      //  (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
//  {
//    // this is the most naive model-based schema based on model values
//    Node lem = opValueBasedLemma(node);
//    Trace("rfp-mult-lemma")
//        << "RfpMultSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
//    // send the value lemma
//    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_V,
//                         nullptr, true);
//  }
//}

// RfpDiv

void RfpMultSolver::checkInitialRefineDiv(Node node) {
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpDiv>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
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
    Trace("rfp-div-lemma") << "RfpMultSolver::Lemma: " << lem 
                           << " ; div_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);
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
    Trace("rfp-div-lemma") << "RfpMultSolver::Lemma: " << lem 
                           << " ; div_finite_rev ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);
  }

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      )
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
    Trace("rfp-div-lemma") << "RfpMultSolver::Lemma: " << lem
                           << " ; div_finite_rev_n ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);
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
    Trace("rfp-div-lemma") << "RfpMultSolver::Lemma: " << lem 
                           << " ; div_special ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_I);
  }
}

void RfpMultSolver::checkAuxRefineDiv(Node node)
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

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
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
      Trace("rfp-div-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
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
      Trace("rfp-div-lemma") << "RfpMultSolver::Lemma: " << lem << " ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX,
                           nullptr, true);
    }
  }
  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
      //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
  {
    if (//(RFP::isNormal(eb,sb, x) || RFP::isSubnormal(eb,sb, x)) &&
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
      Trace("rfp-div-lemma") << "RfpMultSolver::Lemma: " << lem 
                             << " ; div_finite ; AUX_REFINE"
                             << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX);
    }
  }

  if (( options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
        || options().smt.rfpLazyLearn == options::rfpLLMode::MID
        //|| options().smt.rfpLazyLearn == options::rfpLLMode::WEAK 
       ) &&
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
    Trace("rfp-div-lemma") << "RfpMultSolver::Lemma: " << lem
                           << " ; div_finite_rev_n ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_AUX);
  }

  //if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
  //    options().smt.rfpValueRefine == options::rfpVRMode::MID ||
  //    ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
  //      (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  //{
  //  // this is the most naive model-based schema based on model values
  //  Node lem = opValueBasedLemma(node);
  //  Trace("rfp-div-lemma")
  //      << "RfpMultSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  //  // send the value lemma
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_MULT_V,
  //                       nullptr, true);
  //}
}

bool RfpMultSolver::optionalValueRefineCond(const Node& node)
{
  Node valX = d_model.computeConcreteModelValue(node[1]);
  Node valY = d_model.computeConcreteModelValue(node[2]);

  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();

  if (node.getKind() == Kind::RFP_MULT &&
      options().smt.rfpValueRefine == options::rfpVRMode::MID)
  {
    //FloatingPointSize sz = node.getOperator().getConst<RfpMult>().getSize();
    //uint32_t eb = sz.exponentWidth();
    //uint32_t sb = sz.significandWidth();
    //if (RFP::isFinite(eb,sb, x) && RFP::isFinite(eb,sb, y)){
    //  return true;
    //}else{
    //  return false;
    //}
    return true;
  }
  else if (node.getKind() == Kind::RFP_DIV &&
           options().smt.rfpValueRefine == options::rfpVRMode::MID)
  {
    return true;
  }
  else return false;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
