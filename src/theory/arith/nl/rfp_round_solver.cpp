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
  d_rounds.clear();
  d_toRfps.clear();

  Trace("rfp-round-mv") << "RFP_TO_FP terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak == RFP_ROUND)
    {
      u_int32_t hash = a.getOperator().getConst<RfpRound>();
      d_rounds[hash].push_back(a);
      Trace("rfp-round-mv") << "- " << a << std::endl;
    }
    else if(ak == RFP_TO_RFP_FROM_RFP)
    {
      u_int32_t hash = a.getOperator().getConst<RfpToRfpFromRfp>();
      d_toRfps[hash].push_back(a);
      Trace("rfp-round-mv") << "- " << a << std::endl;
    }
    else
    {
      // don't care about other terms
      continue;
    }
  }
}

void RfpRoundSolver::checkInitialRefine()
{
  Trace("rfp-round-check") << "RfpRoundSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_rounds)
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

      checkInitRefineRound(node);
    }
  }

  for (const std::pair<const unsigned, std::vector<Node> >& is : d_toRfps)
  {
    for (const Node& node : is.second)
    {
      if (d_initRefine.find(node) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(node);

      FloatingPointSize srcSz = node.getOperator().getConst<RfpToRfpFromRfp>().getSrcSize();
      FloatingPointSize sz = node.getOperator().getConst<RfpToRfpFromRfp>().getSize();
      uint32_t eb0 = srcSz.exponentWidth();
      uint32_t sb0 = srcSz.significandWidth();
      uint32_t eb = sz.exponentWidth();
      uint32_t sb = sz.significandWidth();

      {
        // finite case
        Node isFinite = mkIsFinite(eb0,sb0, node[1]);
        Node isNotZero = mkIsZero(eb0,sb0, node[1]).notNode();
        Node assumption = isFinite.andNode(isNotZero);
        Node op = nm->mkConst(RfpRound(eb,sb));
        Node rounded = nm->mkNode(kind::RFP_ROUND, op, node[0], node[1]);
        Node conclusion = node.eqNode(rounded);
        Node lem = assumption.impNode(conclusion);
        Trace("rfp-to-rfp-lemma") << "RfpRoundSolver::Lemma: " << lem
                                  << " ; to_rfp_finite ; INIT_REFINE"
                                  << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
      }
      {
        Node lem = mkRoundCases(eb0,sb0, node[1], eb,sb, node);
        Trace("rfp-to-rfp-lemma") << "RfpRoundSolver::Lemma: " << lem
                                  << " ; to_rfp_cases ; INIT_REFINE"
                                  << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
      }
      {
        // to_rfp_rounded
        Node lem = mkIsRounded(eb,sb, node);
        Trace("rfp-to-rfp-lemma") << "RfpSolver::Lemma: " << lem
                                  << " ; to_rfp_rounded ; INIT_REFINE"
                                  << std::endl;
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_INIT_REFINE);
      }
    }
  }
}

void RfpRoundSolver::checkFullRefine()
{
  Trace("rfp-round-check") << "RfpRoundSolver::checkFullRefine";
  Trace("rfp-round-check") << "RFP_ROUND terms: " << std::endl;
  //NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& ts : d_rounds)
  {
    // the reference bitwidth
    //unsigned k = ts.first;
    //for (const Node& t : ts.second)
    for (std::vector<Node>::const_iterator it = ts.second.begin(); 
         it != ts.second.end(); ++it)
    {
      const Node& node = *it;
      FloatingPointSize sz = node.getOperator().getConst<RfpRound>().getSize();
      uint32_t eb = sz.exponentWidth();
      uint32_t sb = sz.significandWidth();

      Node valRound = d_model.computeAbstractModelValue(node);
      Node valRoundC = d_model.computeConcreteModelValue(node);

      Node valRmA = d_model.computeAbstractModelValue(node[0]);
      Node valArgA = d_model.computeAbstractModelValue(node[1]);
      Node valRm = d_model.computeConcreteModelValue(node[0]);
      Node valArg = d_model.computeConcreteModelValue(node[1]);

      Integer rm = valRm.getConst<Rational>().getNumerator();
      Rational arg = valArg.getConst<Rational>();
      Rational round = valRound.getConst<Rational>();
      Rational roundC = valRoundC.getConst<Rational>();

      if (TraceIsOn("rfp-round-check"))
      {
        Trace("rfp-round-check") << "* " << node 
                                 //<< ", value = " << valRound 
                                 << std::endl;
        Trace("rfp-round-check") << "  value  (" << valRmA 
                                 << ", " << valArgA << ") = " << valRound
                                 << std::endl;
        Trace("rfp-round-check") << "  actual (" << rm << ", " << arg
                                 << ") = " << valRoundC << std::endl;

        Rational tC = valRoundC.getConst<Rational>();
        Trace("rfp-round-check") << "         (" << rm << ", "
                         << ARFP(eb,sb, arg)
                         << ") = " << ARFP(eb,sb, tC) << std::endl;
      }
      if (valRound == valRoundC)
      {
        Trace("rfp-round-check") << "...already correct" << std::endl;
        continue;
      }

      checkFullRefineRound(node, rm, arg, round, roundC);

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

        // TODO
        //checkFullRefineRoundPair(node, rm, arg, round, node1, rm1, arg1, round1);
      }
    }
  }

  for (const std::pair<const unsigned, std::vector<Node> >& ts : d_toRfps)
  {
    for (std::vector<Node>::const_iterator it = ts.second.begin(); 
         it != ts.second.end(); ++it)
    {
      const Node& node = *it;

      Node valConv = d_model.computeAbstractModelValue(node);
      Node valConvC = d_model.computeConcreteModelValue(node);

      Node valRm = d_model.computeConcreteModelValue(node[0]);
      Node valArg = d_model.computeConcreteModelValue(node[1]);

      Integer rm = valRm.getConst<Rational>().getNumerator();
      Rational arg = valArg.getConst<Rational>();
      Rational conv = valConv.getConst<Rational>();

      if (TraceIsOn("rfp-to-rfp-check"))
      {
        Trace("rfp-to-rfp-check") << "* " << node << ", value = " << valConv
                                  << std::endl;
        Trace("rfp-to-rfp-check") << "  actual (" << rm << ", " << arg
                                  << ") = " << valConvC << std::endl;
      }
      if (valConv == valConvC)
      {
        Trace("rfp-to-rfp-check") << "...already correct" << std::endl;
        continue;
      }

      // this is the most naive model-based schema based on model values
      Node lem = valueBasedLemma(node);
      Trace("rfp-to-rfp-lemma")
          << "RfpRoundSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
      // send the value lemma
      d_im.addPendingLemma(lem,
                           InferenceId::ARITH_NL_RFP_ROUND_VALUE_REFINE,
                           nullptr,
                           true);
    }
  }
}

void RfpRoundSolver::checkInitRefineRound(TNode node)
{
  //FloatingPointSize sz = node.getOperator().getConst<RfpRound>().getSize();
  //uint32_t eb = sz.exponentWidth();
  //uint32_t sb = sz.significandWidth();
  //NodeManager* nm = NodeManager::currentNM();
  //{
  //  Node diff = nm->mkNode(kind::SUB, node, node[1]);
  //  {
  //    // Bound for subnormal numbers.
  //    Node assumption = mkIsSubnormalWeak(eb,sb, node[1]);
  //    Rational minSN = RFP::minSubnormal(eb,sb);
  //    Node bound = nm->mkConstReal(minSN);
  //    Node lb = nm->mkNode(kind::LT, nm->mkNode(NEG, bound), diff);
  //    Node ub = nm->mkNode(kind::LT, diff, bound);
  //    Node l1 = assumption.impNode(lb.andNode(ub));

  //    Node boundN = nm->mkConstReal(minSN/2);
  //    Node lbN = nm->mkNode(kind::LEQ, nm->mkNode(NEG, boundN), diff);
  //    Node ubN = nm->mkNode(kind::LEQ, diff, boundN);
  //    Node l2 = assumption.impNode(lbN.andNode(ubN));

  //    Node lem = mkIsToNearest(node[0]).iteNode(l2, l1);
  //    Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
  //                             << " ; round_diff_sn ; INIT_REFINE"
  //                             << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
  //  }
  //  {
  //    // Relative bound for normal numbers.
  //    Node assumption = mkIsNormal(eb,sb, node[1]);
  //    Rational d = Rational(Integer::pow2(sb-1)).inverse();

  //    Node coeff = nm->mkConstReal(d);
  //    Node bound = nm->mkNode(kind::MULT, coeff, mkAbs(node[1]));
  //    Node lb = nm->mkNode(kind::LT, nm->mkNode(NEG, bound), diff);
  //    Node ub = nm->mkNode(kind::LT, diff, bound);
  //    Node l1 = assumption.impNode(lb.andNode(ub));

  //    Node coeffN = nm->mkConstReal(d/2);
  //    Node boundN = nm->mkNode(kind::MULT, coeffN, mkAbs(node[1]));
  //    Node lbN = nm->mkNode(kind::LEQ, nm->mkNode(NEG, boundN), diff);
  //    Node ubN = nm->mkNode(kind::LEQ, diff, boundN);
  //    Node l2 = assumption.impNode(lbN.andNode(ubN));

  //    Node lem = mkIsToNearest(node[0]).iteNode(l2, l1);
  //    Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
  //                             << " ; round_diff_n ; INIT_REFINE"
  //                             << std::endl;
  //    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
  //  }
  //}
  //{
  //  Node lem = mkRoundCases(eb,sb, node[1], eb,sb, node);
  //  Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
  //                           << " ; round_cases ; INIT_REFINE"
  //                           << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
  //}
}

void RfpRoundSolver::checkFullRefineRound(TNode node, 
  const Integer& rm, const Rational& arg, 
  const Rational& round, const Rational& roundC)
{
  FloatingPointSize sz = node.getOperator().getConst<RfpRound>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();

  if (!RFP::isNan(eb,sb, arg) 
    && RFP::isSubnormal(eb,sb, arg))
  {
    if ((rm == IRM::NA || rm == IRM::NE)
      && (arg - round).abs() > RFP::minNormal(eb,sb)/2)
    {
      // Bound for subnormal numbers (RN cases).
      Node a1 = mkIsToNearest(node[0]);
      Node a2 = mkIsSubnormalWeak(eb,sb, node[1]);
      Node assumption = a1.andNode(a2);

      Node sub = nm->mkNode(kind::SUB, node, node[1]);
      Node diff = nm->mkNode(kind::ABS, sub);
      Node bnd = nm->mkConstReal(RFP::minSubnormal(eb,sb)/2);
      Node conclusion = nm->mkNode(kind::LEQ, diff, bnd);

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                               << " ; round_diff_sn_rn ; BOUND_REFINE"
                               << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE);
    }
    else if (rm != IRM::NA && rm != IRM::NE
      && (arg - round).abs() > RFP::minNormal(eb,sb))
    {
      // Bound for subnormal numbers (other cases).
      Node assumption = mkIsSubnormalWeak(eb,sb, node[1]);

      Node sub = nm->mkNode(kind::SUB, node, node[1]);
      Node diff = nm->mkNode(kind::ABS, sub);
      Node bnd = nm->mkConstReal(RFP::minSubnormal(eb,sb));
      Node conclusion = nm->mkNode(kind::LEQ, diff, bnd);

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                               << " ; round_diff_sn ; BOUND_REFINE"
                               << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE);
    }
  }

  if (!RFP::isNan(eb,sb, arg) 
    && RFP::isNormal(eb,sb, arg))
  {
    size_t e = arg.ilog2Lower();
    Integer bnd = Integer::pow2(e-sb);
    if ((rm == IRM::NA || rm == IRM::NE)
      && (arg - round).abs() > bnd)
    {
      // Bound for normal numbers (RN cases).
      Node a1 = mkIsToNearest(node[0]);
      Node a2 = mkIsFinite(eb,sb, node[1]);
      Node assumption = a1.andNode(a2);

      Node sub = nm->mkNode(kind::SUB, node, node[1]);
      Node diff = nm->mkNode(kind::ABS, sub);
      Node conclusion = nm->mkNode(kind::LEQ, diff, nm->mkConstReal(bnd));

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                               << " ; round_diff_n_rn ; BOUND_REFINE"
                               << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE);
    }
    else if (rm != IRM::NA && rm != IRM::NE
      && (arg - round).abs() > bnd*2)
    {
      // Bound for normal numbers (other cases).
      Node assumption = mkIsFinite(eb,sb, node[1]);

      Node sub = nm->mkNode(kind::SUB, node, node[1]);
      Node diff = nm->mkNode(kind::ABS, sub);
      Node conclusion = nm->mkNode(kind::LEQ, diff, nm->mkConstReal(bnd*2));

      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                               << " ; round_diff_n_rn ; BOUND_REFINE"
                               << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE);
    }
  }

  if ((arg < 0 && round >= 0) || (arg >= 0 && round < 0))
  {
    // Sign preservation.
    Node r1 = nm->mkNode(kind::LT, node[1], nm->mkConstReal(0));
    Node r2 = nm->mkNode(kind::LT, node, nm->mkConstReal(0));
    Node lem = r1.eqNode(r2);
    Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                             << " ; round_samesign ; BOUND_REFINE"
                             << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE);
  }

  if (!RFP::isNan(eb,sb, arg))
  {
    // Pruning of irrelevant numbers.
    Node nan = nm->mkConstReal(RFP::notANumber(eb,sb));
    Node isNan = nm->mkNode(kind::EQUAL, node[1], nan);
    Node isNotNan = isNan.notNode();
    Rational argDn = RFP::round(eb,sb, IRM::TN, arg);
    if (round <= arg && arg < RFP::plusInfinity(eb,sb) && 
      !(RFP::minusZero(eb,sb) < arg && arg < RFP::plusZero(eb,sb)) &&
      round > argDn)
    {
      Node a1 = nm->mkNode(kind::LEQ, node, node[1]);
      Node a2 = a1.andNode(nm->mkNode(kind::LT, node[1], nm->mkConstReal(RFP::plusInfinity(eb,sb))));
      Node a3l = nm->mkNode(kind::GEQ, nm->mkConstReal(RFP::minusZero(eb,sb)), node[1]);
      Node a3u = nm->mkNode(kind::GEQ, node[1], nm->mkConstReal(RFP::plusZero(eb,sb)));
      Node a3 = a2.andNode(a3l.orNode(a3u));
      Node assumption = a3.andNode(isNotNan);
      Node conclusion = nm->mkNode(kind::LEQ, node, nm->mkConstReal(argDn));
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE ub" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE, nullptr, true);
    }

    Rational argUp = RFP::round(eb,sb, IRM::TP, arg);
    if (arg <= round && RFP::minusInfinity(eb,sb) < arg && 
      !(RFP::minusZero(eb,sb) < arg && arg < RFP::plusZero(eb,sb)) &&
      argUp > round)
    {
      Node a1 = nm->mkNode(kind::LEQ, node[1], node);
      Node a2 = a1.andNode(nm->mkNode(kind::LT, nm->mkConstReal(RFP::minusInfinity(eb,sb)), node[1]));
      Node a3l = nm->mkNode(kind::GEQ, nm->mkConstReal(RFP::minusZero(eb,sb)), node[1]);
      Node a3u = nm->mkNode(kind::GEQ, node[1], nm->mkConstReal(RFP::plusZero(eb,sb)));
      Node a3 = a2.andNode(a3l.orNode(a3u));
      Node assumption = a3.andNode(isNotNan);
      Node conclusion = nm->mkNode(kind::LEQ, nm->mkConstReal(argUp), node);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE lb" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE, nullptr, true);
    }

    if (RFP::plusInfinity(eb,sb) <= arg && 
      round != RFP::maxValue(eb,sb) && round != RFP::plusInfinity(eb,sb))
    {
      Node a1 = nm->mkNode(kind::LEQ, nm->mkConstReal(RFP::plusInfinity(eb,sb)), node[1]);
      Node assumption = a1.andNode(isNotNan);
      Node c1 = nm->mkNode(kind::EQUAL, node, nm->mkConstReal(RFP::maxValue(eb,sb)));
      Node c2 = nm->mkNode(kind::EQUAL, node, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      Node conclusion = c1.orNode(c2);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE lp" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE, nullptr, true);
    }

    if (arg <= RFP::minusInfinity(eb,sb) && 
      round != -RFP::maxValue(eb,sb) && round != RFP::minusInfinity(eb,sb))
    {
      Node a1 = nm->mkNode(kind::LEQ, node[1], nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      Node assumption = a1.andNode(isNotNan);
      Node c1 = nm->mkNode(kind::EQUAL, node, nm->mkConstReal(-RFP::maxValue(eb,sb)));
      Node c2 = nm->mkNode(kind::EQUAL, node, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      Node conclusion = c1.orNode(c2);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE ln" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE, nullptr, true);
    }

    if (RFP::minusZero(eb,sb) < arg && arg < RFP::plusZero(eb,sb) &&
      round != RFP::minusZero(eb,sb) && round != RFP::plusZero(eb,sb))
    {
      Node a1 = nm->mkNode(kind::LT, nm->mkConstReal(RFP::minusZero(eb,sb)), node[1]);
      Node a2 = nm->mkNode(kind::LT, node[1], nm->mkConstReal(RFP::plusZero(eb,sb)));
      Node assumption = a1.andNode(a2).andNode(isNotNan);
      Node c1 = nm->mkNode(kind::EQUAL, node, nm->mkConstReal(RFP::minusZero(eb,sb)));
      Node c2 = nm->mkNode(kind::EQUAL, node, nm->mkConstReal(RFP::plusZero(eb,sb)));
      Node conclusion = c1.orNode(c2);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE zero" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND_REFINE, nullptr, true);
    }
  }

  //if (!RFP::isNan(eb,sb, arg))
  //{
  //  // L2-9 ub
  //  //Node i = nm->mkConstReal(arg);
  //  Node i = nm->mkConstReal(
  //    arg >= RFP::minusInfinity(eb,sb) ? arg : RFP::minusInfinity(eb,sb));
  //  Node assumption = nm->mkNode(LEQ, node, i);
  //  Rational argDn = RFP::round(eb,sb, IRM::TNS, arg);
  //  Node ub = nm->mkConstReal(argDn);
  //  //Kind ubOp = (argDn == RFP::minusInfinity(eb,sb)) ? EQUAL : LEQ;
  //  Node conclusion;
  //  if (argDn == RFP::minusInfinity(eb,sb)){
  //    Node isNinf = nm->mkNode(EQUAL, node, ub);
  //    Node nan = nm->mkConstReal(RFP::notANumber(eb,sb));
  //    Node isNan = nm->mkNode(EQUAL, node, nan);
  //    conclusion = isNinf.orNode(isNan);
  //  }else if (argDn == RFP::minSubnormal(eb,sb)){
  //    Node isPosMinSN = nm->mkNode(EQUAL, node, ub);
  //    Node isPosZero = mkIsPosZero(eb,sb, node);
  //    Node isNegZero = mkIsNegZero(eb,sb, node);
  //    Node leqNegMinSN = nm->mkNode(LEQ, node,
  //      nm->mkConstReal(-RFP::minSubnormal(eb,sb)));
  //    conclusion = isPosMinSN.orNode(isPosZero).orNode(isNegZero)
  //      .orNode(leqNegMinSN);
  //  }else if (argDn == RFP::plusZero(eb,sb)){
  //    Node isPosZero = mkIsPosZero(eb,sb, node);
  //    Node isNegZero = mkIsNegZero(eb,sb, node);
  //    Node leqNegMinSN = nm->mkNode(LEQ, node,
  //      nm->mkConstReal(-RFP::minSubnormal(eb,sb)));
  //    conclusion = isPosZero.orNode(isNegZero)
  //      .orNode(leqNegMinSN);
  //  }else if (argDn == RFP::minusZero(eb,sb)){
  //    Node isNegZero = mkIsNegZero(eb,sb, node);
  //    Node leqNegMinSN = nm->mkNode(LEQ, node,
  //      nm->mkConstReal(-RFP::minSubnormal(eb,sb)));
  //    conclusion = isNegZero.orNode(leqNegMinSN);
  //  }else{
  //    conclusion = nm->mkNode(LEQ, node, ub);
  //  }
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-round-lemma")
  //    << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE ub" << std::endl;
  //  d_im.addPendingLemma(
  //    lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
  //}
  //if (!RFP::isNan(eb,sb, arg) 
  //  //&& arg <= round 
  //  //&& RFP::round(eb,sb, IRM::TPS, arg) >  round
  //  //&& RFP::round(eb,sb, IRM::TPS, arg) <= roundC
  //  )
  //{
  //  // L2-9 lb
  //  //Node i = nm->mkConstReal(arg);
  //  Node i = nm->mkConstReal(
  //    arg <= RFP::plusInfinity(eb,sb) ? arg : RFP::plusInfinity(eb,sb));
  //  Node assumption = nm->mkNode(LEQ, i, node);
  //  Rational argUp = RFP::round(eb,sb, IRM::TPS, arg);
  //  Node lb = nm->mkConstReal(argUp);
  //  //Kind lbOp = (argUp == RFP::plusInfinity(eb,sb)) ? EQUAL : LEQ;
  //  Node conclusion;
  //  if (argUp == RFP::plusInfinity(eb,sb)){
  //    Node isPinf = nm->mkNode(EQUAL, node, lb);
  //    conclusion = isPinf;
  //  }else if (argUp == -RFP::minSubnormal(eb,sb)){
  //    Node isNegMinSN = nm->mkNode(EQUAL, node, lb);
  //    Node isNegZero = mkIsNegZero(eb,sb, node);
  //    Node isPosZero = mkIsPosZero(eb,sb, node);
  //    Node geqPosMinSN = nm->mkNode(GEQ, node, 
  //      nm->mkConstReal(RFP::minSubnormal(eb,sb)));
  //    conclusion = isNegMinSN.orNode(isNegZero).orNode(isPosZero)
  //      .orNode(geqPosMinSN);
  //  }else if (argUp == RFP::minusZero(eb,sb)){
  //    Node isNegZero = mkIsNegZero(eb,sb, node);
  //    Node isPosZero = mkIsPosZero(eb,sb, node);
  //    Node geqPosMinSN = nm->mkNode(GEQ, node, 
  //      nm->mkConstReal(RFP::minSubnormal(eb,sb)));
  //    conclusion = isNegZero.orNode(isPosZero)
  //      .orNode(geqPosMinSN);
  //  }else if (argUp == RFP::plusZero(eb,sb)){
  //    Node isPosZero = mkIsPosZero(eb,sb, node);
  //    Node geqPosMinSN = nm->mkNode(GEQ, node, 
  //      nm->mkConstReal(RFP::minSubnormal(eb,sb)));
  //    conclusion = isPosZero.orNode(geqPosMinSN);
  //  }else{
  //    conclusion = nm->mkNode(LEQ, lb, node);
  //  }
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-round-lemma")
  //    << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE lb" << std::endl;
  //  d_im.addPendingLemma(
  //    lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
  //}

  // this is the most naive model-based schema based on model values
  Node lem = valueBasedLemma(node);
  Trace("rfp-round-lemma")
      << "RfpRoundSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  // send the value lemma
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_VALUE_REFINE,
    nullptr, true);
}

void RfpRoundSolver::checkFullRefineRoundPair(TNode node1, 
  const Integer& rm1, const Rational& arg1, const Rational& round1,
  TNode node2,
  const Integer& rm2, const Rational& arg2, const Rational& round2)
{
  FloatingPointSize sz1 = node1.getOperator().getConst<RfpRound>().getSize();
  FloatingPointSize sz2 = node2.getOperator().getConst<RfpRound>().getSize();
  uint32_t eb = sz1.exponentWidth();
  uint32_t sb = sz1.significandWidth();
  NodeManager* nm = NodeManager::currentNM();

  // monotone lemmas
  if (rm1 == rm2 && sz1 == sz2)
  {
    if (arg1 <= arg2 && round1 > round2){
      // L2-5
      Node a1 = nm->mkNode(EQUAL, node1[0], node2[0]);
      Node isFinite1 = mkIsFinite(eb,sb, node1[1]);
      Node isFinite2 = mkIsFinite(eb,sb, node2[1]);
      Node a2 = isFinite1.andNode(isFinite2).andNode(
        nm->mkNode(LEQ, node1[1], node2[1]));
      Node assumption = nm->mkNode(AND, a1, a2);
      Node op = nm->mkConst(RfpLeq(eb,sb));
      Node conclusion = mkTrue(nm->mkNode(RFP_LEQ, op, node1, node2));
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-round-lemma")
          << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
    }
    if (round1 < round2 && arg1 >= round2){
      // L2-6
      Node a1 = nm->mkNode(EQUAL, node1[0], node2[0]);
      Node op = nm->mkConst(RfpLt(eb,sb));
      Node a2 = mkTrue(nm->mkNode(RFP_LT, op, node1, node2));
      Node assumption = nm->mkNode(AND, a1, a2);
      Node conclusion = mkTrue(nm->mkNode(RFP_LT, op, node1[1], node2));
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-round-lemma")
          << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
    }
    if (round1 < round2 && round1 >= arg2){
      // L2-7
      Node a1 = nm->mkNode(EQUAL, node1[0], node2[0]);
      Node op = nm->mkConst(RfpLt(eb,sb));
      Node a2 = mkTrue(nm->mkNode(RFP_LT, op, node1, node2));
      Node assumption = nm->mkNode(AND, a1, a2);
      Node conclusion = mkTrue(nm->mkNode(RFP_LT, op, node1, node2[1]));
      Node lem = nm->mkNode(IMPLIES, assumption, conclusion);
      Trace("rfp-round-lemma")
          << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
    }

    // TODO: L2-10, L2-11, L2-12
  }
}

Node RfpRoundSolver::valueBasedLemma(Node node)
{
  Assert(node.getKind() == RFP_ROUND || node.getKind() == RFP_TO_RFP_FROM_RFP);
  Node rm = node[0];
  Node arg = node[1];

  Node valRm = d_model.computeConcreteModelValue(rm);
  Node valArg = d_model.computeConcreteModelValue(arg);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(RFP_ROUND, node.getOperator(), valRm, valArg);
  valC = rewrite(valC);

  Node assumption = nm->mkNode(AND, rm.eqNode(valRm), arg.eqNode(valArg));
  return nm->mkNode(IMPLIES, assumption, node.eqNode(valC));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
