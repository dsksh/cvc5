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
#include "theory/arith/nl/ext/ext_state.h"
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
                               NlModel& model,
                               ExtState* data)
    : EnvObj(env),
      d_im(im),
      d_model(model),
      d_data(data),
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

  //d_data->d_rounds.clear();
  //d_data->d_ms_prune_vs.clear();
  //Trace("rfp-round-prune") << "clear d_rounds" << std::endl;

  Trace("rfp-round-mv") << "RFP_TO_FP terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak == Kind::RFP_ROUND)
    {
      u_int32_t hash = a.getOperator().getConst<RfpRound>();
      d_rounds[hash].push_back(a);
      Trace("rfp-round-mv") << "- " << a << std::endl;
    }
    else if(ak == Kind::RFP_TO_RFP_FROM_RFP)
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
        Node rounded = nm->mkNode(Kind::RFP_ROUND, op, node[0], node[1]);
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
  Trace("rfp-round-check") << "RfpRoundSolver::checkFullRefine" << std::endl;
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
        Trace("rfp-round-check") << "  value  (" << valRmA << ", " 
                                 << valArgA << ") = " << valRound
                                 << std::endl;
        Trace("rfp-round-check") << "  actual (" << rm << ", " 
                                 << arg << ") = " << valRoundC 
                                 << std::endl;

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
  FloatingPointSize sz = node.getOperator().getConst<RfpRound>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn != options::rfpLLMode::STRONG)
  {
    NodeManager* nm = NodeManager::currentNM();
    Node sub = nm->mkNode(Kind::SUB, node, node[1]);
    {
      // Bound for subnormal numbers.
      Node assumption = mkIsSubnormalWeak(eb,sb, node[1]);

      Rational minSN = RFP::minSubnormal(eb,sb);
      Node bound = nm->mkConstReal(minSN);
      Node lb = nm->mkNode(Kind::LT, nm->mkNode(Kind::NEG, bound), sub);
      Node ub = nm->mkNode(Kind::LT, sub, bound);
      Node l1 = assumption.impNode(lb.andNode(ub));
    
      Node boundN = nm->mkConstReal(minSN/2);
      Node lbN = nm->mkNode(Kind::LEQ, nm->mkNode(Kind::NEG, boundN), sub);
      Node ubN = nm->mkNode(Kind::LEQ, sub, boundN);
      Node l2 = assumption.impNode(lbN.andNode(ubN));
    
      Node lem = mkIsToNearest(node[0]).iteNode(l2, l1);
      Trace("rfp-round-lemma-bnd") << "RfpRoundSolver::Lemma: " << lem
                                   << " ; round_diff_sn ; INIT_REFINE"
                                   << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
    }
    {
      // Relative bound for normal numbers.
      Node assumption = mkIsNormal(eb,sb, node[1]);

      Rational err = Rational(Integer::pow2(sb-1)).inverse();

      Node coeff = nm->mkConstReal(err);
      Node bound = nm->mkNode(Kind::MULT, coeff, mkAbs(node[1]));
      Node lb = nm->mkNode(Kind::LT, nm->mkNode(Kind::NEG, bound), sub);
      Node ub = nm->mkNode(Kind::LT, sub, bound);
      Node l1 = lb.andNode(ub);

      Node coeffN = nm->mkConstReal(err/2);
      Node boundN = nm->mkNode(Kind::MULT, coeffN, mkAbs(node[1]));
      Node lbN = nm->mkNode(Kind::LEQ, nm->mkNode(Kind::NEG, boundN), sub);
      Node ubN = nm->mkNode(Kind::LEQ, sub, boundN);
      Node l2 = lbN.andNode(ubN);

      Node lem = assumption.impNode( mkIsToNearest(node[0]).iteNode(l2, l1) );
      Trace("rfp-round-lemma-bnd") << "RfpRoundSolver::Lemma: " << lem
                                   << " ; round_diff_n ; INIT_REFINE"
                                   << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
    }
  }
  //{
  //  Node lem = mkRoundCases(eb,sb, node[1], eb,sb, node);
  //  Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
  //                           << " ; round_cases ; INIT_REFINE"
  //                           << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
  //}
  {
    Node isNormal = mkIsNormal(eb,sb, node);
    Node isSubnormal = mkIsSubnormal(eb,sb, node);
    Node isZero = mkIsZero(eb,sb, node);
    Node isInf = mkIsInf(eb,sb, node);
    Node isNan = mkIsNan(eb,sb, node);
    Node lem = isNormal.orNode(isSubnormal).orNode(isZero).orNode(isInf).orNode(isNan);
    Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                             << " ; round_cases ; INIT_REFINE"
                             << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
  }
}

void RfpRoundSolver::checkFullRefineRound(TNode node, 
  const Integer& rm, const Rational& arg, 
  const Rational& round, const Rational& roundC)
{
  FloatingPointSize sz = node.getOperator().getConst<RfpRound>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();
  NodeManager* nm = NodeManager::currentNM();

  // TODO
  d_data->registerRfpRound(node[1], node);

  Node nan = nm->mkConstReal(RFP::notANumber(eb,sb));
  Node isNan = node.eqNode(nan);
  Node isNotNan = isNan.notNode();

  if (options().smt.rfpLazyLearn == options::rfpLLMode::STRONG)
  {
    if (RFP::isSubnormal(eb,sb, arg) || RFP::isSubnormal(eb,sb, round))
    {
      Node a1 = isNotNan.andNode(mkIsSubnormalWeak(eb,sb, node[1]));
      Node a2 = isNotNan.andNode(mkIsSubnormalWeak(eb,sb, node));
      Node aRange = a1.orNode(a2);
      //Node aRange = mkIsSubnormalWeak(eb,sb, node[1]);
      checkRoundError(RFP::minSubnormal(eb,sb), 
        rm, arg, round, node, aRange);
    }

    // TODO: condition can be modified?
    if (RFP::isNormal(eb,sb, arg) || RFP::isNormal(eb,sb, round))
    //if (RFP::isNormal(eb,sb, arg))
    {
      Rational rerr = Rational(Integer::pow2(sb-1)).inverse();

      //Node a1 = mkIsNormal(eb,sb, node[1]);
      //Node a2 = mkIsNormal(eb,sb, node);
      //Node aRange = a1.orNode(a2);
      Node aRange = mkIsNormal(eb,sb, node[1]);
      checkRoundError(rerr, 
        rm, arg, round, node, aRange, true);
    }

    if (RFP::isNormal(eb,sb, arg))
    {
      Rational argAR = RFP::round(eb,sb, IRM::TP, arg.abs());

      int e = argAR.ilog2();
      Rational bnd = e >= int(sb-1) ? Integer::pow2(e-int(sb-1)) :
        Rational(1) / Integer::pow2(int(sb-1)-e);

      Trace("rfp-ilog2-debug") << "ilog2(" << arg.abs() << "): " << arg.ilog2() << std::endl;

      Node a1 = nm->mkNode(Kind::LEQ, nm->mkConstReal(-argAR), node[1]);
      Node a2 = nm->mkNode(Kind::LEQ, node[1], nm->mkConstReal(argAR));
      Node aRange = a1.andNode(a2);
      //Node a3 = mkIsNormal(eb,sb, node);
      //Node aRange = isNotNan.andNode(a1).andNode(a2).andNode(a3);
      checkRoundError(bnd, 
        rm, arg, round, node, aRange);
    }

    if (RFP::isNormal(eb,sb, round))
    {
      // Apply roundings since round can be assigned a non-FP value.
      Rational roundAR = RFP::round(eb,sb, IRM::TP, round.abs());

      int e = roundAR.ilog2();
      Rational bnd = e >= int(sb-1) ? Integer::pow2(e-int(sb-1)) :
        Rational(1) / Integer::pow2(int(sb-1)-e);

      Trace("rfp-ilog2-debug") << "ilog2(" << round.abs() << "): " << round.ilog2() << std::endl;

      Node a1 = nm->mkNode(Kind::LEQ, nm->mkConstReal(-roundAR), node[1]);
      Node a2 = nm->mkNode(Kind::LEQ, node[1], nm->mkConstReal(roundAR));
      Node aRange = a1.andNode(a2);
      //Node a3 = mkIsNormal(eb,sb, node);
      //Node aRange = isNotNan.andNode(a1).andNode(a2).andNode(a3);
      checkRoundError(bnd, 
        rm, arg, round, node, aRange);
    }
  }

  if ((arg < 0 && round >= 0) || (arg >= 0 && round < 0))
  {
    // Sign preservation.
    Node r1 = nm->mkNode(Kind::GT, node[1], nm->mkConstReal(0));
    Node r2 = nm->mkNode(Kind::GT, node, nm->mkConstReal(0));
    Node lem = isNotNan.impNode(r1.eqNode(r2));
    Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                             << " ; round_samesign ; BOUND_REFINE"
                             << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_SIGN);
  }
  if ((arg < 1 && round >= 1) || (arg >= 1 && round < 1))
  {
    Node r1 = nm->mkNode(Kind::GEQ, node[1], nm->mkConstReal(1));
    Node r2 = nm->mkNode(Kind::GEQ, node, nm->mkConstReal(1));
    Node lem = isNotNan.impNode(r1.eqNode(r2));
    Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                             << " ; round_geq_one ; BOUND_REFINE"
                             << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_SIGN);
  }
  if ((arg < -1 && round >= -1) || (arg >= -1 && round < -1))
  {
    Node r1 = nm->mkNode(Kind::GT, node[1], nm->mkConstReal(-1));
    Node r2 = nm->mkNode(Kind::GT, node, nm->mkConstReal(-1));
    Node lem = isNotNan.impNode(r1.eqNode(r2));
    Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem
                             << " ; round_leq_m_one ; BOUND_REFINE"
                             << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_SIGN);
  }

  {
    // Pruning of irrelevant numbers.
    //Node nan = nm->mkConstReal(RFP::notANumber(eb,sb));
    //Node isNan = nm->mkNode(Kind::EQUAL, node[1], nan);
    //Node isNotNan = isNan.notNode();

    Rational argDn = RFP::round(eb,sb, IRM::TN, arg);
    Rational argUp = RFP::round(eb,sb, IRM::TP, arg);

    if (round <= arg && arg < RFP::plusInfinity(eb,sb) && 
      !(RFP::minusZero(eb,sb) < arg && arg < RFP::plusZero(eb,sb)) &&
      round > argDn)
    {
      int e = argDn.abs().ilog2();
      Rational bnd = e >= int(sb-1) ? Integer::pow2(e-int(sb-1)) :
        Rational(1) / Integer::pow2(int(sb-1)-e);
      Rational argDnDn = argDn - bnd;

      //Node a1 = nm->mkNode(Kind::LEQ, node, nm->mkConstReal(arg));
      Node a1 = nm->mkNode(Kind::LT, node, nm->mkConstReal(argUp));
      Node assumption = isNotNan.andNode(a1);

      Node conclusion = nm->mkNode(Kind::LEQ, node, nm->mkConstReal(argDn));
      if (RFP::isNormal(eb,sb, argDnDn))
      {
        Node c1 = node.eqNode(nm->mkConstReal(argDn));
        Node c2 = nm->mkNode(Kind::LEQ, node, nm->mkConstReal(argDnDn));
        conclusion = c1.orNode(c2);

        //e = argDnDn.abs().ilog2();
        //bnd = e >= int(sb-1) ? Integer::pow2(e-int(sb-1)) :
        //  Rational(1) / Integer::pow2(int(sb-1)-e);
        //Rational argDnDnDn = argDnDn - bnd;
        //if (RFP::isNormal(eb,sb, argDnDnDn))
        //{
        //  c1 = node.eqNode(nm->mkConstReal(argDn));
        //  c2 = node.eqNode(nm->mkConstReal(argDnDn));
        //  Node c3 = nm->mkNode(Kind::LEQ, node, nm->mkConstReal(argDnDnDn));
        //  conclusion = c1.orNode(c2).orNode(c3);

        //  e = argDnDnDn.abs().ilog2();
        //  bnd = e >= int(sb-1) ? Integer::pow2(e-int(sb-1)) :
        //    Rational(1) / Integer::pow2(int(sb-1)-e);
        //  Rational argDnDnDnDn = argDnDnDn - bnd;
        //  if (RFP::isNormal(eb,sb, argDnDnDnDn))
        //  {
        //    c1 = node.eqNode(nm->mkConstReal(argDn));
        //    c2 = node.eqNode(nm->mkConstReal(argDnDn));
        //    c3 = node.eqNode(nm->mkConstReal(argDnDnDn));
        //    Node c4 = nm->mkNode(Kind::LEQ, node, nm->mkConstReal(argDnDnDnDn));
        //    conclusion = c1.orNode(c2).orNode(c3).orNode(c4);
        //  }
        //}
      }
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE ub" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_PRUNE, nullptr, true);

      //d_data->registerRfpRound(node[1], node);
    }

    if (arg <= round && RFP::minusInfinity(eb,sb) < arg && 
      !(RFP::minusZero(eb,sb) < arg && arg < RFP::plusZero(eb,sb)) &&
      argUp > round)
    {
      int e = argUp.abs().ilog2();
      Rational bnd = e >= int(sb-1) ? Integer::pow2(e-int(sb-1)) :
        Rational(1) / Integer::pow2(int(sb-1)-e);
      Rational argUpUp = argUp + bnd;

      //Trace("rfp-round-debug1") << "argUp:      " << argUp << std::endl;
      //Trace("rfp-round-debug1") << "argUpUp:    " << argUpUp << std::endl;
      //Trace("rfp-round-debug1") << "r(argUpUp): " << RFP::round(eb,sb, IRM::NE, argUpUp) << std::endl;

      //Node a1 = nm->mkNode(Kind::LEQ, nm->mkConstReal(arg), node);
      Node a1 = nm->mkNode(Kind::LT, nm->mkConstReal(argDn), node);
      Node assumption = isNotNan.andNode(a1);

      Node conclusion = nm->mkNode(Kind::LEQ, nm->mkConstReal(argUp), node);
      if (RFP::isNormal(eb,sb, argUpUp))
      {
        Node c1 = node.eqNode(nm->mkConstReal(argUp));
        Node c2 = nm->mkNode(Kind::LEQ, nm->mkConstReal(argUpUp), node);
        conclusion = c1.orNode(c2);

        //e = argUpUp.abs().ilog2();
        //bnd = e >= int(sb-1) ? Integer::pow2(e-int(sb-1)) :
        //  Rational(1) / Integer::pow2(int(sb-1)-e);
        //Rational argUpUpUp = argUpUp + bnd;
        //if (RFP::isNormal(eb,sb, argUpUpUp))
        //{
        //  c1 = node.eqNode(nm->mkConstReal(argUp));
        //  c2 = node.eqNode(nm->mkConstReal(argUpUp));
        //  Node c3 = nm->mkNode(Kind::LEQ, nm->mkConstReal(argUpUpUp), node);
        //  conclusion = c1.orNode(c2).orNode(c3);

        //  e = argUpUpUp.abs().ilog2();
        //  bnd = e >= int(sb-1) ? Integer::pow2(e-int(sb-1)) :
        //    Rational(1) / Integer::pow2(int(sb-1)-e);
        //  Rational argUpUpUpUp = argUpUpUp + bnd;
        //  if (RFP::isNormal(eb,sb, argUpUpUpUp))
        //  {
        //    c1 = node.eqNode(nm->mkConstReal(argUp));
        //    c2 = node.eqNode(nm->mkConstReal(argUpUp));
        //    c3 = node.eqNode(nm->mkConstReal(argUpUpUp));
        //    Node c4 = nm->mkNode(Kind::LEQ, nm->mkConstReal(argUpUpUpUp), node);
        //    conclusion = c1.orNode(c2).orNode(c3).orNode(c4);
        //  }
        //}
      }
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE lb" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_PRUNE, nullptr, true);

      //d_data->registerRfpRound(node[1], node);
    }

    if (//RFP::plusInfinity(eb,sb) <= arg && 
        arg >= RFP::maxValue(eb,sb) && 
        round != RFP::maxValue(eb,sb) && round != RFP::plusInfinity(eb,sb))
    {
      //Node a1 = nm->mkNode(Kind::LEQ, nm->mkConstReal(RFP::plusInfinity(eb,sb)), node[1]);
      Node a1 = nm->mkNode(Kind::LEQ, nm->mkConstReal(RFP::maxValue(eb,sb)), node[1]);
      Node assumption = isNotNan.andNode(a1);
      Node c1 = nm->mkNode(Kind::EQUAL, node, nm->mkConstReal(RFP::maxValue(eb,sb)));
      Node c2 = nm->mkNode(Kind::EQUAL, node, nm->mkConstReal(RFP::plusInfinity(eb,sb)));
      Node conclusion = c1.orNode(c2);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE lp" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_PRUNE, nullptr, true);
    }

    if (//arg <= RFP::minusInfinity(eb,sb) && 
        arg <= -RFP::maxValue(eb,sb) && 
        round != -RFP::maxValue(eb,sb) && round != RFP::minusInfinity(eb,sb))
    {
      //Node a1 = nm->mkNode(Kind::LEQ, node[1], nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      Node a1 = nm->mkNode(Kind::LEQ, node[1], nm->mkConstReal(-RFP::maxValue(eb,sb)));
      Node assumption = isNotNan.andNode(a1);
      Node c1 = nm->mkNode(Kind::EQUAL, node, nm->mkConstReal(-RFP::maxValue(eb,sb)));
      Node c2 = nm->mkNode(Kind::EQUAL, node, nm->mkConstReal(RFP::minusInfinity(eb,sb)));
      Node conclusion = c1.orNode(c2);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE ln" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_PRUNE, nullptr, true);
    }

    if (RFP::minusZero(eb,sb) < arg && arg < RFP::plusZero(eb,sb) &&
      round != RFP::minusZero(eb,sb) && round != RFP::plusZero(eb,sb))
    {
      Node a1 = nm->mkNode(Kind::LT, nm->mkConstReal(RFP::minusZero(eb,sb)), node[1]);
      Node a2 = nm->mkNode(Kind::LT, node[1], nm->mkConstReal(RFP::plusZero(eb,sb)));
      Node assumption = isNotNan.andNode(a1.andNode(a2));
      Node c1 = nm->mkNode(Kind::EQUAL, node, nm->mkConstReal(RFP::minusZero(eb,sb)));
      Node c2 = nm->mkNode(Kind::EQUAL, node, nm->mkConstReal(RFP::plusZero(eb,sb)));
      Node conclusion = c1.orNode(c2);
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; BOUND_REFINE zero" << std::endl;
      d_im.addPendingLemma(
        lem, InferenceId::ARITH_NL_RFP_ROUND_PRUNE, nullptr, true);
    }
  }

  // TODO: condition can be weakened?
  if ((RFP::isZero(eb,sb, arg) || RFP::isInfinite(eb,sb, arg) || RFP::isNan(eb,sb, arg))) 
  {
    // this is the most naive model-based schema based on model values
    Node lem = valueBasedLemma(node);
    Trace("rfp-round-lemma")
        << "RfpRoundSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_VALUE_REFINE,
      nullptr, true);
  }
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
      Node a1 = node1[0].eqNode(node2[0]);
      Node isFinite1 = mkIsFinite(eb,sb, node1[1]);
      Node isFinite2 = mkIsFinite(eb,sb, node2[1]);
      Node a2 = isFinite1.andNode(isFinite2).andNode(
        nm->mkNode(Kind::LEQ, node1[1], node2[1]));
      Node assumption = a1.andNode(a2);
      Node op = nm->mkConst(RfpLeq(eb,sb));
      Node conclusion = mkTrue(nm->mkNode(Kind::RFP_LEQ, op, node1, node2));
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
          << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
    }
    if (round1 < round2 && arg1 >= round2){
      // L2-6
      Node a1 = node1[0].eqNode(node2[0]);
      Node op = nm->mkConst(RfpLt(eb,sb));
      Node a2 = mkTrue(nm->mkNode(Kind::RFP_LT, op, node1, node2));
      Node assumption = a1.andNode(a2);
      Node conclusion = mkTrue(nm->mkNode(Kind::RFP_LT, op, node1[1], node2));
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
          << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
    }
    if (round1 < round2 && round1 >= arg2){
      // L2-7
      Node a1 = node1[0].eqNode(node2[0]);
      Node op = nm->mkConst(RfpLt(eb,sb));
      Node a2 = mkTrue(nm->mkNode(Kind::RFP_LT, op, node1, node2));
      Node assumption = a1.andNode(a2);
      Node conclusion = mkTrue(nm->mkNode(Kind::RFP_LT, op, node1, node2[1]));
      Node lem = assumption.impNode(conclusion);
      Trace("rfp-round-lemma")
          << "RfpRoundSolver::Lemma: " << lem << " ; MONOTONE_REFINE" << std::endl;
      d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_RFP_ROUND_MONOTONE_REFINE, nullptr, true);
    }

    // TODO: L2-10, L2-11, L2-12
  }
}

void RfpRoundSolver::checkRoundError(Rational err0,
                                     Integer rm, Rational arg, Rational round, 
                                     Node node, Node aRange, 
                                     bool isRelative)
{
  bool isNearest = (rm == IRM::NA || rm == IRM::NE);
  Rational err = isNearest ? err0/2 : err0;

  if ( (!isRelative && (arg - round).abs() <= err)
    || ( isRelative && (arg - round).abs() <= err * arg.abs()) )
  {
    return;
  }

  NodeManager* nm = NodeManager::currentNM();

  // Bound for subnormal numbers (RN cases).
  Node assumption = rewrite(aRange);
  if (isNearest){
    Node a1 = mkIsToNearest(node[0]);
    assumption = assumption.andNode(a1);
  }

  Node sub = nm->mkNode(Kind::SUB, node, node[1]);

  Node bndN, bndP;
  if (!isRelative)
  {
    bndN = nm->mkConstReal(-err);
    bndP = nm->mkConstReal(err);
  }
  else
  {
    Node coeff = nm->mkConstReal(err);
    bndP = nm->mkNode(Kind::MULT, coeff, mkAbs(node[1]));
    bndN = nm->mkNode(Kind::NEG, bndP);
  }
  Node c1 = nm->mkNode(Kind::LEQ, bndN, sub);
  Node c2 = nm->mkNode(Kind::LEQ, sub, bndP);
  Node conclusion = c1.andNode(c2);
  conclusion = rewrite(conclusion);

  Node lem = assumption.impNode(conclusion);
  Trace("rfp-round-err-lemma") << "RfpRoundSolver::Lemma: " << lem
                           << " ; round_diff; BOUND_REFINE"
                           << std::endl;
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_BOUND);
}

Node RfpRoundSolver::valueBasedLemma(Node node)
{
  Assert(node.getKind() == Kind::RFP_ROUND || 
         node.getKind() == Kind::RFP_TO_RFP_FROM_RFP);
  Node rm = node[0];
  Node arg = node[1];

  Node valRm = d_model.computeConcreteModelValue(rm);
  Node valArg = d_model.computeConcreteModelValue(arg);

  NodeManager* nm = NodeManager::currentNM();
  Node valC = nm->mkNode(Kind::RFP_ROUND, node.getOperator(), valRm, valArg);
  valC = rewrite(valC);

  Node assumption = ( rm.eqNode(valRm) ).andNode( arg.eqNode(valArg) );
  return assumption.impNode(node.eqNode(valC));
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
