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
 * Implementation of the RFP solver for comparison operators.
 */

#include "theory/arith/nl/rfp_comp_solver.h"

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

RfpCompSolver::RfpCompSolver(Env& env,
                             InferenceManager& im,
                             NlModel& model)
    : RfpSolver(env, im, model)
{}

RfpCompSolver::~RfpCompSolver() {}

bool RfpCompSolver::isTarget(const Node& n)
{
  Kind k = n.getKind();
  return k == Kind::RFP_GT || k == Kind::RFP_GEQ;
}

//

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

void RfpCompSolver::checkInitialRefineGt(Node node) 
{
  Trace("rfp-gt") << "RFP_GT term (init): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpGt>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
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
    Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
                          << " ; gt_finite ; INIT_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
  }
  //{
  //  Node isPinfX = mkIsPosInf(eb,sb, node[0]);
  //  Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
  //  Node isNotPinfY = mkIsPosInf(eb,sb, node[1]).notNode();
  //  Node assumption = isPinfX
  //    .andNode(isNotNanY).andNode(isNotPinfY);

  //  Node conclusion = mkIsOne(node);

  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
  //                        << " ; gt_pinf ; INIT_REFINE"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
  //}
  //{
  //  Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
  //  Node isNotNinfX = mkIsNegInf(eb,sb, node[0]).notNode();
  //  Node isNinfY = mkIsNegInf(eb,sb, node[1]);
  //  Node assumption = isNotNanX.andNode(isNotNinfX)
  //    .andNode(isNinfY);

  //  Node conclusion = mkIsOne(node);

  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
  //                        << " ; gt_ninf ; INIT_REFINE"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
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
  //  Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
  //                        << " ; gt_non_zero_zero ; INIT"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
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
  //  Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
  //                        << " ; gt_non_zero_zero ; COMP"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
  //}
  {
    // gt_special
    Node lem = mkGtSpecial(eb,sb, node);
    Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
                          << " ; gt_special ; INIT_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
  }
  {
    Node lem = mkBoolIntConstraint(node);
  Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
  << " ; gt_range ; INIT_REFINE"
  << std::endl;
  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
  }
}

void RfpCompSolver::checkAuxRefineGt(Node node) 
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
  //  Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem << " ; AUX_REFINE0"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  //}

  //// TODO
  //{
  //  Node gtTrue = mkIsOne(node);
  //  Node gtFalse = mkFalse(node);
  //  Node gtXY = nm->mkNode(Kind::GT, node[0], node[1]);
  //  gtXY = rewrite(gtXY);
  //  Node lem = gtXY.iteNode(gtTrue, gtFalse);
  //  Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
  //                        << " ; gt_finite ; COMP"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  //}

  if (( options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
        //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
       ) &&
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
    Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
                          << " ; gt_finite ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
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
    Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
                          << " ; gt_pinf ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
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
    Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
                          << " ; gt_pinf ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
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
    Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
                          << " ; gt_zero_non_zero ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
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
    Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
                          << " ; gt_non_zero_zero ; COMP"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  }

  if ((x == RFP::notANumber(eb,sb) || y == RFP::notANumber(eb,sb)) &&
      t != 0)
  {
    Node isNanX = mkIsNan(eb,sb, node[0]);
    Node isNanY = mkIsNan(eb,sb, node[1]);
    Node assumption = isNanX.orNode(isNanY);
    Node lem = assumption.impNode(mkFalse(node));
    Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
                          << " ; gt_nan ; AUX_REFINE"
                          << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  }

  //if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  //{
  //  // gt_special
  //  Node lem = mkGtSpecial(eb,sb, node);
  //  Trace("rfp-gt-lemma") << "RfpCompSolver::Lemma: " << lem 
  //                        << " ; gt_special ; AUX_REFINE"
  //                        << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  //}
  //else
  //if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
  //    ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
  //      (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  //{
  //  // this is the most naive model-based schema based on model values
  //  Node lem = relValueBasedLemma(node);
  //  Trace("rfp-gt-lemma")
  //      << "RfpCompSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  //  // send the value lemma
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_V,
  //                       nullptr, true);
  //}
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

void RfpCompSolver::checkInitialRefineGeq(Node node) 
{
  Trace("rfp-geq") << "RFP_GEQ term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpGeq>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  if (options().smt.rfpLazyLearn == options::rfpLLMode::WEAK
      || options().smt.rfpLazyLearn == options::rfpLLMode::MID
      )
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
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; ge_finite ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
  }
  {
    // ge_special
    Node lem = mkGeqSpecial(eb,sb, node);
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; ge_special ; AUX_INIT"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
  }
  {
    Node lem = mkBoolIntConstraint(node);
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; geq_range ; INIT_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_I);
  }
}

void RfpCompSolver::checkAuxRefineGeq(Node node) 
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
  //  Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem << " ; AUX_REFINE0"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  //}

  if (( options().smt.rfpLazyLearn == options::rfpLLMode::STRONG
        //|| options().smt.rfpLazyLearn == options::rfpLLMode::MID
       ) &&
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
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; ge_finite ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  }

  if (x == RFP::plusInfinity(eb,sb) && !RFP::isNan(eb,sb, y) &&
      t == 0)
  {
    // ge_pinf
    Node isPinfX = mkIsNegInf(eb,sb, node[0]);
    Node isNotNanY = mkIsNan(eb,sb, node[1]).notNode();
    Node assumption = isPinfX.andNode(isNotNanY);
    Node lem = assumption.impNode(mkIsOne(node));
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; ge_pinf ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  }

  if (!RFP::isNan(eb,sb, x) && y == RFP::minusInfinity(eb,sb) &&
      t == 0)
  {
    // ge_ninf
    Node isNotNanX = mkIsNan(eb,sb, node[0]).notNode();
    Node isNinfY = mkIsNegInf(eb,sb, node[1]);
    Node assumption = isNotNanX.andNode(isNinfY);
    Node lem = assumption.impNode(mkIsOne(node));
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; ge_ninf ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
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
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; ge_zero_non_zero ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
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
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; ge_non_zero_zero ; COMP"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  }

  if ((x == RFP::notANumber(eb,sb) || y == RFP::notANumber(eb,sb)) &&
      t != 0)
  {
    Node isNanX = mkIsNan(eb,sb, node[0]);
    Node isNanY = mkIsNan(eb,sb, node[1]);
    Node assumption = isNanX.orNode(isNanY);
    Node lem = assumption.impNode(mkFalse(node));
    Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
                           << " ; ge_nan ; AUX_REFINE"
                           << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  }

  //if (!RFP::isFinite(eb,sb, x) || !RFP::isFinite(eb,sb, y))
  //{
  //  // geq_special
  //  Node lem = mkGeqSpecial(eb,sb, node);
  //  Trace("rfp-geq-lemma") << "RfpCompSolver::Lemma: " << lem 
  //                         << " ; geq_special ; AUX_REFINE"
  //                         << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_AUX);
  //}
  //else
  //if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
  //    ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
  //      (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  //{
  //  // this is the most naive model-based schema based on model values
  //  Node lem = relValueBasedLemma(node);
  //  Trace("rfp-geq-lemma")
  //      << "RfpCompSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  //  // send the value lemma
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_V,
  //                       nullptr, true);
  //}
}

void RfpCompSolver::checkFullRefineRelOp(const FloatingPointSize& sz, Node node) 
{
  Trace("rfp-comp-solver") << "term: " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  Node valTerm = d_model.computeAbstractModelValue(node);
  Node valTermC = d_model.computeConcreteModelValue(node);

  Node valX = d_model.computeConcreteModelValue(node[0]);
  Node valY = d_model.computeConcreteModelValue(node[1]);

  Rational x = valX.getConst<Rational>();
  Rational y = valY.getConst<Rational>();
  Rational t = valTerm.getConst<Rational>();

  if (TraceIsOn("rfp-comp-solver"))
  {
    Trace("rfp-comp-solver") << "* " << node << ", value = " << valTerm
                             << std::endl;
    Trace("rfp-comp-solver") << "  actual (" << x << ", " << y
                             << ") = " << valTermC << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-comp-solver") << "...already correct" << std::endl;
    return;
  }

  if (options().smt.rfpValueRefine == options::rfpVRMode::ALL ||
      ( (RFP::isZero(eb,sb, x) || RFP::isInfinite(eb,sb, x) || RFP::isNan(eb,sb, x)) &&
        (RFP::isZero(eb,sb, y) || RFP::isInfinite(eb,sb, y) || RFP::isNan(eb,sb, y)) ))
  {
    // this is the most naive model-based schema based on model values
    std::vector<Node> cs;
    cs.push_back(node.getOperator());
    cs.push_back(valX);
    cs.push_back(valY);
    Node valC = nm->mkNode(node.getKind(), cs);
    valC = rewrite(valC);

    Node assumption = node[0].eqNode(valX).andNode(node[1].eqNode(valY));
    Node lem = assumption.impNode(node.eqNode(valC));
    Trace("rfp-comp-lemma")
        << "RfpCompSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
    // send the value lemma
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_COMP_V,
                         nullptr, true);
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
