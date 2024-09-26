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
 * Implementation of the RFP solver for rfp.to_real.
 */

#include "theory/arith/nl/rfp_to_real_solver.h"

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

RfpToRealSolver::RfpToRealSolver(Env& env,
                                 InferenceManager& im,
                                 NlModel& model)
    : RfpSolver(env, im, model)
{}

RfpToRealSolver::~RfpToRealSolver() {}

bool RfpToRealSolver::isTarget(const Node& n)
{
  Kind k = n.getKind();
  return k == Kind::RFP_TO_REAL;
}

//

void RfpToRealSolver::checkInitialRefineToReal(Node node) 
{
  Trace("rfp-to-real") << "RFP_TO_REAL term (init): " << node << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FloatingPointSize sz = node.getOperator().getConst<RfpToReal>().getSize();
  uint32_t eb = sz.exponentWidth();
  uint32_t sb = sz.significandWidth();

  {
    //Node a1 = mkIsFinite(eb,sb, node[0]);
    ////Node a2 = mkIsFinite(eb,sb, node);
    ////Node assumption = a1.orNode(a2);
    //Node assumption = a1;
    Node isZeroX = mkIsZero(eb,sb, node[0]);
    Node isZero = node.eqNode(nm->mkConstReal(0)); 
    Node eqX = node.eqNode(node[0]);
    Node conclusion = isZeroX.iteNode(isZero, eqX);
    //Node lem = assumption.impNode(conclusion);
    Node lem = conclusion;
    Trace("rfp-to-real-lemma")
        << "RfpToRealSolver::Lemma: " << lem << " ; INIT_REFINE" << std::endl;
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_TR_INIT_REFINE);
  }
  //{
  //  Node isNormal = mkIsNormal(eb,sb, node);
  //  Node isSubnormal = mkIsSubnormal(eb,sb, node);
  //  Node isZero = mkIsZero(eb,sb, node);
  //  Node isInf = mkIsInf(eb,sb, node);
  //  Node isNan = mkIsNan(eb,sb, node);
  //  Node lem = isNormal.orNode(isSubnormal).orNode(isZero).orNode(isInf).orNode(isNan);
  //  Trace("rfp-to-real-lemma") << "RfpToRealSolver::Lemma: " << lem
  //                             << " ; round_cases ; INIT_REFINE"
  //                             << std::endl;
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_TR_INIT_REFINE);
  //}
}

void RfpToRealSolver::checkAuxRefineToReal(Node node) 
{
  Trace("rfp-to-real") << "RFP_TO_REAL term: " << node << std::endl;
  //NodeManager* nm = NodeManager::currentNM();
  //FloatingPointSize sz = node.getOperator().getConst<RfpToReal>().getSize();
  //uint32_t eb = sz.exponentWidth();
  //uint32_t sb = sz.significandWidth();

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

    //Rational tC = valTermC.getConst<Rational>();
    //Trace("rfp-to-real") << "         ("
    //                     << ARFP(eb,sb, x) << ") = " 
    //                     << ARFP(eb,sb, tC) << std::endl;
  }
  if (valTerm == valTermC)
  {
    Trace("rfp-to-real") << "...already correct" << std::endl;
    return;
  }

  //if (RFP::isNan(eb,sb, x) || RFP::isInfiniteWeak(eb,sb, x))
  //{
  //  Node assumption = node.eqNode(nm->mkConstReal(t));
  //  Node c1 = node[0].eqNode(nm->mkConstReal(t));
  //  Node c2 = mkIsNan(eb,sb, node[0]).orNode(mkIsInf(eb,sb, node[0]));
  //  Node conclusion = c1.orNode(c2);
  //  Node lem = assumption.impNode(conclusion);
  //  Trace("rfp-to-real-lemma")
  //      << "RfpToRealSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
  //  // send the value lemma
  //  d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_TR_VALUE_REFINE);
  //}
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
