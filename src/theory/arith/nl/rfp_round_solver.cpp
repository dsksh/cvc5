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
#include "util/rfp_round.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
  d_zero = nm->mkConstInt(Rational(0));
  d_one = nm->mkConstInt(Rational(1));
  d_two = nm->mkConstInt(Rational(2));
}

RfpRoundSolver::~RfpRoundSolver() {}

void RfpRoundSolver::initLastCall(const std::vector<Node>& assertions,
                                  const std::vector<Node>& false_asserts,
                                  const std::vector<Node>& xts)
{
  d_terms.clear();

  Trace("rfp-round-mv") << "RFP_ROUND terms : " << std::endl;
  for (const Node& a : xts)
  {
    Kind ak = a.getKind();
    if (ak != RFP_ROUND)
    {
      // don't care about other terms
      continue;
    }
    u_int32_t hash = a.getOperator().getConst<RfpRound>();
    d_terms[hash].push_back(a);
    Trace("rfp-round-mv") << "- " << a << std::endl;
  }
}

void RfpRoundSolver::checkInitialRefine()
{
  Trace("rfp-round-check") << "RfpRoundSolver::checkInitialRefine" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_terms)
  {
    // the reference bitwidth
    //unsigned k = is.first;
    for (const Node& i : is.second)
    {
      if (d_initRefine.find(i) != d_initRefine.end())
      {
        // already sent initial axioms for i in this user context
        continue;
      }
      d_initRefine.insert(i);
      //Node op = i.getOperator();
      //uint32_t bsize = op.getConst<IntAnd>().d_size;
      //Node twok = nm->mkConstInt(Rational(Integer(2).pow(bsize)));
      //Node arg0Mod = nm->mkNode(kind::INTS_MODULUS, i[0], twok);
      //Node arg1Mod = nm->mkNode(kind::INTS_MODULUS, i[1], twok);
      //// initial refinement lemmas
      //std::vector<Node> conj;
      //// iand(x,y)=iand(y,x) is guaranteed by rewriting
      //Assert(i[0] <= i[1]);
      //// conj.push_back(i.eqNode(nm->mkNode(IAND, op, i[1], i[0])));
      //// 0 <= iand(x,y) < 2^k
      //conj.push_back(nm->mkNode(LEQ, d_zero, i));
      //conj.push_back(nm->mkNode(LT, i, rewrite(d_iandUtils.twoToK(k))));
      //// iand(x,y)<=mod(x, 2^k)
      //conj.push_back(nm->mkNode(LEQ, i, arg0Mod));
      //// iand(x,y)<=mod(y, 2^k)
      //conj.push_back(nm->mkNode(LEQ, i, arg1Mod));
      //// x=y => iand(x,y)=mod(x, 2^k)
      //conj.push_back(nm->mkNode(IMPLIES, i[0].eqNode(i[1]), i.eqNode(arg0Mod)));
      //Node lem = conj.size() == 1 ? conj[0] : nm->mkNode(AND, conj);
      //Trace("iand-lemma") << "IAndSolver::Lemma: " << lem << " ; INIT_REFINE"
      //                    << std::endl;
      //d_im.addPendingLemma(lem, InferenceId::ARITH_NL_IAND_INIT_REFINE);

      Node op = i.getOperator();
      //uint32_t eb = op.getConst<RfpRound>().d_eb;
      //uint32_t sb = op.getConst<RfpRound>().d_sb;
      // L2-4 w/ same rm
      Node dbl = nm->mkNode(kind::RFP_ROUND, op, i[0], i);
      Node lem = nm->mkNode(EQUAL, dbl, i);
      Trace("rfp-round-lemma") << "RfpRoundSolver::Lemma: " << lem << " ; INIT_REFINE"
                               << std::endl;
      d_im.addPendingLemma(lem, InferenceId::ARITH_NL_RFP_ROUND_INIT_REFINE);
    }
  }
}

void RfpRoundSolver::checkFullRefine()
{
  Trace("rfp-round-check") << "RfpRoundSolver::checkFullRefine";
  Trace("rfp-round-check") << "RFP_ROUND terms: " << std::endl;
  for (const std::pair<const unsigned, std::vector<Node> >& is : d_terms)
  {
    // the reference bitwidth
    //unsigned k = is.first;
    for (const Node& i : is.second)
    {
      Node valRound = d_model.computeAbstractModelValue(i);
      Node valRoundC = d_model.computeConcreteModelValue(i);
      if (TraceIsOn("rfp-round-check"))
      {
        Node x = i[0];
        Node y = i[1];

        Node valX = d_model.computeConcreteModelValue(x);
        Node valY = d_model.computeConcreteModelValue(y);

        Trace("rfp-round-check") << "* " << i << ", value = " << valRound 
                                 << std::endl;
        Trace("rfp-round-check") << "  actual (" << valX << ", " << valY
                                 << ") = " << valRoundC << std::endl;
      }
      if (valRound == valRoundC)
      {
        Trace("rfp-round-check") << "...already correct" << std::endl;
        continue;
      }

      // ************* additional lemma schemas go here
      //// this is the most naive model-based schema based on model values
      //Node lem = valueBasedLemma(i);
      //Trace("iand-lemma")
      //    << "IAndSolver::Lemma: " << lem << " ; VALUE_REFINE" << std::endl;
      //// send the value lemma
      //d_im.addPendingLemma(lem,
      //                     InferenceId::ARITH_NL_IAND_VALUE_REFINE,
      //                     nullptr,
      //                     true);
    }
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
