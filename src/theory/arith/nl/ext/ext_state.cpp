/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common data shared by multiple checks.
 */

#include "theory/arith/nl/ext/ext_state.h"

#include <vector>

#include "expr/node.h"
#include "proof/proof.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/ext/monomial.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"
#include "util/rational.h"

// for rfp
#include "util/int_roundingmode.h"
#include "util/real_floatingpoint.h"
#include "theory/arith/nl/rfp_utils.h"
using namespace cvc5::internal::theory::arith::nl::RfpUtils;

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

ExtState::ExtState(Env& env, InferenceManager& im, NlModel& model)
    : EnvObj(env), d_im(im), d_model(model)
{
  d_false = nodeManager()->mkConst(false);
  d_true = nodeManager()->mkConst(true);
  d_zero = nodeManager()->mkConstInt(Rational(0));
  d_one = nodeManager()->mkConstInt(Rational(1));
  d_neg_one = nodeManager()->mkConstInt(Rational(-1));
  if (env.isTheoryProofProducing())
  {
    d_proof.reset(new CDProofSet<CDProof>(env, env.getUserContext(), "nl-ext"));
  }
}

void ExtState::init(const std::vector<Node>& xts)
{
  d_ms_vars.clear();
  d_ms.clear();
  d_mterms.clear();
  d_tplane_refine.clear();

  // for rfp
  d_ms_rounds.clear();
  d_ms_round_lits.clear();
  //d_ms_prune_vs.clear();
  Trace("rfp-mult-comp-debug3") << "clear" << std::endl;

  Trace("nl-ext-mv") << "Extended terms : " << std::endl;
  // for computing congruence
  std::map<Kind, ArgTrie> argTrie;
  for (unsigned i = 0, xsize = xts.size(); i < xsize; i++)
  {
    Node a = xts[i];
    d_model.computeConcreteModelValue(a);
    d_model.computeAbstractModelValue(a);
    d_model.printModelValue("nl-ext-mv", a);
    Kind ak = a.getKind();
    if (ak == Kind::NONLINEAR_MULT)
    {
      d_ms.push_back(a);

      // context-independent registration
      d_mdb.registerMonomial(a);

      const std::vector<Node>& varList = d_mdb.getVariableList(a);
      for (const Node& v : varList)
      {
        if (std::find(d_ms_vars.begin(), d_ms_vars.end(), v) == d_ms_vars.end())
        {
          d_ms_vars.push_back(v);
        }
      }
      // mark processed if has a "one" factor (will look at reduced monomial)?
    }

    // for rfp
    else if (a.getKind() == Kind::RFP_ROUND &&
             a[1].getKind() == Kind::NONLINEAR_MULT)
    {
      if (d_ms_rounds.find(a[1]) == d_ms_rounds.end())
      {
        Trace("rfp-mult-comp-debug3") << "register a round term: " << a << std::endl;
        d_ms_rounds[a[1]] = a;
      }
    }
  }

  // register constants
  d_mdb.registerMonomial(d_one);

  // register variables
  Trace("nl-ext-mv") << "Variables in monomials : " << std::endl;
  for (unsigned i = 0; i < d_ms_vars.size(); i++)
  {
    Node v = d_ms_vars[i];
    d_mdb.registerMonomial(v);
    d_model.computeConcreteModelValue(v);
    d_model.computeAbstractModelValue(v);
    d_model.printModelValue("nl-ext-mv", v);
  }

  Trace("nl-ext") << "We have " << d_ms.size() << " monomials." << std::endl;
}

bool ExtState::isProofEnabled() const { return d_proof.get() != nullptr; }

CDProof* ExtState::getProof()
{
  Assert(isProofEnabled());
  return d_proof->allocateProof(d_env.getUserContext());
}

// for rfp
void ExtState::checkRfpComp(Kind type, Node lhs, Node rhs, bool doWait)
{
  NodeManager* nm = NodeManager::currentNM();

  Node lit = nm->mkNode(type, lhs, rhs);
  lit = rewrite(lit);
  if (d_ms_round_lits.find(lit) != d_ms_round_lits.end()){ return; }
  d_ms_round_lits[lit] = true;

  std::map<Node, Node>::const_iterator it = d_ms_rounds.find(lhs);
  if (it != d_ms_rounds.end())
  {
    Node lhsRnd = it->second;
    Node rop = lhsRnd.getOperator();
    Node rhsRnd = nm->mkNode(Kind::RFP_ROUND, rop, lhsRnd[0], rhs);

    FloatingPointSize sz = rop.getConst<RfpRound>().getSize();
    uint32_t eb = sz.exponentWidth();
    uint32_t sb = sz.significandWidth();
    Node a1 = mkIsNan(eb,sb, lhsRnd).notNode();
    Node a2 = mkIsNan(eb,sb, rhsRnd).notNode();

    if (type == Kind::GEQ || type == Kind::LEQ || type == Kind::EQUAL)
    {
      Node assumption = a1.andNode(a2).andNode(lit);

      Node inferRnd = nm->mkNode(type, lhsRnd, rhsRnd);
      Node lemma = assumption.impNode(inferRnd);
      Trace("rfp-mult-comp-lemma") << "RfpCompCheck::Lemma: " << lemma
                                   << std::endl;
      d_im.addPendingLemma(lemma,
                           InferenceId::ARITH_NL_RFP_MULT_COMP, nullptr, doWait);
    }
    else if (type == Kind::GT || type == Kind::LT)
    {
      Node a3 = nm->mkNode(type, lhsRnd, rhsRnd);
      Node assumption = a1.andNode(a2).andNode(a3);

      Node infer1 = nm->mkNode(type, lhsRnd, rhs);
      Node infer2 = nm->mkNode(type, lhs, rhsRnd);
      Node lemma = assumption.impNode(infer1.andNode(infer2));
      Trace("rfp-mult-comp-lemma") << "RfpCompCheck::Lemma: " << lemma
                                   << std::endl;
      d_im.addPendingLemma(lemma,
                           InferenceId::ARITH_NL_RFP_MULT_COMP, nullptr, doWait);
    }
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
