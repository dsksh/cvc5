/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of equality proof checker.
 */

#include "theory/uf/proof_checker.h"

#include "theory/uf/theory_uf_rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

void UfProofRuleChecker::registerTo(ProofChecker* pc)
{
  // add checkers
  pc->registerChecker(ProofRule::REFL, this);
  pc->registerChecker(ProofRule::SYMM, this);
  pc->registerChecker(ProofRule::TRANS, this);
  pc->registerChecker(ProofRule::CONG, this);
  pc->registerChecker(ProofRule::NARY_CONG, this);
  pc->registerChecker(ProofRule::TRUE_INTRO, this);
  pc->registerChecker(ProofRule::TRUE_ELIM, this);
  pc->registerChecker(ProofRule::FALSE_INTRO, this);
  pc->registerChecker(ProofRule::FALSE_ELIM, this);
  pc->registerChecker(ProofRule::HO_CONG, this);
  pc->registerChecker(ProofRule::HO_APP_ENCODE, this);
}

Node UfProofRuleChecker::checkInternal(ProofRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  // compute what was proven
  if (id == ProofRule::REFL)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return args[0].eqNode(args[0]);
  }
  else if (id == ProofRule::SYMM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    bool polarity = children[0].getKind() != Kind::NOT;
    Node eqp = polarity ? children[0] : children[0][0];
    if (eqp.getKind() != Kind::EQUAL)
    {
      // not a (dis)equality
      return Node::null();
    }
    Node conc = eqp[1].eqNode(eqp[0]);
    return polarity ? conc : conc.notNode();
  }
  else if (id == ProofRule::TRANS)
  {
    Assert(children.size() > 0);
    Assert(args.empty());
    Node first;
    Node curr;
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      Node eqp = children[i];
      if (eqp.getKind() != Kind::EQUAL)
      {
        return Node::null();
      }
      if (first.isNull())
      {
        first = eqp[0];
      }
      else if (eqp[0] != curr)
      {
        return Node::null();
      }
      curr = eqp[1];
    }
    return first.eqNode(curr);
  }
  else if (id == ProofRule::CONG || id == ProofRule::NARY_CONG)
  {
    Assert(children.size() > 0);
    Assert(args.size() >= 1 && args.size() <= 2);
    // We do congruence over builtin kinds using operatorToKind
    std::vector<Node> lchildren;
    std::vector<Node> rchildren;
    // get the kind encoded as args[0]
    Kind k;
    if (!getKind(args[0], k))
    {
      return Node::null();
    }
    // cannot use HO_APPLY
    if (k == Kind::UNDEFINED_KIND || k == Kind::HO_APPLY)
    {
      return Node::null();
    }
    Trace("uf-pfcheck") << "congruence for " << args[0] << " uses kind " << k
                        << ", metakind=" << kind::metaKindOf(k) << std::endl;
    if (args.size() == 2)
    {
      // parameterized kinds require the operator
      lchildren.push_back(args[1]);
      rchildren.push_back(args[1]);
    }
    else if (args.size() > 2)
    {
      return Node::null();
    }
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      Node eqp = children[i];
      if (eqp.getKind() != Kind::EQUAL)
      {
        return Node::null();
      }
      lchildren.push_back(eqp[0]);
      rchildren.push_back(eqp[1]);
    }
    NodeManager* nm = nodeManager();
    Node l = nm->mkNode(k, lchildren);
    Node r = nm->mkNode(k, rchildren);
    return l.eqNode(r);
  }
  else if (id == ProofRule::TRUE_INTRO)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node trueNode = nodeManager()->mkConst(true);
    return children[0].eqNode(trueNode);
  }
  else if (id == ProofRule::TRUE_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::EQUAL || !children[0][1].isConst()
        || !children[0][1].getConst<bool>())
    {
      return Node::null();
    }
    return children[0][0];
  }
  else if (id == ProofRule::FALSE_INTRO)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT)
    {
      return Node::null();
    }
    Node falseNode = nodeManager()->mkConst(false);
    return children[0][0].eqNode(falseNode);
  }
  else if (id == ProofRule::FALSE_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::EQUAL || !children[0][1].isConst()
        || children[0][1].getConst<bool>())
    {
      return Node::null();
    }
    return children[0][0].notNode();
  }
  if (id == ProofRule::HO_CONG)
  {
    Kind k;
    if (!getKind(args[0], k))
    {
      return Node::null();
    }
    std::vector<Node> lchildren;
    std::vector<Node> rchildren;
    for (size_t i = 0, nchild = children.size(); i < nchild; ++i)
    {
      Node eqp = children[i];
      if (eqp.getKind() != Kind::EQUAL)
      {
        return Node::null();
      }
      lchildren.push_back(eqp[0]);
      rchildren.push_back(eqp[1]);
    }
    NodeManager* nm = nodeManager();
    Node l = nm->mkNode(k, lchildren);
    Node r = nm->mkNode(k, rchildren);
    return l.eqNode(r);
  }
  else if (id == ProofRule::HO_APP_ENCODE)
  {
    Assert(args.size() == 1);
    Node ret = TheoryUfRewriter::getHoApplyForApplyUf(args[0]);
    return args[0].eqNode(ret);
  }
  // no rule
  return Node::null();
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
