/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for theory arithmetic.
 */

#include "theory/arith/theory_arith_type_rules.h"

#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

TypeNode ArithConstantTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ArithConstantTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  // we use different kinds for constant integers and reals
  if (n.getKind() == kind::CONST_RATIONAL)
  {
    // constant rationals are always real type, even if their value is integral
    return nodeManager->realType();
  }
  Assert(n.getKind() == kind::CONST_INTEGER);
  // constant integers should always have integral value
  if (check)
  {
    if (!n.getConst<Rational>().isIntegral())
    {
      throw TypeCheckingExceptionPrivate(
          n, "making an integer constant from a non-integral rational");
    }
  }
  return nodeManager->integerType();
}

TypeNode ArithRealAlgebraicNumberOpTypeRule::preComputeType(NodeManager* nm,
                                                            TNode n)
{
  return nm->realType();
}
TypeNode ArithRealAlgebraicNumberOpTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  return nodeManager->realType();
}
TypeNode ArithRealAlgebraicNumberTypeRule::preComputeType(NodeManager* nm,
                                                          TNode n)
{
  return nm->realType();
}
TypeNode ArithRealAlgebraicNumberTypeRule::computeType(NodeManager* nodeManager,
                                                       TNode n,
                                                       bool check,
                                                       std::ostream* errOut)
{
  return nodeManager->realType();
}

TypeNode ArithOperatorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ArithOperatorTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  TypeNode integerType = nodeManager->integerType();
  TypeNode realType = nodeManager->realType();
  TNode::iterator child_it = n.begin();
  TNode::iterator child_it_end = n.end();
  bool isInteger = true;
  Kind k = n.getKind();
  for (; child_it != child_it_end; ++child_it)
  {
    TypeNode childType = (*child_it).getType(check);
    if (!childType.isInteger())
    {
      isInteger = false;
      if (!check)
      {  // if we're not checking, nothing left to do
        break;
      }
    }
    if (check)
    {
      if (!childType.isRealOrInt())
      {
        throw TypeCheckingExceptionPrivate(n,
                                           "expecting an arithmetic subterm");
      }
      if (k == kind::TO_REAL && !childType.isInteger())
      {
        throw TypeCheckingExceptionPrivate(n, "expecting an integer subterm");
      }
    }
  }
  switch (k)
  {
    case kind::TO_REAL: return realType;
    case kind::TO_INTEGER: return integerType;
    default:
    {
      bool isDivision = k == kind::DIVISION || k == kind::DIVISION_TOTAL;
      return (isInteger && !isDivision ? integerType : realType);
    }
  }
}

TypeNode ArithRelationTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode ArithRelationTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  if (check)
  {
    Assert(n.getNumChildren() == 2);
    if (!n[0].getType(check).isRealOrInt()
        || !n[1].getType(check).isRealOrInt())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting an arithmetic term for arithmetic relation");
    }
  }
  return nodeManager->booleanType();
}

TypeNode RealNullaryOperatorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RealNullaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  // for nullary operators, we only computeType for check=true, since they are
  // given TypeAttr() on creation
  Assert(check);
  TypeNode realType = n.getType();
  if (realType != NodeManager::currentNM()->realType())
  {
    throw TypeCheckingExceptionPrivate(n, "expecting real type");
  }
  return realType;
}

TypeNode IAndTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode IAndTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check,
                                   std::ostream* errOut)
{
  if (n.getKind() != kind::IAND)
  {
    InternalError() << "IAND typerule invoked for " << n << " instead of IAND kind";
  }
  if (check)
  {
    TypeNode arg1 = n[0].getType(check);
    TypeNode arg2 = n[1].getType(check);
    if (!arg1.isInteger() || !arg2.isInteger())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting integer terms");
    }
  }
  return nodeManager->integerType();
}

TypeNode Pow2TypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode Pow2TypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check,
                                   std::ostream* errOut)
{
  if (n.getKind() != kind::POW2)
  {
    InternalError() << "POW2 typerule invoked for " << n << " instead of POW2 kind";
  }
  if (check)
  {
    TypeNode arg1 = n[0].getType(check);
    if (!arg1.isInteger())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting integer terms");
    }
  }
  return nodeManager->integerType();
}

TypeNode RfpUnOpTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->realType();
}
TypeNode RfpUnOpTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  if (n.getKind() != kind::RFP_ROUND && n.getKind() != kind::RFP_NEG)
  {
    InternalError() << "RFP_UN_OP typerule invoked for " << n << " instead of RFP_UN_OP kind";
  }
  if (check)
  {
    if (n.getKind() == kind::RFP_ROUND)
    {
      TypeNode rm = n[0].getType(check);
      if (!rm.isInteger())
        throw TypeCheckingExceptionPrivate(n, "expecting an integer (irm) term");
      TypeNode arg1 = n[1].getType(check);
      if (!arg1.isReal())
        throw TypeCheckingExceptionPrivate(n, "expecting a real term");
    }
    else
    {
      TypeNode arg1 = n[0].getType(check);
      if (!arg1.isReal())
        throw TypeCheckingExceptionPrivate(n, "expecting a real term");
    }
  }
  return nodeManager->realType();
}

TypeNode RfpBinOpTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->realType();
}
TypeNode RfpBinOpTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check,
                                       std::ostream* errOut)
{
  if (n.getKind() != kind::RFP_ADD && n.getKind() != kind::RFP_SUB && 
      n.getKind() != kind::RFP_MUL && n.getKind() != kind::RFP_DIV)
  {
    InternalError() << "RFP_BIN_OP typerule invoked for " << n << " instead of RFP_BIN_OP kind";
  }
  if (check)
  {
    TypeNode rm = n[0].getType(check);
    TypeNode arg1 = n[1].getType(check);
    TypeNode arg2 = n[2].getType(check);
    if (!rm.isInteger())
      throw TypeCheckingExceptionPrivate(n, "expecting an integer (irm) term");
    if (!arg1.isReal())
      throw TypeCheckingExceptionPrivate(n, "expecting a real term");
    if (!arg2.isReal())
      throw TypeCheckingExceptionPrivate(n, "expecting a real term");
  }
  return nodeManager->realType();
}

TypeNode RfpPropTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode RfpPropTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  if (n.getKind() != kind::RFP_IS_NORMAL && n.getKind() != kind::RFP_IS_SUBNORMAL && 
      n.getKind() != kind::RFP_IS_ZERO && n.getKind() != kind::RFP_IS_INFINITE && 
      n.getKind() != kind::RFP_IS_NAN &&
      n.getKind() != kind::RFP_IS_NEGATIVE && n.getKind() != kind::RFP_IS_POSITIVE)
  {
    InternalError() << "RFP_PROP typerule invoked for " << n << " instead of RFP_PROP kind";
  }
  if (check)
  {
    TypeNode arg1 = n[0].getType(check);
    if (!arg1.isReal())
      throw TypeCheckingExceptionPrivate(n, "expecting a real term");
  }
  return nodeManager->booleanType();
}

TypeNode RfpRelOpTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode RfpRelOpTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check,
                                       std::ostream* errOut)
{
  if (n.getKind() != kind::RFP_EQ && 
      n.getKind() != kind::RFP_LT && n.getKind() != kind::RFP_LE &&
      n.getKind() != kind::RFP_GT && n.getKind() != kind::RFP_GE)
  {
    InternalError() << "RFP_REL_OP typerule invoked for " << n << " instead of RFP_REL_OP kind";
  }
  if (check)
  {
    TypeNode arg1 = n[0].getType(check);
    TypeNode arg2 = n[1].getType(check);
    if (!arg1.isReal())
      throw TypeCheckingExceptionPrivate(n, "expecting a real term");
    if (!arg2.isReal())
      throw TypeCheckingExceptionPrivate(n, "expecting a real term");
  }
  return nodeManager->booleanType();
}

TypeNode IndexedRootPredicateTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode IndexedRootPredicateTypeRule::computeType(NodeManager* nodeManager,
                                                   TNode n,
                                                   bool check,
                                                   std::ostream* errOut)
{
  if (check)
  {
    TypeNode t1 = n[0].getType(check);
    if (!t1.isBoolean())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting boolean term as first argument");
    }
    TypeNode t2 = n[1].getType(check);
    if (!t2.isRealOrInt())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting polynomial as second argument");
    }
  }
  return nodeManager->booleanType();
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
