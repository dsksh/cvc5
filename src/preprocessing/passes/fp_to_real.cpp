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
 * The implementation of FPToReal.
 */

#include "preprocessing/passes/fp_to_real.h"

#include <cmath>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"
#include "util/floatingpoint.h"
#include "util/real_floatingpoint.h"
#include "util/int_roundingmode.h"
#include "theory/arith/nl/rfp_utils.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;

namespace RFP = cvc5::internal::RealFloatingPoint;
using namespace cvc5::internal::theory::arith::nl::RfpUtils;

FPToReal::FPToReal(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "fp-to-real"), 
      d_realblastCache(userContext()),
      d_rangeAssertions(userContext())
{
  d_nm = NodeManager::currentNM();
  d_zero = d_nm->mkConstReal(0);
  d_one = d_nm->mkConstReal(1);
}

Node FPToReal::realBlast(Node n,
                         std::vector<Node>& lemmas,
                         std::map<Node, Node>& skolems)
{
  // make sure the node is re-written
  n = rewrite(n);

  // helper vector for traversal.
  std::vector<Node> toVisit;
  toVisit.push_back(n);

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    Trace("fp-to-real") << "current: " << current << std::endl;
    uint64_t currentNumChildren = current.getNumChildren();
    if (d_realblastCache.find(current) == d_realblastCache.end())
    {
      Trace("fp-to-real") << "Cached." << endl;

      // This is the first time we visit this node and it is not in the cache.
      // We mark this node as visited but not translated by assiging
      // a null node to it.
      d_realblastCache[current] = Node();
      // all the node's children are added to the stack to be visited
      // before visiting this node again.
      for (const Node& child : current)
      {
        toVisit.push_back(child);
      }
      // If this is a UF application, we also add the function to
      // toVisit.
      if (current.getKind() == kind::APPLY_UF)
      {
        toVisit.push_back(current.getOperator());
      }
    }
    else
    {
      // We already visited and translated this node
      if (!d_realblastCache[current].get().isNull())
      {
        // We are done computing the translation for current
        toVisit.pop_back();
      }
      else
      {
        // We are now visiting current on the way back up.
        // This is when we do the actual translation.
        Node translation;
        if (currentNumChildren == 0)
        {
          Trace("fp-to-real") << "No children." << endl;

          translation = translateNoChildren(current, lemmas, skolems);
        }
        else
        {
          Trace("fp-to-real") << "With children." << endl;

          /**
           * The current node has children.
           * Since we are on the way back up,
           * these children were already translated.
           * We save their translation for easy access.
           * If the node's kind is APPLY_UF,
           * we also need to include the translated uninterpreted function in
           * this list.
           */
          std::vector<Node> translated_children;
          if (current.getKind() == kind::APPLY_UF)
          {
            Assert(d_realblastCache.find(current.getOperator())
                   != d_realblastCache.end());
            translated_children.push_back(
                d_realblastCache[current.getOperator()]);
          }
          for (const Node& cc : current)
          {
            Assert(d_realblastCache.find(cc) != d_realblastCache.end());
            translated_children.push_back(d_realblastCache[cc]);
          }
          translation =
              translateWithChildren(current, translated_children, lemmas);
        }
        Assert(!translation.isNull());
        // Map the current node to its translation in the cache.
        d_realblastCache[current] = translation;
        // Also map the translation to itself.
        d_realblastCache[translation] = translation;
        toVisit.pop_back();
      }
    }
  }
  Assert(d_realblastCache.find(n) != d_realblastCache.end());
  return d_realblastCache[n].get();
}

PreprocessingPassResult FPToReal::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::vector<Node> additionalConstraints;
  std::map<Node, Node> skolems;
  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Node origNode = (*assertionsToPreprocess)[i];
    //Node newNode = d_nm->mkNode(kind::LT, d_zero, d_one);
    Node newNode = realBlast(origNode, additionalConstraints, skolems);
    Node rwNode = rewrite(newNode);
    Trace("fp-to-real") << "orig node: " << origNode << std::endl;
    Trace("fp-to-real") << "new node: " << newNode << std::endl;
    Trace("fp-to-real") << "rw node: " << rwNode << std::endl;
    assertionsToPreprocess->replace(i, rwNode);
  }
  addFinalizeAssertions(assertionsToPreprocess, additionalConstraints);
  addSkolemDefinitions(skolems);
  return PreprocessingPassResult::NO_CONFLICT;
}

void FPToReal::addFPRangeConstraint(Node node,
                                    uint32_t eb,
                                    uint32_t sb,
                                    std::vector<Node>& lemmas)
{
  // TODO
  Node constr = mkIsRounded(eb,sb, node);
  if (d_rangeAssertions.find(constr) == d_rangeAssertions.end())
  {
    Trace("fp-to-real") << "range constraint computed: " << constr 
                        << std::endl;
    d_rangeAssertions.insert(constr);
    lemmas.push_back(constr);
  }
}

void FPToReal::addRMRangeConstraint(Node node,
                                    std::vector<Node>& lemmas)
{
  Node lower = d_nm->mkNode(kind::LEQ, d_nm->mkConstInt(0), node);
  Node upper = d_nm->mkNode(kind::LEQ, node, d_nm->mkConstInt(4));
  Node constr = d_nm->mkNode(kind::AND, lower, upper);
  if (d_rangeAssertions.find(constr) == d_rangeAssertions.end())
  {
    Trace("fp-to-real") << "range constraint computed: " << constr 
                        << std::endl;
    d_rangeAssertions.insert(constr);
    lemmas.push_back(constr);
  }
}

Node FPToReal::translateWithChildren(
    Node original,
    const std::vector<Node>& translated_children,
    std::vector<Node>& lemmas)
{
  Trace("fp-to-real") << original << endl;

  // The translation of the original node is determined by the kind of
  // the node.
  kind::Kind_t newKind;
  switch (original.getKind())
  {
    //case kind::FLOATINGPOINT_IS_NORMAL:
    //  newKind = kind::RFP_IS_NORMAL; 
    //  break;
    //case kind::FLOATINGPOINT_IS_SUBNORMAL:
    //  newKind = kind::RFP_IS_SUBNORMAL;
    //  break;
    //case kind::FLOATINGPOINT_IS_ZERO:
    //  newKind = kind::RFP_IS_ZERO; 
    //  break;
    //case kind::FLOATINGPOINT_IS_INF:
    //  newKind = kind::RFP_IS_INF; 
    //  break;
    //case kind::FLOATINGPOINT_IS_NAN:
    //  newKind = kind::RFP_IS_NAN; 
    //  break;
    //case kind::FLOATINGPOINT_IS_NEG:
    //  newKind = kind::RFP_IS_NEG; 
    //  break;
    //case kind::FLOATINGPOINT_IS_POS:
    //  newKind = kind::RFP_IS_POS; 
    //  break;
    case kind::FLOATINGPOINT_TO_FP_FROM_FP:
      newKind = kind::RFP_TO_RFP_FROM_RFP; 
      break;
    case kind::FLOATINGPOINT_TO_FP_FROM_REAL:
      newKind = kind::RFP_ROUND; 
      break;
    case kind::FLOATINGPOINT_ADD:
      newKind = kind::RFP_ADD; 
      break;
    case kind::FLOATINGPOINT_SUB:
      newKind = kind::RFP_SUB; 
      break;
    case kind::FLOATINGPOINT_NEG:
      newKind = kind::RFP_NEG; 
      break;
    case kind::FLOATINGPOINT_MULT:
      newKind = kind::RFP_MULT; 
      break;
    case kind::FLOATINGPOINT_DIV:
      newKind = kind::RFP_DIV; 
      break;
    case kind::FLOATINGPOINT_EQ:
      newKind = kind::RFP_EQ; 
      break;
    case kind::FLOATINGPOINT_LT:
      newKind = kind::RFP_LT; 
      break;
    case kind::FLOATINGPOINT_LEQ:
      newKind = kind::RFP_LEQ; 
      break;
    case kind::FLOATINGPOINT_GT:
      newKind = kind::RFP_GT; 
      break;
    case kind::FLOATINGPOINT_GEQ:
      newKind = kind::RFP_GEQ; 
      break;
    default:
      newKind = original.getKind();
  }

  // Store the translated node
  Node returnNode;

  ///**
  // * higher order logic allows comparing between functions
  // * The translation does not support this,
  // * as the translated functions may be different outside
  // * of the bounds that were relevant for the original
  // * bit-vectors.
  // */
  //if (childrenTypesChanged(original) && logicInfo().isHigherOrder())
  //{
  //  throw OptionException("bv-to-int does not support higher order logic ");
  //}

  // Translate according to the kind of the original node.
  switch (newKind)
  {
    case kind::FLOATINGPOINT_IS_NORMAL:
    case kind::FLOATINGPOINT_IS_SUBNORMAL:
    case kind::FLOATINGPOINT_IS_ZERO:
    case kind::FLOATINGPOINT_IS_INF:
    case kind::FLOATINGPOINT_IS_NAN:
    case kind::FLOATINGPOINT_IS_NEG:
    case kind::FLOATINGPOINT_IS_POS:
    {
      Assert(original.getNumChildren() == 1);
      uint32_t eb = original[0].getType().getFloatingPointExponentSize();
      uint32_t sb = original[0].getType().getFloatingPointSignificandSize();
      returnNode = createPropertyNode(newKind, eb, sb, translated_children[0]);
      break;
    }
    case kind::FLOATINGPOINT_TO_REAL:
    case kind::FLOATINGPOINT_TO_REAL_TOTAL:
    {
      Assert(original.getNumChildren() == 1);
      uint32_t eb = original[0].getType().getFloatingPointExponentSize();
      uint32_t sb = original[0].getType().getFloatingPointSignificandSize();
      Node op = d_nm->mkConst(RfpToReal(eb, sb));
      returnNode = d_nm->mkNode(kind::RFP_TO_REAL, op, translated_children[0]);
      break;
    }
    case kind::RFP_TO_RFP_FROM_RFP:
    {
      Assert(original.getNumChildren() == 2);
      uint32_t eb0 = original[1].getType().getFloatingPointExponentSize();
      uint32_t sb0 = original[1].getType().getFloatingPointSignificandSize();
      uint32_t eb = original.getType().getFloatingPointExponentSize();
      uint32_t sb = original.getType().getFloatingPointSignificandSize();
      Node op = d_nm->mkConst(RfpToRfpFromRfp(eb0, sb0, eb, sb));
      returnNode = d_nm->mkNode(newKind, op, translated_children[0], translated_children[1]);
      break;
    }
    case kind::RFP_ROUND:
    {
      Assert(original.getNumChildren() == 2);
      uint32_t eb = original.getType().getFloatingPointExponentSize();
      uint32_t sb = original.getType().getFloatingPointSignificandSize();
      Node op = createFPOperator(newKind, eb, sb);
      returnNode = d_nm->mkNode(newKind, op, translated_children[0], translated_children[1]);
      break;
    }
    case kind::RFP_NEG:
    {
      Assert(original.getNumChildren() == 1);
      uint32_t eb = original.getType().getFloatingPointExponentSize();
      uint32_t sb = original.getType().getFloatingPointSignificandSize();
      Node op = createFPOperator(newKind, eb, sb);
      returnNode = d_nm->mkNode(newKind, op, translated_children[0]);
      break;
    }
    case kind::RFP_ADD:
    case kind::RFP_SUB:
    case kind::RFP_MULT:
    case kind::RFP_DIV:
    {
      Assert(original.getNumChildren() == 3);
      uint32_t eb = original.getType().getFloatingPointExponentSize();
      uint32_t sb = original.getType().getFloatingPointSignificandSize();
      Node op = createFPOperator(newKind, eb, sb);
      returnNode = d_nm->mkNode(newKind, op, translated_children[0], 
        translated_children[1], translated_children[2]);
      break;
    }
    //case kind::RFP_IS_NORMAL:
    //case kind::RFP_IS_SUBNORMAL:
    //case kind::RFP_IS_ZERO:
    //case kind::RFP_IS_INF:
    //case kind::RFP_IS_NAN:
    //case kind::RFP_IS_NEG:
    //case kind::RFP_IS_POS:
    //{
    //  Assert(original.getNumChildren() == 1);
    //  uint32_t eb = original[0].getType().getFloatingPointExponentSize();
    //  uint32_t sb = original[0].getType().getFloatingPointSignificandSize();
    //  Node op = createFPOperator(newKind, eb, sb);
    //  returnNode = d_nm->mkNode(newKind, op, translated_children[0]);
    //  break;
    //}
    case kind::RFP_EQ:
    case kind::RFP_LT:
    case kind::RFP_LEQ:
    case kind::RFP_GT:
    case kind::RFP_GEQ:
    {
      Assert(original.getNumChildren() == 2);
      uint32_t eb = original[0].getType().getFloatingPointExponentSize();
      uint32_t sb = original[0].getType().getFloatingPointSignificandSize();
      Node op = createFPOperator(newKind, eb, sb);
      Node rel = d_nm->mkNode(newKind, op, 
        translated_children[0], translated_children[1]);

      //Node intZero = d_nm->mkConstInt(0);
      //returnNode = d_nm->mkNode(kind::NOT, d_nm->mkNode(kind::EQUAL, rel, intZero));
      //// TODO
      //Node intOne = d_nm->mkConstInt(1);
      //returnNode = d_nm->mkNode(kind::EQUAL, rel, intOne);
      returnNode = mkTrue(rel);

      // TODO: range constraint
      //Node lb = d_nm->mkNode(kind::LEQ, d_nm->mkConstInt(0), rel);
      //Node ub = d_nm->mkNode(kind::LEQ, rel, d_nm->mkConstInt(1));
      //Node rangeConstraint = d_nm->mkNode(kind::AND, lb, ub);
      //lemmas.push_back(rangeConstraint);
      lemmas.push_back(mkBoolIntConstraint(rel));

      break;
    }
    case kind::EQUAL:
    {
      returnNode = d_nm->mkNode(kind::EQUAL, translated_children);
      break;
    }
    default:
    {
      Trace("fp-to-real") << "Unsupported kind: " << newKind << endl;

      // first, verify that we haven't missed
      // any bv operator
      Assert(theory::kindToTheoryId(newKind) != THEORY_FP);

      // In the default case, we have reached an operator that we do not
      // translate directly to reals. The children whose types have
      // changed from fp to real should be adjusted back to fp and then
      // this term is reconstructed.
      TypeNode resultingType;
      if (original.getType().isFloatingPoint())
      {
        resultingType = d_nm->realType();
      }
      else
      {
        resultingType = original.getType();
      }
      Node reconstruction =
          reconstructNode(original, resultingType, translated_children);
      returnNode = reconstruction;
      break;
    }
  }

  Trace("fp-to-real") << "original: " << original << std::endl;
  Trace("fp-to-real") << "returnNode: " << returnNode << std::endl;
  return returnNode;
}

Node FPToReal::translateNoChildren(Node original,
                                   std::vector<Node>& lemmas,
                                   std::map<Node, Node>& skolems)
{
  Trace("fp-to-real")
      << "translating leaf: " << original << "; of type: " << original.getType()
      << std::endl;
  // The result of the translation
  Node translation;

  // The translation is done differently for variables (bound or free)  and
  // constants (values)
  if (original.isVar())
  {
    if (original.getType().isFloatingPoint())
    {
      // For fp variables, we create fresh real variables.
      if (original.getKind() == kind::BOUND_VARIABLE)
      {
        // Range constraints for the bound real variables are not added now.
        // they will be added once the quantifier itself is handled.
        // TO_CHECK
        std::stringstream ss;
        ss << original;
        translation = d_nm->mkBoundVar(ss.str() + "_real", d_nm->realType());
      }
      else
      {
        Node realCast = castToType(original, d_nm->realType());
        Node fpCast;
        // we introduce a fresh variable, add range constraints, and save the
        // connection between original and the new variable via realCast
        translation = d_nm->getSkolemManager()->mkPurifySkolem(realCast);
        Trace("fp-to-real") << "addRC for " << translation << std::endl;
        uint32_t eb = original.getType().getFloatingPointExponentSize();
        uint32_t sb = original.getType().getFloatingPointSignificandSize();
        addFPRangeConstraint(translation, eb, sb, lemmas);
        // put new definition of old variable in skolems
        fpCast = castToType(translation, original.getType());

        // add fpCast to skolems if it is not already there.
        if (skolems.find(original) == skolems.end())
        {
          skolems[original] = fpCast;
        }
        else
        {
          Assert(skolems[original] == fpCast);
        }
      }
    }
    else if (original.getType().isRoundingMode())
    {
      // For rm variables, we create fresh int variables.
      if (original.getKind() == kind::BOUND_VARIABLE)
      {
        // Range constraints for the bound integer variables are not added now.
        // they will be added once the quantifier itself is handled.
        // TO_CHECK
        std::stringstream ss;
        ss << original;
        translation = d_nm->mkBoundVar(ss.str() + "_int", d_nm->integerType());
      }
      else
      {
        Node intCast = castToType(original, d_nm->integerType());
        Node rmCast;
        // we introduce a fresh variable, add range constraints, and save the
        // connection between original and the new variable via intCast
        translation = d_nm->getSkolemManager()->mkPurifySkolem(intCast);
        addRMRangeConstraint(translation, lemmas);
        // put new definition of old variable in skolems
        rmCast = castToType(translation, original.getType());

        // add rmCast to skolems if it is not already there.
        if (skolems.find(original) == skolems.end())
        {
          skolems[original] = rmCast;
        }
        else
        {
          Assert(skolems[original] == rmCast);
        }
      }
    }
    //// TODO
    //else if (original.getType().isFunction())
    //{
    //  // translate function symbol
    //  translation = translateFunctionSymbol(original, skolems);
    //}
    else
    {
      // leave other variables intact
      translation = original;
    }
  }
  else // Constants.
  {
    // original is a constant (value) or an operator with no arguments (e.g., PI)
    if (original.getKind() == kind::CONST_FLOATINGPOINT)
    {
      // Floating-point constants are transformed into their real value.
      FloatingPoint constant(original.getConst<FloatingPoint>());
      //Rational r = constant.convertToRationalTotal(Rational(0));
      Rational r = RFP::convertFPToReal(constant);
      translation = d_nm->mkConstReal(r);
    }
    else if (original.getKind() == kind::CONST_ROUNDINGMODE)
    {
      // Roung-mode constants are transformed into their int value.
      RoundingMode constant(original.getConst<RoundingMode>());
      Integer i = IntRoundingMode::convert(constant);
      translation = d_nm->mkConstInt(i);
    }
    else
    {
      // Other constants or operators stay the same.
      translation = original;
    }
  }
  Trace("fp-to-real") << "translation: " << translation << std::endl;
  return translation;
}

Node FPToReal::castToType(Node n, TypeNode tn)
{
  // If there is no reason to cast, return the original node.
  if (n.getType() == tn)
  {
    return n;
  }
  // We only case between real and fp or between int and rm.
  Assert((n.getType().isFloatingPoint() && tn.isReal()) ||
         (n.getType().isReal() && tn.isFloatingPoint()) ||
         (n.getType().isInteger() && tn.isRoundingMode()) ||
         (n.getType().isRoundingMode() && tn.isInteger()));
  Trace("fp-to-real") << "castToType from " << n.getType() << " to " << tn
                      << std::endl;

  if (n.getType().isReal())
  {
    // Casting reals to FP numbers.
    Assert(tn.isFloatingPoint());
    Node op = d_nm->mkConst(RfpToFP(tn.getConst<FloatingPointSize>()));
    return d_nm->mkNode(kind::RFP_TO_FP, op, n);
    //Node op = d_nm->mkConst(FloatingPointToFPReal(tn.getConst<FloatingPointSize>()));
    //Node rm = d_nm->mkConst(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
    //return d_nm->mkNode(kind::FLOATINGPOINT_TO_FP_FROM_REAL, op, rm, n);
  }
  else if (n.getType().isFloatingPoint())
  {
    // Casting FP numbers to reals.
    Assert(tn.isReal());
    return d_nm->mkNode(kind::FP_TO_RFP, n);
  }
  else if (n.getType().isInteger())
  {
    // Casting integers to RMs.
    Assert(tn.isRoundingMode());
    return d_nm->mkNode(kind::IRM_TO_RM, n);
  }
  else
  {
    // Casting RMs to integers.
    Assert(n.getType().isRoundingMode());
    Assert(tn.isInteger());
    return d_nm->mkNode(kind::IRM_TO_INT, n);
  }
}

Node FPToReal::reconstructNode(Node originalNode,
                                 TypeNode resultType,
                                 const std::vector<Node>& translated_children)
{
  // first, we adjust the children of the node as needed.
  // re-construct the term with the adjusted children.
  kind::Kind_t oldKind = originalNode.getKind();
  NodeBuilder builder(oldKind);
  if (originalNode.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << originalNode.getOperator();
  }
  for (uint32_t i = 0; i < originalNode.getNumChildren(); i++)
  {
    Node originalChild = originalNode[i];
    Node translatedChild = translated_children[i];
    Node adjustedChild = castToType(translatedChild, originalChild.getType());
    builder << adjustedChild;
  }
  Node reconstruction = builder.constructNode();
  // cast to tn in case the reconstruction is an FP or RM term.
  reconstruction = castToType(reconstruction, resultType);
  return reconstruction;
}

Node FPToReal::createPropertyNode(kind::Kind_t pKind, uint32_t eb, uint32_t sb, TNode node)
{
  switch (pKind)
  {
    case kind::FLOATINGPOINT_IS_NORMAL:
      return mkIsNormal(eb,sb, node);
    case kind::FLOATINGPOINT_IS_SUBNORMAL:
      return mkIsSubnormal(eb,sb, node);
    case kind::FLOATINGPOINT_IS_ZERO:
      return mkIsZero(eb,sb, node);
    case kind::FLOATINGPOINT_IS_INF:
      return mkIsInf(eb,sb, node);
    case kind::FLOATINGPOINT_IS_NAN:
      return mkIsNan(eb,sb, node);
    case kind::FLOATINGPOINT_IS_NEG:
      return mkIsNeg(eb,sb, node);
    case kind::FLOATINGPOINT_IS_POS:
      return mkIsPos(eb,sb, node);
  }
}

Node FPToReal::createFPOperator(kind::Kind_t rfpKind, uint32_t eb, uint32_t sb)
{
  switch (rfpKind)
  {
    case kind::RFP_TO_REAL:
      return d_nm->mkConst(RfpToReal(eb, sb));
    case kind::RFP_IS_NORMAL:
      return d_nm->mkConst(RfpIsNormal(eb, sb));
    case kind::RFP_IS_SUBNORMAL:
      return d_nm->mkConst(RfpIsSubnormal(eb, sb));
    case kind::RFP_IS_ZERO:
      return d_nm->mkConst(RfpIsZero(eb, sb));
    case kind::RFP_IS_INF:
      return d_nm->mkConst(RfpIsInf(eb, sb));
    case kind::RFP_IS_NAN:
      return d_nm->mkConst(RfpIsNan(eb, sb));
    case kind::RFP_IS_NEG:
      return d_nm->mkConst(RfpIsNeg(eb, sb));
    case kind::RFP_IS_POS:
      return d_nm->mkConst(RfpIsPos(eb, sb));
    case kind::RFP_ROUND:
      return d_nm->mkConst(RfpRound(eb, sb));
    case kind::RFP_ADD:
      return d_nm->mkConst(RfpAdd(eb, sb));
    case kind::RFP_SUB:
      return d_nm->mkConst(RfpSub(eb, sb));
    case kind::RFP_NEG:
      return d_nm->mkConst(RfpNeg(eb, sb));
    case kind::RFP_MULT:
      return d_nm->mkConst(RfpMult(eb, sb));
    case kind::RFP_DIV:
      return d_nm->mkConst(RfpDiv(eb, sb));
    case kind::RFP_EQ:
      return d_nm->mkConst(RfpEq(eb, sb));
    case kind::RFP_LT:
      return d_nm->mkConst(RfpLt(eb, sb));
    case kind::RFP_LEQ:
      return d_nm->mkConst(RfpLeq(eb, sb));
    case kind::RFP_GT:
      return d_nm->mkConst(RfpGt(eb, sb));
    case kind::RFP_GEQ:
      return d_nm->mkConst(RfpGeq(eb, sb));
    default:
      Assert(false);
  }
}

void FPToReal::addFinalizeAssertions(
    AssertionPipeline* assertionsToPreprocess,
    const std::vector<Node>& additionalConstraints)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lemmas = nm->mkAnd(additionalConstraints);
  assertionsToPreprocess->push_back(lemmas);
  Trace("fp-to-real-debug") << "range constraints: " << lemmas.toString()
                            << std::endl;
}

void FPToReal::addSkolemDefinitions(const std::map<Node, Node>& skolems)
{
  map<Node, Node>::const_iterator it;
  for (it = skolems.begin(); it != skolems.end(); it++)
  {
    Node originalSkolem = it->first;
    Node definition = it->second;
    std::vector<Node> args;
    Node body;
    if (definition.getType().isFunction())
    {
      args.insert(args.end(), definition[0].begin(), definition[0].end());
      body = definition[1];
    }
    else
    {
      body = definition;
    }
    Trace("fp-to-real-debug") << "adding substitution: " << "[" << originalSkolem  << "] ----> [" << definition << "]"  << std::endl; 
    d_preprocContext->addSubstitution(originalSkolem, definition);
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
