#include "preprocessing/passes/test_pp.h"

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
#include "util/rational.h"
#include "util/t_add.h"
#include "util/t_pow.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;

TestPp::TestPp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "test-pass"), 
      d_binarizeCache(userContext()),
      d_realblastCache(userContext())
{
  d_nm = NodeManager::currentNM();
  d_zero = d_nm->mkConstInt(0);
  d_one = d_nm->mkConstInt(1);
}

Node TestPp::cacheNode(Node n)
{
  Trace("test-pp") << "cacheNode: " << n << std::endl;

  if (d_binarizeCache.find(n) != d_binarizeCache.end())
  {
    return d_binarizeCache[n];
  }
  else
  {
    d_binarizeCache[n] = n;
    return n;
  }
}

Node TestPp::realBlast(Node n,
                         std::vector<Node>& lemmas,
                         std::map<Node, Node>& skolems)
{
  // make sure the node is re-written
  n = rewrite(n);

  // helper vector for traversal.
  std::vector<Node> toVisit;
  toVisit.push_back(cacheNode(n));

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    Trace("test-pp") << "current: " << current << std::endl;
    uint64_t currentNumChildren = current.getNumChildren();
    if (d_realblastCache.find(current) == d_realblastCache.end())
    {
      Trace("test-pp") << "Cached." << endl;

      // This is the first time we visit this node and it is not in the cache.
      // We mark this node as visited but not translated by assiging
      // a null node to it.
      d_realblastCache[current] = Node();
      // all the node's children are added to the stack to be visited
      // before visiting this node again.
      for (const Node& child : current)
      {
        toVisit.push_back(cacheNode(child));
      }
      // If this is a UF applicatinon, we also add the function to
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
          Trace("test-pp") << "No children." << endl;

          translation = translateNoChildren(current, lemmas, skolems);
        }
        else
        {
          Trace("test-pp") << "With children." << endl;

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
            Node ccb = cacheNode(cc);
            Assert(d_realblastCache.find(ccb) != d_realblastCache.end());
            translated_children.push_back(d_realblastCache[ccb]);
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

PreprocessingPassResult TestPp::applyInternal(
      AssertionPipeline* assertionsToPreprocess)
{
  std::vector<Node> additionalConstraints;
  std::map<Node, Node> skolems;
  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Node origNode = (*assertionsToPreprocess)[i];
    Node newNode = realBlast(origNode, additionalConstraints, skolems);
    Node rwNode = rewrite(newNode);
    Trace("test-pp") << "orig node: " << origNode << std::endl;
    Trace("test-pp") << "new node: " << newNode << std::endl;
    Trace("test-pp") << "rw node: " << rwNode << std::endl;
    assertionsToPreprocess->replace(i, rwNode);
  }
  //addFinalizeAssertions(assertionsToPreprocess, additionalConstraints);
  //addSkolemDefinitions(skolems);
  return PreprocessingPassResult::NO_CONFLICT;
}

//void TestPp::addRangeConstraint(Node node, uint32_t esz,
//                                  uint32_t ssz,
//                                  std::vector<Node>& lemmas)
//{
//  Node rangeConstraint = mkRangeConstraint(node);
//  Trace("test-pp")
//      << "range constraint computed: " << rangeConstraint << std::endl;
//  if (d_rangeAssertions.find(rangeConstraint) == d_rangeAssertions.end())
//  {
//    Trace("test-pp")
//        << "range constraint added to cache and lemmas " << std::endl;
//    d_rangeAssertions.insert(rangeConstraint);
//    lemmas.push_back(rangeConstraint);
//  }
//}

//Node TestPp::mkRangeConstraint(Node newVar)
//{
//  //Node lower = d_nm->mkNode(kind::LEQ, d_zero, newVar);
//  //Node upper = d_nm->mkNode(kind::LT, newVar, d_one);
//  Node lower = d_nm->mkNode(kind::LEQ, d_nm->mkConstReal(-100), newVar);
//  Node upper = d_nm->mkNode(kind::LT, newVar, d_nm->mkConstReal(100));
//  Node result = d_nm->mkNode(kind::AND, lower, upper);
//  return rewrite(result);
//}

Node TestPp::reconstructNode(Node originalNode,
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
    //Node adjustedChild = castToType(translatedChild, originalChild.getType());
    //builder << adjustedChild;
    builder << translatedChild;
  }
  Node reconstruction = builder.constructNode();
  //// cast to tn in case the reconstruction is a bit-vector.
  //reconstruction = castToType(reconstruction, resultType);
  return reconstruction;
}

Node TestPp::translateWithChildren(
    Node original,
    const std::vector<Node>& translated_children,
    std::vector<Node>& lemmas)
{
  Trace("test-pp") << original << endl;

  // The translation of the original node is determined by the kind of
  // the node.
  kind::Kind_t oldKind = original.getKind();

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
  switch (oldKind)
  {
    case kind::T_ID:
    {
      Trace("test-pp") << "detect t.id: " << original.getNumChildren() << endl;
      Assert(original.getNumChildren() == 1);
      returnNode = translated_children[0];
      break;
    }
    case kind::T_ADD:
    {
      Trace("test-pp") << "detect t.add: " << original.getNumChildren() << endl;
      Assert(original.getNumChildren() == 1);
      Node x = d_nm->mkConstReal( original.getOperator().getConst<internal::TAdd>().d_arg );
      Node y = translated_children[0];
      returnNode = d_nm->mkNode(kind::ADD, x, y);
      break;
    }
    case kind::T_POW:
    {
      Trace("test-pp") << "detect t.pow: " << original.getNumChildren() << endl;
      returnNode = original;
      break;
    }

    //case kind::FLOATINGPOINT_MULT:
    //{
    //  Trace("test-pp") << original.getNumChildren() << endl;
    //  Assert(original.getNumChildren() == 3);

    //  //uint32_t bvsize = original[0].getType().getBitVectorSize();
    //  //returnNode = createBVAddNode(
    //  //    translated_children[0], translated_children[1], bvsize);

    //  uint32_t esz = original.getType().getFloatingPointExponentSize();
    //  uint32_t ssz = original.getType().getFloatingPointSignificandSize();
    //  returnNode = createFPMultNode(
    //      translated_children[0], translated_children[1], translated_children[2], esz, ssz);

    //  break;
    //}
    //case kind::BITVECTOR_MULT:
    //{
    //  Assert(original.getNumChildren() == 2);
    //  uint32_t bvsize = original[0].getType().getBitVectorSize();
    //  Node mult = d_nm->mkNode(kind::MULT, translated_children);
    //  Node p2 = pow2(bvsize);
    //  returnNode = d_nm->mkNode(kind::INTS_MODULUS_TOTAL, mult, p2);
    //  break;
    //}
    //case kind::BITVECTOR_UDIV:
    //{
    //  // we use an ITE for the case where the second operand is 0.
    //  uint32_t bvsize = original[0].getType().getBitVectorSize();
    //  Node pow2BvSize = pow2(bvsize);
    //  Node divNode =
    //      d_nm->mkNode(kind::INTS_DIVISION_TOTAL, translated_children);
    //  returnNode = d_nm->mkNode(
    //      kind::ITE,
    //      d_nm->mkNode(kind::EQUAL, translated_children[1], d_zero),
    //      d_nm->mkNode(kind::SUB, pow2BvSize, d_one),
    //      divNode);
    //  break;
    //}
    //case kind::EQUAL:
    //{
    //  returnNode = d_nm->mkNode(kind::EQUAL, translated_children);
    //  break;
    //}
    default:
    {
      // first, verify that we haven't missed
      // any bv operator
      Assert(theory::kindToTheoryId(oldKind) != THEORY_BV);

      // In the default case, we have reached an operator that we do not
      // translate directly to integers. The children whose types have
      // changed from bv to int should be adjusted back to bv and then
      // this term is reconstructed.
      TypeNode resultingType;
      if (original.getType().isBitVector())
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

      //returnNode = original;
      break;
    }
  }
  Trace("test-pp") << "original: " << original << std::endl;
  Trace("test-pp") << "returnNode: " << returnNode << std::endl;
  return returnNode;
}

Node TestPp::translateNoChildren(Node original,
                                   std::vector<Node>& lemmas,
                                   std::map<Node, Node>& skolems)
{
  Trace("test-pp")
      << "translating leaf: " << original << "; of type: " << original.getType()
      << std::endl;
  // The result of the translation
  Node translation;

  //// The translation is done differently for variables (bound or free)  and
  //// constants (values)
  //if (original.isVar())
  //{
  //  if (original.getType().isFloatingPoint())
  //  {
  //    // For bit-vector variables, we create fresh integer variables.
  //    if (original.getKind() == kind::BOUND_VARIABLE)
  //    {
  //      // Range constraints for the bound real variables are not added now.
  //      // they will be added once the quantifier itself is handled.
  //      std::stringstream ss;
  //      ss << original;
  //      translation = d_nm->mkBoundVar(ss.str() + "_real", d_nm->realType());
  //    }
  //    else
  //    {
  //      Node realCast = castToType(original, d_nm->realType());
  //      Node fpCast;
  //      // we introduce a fresh variable, add range constraints, and save the
  //      // connection between original and the new variable via intCast
  //      translation = d_nm->getSkolemManager()->mkPurifySkolem(realCast);
  //      uint32_t esz = original.getType().getFloatingPointExponentSize();
  //      uint32_t ssz = original.getType().getFloatingPointSignificandSize();
  //      addRangeConstraint(translation, esz, ssz, lemmas);
  //      // put new definition of old variable in skolems
  //      fpCast = castToType(translation, original.getType());

  //      // add bvCast to skolems if it is not already there.
  //      if (skolems.find(original) == skolems.end())
  //      {
  //        skolems[original] = fpCast;
  //      }
  //      else
  //      {
  //        Assert(skolems[original] == fpCast);
  //      }
  //    }
  //  }
  //  //else if (original.getType().isFunction())
  //  //{
  //  //  // translate function symbol
  //  //  translation = translateFunctionSymbol(original, skolems);
  //  //}
  //  else
  //  {
  //    // leave other variables intact
  //    translation = original;
  //  }
  //}
  //else // Constants.
  //{
  //  // original is a constant (value) or an operator with no arguments (e.g., PI)
  //  if (original.getKind() == kind::CONST_FLOATINGPOINT)
  //  {
  //    //// Bit-vector constants are transformed into their integer value.
  //    //BitVector constant(original.getConst<BitVector>());
  //    //Integer c = constant.toInteger();
  //    //Rational r = Rational(c, Integer(1));
  //    //translation = d_nm->mkConstInt(r);

  //    FloatingPoint constant(original.getConst<FloatingPoint>());
  //    Rational r = constant.convertToRationalTotal(Rational(0));
  //    translation = d_nm->mkConstReal(r);
  //  }
  //  else
  //  {
  //    // Other constants or operators stay the same.
  //    translation = original;
  //  }
  //}

  translation = original;

  return translation;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal