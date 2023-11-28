
#ifndef __CVC5__PREPROCESSING__PASSES__TEST_PP_H
#define __CVC5__PREPROCESSING__PASSES__TEST_PP_H

#include "cvc5_private.h"

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using CDNodeMap = context::CDHashMap<Node, Node>;

class TestPp : public PreprocessingPass
{
 public:
  TestPp(PreprocessingPassContext* preprocContext);

 protected:
  Node cacheNode(Node n);

  Node realBlast(Node n,
                std::vector<Node>& lemmas,
                std::map<Node, Node>& skolems);

  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  /** Returns a node that represents the mult of x and y. */
  Node createFPMultNode(Node rm, Node x, Node y, uint32_t esz, uint32_t ssz);

  ///**
  // * A useful utility function.
  // * if n is an integer and tn is bit-vector,
  // * applies the IntToBitVector operator on n.
  // * if n is a bit-vector and tn is integer,
  // * applies BitVector_TO_NAT operator.
  // * Otherwise, keeps n intact.
  // */
  //Node castToType(Node n, TypeNode tn);

  ///** Adds the constraint 0 <= node < 2^size to lemmas */
  //void addRangeConstraint(Node node, uint32_t esize, uint32_t ssize, std::vector<Node>& lemmas);

  //Node mkRangeConstraint(Node newVar);

  /**
   * Reconstructs a node whose main operator cannot be
   * translated to reals.
   * 
   * Reconstruction is done by casting to reals as needed.
   * For example, if node is (select A x) where A
   * is a bit-vector array, we do not change A to be
   * an integer array, even though x was translated
   * to integers.
   * In this case we cast x to (bv2nat x) during
   * the reconstruction.
   *
   * @param originalNode the node that we are reconstructing
   * @param resultType the desired type for the reconstruction
   * @param translated_children the children of originalNode
   *        after their translation to integers.
   * @return A node with originalNode's operator that has type resultType.
   */
  Node reconstructNode(Node originalNode,
                       TypeNode resultType,
                       const std::vector<Node>& translated_children);

  /**
   * Performs the actual translation to integers for nodes
   * that have children.
   */
  Node translateWithChildren(Node original,
                             const std::vector<Node>& translated_children,
                             std::vector<Node>& lemmas);

  /**
   * Performs the actual translation to integers for nodes
   * that don't have children (variables, constants, uninterpreted function
   * symbols).
   */
  Node translateNoChildren(Node original,
                           std::vector<Node>& lemmas,
                           std::map<Node, Node>& skolems);

  /** Node manager that is used throughout the pass */
  NodeManager* d_nm;

  //context::CDHashSet<Node> d_rangeAssertions;

  /** Caches for the different functions */
  CDNodeMap d_binarizeCache;
  CDNodeMap d_realblastCache;

  /** Useful constants */
  Node d_zero;
  Node d_one;

};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* __CVC5__PREPROCESSING__PASSES__TEST_PP_H */