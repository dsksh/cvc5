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
 * The FPToReal preprocessing pass.
 */

#ifndef __CVC5__PREPROCESSING__PASSES__FP_TO_REAL_H
#define __CVC5__PREPROCESSING__PASSES__FP_TO_REAL_H

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

class FPToReal : public PreprocessingPass
{
 public:
  FPToReal(PreprocessingPassContext* preprocContext);

 protected:
  Node realBlast(Node n,
                 std::vector<Node>& lemmas,
                 std::map<Node, Node>& skolems);

  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  /** Returns a node that represents the addition of x and y. */
  //Node createFPNode(kind::Kind_t kind, Node rm, Node x, Node y, uint32_t esz, uint32_t ssz);
  Node createFPOperator(kind::Kind_t rfpKind, uint32_t eb = 0, uint32_t sb = 0);

  /**
   * A useful utility function.
   * if n is an integer and tn is bit-vector,
   * applies the IntToBitVector operator on n.
   * if n is a bit-vector and tn is integer,
   * applies BitVector_TO_NAT operator.
   * Otherwise, keeps n intact.
   */
  Node castToType(Node n, TypeNode tn);

  /** Adds the range constraint to lemmas */
  void addFPRangeConstraint(Node node, uint32_t esize, uint32_t ssize, std::vector<Node>& lemmas);
  void addRMRangeConstraint(Node node, std::vector<Node>& lemmas);

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

  /** Caches for the different functions */
  CDNodeMap d_realblastCache;

  /** Useful constants */
  Node d_zero;
  Node d_one;

};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* __CVC5__PREPROCESSING__PASSES__FP_TO_REAL_H */
