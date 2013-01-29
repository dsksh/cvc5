/*********************                                                        */
/*! \file slicer.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "theory/bv/slicer.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace std; 


const TermId CVC4::theory::bv::UndefinedId = -1; 

/**
 * Base
 * 
 */
Base::Base(uint32_t size) 
  : d_size(size),
    d_repr((size-1)/32 + ((size-1) % 32 == 0? 0 : 1), 0)
{
  Assert (d_size > 0); 
}

  
void Base::sliceAt(Index index) {
  Index vector_index = index / 32;
  Assert (vector_index < d_size - 1); 
  Index int_index = index % 32;
  uint32_t bit_mask = utils::pow2(int_index); 
  d_repr[vector_index] = d_repr[vector_index] | bit_mask; 
}

void Base::sliceWith(const Base& other) {
  Assert (d_size == other.d_size);
  for (unsigned i = 0; i < d_repr.size(); ++i) {
    d_repr[i] = d_repr[i] | other.d_repr[i]; 
  }
}

bool Base::isCutPoint (Index index) const {
  // there is an implicit cut point at the end of the bv
  if (index == d_size - 1)
    return true;
    
  Index vector_index = index / 32;
  Assert (vector_index < d_size - 1); 
  Index int_index = index % 32;
  uint32_t bit_mask = utils::pow2(int_index); 

  return (bit_mask & d_repr[vector_index]) != 0; 
}

void Base::diffCutPoints(const Base& other, Base& res) const {
  Assert (d_size == other.d_size && res.d_size == d_size);
  for (unsigned i = 0; i < d_repr.size(); ++i) {
    Assert (res.d_repr[i] == 0); 
    res.d_repr[i] = d_repr[i] ^ other.d_repr[i]; 
  }
}

bool Base::isEmpty() const {
  for (unsigned i = 0; i< d_repr.size(); ++i) {
    if (d_repr[i] != 0)
      return false;
  }
  return true;
}

std::string Base::debugPrint() const {
  std::ostringstream os;
  os << "[";
  bool first = true; 
  for (unsigned i = 0; i < d_size - 1; ++i) {
    if (isCutPoint(i)) {
      if (first)
        first = false;
      else
        os <<"| "; 
        
      os << i ; 
    }
  }
  os << "]"; 
  return os.str(); 
}

/**
 * NormalForm
 *
 */

TermId NormalForm::getTerm(Index i, const UnionFind& uf) const {
  Assert (i < base.getBitwidth()); 
  Index count = 0;
  for (unsigned i = 0; i < decomp.size(); ++i) {
    Index size = uf.getBitwidth(decomp[i]); 
    if ( count + size <= i && count >= i) {
      return decomp[i]; 
    }
    count += size; 
  }
  Unreachable(); 
}
 
/**
 * UnionFind
 * 
 */
TermId UnionFind::addTerm(Index bitwidth) {
  Node node(bitwidth);
  d_nodes.push_back(node);
  TermId id = d_nodes.size() - 1; 
  d_representatives.insert(id);
  return id; 
}
/** 
 * At this point we assume the slicings of the two terms are properly aligned. 
 * 
 * @param t1 
 * @param t2 
 */
void UnionFind::unionTerms(const ExtractTerm& t1, const ExtractTerm& t2) {
  Assert (t1.getBitwidth() == t2.getBitwidth());
  
  NormalForm nf1(t1.getBitwidth());
  NormalForm nf2(t2.getBitwidth());
  
  getNormalForm(t1, nf1);
  getNormalForm(t2, nf2);

  Assert (nf1.decomp.size() == nf2.decomp.size());
  Assert (nf1.base == nf2.base);
  
  for (unsigned i = 0; i < nf1.decomp.size(); ++i) {
    merge (nf1.decomp[i], nf2.decomp[i]); 
  } 
}

/** 
 * Merge the two terms in the union find. Both t1 and t2
 * should be root terms. 
 * 
 * @param t1 
 * @param t2 
 */
void UnionFind::merge(TermId t1, TermId t2) {
  t1 = find(t1);
  t2 = find(t2); 

  if (t1 == t2)
    return;

  Node n1 = getNode(t1); 
  Node n2 = getNode(t2);
  Assert (! n1.hasChildren() && ! n2.hasChildren());
  n1.setRepr(t2); 
  d_representatives.erase(t1); 
}

TermId UnionFind::find(TermId id) const {
  Node node = getNode(id); 
  if (node.getRepr() != UndefinedId)
    return find(node.getRepr());
  return id; 
}
/** 
 * Splits the representative of the term between i-1 and i
 * 
 * @param id the id of the term
 * @param i the index we are splitting at
 * 
 * @return 
 */
void UnionFind::split(TermId id, Index i) {
  id = find(id); 
  Node node = getNode(id); 
  Assert (i < node.getBitwidth());

  if (i == 0 || i == node.getBitwidth()) {
    // nothing to do 
    return;
  }

  if (!node.hasChildren()) {
    // first time we split this term 
    TermId bottom_id = addTerm(i);
    TermId top_id = addTerm(node.getBitwidth() - i);
    node.setChildren(top_id, bottom_id);

  } else {
    Index cut = node.getCutPoint(*this); 
    if (i < cut )
      split(node.getChild(0), i);
    else
      split(node.getChild(1), i - cut); 
  }
}

void UnionFind::getNormalForm(const ExtractTerm& term, NormalForm& nf) {
  getDecomposition(term, nf.decomp);
  // update nf base
  Index count = 0; 
  for (unsigned i = 0; i < nf.decomp.size(); ++i) {
    count += getBitwidth(nf.decomp[i]);
    nf.base.sliceAt(count); 
  }
}

void UnionFind::getDecomposition(const ExtractTerm& term, Decomposition& decomp) {
  // making sure the term is aligned
  TermId id = find(term.id); 

  Node node = getNode(id);
  Assert (term.high < node.getBitwidth());
  // because we split the node, this must be the whole extract
  if (!node.hasChildren()) {
    Assert (term.high == node.getBitwidth() - 1 &&
            term.low == 0);
    decomp.push_back(id); 
  }
    
  Index cut = node.getCutPoint(*this);
  
  if (term.low < cut && term.high < cut) {
    // the extract falls entirely on the low child
    ExtractTerm child_ex(node.getChild(0), term.high, term.low); 
    getDecomposition(child_ex, decomp); 
  }
  else if (term.low >= cut && term.high >= cut){
    // the extract falls entirely on the high child
    ExtractTerm child_ex(node.getChild(1), term.high - cut, term.low - cut);
    getDecomposition(child_ex, decomp); 
  }
  else {
    // the extract is split over the two children
    ExtractTerm low_child(node.getChild(0), cut - 1, term.low);
    getDecomposition(low_child, decomp);
    ExtractTerm high_child(node.getChild(1), term.high, cut);
    getDecomposition(high_child, decomp); 
  }
}
/** 
 * May cause reslicings of the decompositions. Must not assume the decompositons
 * are the current normal form. 
 * 
 * @param d1 
 * @param d2 
 * @param common 
 */
void UnionFind::handleCommonSlice(const Decomposition& decomp1, const Decomposition& decomp2, TermId common) {
  Index common_size = getBitwidth(common); 

  // find starting points of common slice
  Index start1 = 0;
  for (unsigned j = 0; j < decomp1.size(); ++j) {
    if (decomp1[j] == common)
      break;
    start1 += getBitwidth(decomp1[j]); 
  }

  Index start2 = 0; 
  for (unsigned j = 0; j < decomp2.size(); ++j) {
    if (decomp2[j] == common)
      break;
    start2 += getBitwidth(decomp2[j]); 
  }
  start1 = start1 > start2 ? start2 : start1;
  start2 = start1 > start2 ? start1 : start2; 

  if (start1 + common_size <= start2) {
    Index overlap = start1 + common_size - start2;
    Assert (overlap > 0);
    Index diff = start2 - overlap;
    Assert (diff > 0);
    Index granularity = utils::gcd(diff, overlap);
    // split the common part 
    for (unsigned i = 0; i < common_size; i+= granularity) {
      split(common, i); 
    }
  }

}

void UnionFind::alignSlicings(const ExtractTerm& term1, const ExtractTerm& term2) {
  NormalForm nf1(term1.getBitwidth());
  NormalForm nf2(term2.getBitwidth());
  
  getNormalForm(term1, nf1);
  getNormalForm(term2, nf2);

  Assert (nf1.base.getBitwidth() == nf2.base.getBitwidth());
  
  // first check if the two have any common slices 
  std::vector<TermId> intersection; 
  utils::intersect(nf1.decomp, nf2.decomp, intersection); 
  for (unsigned i = 0; i < intersection.size(); ++i) {
    // handle common slice may change the normal form 
    handleCommonSlice(nf1.decomp, nf2.decomp, intersection[i]); 
  }
  
  // we need to update the normal form which may have changed 
  getNormalForm(term1, nf1);
  getNormalForm(term2, nf2); 

  // align the cuts points of the two slicings
  // FIXME: this can be done more efficiently
  Base& cuts = nf1.base;
  cuts.sliceWith(nf2.base);
  for (unsigned i = 0; i < cuts.getBitwidth(); ++i) {
    if (cuts.isCutPoint(i)) {
      TermId t1 = nf1.getTerm(i, *this);
      split(t1, i); 
      TermId t2 = nf2.getTerm(i, *this);
      split(t2, i); 
    }
  }
}
/** 
 * Given an extract term a[i:j] makes sure a is sliced
 * at indices i and j. 
 * 
 * @param term 
 */
void UnionFind::ensureSlicing(const ExtractTerm& term) {
  TermId id = find(term.id);
  split(id, term.high);
  split(id, term.low);
}

/**
 * Slicer
 * 
 */

ExtractTerm Slicer::registerTerm(TNode node) {
  Index low = 0, high = utils::getSize(node); 
  TNode n = node; 
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    TNode n = node[0];
    high = utils::getExtractHigh(node);
    low = utils::getExtractLow(node); 
  }
  if (d_nodeToId.find(n) == d_nodeToId.end()) {
    TermId id = d_unionFind.addTerm(utils::getSize(n)); 
    d_nodeToId[n] = id;
    d_idToNode[id] = n; 
  }
  TermId id = d_nodeToId[n];

  return ExtractTerm(id, high, low); 
}

void Slicer::processEquality(TNode eq) {
  Assert (eq.getKind() == kind::EQUAL);
  TNode a = eq[0];
  TNode b = eq[1];
  ExtractTerm a_ex= registerTerm(a);
  ExtractTerm b_ex= registerTerm(b);
  
  d_unionFind.ensureSlicing(a_ex);
  d_unionFind.ensureSlicing(b_ex);
  
  d_unionFind.alignSlicings(a_ex, b_ex);
  d_unionFind.unionTerms(a_ex, b_ex); 
}

void Slicer::getBaseDecomposition(TNode node, std::vector<Node>& decomp) {
  Index high = utils::getSize(node);
  Index low = 0; 
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    high = utils::getExtractHigh(node);
    low = utils::getExtractLow(node);
    node = node[0]; 
  }
  Assert (d_nodeToId.find(node) != d_nodeToId.end()); 
  TermId id = d_nodeToId[node];
  NormalForm nf(utils::getSize(node)); 
  d_unionFind.getNormalForm(ExtractTerm(id, high, low), nf);
  
  // construct actual extract nodes
  Index current_low = 0;
  Index current_high = 0; 
  for (unsigned i = 0; i < nf.decomp.size(); ++i) {
    Index current_size = d_unionFind.getBitwidth(nf.decomp[i]); 
    current_high += current_size; 
    Node current = utils::mkExtract(node, current_high - 1, current_low);
    current_low += current_size;
    decomp.push_back(current); 
  }
}

bool Slicer::isCoreTerm(TNode node) {
  if (d_coreTermCache.find(node) == d_coreTermCache.end()) {
    Kind kind = node.getKind(); 
    if (kind != kind::BITVECTOR_EXTRACT &&
        kind != kind::BITVECTOR_CONCAT &&
        kind != kind::EQUAL && kind != kind::NOT &&
        node.getMetaKind() != kind::metakind::VARIABLE &&
        kind != kind::CONST_BITVECTOR) {
      d_coreTermCache[node] = false;
      return false; 
    } else {
      // we need to recursively check whether the term is a root term or not
      bool isCore = true;
      for (unsigned i = 0; i < node.getNumChildren(); ++i) {
        isCore = isCore && isCoreTerm(node[i]); 
      }
      d_coreTermCache[node] = isCore;
      return isCore; 
    }
  }
  return d_coreTermCache[node]; 
}

void Slicer::splitEqualities(TNode node, std::vector<Node>& equalities) {
  Assert (node.getKind() == kind::EQUAL);
  TNode t1 = node[0];
  TNode t2 = node[1];

  uint32_t width = utils::getSize(t1); 
  
  Base base1(width); 
  if (t1.getKind() == kind::BITVECTOR_CONCAT) {
    int size = -1;
    // no need to count the last child since the end cut point is implicit 
    for (int i = t1.getNumChildren() - 1; i >= 1 ; --i) {
      size = size + utils::getSize(t1[i]);
      base1.sliceAt(size); 
    }
  }

  Base base2(width); 
  if (t2.getKind() == kind::BITVECTOR_CONCAT) {
    unsigned size = -1; 
    for (int i = t2.getNumChildren() - 1; i >= 1; --i) {
      size = size + utils::getSize(t2[i]);
      base2.sliceAt(size); 
    }
  }

  base1.sliceWith(base2); 
  if (!base1.isEmpty()) {
    // we split the equalities according to the base
    int last = 0; 
    for (unsigned i = 0; i < utils::getSize(t1); ++i) {
      if (base1.isCutPoint(i)) {
        Node extract1 = Rewriter::rewrite(utils::mkExtract(t1, i, last));
        Node extract2 = Rewriter::rewrite(utils::mkExtract(t2, i, last));
        last = i + 1;
        Assert (utils::getSize(extract1) == utils::getSize(extract2)); 
        equalities.push_back(utils::mkNode(kind::EQUAL, extract1, extract2)); 
      }
    }
  } else {
    // just return same equality
    equalities.push_back(node);
  }
} 
