/*********************                                                        */
/*! \file theory.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base of the theory interface.
 **
 ** Base of the theory interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__THEORY_H
#define __CVC4__THEORY__THEORY_H

#include "expr/node.h"
#include "expr/attribute.h"
#include "theory/output_channel.h"
#include "context/context.h"

#include <deque>
#include <list>

#include <string>
#include <iostream>

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Instances of this class serve as response codes from
 * Theory::preRewrite() and Theory::postRewrite().  Instances of
 * derived classes RewritingComplete(n) and RewriteAgain(n) should
 * be used for better self-documenting behavior.
 */
class RewriteResponse {
protected:
  enum Status { DONE, REWRITE };

  RewriteResponse(Status s, Node n) : d_status(s), d_node(n) {}

private:
  const Status d_status;
  const Node d_node;

public:
  bool isDone() const { return d_status == DONE; }
  bool needsMoreRewriting() const { return d_status == REWRITE; }
  Node getNode() const { return d_node; }
};

/**
 * Return n, but request additional (pre,post)rewriting of it.
 */
class RewriteAgain : public RewriteResponse {
public:
  RewriteAgain(Node n) : RewriteResponse(REWRITE, n) {}
};

/**
 * Signal that (pre,post)rewriting of the node is complete at n.
 */
class RewritingComplete : public RewriteResponse {
public:
  RewritingComplete(Node n) : RewriteResponse(DONE, n) {}
};

/**
 * Base class for T-solvers.  Abstract DPLL(T).
 *
 * This is essentially an interface class.  The TheoryEngine has
 * pointers to Theory.  Note that only one specific Theory type (e.g.,
 * TheoryUF) can exist per NodeManager, because of how the
 * RegisteredAttr works.  (If you need multiple instances of the same
 * theory, you'll have to write a multiplexed theory that dispatches
 * all calls to them.)
 */
class Theory {
private:

  friend class ::CVC4::TheoryEngine;

  /**
   * Disallow default construction.
   */
  Theory();

  /**
   * The context for the Theory.
   */
  context::Context* d_context;

  /**
   * The assertFact() queue.
   *
   * This queue MUST be emptied by ANY call to check() at ANY effort
   * level.  In debug builds, this is checked.  On backjump we clear
   * the fact queue (see FactsResetter, below).
   *
   * These can safely be TNodes because the literal map maintained in
   * the SAT solver keeps them live.  As an added benefit, if we have
   * them as TNodes, dtors are cheap (optimized away?).
   */
  std::deque<TNode> d_facts;

  /** Helper class to reset the fact queue on pop(). */
  class FactsResetter : public context::ContextNotifyObj {
    Theory& d_thy;

  public:
    FactsResetter(Theory& thy) :
      context::ContextNotifyObj(thy.d_context),
      d_thy(thy) {
    }

    void notify() {
      d_thy.d_facts.clear();
    }
  } d_factsResetter;

  friend class FactsResetter;

protected:

  /**
   * Construct a Theory.
   */
  Theory(context::Context* ctxt, OutputChannel& out) throw() :
    d_context(ctxt),
    d_facts(),
    d_factsResetter(*this),
    d_out(&out) {
  }

  /**
   * This is called at shutdown time by the TheoryEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory (based on what
   * hard-links to Nodes are outstanding).  As the fact queue might be
   * nonempty, we ensure here that it's clear.  If you overload this,
   * you must make an explicit call here to this->Theory::shutdown()
   * too.
   */
  virtual void shutdown() {
    d_facts.clear();
  }

  /**
   * Get the context associated to this Theory.
   */
  context::Context* getContext() const {
    return d_context;
  }

  /**
   * The output channel for the Theory.
   */
  OutputChannel* d_out;

  /**
   * Returns true if the assertFact queue is empty
   */
  bool done() throw() {
    return d_facts.empty();
  }

  /**
   * Return whether a node is shared or not.  Used by setup().
   */
  bool isShared(TNode n) throw();

  /** Tag for the "registerTerm()-has-been-called" flag on Nodes */
  struct Registered {};
  /** The "registerTerm()-has-been-called" flag on Nodes */
  typedef CVC4::expr::CDAttribute<Registered, bool> RegisteredAttr;

  /** Tag for the "preRegisterTerm()-has-been-called" flag on Nodes */
  struct PreRegistered {};
  /** The "preRegisterTerm()-has-been-called" flag on Nodes */
  typedef CVC4::expr::Attribute<PreRegistered, bool> PreRegisteredAttr;

  /**
   * Returns the next atom in the assertFact() queue.  Guarantees that
   * registerTerm() has been called on the theory specific subterms.
   *
   * @return the next atom in the assertFact() queue.
   */
  Node get();

public:

  /**
   * Destructs a Theory.  This implementation does nothing, but we
   * need a virtual destructor for safety in case subclasses have a
   * destructor.
   */
  virtual ~Theory() {
  }

  /**
   * Subclasses of Theory may add additional efforts.  DO NOT CHECK
   * equality with one of these values (e.g. if STANDARD xxx) but
   * rather use range checks (or use the helper functions below).
   * Normally we call QUICK_CHECK or STANDARD; at the leaves we call
   * with MAX_EFFORT.
   */
  enum Effort {
    MIN_EFFORT = 0,
    QUICK_CHECK = 10,
    STANDARD = 50,
    FULL_EFFORT = 100
  };/* enum Effort */

  // TODO add compiler annotation "constant function" here
  static bool minEffortOnly(Effort e)        { return e == MIN_EFFORT; }
  static bool quickCheckOrMore(Effort e)     { return e >= QUICK_CHECK; }
  static bool quickCheckOnly(Effort e)       { return e >= QUICK_CHECK && e < STANDARD; }
  static bool standardEffortOrMore(Effort e) { return e >= STANDARD; }
  static bool standardEffortOnly(Effort e)   { return e >= STANDARD && e < FULL_EFFORT; }
  static bool fullEffort(Effort e)           { return e >= FULL_EFFORT; }

  /**
   * Set the output channel associated to this theory.
   */
  void setOutputChannel(OutputChannel& out) {
    d_out = &out;
  }

  /**
   * Get the output channel associated to this theory.
   */
  OutputChannel& getOutputChannel() {
    return *d_out;
  }

  /**
   * Get the output channel associated to this theory [const].
   */
  const OutputChannel& getOutputChannel() const {
    return *d_out;
  }

  /**
   * Pre-register a term.  Done one time for a Node, ever.
   */
  virtual void preRegisterTerm(TNode) = 0;

  /**
   * Pre-rewrite a term.  This default base-class implementation
   * simply returns RewritingComplete(n).  A theory should never
   * rewrite a term to a strictly larger term that contains itself, as
   * this will cause a loop of hard Node links in the cache (and thus
   * memory leakage).
   */
  virtual RewriteResponse preRewrite(TNode n, bool topLevel) {
    Debug("theory-rewrite") << "no pre-rewriting to perform for " << n << std::endl;
    return RewritingComplete(n);
  }

  /**
   * Post-rewrite a term.  This default base-class implementation
   * simply returns RewritingComplete(n).  A theory should never
   * rewrite a term to a strictly larger term that contains itself, as
   * this will cause a loop of hard Node links in the cache (and thus
   * memory leakage).
   */
  virtual RewriteResponse postRewrite(TNode n, bool topLevel) {
    Debug("theory-rewrite") << "no post-rewriting to perform for " << n << std::endl;
    return RewritingComplete(n);
  }

  /**
   * Register a term.
   *
   * When get() is called to get the next thing off the theory queue,
   * setup() is called on its subterms (in TheoryEngine).  Then setup()
   * is called on this node.
   *
   * This is done in a "context escape" -- that is, at context level 0.
   * setup() MUST NOT MODIFY context-dependent objects that it hasn't
   * itself just created.
   */
  virtual void registerTerm(TNode) = 0;

  /**
   * Assert a fact in the current context.
   */
  void assertFact(TNode n) {
    Debug("theory") << "Theory::assertFact(" << n << ")" << std::endl;
    d_facts.push_back(n);
  }

  /**
   * Check the current assignment's consistency.
   *
   * An implementation of check() is required to either:
   * - return a conflict on the output channel,
   * - be interrupted,
   * - throw an exception
   * - or call get() until done() is true.
   */
  virtual void check(Effort level = FULL_EFFORT) = 0;

  /**
   * T-propagate new literal assignments in the current context.
   */
  virtual void propagate(Effort level = FULL_EFFORT) = 0;

  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).  Report
   * explanations to an output channel.
   */
  virtual void explain(TNode n, Effort level = FULL_EFFORT) = 0;

  /**
   * Identify this theory (for debugging, dynamic configuration,
   * etc..)
   */
  virtual std::string identify() const = 0;

  //
  // CODE INVARIANT CHECKING (used only with CVC4_ASSERTIONS)
  //

  /**
   * Different states at which invariants are checked.
   */
  enum ReadyState {
    ABOUT_TO_PUSH,
    ABOUT_TO_POP
  };/* enum ReadyState */

  /**
   * Public invariant checker.  Assert that this theory is in a valid
   * state for the (external) system state.  This implementation
   * checks base invariants and then calls theoryReady().  This
   * function may abort in the case of a failed assert, or return
   * false (the caller should assert that the return value is true).
   *
   * @param s the state about which to check invariants
   */
  bool ready(ReadyState s) {
    if(s == ABOUT_TO_PUSH) {
      Assert(d_facts.empty(), "Theory base code invariant broken: "
             "fact queue is nonempty on context push");
    }

    return theoryReady(s);
  }

protected:

  /**
   * Check any invariants at the ReadyState given.  Only called by
   * Theory class, and then only with CVC4_ASSERTIONS enabled.  This
   * function may abort in the case of a failed assert, or return
   * false (the caller should assert that the return value is true).
   *
   * @param s the state about which to check invariants
   */
  virtual bool theoryReady(ReadyState s) {
    return true;
  }

};/* class Theory */

std::ostream& operator<<(std::ostream& os, Theory::Effort level);

}/* CVC4::theory namespace */

inline std::ostream& operator<<(std::ostream& out, const CVC4::theory::Theory& theory) {
  return out << theory.identify();
}

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_H */
