/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for printing Alethe proof nodes.
 */

#include "proof/alethe/alethe_printer.h"

#include <iostream>
#include <sstream>
#include <unordered_map>

#include "options/proof_options.h"
#include "options/printer_options.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "util/smt2_quote_string.h"

namespace cvc5::internal {

namespace proof {

LetUpdaterPfCallback::LetUpdaterPfCallback(AletheLetBinding& lbind)
    : d_lbind(lbind)
{
}

LetUpdaterPfCallback::~LetUpdaterPfCallback() {}

bool LetUpdaterPfCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                        const std::vector<Node>& fa,
                                        bool& continueUpdate)
{
  ProofRule r = pn->getRule();
  if (r == ProofRule::ASSUME)
  {
    d_lbind.process(pn->getResult());
    return false;
  }
  const std::vector<Node>& args = pn->getArguments();
  if (r == ProofRule::SCOPE)
  {
    for (size_t i = 0, size = args.size(); i < size; ++i)
    {
      d_lbind.process(args[i]);
    }
    return false;
  }
  // Letification done on the converted terms (thus from the converted
  // conclusion) and potentially on arguments, which means to ignore the first
  // two arguments (which are the Alethe rule and the original conclusion).
  AlwaysAssert(args.size() > 2)
      << "res: " << pn->getResult() << "\nid: " << pn->getRule();
  for (size_t i = 2, size = args.size(); i < size; ++i)
  {
    Trace("alethe-printer") << "Process " << args[i] << std::endl;
    // We do not share s-expressions, but rather their children
    if (args[i].getKind() == Kind::SEXPR)
    {
      for (const auto& arg : args[i])
      {
        d_lbind.process(arg);
      }
      continue;
    }
    d_lbind.process(args[i]);
  }
  return false;
}

AletheProofPrinter::AletheProofPrinter(Env& env, AletheNodeConverter& anc)
    : EnvObj(env),
      d_lbind(options().printer.dagThresh ? options().printer.dagThresh + 1
                                          : 0),
      d_anc(anc),
      d_cb(new LetUpdaterPfCallback(d_lbind))
{
}

void AletheProofPrinter::printStepId(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    std::unordered_map<Node, std::string>& assumptionsMap,
    std::unordered_map<std::shared_ptr<ProofNode>, std::string>& pfMap)
{
  if (pfn->getRule() == ProofRule::ASSUME)
  {
    Node res = d_anc.convert(pfn->getResult());
    Assert(!res.isNull());
    Trace("alethe-printer") << "... reached assumption " << res << std::endl;
    auto it = assumptionsMap.find(res);
    Assert(it != assumptionsMap.end())
        << "Assumption has not been printed yet! " << res << "/"
        << assumptionsMap << std::endl;
    Trace("alethe-printer") << "... found assumption in list " << it->second
                            << ": " << res << "/" << assumptionsMap << std::endl;
    out << it->second;
    return;
  }
  Assert(pfMap.find(pfn) != pfMap.end())
      << "Cannot find proof of " << pfn->getResult() << std::endl;
  out << pfMap.find(pfn)->second;
}

void AletheProofPrinter::printTerm(std::ostream& out, TNode n)
{
  std::stringstream ss;
  options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
  // We print lambda applications in non-curried manner
  options::ioutils::applyFlattenHOChains(ss, true);
  // Make sure we do not introduce "let" for sharing, since names will not have
  // been introduced under binders.
  options::ioutils::applyDagThresh(ss, 0);
  ss << d_lbind.convert(n, "@p_");
  out << ss.str();
}

void AletheProofPrinter::print(
    std::ostream& out,
    std::shared_ptr<ProofNode> pfn,
    const std::map<Node, std::string>& assertionNames)
{
  Trace("alethe-printer") << "- Print proof in Alethe format." << std::endl;
  // ignore outer scope
  pfn = pfn->getChildren()[0];
  std::shared_ptr<ProofNode> innerPf = pfn->getChildren()[0];
  Assert(innerPf);

  // print quantifier Skolems, if they are being defined
  if (options().proof.proofAletheDefineSkolems)
  {
    const std::map<Node, Node>& skolemDefs = d_anc.getSkolemDefinitions();
    for (const auto& [skolem, choice] : skolemDefs)
    {
      out << "(define-fun " << skolem << " () " << skolem.getType() << " ";
      printTerm(out, choice);
      out << ")" << std::endl;
    }
  }
  if (options().printer.dagThresh)
  {
    // Traverse the proof node to letify the (converted) conclusions of proof
    // steps. Note that we traverse the original proof node because assumptions
    // may apper just in them (if they are not used in the rest of the proof).
    // Otherwise repeated terms *only* in assumptions would not be letified.
    ProofNodeUpdater updater(d_env, *(d_cb.get()), false, false);
    Trace("alethe-printer") << "- letify." << std::endl;
    updater.process(pfn);

    std::vector<Node> letList;
    d_lbind.letify(letList);
    if (TraceIsOn("alethe-printer"))
    {
      for (TNode n : letList)
      {
        Trace("alethe-printer")
            << "Term " << n << " has id " << d_lbind.getId(n) << std::endl;
      }
    }
  }
  Trace("alethe-printer") << "- Print assumptions." << std::endl;
  std::unordered_map<Node, std::string> assumptionsMap;
  const std::vector<Node>& args = pfn->getArguments();
  // Special handling for the first scope. Print assumptions and add them to the
  // list but do not print anchor.
  Assert(!args.empty());
  for (size_t i = 0, size = args.size(); i < size; i++)
  {
    // search name with original assumption rather than its conversion
    Assert(!d_anc.getOriginalAssumption(args[i]).isNull());
    Node original = d_anc.getOriginalAssumption(args[i]);
    auto it = assertionNames.find(original);
    if (it != assertionNames.end())
    {
      // Since names can be strings that were originally quoted, we must see if
      // the quotes need to be added back.
      std::string quotedName = quoteSymbol(it->second);
      out << "(assume " << quotedName << " ";
      assumptionsMap[args[i]] = quotedName;
    }
    else
    {
      out << "(assume a" << i << " ";
      assumptionsMap[args[i]] = "a" + std::to_string(i);
    }
    printTerm(out, args[i]);
    out << ")" << std::endl;
  }
  // Then, print the rest of the proof node
  std::unordered_map<std::shared_ptr<ProofNode>, std::string> pfMap;
  size_t id = 0;
  printInternal(out, "", id, pfn->getChildren()[0], assumptionsMap, pfMap);
}

void AletheProofPrinter::printInternal(
    std::ostream& out,
    const std::string& prefix,
    size_t& id,
    std::shared_ptr<ProofNode> pfn,
    std::unordered_map<Node, std::string>& assumptionsMap,
    std::unordered_map<std::shared_ptr<ProofNode>, std::string>& pfMap)
{
  // assumptions are not printed when reached here because in Alethe they are
  // always printed beforehand, i.e., from the scope introducing them, or being
  // the initial assumptions.
  if (pfn->getRule() == ProofRule::ASSUME)
  {
    return;
  }
  std::unordered_map<std::shared_ptr<ProofNode>, std::string>::const_iterator pfIt =
      pfMap.find(pfn);
  if (pfIt != pfMap.end())
  {
    Trace("alethe-printer") << "... step is already printed t" << pfIt->second
                            << " " << pfn->getResult() << " "
                            << getAletheRule(pfn->getArguments()[0]) << std::endl;
    return;
  }
  const std::vector<Node>& args = pfn->getArguments();
  const std::vector<std::shared_ptr<ProofNode>>& pfChildren = pfn->getChildren();
  // Get the alethe proof rule
  AletheRule arule = getAletheRule(args[0]);
  Trace("alethe-printer") << "... print step " << arule << " : " << args[2]
                          << std::endl;
  // We special case printing anchors
  if (arule >= AletheRule::ANCHOR_SUBPROOF
      && arule <= AletheRule::ANCHOR_SKO_EX)
  {
    Trace("alethe-printer") << push;
    Assert(pfChildren.size() == 1);
    out << "(anchor :step " << prefix << "t" << id;
    std::string subproofPrefix = prefix + "t" + std::to_string(id) + ".";
    // create maps to be used when printing the subproof, which will be discarded once we finish
    std::unordered_map<Node, std::string> subproofAssumptionsMap{assumptionsMap.begin(), assumptionsMap.end()};
    std::unordered_map<std::shared_ptr<ProofNode>, std::string> subproofPfMap{pfMap.begin(), pfMap.end()};
    std::vector<std::string> dischargeIds;
    // since the subproof shape relies on having at least one step inside it, if
    // the step relative to children[0] is already pfMap, we remove it from
    // subproofPfMap
    auto it = subproofPfMap.find(pfChildren[0]);
    if (it != subproofPfMap.end())
    {
      subproofPfMap.erase(it);
    }
    // if subproof, print assumptions, otherwise print arguments
    if (arule == AletheRule::ANCHOR_SUBPROOF)
    {
      out << ")" << std::endl;
      Assert(args.size() >= 3);
      for (size_t i = 3, size = args.size(); i < size; ++i)
      {
        Trace("alethe-printer")
            << "... print assumption " << args[i] << std::endl;
        std::string assumptionId = subproofPrefix + "a" + std::to_string(i - 3);
        out << "(assume " << assumptionId << " ";
        printTerm(out, args[i]);
        out << ")" << std::endl;
        subproofAssumptionsMap[args[i]] = assumptionId;
        dischargeIds.push_back(assumptionId);
      }
    }
    else
    {
      Assert(arule >= AletheRule::ANCHOR_BIND && arule <= AletheRule::ANCHOR_SKO_EX);
      out << " :args (";
      for (size_t i = 3, size = args.size(); i < size; ++i)
      {
        if (args[i].getKind() == Kind::EQUAL)
        {
          Assert(args[i][0].getKind() == Kind::BOUND_VARIABLE);
          out << "(:= (" << args[i][0] << " " << args[i][0].getType() << ") ";
          printTerm(out, args[i][1]);
          out << ")" << (i != args.size() - 1 ? " " : "");
          continue;
        }
        Assert(args[i].getKind() == Kind::BOUND_VARIABLE) << args[i];
        out << "(" << args[i] << " " << args[i].getType() << ") ";
      }
      out << "))" << std::endl;
    }
    size_t subproofId = 0;
    printInternal(out, subproofPrefix, subproofId, pfChildren[0], subproofAssumptionsMap, subproofPfMap);
    Trace("alethe-printer") << pop;
    std::string stepId = prefix + "t" + std::to_string(id++);
    out << "(step " << stepId << " ";
    printTerm(out, args[2]);
    out << " :rule " << arule;
    // Discharge assumptions in the case of subproof
    if (arule == AletheRule::ANCHOR_SUBPROOF)
    {
      out << " :discharge (";
      for (size_t i = 3, size = args.size(); i < size; ++i)
      {
        out << dischargeIds[i - 3] << (i < args.size() - 1 ? " " : "");
      }
      out << ")";
    }
    out << ")" << std::endl;
    pfMap[pfn] = stepId;
    return;
  }
  // Print the steps for children to guarantee we will have ids for them in the
  // premises of this step
  for (const std::shared_ptr<ProofNode>& pfChild : pfChildren)
  {
    printInternal(out, prefix, id, pfChild, assumptionsMap, pfMap);
  }
  // Print this step
  std::string stepId = prefix + "t" + std::to_string(id++);
  out << "(step " << stepId << " ";
  // print the conclusion and the rule
  printTerm(out, args[2]);
  out << " :rule " << arule;
  if (!pfChildren.empty())
  {
    out << " :premises (";
    bool first = true;
    for (const std::shared_ptr<ProofNode>& pfChild : pfChildren)
    {
      out << (first ? "" : " ");
      first = false;
      printStepId(out, pfChild, assumptionsMap, pfMap);
    }
    out << ")";
  }
  if (args.size() > 3)
  {
    out << " :args (";
    for (size_t i = 3, size = args.size(); i < size; i++)
    {
      printTerm(out, args[i]);
      out << (i < args.size() - 1 ? " " : "");
    }
    out << ")";
  }
  out << ")" << std::endl;
  pfMap[pfn] = stepId;
}

}  // namespace proof
}  // namespace cvc5::internal
