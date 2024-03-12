/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Testing stuff that is not exposed by the python API to fix code coverage
 */

#include <cvc5/cvc5_parser.h>

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackUncovered : public TestApi
{
};

TEST_F(TestApiBlackUncovered, exception_getmessage)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x).notTerm());

  ASSERT_THROW(d_solver->getValue(x), CVC5ApiRecoverableException);

  try
  {
    d_solver->getValue(x);
  }
  catch (const CVC5ApiRecoverableException& e)
  {
    ASSERT_NO_THROW(e.getMessage());
  }
}

TEST_F(TestApiBlackUncovered, streaming_operators_to_string)
{
  std::stringstream ss;
  ss << cvc5::Kind::EQUAL << std::to_string(cvc5::Kind::EQUAL)
     << cvc5::kindToString(cvc5::Kind::EQUAL);
  ss << cvc5::SortKind::ARRAY_SORT << std::to_string(cvc5::SortKind::ARRAY_SORT)
     << cvc5::sortKindToString(cvc5::SortKind::ARRAY_SORT);
  ss << cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE
     << std::to_string(cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE);
  ss << cvc5::UnknownExplanation::UNKNOWN_REASON
     << std::to_string(cvc5::UnknownExplanation::UNKNOWN_REASON);
  ss << cvc5::modes::BlockModelsMode::LITERALS
     << std::to_string(cvc5::modes::BlockModelsMode::LITERALS);
  ss << cvc5::modes::LearnedLitType::PREPROCESS
     << std::to_string(cvc5::modes::LearnedLitType::PREPROCESS);
  ss << cvc5::modes::ProofComponent::FULL
     << std::to_string(cvc5::modes::ProofComponent::FULL);
  ss << cvc5::modes::FindSynthTarget::ENUM
     << std::to_string(cvc5::modes::FindSynthTarget::ENUM);
  ss << cvc5::modes::InputLanguage::SMT_LIB_2_6
     << std::to_string(cvc5::modes::InputLanguage::SMT_LIB_2_6);
  ss << cvc5::modes::ProofFormat::LFSC
     << std::to_string(cvc5::modes::ProofFormat::LFSC);
  ss << cvc5::ProofRule::ASSUME;
  ss << cvc5::Result();
  ss << cvc5::Op();
  ss << cvc5::SynthResult();
  ss << cvc5::Grammar();

  Sort intsort = d_tm.getIntegerSort();
  Term x = d_tm.mkConst(intsort, "x");

  ss << std::vector<Term>{x, x};
  ss << std::set<Term>{x, x};
  ss << std::unordered_set<Term>{x, x};
}

TEST_F(TestApiBlackUncovered, datatypeApi)
{
  DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_tm.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort listSort = d_tm.mkDatatypeSort(dtypeSpec);
  Datatype d = listSort.getDatatype();

  std::stringstream ss;
  ss << cons;
  ss << d.getConstructor("cons");
  ss << d.getSelector("head");
  ss << std::vector<DatatypeConstructorDecl>{cons, nil};
  ss << d;

  {
    DatatypeConstructor c = d.getConstructor("cons");
    DatatypeConstructor::const_iterator it;
    it = c.begin();
    ASSERT_NE(it, c.end());
    ASSERT_EQ(it, c.begin());
    *it;
    ASSERT_NO_THROW(it->getName());
    ++it;
    it++;
  }
  {
    Datatype::const_iterator it;
    it = d.begin();
    ASSERT_NE(it, d.end());
    ASSERT_EQ(it, d.begin());
    it->getName();
    *it;
    ++it;
    it++;
  }
}

TEST_F(TestApiBlackUncovered, termNativeTypes)
{
  Term t = d_tm.mkInteger(0);
  d_tm.mkReal(0);
  d_tm.mkReal(0, 1);
  d_solver->mkReal(0);
  d_solver->mkReal(0, 1);
  t.isInt32Value();
  t.getInt32Value();
  t.isInt64Value();
  t.getInt64Value();
  t.isUInt32Value();
  t.getUInt32Value();
  t.isUInt64Value();
  t.getUInt64Value();
  t.isReal32Value();
  t.getReal32Value();
  t.isReal64Value();
  t.getReal64Value();
}

TEST_F(TestApiBlackUncovered, termIterators)
{
  Term t = d_tm.mkInteger(0);
  auto it = t.begin();
  auto it2(it);
  it++;
}

TEST_F(TestApiBlackUncovered, checkSatAssumingSingle)
{
  Sort boolsort = d_tm.getBooleanSort();
  Term b = d_tm.mkConst(boolsort, "b");
  d_solver->checkSatAssuming(b);
}

TEST_F(TestApiBlackUncovered, mkOpInitializerList)
{
  d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {1, 1});
  d_solver->mkOp(Kind::BITVECTOR_EXTRACT, {1, 1});
}

TEST_F(TestApiBlackUncovered, mkTermKind)
{
  Term b = d_tm.mkConst(d_tm.getRealSort(), "b");
  d_tm.mkTerm(Kind::GT, {b, b});
  d_solver->mkTerm(Kind::GT, {b, b});
}

TEST_F(TestApiBlackUncovered, getValue)
{
  d_solver->setOption("produce-models", "true");
  Sort boolsort = d_tm.getBooleanSort();
  Term b = d_tm.mkConst(boolsort, "b");
  d_solver->assertFormula(b);
  d_solver->checkSat();
  d_solver->getValue({b, b, b});
}

TEST_F(TestApiBlackUncovered, isOutputOn)
{
  d_solver->isOutputOn("inst");
  d_solver->getOutput("inst");
}

TEST_F(TestApiBlackUncovered, Options)
{
  auto dopts = d_solver->getDriverOptions();
  dopts.err();
  dopts.in();
  dopts.out();

  std::stringstream ss;
  {
    auto info = d_solver->getOptionInfo("verbose");
    ss << info;
    }
    {
    auto info = d_solver->getOptionInfo("print-success");
    ss << info;
    info.boolValue();
    }
    {
    auto info = d_solver->getOptionInfo("verbosity");
    ss << info;
    info.intValue();
    }
    {
    auto info = d_solver->getOptionInfo("rlimit");
    ss << info;
    info.uintValue();
    }
    {
    auto info = d_solver->getOptionInfo("random-freq");
    ss << info;
    info.doubleValue();
    }
    {
    auto info = d_solver->getOptionInfo("force-logic");
    ss << info;
    info.stringValue();
    }
    {
    auto info = d_solver->getOptionInfo("simplification");
    ss << info;
    }
}

TEST_F(TestApiBlackUncovered, Statistics)
{
    d_solver->assertFormula(d_tm.mkConst(d_tm.getBooleanSort(), "x"));
    d_solver->checkSat();
    Statistics stats = d_solver->getStatistics();
    std::stringstream ss;
    ss << stats;
    auto it = stats.begin();
    ASSERT_NE(it, stats.end());
    it++;
    it--;
    ++it;
    --it;
    ASSERT_EQ(it, stats.begin());
    ss << it->first;

    testing::internal::CaptureStdout();
    d_solver->printStatisticsSafe(STDOUT_FILENO);
    testing::internal::GetCapturedStdout();
}

// Copied from api/cpp/solver_black.cpp
TEST_F(TestApiBlackUncovered, declareOracleFunUnsat)
{
    d_solver->setOption("oracles", "true");
    Sort iSort = d_tm.getIntegerSort();
    // f is the function implementing (lambda ((x Int)) (+ x 1))
    Term f = d_solver->declareOracleFun(
        "f", {iSort}, iSort, [&](const std::vector<Term>& input) {
          if (input[0].isUInt32Value())
          {
            return d_tm.mkInteger(input[0].getUInt32Value() + 1);
          }
          return d_tm.mkInteger(0);
        });
    Term three = d_tm.mkInteger(3);
    Term five = d_tm.mkInteger(5);
    Term eq = d_tm.mkTerm(Kind::EQUAL,
                          {d_tm.mkTerm(Kind::APPLY_UF, {f, three}), five});
    d_solver->assertFormula(eq);
    d_solver->checkSat();
}

TEST_F(TestApiBlackUncovered, Proof)
{
  Proof proof;
  ASSERT_EQ(proof.getRule(), ProofRule::UNKNOWN);
  ASSERT_TRUE(proof.getResult().isNull());
  ASSERT_TRUE(proof.getChildren().empty());
  ASSERT_TRUE(proof.getArguments().empty());
}

TEST_F(TestApiBlackUncovered, Parser)
{
  parser::Command command;
  Solver solver;
  parser::InputParser inputParser(&solver);
  ASSERT_EQ(inputParser.getSolver(), &solver);
  parser::SymbolManager* sm = inputParser.getSymbolManager();
  ASSERT_EQ(sm->isLogicSet(), false);
  std::stringstream ss;
  ss << command << std::endl;
  inputParser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "Parser");
  parser::ParserException defaultConstructor;
  std::string message = "error";
  const char* cMessage = "error";
  std::string filename = "file.smt2";
  parser::ParserException stringConstructor(message);
  parser::ParserException cStringConstructor(cMessage);
  parser::ParserException exception(message, filename, 10, 11);
  exception.toStream(ss);
  ASSERT_EQ(message, exception.getMessage());
  ASSERT_EQ(message, exception.getMessage());
  ASSERT_EQ(filename, exception.getFilename());
  ASSERT_EQ(10, exception.getLine());
  ASSERT_EQ(11, exception.getColumn());

  parser::ParserEndOfFileException eofDefault;
  parser::ParserEndOfFileException eofString(message);
  parser::ParserEndOfFileException eofCMessage(cMessage);
  parser::ParserEndOfFileException eof(message, filename, 10, 11);
}

}  // namespace test
}  // namespace cvc5::internal
