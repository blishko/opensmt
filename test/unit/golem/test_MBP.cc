//
// Created by Martin Blicha on 09.06.21.
//

#include <gtest/gtest.h>
#include <LRALogic.h>
#include <ModelBasedProjection.h>
#include <ModelBuilder.h>

TEST(test_MBP, test_AllEqualBounds) {
    LRALogic logic;
    ModelBasedProjection mbp(logic);
    PTRef x0 = logic.mkNumVar("x0");
    PTRef x1 = logic.mkNumVar("x1");
    PTRef one = logic.getTerm_NumOne();
    // x0 = 0 and x1 = x0 + 1
    // (and (<= x0 0) (<= 0 x0) (<= (- x1 x0) 1) (<= 1 (- x1 x0)))
    PTRef lit1 = logic.mkNumLeq(x0, logic.getTerm_NumZero());
    PTRef lit2 = logic.mkNumGeq(x0, logic.getTerm_NumZero());
    PTRef lit3 = logic.mkNumLeq(logic.mkNumMinus(x1, x0), logic.getTerm_NumOne());
    PTRef lit4 = logic.mkNumGeq(logic.mkNumMinus(x1, x0), logic.getTerm_NumOne());
    ModelBuilder builder(logic);
    builder.addVarValue(x0, logic.getTerm_NumZero());
    builder.addVarValue(x1, logic.getTerm_NumOne());
    auto model = builder.build();
    PTRef result = mbp.project(logic.mkAnd({lit1, lit2, lit3, lit4}), {x0}, *model);
    // result should be equivalent to "x1 = 1"
    std::cout << logic.printTerm(result) << std::endl;
    ASSERT_EQ(result, logic.mkAnd(logic.mkNumLeq(one, x1), logic.mkNumLeq(x1, one)));
}

TEST(test_MBP, test_SimpleDisjunction) {
    LRALogic logic;
    ModelBasedProjection mbp(logic);
    PTRef x0 = logic.mkNumVar("x0");
    PTRef x1 = logic.mkNumVar("x1");
    PTRef a = logic.mkBoolVar("a");
    PTRef b = logic.mkBoolVar("b");
    PTRef zero = logic.getTerm_NumZero();
    // (a or b) and (x0 <= 0) and (x0 >= x1))
    PTRef part1 = logic.mkOr(a,b);
    PTRef part2 = logic.mkNumLeq(x0, zero);
    PTRef part3 = logic.mkNumLeq(x1, x0);
    ModelBuilder builder(logic);
    builder.addVarValue(x0, zero);
    builder.addVarValue(x1, zero);
    builder.addVarValue(a, logic.getTerm_true());
    builder.addVarValue(b, logic.getTerm_true());
    auto model = builder.build();
    PTRef result = mbp.project(logic.mkAnd({part1, part2, part3}), {x0}, *model);
    // NOTE: Check that the result is not unnecessary strict.
    // Ideally the result should be "(a or b) and (x1 <= 0)"
    std::cout << logic.printTerm(result) << std::endl;
    ASSERT_TRUE(logic.isAnd(result));
    PTRef expectedConjunct = logic.mkNumLeq(x1, zero);
    bool found = false;
    for (int i = 0; i < logic.getPterm(result).size(); ++i) {
        found = found or logic.getPterm(result)[i] == expectedConjunct;
    }
    ASSERT_TRUE(found);
}
