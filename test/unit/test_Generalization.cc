//
// Created by Martin Blicha on 24.06.20.
//

#include <gtest/gtest.h>
#include <LRALogic.h>
#include <SMTConfig.h>
#include <Model.h>


class LAModelTest : public ::testing::Test {
protected:
    LAModelTest(): logic{config} {}
    virtual void SetUp() {
        x = logic.mkNumVar("x");
        y = logic.mkNumVar("y");
        z = logic.mkNumVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
    }
    SMTConfig config;
    LRALogic logic;
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef a;
    PTRef b;

    std::unique_ptr<Model> getModel() {
        Model::Evaluation eval {
            std::make_pair(x, logic.getTerm_NumOne()),
            std::make_pair(y, logic.mkConst("2")),
            std::make_pair(z, logic.getTerm_NumZero()),
            std::make_pair(a, logic.getTerm_true()),
            std::make_pair(b, logic.getTerm_false())
        };
        return std::unique_ptr<Model>(new ExplicitModel(logic, eval));
    }

};

TEST_F(LAModelTest, test_singleVarSingleBounds) {
    PTRef lowerBoundX = logic.mkNumLeq(logic.getTerm_NumZero(), x);
    PTRef upperBoundX = logic.mkNumLeq(y, x);
    Logic::implicant_t literals {PtAsgn(lowerBoundX, l_True), PtAsgn(upperBoundX, l_False)};
    vec<PTRef> vars {x};
    auto model = getModel();
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model->evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, *model);
    PTRef expected = logic.mkNumLt(logic.getTerm_NumZero(), y);
    EXPECT_EQ(model->evaluate(res), logic.getTerm_true());
    EXPECT_EQ(res, expected);
}

TEST_F(LAModelTest, test_singleVarTwoUpperBounds) {
    PTRef lowerBoundX = logic.mkNumLeq(logic.getTerm_NumZero(), x);
    PTRef upperBoundX1 = logic.mkNumLeq(y, x);
    PTRef upperBoundX2 = logic.mkNumLeq(x, logic.mkNumPlus(vec<PTRef>{z, logic.mkConst("10")}));
    Logic::implicant_t literals {PtAsgn(lowerBoundX, l_True), PtAsgn(upperBoundX1, l_False),
                                 PtAsgn(upperBoundX2, l_True)};
    vec<PTRef> vars {x};
    auto model = getModel();
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model->evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, *model);
    PTRef expected = logic.mkAnd(
        logic.mkNumLt(logic.getTerm_NumZero(), y),
        logic.mkNumLt(logic.mkConst("-10"), z)
        ); // Underapproximation, not true quantifier elimination => "(z + 10 > 0)" and not "(z + 10 >= 0)"

    EXPECT_EQ(model->evaluate(res), logic.getTerm_true());
    EXPECT_EQ(res, expected);
}

TEST_F(LAModelTest, test_singleVarTwoUpperBounds_SecondModel) {
    PTRef lowerBoundX = logic.mkNumLeq(logic.getTerm_NumZero(), x);
    PTRef upperBoundX1 = logic.mkNumLeq(y, x);
    PTRef upperBoundX2 = logic.mkNumLeq(x, logic.mkNumPlus(vec<PTRef>{z, logic.mkConst("10")}));
    Logic::implicant_t literals {PtAsgn(lowerBoundX, l_True), PtAsgn(upperBoundX1, l_False),
                                 PtAsgn(upperBoundX2, l_True)};
    vec<PTRef> vars {x};
    ExplicitModel model(logic, Model::Evaluation {
        std::make_pair(x, logic.getTerm_NumOne()),
        std::make_pair(y, logic.mkConst("2")),
        std::make_pair(z, logic.mkConst("-9"))
    });
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model.evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, model);
    PTRef expected = logic.mkAnd(
        logic.mkNumLt(logic.mkConst("10"), logic.mkNumMinus(y,z)),
        logic.mkNumLt(logic.mkConst("-10"), z)
    );

//    std::cout << "Expected: " << logic.printTerm(expected) << '\n';
//    std::cout << "Result:   " << logic.printTerm(res) << std::endl;

    EXPECT_EQ(model.evaluate(res), logic.getTerm_true());
    EXPECT_EQ(res, expected);
}

TEST_F(LAModelTest, test_singleVarTwoUpperBounds_ThirdModel) {
    PTRef lowerBoundX = logic.mkNumLeq(logic.getTerm_NumZero(), x);
    PTRef upperBoundX1 = logic.mkNumLeq(y, x);
    PTRef upperBoundX2 = logic.mkNumLeq(x, logic.mkNumPlus(vec<PTRef>{z, logic.mkConst("10")}));
    // (0 <= x) and not (y <= x) and (x <= z + 10)
    Logic::implicant_t literals {PtAsgn(lowerBoundX, l_True), PtAsgn(upperBoundX1, l_False),
                                 PtAsgn(upperBoundX2, l_True)};
    vec<PTRef> vars {x};
    ExplicitModel model(logic, Model::Evaluation {
        std::make_pair(x, logic.getTerm_NumZero()),
        std::make_pair(y, logic.mkConst("2")),
        std::make_pair(z, logic.mkConst("-10"))
    });
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model.evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, model);
    // No expected, since there are two possibilities that could occur
    EXPECT_EQ(model.evaluate(res), logic.getTerm_true());
}

TEST_F(LAModelTest, test_singleVarSingleBounds_WithOtherAtoms) {
    PTRef lowerBoundX = logic.mkNumLeq(logic.getTerm_NumZero(), x);
    PTRef upperBoundX = logic.mkNumLeq(y, x);
    Logic::implicant_t literals {PtAsgn(lowerBoundX, l_True), PtAsgn(upperBoundX, l_False), PtAsgn(a, l_True)};
    vec<PTRef> vars {x};
    auto model = getModel();
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model->evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, *model);
    PTRef expected = logic.mkAnd(
        logic.mkNumLt(logic.getTerm_NumZero(), y),
        a
    );
    EXPECT_EQ(model->evaluate(res), logic.getTerm_true());
    EXPECT_EQ(res, expected);
}

TEST_F(LAModelTest, test_singleVarNoLowerBound) {
    PTRef upperBoundX1 = logic.mkNumLeq(y, x);
    PTRef upperBoundX2 = logic.mkNumLeq(logic.mkNumPlus(vec<PTRef>{z, logic.mkConst("42")}), x);
    Logic::implicant_t literals {PtAsgn(upperBoundX1, l_False), PtAsgn(upperBoundX2, l_False)};
    vec<PTRef> vars {x};
    auto model = getModel();
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model->evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, *model);
    PTRef expected = logic.getTerm_true();
    EXPECT_EQ(res, expected);
}

TEST_F(LAModelTest, test_singleBoolVarPositive) {
    Logic::implicant_t literals {PtAsgn(a, l_True)};
    vec<PTRef> vars {a};
    auto model = getModel();
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model->evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, *model);
    EXPECT_EQ(res, logic.getTerm_true());
}

TEST_F(LAModelTest, test_singleBoolVarNegative) {
    Logic::implicant_t literals {PtAsgn(b, l_False)};
    vec<PTRef> vars {b};
    auto model = getModel();
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model->evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, *model);
    EXPECT_EQ(res, logic.getTerm_true());
}

TEST_F(LAModelTest, test_eliminateVarNotPresent) {
    Logic::implicant_t literals {PtAsgn(b, l_False)};
    vec<PTRef> vars {a};
    auto model = getModel();
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model->evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, *model);
    PTRef expected = logic.mkNot(b);
    EXPECT_EQ(res, expected);
}

TEST_F(LAModelTest, test_eliminateBoolAndRealVar) {
    PTRef upperBoundX = logic.mkNumLeq(y, x);
    Logic::implicant_t literals {PtAsgn(upperBoundX, l_False), PtAsgn(a, l_True)};
    vec<PTRef> vars {a, x};
    auto model = getModel();
    for (PtAsgn literal : literals) {
        ASSERT_EQ(model->evaluate(literal.tr),literal.sgn == l_True ? logic.getTerm_true() : logic.getTerm_false());
    }
    auto res = logic.modelBasedProjection(vars, literals, *model);
    EXPECT_EQ(res, logic.getTerm_true());
}

TEST_F(LAModelTest, test_eliminateTwoRealVars) {
    PTRef xp = logic.mkNumVar("xp");
    PTRef yp = logic.mkNumVar("yp");
    PTRef one = logic.getTerm_NumOne();

    // A1: x' = x + 1
    // A2: y' = y + 1
    // A3: y' = 1

    PTRef a1 = logic.mkEq(xp, logic.mkNumPlus(vec<PTRef>{x, one}));
    PTRef a2 = logic.mkEq(yp, logic.mkNumPlus(vec<PTRef>{y, one}));
    PTRef a3 = logic.mkEq(yp, one);
    vec<PTRef> vars {xp, yp};
    ExplicitModel model(logic, Model::Evaluation {
        std::make_pair(x, logic.getTerm_NumZero()),
        std::make_pair(y, logic.getTerm_NumZero()),
        std::make_pair(xp, one),
        std::make_pair(yp, one)
    });
    vec<PTRef> args{a1, a2, a3};
    PTRef fla = logic.mkAnd(args);
    auto res = logic.generalize(fla, vars, model);

//    std::cout << logic.printTerm(res) << std::endl;

    EXPECT_EQ(model.evaluate(res), logic.getTerm_true());
}



