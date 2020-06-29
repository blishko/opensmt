//
// Created by Martin Blicha on 20.06.20.
//

#include <gtest/gtest.h>
#include <LRALogic.h>
#include <SMTConfig.h>
#include <Model.h>
#include <TermVisitor.h>

class LAImplicantTest : public ::testing::Test {
protected:
    LAImplicantTest() : logic{config} {}

    virtual void SetUp() {
        x = logic.mkNumVar("x");
        y = logic.mkNumVar("y");
        z = logic.mkNumVar("z");
        a = logic.mkBoolVar("a");
        b = logic.mkBoolVar("b");
        trueTerm = logic.getTerm_true();
        falseTerm = logic.getTerm_false();
    }

    SMTConfig config;
    LRALogic logic;
    PTRef x;
    PTRef y;
    PTRef z;
    PTRef a;
    PTRef b;
    PTRef trueTerm;
    PTRef falseTerm;
};

TEST_F(LAImplicantTest, test_singleClause) {
    vec<PTRef> args {a, b, logic.mkNumLeq(x,y)};
    PTRef clause_singleLit = logic.mkOr(args);

    Model::Evaluation eval {
            std::make_pair(x, logic.getTerm_NumOne()),
            //std::make_pair(y, logic.getTerm_NumZero()),
            //std::make_pair(z, logic.getTerm_NumOne()),
            std::make_pair(a, logic.getTerm_true()),
            std::make_pair(b, logic.getTerm_false())
    };
    ExplicitModel model {logic, eval};
    {
        auto implicant = logic.getImplicant(clause_singleLit, model);
        // single literal is satisfied in the clause
        ASSERT_EQ(implicant.size(), 1);
        EXPECT_EQ(implicant.begin()->tr, a);
        EXPECT_EQ(implicant.begin()->sgn, l_True);
    }
    {
        args[1] = logic.mkNot(b);
        PTRef clause_twoLits = logic.mkOr(args);
        auto implicant = logic.getImplicant(clause_twoLits, model);
        // single literal is satisfied in the clause
        EXPECT_LE(implicant.size(), 2);
        ASSERT_GE(implicant.size(), 1);
        PtAsgn literal = *implicant.begin();
        EXPECT_TRUE((literal.tr == a && literal.sgn == l_True) || (literal.tr == b && literal.sgn == l_False));
    }
}

TEST_F(LAImplicantTest, test_singleCube) {
    PTRef ineq = logic.mkNumLeq(y,x);
    ASSERT_TRUE(logic.isAtom(ineq));
    vec<PTRef> args {a, logic.mkNot(b), ineq};
    PTRef cube = logic.mkAnd(args);

    Model::Evaluation eval {
            std::make_pair(x, logic.getTerm_NumOne()),
            std::make_pair(y, logic.getTerm_NumZero()),
            std::make_pair(z, logic.getTerm_NumOne()),
            std::make_pair(a, logic.getTerm_true()),
            std::make_pair(b, logic.getTerm_false())
    };
    ExplicitModel model {logic, eval};
    auto implicant = logic.getImplicant(cube, model);
    // single literal is satisfied in the clause
    ASSERT_EQ(implicant.size(), 3);
    EXPECT_TRUE(implicant.find(PtAsgn(a,l_True)) != implicant.end());
    EXPECT_TRUE(implicant.find(PtAsgn(b,l_False)) != implicant.end());
    EXPECT_TRUE(implicant.find(PtAsgn(ineq,l_True)) != implicant.end());
}

TEST_F(LAImplicantTest, test_simpleCNF) {
    PTRef cnf = logic.mkAnd(
        {
            logic.mkOr({a, b}),
            logic.mkOr({logic.mkNot(a), logic.mkNot(b)}),
            logic.mkOr({logic.mkNot(b), a})
        }
    );

    Model::Evaluation eval {
            std::make_pair(a, logic.getTerm_true()),
            std::make_pair(b, logic.getTerm_false())
    };
    ExplicitModel model {logic, eval};
    ASSERT_EQ(model.evaluate(cnf), trueTerm);
    auto implicant = logic.getImplicant(cnf, model);
    // single literal is satisfied in the clause
    ASSERT_EQ(implicant.size(), 2);
    EXPECT_TRUE(implicant.find(PtAsgn(a,l_True)) != implicant.end());
    EXPECT_TRUE(implicant.find(PtAsgn(b,l_False)) != implicant.end());
}

TEST_F(LAImplicantTest, test_simpleNNF) {
    PTRef c = logic.mkBoolVar("c");

    PTRef nnf = logic.mkOr(
        {
            logic.mkAnd({
                            logic.mkOr({a, b}),
                            logic.mkOr({a, c})
                        }),
            logic.mkAnd({
                            logic.mkOr({a, b}),
                            logic.mkOr({b, c})
                        }),
        }
    );

    {
        Model::Evaluation eval {
            std::make_pair(a, logic.getTerm_true()),
        };
        ExplicitModel model{logic, eval};
        ASSERT_EQ(model.evaluate(nnf), trueTerm);
        auto implicant = logic.getImplicant(nnf, model);
        // single literal is satisfied in the clause
        ASSERT_EQ(implicant.size(), 1);
        EXPECT_TRUE(implicant.find(PtAsgn(a, l_True)) != implicant.end());
    }
    {
        Model::Evaluation eval {
            std::make_pair(b, logic.getTerm_true()),
        };
        ExplicitModel model{logic, eval};
        ASSERT_EQ(model.evaluate(nnf), trueTerm);
        auto implicant = logic.getImplicant(nnf, model);
        // single literal is satisfied in the clause
        ASSERT_EQ(implicant.size(), 1);
        EXPECT_TRUE(implicant.find(PtAsgn(b, l_True)) != implicant.end());
    }
}
