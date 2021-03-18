//
// Created by Martin Blicha on 01.09.20.
//

#ifndef OPENSMT_NORMALIZER_H
#define OPENSMT_NORMALIZER_H

#include "ChcSystem.h"
#include "TermUtils.h"

#include "DivModRewriter.h"

#include <memory>
#include <unordered_map>

struct NormalizedChcSystem{
    std::unique_ptr<ChcSystem> normalizedSystem;
    CanonicalPredicateRepresentation canonicalPredicateRepresentation;
};

class Normalizer{
    Logic& logic;
    TimeMachine timeMachine;
    std::unordered_map<SymRef, std::vector<PTRef>, SymRefHash> predicateToUniqVars;
    vec<PTRef> topLevelEqualities;
    long long counter = 0;

    ChClause normalize(ChClause const& clause) {
        auto const& head = clause.head;
        auto const& body = clause.body;
        topLevelEqualities.clear();
        ChcHead newHead = normalize(head);
        ChcBody newBody = normalize(body);
        ChClause res = eliminateRedundantVariables(ChClause{.head = std::move(newHead), .body = std::move(newBody)});
        topLevelEqualities.clear();
        return res;
    }

    ChcHead normalize(ChcHead const& head) {
        auto predicate = head.predicate.predicate;
        auto predicateSymbol = logic.getSymRef(predicate);
        if (predicateToUniqVars.count(predicateSymbol) == 0) {
            createUniqueRepresentation(predicate);
        }
        assert(predicateToUniqVars.count(predicateSymbol) > 0);
        auto const& representation = predicateToUniqVars.at(predicateSymbol);
        assert(representation.size() == logic.getPterm(predicate).size());
        vec<PTRef> newArgs;
        for (int i = 0; i < representation.size(); ++i) {
            PTRef nextStateVar = timeMachine.sendVarThroughTime(representation[i], 1);
            PTRef arg = logic.getPterm(predicate)[i];
            topLevelEqualities.push(logic.mkEq(nextStateVar, arg));
            newArgs.push(nextStateVar);
        }
        PTRef newPredicate = logic.insertTerm(predicateSymbol, newArgs);
        return ChcHead{newPredicate};
    }

    void createUniqueRepresentation(PTRef predicate) {
        auto size = logic.getPterm(predicate).size();
        std::vector<PTRef> repre;
        for (int i = 0; i < size; ++i) {
            SRef sort = logic.getSortRef(logic.getPterm(predicate)[i]);
            std::string uniq_name = "x#" + std::to_string(counter++);
            PTRef versionlessVar = logic.mkVar(sort, uniq_name.c_str());
            repre.push_back(timeMachine.getVarVersionZero(versionlessVar));
        }
        predicateToUniqVars.insert(std::make_pair(logic.getSymRef(predicate), std::move(repre)));
    }

    ChcBody normalize(ChcBody const& body) {
        // uninterpreted part
        std::vector<UninterpretedPredicate> newUninterpretedPart;
        auto const& uninterpreted = body.uninterpretedPart;
        for (auto const& predicateWrapper : uninterpreted) {
            PTRef predicate = predicateWrapper.predicate;
            auto predicateSymbol = logic.getSymRef(predicate);
            if (predicateToUniqVars.count(predicateSymbol) == 0) {
                createUniqueRepresentation(predicate);
            }
            assert(predicateToUniqVars.count(predicateSymbol) > 0);
            auto const& representation = predicateToUniqVars.at(predicateSymbol);
            assert(representation.size() == logic.getPterm(predicate).size());
            vec<PTRef> newArgs;
            for (int i = 0; i < representation.size(); ++i) {
                PTRef arg = logic.getPterm(predicate)[i];
                PTRef narg = representation[i];
                topLevelEqualities.push(logic.mkEq(narg, arg));
                newArgs.push(narg);
            }
            PTRef newPredicate = logic.insertTerm(predicateSymbol, newArgs);
            newUninterpretedPart.push_back(UninterpretedPredicate{newPredicate});
        }
        if (uninterpreted.empty()) { createUniqueRepresentation(logic.getTerm_true()); }
        // interpreted part
        // just add the toplevel equalities collected for this clause; Here we assume 'head' has already been processed
        PTRef newInterpretedPart = logic.mkAnd(body.interpretedPart.fla, logic.mkAnd(topLevelEqualities));
        LIALogic * lialogic = dynamic_cast<LIALogic *>(&logic);
        if (lialogic) {
            newInterpretedPart = DivModRewriter(*lialogic).rewrite(newInterpretedPart);
        }
        return ChcBody{InterpretedFla{newInterpretedPart}, std::move(newUninterpretedPart)};
    }

    CanonicalPredicateRepresentation getCanonicalPredicateRepresentation() const {
        CanonicalPredicateRepresentation repre;
        for (auto const & entry : predicateToUniqVars) {
            auto const & vars = entry.second;
            vec<PTRef> stateVars;
            vec<PTRef> nextVars;
            for (PTRef var : vars) {
                assert(logic.isVar(var));
                assert(timeMachine.isVersioned(var));
                stateVars.push(var);
                nextVars.push(timeMachine.sendVarThroughTime(var, 1));
            }
            SymRef symbol = entry.first;
            repre.addRepresentation(symbol, logic.insertTerm(symbol, stateVars), logic.insertTerm(symbol, nextVars));
        }
        return repre;
    }

    ChClause eliminateRedundantVariables(ChClause && clause) {
        // For now we just eliminate variables left over after normalization
        // In the future we can do variable elimination here
        TermUtils utils(logic);
        std::unordered_set<PTRef, PTRefHash> validVars;
        // vars from head
        {
            auto headVars = utils.getVarsFromPredicateInOrder(clause.head.predicate.predicate);
            validVars.insert(headVars.begin(), headVars.end());
        }
        // vars from uninterpreted body
        for (auto const & pred : clause.body.uninterpretedPart) {
            auto vars = utils.getVarsFromPredicateInOrder(pred.predicate);
            validVars.insert(vars.begin(), vars.end());
        }
        // build substitution map
        std::unordered_map<PTRef, PTRef, PTRefHash> subst;
        for (PTRef eq : topLevelEqualities) {
            PTRef lhs = logic.getPterm(eq)[0];
            PTRef rhs = logic.getPterm(eq)[1];
            if (logic.isVar(lhs) && validVars.find(lhs) == validVars.end()) {
                if (subst.count(lhs) == 0) {
                    subst.insert({lhs, rhs});
                }
                continue;
            }
            if (logic.isVar(rhs) && validVars.find(rhs) == validVars.end()) {
                if (subst.count(rhs) == 0) {
                    subst.insert({rhs, lhs});
                }
            }
        }
        PTRef newInterpretedBody = utils.varSubstitute(clause.body.interpretedPart.fla, subst);
        ////////////////////// DEALING with LOCAL VARIABLES /////////////////////////
        {
            // Let's try to do variable elimination already here
            auto allVars = utils.getVars(newInterpretedBody);
            auto isValidVar = [&validVars](PTRef var) {
                return validVars.find(var) != validVars.end();
            };
            auto newEnd = std::remove_if(allVars.begin(), allVars.end(), isValidVar);
            allVars.shrink_(allVars.end() - newEnd);
            if (allVars.size() > 0) {
//                std::cout << "Before variable elimination: " << logic.printTerm(newInterpretedBody) << std::endl;
                newInterpretedBody = TrivialQuantifierElimination(logic).eliminateVars(allVars, newInterpretedBody);
//                std::cout << "After variable elimination: " << logic.printTerm(newInterpretedBody) << std::endl;
            }
            auto varsAfterElimination = utils.getVars(newInterpretedBody);
            auto localsEnd = std::remove_if(varsAfterElimination.begin(), varsAfterElimination.end(), isValidVar);
            if (localsEnd != varsAfterElimination.begin()) {
                // there are some local variables left, rename them and make them versioned
                subst.clear();
                for (auto it = varsAfterElimination.begin(); it != localsEnd; ++it) {
                    PTRef localVar = *it;
                    SRef sort = logic.getSortRef(localVar);
                    std::string uniq_name = "aux#" + std::to_string(counter++);
                    PTRef versionlessVar = logic.mkVar(sort, uniq_name.c_str());
                    PTRef renamed = timeMachine.getVarVersionZero(versionlessVar);
                    subst.insert({localVar, renamed});
                }
                newInterpretedBody = utils.varSubstitute(newInterpretedBody, subst);
            }
        }
        ////////////////////// END OF DEALING with LOCAL VARIABLES /////////////////////////

        return ChClause{clause.head, ChcBody{newInterpretedBody, clause.body.uninterpretedPart}};
    }

public:
    Normalizer(Logic& logic) : logic(logic), timeMachine(logic) {}

    NormalizedChcSystem normalize(ChcSystem const & system);

};


#endif //OPENSMT_NORMALIZER_H
