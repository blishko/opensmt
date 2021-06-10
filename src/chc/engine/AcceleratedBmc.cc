//
// Created by Martin Blicha on 01.06.21.
//

#include "AcceleratedBmc.h"
#include "TransformationUtils.h"
#include "TransitionSystem.h"
#include "ModelBasedProjection.h"

#include "MainSolver.h"

GraphVerificationResult AcceleratedBmc::solve(ChcDirectedHyperGraph & system) {
    throw std::logic_error("Not supported yet!");
}

GraphVerificationResult AcceleratedBmc::solve(const ChcDirectedGraph & system) {
    if (isTransitionSystem(system)) {
        auto ts = toTransitionSystem(system, logic);
        return solveTransitionSystem(*ts);
    }
    else {
        throw std::logic_error("BMC cannot handle general CHC systems yet!");
    }
}

PTRef AcceleratedBmc::getInit() const {
    return init;
}

PTRef AcceleratedBmc::getTransitionRelation() const {
    return transition;
}

PTRef AcceleratedBmc::getQuery() const {
    return query;
}

PTRef AcceleratedBmc::getExactPower(unsigned short power) const {
    assert(power >= 0 and power < exactPowers.size());
    return exactPowers[power];
}

void AcceleratedBmc::storeExactPower(unsigned short power, PTRef tr) {
    assert(power >= 0);
//    std::cout << "Strengthening exact reachability on level " << power << " with " << logic.printTerm(tr) << std::endl;
    exactPowers.growTo(power + 1, PTRef_Undef);
    PTRef current = exactPowers[power];
    PTRef toStore = current == PTRef_Undef ? tr : logic.mkAnd(current, tr);
    exactPowers[power] = toStore;
}

PTRef AcceleratedBmc::getLessThanPower(unsigned short power) const {
    assert(power >= 0 and power < lessThanPowers.size());
    return lessThanPowers[power];
}

void AcceleratedBmc::storeLessThanPower(unsigned short power, PTRef tr) {
//    std::cout << "Strengthening less-than reachability on level " << power << " with " << logic.printTerm(tr) << std::endl;
    assert(power >= 0);
    lessThanPowers.growTo(power + 1, PTRef_Undef);
    PTRef current = lessThanPowers[power];
    PTRef toStore = current == PTRef_Undef ? tr : logic.mkAnd(current, tr);
    lessThanPowers[power] = toStore;
}

vec<PTRef> AcceleratedBmc::getStateVars(int version) {
    vec<PTRef> versioned;
    TimeMachine timeMachine(logic);
    for (PTRef var : stateVariables) {
        versioned.push(timeMachine.sendVarThroughTime(var, version));
    }
    return versioned;
}


GraphVerificationResult AcceleratedBmc::solveTransitionSystem(TransitionSystem & system) {
    resetTransitionSystem(system);
    // TODO: Check 0 step separetely
    unsigned short power = 1;
    while (true) {
        auto res = checkPower(power);
        if (res == VerificationResult::UNSAFE) {
            return GraphVerificationResult(res);
        }
        ++power;
    }
}

bool isReachable (AcceleratedBmc::QueryResult res) { return res.result == AcceleratedBmc::QueryResult::ReachabilityResult::REACHABLE; };
bool isUnreachable (AcceleratedBmc::QueryResult res) { return res.result == AcceleratedBmc::QueryResult::ReachabilityResult::UNREACHABLE; };
PTRef extractReachableTarget (AcceleratedBmc::QueryResult res) { return res.refinedTarget; };


VerificationResult AcceleratedBmc::checkPower(unsigned short power) {
    assert(power > 0);
    // First compute the exact power using the concatenation of previous one
    auto res = reachabilityQueryExact(init, query, power);
    if (isReachable(res)) {
        return VerificationResult::UNSAFE;
    }
    // Second compute the <2^n transition relation using information from previous level;
    res = reachabilityQueryLessThan(init, query, power);
    if (isReachable(res)) {
        return VerificationResult::UNSAFE;
    } else if (isUnreachable(res)) {
        return VerificationResult::SAFE;
    } else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
}

AcceleratedBmc::QueryResult AcceleratedBmc::reachabilityExactOneStep(PTRef from, PTRef to) {
    // TODO: this solver can be persistent and used incrementally
    QueryResult result;
    SMTConfig config;
    MainSolver solver(logic, config, "1-step checker");
    solver.insertFormula(getExactPower(1));
    PTRef goal = getNextVersion(to);
    solver.insertFormula(logic.mkAnd(from, goal));
    auto res = solver.check();
    if (res == s_True) {
        result.result = QueryResult::ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = QueryResult::ReachabilityResult::UNREACHABLE;
        return result;
    }
    throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
}

AcceleratedBmc::QueryResult AcceleratedBmc::reachabilityExactZeroStep(PTRef from, PTRef to) {
    QueryResult result;
    SMTConfig config;
    MainSolver solver(logic, config, "0-step checker");
    solver.insertFormula(logic.mkAnd(from, to));
    auto res = solver.check();
    if (res == s_True) {
        result.result = QueryResult::ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = QueryResult::ReachabilityResult::UNREACHABLE;
        return result;
    }
    throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in exactly 2^n steps (n is 'power').
 * We do this using the (n-1)th abstraction of the transition relation and check 2-step reachability in this abstraction.
 * If 'to' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n.
 */
AcceleratedBmc::QueryResult AcceleratedBmc::reachabilityQueryExact(PTRef from, PTRef to, unsigned short power) {
//    std::cout << "Checking exact reachability on level " << power << std::endl;
//        std::cout << "Checking exact reachability on level " << power << " from " << logic.printTerm(from) << " to " << logic.printTerm(to) << std::endl;
    assert(power >= 1);
    if (power == 1) { // Basic check with real transition relation
        return reachabilityExactOneStep(from, to);
    }
    QueryResult result;
    PTRef goal = getNextVersion(to, 2);
    while(true) {
        SMTConfig config;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        MainSolver solver(logic, config, "Exact reachability checker");
        PTRef previousTransition = getExactPower(power - 1);
        PTRef translatedPreviousTransition = getNextVersion(previousTransition);
        PTRef twoStepTransition = logic.mkAnd(previousTransition, translatedPreviousTransition);
        // TODO: assert from and to are current-state formulas
        solver.insertFormula(twoStepTransition);
        solver.insertFormula(logic.mkAnd(from, goal));
//        std::cout << "The transition is " << logic.printTerm(twoStepTransition) << std::endl;
        auto res = solver.check();
        if (res == s_False) {
            auto itpContext = solver.getInterpolationContext();
            vec<PTRef> itps;
            ipartitions_t mask = 1;
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 1);
            PTRef itp = itps[0];
            // replace next-next variables with next-variables
            itp = cleanInterpolant(itp);
            storeExactPower(power, itp);
            result.result = QueryResult::ReachabilityResult::UNREACHABLE;
            return result;
        } else if (res == s_True) {
            auto model = solver.getModel();
            if (power == 2) { // Base case, the 2 steps of the exact transition relation have been used
                result.result = QueryResult::ReachabilityResult::REACHABLE;
                result.refinedTarget = getNextVersion(refineTwoStepTarget(from, twoStepTransition, goal, *model), -2);
                return result;
            }
            // Create the three states corresponding to current, next and next-next variables from the query
//            PTRef modelMidpoint = getNextVersion(extractStateFromModel(getStateVars(1), *model), -1);
            PTRef nextState = getNextVersion(extractMidPoint(from, previousTransition, translatedPreviousTransition, goal, *model), -1);
//            std::cout << "Midpoint single point: " << logic.printTerm(modelMidpoint) << '\n';
//            std::cout << "Midpoint from MBP: " << logic.printTerm(nextState) << std::endl;
            // check the reachability using lower level abstraction
            auto subQueryRes = reachabilityQueryExact(from, nextState, power - 1);
            if (isUnreachable(subQueryRes)) {
                assert(getExactPower(power - 1) != previousTransition);
                continue; // We need to re-check this level with refined abstraction
            } else {
                assert(isReachable(subQueryRes));
                // TODO: check that this is really a subset of the original midpoint
                nextState = extractReachableTarget(subQueryRes);
                if (nextState == PTRef_Undef) {
                    throw std::logic_error("Refined reachable target not set in subquery!");
                }
            }
            // here the first half of the found path is feasible, check the second half
            subQueryRes = reachabilityQueryExact(nextState, to, power - 1);
            if (isUnreachable(subQueryRes)) {
                assert(getExactPower(power - 1) != previousTransition);
                continue; // We need to re-check this level with refined abstraction
            }
            assert(isReachable(subQueryRes));
            // both halves of the found path are feasible => this path is feasible!
            return subQueryRes;
        } else {
            throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
        }
    }
}

/*
 * Check if 'to' is reachable from 'from' (these are state formulas) in less than 2^n steps (n is 'power').
 * We do this using the (n-1)th abstractions of the transition relation (both exact and less-than).
 * Reachability in <2^n steps can happen if it is reachable in <2^(n-1) steps or if it is reachable in 2^(n-1) + <2^(n-1) steps.
 * If 'to' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n.
 */
AcceleratedBmc::QueryResult AcceleratedBmc::reachabilityQueryLessThan(PTRef from, PTRef to, unsigned short power) {
//    std::cout << "Checking less-than reachability on level " << power << std::endl;
//        std::cout << "Checking less-than reachability on level " << power << " from " << logic.printTerm(from) << " to " << logic.printTerm(to) << std::endl;
    assert(power >= 1);
    if (power == 1) {
        return reachabilityExactZeroStep(from, to);
    }
    QueryResult result;
    assert(power >= 2);
    PTRef goal = getNextVersion(to, 2);
    while(true) {
        SMTConfig config;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        MainSolver solver(logic, config, "Less-than reachability checker");
        PTRef previousLessThanTransition = getLessThanPower(power - 1);
        PTRef previousExactTransition = getExactPower(power - 1);
        PTRef translatedLessThanTransition = getNextVersion(previousLessThanTransition);
        PTRef currentToNextNextPreviousLessThanTransition = shiftOnlyNextVars(previousLessThanTransition);
        PTRef twoStepTransition = logic.mkOr(
            currentToNextNextPreviousLessThanTransition,
            logic.mkAnd(previousExactTransition, translatedLessThanTransition)
        );
        // TODO: assert from and to are current-state formulas
        solver.insertFormula(twoStepTransition);
        solver.insertFormula(logic.mkAnd(from, goal));
        auto res = solver.check();
        if (res == s_False) {
            auto itpContext = solver.getInterpolationContext();
            vec<PTRef> itps;
            ipartitions_t mask = 1;
            itpContext->getSingleInterpolant(itps, mask);
            assert(itps.size() == 1);
            PTRef itp = itps[0];
            // replace next-next variables with next-variables
            itp = cleanInterpolant(itp);
            storeLessThanPower(power, itp);
            result.result = AcceleratedBmc::QueryResult::ReachabilityResult::UNREACHABLE;
            return result;
        } else if (res == s_True) {
            auto model = solver.getModel();
            if (model->evaluate(currentToNextNextPreviousLessThanTransition) == logic.getTerm_true()) {
                // First disjunct was responsible for the positive answer, check it
                if (power == 2) { // This means the goal is reachable in 0 steps, no need to re-check anythin
                    result.result = AcceleratedBmc::QueryResult::ReachabilityResult::REACHABLE;
                    result.refinedTarget = logic.mkAnd(from, to); // TODO: check if this is needed
                    return result;
                }
                auto subQueryRes = reachabilityQueryLessThan(from, to, power - 1);
                if (isReachable(subQueryRes)) {
                    return subQueryRes;
                } else {
                    assert(isUnreachable(subQueryRes));
                    assert(getLessThanPower(power - 1) != previousLessThanTransition);
                    continue;
                }
            } else {
                // Second disjunct was responsible for the positive answer
                assert(model->evaluate(logic.mkAnd(previousExactTransition, translatedLessThanTransition)) == logic.getTerm_true());
                if (power == 2) { // Since it was not reachable in 0 steps (checked above), here it means it was reachable in exactly 1 step
                    result.result = QueryResult::ReachabilityResult::REACHABLE;
                    // TODO: this could be simplified, but I need refineOneStepTarget
                    result.refinedTarget = getNextVersion(refineTwoStepTarget(from, logic.mkAnd(previousExactTransition, translatedLessThanTransition), goal, *model), -2);
                    return result;
                }
                PTRef nextState = getNextVersion(extractMidPoint(from, previousExactTransition, translatedLessThanTransition, goal, *model), -1);
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQueryExact(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    assert(getExactPower(power - 1) != previousExactTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    nextState = extractReachableTarget(subQueryRes);
                    if (nextState == PTRef_Undef) {
                        throw std::logic_error("Refined reachable target not set in subquery!");
                    }
                }
                // here the first half of the found path is feasible, check the second half
                subQueryRes = reachabilityQueryLessThan(nextState, to, power - 1);
                if (isUnreachable(subQueryRes)) {
                    assert(getExactPower(power - 1) != translatedLessThanTransition);
                    continue; // We need to re-check this level with refined abstraction
                }
                assert(isReachable(subQueryRes));
                // both halves of the found path are feasible => this path is feasible!
                return subQueryRes;
            }
        } else {
            throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
        }
    }
}

PTRef AcceleratedBmc::extractStateFromModel(vec<PTRef> const & vars, Model & model) {
    vec<PTRef> eqs;
    for (PTRef var : vars) {
        PTRef val = model.evaluate(var);
        assert(val != PTRef_Undef);
        eqs.push(logic.mkEq(var, val));
    }
    return logic.mkAnd(eqs);
}

// TODO: unify cleanInterpolant and shiftOnlyNextVars. They are dual to each other and very similar
PTRef AcceleratedBmc::cleanInterpolant(PTRef itp) {
    TermUtils utils(logic);
    auto itpVars = utils.getVars(itp);
    auto currentVars = getStateVars(0);
    auto nextnextVars = getStateVars(2);
    assert(std::all_of(itpVars.begin(), itpVars.end(), [&](PTRef var) {
        return std::find(currentVars.begin(), currentVars.end(), var) != currentVars.end() or
            std::find(nextnextVars.begin(), nextnextVars.end(), var) != nextnextVars.end();
    }));
    auto nextVars = getStateVars(1);
    TermUtils::substitutions_map subst;
    assert(nextVars.size() == nextnextVars.size());
    for (int i = 0; i < nextVars.size(); ++i) {
        subst.insert({nextnextVars[i], nextVars[i]});
    }
    return utils.varSubstitute(itp, subst);
}

PTRef AcceleratedBmc::shiftOnlyNextVars(PTRef fla) {
    TermUtils utils(logic);
    auto vars = utils.getVars(fla);
    auto currentVars = getStateVars(0);
    auto nextVars = getStateVars(1);
    assert(std::all_of(vars.begin(), vars.end(), [&](PTRef var) {
        return std::find(currentVars.begin(), currentVars.end(), var) != currentVars.end() or
               std::find(nextVars.begin(), nextVars.end(), var) != nextVars.end();
    }));
    auto nextnextVars = getStateVars(2);
    TermUtils::substitutions_map subst;
    assert(nextVars.size() == nextnextVars.size());
    for (int i = 0; i < nextVars.size(); ++i) {
        subst.insert({nextVars[i], nextnextVars[i]});
    }
    return utils.varSubstitute(fla, subst);
}

void AcceleratedBmc::resetTransitionSystem(TransitionSystem const & system) {
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);
    this->stateVariables.clear();
    this->auxiliaryVariables.clear();
    auto stateVars = system.getStateVars();
    auto auxVars = system.getAuxiliaryVars();
    TermUtils::substitutions_map substMap;
    for (PTRef var : stateVars) {
        PTRef versionedVar = timeMachine.getVarVersionZero(var);
        this->stateVariables.push(versionedVar);
        substMap.insert({var, versionedVar});
    }
    for (PTRef var : auxVars) {
        PTRef versionedVar = timeMachine.getVarVersionZero(var);
        this->auxiliaryVariables.push(versionedVar);
        substMap.insert({var, versionedVar});
    }
    this->init = utils.varSubstitute(system.getInit(), substMap);
    this->init = utils.toNNF(this->init);
    this->query = utils.varSubstitute(system.getQuery(), substMap);
    this->query = utils.toNNF(this->query);
    auto nextStateVars = system.getNextStateVars();
    vec<PTRef> currentNextEqs;
    assert(nextStateVars.size() == stateVars.size());
    for (int i = 0; i < nextStateVars.size(); ++i) {
        PTRef nextStateVersioned = timeMachine.sendVarThroughTime(substMap[stateVars[i]], 1);
        substMap.insert({nextStateVars[i], nextStateVersioned});
        currentNextEqs.push(logic.mkEq(stateVariables[i], nextStateVersioned));
    }
    this->transition = utils.varSubstitute(system.getTransition(), substMap);
    this->transition = utils.toNNF(this->transition);
    this->exactPowers.clear();
    exactPowers.push(logic.mkAnd(currentNextEqs));
    exactPowers.push(transition);
    lessThanPowers.push(PTRef_Undef); // <0 does not make sense
    lessThanPowers.push(exactPowers[0]); // <1 is just exact 0
//    std::cout << "Init: " << logic.printTerm(init) << std::endl;
//    std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
//    std::cout << "Query: " << logic.printTerm(query) << std::endl;
}

PTRef AcceleratedBmc::getNextVersion(PTRef currentVersion, int shift) {
    return TimeMachine(logic).sendFlaThroughTime(currentVersion, shift);
}

/*
PTRef AcceleratedBmc::extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model & model) {
    ModelBasedProjection mbp(logic);
    PTRef firstHalf = logic.mkAnd(start, firstTransition);
    auto nextStateVars = getStateVars(1);
    TermUtils utils(logic);
    auto varsInFirstHalf = utils.getVars(firstHalf);
    vec<PTRef> toEliminate;
    for (PTRef var : varsInFirstHalf) {
        auto it = std::find(nextStateVars.begin(), nextStateVars.end(), var);
        if (it == nextStateVars.end()) {
            toEliminate.push(var);
        }
    }
    PTRef midPointFromBeginning = mbp.project(firstHalf, toEliminate, model);

    PTRef secondHalf = logic.mkAnd(secondTransition, goal);
    auto varsInSecondHalf = utils.getVars(secondHalf);
    toEliminate.clear();
    for (PTRef var : varsInSecondHalf) {
        auto it = std::find(nextStateVars.begin(), nextStateVars.end(), var);
        if (it == nextStateVars.end()) {
            toEliminate.push(var);
        }
    }
    PTRef midPointFromEnd = mbp.project(secondHalf, toEliminate, model);
    return logic.mkAnd(midPointFromBeginning, midPointFromEnd);
}
*/

PTRef AcceleratedBmc::extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model & model) {
    ModelBasedProjection mbp(logic);
    PTRef transitionQuery = logic.mkAnd({start, firstTransition, secondTransition, goal});
    assert(model.evaluate(transitionQuery) == logic.getTerm_true());
    auto nextStateVars = getStateVars(1);
    TermUtils utils(logic);
    auto vars = utils.getVars(transitionQuery);
    vec<PTRef> toEliminate;
    for (PTRef var : vars) {
        auto it = std::find(nextStateVars.begin(), nextStateVars.end(), var);
        if (it == nextStateVars.end()) {
            toEliminate.push(var);
        }
    }
    PTRef midPoint = mbp.project(transitionQuery, toEliminate, model);
    return midPoint;
}

PTRef AcceleratedBmc::refineTwoStepTarget(PTRef start, PTRef twoSteptransition, PTRef goal, Model & model) {
    ModelBasedProjection mbp(logic);
    PTRef transitionQuery = logic.mkAnd({start, twoSteptransition, goal});
    assert(model.evaluate(transitionQuery) == logic.getTerm_true());
    auto nextnextStateVars = getStateVars(2);
    TermUtils utils(logic);
    auto vars = utils.getVars(transitionQuery);
    vec<PTRef> toEliminate;
    for (PTRef var : vars) {
        auto it = std::find(nextnextStateVars.begin(), nextnextStateVars.end(), var);
        if (it == nextnextStateVars.end()) {
            toEliminate.push(var);
        }
    }
    PTRef refinedGoal = mbp.project(transitionQuery, toEliminate, model);
    return refinedGoal;
}