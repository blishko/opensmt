//
// Created by Martin Blicha on 01.06.21.
//

#include "AcceleratedBmc.h"
#include "TransformationUtils.h"
#include "TransitionSystem.h"

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

PTRef AcceleratedBmc::getPower(unsigned short power) const {
    assert(power >= 0 and power < exactPowers.size());
    return exactPowers[power];
}

void AcceleratedBmc::storePower(unsigned short power, PTRef tr) {
    assert(power >= 0);
    exactPowers.growTo(power + 1, PTRef_Undef);
    PTRef current = exactPowers[power];
    PTRef toStore = current == PTRef_Undef ? tr : logic.mkAnd(current, tr);
    exactPowers[power] = toStore;
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

VerificationResult AcceleratedBmc::checkPower(unsigned short power) {
    assert(power > 0);
    // First compute the exact power using the concatenation of previous one
    auto res = reachabilityQuery(init, query, power);
    if (res == ReachabilityResult::REACHABLE) {
        return VerificationResult::UNSAFE;
    }
    // TODO: temporary
    return VerificationResult::SAFE;
    // If reachable, we need to refine previous power, otherwise we need to interpolate to obtain the current power
    throw std::logic_error("Not implemented yet");
}

/*
 * Check if 'to' is reachabile from 'from' (these are state formulas) in exactly 2^n steps (n is 'power').
 * We do this using the (n-1)th abstraction of the transition relation and check 2-step reachability in this abstraction.
 * If 'from' is unreachable, we interpolate over the 2 step transition to obtain 1-step transition of level n.
 */
AcceleratedBmc::ReachabilityResult AcceleratedBmc::reachabilityQuery(PTRef from, PTRef to, unsigned short power) {
    assert(power >= 1);
    if (power == 1) { // Basic check with real transition relation
        // TODO: this solver can persistent and used incrementally
        SMTConfig config;
        MainSolver solver(logic, config, "1-step checker");
        solver.insertFormula(getPower(1));
        PTRef goal = getNextVersion(to);
        solver.insertFormula(logic.mkAnd(from, goal));
        auto res = solver.check();
        if (res == s_True) {
            return ReachabilityResult::REACHABLE;
        } else if (res == s_False) {
            return ReachabilityResult::UNREACHABLE;
        }
        throw std::logic_error("Accelerated BMC: Unexpected situation checking reachability");
    }
    auto isReachable = [](ReachabilityResult res) { return res == ReachabilityResult::REACHABLE; };
    auto isUnreachable = [](ReachabilityResult res) { return res == ReachabilityResult::UNREACHABLE; };
    while(true) {
        SMTConfig config;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        MainSolver solver(logic, config, "Reachability checker");
        PTRef previousTransition = getPower(power - 1);
        PTRef translatedPreviousTransition = getNextVersion(previousTransition);
        PTRef twoStepTransition = logic.mkAnd(previousTransition, translatedPreviousTransition);
        // TODO: assert from and to are current-state formulas
        PTRef goal = getNextVersion(to, 2);
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
            storePower(power, itp);
            return AcceleratedBmc::ReachabilityResult::UNREACHABLE;
        } else if (res == s_True) {
            auto model = solver.getModel();
            // Create the three states corresponding to current, next and next-next variables from the query
            auto currentVars = getStateVars(0);
            auto nextVars = getStateVars(1);
            auto nextnextVars = getStateVars(2);
            PTRef currentState = extractStateFromModel(currentVars, *model);
            PTRef nextState = getNextVersion(extractStateFromModel(nextVars, *model), -1);
            PTRef nextnextState = getNextVersion(extractStateFromModel(nextnextVars, *model), -2);
            // check the reachability using lower level abstraction
            auto subQueryRes = reachabilityQuery(currentState, nextState, power - 1);
            if (isUnreachable(subQueryRes)) {
                assert(getPower(power - 1) != previousTransition);
                continue; // We need to re-check this level with refined abstraction
            }
            // here the first half of the found path is feasible, check the second half
            subQueryRes = reachabilityQuery(nextState, nextnextState, power - 1);
            if (isUnreachable(subQueryRes)) {
                assert(getPower(power - 1) != previousTransition);
                continue; // We need to re-check this level with refined abstraction
            }
            assert(isReachable(subQueryRes));
            // both halves of the found path are feasible => this path is feasible!
            return ReachabilityResult::REACHABLE;
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

void AcceleratedBmc::resetTransitionSystem(TransitionSystem const & system) {
    TimeMachine timeMachine(logic);
    TermUtils utils(logic);
    this->stateVariables.clear();
    auto stateVars = system.getStateVars();
    TermUtils::substitutions_map substMap;
    for (PTRef var : stateVars) {
        PTRef versionedVar = timeMachine.getVarVersionZero(var);
        this->stateVariables.push(versionedVar);
        substMap.insert({var, versionedVar});
    }
    this->init = utils.varSubstitute(system.getInit(), substMap);
    this->query = utils.varSubstitute(system.getQuery(), substMap);
    auto nextStateVars = system.getNextStateVars();
    vec<PTRef> currentNextEqs;
    assert(nextStateVars.size() == stateVars.size());
    for (int i = 0; i < nextStateVars.size(); ++i) {
        PTRef nextStateVersioned = timeMachine.sendVarThroughTime(substMap[stateVars[i]], 1);
        substMap.insert({nextStateVars[i], nextStateVersioned});
        currentNextEqs.push(logic.mkEq(stateVariables[i], nextStateVersioned));
    }
    this->transition = utils.varSubstitute(system.getTransition(), substMap);
    this->exactPowers.clear();
    exactPowers.push(logic.mkAnd(currentNextEqs));
    exactPowers.push(transition);
}

PTRef AcceleratedBmc::getNextVersion(PTRef currentVersion, int shift) {
    return TimeMachine(logic).sendFlaThroughTime(currentVersion, shift);
}