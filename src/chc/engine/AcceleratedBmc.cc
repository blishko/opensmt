//
// Created by Martin Blicha on 01.06.21.
//

#include "AcceleratedBmc.h"
#include "TransformationUtils.h"
#include "TransitionSystem.h"
#include "ModelBasedProjection.h"
#include "QuantifierElimination.h"

#include "MainSolver.h"

class SolverWrapperSingleUse : public SolverWrapper {
    Logic & logic;
    SMTConfig config;
    sstat lastResult = s_Undef;
    std::unique_ptr<MainSolver> solver;
public:
    SolverWrapperSingleUse(Logic & logic, PTRef transition) : logic(logic) {
        this->transition = transition;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
        solver.reset(new MainSolver(logic, config, "Reachability checker"));
        solver->insertFormula(transition);
        solver->insertFormula(query);
        lastResult = solver->check();
        if (lastResult == s_False) {
            return ReachabilityResult::UNREACHABLE;
        } else if (lastResult == s_True) {
            return ReachabilityResult::REACHABLE;
        } else {
            throw std::logic_error("Unexpected solver result in checking reachability!");
        }
    }

    void strenghtenTransition(PTRef nTransition) override {
        transition = logic.mkAnd(transition, nTransition);
    }

    std::unique_ptr<Model> lastQueryModel() override {
        if (not solver or lastResult != s_True) {
            throw std::logic_error("Invalid call for obtaining a model from solver");
        }
        return solver->getModel();
    }

    PTRef lastQueryTransitionInterpolant() override {
        if (not solver or lastResult != s_False) {
            throw std::logic_error("Invalid call for obtaining an interpolant from solver");
        }
        auto itpContext = solver->getInterpolationContext();
        vec<PTRef> itps;
        ipartitions_t mask = 1; // The transition was the first formula inserted
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        PTRef itp = itps[0];
        return itp;
    }
};

class SolverWrapperIncremental : public SolverWrapper {
    Logic & logic;
    SMTConfig config;
    sstat lastResult = s_Undef;
    std::unique_ptr<MainSolver> solver;

    unsigned allformulasInserted = 0;
    ipartitions_t mask = 0;
    bool pushed = false;

public:
    SolverWrapperIncremental(Logic & logic, PTRef transition) : logic(logic) {
//        std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
        this->transition = transition;
        const char * msg = "ok";
        config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        solver.reset(new MainSolver(logic, config, "incremental reachability checker"));
        solver->insertFormula(transition);
        opensmt::setbit(mask, allformulasInserted++);
    }

    ReachabilityResult checkConsistent(PTRef query) override {
//        std::cout << "Query: " << logic.printTerm(query) << std::endl;
        assert(not pushed);
        solver->push();
        pushed = true;
        solver->insertFormula(query);
        ++allformulasInserted;
        lastResult = solver->check();
        if (lastResult == s_False) {
            return ReachabilityResult::UNREACHABLE;
        } else if (lastResult == s_True) {
            return ReachabilityResult::REACHABLE;
        } else {
            throw std::logic_error("Unexpected solver result in checking reachability!");
        }
    }

    void strenghtenTransition(PTRef nTransition) override {
        assert(not pushed);
        solver->insertFormula(nTransition);
        opensmt::setbit(mask, allformulasInserted++);
//        std::cout << "Current number of formulas inserted: " << allformulasInserted << std::endl;
    }

    std::unique_ptr<Model> lastQueryModel() override {
        if (lastResult != s_True or not pushed) {
            throw std::logic_error("Invalid call for obtaining a model from solver");
        }
        auto model = solver->getModel();
        solver->pop();
        pushed = false;
        return std::move(model);
    }

    PTRef lastQueryTransitionInterpolant() override {
        if (lastResult != s_False or not pushed) {
            throw std::logic_error("Invalid call for obtaining an interpolant from solver");
        }
        auto itpContext = solver->getInterpolationContext();
        vec<PTRef> itps;
//        std::cout << "Current mask: "  << mask << std::endl;
        itpContext->getSingleInterpolant(itps, mask);
        assert(itps.size() == 1);
        PTRef itp = itps[0];
        solver->pop();
        pushed = false;
//        std::cout << logic.printTerm(itp) << std::endl;
        return itp;
    }
};

AcceleratedBmc::~AcceleratedBmc() {
    for (SolverWrapper* solver : reachabilitySolvers) {
        delete solver;
    }
}

GraphVerificationResult AcceleratedBmc::solve(ChcDirectedHyperGraph & system) {
    throw std::logic_error("Not supported yet!");
}

GraphVerificationResult AcceleratedBmc::solve(const ChcDirectedGraph & system) {
    if (isTransitionSystem(system)) {
        auto ts = toTransitionSystem(system, logic);
        return solveTransitionSystem(*ts, system);
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
//    std::cout << "Strengthening exact reachability on level " << power << " with " << logic.printTerm(tr) << std::endl;
    exactPowers.growTo(power + 1, PTRef_Undef);
    PTRef current = exactPowers[power];
    PTRef toStore = current == PTRef_Undef ? tr : logic.mkAnd(current, tr);
    exactPowers[power] = toStore;

    reachabilitySolvers.growTo(power + 2, nullptr);
    PTRef nextLevelTransitionStrengthening = logic.mkAnd(tr, getNextVersion(tr));
    if (not reachabilitySolvers[power + 1]) {
        reachabilitySolvers[power + 1] = new SolverWrapperIncremental(logic, nextLevelTransitionStrengthening);
//        reachabilitySolvers[power + 1] = new SolverWrapperSingleUse(logic, nextLevelTransitionStrengthening);
    } else {
        reachabilitySolvers[power + 1]->strenghtenTransition(nextLevelTransitionStrengthening);
    }
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

SolverWrapper* AcceleratedBmc::getExactReachabilitySolver(unsigned short power) const {
    assert(reachabilitySolvers.size() > power);
    return reachabilitySolvers[power];
}

vec<PTRef> AcceleratedBmc::getStateVars(int version) {
    vec<PTRef> versioned;
    TimeMachine timeMachine(logic);
    for (PTRef var : stateVariables) {
        versioned.push(timeMachine.sendVarThroughTime(var, version));
    }
    return versioned;
}


GraphVerificationResult AcceleratedBmc::solveTransitionSystem(TransitionSystem & system, ChcDirectedGraph const & graph) {
    resetTransitionSystem(system);
    unsigned short power = 1;
    while (true) {
        auto res = checkPower(power);
        switch (res) {
            case VerificationResult::UNSAFE:
                return GraphVerificationResult(res);
            case VerificationResult::SAFE:
            {
                if (not options.hasOption(Options::COMPUTE_WITNESS) or inductiveInvariant == PTRef_Undef) {
                    return GraphVerificationResult(res);
                }
//                std::cout << "Computed invariant: " << logic.printTerm(stateInvariant) << std::endl;
                auto vertices = graph.getVertices();
                assert(vertices.size() == 3);
                VId vertex = vertices[2];
                assert(vertex != graph.getEntryId() and vertex != graph.getExitId());
                TermUtils utils(logic);
                TermUtils::substitutions_map subs;
                auto graphVars = utils.getVarsFromPredicateInOrder(graph.getStateVersion(vertex));
                auto systemVars = getStateVars(0);
                assert(graphVars.size() == systemVars.size());
                for (int i = 0; i < graphVars.size(); ++i) {
                    subs.insert({systemVars[i], graphVars[i]});
                }
                PTRef graphInvariant = utils.varSubstitute(inductiveInvariant, subs);
//                std::cout << "Graph invariant: " << logic.printTerm(graphInvariant) << std::endl;
                ValidityWitness::definitions_type definitions;
                definitions.insert({graph.getStateVersion(vertex), graphInvariant});
                return GraphVerificationResult(res, ValidityWitness(definitions));
            }
            case VerificationResult::UNKNOWN:
                ++power;
        }
    }
}

bool isReachable (AcceleratedBmc::QueryResult res) { return res.result == ReachabilityResult::REACHABLE; };
bool isUnreachable (AcceleratedBmc::QueryResult res) { return res.result == ReachabilityResult::UNREACHABLE; };
PTRef extractReachableTarget (AcceleratedBmc::QueryResult res) { return res.refinedTarget; };


VerificationResult AcceleratedBmc::checkPower(unsigned short power) {
    assert(power > 0);
//    std::cout << "Checking power " << power << std::endl;
    // First compute the <2^n transition relation using information from previous level;
    auto res = reachabilityQueryLessThan(init, query, power);
    if (isReachable(res)) {
        return VerificationResult::UNSAFE;
    } else if (isUnreachable(res)) {
        // Check if we have not reached fixed point.
        if (power >= 3) {
            auto fixedPointReached = checkLessThanFixedPoint(power);
            if (fixedPointReached) {
                return VerificationResult::SAFE;
            }
            fixedPointReached = checkExactFixedPoint(power - 1);
            if (fixedPointReached) {
                return VerificationResult::SAFE;
            }
        }
    }
    // Second compute the exact power using the concatenation of previous one
    res = reachabilityQueryExact(init, query, power);
    if (isReachable(res)) {
        return VerificationResult::UNSAFE;
    } else if (isUnreachable(res)) {
        return VerificationResult::UNKNOWN;
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
        result.result = ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = ReachabilityResult::UNREACHABLE;
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
        result.result = ReachabilityResult::REACHABLE;
        return result;
    } else if (res == s_False) {
        result.result = ReachabilityResult::UNREACHABLE;
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
//    std::cout << "Checking exact reachability on level " << power << " from " << from.x << " to " << to.x << std::endl;
    assert(power >= 1);
    if (power == 1) { // Basic check with real transition relation
        return reachabilityExactOneStep(from, to);
    }
    QueryResult result;
    PTRef goal = getNextVersion(to, 2);
//    unsigned counter = 0;
    while(true) {
//        std::cout << "Exact: Iteration " << ++counter << " on level " << power << std::endl;
        auto solver = getExactReachabilitySolver(power);
        assert(solver);
        auto res = solver->checkConsistent(logic.mkAnd(from, goal));
        switch (res) {
            case ReachabilityResult::REACHABLE:
            {
                PTRef previousTransition = getExactPower(power - 1);
                PTRef translatedPreviousTransition = getNextVersion(previousTransition);
                auto model = solver->lastQueryModel();
                if (power == 2) { // Base case, the 2 steps of the exact transition relation have been used
                    result.result = ReachabilityResult::REACHABLE;
                    result.refinedTarget = getNextVersion(refineTwoStepTarget(from, logic.mkAnd(previousTransition, translatedPreviousTransition), goal, *model), -2);
                    return result;
                }
                // Create the three states corresponding to current, next and next-next variables from the query
//              PTRef modelMidpoint = getNextVersion(extractStateFromModel(getStateVars(1), *model), -1);
                PTRef nextState = getNextVersion(extractMidPoint(from, previousTransition, translatedPreviousTransition, goal, *model), -1);
//              std::cout << "Midpoint single point: " << logic.printTerm(modelMidpoint) << '\n';
//                std::cout << "Midpoint from MBP: " << logic.printTerm(nextState) << std::endl;
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQueryExact(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    assert(getExactPower(power - 1) != previousTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    // TODO: check that this is really a subset of the original midpoint
                    nextState = extractReachableTarget(subQueryRes);
//                    std::cout << "Midpoint from MBP - part 2: " << logic.printTerm(nextState) << std::endl;
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
            }
            case ReachabilityResult::UNREACHABLE:
            {
                PTRef itp = solver->lastQueryTransitionInterpolant();
                itp = cleanInterpolant(itp);
//                std::cout << "Strenghtening representation of exact reachability on level " << power << " :";
//                TermUtils(logic).printTermWithLets(std::cout, itp);
//                std::cout << std::endl;
                storeExactPower(power, itp);
                result.result = ReachabilityResult::UNREACHABLE;
                return result;
            }
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
//    unsigned counter = 0;
    while(true) {
//        std::cout << "Less-than: Iteration " << ++counter << " on level " << power << std::endl;
        SMTConfig config;
        const char * msg = "ok";
//        config.setOption(SMTConfig::o_verbosity, SMTOption(1), msg);
        config.setReduction(1);
        config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
        config.setSimplifyInterpolant(4);
        config.setLRAInterpolationAlgorithm(itp_lra_alg_decomposing_strong);
        MainSolver solver(logic, config, "Less-than reachability checker");
        // Tr^{<n-1} or (Tr^{<n-1} concat Tr^{n-1})
        PTRef previousLessThanTransition = getLessThanPower(power - 1);
        PTRef translatedExactTransition = getNextVersion(getExactPower(power - 1));
        PTRef currentToNextNextPreviousLessThanTransition = shiftOnlyNextVars(previousLessThanTransition);
        PTRef twoStepTransition = logic.mkOr(
            currentToNextNextPreviousLessThanTransition,
            logic.mkAnd(previousLessThanTransition, translatedExactTransition)
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
            result.result = ReachabilityResult::UNREACHABLE;
            return result;
        } else if (res == s_True) {
            auto model = solver.getModel();
            if (model->evaluate(currentToNextNextPreviousLessThanTransition) == logic.getTerm_true()) {
                // First disjunct was responsible for the positive answer, check it
                if (power == 2) { // This means the goal is reachable in 0 steps, no need to re-check anythin
                    // TODO: double-check this
                    result.result = ReachabilityResult::REACHABLE;
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
                assert(model->evaluate(logic.mkAnd(previousLessThanTransition, translatedExactTransition)) == logic.getTerm_true());
                if (power == 2) { // Since it was not reachable in 0 steps (checked above), here it means it was reachable in exactly 1 step
                    result.result = ReachabilityResult::REACHABLE;
                    // TODO: this could be simplified, but I need refineOneStepTarget
                    result.refinedTarget = getNextVersion(refineTwoStepTarget(from, logic.mkAnd(previousLessThanTransition, translatedExactTransition), goal, *model), -2);
                    return result;
                }
                PTRef nextState = getNextVersion(extractMidPoint(from, previousLessThanTransition, translatedExactTransition, goal, *model), -1);
                // check the reachability using lower level abstraction
                auto subQueryRes = reachabilityQueryLessThan(from, nextState, power - 1);
                if (isUnreachable(subQueryRes)) {
                    assert(getLessThanPower(power - 1) != previousLessThanTransition);
                    continue; // We need to re-check this level with refined abstraction
                } else {
                    assert(isReachable(subQueryRes));
                    nextState = extractReachableTarget(subQueryRes);
                    if (nextState == PTRef_Undef) {
                        throw std::logic_error("Refined reachable target not set in subquery!");
                    }
                }
                // here the first half of the found path is feasible, check the second half
                PTRef previousExactTransition = getExactPower(power - 1);
                subQueryRes = reachabilityQueryExact(nextState, to, power - 1);
                if (isUnreachable(subQueryRes)) {
                    assert(getExactPower(power - 1) != previousExactTransition);
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
//    std::cout << "Before simplifications: " << transition.x << std::endl;
    if (not logic.isAtom(this->transition)) {
        this->transition = ::rewriteMaxArityAggresive(logic, this->transition);
//    std::cout << "After simplifications 1: " << transition.x << std::endl;
        this->transition = ::simplifyUnderAssignment_Aggressive(this->transition, logic);
//    std::cout << "After simplifications 2: " << transition.x << std::endl;
    }
    this->exactPowers.clear();
    storeExactPower(0, logic.mkAnd(currentNextEqs));
    storeExactPower(1, transition);
    lessThanPowers.push(PTRef_Undef); // <0 does not make sense
    lessThanPowers.push(exactPowers[0]); // <1 is just exact 0
//    std::cout << "Init: " << logic.printTerm(init) << std::endl;
//    std::cout << "Transition: " << logic.printTerm(transition) << std::endl;
//    std::cout << "Transition: "; TermUtils(logic).printTermWithLets(std::cout, transition); std::cout << std::endl;
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
    PTRef transitionQuery = logic.mkAnd({start, twoSteptransition});
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

bool AcceleratedBmc::verifyLessThanPower(unsigned short power) {
    assert(power >= 2);
    SMTConfig config;
    MainSolver solver(logic, config, "");
    PTRef current = getLessThanPower(power);
    PTRef previous = getLessThanPower(power - 1);
    PTRef previousExact = getExactPower(power - 1);
//    std::cout << "Previous exact: " << logic.printTerm(previousExact) << std::endl;
    // check that previous or previousExact concatenated with previous implies current
    solver.insertFormula(logic.mkOr(
        shiftOnlyNextVars(previous),
        logic.mkAnd(previous, getNextVersion(previousExact))
    ));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == s_False;
}

bool AcceleratedBmc::verifyExactPower(unsigned short power) {
    assert(power >= 2);
    if (power > 2) {
        bool previousRes = verifyExactPower(power - 1);
        if (not previousRes) {
            return false;
        }
    }
    SMTConfig config;
    MainSolver solver(logic, config, "");
    PTRef current = getExactPower(power);
    PTRef previous = getExactPower(power - 1);
//    std::cout << "Exact on level " << power << " : " << logic.printTerm(current) << std::endl;
//    std::cout << "Exact on level " << power - 1 << " : " << logic.printTerm(previous) << std::endl;
    // check that previous or previousExact concatenated with previous implies current
    solver.insertFormula(logic.mkAnd(previous, getNextVersion(previous)));
    solver.insertFormula(logic.mkNot(shiftOnlyNextVars(current)));
    auto res = solver.check();
    return res == s_False;
}


bool AcceleratedBmc::checkLessThanFixedPoint(unsigned short power) {
    assert(power >= 3);
    assert(verifyLessThanPower(power));
    for (unsigned short i = 3; i <= power; ++i) {
        PTRef currentLevelTransition = getLessThanPower(i);
        SMTConfig config;
        MainSolver solver(logic, config, "Fixed-point checker");
        PTRef currentTwoStep = logic.mkAnd(currentLevelTransition, getNextVersion(currentLevelTransition));
        solver.insertFormula(logic.mkAnd({currentTwoStep, logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
        auto satres = solver.check();
        if (satres == s_False) {
            // std::cout << "Fixed point detected in less-than relation on level " << i << " from " << power << std::endl;
            // std::cout << "Computing inductive invariant" << std::endl;
            inductiveInvariant = getNextVersion(QuantifierElimination(logic).eliminate(logic.mkAnd(init, currentLevelTransition), getStateVars(0)), -1);
            return true;
        }
    }
    return false;
}

bool AcceleratedBmc::checkExactFixedPoint(unsigned short power) {
    assert(power >= 2);
    for (unsigned short i = 2; i <= power; ++i) {
        PTRef currentLevelTransition = getExactPower(i);
        SMTConfig config;
        MainSolver solver(logic, config, "Fixed-point checker");
        PTRef currentTwoStep = logic.mkAnd(currentLevelTransition, getNextVersion(currentLevelTransition));
        solver.insertFormula(logic.mkAnd({currentTwoStep, logic.mkNot(shiftOnlyNextVars(currentLevelTransition))}));
        auto satres = solver.check();
        if (satres == s_False) {
//             std::cout << "Fixed point detected in exact relation on level " << i << " from " << power << std::endl;
            if (power <= 10) {
//                std::cout << "Computing inductive invariant" << std::endl;
                assert(verifyLessThanPower(i));
                assert(verifyExactPower(i));
//                std::cout << "Less-than transition: " << logic.printTerm(getLessThanPower(i)) << '\n';
//                std::cout << "Exact transition: " << logic.printTerm(getExactPower(i)) << std::endl;
                PTRef transitionInvariant = logic.mkOr(
                    shiftOnlyNextVars(getLessThanPower(i)),
                    logic.mkAnd(getLessThanPower(i), getNextVersion(getExactPower(i)))
                );
//                std::cout << "Transition invariant: " << logic.printTerm(transitionInvariant) << std::endl;
                PTRef stateInvariant = QuantifierElimination(logic).eliminate(logic.mkAnd(init,transitionInvariant), getStateVars(0));
//                std::cout << "After eliminating current state vars: " << logic.printTerm(stateInvariant) << std::endl;
                stateInvariant = QuantifierElimination(logic).eliminate(stateInvariant, getStateVars(1));
                stateInvariant = getNextVersion(stateInvariant, -2);
//                std::cout << "State invariant: " << logic.printTerm(stateInvariant) << std::endl;

                unsigned long k = 1;
                k <<= (i - 1);
                inductiveInvariant = kinductiveToInductive(stateInvariant, k);
//                std::cout << "Inductive invariant: " << logic.printTerm(inductiveInvariant) << std::endl;
//                std::cout << "Inductive invariant computed!" << std::endl;
            } else {
                std::cerr << "; k-inductive invariant computed, by k is too large to compute 1-inductive invariant" << std::endl;
                inductiveInvariant = PTRef_Undef;
            }
            return true;
        }
    }
    return false;
}

// TODO: this is most likely incorrect
PTRef AcceleratedBmc::kinductiveToInductive(PTRef invariant, unsigned long k) {
    // TODO: eliminate auxiliary variables from transition relation beforehand
    vec<PTRef> steps;
    for (unsigned long i = 0; i < k - 1; ++i) {
        steps.push(getNextVersion(invariant, i));
        steps.push(getNextVersion(transition, i));
    }
    steps.push(getNextVersion(invariant, k-1));
    PTRef expanded = logic.mkAnd(steps);
    vec<PTRef> allVars = TermUtils(logic).getVars(expanded);
    vec<PTRef> currentStateVars = getStateVars(0);
    vec<PTRef> toEliminate;
    for (PTRef var : allVars) {
        if (std::find(currentStateVars.begin(), currentStateVars.end(), var) == currentStateVars.end()) {
            toEliminate.push(var);
        }
    }
    return QuantifierElimination(logic).eliminate(expanded, toEliminate);
}