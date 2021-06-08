//
// Created by Martin Blicha on 01.06.21.
//

#ifndef OPENSMT_ACCELERATEDBMC_H
#define OPENSMT_ACCELERATEDBMC_H

#include "Engine.h"

class TransitionSystem;

class AcceleratedBmc : public Engine {

    Logic & logic;

    Options const & options;

    vec<PTRef> exactPowers;
    vec<PTRef> lessThanPowers;

    // Versioned representation of the transition system
    PTRef init;
    PTRef transition;
    PTRef query;
    vec<PTRef> stateVariables;
    vec<PTRef> auxiliaryVariables;

public:
    AcceleratedBmc(Logic& logic, Options const & options) : logic(logic), options(options) {}

    GraphVerificationResult solve(ChcDirectedHyperGraph & system) override;

    GraphVerificationResult solve(const ChcDirectedGraph & system) override;

    ~AcceleratedBmc() override = default;

private:
    GraphVerificationResult solveTransitionSystem(TransitionSystem & system);

    void resetTransitionSystem(TransitionSystem const & system);

    PTRef getInit() const;
    PTRef getTransitionRelation() const;
    PTRef getQuery() const;

    VerificationResult checkPower(unsigned short power);

    PTRef getExactPower(unsigned short power) const;
    void storeExactPower(unsigned short power, PTRef tr);

    PTRef getLessThanPower(unsigned short power) const;
    void storeLessThanPower(unsigned short power, PTRef tr);

    PTRef getNextVersion(PTRef currentVersion, int);
    PTRef getNextVersion(PTRef currentVersion) { return getNextVersion(currentVersion, 1); };

    vec<PTRef> getStateVars(int version);

    /* Shifts only next-next vars to next vars */
    PTRef cleanInterpolant(PTRef itp);
    /* Shifts only next vars to next-next vars */
    PTRef shiftOnlyNextVars(PTRef transition);

    enum class ReachabilityResult {REACHABLE, UNREACHABLE};
    ReachabilityResult reachabilityQueryExact(PTRef from, PTRef to, unsigned short power);
    ReachabilityResult reachabilityQueryLessThan(PTRef from, PTRef to, unsigned short power);

    PTRef extractStateFromModel(vec<PTRef> const & vars, Model& model);
    PTRef extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model& model);
};


#endif //OPENSMT_ACCELERATEDBMC_H
