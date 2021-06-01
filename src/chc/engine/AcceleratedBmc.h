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
    vec<PTRef> lessThenPowers;

    // Versioned representation of the transition system
    PTRef init;
    PTRef transition;
    PTRef query;
    vec<PTRef> stateVariables;

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

    PTRef getPower(unsigned short power) const;
    void storePower(unsigned short power, PTRef tr);

    PTRef getNextVersion(PTRef currentVersion, int);
    PTRef getNextVersion(PTRef currentVersion) { return getNextVersion(currentVersion, 1); };

    vec<PTRef> getStateVars(int version);

    PTRef cleanInterpolant(PTRef itp);

    enum class ReachabilityResult {REACHABLE, UNREACHABLE};
    ReachabilityResult reachabilityQuery(PTRef from, PTRef to, unsigned short power);

    PTRef extractStateFromModel(vec<PTRef> const & vars, Model& model);
};


#endif //OPENSMT_ACCELERATEDBMC_H
