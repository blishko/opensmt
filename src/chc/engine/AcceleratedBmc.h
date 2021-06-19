//
// Created by Martin Blicha on 01.06.21.
//

#ifndef OPENSMT_ACCELERATEDBMC_H
#define OPENSMT_ACCELERATEDBMC_H

#include "Engine.h"

class TransitionSystem;

enum class ReachabilityResult {REACHABLE, UNREACHABLE};

class SolverWrapper {
protected:
    PTRef transition = PTRef_Undef;

public:
    virtual ~SolverWrapper() = default;
    virtual ReachabilityResult checkConsistent(PTRef query) = 0;
    virtual void strenghtenTransition(PTRef nTransition) = 0;
    virtual std::unique_ptr<Model> lastQueryModel() = 0;
    virtual PTRef lastQueryTransitionInterpolant() = 0;
};


class AcceleratedBmc : public Engine {

    Logic & logic;

    Options const & options;

    vec<PTRef> exactPowers;
    vec<PTRef> lessThanPowers;

    vec<SolverWrapper*> reachabilitySolvers;

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

    ~AcceleratedBmc() override;

    struct QueryResult {
        ReachabilityResult result;
        PTRef refinedTarget = PTRef_Undef;
    };

private:
    GraphVerificationResult solveTransitionSystem(TransitionSystem & system, ChcDirectedGraph const & graph);

    void resetTransitionSystem(TransitionSystem const & system);

    PTRef getInit() const;
    PTRef getTransitionRelation() const;
    PTRef getQuery() const;

    VerificationResult checkPower(unsigned short power);

    PTRef getExactPower(unsigned short power) const;
    void storeExactPower(unsigned short power, PTRef tr);

    PTRef getLessThanPower(unsigned short power) const;
    void storeLessThanPower(unsigned short power, PTRef tr);

    SolverWrapper* getExactReachabilitySolver(unsigned short power) const;

    PTRef getNextVersion(PTRef currentVersion, int);
    PTRef getNextVersion(PTRef currentVersion) { return getNextVersion(currentVersion, 1); };

    vec<PTRef> getStateVars(int version);

    /* Shifts only next-next vars to next vars */
    PTRef cleanInterpolant(PTRef itp);
    /* Shifts only next vars to next-next vars */
    PTRef shiftOnlyNextVars(PTRef transition);

    QueryResult reachabilityQueryExact(PTRef from, PTRef to, unsigned short power);
    QueryResult reachabilityQueryLessThan(PTRef from, PTRef to, unsigned short power);

    QueryResult reachabilityExactOneStep(PTRef from, PTRef to);
    QueryResult reachabilityExactZeroStep(PTRef from, PTRef to);

    PTRef extractStateFromModel(vec<PTRef> const & vars, Model& model);
    PTRef extractMidPoint(PTRef start, PTRef firstTransition, PTRef secondTransition, PTRef goal, Model& model);

    PTRef refineTwoStepTarget(PTRef start, PTRef transition, PTRef goal, Model& model);

    bool verifyLessThanPower(unsigned short power);
    bool checkLessThanFixedPoint(unsigned short power);
    bool checkExactFixedPoint(unsigned short power);
};


#endif //OPENSMT_ACCELERATEDBMC_H
