//
// Created by Martin Blicha on 21.07.20.
//

#ifndef OPENSMT_TRANSITIONSYSTEM_H
#define OPENSMT_TRANSITIONSYSTEM_H

#include "PTRef.h"
#include "Logic.h"

#include <vector>
#include <unordered_map>
#include <memory>

class SystemType {

    std::vector<PTRef> stateVars;
    std::vector<PTRef> nextStateVars;

    Logic & logic;

public:

    SystemType(std::vector<SRef> stateVarTypes, Logic & logic);

    bool isStateFormula(PTRef fla) const;

    bool isTransitionFormula(PTRef fla) const;

    std::vector<PTRef> const & getStateVars() const { return stateVars; }
    std::vector<PTRef> const & getNextStateVars() const { return nextStateVars; }
};

class TransitionSystemHelper {
    struct Frame {
        std::vector<PTRef> frameVars;
        std::unordered_map<PTRef, PTRef, PTRefHash> stateToFrameVarMap;
        std::unordered_map<PTRef, PTRef, PTRefHash> frameToStateVarMap;
    };
    SystemType const & systemType;
    std::vector<Frame> frames;

    Logic & logic;

    std::string framePrefix = "f::";

    void ensureFrames(std::size_t k);

    PTRef toFrameVar(PTRef var, std::size_t frameNum);

public:
    TransitionSystemHelper(Logic & logic, SystemType const & systemType) : logic(logic), systemType(systemType) {}

    PTRef getFutureStateFormula(PTRef fla, std::size_t k);

    PTRef getFutureTransitionFormula(PTRef fla, std::size_t k);
};

class TransitionSystem {

    Logic & logic;

    std::unique_ptr<SystemType> systemType;

    PTRef init;
    PTRef transition;
    PTRef query;

    std::unique_ptr<TransitionSystemHelper> helper;



public:
    TransitionSystem(Logic & logic, std::unique_ptr<SystemType> systemType,
        PTRef initialStates, PTRef transitionRelation, PTRef badStates) :
        logic(logic),
        systemType(std::move(systemType)),
        init(initialStates),
        transition(transitionRelation),
        query(badStates)
    {
        helper = std::unique_ptr<TransitionSystemHelper>(new TransitionSystemHelper(logic, *this->systemType));
        assert(isWellFormed());
    }

    PTRef getPathFormula(std::size_t unrollingNumber);

private:
    bool isWellFormed();

    PTRef moveNStepsIntoFuture(PTRef fla, std::size_t n);

    PTRef toNextStateVar(PTRef var, std::size_t steps);
    PTRef toNextStateVar(PTRef var) { return toNextStateVar(var, 1); }

};


#endif //OPENSMT_TRANSITIONSYSTEM_H
