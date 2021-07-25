#include "UFLRATHandler.h"
#include "lrasolver/LRASolver.h"
#include "TreeOps.h"
//#include "InterpolatingEgraph.h"
#include "Egraph.h"
#include "UFLRALogic.h"

UFLRATHandler::UFLRATHandler(SMTConfig & c, UFLRALogic & l)
        : TSolverHandler(c), logic(l)
{
    lrasolver = new LRASolver(config, logic);
    SolverId lra_id = lrasolver->getId();
    tsolvers[lra_id.id] = lrasolver;
    solverSchedule.push(lra_id.id);

    ufsolver = new Egraph(config, logic);

    SolverId uf_id = ufsolver->getId();
    tsolvers[uf_id.id] = ufsolver;
    solverSchedule.push(uf_id.id);

}

UFLRATHandler::~UFLRATHandler() {}

Logic & UFLRATHandler::getLogic() {
    return logic;
}

Logic const & UFLRATHandler::getLogic() const {
    return logic;
}

PTRef UFLRATHandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager)
{
    throw std::logic_error("Not implemented");
}

TRes UFLRATHandler::check(bool fullCheck) {
    if (fullCheck) {
        auto res = TSolverHandler::check(fullCheck);
        if (res == TRes::SAT) {
            // see if we need to propagate more deduced equalities
//            for (PTRef var : interfaceVariables) {
//                std::cout << logic.pp(var) << std::endl;
//            }
            auto equalities = ufsolver->getDeducedEqualities(interfaceVariables);
            equalities.copyTo(equalitiesToPropagate);
            if (equalities.size() > 0) {
                return res;
            } else {
                // TODO: Obtain equalities from LRA solver
//                throw std::logic_error("Not implemented yet!");
            }
        }
        return res;
    } else {
        return TSolverHandler::check(false);
    }
}

void UFLRATHandler::declareAtom(PTRef tr) {
    TSolverHandler::declareAtom(tr);
    if (logic.isUFEquality(tr)) {
        // Let's go for crude solution for now
        MapWithKeys<PTRef,bool,PTRefHash> allVars;
        getVars(tr, logic, allVars);
        for (PTRef var : allVars.getKeys()) {
            if (logic.isNumVar(var)) {
                if (std::find(interfaceVariables.begin(), interfaceVariables.end(), var) == interfaceVariables.end()) {
                    interfaceVariables.push(var);
                }
            }
        }
    }
}

