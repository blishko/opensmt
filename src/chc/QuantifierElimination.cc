//
// Created by Martin Blicha on 12.06.21.
//

#include "QuantifierElimination.h"

#include "ModelBasedProjection.h"
#include "TermUtils.h"

#include "SMTConfig.h"
#include "MainSolver.h"


PTRef QuantifierElimination::eliminate(PTRef fla, PTRef var) {
    if (not logic.isVar(var) or not logic.hasSortBool(fla)) {
        throw std::invalid_argument("Invalid arguments to quantifier elimination");
    }

    fla = TermUtils(logic).toNNF(fla);
    vec<PTRef> projections;

    SMTConfig config;
    const char* msg = "ok";
    config.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
    MainSolver solver(logic, config, "QE solver");
    solver.insertFormula(fla);
    while(true) {
        auto res = solver.check();
        if (res == s_False) {
            break;
        } else if (res == s_True) {
            auto model = solver.getModel();
            ModelBasedProjection mbp(logic);
            PTRef projection = mbp.project(fla, {var}, *model);
//            std::cout << "Projection: " << logic.printTerm(projection) << std::endl;
            projections.push(projection);
            solver.push(); // to avoid processing the same formula over and over again
            solver.insertFormula(logic.mkNot(projection));
        } else {
            throw std::logic_error("Error in solver during quantifier elimination");
        }
    }
    PTRef result = logic.mkOr(projections);
    if (not logic.isAtom(result)) {
        result = ::rewriteMaxArityAggresive(logic, result);
        result = ::simplifyUnderAssignment_Aggressive(result, logic);
        // TODO: more simplifications?
    }
    return result;
}
