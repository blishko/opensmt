//
// Created by Martin Blicha on 06.03.21.
//

#ifndef OPENSMT_MODELBASEDPROJECTION_H
#define OPENSMT_MODELBASEDPROJECTION_H

#endif //OPENSMT_MODELBASEDPROJECTION_H

#include "PTRef.h"
#include "Model.h"

#include <unordered_set>
#include <iosfwd>
class Logic;
class LALogic;

class ModelBasedProjection {
private:
    Logic & logic;

public:
    explicit ModelBasedProjection(Logic & logic) : logic(logic) {}

    PTRef project(PTRef fla, vec<PTRef> const& varsToEliminate, Model& model);

private:
    using implicant_t = std::vector<PtAsgn>;

    implicant_t projectSingleVar(PTRef var, implicant_t implicant, Model & model);

    implicant_t getImplicant(PTRef var, Model & model);

    void dumpImplicant(ostream& out, implicant_t const & implicant);

    void postprocess(implicant_t & literals, LALogic & logic);

    // LIA version

    struct DivisibilityConstraint {
        PTRef constant;
        PTRef term;
    };

    using div_constraints_t = std::vector<DivisibilityConstraint>;

    PTRef projectIntegerVars(PTRef* beg, PTRef* end, implicant_t implicant, Model & model);

    void processDivConstraints(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model);

    void processClassicLiterals(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model);

    struct LIABound {
        PTRef term;
        PTRef coeff;
    };

    struct LIABoundLower {
        PTRef term;
        PTRef coeff;
    };
    struct LIABoundUpper {
        PTRef term;
        PTRef coeff;
    };

    struct ResolveResult {
        std::vector<PTRef> bounds;
        DivisibilityConstraint constraint; // TODO: optional
    };

    ResolveResult resolve(LIABoundLower const& lower, LIABoundUpper const& upper, Model & model, LIALogic & lialogic);
};