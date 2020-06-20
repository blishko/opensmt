//
// Created by Martin Blicha on 14.06.20.
//

#ifndef OPENSMT_MODELBUILDER_H
#define OPENSMT_MODELBUILDER_H

#include "PTRef.h"
#include "Model.h"

#include <unordered_map>
#include <memory>

class Logic;

class ModelBuilder {

    std::unordered_map<PTRef, PTRef, PTRefHash> assignment;

    Map<PTRef, PtAsgn, PTRefHash> substitutions;

    Logic& logic;

public:

    ModelBuilder(Logic & logic) : logic(logic) {}

    void addVarValue(PTRef var, PTRef value) {
        auto res = assignment.insert(std::make_pair(var, value));
        assert(res.second); (void)res;
    }

    template<typename TIt>
    void addVarValues(TIt begin, TIt end) {
        assignment.insert(begin, end);
    }

    std::unique_ptr<Model> buildModelWithDefaults() {
        processSubstitutionsWithDefault();
        return buildModelWithDefaults_();
    }

    std::unique_ptr<Model> buildPreciseModel() {
        processSubstitutionsExact();
        return buildPreciseModel_();
    }

    /*
     * Incorporates the given substitution map into the model.
     * PRECONDITIONS: all keys are variables
     */
    void addSubstitutions(Map<PTRef,PtAsgn,PTRefHash> const & subst);

private:
    template<typename TGetModel>
    void processSubstitutions(TGetModel getModel);
    void processSubstitutionsWithDefault();
    void processSubstitutionsExact();

    std::unique_ptr<Model> buildModelWithDefaults_() const {
        return std::unique_ptr<Model>(new ModelWithDefaults(logic, std::move(assignment)));
    }

    std::unique_ptr<Model> buildPreciseModel_() const {
        return std::unique_ptr<Model>(new ExplicitModel(logic, std::move(assignment)));
    }
};


#endif //OPENSMT_MODELBUILDER_H
