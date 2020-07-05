//
// Created by Martin Blicha on 14.06.20.
//

#include "ModelBuilder.h"

void ModelBuilder::addSubstitutions(Map<PTRef,PtAsgn,PTRefHash> const & subst) {
    auto entries = subst.getKeysAndValsPtrs();
    for (auto const * const entry : entries) {
        assert(logic.isVar(entry->key));
        if (entry->data.sgn == l_True) {
            if (substitutions.has(entry->key)) {
                substitutions[entry->key] = entry->data;
            }
            else {
                substitutions.insert(entry->key, entry->data);
            }
        }
    }
}
template<typename TGetModel>
void ModelBuilder::processSubstitutions(TGetModel getModel) {
    logic.substitutionsTransitiveClosure(substitutions);
    auto assignCopy = this->assignment;
    auto model = getModel();
    auto entries = substitutions.getKeysAndValsPtrs();
    for (auto const * const entry : entries) {
        assert(logic.isVar(entry->key));
        if (entry->data.sgn == l_True) {
            PTRef mappedTerm = entry->data.tr;
            PTRef val = model->evaluate(mappedTerm);
            assert(logic.isConstant(val));
            auto res = assignCopy.insert(std::make_pair(entry->key, val));
            if (!res.second && val != res.first->second) {
                assert(false);
                std::cerr << "Inconsistent values for " << logic.printTerm(entry->key)
                    << ": " << logic.printTerm(res.first->second) << " and " << logic.printTerm(val) << std::endl;
                throw std::logic_error("Inconsistency when building model\n");
            }
        }
    }
    this->assignment = std::move(assignCopy);
}

void ModelBuilder::processSubstitutionsWithDefault() {
    processSubstitutions([this] { return this->buildModelWithDefaults_(); });
}

void ModelBuilder::processSubstitutionsExact() {
    processSubstitutions([this] { return this->buildPreciseModel_(); });
}
