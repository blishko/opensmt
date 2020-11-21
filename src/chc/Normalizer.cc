//
// Created by Martin Blicha on 01.09.20.
//

#include "Normalizer.h"

NormalizedChcSystem Normalizer::normalize(const ChcSystem & system) {
    std::vector<ChClause> normalized;
    auto const& clauses = system.getClauses();
    for (auto const & clause : clauses) {
        normalized.push_back(normalize(clause));
    }
    CanonicalPredicateRepresentation cpr = getCanonicalPredicateRepresentation();
    // build graph out of normalized system
    std::unique_ptr<ChcSystem> newSystem(new ChcSystem());
    for (auto const & clause : normalized) {
        newSystem->addClause(clause);
    }
    return NormalizedChcSystem{.normalizedSystem = std::move(newSystem), .canonicalPredicateRepresentation = std::move(cpr)};
}
