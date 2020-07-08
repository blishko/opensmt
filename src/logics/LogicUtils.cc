//
// Created by Martin Blicha on 08.07.20.
//

#include "LogicUtils.h"
#include "Real.h"

namespace {

enum class IBoundType : bool {
    LOWER, UPPER
};

enum class IBoundStrictness : bool {
    STRICT, NONSTRICT
};

struct IBound {
    opensmt::Real val;
    IBoundType type;
    IBoundStrictness strictness;
    PtAsgn originalLiteral;
};
}

using implicant_t = Logic::implicant_t;

Logic::implicant_t LALogicUtils::compactImplicant(Logic::implicant_t implicant) {
    implicant_t n_implicant;

    std::unordered_map<PTRef, std::vector<IBound>, PTRefHash> bounds;
    for (PtAsgn lit : implicant) {
        PTRef atom = lit.tr;
        assert(not logic.isNot(atom));
        if (!logic.isNumLeq(atom)) {
            n_implicant.insert(lit);
            continue;
        }
        assert(logic.isNumLeq(atom));
        PTRef constant = logic.getPterm(atom)[0];
        assert(logic.isNumConst(constant));
        auto constantVal = logic.getNumConst(constant);
        PTRef term = logic.getPterm(atom)[1];
        assert(logic.isLinearTerm(term));
        // positive sign means the bound is lower and non-strict, negative sign means upper and strict
        bool isLower = lit.sgn == l_True;
        bool isStrict = !isLower;
        if(logic.isNegated(term)) { // get the positive version of the term; this can switch lower to upper bound
            term = logic.mkNumNeg(term);
            constantVal.negate();
            isLower = !isLower;
        }
        IBound bound {.val = std::move(constantVal),
            .type = isLower ? IBoundType::LOWER : IBoundType::UPPER,
            .strictness = isStrict ? IBoundStrictness::STRICT : IBoundStrictness::NONSTRICT,
            .originalLiteral = lit
        };

        bounds[term].push_back(bound);
    }
    // now pick only the strongest bounds for each term
    for (auto & entry : bounds) {
        auto & e_bounds = entry.second;
        if (e_bounds.size() == 1) { // just a single value, nothing else to do, just use it
            n_implicant.insert(e_bounds[0].originalLiteral);
            continue;
        }
        assert(e_bounds.size() >= 2);

        // partition to lower bounds and upper bounds
        auto lowerEnd = std::partition(e_bounds.begin(), e_bounds.end(),
                                       [](IBound const & bound) { return bound.type == IBoundType::LOWER; });

        // the strongest lower bound is the highest bound with strict being higher than non-strict (c < c + delta)
        auto lowerBoundsLessThan = [](IBound const & first, IBound const & second) {
            return first.val < second.val ||
                   (first.val == second.val && second.strictness == IBoundStrictness::STRICT &&
                    first.strictness == IBoundStrictness::NONSTRICT);
        };
        auto highestLowerBoundIt = std::max_element(e_bounds.begin(), lowerEnd, lowerBoundsLessThan);
        if (highestLowerBoundIt != lowerEnd) { n_implicant.insert(highestLowerBoundIt->originalLiteral); }

        // the strongest upper bound is the lowest bound with strict being lower than non-strict (c - delta < c)
        auto upperBoundsLessThan = [](IBound const & first, IBound const & second) {
            return first.val < second.val ||
                   (first.val == second.val && second.strictness == IBoundStrictness::NONSTRICT &&
                    first.strictness == IBoundStrictness::STRICT);
        };
        auto lowestUpperBoundIt = std::min_element(lowerEnd, e_bounds.end(), upperBoundsLessThan);
        if (lowestUpperBoundIt != e_bounds.end()) { n_implicant.insert(lowestUpperBoundIt->originalLiteral); }
    }
    return n_implicant;

}
