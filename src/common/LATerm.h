//
// Created by Martin Blicha on 01.02.20.
//

#ifndef OPENSMT_LATERM_H
#define OPENSMT_LATERM_H

#include <vector>

template<typename TVar, typename TCoeff>
class LATerm{

    struct LAFactor {
        TVar var;
        TCoeff coeff;

        LAFactor(TVar var, TCoeff coeff) : var{var}, coeff{std::move(coeff)} {}
        LAFactor(TCoeff coeff, TVar var) : var{var}, coeff{std::move(coeff)} {}
    };

    TCoeff constantFactor;
    std::vector<LAFactor> variableFactors;

public:

    using Factor = LAFactor;
    using iterator = typename std::vector<Factor>::iterator;
    using const_iterator = typename std::vector<Factor>::const_iterator;

    LATerm(TCoeff constantFactor, std::vector<Factor> variableFactors)
    : constantFactor{std::move(constantFactor)}, variableFactors{std::move(variableFactors)}
    {}

    LATerm(std::vector<Factor> variableFactors, TCoeff constantFactor)
            : constantFactor{std::move(constantFactor)}, variableFactors{std::move(variableFactors)}
    {}

    std::size_t getNumberOfVars() const { return variableFactors.size(); }

    TCoeff getConstantFactor() const { return constantFactor; }

    const_iterator getFactorIterator() const { return variableFactors.cbegin(); }

    const_iterator getFactorIteratorEnd() const { return variableFactors.cend(); }

    void normalizeFor(TVar var) {
        auto pos = std::find_if(variableFactors.begin(), variableFactors.end(),
                [var](const Factor& factor) { return factor.var == var; });
        assert(pos != variableFactors.end());
        std::iter_swap(variableFactors.begin(), pos);
        TCoeff coeff = variableFactors.begin()->coeff;
        for (Factor & factor : variableFactors) {
            factor.coeff = factor.coeff / coeff;
        }
        constantFactor = constantFactor / coeff;
    }

    LATerm<TVar,TCoeff> solveFor(TVar var) {
        auto pos = std::find_if(variableFactors.begin(), variableFactors.end(),
                                [var](const Factor& factor) { return factor.var == var; });
        assert(pos != variableFactors.end());
        std::iter_swap(variableFactors.begin(), pos);
        TCoeff coeff = -variableFactors.begin()->coeff;
        std::vector<Factor> solvedFactors;
        solvedFactors.reserve(variableFactors.size() - 1);
        std::transform(variableFactors.begin() + 1, variableFactors.end(), std::back_inserter(solvedFactors),
                [&coeff](Factor const& f) { return Factor(f.var, f.coeff/coeff); });
        return LATerm(std::move(solvedFactors), constantFactor / coeff);
    }

};
#endif //OPENSMT_LATERM_H
