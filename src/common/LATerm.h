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

};
#endif //OPENSMT_LATERM_H
