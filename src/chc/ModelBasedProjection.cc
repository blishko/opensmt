//
// Created by Martin Blicha on 06.03.21.
//

#include "ModelBasedProjection.h"

#include "LRALogic.h"
#include "TreeOps.h"
#include "TermUtils.h"

#include <memory>


namespace{
    enum class BoundType {LOWER, UPPER};

    struct Bound {
        BoundType type;
        PTRef val;
        bool strict;
    };

    PTRef substituteBound(Bound const& what, Bound const& where, LALogic & logic) {
        assert(what.type == BoundType::LOWER);
        if (what.type != BoundType::LOWER) {
            throw std::invalid_argument("Bound substitution can use only lower bounds");
        }
        if (where.type == BoundType::LOWER) {
            // Here it does not matter if 'what' bound is strict or not the result is non-strict bound
            return logic.mkNumLeq(where.val, what.val);
        } else {
            assert(where.type == BoundType::UPPER);
            if (what.strict or where.strict) {
                return logic.mkNumLt(what.val, where.val);
            } else {
                return logic.mkNumLeq(what.val, where.val);
            }
        }
    }

    std::pair<PTRef, PTRef> splitLinearFactorToVarAndConst(PTRef tr, LALogic const & logic) {
        assert(logic.isLinearFactor(tr));
        PTRef var;
        PTRef constant;
        logic.splitTermToVarAndConst(tr, var, constant);
        return {var, constant};
    }

    std::vector<std::pair<PTRef, PTRef>> splitLinearTermToFactors(PTRef tr, LALogic const & logic ) {
        std::vector<std::pair<PTRef, PTRef>> factors;
        assert(logic.isLinearTerm(tr));
        if (logic.isLinearFactor(tr)) { return {splitLinearFactorToVarAndConst(tr, logic)}; }

        Pterm const & t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); ++i) {
            factors.push_back(splitLinearFactorToVarAndConst(t[i], logic));
        }
        return factors;
    }
}

ModelBasedProjection::implicant_t ModelBasedProjection::projectSingleVar(PTRef var, implicant_t implicant, Model & model) {
    assert(logic.isVar(var));
    // if the variable is boolean, simply remove it from implicant
    if (logic.hasSortBool(var)) {
        auto it = std::find_if(implicant.begin(), implicant.end(), [var](PtAsgn literal) { return literal.tr == var; });
        if (it != implicant.end()) {
            it = implicant.erase(it);
            // the same boolean variable cannot be present twice in the implicant
            assert(std::find_if(it, implicant.end(), [var](PtAsgn literal) { return literal.tr == var; }) == implicant.end());
        }
        return std::move(implicant);
    }
    LALogic * lalogic = dynamic_cast<LALogic *>(&logic);
    if (not lalogic or not lalogic->isNumVar(var)) {
        throw std::logic_error("Projection for other than Reals or Ints not supported");
    }
    // proper elimination of Real variable
    LATermUtils utils(*lalogic);
    auto containsVar = [var, &utils](PtAsgn lit) {
        return utils.atomContainsVar(lit.tr, var);
    };

    // split the literals to those containing var and those not containing var
    auto interestingEnd = std::partition(implicant.begin(), implicant.end(), containsVar);
    // preprocessing
    for (auto it = implicant.begin(); it != interestingEnd; ++it) {
        PtAsgn lit = *it;
        if (logic.isEquality(lit.tr)) {
            PTRef lhs = logic.getPterm(lit.tr)[0];
            PTRef rhs = logic.getPterm(lit.tr)[1];
            if (lit.sgn == l_True) { // if equality is present, we just use it to substitute the variable away
                assert(model.evaluate(lit.tr) == logic.getTerm_true());
                // express variable and substitute in the rest of literals
                PTRef zeroTerm = lalogic->mkNumMinus(lhs, rhs);
                PTRef substitutionTerm = utils.expressZeroTermFor(zeroTerm, var);
                MapWithKeys<PTRef, PtAsgn, PTRefHash> subst;
                subst.insert(var, PtAsgn(substitutionTerm, l_True));
                Substitutor substitutor(logic, subst);
                for (auto it2 = implicant.begin(); it2 != interestingEnd; ++it2) {
                    it2->tr = substitutor.rewrite(it2->tr);
                }
                // remove the true terms
                assert(it->tr == logic.getTerm_true());
                auto size = implicant.size();
                for (std::size_t i = 0; i < size; /* manual control */) {
                    PtAsgn literal = implicant[i];
                    if ((literal.tr == logic.getTerm_true() and literal.sgn == l_True) or (literal.tr == logic.getTerm_false() and literal.sgn == l_False)) {
                        implicant[i] = implicant.back();
                        implicant.pop_back();
                        --size;
                        assert(size == implicant.size());
                    } else {
                        ++i;
                    }
                }
                return std::move(implicant);
            } else {
                assert(lit.sgn == l_False);
                // replace the non-equality with the strict inequality that is true in the model
                PTRef lt = lalogic->mkNumLt(lhs, rhs);
                PTRef replacement = model.evaluate(lt) == logic.getTerm_true() ? lt : lalogic->mkNumLt(rhs, lhs);
                assert(logic.isNot(replacement)); // strict inequalities are expressed as negations of non-strict ones
                it->tr = logic.getPterm(replacement)[0]; // we store the non-strict inequality, the sign is already set to false
                assert(it->sgn == l_False);
            }
        }
    }
    // at this point we have only strict and nonstrict inequalities

    // literals with the variable that we want to eliminate are now in the front of the vector
    // "interestingEnd" points to the first literal that does not contain the var anymore

    // collect the lower and upper bounds, remember if they are strict or non-strict
    std::vector<Bound> bounds;
    std::vector<PTRef> lBounds;
    std::vector<PTRef> uBounds;
    for (auto it = implicant.begin(); it != interestingEnd; ++it) {
        PTRef ineq = it->tr;
        lbool sign = it->sgn;
        assert(sign == l_True || sign == l_False);
        bool isStrict = sign == l_False;
        bool isLower = sign != l_False; // inequalities are of form "c <= t" where c is constant
        PTRef constant = lalogic->getPterm(ineq)[0];
        assert(lalogic->isConstant(constant));
        PTRef linTerm = lalogic->getPterm(ineq)[1];
        assert(lalogic->isLinearTerm(linTerm));
        auto factors = splitLinearTermToFactors(linTerm, *lalogic);
        auto interestingVarIt = std::find_if(factors.begin(), factors.end(), [var](std::pair<PTRef, PTRef> factor) {
            return factor.first == var;
        });
        assert(interestingVarIt != factors.end());
        auto coeffPTRef = interestingVarIt->second;
        factors.erase(interestingVarIt);
        auto coeff = lalogic->getNumConst(coeffPTRef);
        if (coeff.sign() < 0) {
            isLower = !isLower;
        }
        PTRef newConstant = lalogic->mkConst(lalogic->getNumConst(constant) / coeff);
        coeff.negate();
        // update the coefficients in the factor
        vec<PTRef> boundArgs;
        for (auto & factor : factors) { // in place update
            auto newCoeff = lalogic->getNumConst(factor.second) / coeff;
            factor.second = lalogic->mkConst(newCoeff);
            boundArgs.push(lalogic->mkNumTimes(factor.first, factor.second)); // MB: no simplification, could be insertTermHash directly
        }
        boundArgs.push(newConstant);
        PTRef bound = lalogic->mkNumPlus(boundArgs); // MB: no simplification should happen, could be insertTermHash
        // Remember the bound
        auto boundType = isLower ? BoundType::LOWER : BoundType::UPPER;
        bounds.push_back(Bound{.type = boundType, .val = bound, .strict = isStrict});
        auto & whereToPush = isLower ? lBounds : uBounds;
        whereToPush.push_back(bound);
    }

    // pick the correct literal based on the model
    PTRef varVal = model.evaluate(var);
    assert(lalogic->isConstant(varVal));
    if (lBounds.empty() or uBounds.empty()) {
        // if we are missing either upper or lower bounds altogether, no new literals are produced and we can just return those not containing this variable
        return implicant_t(interestingEnd, implicant.end());
    }
    // pick substitution from lower bounds
    // pick highest lower bound according to the model
    Bound const * highestLowerBound = nullptr;
    for (auto const& bound : bounds) {
        if (bound.type == BoundType::UPPER) { continue; }
        if (highestLowerBound == nullptr) {
            highestLowerBound = &bound;
            continue;
        }
        PTRef currentValRef = model.evaluate(highestLowerBound->val);
        PTRef otherValRef = model.evaluate(bound.val);
        assert(lalogic->isConstant(currentValRef) && lalogic->isConstant(otherValRef));
        auto const & currentVal = lalogic->getNumConst(currentValRef);
        auto const & otherVal = lalogic->getNumConst(otherValRef);
        if (otherVal > currentVal or (otherVal == currentVal and not bound.strict)) {
            highestLowerBound = &bound;
        }
    }
    // perform substitution
    implicant_t newLiterals;
    for (Bound const & bound : bounds) {
        PTRef subResult = substituteBound(*highestLowerBound, bound, *lalogic);
        if (lalogic->isNumEq(subResult)) {
            throw std::logic_error("This should not happen anymore");
        }
        else if (subResult != logic.getTerm_true()) {
            PtAsgn newLiteral = lalogic->isNot(subResult) ? PtAsgn(lalogic->getPterm(subResult)[0], l_False)
                                                       : PtAsgn(subResult, l_True);
            newLiterals.push_back(newLiteral);
        }
    }
    // don't forget the literals not containing the var to eliminate
    newLiterals.insert(newLiterals.end(), interestingEnd, implicant.end());
    return std::move(newLiterals);
}

namespace{
void collectImplicant(Logic & logic, PTRef fla, Model & model, std::vector<char> & processed, std::vector<PtAsgn>& literals) {
    auto id = Idx(logic.getPterm(fla).getId());
    if (id >= processed.size()) {
        throw std::logic_error("Should not happen!");
    }
    if (processed[id]) { return; }
    processed[id] = 1;
    PTRef trueTerm = logic.getTerm_true();
    assert(model.evaluate(fla) == trueTerm);
    if (logic.isAtom(fla)) {
        literals.push_back(PtAsgn(fla, l_True));
        return;
    }
    if (logic.isAnd(fla)) {
        // all children must be satisfied
        auto size = logic.getPterm(fla).size();
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            assert(model.evaluate(child) == trueTerm);
            collectImplicant(logic, child, model, processed, literals);
        }
        return;
    }
    if (logic.isOr(fla)) {
        // at least one child must be satisfied
        auto size = logic.getPterm(fla).size();
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            if (model.evaluate(child) == trueTerm) {
                collectImplicant(logic, child, model, processed, literals);
                return;
            }
        }
        assert(false);
        throw std::logic_error("Error in processing disjunction in collectImplicant!");
    }
    if (logic.isNot(fla)) {
        PTRef child = logic.getPterm(fla)[0];
        if (logic.isAtom(child)) {
            assert(model.evaluate(child) == logic.getTerm_false());
            literals.push_back(PtAsgn(child, l_False));
            return;
        }
        throw std::logic_error("Formula is not in NNF in collectImplicant!");
    }
    throw std::logic_error("Unexpected connective in formula in collectImplicant");
}
}

ModelBasedProjection::implicant_t ModelBasedProjection::getImplicant(PTRef fla, Model & model) {
    assert(model.evaluate(fla) == logic.getTerm_true());
    std::vector<PtAsgn> literals;
    std::vector<char> processed;
    processed.resize(Idx(logic.getPterm(fla).getId()) + 1, 0);
    collectImplicant(logic, fla, model, processed, literals);
    return literals;
}

PTRef ModelBasedProjection::project(PTRef fla, const vec<PTRef> & varsToEliminate, Model & model) {
    auto checkImplicant = [&](implicant_t const& impl){
        for (auto const& elem : impl) {
            assert(elem.sgn == l_False or elem.sgn == l_True);
            assert((elem.sgn == l_False and model.evaluate(elem.tr) == logic.getTerm_false())
                or (elem.sgn == l_True and model.evaluate(elem.tr) == logic.getTerm_true()));
        }
    };

    vec<PTRef> tmp;
    varsToEliminate.copyTo(tmp);
    auto boolEndIt = std::stable_partition(tmp.begin(), tmp.end(), [&](PTRef var) {
        assert(logic.isVar(var));
        return logic.hasSortBool(var);
    });

    if (boolEndIt != tmp.begin()) { // there are some booleans
        MapWithKeys<PTRef, PtAsgn, PTRefHash> subst;
        for (auto it = tmp.begin(); it != boolEndIt; ++it) {
            subst.insert(*it, PtAsgn(model.evaluate(*it), l_True));
        }
        fla = Substitutor(logic, subst).rewrite(fla);
    }
    if (boolEndIt == tmp.end()) {
        return fla;
    }

    PTRef nnf = TermUtils(logic).toNNF(fla);
    auto implicant = getImplicant(nnf, model);
//    dumpImplicant(std::cout, implicant);
    checkImplicant(implicant);
//    for (PTRef var : varsToEliminate) {
    for (auto it = boolEndIt; it != tmp.end(); ++it) {
        PTRef var = *it;
//        std::cout << "Eliminating " << logic.printTerm(var) << std::endl;
        implicant = projectSingleVar(var, std::move(implicant), model);
//        dumpImplicant(std::cout, implicant);
        checkImplicant(implicant);
    }
    tmp.clear();
    for (PtAsgn literal : implicant) {
        tmp.push(literal.sgn == l_True ? literal.tr : logic.mkNot(literal.tr));
    }
    return logic.mkAnd(tmp);
}

void ModelBasedProjection::dumpImplicant(std::ostream & out, implicant_t const& implicant) {
    out << "Implicant:\n";
    std::for_each(implicant.begin(), implicant.end(), [&](PtAsgn i) { out << logic.printTerm(i.tr) << ' ' << toInt(i.sgn) << '\n'; });
    out << std::endl;
}

