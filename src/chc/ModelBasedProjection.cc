//
// Created by Martin Blicha on 06.03.21.
//

#include "ModelBasedProjection.h"

#include "LRALogic.h"
#include "LIALogic.h"
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
            if (where.strict and not what.strict) {
                return logic.mkNumLt(where.val, what.val);
            } else {
                return logic.mkNumLeq(where.val, what.val);
            }
        } else {
            assert(where.type == BoundType::UPPER);
            if (what.strict or where.strict) {
                return logic.mkNumLt(what.val, where.val);
            } else {
                return logic.mkNumLeq(what.val, where.val);
            }
        }
    }

    struct LinearFactor {
        PTRef var;
        PTRef coeff;
    };

    LinearFactor splitLinearFactorToVarAndConst(PTRef tr, LALogic const & logic) {
        assert(logic.isLinearFactor(tr));
        LinearFactor res;
        logic.splitTermToVarAndConst(tr, res.var, res.coeff);
        return res;
    }

    std::vector<LinearFactor> splitLinearTermToFactors(PTRef tr, LALogic const & logic ) {
        std::vector<LinearFactor> factors;
        assert(logic.isLinearTerm(tr));
        if (logic.isLinearFactor(tr)) { return {splitLinearFactorToVarAndConst(tr, logic)}; }

        Pterm const & t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); ++i) {
            factors.push_back(splitLinearFactorToVarAndConst(t[i], logic));
        }
        return factors;
    }

    std::pair<LinearFactor, PTRef> separateVarFromTerm(PTRef var, PTRef term, LIALogic & logic) {
        assert(logic.isVar(var) and logic.isLinearTerm(term));
        auto factors = splitLinearTermToFactors(term, logic);
        LinearFactor const * varFactor = nullptr;
        vec<PTRef> args;
        for (auto const & factor : factors) {
            if (factor.var == var) {
                assert(varFactor == nullptr);
                varFactor = &factor;
            } else {
                args.push(factor.var == PTRef_Undef ? factor.coeff : logic.mkNumTimes(factor.coeff, factor.var));
            }
        }
        assert(varFactor);
        return {*varFactor, logic.mkNumPlus(args)};
    }
}

void ModelBasedProjection::postprocess(implicant_t & literals, LALogic & lalogic) {
    MapWithKeys<PtAsgn, PTRef, PtAsgnHash> bounds;
    for (PtAsgn literal : literals) {
        auto sign = literal.sgn;
        PTRef ineq = literal.tr;
        if (not lalogic.isNumLeq(ineq)) {
            throw std::logic_error("Only inequalities should be present in collect literals in MBP");
        }
        PTRef constant = lalogic.getPterm(ineq)[0];
        PTRef term = lalogic.getPterm(ineq)[1];
        assert(lalogic.isConstant(constant) and lalogic.isLinearTerm(term));
        PtAsgn key(term, sign);
        PTRef currentValue;
        if (bounds.peek(key, currentValue)) {
            // keep only the stronger bound
            if (sign == l_True) { // positive literal -> lower bound -> keep higher number
                if (lalogic.getNumConst(constant) > lalogic.getNumConst(currentValue)) {
                    bounds[key] = constant;
                }
            } else {
                assert(sign == l_False);
                // negative literal -> upper bound -> keep lower number
                if (lalogic.getNumConst(constant) < lalogic.getNumConst(currentValue)) {
                    bounds[key] = constant;
                }
            }
        } else {
            bounds.insert(key, constant);
        }
    }
    auto const & keys = bounds.getKeys();
    if (keys.size() < literals.size()) { // something actually changed
        literals.clear();
        for (PtAsgn key : keys) {
            literals.push_back(PtAsgn(lalogic.mkNumLeq(bounds[key], key.tr), key.sgn));
        }
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

    // Normalize equalities (this would be better to ensure some other way)
    std::for_each(implicant.begin(), implicant.end(), [lalogic](PtAsgn & lit) {
       if (lalogic->isEquality(lit.tr)) {
           PTRef lhs = lalogic->getPterm(lit.tr)[0];
           PTRef rhs = lalogic->getPterm(lit.tr)[1];
           if (lhs == lalogic->getTerm_NumZero() or rhs == lalogic->getTerm_NumZero() or lalogic->isNumConst(lhs) or lalogic->isNumConst(rhs)) {
               // already normalized
               return;
           }
           lit.tr = lalogic->mkEq(lalogic->mkNumMinus(lhs, rhs), lalogic->getTerm_NumZero());
       }
    });

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
                if (replacement == logic.getTerm_true()) {
                    // This could happen if the original inequality is like "x != x + 1"
                    it->tr = logic.getTerm_true();
                    it->sgn = l_True;
                } else {
                    assert(logic.isNot(replacement)); // strict inequalities are expressed as negations of non-strict ones
                    it->tr = logic.getPterm(replacement)[0]; // we store the non-strict inequality, the sign is already set to false
                    assert(it->sgn == l_False);
                }
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
        if (ineq == logic.getTerm_true()) { // this is still possible if we had true disequality at the beginning (x != x + 1)
            assert(sign == l_True);
            continue;
        }
        bool isStrict = sign == l_False;
        bool isLower = sign != l_False; // inequalities are of form "c <= t" where c is constant
        PTRef constant = lalogic->getPterm(ineq)[0];
        assert(lalogic->isConstant(constant));
        PTRef linTerm = lalogic->getPterm(ineq)[1];
        assert(lalogic->isLinearTerm(linTerm));
        auto factors = splitLinearTermToFactors(linTerm, *lalogic);
        auto interestingVarIt = std::find_if(factors.begin(), factors.end(), [var](LinearFactor factor) {
            return factor.var == var;
        });
        assert(interestingVarIt != factors.end());
        auto coeffPTRef = interestingVarIt->coeff;
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
            auto newCoeff = lalogic->getNumConst(factor.coeff) / coeff;
            factor.coeff = lalogic->mkConst(newCoeff);
            boundArgs.push(lalogic->mkNumTimes(factor.var, factor.coeff)); // MB: no simplification, could be insertTermHash directly
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
        if (otherVal > currentVal or (otherVal == currentVal and bound.strict)) {
            highestLowerBound = &bound;
        }
    }
    // perform substitution
    implicant_t newLiterals;
    for (Bound const & bound : bounds) {
        PTRef subResult = substituteBound(*highestLowerBound, bound, *lalogic);
        assert(model.evaluate(subResult) == logic.getTerm_true());
        if (lalogic->isNumEq(subResult)) {
            throw std::logic_error("This should not happen anymore");
        }
        else if (subResult != logic.getTerm_true()) {
            PtAsgn newLiteral = lalogic->isNot(subResult) ? PtAsgn(lalogic->getPterm(subResult)[0], l_False)
                                                       : PtAsgn(subResult, l_True);
            newLiterals.push_back(newLiteral);
        }
    }
    postprocess(newLiterals, *lalogic);
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
    if (dynamic_cast<LIALogic*>(&logic)) {
        return projectIntegerVars(boolEndIt, tmp.end(), std::move(implicant), model);
    }
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

PTRef ModelBasedProjection::projectIntegerVars(PTRef * beg, PTRef * end, implicant_t implicant, Model & model) {
    LIALogic & lialogic = dynamic_cast<LIALogic&>(logic);
    div_constraints_t divConstraints;
    for (PTRef * it = beg; it != end; ++it) {
        PTRef var = *it;
        if (not lialogic.isIntVar(lialogic.getSymRef(var))) {
            throw std::logic_error("Non-integer variable encountered in MBP for integers!");
        }
        if (not divConstraints.empty()) {
            processDivConstraints(var, divConstraints, implicant, model);
        } else {
            processClassicLiterals(var, divConstraints, implicant, model);
        }
    }
    vec<PTRef> tmp;
    for (PtAsgn literal : implicant) {
        tmp.push(literal.sgn == l_True ? literal.tr : logic.mkNot(literal.tr));
    }
    if (not divConstraints.empty()) {
        for (auto const & constraint : divConstraints) {
            assert(lialogic.isConstant(constraint.constant));
            PTRef mod = lialogic.mkIntMod(constraint.term, constraint.constant);
            tmp.push(logic.mkEq(mod, lialogic.getTerm_NumZero()));
        }
    }
    return logic.mkAnd(tmp);
}

namespace {
// TODO: replace when available in FastRationals
FastRational mbp_fastrat_fdiv_r(FastRational const & n, FastRational const & d) {
    FastRational q = fastrat_fdiv_q(n, d);
    FastRational u = n - (q*d);
    return u;
}
}

/*
 * Projecting single integer variable in the presence of divisibility constraints.
 * Implemented according to the description from https://easychair.org/publications/paper/jmM
 * Bjorner & Janota, Playing with Quantified Satisfaction, LPAR-20, 2015
 */
void ModelBasedProjection::processDivConstraints(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model) {
    LIALogic & lialogic = dynamic_cast<LIALogic&>(logic);
    LATermUtils utils(lialogic);
    auto itInterestingEnd = std::partition(divConstraints.begin(), divConstraints.end(), [&](DivisibilityConstraint const& c) {
        return utils.termContainsVar(c.term, var);
    });
    if (itInterestingEnd != divConstraints.begin()) {
        // there are some div constraints for this variable
        auto beg = divConstraints.begin();
        auto end = itInterestingEnd;
        std::vector<FastRational> divisors;
        std::transform(beg, end, std::back_inserter(divisors), [&lialogic](DivisibilityConstraint const& constraint) {
            auto const& val = lialogic.getNumConst(constraint.constant);
            assert(val.isInteger() and val.sign() > 0);
            return val;
        });
        FastRational d = divisors[0];
        // TODO: std::accumulate?
        std::for_each(beg + 1, end, [&](DivisibilityConstraint const & next) {
            d = lcm(d, lialogic.getNumConst(next.constant));
        });
        // TODO: add fastrat_fdiv_r
        FastRational const& val = lialogic.getNumConst(model.evaluate(var));
        FastRational u = mbp_fastrat_fdiv_r(val,d);
        assert(u.sign() >= 0 and u.isInteger());

        // update divisibility constraints by substituting u for x
        // TODO: make this more efficient
        TermUtils::substitutions_map subst;
        subst.insert({var, lialogic.mkConst(u)});
        TermUtils tutils(logic);
        std::for_each(beg, end, [&tutils, &subst](DivisibilityConstraint & constraint) {
            constraint.term = tutils.varSubstitute(constraint.term, subst);
        });

        // update the classic constraints and the variable that needs to be eliminated
        PTRef replacementVar = lialogic.mkNumVar("MBP_LIA_tmp");
        subst.clear();
        // v -> u + d * v_tmp
        subst.insert({var, lialogic.mkNumPlus(lialogic.mkConst(u), lialogic.mkNumTimes(lialogic.mkConst(d), replacementVar))});
        // TODO: only for those that contain the variable?
        std::for_each(implicant.begin(), implicant.end(), [&](PtAsgn & lit){
            lit.tr = tutils.varSubstitute(lit.tr, subst);
        });
        var = replacementVar;
    }
    processClassicLiterals(var, divConstraints, implicant, model);
}

/*
 * At this point, the var is not present in the divisibility constraints, we only need to process the proper literals in the implicant.
 * These literals might still contain equalities, disequalities or strict inequalities (TODO: verify?)
 */
void ModelBasedProjection::processClassicLiterals(PTRef var, div_constraints_t & divConstraints, implicant_t & implicant, Model & model) {
    LIALogic & lialogic = dynamic_cast<LIALogic&>(logic);
    assert(lialogic.isNumVar(var));
    LATermUtils utils(lialogic);
    auto containsVar = [var, &utils](PtAsgn lit) {
        return utils.atomContainsVar(lit.tr, var);
    };
    // split the literals to those containing var and those not containing var
    auto interestingEnd = std::partition(implicant.begin(), implicant.end(), containsVar);

    // search for equality, replace disequalities and strict inequalities
    std::vector<LIABoundLower> lower;
    std::vector<LIABoundUpper> upper;
    std::vector<LIABound> equal;
    for (auto it = implicant.begin(); it != interestingEnd; ++it) {
        PtAsgn literal = *it;
        if (lialogic.isEquality(literal.tr)) {
            PTRef lhs = lialogic.getPterm(literal.tr)[0];
            PTRef rhs = lialogic.getPterm(literal.tr)[1];
            if (literal.sgn == l_True) {
                // Express as "ax = t" where "a > 0"
                PTRef zeroTerm = lialogic.mkNumMinus(lhs, rhs);
                auto res = separateVarFromTerm(var, zeroTerm, lialogic);
                LinearFactor factor = res.first;
                FastRational const& coeff = lialogic.getNumConst(factor.coeff);
                if (coeff.sign() < 0) {
                    equal.push_back(LIABound{.term = res.second, .coeff = lialogic.mkConst(-coeff)});
                } else {
                    assert(coeff.sign() > 0);
                    equal.push_back(LIABound{.term = lialogic.mkNumNeg(res.second), .coeff = factor.coeff});
                }
            } else {
                assert(literal.sgn == l_False);
                // replace the non-equality with the inequality that is true in the model
                PTRef zeroTerm = lialogic.mkNumMinus(lhs, rhs);
                PTRef valterm = model.evaluate(zeroTerm);
                assert(lialogic.getNumConst(valterm) >= 1 or lialogic.getNumConst(valterm) <= -1);
                FastRational const& val = lialogic.getNumConst(valterm);
                auto res = separateVarFromTerm(var, zeroTerm, lialogic);
                LinearFactor factor = res.first;
                FastRational const& coeff = lialogic.getNumConst(factor.coeff);
                if (val.sign() > 0) {
                    if (coeff.sign() > 0) {
                        lower.push_back(LIABoundLower{.term = lialogic.mkNumPlus(lialogic.getTerm_NumOne(), lialogic.mkNumNeg(res.second)), .coeff = factor.coeff});
                    } else {
                        upper.push_back(LIABoundUpper{.term = lialogic.mkNumPlus(lialogic.getTerm_NumMinusOne(), res.second), .coeff = lialogic.mkConst(-coeff)});
                    }
                } else {
                    assert(val.sign() < 0);
                    if (coeff.sign() > 0) {
                        upper.push_back(LIABoundUpper{.term = lialogic.mkNumPlus(lialogic.getTerm_NumMinusOne(), lialogic.mkNumNeg(res.second)), .coeff = factor.coeff});
                    } else {
                        lower.push_back(LIABoundLower{.term = lialogic.mkNumPlus(lialogic.getTerm_NumOne(), res.second), .coeff = lialogic.mkConst(-coeff)});
                    }
                }
            }
        } else {
            assert(lialogic.isNumLeq(literal.tr));
            if (literal.sgn == l_False) { // not (c <= t) <=> c > t <=> c - 1 >= t
                literal.sgn = l_True;
                auto sides = lialogic.leqToConstantAndTerm(literal.tr);
                assert(lialogic.isNumConst(sides.first));
                literal.tr = lialogic.mkNumGeq(lialogic.mkConst(lialogic.getNumConst(sides.first) - 1), sides.second);
            }
            assert(literal.sgn == l_True);
            auto sides = lialogic.leqToConstantAndTerm(literal.tr);
            PTRef zeroTerm = lialogic.mkNumMinus(sides.second, sides.first);
            auto res = separateVarFromTerm(var, zeroTerm, lialogic);
            LinearFactor factor = res.first;
            FastRational const& coeff = lialogic.getNumConst(factor.coeff);
            if (coeff.sign() > 0) {
                lower.push_back(LIABoundLower{.term = lialogic.mkNumNeg(res.second), .coeff = factor.coeff});
            } else {
                upper.push_back(LIABoundUpper{.term = res.second, .coeff = lialogic.mkConst(-coeff)});
            }
        }
    }

    if (equal.empty()) {
        // only upper and lower bounds
        if (lower.empty() or upper.empty()) { // this variable can be eliminated without any additional constraints
            implicant.erase(implicant.begin(), interestingEnd);
            return;
        }
        // pick greatest lower bound in the model
        auto getValue = [&](LIABoundLower const& bound) {
            assert(lialogic.getNumConst(bound.coeff) >= 1);
            return lialogic.getNumConst(model.evaluate(bound.term)) / lialogic.getNumConst(bound.coeff);
        };
        LIABoundLower const * greatestLowerBound = &lower[0];
        FastRational value = getValue(*greatestLowerBound);
        for (auto it = lower.begin() + 1; it != lower.end(); ++it) {
            auto const& bound = *it;
            auto otherVal = getValue(bound);
            if (otherVal > value) {
                greatestLowerBound = &bound;
                value = std::move(otherVal);
            }
        }
        implicant_t newLiterals;
        FastRational const& glbCoeff = lialogic.getNumConst(greatestLowerBound->coeff);
        // handle lower bounds
        for (auto const& bound : lower) {
            if (&bound == greatestLowerBound) { continue; }
            PTRef lhs = glbCoeff.isOne() ? bound.term : lialogic.mkNumTimes(bound.term, greatestLowerBound->coeff);
            PTRef rhs = lialogic.getNumConst(bound.coeff).isOne() ? greatestLowerBound->term : lialogic.mkNumTimes(greatestLowerBound->term, bound.coeff);
            PTRef nBound = lialogic.mkNumLeq(lhs, rhs);
            if (nBound != lialogic.getTerm_true()) { // This can happen when we have a stronger and weaker bound on the same term
                newLiterals.push_back(PtAsgn(nBound, l_True));
            }
        }
        // handle upper bounds
        for (auto const& bound : upper) {
            auto res = resolve(*greatestLowerBound, bound, model, lialogic);
            assert(res.bounds.size() <= 2);
            for (PTRef nBound : res.bounds) {
                assert(nBound != lialogic.getTerm_true());
                newLiterals.push_back(PtAsgn(nBound, l_True));
            }
            if (res.hasDivConstraint) {
                divConstraints.push_back(res.constraint);
            }
        }
        // add literals not containing the variable
        newLiterals.insert(newLiterals.end(), interestingEnd, implicant.end());
        implicant = std::move(newLiterals);
        return;
    } else {
        implicant_t newLiterals;
        LIABound const& eqBound = equal[0];
        assert(lialogic.getNumConst(eqBound.coeff).sign() > 0 and lialogic.getNumConst(eqBound.coeff).isInteger());
        // equal bounds
        for (auto it = equal.begin() + 1; it != equal.end(); ++it) {
            // ax = t; bx = s => as = bt
            LIABound const & otherBound = *it;
            assert(lialogic.getNumConst(otherBound.coeff).sign() > 0 and lialogic.getNumConst(otherBound.coeff).isInteger());
            PTRef lhs = lialogic.mkNumTimes(otherBound.term, eqBound.coeff);
            PTRef rhs = lialogic.mkNumTimes(eqBound.term, otherBound.coeff);
            PTRef newLit = lialogic.mkEq(lhs, rhs);
            if (newLit != lialogic.getTerm_true()) {
                newLiterals.push_back(PtAsgn(newLit, l_True));
            }
        }
        // lower bounds
        for (auto const & lowerBound : lower) {
            assert(lialogic.getNumConst(lowerBound.coeff).sign() > 0 and lialogic.getNumConst(lowerBound.coeff).isInteger());
            // ax = t; s <= bx => as <= bt
            PTRef lhs = lialogic.mkNumTimes(lowerBound.term, eqBound.coeff);
            PTRef rhs = lialogic.mkNumTimes(eqBound.term, lowerBound.coeff);
            PTRef newLit = lialogic.mkNumLeq(lhs, rhs);
            if (newLit != lialogic.getTerm_true()) {
                newLiterals.push_back(PtAsgn(newLit, l_True));
            }
        }
        // upper bounds
        for (auto const & upperBound : upper) {
            assert(lialogic.getNumConst(upperBound.coeff).sign() > 0 and lialogic.getNumConst(upperBound.coeff).isInteger());
            // ax = t; s >= bx => as >= bt
            PTRef lhs = lialogic.mkNumTimes(upperBound.term, eqBound.coeff);
            PTRef rhs = lialogic.mkNumTimes(eqBound.term, upperBound.coeff);
            PTRef newLit = lialogic.mkNumGeq(lhs, rhs);
            if (newLit != lialogic.getTerm_true()) {
                newLiterals.push_back(PtAsgn(newLit, l_True));
            }
        }
        // From the equality ax = t it also follows that t must be divisible by a
        assert(lialogic.getNumConst(eqBound.coeff).sign() > 0);
        if (eqBound.coeff != lialogic.getTerm_NumOne()) {
            divConstraints.push_back(DivisibilityConstraint{.constant = eqBound.coeff, .term = eqBound.term});
        }
        // add literals not containing the variable
        newLiterals.insert(newLiterals.end(), interestingEnd, implicant.end());
        implicant = std::move(newLiterals);
        return;
    }
    throw std::logic_error("UNREACHABLE!");
}

/*
 * Resolves the lower bound with the upper bound (on some variable) under the given model M.
 * Possibly adds new divisibility constraints.
 *
 * Given upper bound ax <= t and lower bound bx >= s, the resolvent is
 * 1. as + (a-1)(b-1) <= bt                             if (a-1)(b-1) <= M(bt - as)
 * 2. as <= bt and a(s+d) <= bt and b|(s+d)             elif a>=b and d:=M(-s) mod b
 * 3. as <= bt and as <= b(t-d) and a|(t-d)             else b>a and d:=M(t) mod a
 * */
ModelBasedProjection::ResolveResult ModelBasedProjection::resolve(LIABoundLower const & lower, LIABoundUpper const & upper, Model & model, LIALogic & lialogic) {
    ResolveResult result;
    PTRef a_term = upper.coeff;
    PTRef b_term = lower.coeff;
    auto const& a = lialogic.getNumConst(a_term);
    auto const& b = lialogic.getNumConst(b_term);
    assert(a.isInteger() and b.isInteger());
    assert(a.sign() > 0 and b.sign() > 0);
    PTRef t_term = upper.term;
    PTRef s_term = lower.term;
    PTRef as_term = lialogic.mkNumTimes(a_term, s_term);
    PTRef bt_term = lialogic.mkNumTimes(b_term, t_term);
    auto const& t = lialogic.getNumConst(model.evaluate(t_term));
    auto const& s = lialogic.getNumConst(model.evaluate(s_term));

    FastRational mul = (a-1)*(b-1);
    if (mul <= (b*t - a*s)) {
        // case 1
        PTRef nBound = lialogic.mkNumLeq(lialogic.mkNumPlus(as_term, lialogic.mkConst(mul)), bt_term);
        if (nBound != lialogic.getTerm_true()) {
            result.bounds.push_back(nBound);
        }
        result.hasDivConstraint = false;
        return result;
    }

    PTRef firstBound = lialogic.mkNumLeq(as_term, bt_term);
    if (firstBound != lialogic.getTerm_true()) {
        result.bounds.push_back(firstBound);
    }
    if (a >= b) {
        // case 2
        FastRational d = mbp_fastrat_fdiv_r(-s, b);
        assert(d.isInteger());
        PTRef modified = lialogic.mkNumPlus(s_term, lialogic.mkConst(d));
        if (not d.isZero()) {
            PTRef secondBound = lialogic.mkNumLeq(lialogic.mkNumTimes(a_term, modified), bt_term);
            assert(secondBound != lialogic.getTerm_true());
            result.bounds.push_back(secondBound);
        }
        result.constraint.constant = b_term;
        result.constraint.term = modified;
        result.hasDivConstraint = true;
    } else {
        // case 3
        FastRational d = mbp_fastrat_fdiv_r(t, a);
        assert(d.isInteger());
        PTRef modified = lialogic.mkNumMinus(t_term, lialogic.mkConst(d));
        if (not d.isZero()) {
            PTRef secondBound = lialogic.mkNumLeq(as_term, lialogic.mkNumTimes(b_term, modified));
            assert(secondBound != lialogic.getTerm_true());
            result.bounds.push_back(secondBound);
        }
        result.constraint.constant = a_term;
        result.constraint.term = modified;
        result.hasDivConstraint = true;
    }
    return result;
}

