//
// Created by Martin Blicha on 06.03.21.
//

#include "ModelBasedProjection.h"

#include "LRALogic.h"
#include "TreeOps.h"
#include "TermUtils.h"

#include <memory>


namespace{
    enum class BoundType {EXACT, LOWER, UPPER};

    struct Bound {
        BoundType type;
        PTRef val;
    };

    class VirtualSubstitution {
    protected:
        LALogic & logic;
    public:
        explicit VirtualSubstitution(LALogic & logic) : logic{logic} {};

        virtual ~VirtualSubstitution() = default;

        virtual PTRef substitute(Bound bound) const = 0;

    };

    class VirtualSubstitutionEqual : public VirtualSubstitution {
        PTRef val;
    public:
        VirtualSubstitutionEqual(PTRef val, LALogic & logic) : VirtualSubstitution(logic), val{val} {}

        virtual PTRef substitute(Bound bound) const override {
            BoundType type = bound.type;
            switch(type) {
                case BoundType::EXACT:
                    return logic.mkEq(val, bound.val);
                case BoundType::LOWER:
                    return logic.mkNumLt(bound.val, val);
                case BoundType::UPPER:
                    return logic.mkNumGt(bound.val, val);
                default:
                    assert(false);
                    throw std::logic_error("Unreachable!");
            }
        }
    };

    class VirtualSubstitutionLower : public VirtualSubstitution {
        PTRef val;
    public:
        VirtualSubstitutionLower(PTRef val, LALogic & logic) : VirtualSubstitution(logic), val{val} {}

        virtual PTRef substitute(Bound bound) const override {
            BoundType type = bound.type;
            switch(type) {
                case BoundType::EXACT:
                    return logic.getTerm_false();
                case BoundType::LOWER:
                    return logic.mkNumLeq(bound.val, val);
                case BoundType::UPPER:
                    return logic.mkNumGt(bound.val, val);
                default:
                    assert(false);
                    throw std::logic_error("Unreachable!");
            }
        }
    };

    class VirtualSubstitutionMinusInf : public VirtualSubstitution {
    public:
        VirtualSubstitutionMinusInf(LALogic & logic) : VirtualSubstitution(logic) {}

        virtual PTRef substitute(Bound bound) const override {
            BoundType type = bound.type;
            switch(type) {
                case BoundType::EXACT:
                case BoundType::LOWER:
                    return logic.getTerm_false();
                case BoundType::UPPER:
                    return logic.getTerm_true();
                default:
                    assert(false);
                    throw std::logic_error("Unreachable!");
            }
        }
    };

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
    std::vector<PtAsgn> literals; // collect literals in std::vector, and also deal with equalities
    for (PtAsgn ptasgn : implicant) {
        if (lalogic->isNumEq(ptasgn.tr)) { // special handling of equality
            PTRef lhs = lalogic->getPterm(ptasgn.tr)[0];
            PTRef rhs = lalogic->getPterm(ptasgn.tr)[1];
            if (ptasgn.sgn == l_True) { // just put both inequalities there
                literals.push_back(PtAsgn(lalogic->mkNumLeq(lhs, rhs), l_True));
                literals.push_back(PtAsgn(lalogic->mkNumLeq(rhs, lhs), l_True));
            } else if (ptasgn.sgn == l_False) {
                PTRef lt = lalogic->mkNumLt(lhs, rhs);
                PTRef gt = lalogic->mkNumGt(lhs, rhs);
                PTRef valid = model.evaluate(lt) == lalogic->getTerm_true() ? lt : gt;
                assert(model.evaluate(valid) == lalogic->getTerm_true());
                assert(lalogic->isNot(valid)); // strict inequality is negation of non-strict one
                literals.push_back(PtAsgn(lalogic->getPterm(valid)[0], l_False));
            }
        }
        else { // just copy the element if it is not TRUE
            if (not (lalogic->isTrue(ptasgn.tr) && ptasgn.sgn == l_True)) {
                literals.push_back(ptasgn);
            }
        }
    }
    LATermUtils utils(*lalogic);
    auto containsVar = [var, &utils](PtAsgn lit) {
        return utils.atomContainsVar(lit.tr, var);
    };
    // split the literals to those containing var and those not containing var
    auto interestingEnd = std::partition(literals.begin(), literals.end(), containsVar);
    // literals with the variable that we want to eliminate are now in the front of the vector
    // "interestingEnd" points to the first literal that does not contain the var anymore

    // collect the three types of bounds: equality, strict lower, strict upper
    std::vector<Bound> bounds;
    std::vector<PTRef> lBounds;
    std::vector<PTRef> eBounds;
    for (auto it = literals.begin(); it != interestingEnd; ++it) {
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
        std::vector<std::pair<PTRef, PTRef>> factorsVec(factors.begin(), factors.end());
        auto interestingVarIt = std::find_if(factorsVec.begin(), factorsVec.end(), [var](std::pair<PTRef, PTRef> factor) {
            return factor.first == var;
        });
        assert(interestingVarIt != factorsVec.end());
        auto coeffPTRef = interestingVarIt->second;
        factorsVec.erase(interestingVarIt);
        auto coeff = lalogic->getNumConst(coeffPTRef);
        if (coeff.sign() < 0) {
            isLower = !isLower;
        }
        PTRef newConstant = lalogic->mkConst(lalogic->getNumConst(constant) / coeff);
        coeff.negate();
        // update the coefficients in the factor
        vec<PTRef> boundArgs;
        for (auto & factor : factorsVec) { // in place update
            auto newCoeff = lalogic->getNumConst(factor.second) / coeff;
            factor.second = lalogic->mkConst(newCoeff);
            boundArgs.push(lalogic->mkNumTimes(factor.first, factor.second)); // MB: no simplification, could be insertTermHash directly
        }
        boundArgs.push(newConstant);
        PTRef bound = lalogic->mkNumPlus(boundArgs); // MB: no simplification should happen, could be insertTermHash
        // Remember the bound
        // MB: TODO: Experimental! Verify/test if we can ignore the part of non-strict inequality that is not satisfied by the model!
        if (isStrict) {
            auto boundType = isLower ? BoundType::LOWER : BoundType::UPPER;
            bounds.push_back(Bound{.type = boundType, .val = bound});
            if (isLower) { lBounds.push_back(bound); }
        } else {
            // decide based on model which one to used; MB: double check the correctness of this!
            PTRef boundVal = model.evaluate(bound);
            assert(lalogic->isConstant(boundVal));
            if (boundVal == model.evaluate(var)) {
                bounds.push_back(Bound{.type = BoundType::EXACT, .val = bound});
                eBounds.push_back(bound);
            } else {
                auto boundType = isLower ? BoundType::LOWER : BoundType::UPPER;
                bounds.push_back(Bound{.type = boundType, .val = bound});
                if (isLower) { lBounds.push_back(bound); }
            }
        }
    }

    // pick the correct literal based on the model
    PTRef varVal = model.evaluate(var);
    assert(lalogic->isConstant(varVal));
    std::unique_ptr<VirtualSubstitution> substitution;
    for (PTRef eqBound : eBounds) {
        PTRef val = model.evaluate(eqBound);
        assert(lalogic->isConstant(val));
        if (val == varVal) {
            substitution.reset(new VirtualSubstitutionEqual(eqBound, *lalogic));
            break;
        }
    }
    if (!substitution && not lBounds.empty()) { // pick substitution from lower bounds
        // pick highers lower bound according to the model
        std::sort(lBounds.begin(), lBounds.end(), [lalogic,&model](PTRef b1, PTRef b2) {
            PTRef val1 = model.evaluate(b1);
            PTRef val2 = model.evaluate(b2);
            assert(lalogic->isConstant(val1) && lalogic->isConstant(val2));
            return lalogic->getNumConst(val1) > lalogic->getNumConst(val2);
        });
        // first is highest
        PTRef bound = lBounds[0];
        PTRef val = model.evaluate(bound); (void) val;
        assert(lalogic->isConstant(val) && lalogic->getNumConst(varVal) > lalogic->getNumConst(val));
        substitution.reset(new VirtualSubstitutionLower(bound, *lalogic));
    }
    if (!substitution) {
        substitution.reset(new VirtualSubstitutionMinusInf(*lalogic));
    }
    // perform virtual substitution
    implicant_t newLiterals;
    for (Bound bound : bounds) {
        PTRef subResult = substitution->substitute(bound);
        if (lalogic->isNumEq(subResult)) { // special case, which we need to handle
            PTRef lhs = lalogic->getPterm(subResult)[0];
            PTRef rhs = lalogic->getPterm(subResult)[1];
            newLiterals.push_back(PtAsgn(lalogic->mkNumLeq(lhs, rhs), l_True));
            newLiterals.push_back(PtAsgn(lalogic->mkNumLeq(rhs, lhs), l_True));
        }
        else {
            PtAsgn newLiteral = lalogic->isNot(subResult) ? PtAsgn(lalogic->getPterm(subResult)[0], l_False)
                                                       : PtAsgn(subResult, l_True);
            newLiterals.push_back(newLiteral);
        }
    }
    // don't forget the literals not containing the var to eliminate
    newLiterals.insert(newLiterals.end(), interestingEnd, literals.end());
    return std::move(newLiterals);
}

ModelBasedProjection::implicant_t ModelBasedProjection::getImplicant(PTRef fla, Model & model) {
    class CollectImplicantConfig :public DefaultVisitorConfig {
    private:
        Logic & logic;

        Model& model;

        implicant_t literals;

    public:
        CollectImplicantConfig(Logic& logic, Model& model) : logic(logic), model(model) {}

        implicant_t getImplicant() const { return std::move(literals); }

        void visit(PTRef term) override {
            assert(model.evaluate(term) == logic.getTerm_true());
            if (logic.isAtom(term)) {
                literals.push_back(PtAsgn(term, l_True));
            } else if (logic.isNot(term)) {
                PTRef child = logic.getPterm(term)[0];
                if (not logic.isAtom(child)) {
                    throw std::logic_error("Formula must be in NNF for implicant extraction!");
                }
                literals.push_back(PtAsgn(child, l_False));
            }
        }

        bool previsit(PTRef term) override {
            return logic.hasSortBool(term) && model.evaluate(term) == logic.getTerm_true();
        }
    };
    CollectImplicantConfig config(logic, model);
    TermVisitor<CollectImplicantConfig> collector(logic, config);
    collector.visit(fla);
    return config.getImplicant();
}

PTRef ModelBasedProjection::project(PTRef fla, const vec<PTRef> & varsToEliminate, Model & model) {
    auto checkImplicant = [&](implicant_t const& impl){
        for (auto const& elem : impl) {
            assert(elem.sgn == l_False or elem.sgn == l_True);
            assert((elem.sgn == l_False and model.evaluate(elem.tr) == logic.getTerm_false())
                or (elem.sgn == l_True and model.evaluate(elem.tr) == logic.getTerm_true()));
        }
    };
    auto implicant = getImplicant(fla, model);
//    dumpImplicant(std::cout, implicant);
    checkImplicant(implicant);
    for (PTRef var : varsToEliminate) {
//        std::cout << "Eliminating " << logic.printTerm(var) << std::endl;
        implicant = projectSingleVar(var, std::move(implicant), model);
//        dumpImplicant(std::cout, implicant);
        checkImplicant(implicant);
    }
    vec<PTRef> finalArgs;
    for (PtAsgn literal : implicant) {
        finalArgs.push(literal.sgn == l_True ? literal.tr : logic.mkNot(literal.tr));
    }
    return logic.mkAnd(finalArgs);
}

void ModelBasedProjection::dumpImplicant(std::ostream & out, implicant_t const& implicant) {
    out << "Implicant:\n";
    std::for_each(implicant.begin(), implicant.end(), [&](PtAsgn i) { out << logic.printTerm(i.tr) << ' ' << toInt(i.sgn) << '\n'; });
    out << std::endl;
}

