/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/
#include "LRALogic.h"

#include "SStore.h"
#include "PtStore.h"
#include "TreeOps.h"
#include "LA.h"
#include "Model.h"

const char* LRALogic::e_nonlinear_term = "Logic does not support nonlinear terms";

/***********************************************************
 * Class defining simplifications
 ***********************************************************/

//const char* LRALogic::tk_val_real_default = "1";
const char* LRALogic::tk_real_zero  = "0";
const char* LRALogic::tk_real_one   = "1";
const char* LRALogic::tk_real_neg   = "-";
const char* LRALogic::tk_real_minus = "-";
const char* LRALogic::tk_real_plus  = "+";
const char* LRALogic::tk_real_times = "*";
const char* LRALogic::tk_real_div   = "/";
const char* LRALogic::tk_real_lt    = "<";
const char* LRALogic::tk_real_leq   = "<=";
const char* LRALogic::tk_real_gt    = ">";
const char* LRALogic::tk_real_geq   = ">=";
const char* LRALogic::s_sort_real = "Real";

LRALogic::LRALogic(SMTConfig& c) :
        LALogic(c)
        , sym_Real_ZERO(SymRef_Undef)
        , sym_Real_ONE(SymRef_Undef)
        , sym_Real_NEG(SymRef_Undef)
        , sym_Real_MINUS(SymRef_Undef)
        , sym_Real_PLUS(SymRef_Undef)
        , sym_Real_TIMES(SymRef_Undef)
        , sym_Real_DIV(SymRef_Undef)
        , sym_Real_EQ(SymRef_Undef)
        , sym_Real_LEQ(SymRef_Undef)
        , sym_Real_LT(SymRef_Undef)
        , sym_Real_GEQ(SymRef_Undef)
        , sym_Real_GT(SymRef_Undef)
        , sym_Real_ITE(SymRef_Undef)
        , sort_REAL(SRef_Undef)
        , term_Real_ZERO(PTRef_Undef)
        , term_Real_ONE(PTRef_Undef)
        , term_Real_MINUSONE(PTRef_Undef)
        , split_eq(false)
{
    char* m;
    char** msg = &m;
    logic_type = opensmt::Logic_t::QF_LRA;
    sort_REAL = declareSort(s_sort_real, msg);
    ufsorts.remove(sort_REAL);
//    printf("Setting sort_REAL to %d at %p\n", sort_REAL.x, &(sort_REAL.x));
    vec<SRef> params;
    term_Real_ZERO = mkConst(sort_REAL, tk_real_zero);
    sym_Real_ZERO  = getSymRef(term_Real_ZERO);
    sym_store.setInterpreted(sym_Real_ZERO);
    term_Real_ONE  = mkConst(sort_REAL, tk_real_one);
    sym_Real_ONE   = getSymRef(term_Real_ONE);
    sym_store.setInterpreted(sym_Real_ONE);
    term_Real_MINUSONE  = mkConst(sort_REAL, "-1");
    params.push(sort_REAL);
    // Negation
    sym_Real_NEG = declareFun(tk_real_neg, sort_REAL, params, msg, true);
    sym_store.setInterpreted(sym_Real_NEG);
    params.push(sort_REAL);
    sym_Real_MINUS = declareFun(tk_real_neg, sort_REAL, params, msg, true);
    sym_store[sym_Real_MINUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_MINUS);
    sym_Real_PLUS  = declareFun(tk_real_plus, sort_REAL, params, msg, true);
    sym_store[sym_Real_PLUS].setNoScoping();
    sym_store[sym_Real_PLUS].setCommutes();
    sym_store[sym_Real_PLUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_PLUS);
    sym_Real_TIMES = declareFun(tk_real_times, sort_REAL, params, msg, true);
    sym_store[sym_Real_TIMES].setNoScoping();
    sym_store[sym_Real_TIMES].setLeftAssoc();
    sym_store[sym_Real_TIMES].setCommutes();
    sym_store.setInterpreted(sym_Real_TIMES);
    sym_Real_DIV   = declareFun(tk_real_div, sort_REAL, params, msg, true);
    sym_store[sym_Real_DIV].setNoScoping();
    sym_store[sym_Real_DIV].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_DIV);
    sym_Real_LEQ  = declareFun(tk_real_leq, sort_BOOL, params, msg, true);
    sym_store[sym_Real_LEQ].setNoScoping();
    sym_store[sym_Real_LEQ].setChainable();
    sym_store.setInterpreted(sym_Real_LEQ);
    sym_Real_LT   = declareFun(tk_real_lt, sort_BOOL, params, msg, true);
    sym_store[sym_Real_LT].setNoScoping();
    sym_store[sym_Real_LT].setChainable();
    sym_store.setInterpreted(sym_Real_LT);
    sym_Real_GEQ  = declareFun(tk_real_geq, sort_BOOL, params, msg, true);
    sym_store[sym_Real_GEQ].setNoScoping();
    sym_store[sym_Real_GEQ].setChainable();
    sym_store.setInterpreted(sym_Real_GEQ);
    sym_Real_GT   = declareFun(tk_real_gt, sort_BOOL, params, msg, true);
    sym_store[sym_Real_GT].setNoScoping();
    sym_store[sym_Real_GT].setChainable();
    sym_store.setInterpreted(sym_Real_GEQ);
    vec<SRef> ite_params;
    ite_params.push(sort_BOOL);
    ite_params.push(sort_REAL);
    ite_params.push(sort_REAL);
    sym_Real_ITE = declareFun(tk_ite, sort_REAL, ite_params, msg, true);
    //sym_store[sym_Real_ITE].setLeftAssoc();
    sym_store[sym_Real_ITE].setNoScoping();
    sym_store.setInterpreted(sym_Real_ITE);
}

const SymRef LRALogic::get_sym_Num_TIMES () const {return sym_Real_TIMES;}
const SymRef LRALogic::get_sym_Num_DIV () const {return sym_Real_DIV;}
const SymRef LRALogic::get_sym_Num_MINUS () const {return sym_Real_MINUS;}
const SymRef LRALogic::get_sym_Num_PLUS () const {return sym_Real_PLUS;}
const SymRef LRALogic::get_sym_Num_NEG () const {return sym_Real_NEG;}
const SymRef LRALogic::get_sym_Num_LEQ () const {return sym_Real_LEQ;}
const SymRef LRALogic::get_sym_Num_GEQ () const {return sym_Real_GEQ;}
const SymRef LRALogic::get_sym_Num_LT () const {return sym_Real_LT;}
const SymRef LRALogic::get_sym_Num_GT () const {return sym_Real_GT;}
const SymRef LRALogic::get_sym_Num_EQ () const {return sym_Real_EQ;}
const SymRef LRALogic::get_sym_Num_ZERO () const {return sym_Real_ZERO;}
const SymRef LRALogic::get_sym_Num_ONE () const {return sym_Real_ONE;}
const SymRef LRALogic::get_sym_Num_ITE () const {return sym_Real_ITE;}
const SRef LRALogic::get_sort_NUM () const {return sort_REAL;}

PTRef   LRALogic::getTerm_NumZero()     const  { return term_Real_ZERO; }
PTRef   LRALogic::getTerm_NumOne()      const  { return term_Real_ONE; }
PTRef   LRALogic::getTerm_NumMinusOne() const  { return term_Real_MINUSONE; }
bool    LRALogic::hasSortNum(PTRef tr)  const  { return hasSortReal(getPterm(tr).symb()); }


namespace{
enum class BoundType {EXACT, LOWER, UPPER};

struct Bound {
    BoundType type;
    PTRef val;
};

class VirtualSubstitution {
protected:
    LRALogic & logic;
public:
    VirtualSubstitution(LRALogic & logic) : logic{logic} {};

    virtual ~VirtualSubstitution() = default;

    virtual PTRef substitute(Bound bound) const = 0;

};

class VirtualSubstitutionEqual : public VirtualSubstitution {
    PTRef val;
public:
    VirtualSubstitutionEqual(PTRef val, LRALogic & logic) : VirtualSubstitution(logic), val{val} {}

    virtual PTRef substitute(Bound bound) const override {
        BoundType type = bound.type;
        switch(type) {
            case BoundType::EXACT:
                return bound.val == this->val ? logic.getTerm_true() : logic.getTerm_false();
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
    VirtualSubstitutionLower(PTRef val, LRALogic & logic) : VirtualSubstitution(logic), val{val} {}

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
    VirtualSubstitutionMinusInf(LRALogic & logic) : VirtualSubstitution(logic) {}

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

}

Logic::implicant_t LRALogic::modelBasedProjectionSingleVar(PTRef var, Logic::implicant_t implicant, Model & model) {
    assert(this->isVar(var));
    // if the variable is boolean, simply remove it from implicant
    if (isBoolAtom(var)) {
        auto it = std::find_if(implicant.begin(), implicant.end(), [var](PtAsgn literal) { return literal.tr == var; });
        if (it != implicant.end()) {
            it = implicant.erase(it);
            // the same boolean variable cannot be present twice in the implicant
            assert(std::find_if(it, implicant.end(), [var](PtAsgn literal) { return literal.tr == var; }) == implicant.end());
        }
        return implicant;
    }
    assert(isNumVar(var));
    // proper elimination of Real variable

    std::vector<PtAsgn> literals(implicant.begin(), implicant.end());
    auto containsVar = [var, this](PtAsgn lit) {
        PTRef atom = lit.tr;
        if (this->isBoolAtom(atom)) { return false;}
        assert(isNumLeq(atom));
        // inequalities have form "constant <= term"
        PTRef term = this->getPterm(atom)[1];
        assert(this->isLinearTerm(term));
        auto getVarFromFactor = [this](PTRef factor) {
            PTRef fvar, constant;
            this->splitTermToVarAndConst(factor, fvar, constant);
            return fvar;
        };
        if (this->isLinearFactor(term)) {
            return getVarFromFactor(term) == var;
        } else {
            assert(isNumPlus(term));
            for (int i = 0; i < this->getPterm(term).size(); ++i) {
                PTRef factor = this->getPterm(term)[i];
                PTRef factorVar = getVarFromFactor(factor);
                if (factorVar == var) { return true; }
            }
            return false;
        }
        assert(false); // Not reachable
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
        PTRef constant = this->getPterm(ineq)[0];
        assert(this->isConstant(constant));
        PTRef linTerm = this->getPterm(ineq)[1];
        assert(this->isLinearTerm(linTerm));
        auto factors = this->splitLinearTermToFactors(linTerm);
        std::vector<std::pair<PTRef, PTRef>> factorsVec(factors.begin(), factors.end());
        auto interestingVarIt = std::find_if(factorsVec.begin(), factorsVec.end(), [var](std::pair<PTRef, PTRef> factor) {
            return factor.first == var;
        });
        assert(interestingVarIt != factorsVec.end());
        auto coeffPTRef = interestingVarIt->second;
        factorsVec.erase(interestingVarIt);
        auto coeff = this->getNumConst(coeffPTRef);
        if (coeff.sign() < 0) {
            isLower = !isLower;
        }
        PTRef newConstant = this->mkConst(this->getNumConst(constant) / coeff);
        coeff.negate();
        // update the coefficients in the factor
        vec<PTRef> boundArgs;
        for (auto & factor : factorsVec) { // in place update
            auto newCoeff = this->getNumConst(factor.second) / coeff;
            factor.second = this->mkConst(newCoeff);
            boundArgs.push(this->mkNumTimes(factor.first, factor.second)); // MB: no simplification, could be insertTermHash directly
        }
        boundArgs.push(newConstant);
        PTRef bound = this->mkNumPlus(boundArgs); // MB: no simplification should happen, could be insertTermHash
        // Remember the bound
        // MB: TODO: Experimental! Verify/test if we can ignore the part of non-strict inequality that is not satisfied by the model!
        if (isStrict) {
            auto boundType = isLower ? BoundType::LOWER : BoundType::UPPER;
            bounds.push_back(Bound{.type = boundType, .val = bound});
            if (isLower) { lBounds.push_back(bound); }
        } else {
            // decide based on model which one to used; MB: double check the correctness of this!
            PTRef boundVal = model.evaluate(bound);
            assert(this->isConstant(boundVal));
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
    assert(this->isConstant(varVal));
    std::unique_ptr<VirtualSubstitution> substitution;
    for (PTRef eqBound : eBounds) {
        PTRef val = model.evaluate(eqBound);
        assert(this->isConstant(val));
        if (val == varVal) {
            substitution.reset(new VirtualSubstitutionEqual(eqBound, *this));
            break;
        }
    }
    if (!substitution && not lBounds.empty()) { // pick substitution from lower bounds
        // pick highers lower bound according to the model
        std::sort(lBounds.begin(), lBounds.end(), [this,&model](PTRef b1, PTRef b2) {
            PTRef val1 = model.evaluate(b1);
            PTRef val2 = model.evaluate(b2);
            assert(this->isConstant(val1) && this->isConstant(val2));
            return this->getNumConst(val1) > this->getNumConst(val2);
        });
        // first is highest
        PTRef bound = lBounds[0];
        PTRef val = model.evaluate(bound); (void) val;
        assert(this->isConstant(val) && this->getNumConst(varVal) > this->getNumConst(val));
        substitution.reset(new VirtualSubstitutionLower(bound, *this));
    }
    if (!substitution) {
        substitution.reset(new VirtualSubstitutionMinusInf(*this));
    }
    // perform virtual substitution
    implicant_t newLiterals;
    for (Bound bound : bounds) {
        PTRef subResult = substitution->substitute(bound);
        PtAsgn newLiteral = this->isNot(subResult) ? PtAsgn(this->getPterm(subResult)[0], l_False)
            : PtAsgn(subResult, l_True);
        newLiterals.insert(newLiteral);
    }
    return newLiterals;
}
