//
// Created by Martin Blicha on 20.08.20.
//

#include "TermUtils.h"

#include "LALogic.h"

/** Given an equality 'eq' containing variable 'var', try to derive a definition of 'var' from 'eq'.
    Returns the derived definition or PTRef_Undef is no definition could be derived
 */
PTRef TrivialQuantifierElimination::tryGetSubstitutionFromEquality(PTRef var, PTRef eq) const {
    assert(logic.isVar(var) and logic.isEquality(eq));
    PTRef lhs = logic.getPterm(eq)[0];
    PTRef rhs = logic.getPterm(eq)[1];
    if (logic.hasSortBool(var)) {
        // the only possibility how to get definition here is if one side of 'eq' is 'not var'
        PTRef varNeg = logic.mkNot(var);
        if (lhs == varNeg) {
            return logic.mkNot(rhs);
        }
        if (rhs == varNeg) {
            return logic.mkNot(lhs);
        }
        return PTRef_Undef;
    }
    if (logic.getLogic() == opensmt::Logic_t::QF_LIA || logic.getLogic() == opensmt::Logic_t::QF_LRA) {
        LALogic & lalogic = dynamic_cast<LALogic &>(logic);
        if (not lalogic.isNumVar(var)) {
            return PTRef_Undef;
        }
        if (logic.hasSortBool(lhs)) {
            assert(logic.hasSortBool(rhs));
            return PTRef_Undef;
        }
        PTRef zeroTerm = lalogic.mkNumMinus(lhs, rhs);
        PTRef substitutionTerm = LATermUtils(lalogic).expressZeroTermFor(zeroTerm, var);
        // For LIA we should most likely check the coefficients in the result are Integers
        if (lalogic.getLogic() == opensmt::Logic_t::QF_LIA) {
            auto hasIntegerCoeff = [&lalogic](PTRef factor) {
                assert(lalogic.isLinearFactor(factor));
                PTRef v, c;
                lalogic.splitTermToVarAndConst(factor, v, c);
                return lalogic.getNumConst(c).isInteger();
            };
            if (lalogic.isLinearFactor(substitutionTerm)) {
                if (not hasIntegerCoeff(substitutionTerm)) {
                    return PTRef_Undef;
                }
            } else {
                auto argsCount = lalogic.getPterm(substitutionTerm).size();
                for (int i = 0; i < argsCount; ++i) {
                    PTRef factor = lalogic.getPterm(substitutionTerm)[i];
                    if (not hasIntegerCoeff(factor)) {
                        return PTRef_Undef;
                    }
                }
            }
        }
        return substitutionTerm;

    }
    return PTRef_Undef;
}

PTRef LATermUtils::expressZeroTermFor(PTRef zeroTerm, PTRef var) {
    assert(logic.isLinearTerm(zeroTerm) and logic.isNumVar(var));
    // split the zeroTerm to the factor with the variable 'var' and rest
    if (logic.isLinearFactor(zeroTerm)) {
        // simple case of 'c * v = 0', the resulting term is simply zero
        return logic.getTerm_NumZero();
    } else {
        assert(logic.isNumPlus(zeroTerm));
        PTRef varCoeff;
        vec<PTRef> otherFactors;
        auto size = logic.getPterm(zeroTerm).size();
        for (int i = 0; i < size; ++i) {
            PTRef factor = logic.getPterm(zeroTerm)[i];
            assert(logic.isLinearFactor(factor));
            PTRef factorVar;
            PTRef coeff;
            logic.splitTermToVarAndConst(factor, factorVar, coeff);
            if (factorVar == var) {
                varCoeff = coeff;
            } else {
                otherFactors.push(factor);
            }
        }
        // now we have 't = 0' where 't = c * var + t1' => 'var = t1/-c'
        PTRef res = logic.mkNumDiv(logic.mkNumPlus(otherFactors), logic.mkNumNeg(varCoeff));
        return res;
    }
}

void TermUtils::printTermWithLets(ostream & out, PTRef root) {
    // collect mapping of id to let expressions
    auto toLetId = [](PTRef x) -> std::string { return "l" + std::to_string(x.x); };
    std::vector<PTRef> dfsOrder;
    std::vector<std::pair<bool, PTRef>> queue; // true means parent and we should put it in the order; false means child and we should process it
    std::unordered_set<PTRef, PTRefHash> visited;
    queue.push_back({false, root});
    while (not queue.empty()) {
        auto current = queue.back();
        queue.pop_back();
        if (current.first) {
            dfsOrder.push_back(current.second);
            continue;
        }
        PTRef ref = current.second;
        visited.insert(ref);
        queue.push_back({true, ref});
        Pterm const & pterm = logic.getPterm(ref);
        for (int i = 0; i < pterm.size(); ++i) {
            if (visited.find(pterm[i]) == visited.end()) {
                queue.push_back({false, pterm[i]});
            }
        }
    }

    std::unordered_map<PTRef, std::string, PTRefHash> strRepr;

    auto toStr = [this, &strRepr](PTRef ref) -> std::string {
        Pterm const & pterm = logic.getPterm(ref);
        char * symbol = logic.printSym(pterm.symb());
        if (pterm.size() == 0) {
            std::string res(symbol);
            free(symbol);
            return res;
        }
        std::stringstream ss;
        ss << '(' << symbol << ' ';
        for (int i = 0; i < pterm.size(); ++i) {
            ss << strRepr.at(pterm[i]) << ' ';
        }
        ss << ')';
        free(symbol);
        return ss.str();
    };

    int letCount = 0;
    for (PTRef ref : dfsOrder) {
        auto actualRepr = toStr(ref);
        bool introduceLet = false;
        if (logic.isAnd(ref) or logic.isOr(ref)) { introduceLet = true; }
        if (introduceLet) {
            out << "(let " << '(' << toLetId(ref) << ' ' << actualRepr << ')';
            strRepr.insert({ref, toLetId(ref)});
        } else {
            strRepr.insert({ref, std::move(actualRepr)});
        }
    }

    out << strRepr.at(root) << std::string(letCount, ')');
}

class NNFTransformer {
    Logic & logic;

    std::unordered_map<PTRef, PTRef, PTRefHash> transformed;
    std::unordered_map<PTRef, PTRef, PTRefHash> negated;

    PTRef transform(PTRef);
    PTRef negate(PTRef);

public:
    NNFTransformer(Logic & logic) : logic(logic) {}

    PTRef toNNF(PTRef fla) { return transform(fla); };
};

PTRef NNFTransformer::transform(PTRef fla) {
    auto it = transformed.find(fla);
    if (it != transformed.end()) {
        return it->second;
    }
    if (logic.isAtom(fla)) {
        transformed.insert({fla, fla});
        return fla;
    }
    if (logic.isAnd(fla)) {
        auto size = logic.getPterm(fla).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            nargs.push(transform(child));
        }
        PTRef nfla = logic.mkAnd(nargs);
        transformed.insert({fla, nfla});
        return nfla;
    }
    if (logic.isOr(fla)) {
        auto size = logic.getPterm(fla).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            nargs.push(transform(child));
        }
        PTRef nfla = logic.mkOr(nargs);
        transformed.insert({fla, nfla});
        return nfla;
    }
    if (logic.isNot(fla)) {
        PTRef npos = transform(logic.getPterm(fla)[0]);
        PTRef nfla = negate(npos);
        transformed.insert({fla, nfla});
        return nfla;
    }
    assert(false);
    throw std::logic_error("Unexpected formula in NNF transformation");
}

PTRef NNFTransformer::negate(PTRef fla) {
    assert(logic.isAnd(fla) or logic.isOr(fla) or logic.isAtom(fla) or (logic.isNot(fla) and logic.isAtom(logic.getPterm(fla)[0])));
    auto it = negated.find(fla);
    if (it != negated.end()) {
        return it->second;
    }
    if (logic.isNot(fla)) {
        assert(logic.isAtom(logic.getPterm(fla)[0]));
        PTRef nfla = logic.getPterm(fla)[0];
        negated.insert({fla, nfla});
        return nfla;
    }
    if (logic.isAtom(fla)) {
        PTRef nfla = logic.mkNot(fla);
        negated.insert({fla, nfla});
        return nfla;
    }
    if (logic.isAnd(fla)) {
        auto size = logic.getPterm(fla).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            nargs.push(negate(child));
        }
        PTRef nfla = logic.mkOr(nargs);
        transformed.insert({fla, nfla});
        return nfla;
    }
    if (logic.isOr(fla)) {
        auto size = logic.getPterm(fla).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(fla)[i];
            nargs.push(negate(child));
        }
        PTRef nfla = logic.mkAnd(nargs);
        transformed.insert({fla, nfla});
        return nfla;
    }
    assert(false);
    throw std::logic_error("Unexpected formula in NNF transformation");
}


PTRef TermUtils::toNNF(PTRef fla) {
    if (not logic.hasSortBool(fla)) {
        throw std::invalid_argument("toNNF called with non-boolean formula!");
    }
    NNFTransformer nnfTransformer(logic);
    return nnfTransformer.toNNF(fla);
}
