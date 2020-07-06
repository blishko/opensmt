//
// Created by Martin Blicha on 20.06.20.
//

#include "TermVisitor.h"

PTRef CollectImplicantTermVisitor::visitAndSimplify(PTRef term) {

    if (isInCache(term)) { return getFromCache(term); }
    PTRef simplified = PTRef_Undef;
    PTRef trueTerm = logic.getTerm_true();
    PTRef falseTerm = logic.getTerm_false();
    if (logic.isConstant(term)) {
        simplified = term;
    }
    else if (logic.isNot(term)) {
        PTRef arg_simpl = visitAndSimplify(logic.getPterm(term)[0]);
        assert(arg_simpl != PTRef_Undef); // Term should be visited only when it has known value in the model
        simplified = logic.mkNot(arg_simpl);
    }
    else if (logic.isAnd(term)) {
        PTRef val = model.evaluate(term);
        assert(val != PTRef_Undef);
        assert(val == trueTerm || val == falseTerm);
        if (val == trueTerm) {
            // all children must be satisfied
            auto size = logic.getPterm(term).size();
            simplified = trueTerm;
            for (int i = 0; i < size; ++i) {
                PTRef child = logic.getPterm(term)[i];
                assert(model.evaluate(child) == trueTerm);
                simplified = visitAndSimplify(child);
                assert(simplified == trueTerm);
            }
        } else {
            assert(val == falseTerm);
            // some child is falsified
            auto size = logic.getPterm(term).size();
            PTRef falsifiedChild = PTRef_Undef;
            for (int i = 0; i < size; ++i) {
                PTRef child = logic.getPterm(term)[i];
                if (model.evaluate(child) == falseTerm) {
                    falsifiedChild = child;
                    break;
                }
            }
            assert(falsifiedChild != PTRef_Undef);
            simplified = visitAndSimplify(falsifiedChild);
            assert(simplified == falseTerm);
        }
    } else if (logic.isOr(term)) {
        PTRef val = model.evaluate(term);
        assert(val != PTRef_Undef);
        assert(val == trueTerm || val == falseTerm);
        if (val == falseTerm) {
            // all children must be falsified
            auto size = logic.getPterm(term).size();
            simplified = falseTerm;
            for (int i = 0; i < size; ++i) {
                PTRef child = logic.getPterm(term)[i];
                assert(model.evaluate(child) == falseTerm);
                simplified = visitAndSimplify(child);
                assert(simplified == falseTerm);
            }
        } else {
            assert(val == trueTerm);
            // some child is satisfied
            auto size = logic.getPterm(term).size();
            PTRef satisfiedChild = PTRef_Undef;
            for (int i = 0; i < size; ++i) {
                PTRef child = logic.getPterm(term)[i];
                if (model.evaluate(child) == trueTerm) {
                    satisfiedChild = child;
                    break;
                }
            }
            assert(satisfiedChild != PTRef_Undef);
            simplified = visitAndSimplify(satisfiedChild);
            assert(simplified == trueTerm);
        }
    } else if (logic.isIteVar(term)) {
        auto ite = logic.generalizedITEs[term];
        auto it = std::find_if(ite.cases.begin(), ite.cases.end(),
            [this, trueTerm](Logic::Cases::Case const& kase ) { return visitAndSimplify(kase.condition) == trueTerm; });
        PTRef chosenBranch = it != ite.cases.end() ? it->result : ite.defaultRes;
        assert(logic.hasSortBool(chosenBranch)); // MB: Here we are handling only Boolean ITEs
        simplified = visitAndSimplify(chosenBranch);
    } else if (logic.isBoolAtom(term)) { // must be AFTER ITEs are handled
        simplified = registerAtom(term);
    } else if (logic.isAtom(term)) { // Theory-specific handling of theory atoms
        assert(logic.isTheoryTerm(term));
        simplified = simplifyAndVisitTheoryAtom(term);
    } else if (logic.isEquality(term)) {
        assert(not logic.isTheoryEquality(term));
        // equality of boolean terms
        PTRef lhs = logic.getPterm(term)[0];
        PTRef rhs = logic.getPterm(term)[1];
        PTRef simplifiedLHS = visitAndSimplify(lhs);
        PTRef simplifiedRHS = visitAndSimplify(rhs);
        simplified = (lhs == simplifiedLHS && rhs == simplifiedRHS) ? term
            : logic.mkEq(simplifiedLHS, simplifiedRHS);
    }
    if (simplified == PTRef_Undef) {
        std::cerr << logic.printTerm(term) << std::endl;
        throw std::logic_error{"Unsupported structure of formula"};
    }
    cacheResults(term, simplified);
    return simplified;
}

PTRef CollectImplicantTermVisitor::registerAtom(PTRef atom) {
    PTRef val = model.evaluate(atom);
    assert(val == logic.getTerm_true() || val == logic.getTerm_false());
    auto sign = val == logic.getTerm_true() ? l_True : l_False;
    literals.insert(PtAsgn(atom, sign));
    return val;
}

void CollectImplicantTermVisitor::cacheResults(PTRef original, PTRef simplified) {
    cache.insert(std::make_pair(original, simplified));
}

//void ToNNFVisitor::visit_(PTRef root) {
//    this->res = transform(root);
//}
//
//PTRef ToNNFVisitor::transform(PTRef term) {
//    auto it = transformed.find(term);
//    if (it != transformed.end()) { return it->second; }
//
//    if (logic.isAtom(term)) {
//        transformed.insert(std::make_pair(term, term));
//        return term;
//    }
//    if (logic.isAnd(term)) {
//        auto size = logic.getPterm(term).size();
//        vec<PTRef> nargs;
//        nargs.capacity(size);
//        for (int i = 0; i < size; ++i) {
//            PTRef child = logic.getPterm(term)[i];
//            nargs.push(transform(child));
//        }
//        PTRef nterm = logic.mkAnd(nargs);
//        transformed.insert(std::make_pair(term, nterm));
//        return nterm;
//    }
//
//    if (logic.isOr(term)) {
//        auto size = logic.getPterm(term).size();
//        vec<PTRef> nargs;
//        nargs.capacity(size);
//        for (int i = 0; i < size; ++i) {
//            PTRef child = logic.getPterm(term)[i];
//            nargs.push(transform(child));
//        }
//        PTRef nterm = logic.mkOr(nargs);
//        transformed.insert(std::make_pair(term, nterm));
//        return nterm;
//    }
//
//    if (logic.isNot(term)) {
//        PTRef npos = transform(logic.getPterm(term)[0]);
//        PTRef nterm = negate(npos);
//        transformed.insert(std::make_pair(term, nterm));
//        return nterm;
//    }
//
//    throw std::logic_error("Unexpected term in NNF transformation");
//
//}
//
//PTRef ToNNFVisitor::negate(PTRef term) {
//    // term must already be in NNF form
//    assert(logic.isAnd(term) || logic.isOr(term) || logic.isAtom(term)
//        || (logic.isNot(term) && logic.isAtom(logic.getPterm(term)[0])));
//
//    auto it = negated.find(term);
//    if (it != negated.end()) { return it->second; }
//
//    if (logic.isNot(term)) {
//        assert(logic.isAtom(logic.getPterm(term)[0]));
//        PTRef nterm = logic.getPterm(term)[0];
//        negated.insert(std::make_pair(term, nterm));
//        return nterm;
//    }
//
//    if (logic.isAtom(term)) {
//        PTRef nterm = logic.mkNot(term);
//        negated.insert(std::make_pair(term, nterm));
//        return nterm;
//    }
//
//    if (logic.isAnd(term)) {
//        auto size = logic.getPterm(term).size();
//        vec<PTRef> nargs;
//        nargs.capacity(size);
//        for (int i = 0; i < size; ++i) {
//            PTRef child = logic.getPterm(term)[i];
//            nargs.push(negate(child));
//        }
//        PTRef nterm = logic.mkOr(nargs);
//        negated.insert(std::make_pair(term, nterm));
//        return nterm;
//    }
//
//    if (logic.isOr(term)) {
//        auto size = logic.getPterm(term).size();
//        vec<PTRef> nargs;
//        nargs.capacity(size);
//        for (int i = 0; i < size; ++i) {
//            PTRef child = logic.getPterm(term)[i];
//            nargs.push(negate(child));
//        }
//        PTRef nterm = logic.mkAnd(nargs);
//        negated.insert(std::make_pair(term, nterm));
//        return nterm;
//    }
//    assert(false); // UNREACHABLE
//    throw std::logic_error("Error in NNF transformation");
//}

void LRACollectImplicantTermVisitor::visit_(PTRef term) {
    PTRef res = visitAndSimplify(term);
    assert(res == logic.getTerm_true()); (void) res;
}

PTRef LRACollectImplicantTermVisitor::simplifyAndVisitTheoryAtom(PTRef atom) {
    // NOTE: No caching here, the caller takes care of that
    assert(lralogic.isNumLeq(atom) || lralogic.isNumEq(atom));
    if (lralogic.isNumLeq(atom)) {
        PTRef constant = lralogic.getPterm(atom)[0];
        assert(lralogic.isNumConst(constant));
        PTRef term = lralogic.getPterm(atom)[1];
        assert(lralogic.isLinearTerm(term));
        PTRef simplifiedTerm = simplifyAndVisitLinearTerm(term);
        PTRef simplifiedAtom = simplifiedTerm == term ? atom : lralogic.mkNumLeq(constant, simplifiedTerm);
        return registerAtom(simplifiedAtom);
    } else if (lralogic.isNumEq(atom)) {
        PTRef lhs = lralogic.getPterm(atom)[0];
        PTRef rhs = lralogic.getPterm(atom)[1];
        assert(lralogic.isLinearTerm(lhs) && lralogic.isLinearTerm(rhs));
        PTRef simplifiedLHS = simplifyAndVisitLinearTerm(lhs);
        PTRef simplifiedRHS = simplifyAndVisitLinearTerm(rhs);
        PTRef simplifiedAtom = (simplifiedLHS == lhs && simplifiedRHS == rhs) ? atom
            : lralogic.mkEq(simplifiedLHS, simplifiedRHS);
        return registerAtom(simplifiedAtom);
    }
    assert(false); // UNREACHABLE
    throw std::logic_error("Error in implicant computation");


}

PTRef LRACollectImplicantTermVisitor::simplifyAndVisitLinearTerm(PTRef term) {
    assert(lralogic.isLinearTerm(term));
    if (this->isInCache(term)) {
        return getFromCache(term);
    }
    if (lralogic.isLinearFactor(term)) {
        return simplifyAndVisitLinearFactor(term);
        // do not store in cache here, it is done in simplifyAndVisitLinearFactor
    }
    else {
        // split to individual factors
        assert(lralogic.isNumPlus(term));
        auto size = lralogic.getPterm(term).size();
        bool changed = false;
        vec<PTRef> nargs;
        for (int i = 0; i < size; ++i) {
            PTRef factor = lralogic.getPterm(term)[i];
            PTRef simplifiedFactor = simplifyAndVisitLinearFactor(factor);
            changed |= factor != simplifiedFactor;
            nargs.push(simplifiedFactor);
        }
        PTRef simplifiedTerm = changed ? lralogic.mkNumPlus(nargs) : term;
        cacheResults(term, simplifiedTerm);
        return simplifiedTerm;
    }
}

PTRef LRACollectImplicantTermVisitor::simplifyAndVisitLinearFactor(PTRef factor) {
    assert(lralogic.isLinearFactor(factor));
    if (this->isInCache(factor)) {
        return getFromCache(factor);
    }
    if (lralogic.isNumVar(factor)) {
        return simplifyAndVisitVariable(factor);
        // No caching here, it's done in simplifyAndVisitVariable
    }
    else if (lralogic.isNumConst(factor)) {
        cacheResults(factor, factor);
        return factor;
    }
    else {
        assert(lralogic.isNumTimes(factor));
        auto split = lralogic.splitLinearFactorToVarAndConst(factor);
        PTRef var = split.first;
        PTRef constant = split.second;
        PTRef simplifiedVar = simplifyAndVisitVariable(var);
        PTRef simplifiedFactor = simplifiedVar == var ? factor : lralogic.mkNumTimes(constant, simplifiedVar);
        cacheResults(factor, simplifiedFactor);
        return simplifiedFactor;
    }
}

PTRef LRACollectImplicantTermVisitor::simplifyAndVisitVariable(PTRef var) {
    assert(lralogic.isNumVar(var));
    if (this->isInCache(var)) {
        return getFromCache(var);
    }
    if (lralogic.isIteVar(var)) {
        auto ite = logic.generalizedITEs[var];
        auto it = std::find_if(ite.cases.begin(), ite.cases.end(),
                               [this](Logic::Cases::Case const& kase ) { return visitAndSimplify(kase.condition) == lralogic.getTerm_true(); });
        PTRef chosenBranch = it != ite.cases.end() ? it->result : ite.defaultRes;
        // evaluate condition and based on the value choose the appropriate branch
        assert(lralogic.hasSortNum(chosenBranch));
        PTRef simplifiedVar = simplifyAndVisitLinearTerm(chosenBranch);
        cacheResults(var, simplifiedVar);
        return simplifiedVar;
    } else {
        // normal var, don't do anything
        cacheResults(var, var);
        return var;
    }
}
