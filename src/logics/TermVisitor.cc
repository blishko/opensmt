//
// Created by Martin Blicha on 20.06.20.
//

#include "TermVisitor.h"

void CollectImplicantTermVisitor::uncheckedVisit(PTRef term) {
    PTRef trueTerm = logic.getTerm_true();
    assert(model.evaluate(term) == trueTerm); // Yes or no??
    if (logic.isAtom(term)) {
        if (model.evaluate(term) == trueTerm) {
            literals.insert(PtAsgn(term, l_True));
            return;
        }
        assert(false);
    }
    else if (logic.isAnd(term)) {
        // all children must be satisfied
        auto size = logic.getPterm(term).size();
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(term)[i];
            assert(model.evaluate(child) == trueTerm);
            visit_(child);
        }
        return;
    }
    else if (logic.isOr(term)) {
        // some child must be satisfied
        // First-try strategy : go to first satisfied child
        auto size = logic.getPterm(term).size();
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(term)[i];
            if (model.evaluate(child) == trueTerm) {
                visit_(child);
                return;
            }
        }
        assert(false); // Should be unreachable
    }
    else if (logic.isNot(term)) {
        assert(logic.getPterm(term).size() == 1 && logic.isAtom(logic.getPterm(term)[0]));
        PTRef child = logic.getPterm(term)[0];
        if (logic.isAtom(child)) {
            if (model.evaluate(child) == logic.getTerm_false()) { // In NOT context!
                literals.insert(PtAsgn(child, l_False));
                return;
            }
        }
    }
    // TODO: ITE terms?
    throw std::logic_error{"Unsupported structure of formula"};
}

void ToNNFVisitor::visit_(PTRef root) {
    this->res = transform(root);
}

PTRef ToNNFVisitor::transform(PTRef term) {
    auto it = transformed.find(term);
    if (it != transformed.end()) { return it->second; }

    if (logic.isAtom(term)) {
        transformed.insert(std::make_pair(term, term));
        return term;
    }
    if (logic.isAnd(term)) {
        auto size = logic.getPterm(term).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(term)[i];
            nargs.push(transform(child));
        }
        PTRef nterm = logic.mkAnd(nargs);
        transformed.insert(std::make_pair(term, nterm));
        return nterm;
    }

    if (logic.isOr(term)) {
        auto size = logic.getPterm(term).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(term)[i];
            nargs.push(transform(child));
        }
        PTRef nterm = logic.mkOr(nargs);
        transformed.insert(std::make_pair(term, nterm));
        return nterm;
    }

    if (logic.isNot(term)) {
        PTRef npos = transform(logic.getPterm(term)[0]);
        PTRef nterm = negate(npos);
        transformed.insert(std::make_pair(term, nterm));
        return nterm;
    }

    throw std::logic_error("Unexpected term in NNF transformation");

}

PTRef ToNNFVisitor::negate(PTRef term) {
    // term must already be in NNF form
    assert(logic.isAnd(term) || logic.isOr(term) || logic.isAtom(term)
        || (logic.isNot(term) && logic.isAtom(logic.getPterm(term)[0])));

    auto it = negated.find(term);
    if (it != negated.end()) { return it->second; }

    if (logic.isNot(term)) {
        assert(logic.isAtom(logic.getPterm(term)[0]));
        PTRef nterm = logic.getPterm(term)[0];
        negated.insert(std::make_pair(term, nterm));
        return nterm;
    }

    if (logic.isAtom(term)) {
        PTRef nterm = logic.mkNot(term);
        negated.insert(std::make_pair(term, nterm));
        return nterm;
    }

    if (logic.isAnd(term)) {
        auto size = logic.getPterm(term).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(term)[i];
            nargs.push(negate(child));
        }
        PTRef nterm = logic.mkOr(nargs);
        negated.insert(std::make_pair(term, nterm));
        return nterm;
    }

    if (logic.isOr(term)) {
        auto size = logic.getPterm(term).size();
        vec<PTRef> nargs;
        nargs.capacity(size);
        for (int i = 0; i < size; ++i) {
            PTRef child = logic.getPterm(term)[i];
            nargs.push(negate(child));
        }
        PTRef nterm = logic.mkAnd(nargs);
        negated.insert(std::make_pair(term, nterm));
        return nterm;
    }
    assert(false); // UNREACHABLE
    throw std::logic_error("Error in NNF transformation");
}
