//
// Created by Martin Blicha on 20.06.20.
//

#include "TermVisitor.h"

void CollectImplicantTermVisitor::visit_(PTRef term) {
    if (isProcessed(term)) { return; }
    markProcessed(term);

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
