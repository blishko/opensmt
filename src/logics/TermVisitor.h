//
// Created by Martin Blicha on 20.06.20.
//

#ifndef OPENSMT_TERMVISITOR_H
#define OPENSMT_TERMVISITOR_H

#include "Logic.h"
#include "Model.h"

#include <unordered_set>

class TermVisitor {
protected:
    Logic& logic;
public:
    TermVisitor(Logic& logic) : logic{logic} {}

    void visit(PTRef root) { visit_(root); }

private:
    virtual void visit_(PTRef) = 0;


};


class CollectImplicantTermVisitor :public TermVisitor {
private:
    Model& model;

    std::unordered_set<PTRef, PTRefHash> visited;

    std::unordered_set<PtAsgn, PtAsgnHash> literals;

public:
    CollectImplicantTermVisitor(Logic& logic, Model& model) : TermVisitor(logic), model{model} {}

    std::unordered_set<PtAsgn, PtAsgnHash> getImplicant() const { return literals; }
private:
    virtual void visit_(PTRef fla) override;

    bool isProcessed(PTRef term) { return visited.find(term) != visited.end(); }

    void markProcessed(PTRef term) { visited.insert(term); }
};


#endif //OPENSMT_TERMVISITOR_H
