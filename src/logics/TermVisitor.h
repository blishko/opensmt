//
// Created by Martin Blicha on 20.06.20.
//

#ifndef OPENSMT_TERMVISITOR_H
#define OPENSMT_TERMVISITOR_H

#include "Logic.h"
#include "LRALogic.h"
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

//class CachingTermVisitor : public TermVisitor {
//public:
//    CachingTermVisitor(Logic& logic) : TermVisitor(logic) {}
//protected:
//    virtual void visit_(PTRef pt) override {
//        if (isProcessed(pt)) { return; }
//        uncheckedVisit(pt);
//        markProcessed(pt);
//    }
//private:
//    virtual void uncheckedVisit(PTRef term) = 0;
//
//    bool isProcessed(PTRef term) { return visited.find(term) != visited.end(); }
//
//    void markProcessed(PTRef term) { visited.insert(term); }
//
//    std::unordered_set<PTRef, PTRefHash> visited;
//};

class CollectImplicantTermVisitor : public TermVisitor {
private:
    Model& model;

    std::unordered_set<PtAsgn, PtAsgnHash> literals;

    std::unordered_map<PTRef, PTRef, PTRefHash> cache;

public:
    CollectImplicantTermVisitor(Logic& logic, Model& model) : TermVisitor(logic), model{model} {}

    std::unordered_set<PtAsgn, PtAsgnHash> getImplicant() const { return literals; }
protected:

    PTRef registerAtom(PTRef atom);
    PTRef visitAndSimplify(PTRef term);
    void cacheResults(PTRef original, PTRef simplified);
    bool isInCache(PTRef term) { return cache.find(term) != cache.end(); }
    PTRef getFromCache(PTRef term) { return cache.at(term); }
private:
    virtual PTRef simplifyAndVisitTheoryAtom(PTRef theoryAtom) = 0;
};

class LRACollectImplicantTermVisitor : public CollectImplicantTermVisitor {

    LRALogic & lralogic;

    void visit_(PTRef term) override;

    PTRef simplifyAndVisitTheoryAtom(PTRef theoryAtom) override;

    PTRef simplifyAndVisitLinearTerm(PTRef term);

    PTRef simplifyAndVisitLinearFactor(PTRef term);

    PTRef simplifyAndVisitVariable (PTRef var);

public:
    LRACollectImplicantTermVisitor(LRALogic & logic, Model & model)
        : CollectImplicantTermVisitor(logic, model), lralogic(logic)
    {}

};

//class ToNNFVisitor : public TermVisitor {
//public:
//    ToNNFVisitor(Logic& logic) : TermVisitor(logic) {}
//
//    PTRef getNNF() const { return res; }
//
//private:
//    virtual void visit_(PTRef) override;
//
//    PTRef transform(PTRef);
//
//    PTRef negate(PTRef);
//
//    std::unordered_map<PTRef, PTRef, PTRefHash> transformed;
//    std::unordered_map<PTRef, PTRef, PTRefHash> negated;
//
//    PTRef res = PTRef_Undef;
//};



#endif //OPENSMT_TERMVISITOR_H
