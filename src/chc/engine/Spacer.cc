//
// Created by Martin Blicha on 21.02.21.
//

#include "Spacer.h"
#include "MainSolver.h"

class ApproxMap {

};

class UnderApproxMap : public ApproxMap {
public:
    PTRef get(VId vid, std::size_t bound);
    void insert(VId vid, std::size_t bound, PTRef summary);
};

class OverApproxMap : public ApproxMap {

};

class SpacerContext {
    Logic & logic;
    ChcDirectedHyperGraph const & graph;
    std::size_t currentBound = 0;

    UnderApproxMap under;
    OverApproxMap over;

    bool boundSafety();

    enum class QueryAnswer {VALID, INVALID, ERROR, UNKNOWN};
    struct QueryResult {
        QueryAnswer answer;
        std::unique_ptr<Model> model;
    };
    QueryResult implies(PTRef antecedent, PTRef consequent);

    struct MustReachResult {
        bool applied = false;
        PTRef mustSummary = PTRef_Undef;
    };

    MustReachResult mustReachable(EId eid, PTRef targetConstraint, std::size_t bound);

    PTRef projectFormula(PTRef fla, vec<PTRef> const & vars, Model* model);


public:
    SpacerContext(Logic & logic, ChcDirectedHyperGraph const & graph): logic(logic), graph(graph) {}

    GraphVerificationResult run();
};

GraphVerificationResult Spacer::solve(ChcDirectedHyperGraph & system) {
    return Engine::solve(system);
}

GraphVerificationResult Spacer::solve(const ChcDirectedGraph & system) {
    return Engine::solve(system);
}

GraphVerificationResult SpacerContext::run() {
    auto res = boundSafety();
    throw "Not implemented";
}

struct ProofObligation {
    VId vertex;
    std::size_t bound;
    PTRef constraint;
};

struct PriorityQueue {

    void push(ProofObligation pob);
    ProofObligation const & peek();
    void pop();
    bool empty() const;
};


std::vector<EId> incomingEdges(VId v, ChcDirectedHyperGraph const & graph) {
    auto res = graph.getEdges();
    res.erase(std::remove_if(res.begin(), res.end(), [&](EId e) { return graph.getEdge(e).to == v; }));
    return res;
}

bool SpacerContext::boundSafety() {
    VId query = graph.getExitId();
    PriorityQueue pqueue;
    pqueue.push(ProofObligation{query, currentBound, logic.getTerm_true()});
    while(not pqueue.empty()) {
        auto const & pob = pqueue.peek();
        auto edges = incomingEdges(pob.vertex, graph);
        bool mustReached = false;
        for (EId edgeId : edges) {
            auto edge = graph.getEdge(edgeId);
            // test if vertex can be reached using must summaries
            auto result = mustReachable(edgeId, pob.constraint, pob.bound - 1);
            if (result.applied) {
                assert(result.mustSummary != PTRef_Undef);
                under.insert(pob.vertex, pob.bound, result.mustSummary);
                if (pob.vertex == query) {
                    return false; // query is reachable
                }
                pqueue.pop();
                mustReached = true;
                break;
            } else {
                // TODO: test may-summary to block this edge
            }
        }
        if (mustReached) { continue; }
    }
    throw "Not implemented";
}

SpacerContext::QueryResult SpacerContext::implies(PTRef antecedent, PTRef consequent) {
    SMTConfig config;
    MainSolver solver(logic, config, "checker");
    solver.insertFormula(antecedent);
    solver.insertFormula(logic.mkNot(consequent));
    auto res = solver.check();
    QueryResult qres;
    if (res == s_True) {
        qres.answer = QueryAnswer::INVALID;
        qres.model = solver.getModel();
    }
    else if (res == s_False) {
        qres.answer = QueryAnswer::VALID;
    }
    else if (res == s_Undef) {
        qres.answer = QueryAnswer::UNKNOWN;
    }
    else if (res == s_Error) {
        qres.answer = QueryAnswer::ERROR;
    }
    else {
        assert(false);
        throw std::logic_error("Unreachable code!");
    }
    return qres;
}

SpacerContext::MustReachResult SpacerContext::mustReachable(EId eid, PTRef targetConstraint, std::size_t bound) {
    auto edge = graph.getEdge(eid);
    VId target = edge.to;
    PTRef edgeLabel = edge.fla.fla;
    vec<PTRef> bodyComponents{edgeLabel};
    for (VId source : edge.from) {
        PTRef mustSummary = under.get(source, bound);
        bodyComponents.push(mustSummary);
    }
    PTRef body = logic.mkAnd(bodyComponents);
    auto implCheckRes = implies(body, targetConstraint);
    MustReachResult res;
    if (implCheckRes.answer == SpacerContext::QueryAnswer::INVALID) {
        res.applied = true;
        // eliminate variables from body except variables present in predicate of edge target
        auto predicateVars = TermUtils(logic).getVars(graph.getNextStateVersion(target));
        PTRef newMustSummary = projectFormula(body, predicateVars, implCheckRes.model.get());
        res.mustSummary = newMustSummary;
    } else {
        res.applied = false;
        res.mustSummary = PTRef_Undef;
    }
    return res;
}