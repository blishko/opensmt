//
// Created by Martin Blicha on 21.02.21.
//

#include "Spacer.h"
#include "MainSolver.h"

class ApproxMap {
public:
    PTRef getWhole(VId vid, std::size_t bound);
    std::vector<PTRef> getComponents(VId vid, std::size_t bound);
    void insert(VId vid, std::size_t bound, PTRef summary);
};

class UnderApproxMap : public ApproxMap {

};

class OverApproxMap : public ApproxMap {

};


class SpacerContext {
    Logic & logic;
    ChcDirectedHyperGraph const & graph;

    UnderApproxMap under;
    OverApproxMap over;

    bool boundSafety(std::size_t currentBound);

    bool isInductive(std::size_t currentBound);

    enum class QueryAnswer {VALID, INVALID, ERROR, UNKNOWN};
    struct QueryResult {
        QueryAnswer answer;
        std::unique_ptr<Model> model;
    };
    QueryResult implies(PTRef antecedent, PTRef consequent);

    struct ItpQueryResult {
        QueryAnswer answer;
        PTRef interpolant = PTRef_Undef;
    };
    ItpQueryResult interpolatingImplies(PTRef antecedent, PTRef consequent);

    struct MustReachResult {
        bool applied = false;
        PTRef mustSummary = PTRef_Undef;
    };

    struct MayReachResult {
        bool blocked = false;
        PTRef maySummary = PTRef_Undef;
    };

    MustReachResult mustReachable(EId eid, PTRef targetConstraint, std::size_t bound);

    MayReachResult mayReachable(EId eid, PTRef targetConstraint, std::size_t bound);

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
    auto res = boundSafety(0);
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

bool SpacerContext::boundSafety(std::size_t currentBound) {
    VId query = graph.getExitId();
    PriorityQueue pqueue;
    pqueue.push(ProofObligation{query, currentBound, logic.getTerm_true()});
    while(not pqueue.empty()) {
        auto const & pob = pqueue.peek();
        auto edges = incomingEdges(pob.vertex, graph);
        bool mustReached = false;
        std::vector<ProofObligation> newProofObligations;
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
                auto result = mayReachable(edgeId, pob.constraint, pob.bound - 1);
                if (result.blocked) {
                    continue; // This edge has been blocked, we can continue
                }
            }
            // if we got there then it was not possible to prove that the edge can be taken or prove that it cannot be taken
            // examine the sources to generate a new proof obligation for this edge

            // Find the first source vertex such that under-approximating it (instead of over-approximating it) makes the target unreachable
            auto const& targets = edge.from;
            assert(not targets.empty());
            std::size_t vertexToRefine = 0; // vertex that is the last one to be over-approximated
            auto bound = pob.bound - 1;
            // looking for vertex which is the point where using over-approximation makes the edge feasible
            while(true) {
                vec<PTRef> components;
                for (std::size_t i = 0; i <= vertexToRefine; ++i) {
                    components.push(over.getWhole(targets[i], bound));
                }
                for (std::size_t i = vertexToRefine + 1; i < targets.size(); ++i) {
                    components.push(under.getWhole(targets[i], bound));
                }
                components.push(edge.fla.fla);
                PTRef body = logic.mkAnd(components);
                auto res = implies(body, logic.mkNot(pob.constraint));
                if (res.answer == QueryAnswer::INVALID) {
                    // When this target is over-approximated and the edge becomes feasible -> extract next proof obligation
                    VId source = targets[vertexToRefine];
                    auto predicateVars = TermUtils(logic).getVars(graph.getStateVersion(source));
                    auto newConstraint = projectFormula(logic.mkAnd(body, pob.constraint), predicateVars, res.model.get());
                    newProofObligations.push_back(ProofObligation{targets[vertexToRefine], bound, newConstraint});
                    break;
                }
                if (res.answer == QueryAnswer::VALID) {
                    // Continue with the next vertex to refine
                    ++vertexToRefine;
                    assert(vertexToRefine < targets.size());
                    continue;
                }
                assert(false);
                throw std::logic_error("Unreachable!");
            }
        }
        if (mustReached) { continue; }
        else {
            if (newProofObligations.empty()) {
                // all edges are blocked; compute new lemma blocking the current proof obligation
                // TODO:
                vec<PTRef> edgeRepresentations;
                for (EId eid : edges) {
                    vec<PTRef> sourceFlas;
                    auto sources = graph.getSources(eid);
                    for (VId source : sources) {
                        sourceFlas.push(over.getWhole(source, pob.bound - 1));
                    }
                    sourceFlas.push(graph.getEdgeLabel(eid));
                    edgeRepresentations.push(logic.mkAnd(sourceFlas));
                }
                auto res = interpolatingImplies(logic.mkOr(edgeRepresentations), logic.mkNot(pob.constraint));
                assert(res.answer == QueryAnswer::VALID);
                if (res.answer != QueryAnswer::VALID) {
                    throw std::logic_error("All edges should have been blocked, but they are not!");
                }
                over.insert(pob.vertex, pob.bound, res.interpolant);
                pqueue.pop(); // This POB has been successfully blocked
            } else {
                for (auto const& npob : newProofObligations) {
                    pqueue.push(npob);
                }
            }
        }
    } // end of main cycle
    return true; // SAFE (not reachable) at this bound
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

SpacerContext::ItpQueryResult SpacerContext::interpolatingImplies(PTRef antecedent, PTRef consequent) {
    SMTConfig config;
    const char* msg = "ok";
    bool set = config.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    assert(set); (void)set;
    config.simplify_interpolant = 4;
    MainSolver solver(logic, config, "checker");
    solver.insertFormula(antecedent);
    solver.insertFormula(logic.mkNot(consequent));
    auto res = solver.check();
    ItpQueryResult qres;
    if (res == s_True) {
        qres.answer = QueryAnswer::INVALID;
    }
    else if (res == s_False) {
        qres.answer = QueryAnswer::VALID;
        auto itpCtx = solver.getInterpolationContext();
        std::vector<PTRef> itps;
        ipartitions_t mask = 0;
        setbit(mask, 0);
        itpCtx->getSingleInterpolant(itps, mask);
        qres.interpolant = itps[0];
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
        PTRef mustSummary = under.getWhole(source, bound);
        bodyComponents.push(mustSummary);
    }
    PTRef body = logic.mkAnd(bodyComponents);
    auto implCheckRes = implies(body, logic.mkNot(targetConstraint));
    MustReachResult res;
    if (implCheckRes.answer == SpacerContext::QueryAnswer::INVALID) {
        res.applied = true;
        // eliminate variables from body except variables present in predicate of edge target
        auto predicateVars = TermUtils(logic).getVars(graph.getNextStateVersion(target));
        PTRef newMustSummary = projectFormula(body, predicateVars, implCheckRes.model.get()); // TODO: is body OK, or do I need to project also the head?
        res.mustSummary = newMustSummary;
    } else {
        res.applied = false;
        res.mustSummary = PTRef_Undef;
    }
    return res;
}

SpacerContext::MayReachResult SpacerContext::mayReachable(EId eid, PTRef targetConstraint, std::size_t bound) {
    auto edge = graph.getEdge(eid);
    VId target = edge.to;
    PTRef edgeLabel = edge.fla.fla;
    vec<PTRef> bodyComponents{edgeLabel};
    for (VId source : edge.from) {
        PTRef maySummary = over.getWhole(source, bound);
        bodyComponents.push(maySummary);
    }
    PTRef body = logic.mkAnd(bodyComponents);
    auto implCheckRes = interpolatingImplies(body, logic.mkNot(targetConstraint));
    MayReachResult res;
    if (implCheckRes.answer == SpacerContext::QueryAnswer::VALID) {
        res.blocked = true;
        res.maySummary = res.maySummary;
    } else {
        res.blocked = false;
        res.maySummary = PTRef_Undef;
    }
    return res;
}

// *********** INDUCTIVE CHECK *****************************
bool SpacerContext::isInductive(std::size_t level) {
    bool inductive = true;
    for (VId vid : graph.getVertices()) {
        auto maySummaryComponents = over.getComponents(vid, level);
        // encode body as disjunction over all the incoming edges
        vec<PTRef> edgeRepresentations;
        for (EId eid : incomingEdges(vid, graph)) {
            vec<PTRef> edgeBodyArgs;
            for (VId source : graph.getSources(eid)) {
                edgeBodyArgs.push(over.getWhole(source, level));
            }
            edgeBodyArgs.push(graph.getEdgeLabel(eid));
            edgeRepresentations.push(logic.mkAnd(edgeBodyArgs));
        }
        PTRef body = logic.mkOr(edgeRepresentations);
        // Figure out which components of the may summary are implied by body at level n and so can be pushed to level n+1
        for (PTRef component : maySummaryComponents) {
            auto res = implies(body, component);
            if (res.answer == QueryAnswer::VALID) {
                over.insert(vid, level + 1, component);
            } else {
                inductive = false;
            }
        }
    }
    return inductive;
}