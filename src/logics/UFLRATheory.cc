#include "UFLRATheory.h"
#include "TreeOps.h"
#include "ArithmeticEqualityRewriter.h"
#include "Substitutor.h"
#include "OsmtInternalException.h"

bool UFLRATheory::simplify(const vec<PFRef>& formulas, PartitionManager &pmanager, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    if (keepPartitions()) {
        throw OsmtInternalException("Interpolation not available yet for UFLRA!");
    }
    // Let's ignore substitution for now
    PTRef fla = logic.mkAnd(currentFrame.formulas);
    PTRef purified = purify(fla);
    PTRef enriched = addEqDefinitionsAndTrichotomyAxioms(purified);
    currentFrame.root = enriched;
    return true;
}

namespace {
class PurifyConfig : public DefaultVisitorConfig {
    static std::string prefix;
    UFLRALogic & logic;
    Logic::SubstMap substMap;

    void createVarFor(PTRef ptref) {
        if (substMap.has(ptref)) {
            return;
        }
        assert(logic.hasSortNum(ptref));
        auto name = prefix + std::to_string(ptref.x);
        PTRef var = logic.mkNumVar(name.c_str());
        substMap.insert(ptref, var);
    }

public:
    PurifyConfig(UFLRALogic & logic) : DefaultVisitorConfig(), logic(logic) {}

    void visit(PTRef ptref) override {
        auto const & term = logic.getPterm(ptref);
        if (logic.isInterpreted(term.symb())) {
            auto nargs = term.nargs();
            for (unsigned i = 0; i < nargs; ++i) {
                PTRef child = logic.getPterm(ptref)[i];
                if (logic.isUninterpreted(logic.getSymRef(child))) {
                    createVarFor(child);
                }
            }
        }
    }

    Logic::SubstMap const & getPurificationMap() const { return substMap; }
};

std::string PurifyConfig::prefix = ".purify_";

class Purifier : public TermVisitor<PurifyConfig> {
    PurifyConfig config;

public:
    Purifier(UFLRALogic & logic) : TermVisitor<PurifyConfig>(logic, config), config(logic) {}

    Logic::SubstMap const & getPurificationMap() const { return config.getPurificationMap(); }
};
}

namespace{
void closeSubstitutionMapOnKeys(Logic & logic, Logic::SubstMap & substMap) {
    bool changed = true;
    while (changed) {
        changed = false;
        vec<PTRef> newKeys;
        vec<PTRef> values;
        vec<PTRef> oldKeys;
        substMap.getKeys().copyTo(oldKeys);
        for (PTRef oldKey : oldKeys) {
            PTRef newKey = Substitutor(logic, substMap).rewrite(oldKey);
            if (newKey != oldKey and newKey != substMap[oldKey]) {
                changed = true;
                newKeys.push(newKey);
                values.push(substMap[oldKey]);
            }
        }
        assert(newKeys.size() == values.size());
        for (int i = 0; i < newKeys.size(); ++i) {
            substMap.insert(newKeys[i], values[i]);
        }
    }
}
}

PTRef UFLRATheory::purify(PTRef fla) {
    Purifier purifier(logic);
    purifier.visit(fla);
    auto const & purificationMap = purifier.getPurificationMap();
    Logic::SubstMap closedPurificationMap;
    purificationMap.copyTo(closedPurificationMap);
    closeSubstitutionMapOnKeys(logic, closedPurificationMap); // TODO: this should probably be handled better in Substitutor
    vec<PTRef> equalities;
    equalities.capacity(closedPurificationMap.getSize() + 1);
    for (PTRef key : closedPurificationMap.getKeys()) {
        equalities.push(logic.mkEq(key, closedPurificationMap[key]));
    }
    equalities.push(Substitutor(logic, closedPurificationMap).rewrite(fla));
    return logic.mkAnd(equalities);
}

class CollectEqsConfig : public DefaultVisitorConfig {
    vec<PTRef> numEqs;
    UFLRALogic & logic;

public:
    CollectEqsConfig(UFLRALogic & logic) : DefaultVisitorConfig(), logic(logic) {}

    bool previsit(PTRef ptref) override {
        return logic.hasSortBool(ptref);
    }

    void visit(PTRef ptref) override {
        if (logic.isNumEq(ptref)) {
            numEqs.push(ptref);
        }
    }

    vec<PTRef> const & getEqs() const { return numEqs; }
};

PTRef UFLRATheory::addEqDefinitionsAndTrichotomyAxioms(PTRef fla) {
    CollectEqsConfig config(logic);
    TermVisitor<CollectEqsConfig>(logic, config).visit(fla);
    auto const & eqs = config.getEqs();

    vec<PTRef> axioms;
    for (PTRef eq : eqs) {
        if (not isPureLA(eq)) {
            continue;
        }
        PTRef lhs = logic.getPterm(eq)[0];
        PTRef rhs = logic.getPterm(eq)[1];
        // x = y => x <= y and x >= y
        PTRef definition = logic.mkImpl(eq, logic.mkAnd(logic.mkNumLeq(lhs, rhs), logic.mkNumLeq(rhs, lhs)));
        axioms.push(definition);
        // x = y or x > y or x < y
        PTRef trichotomy = logic.mkOr({eq, logic.mkNumGt(lhs, rhs), logic.mkNumGt(rhs, lhs)});
        axioms.push(trichotomy);
    }
    vec<PTRef> & nArgs = axioms;
    nArgs.push(fla);
    return logic.mkAnd(nArgs);
}

bool UFLRATheory::isPureLA(PTRef term) const {
    class UFFinderConfig : public DefaultVisitorConfig {
        UFLRALogic & logic;
    public:
        UFFinderConfig(UFLRALogic & logic) : DefaultVisitorConfig(), logic(logic) {}
        bool previsit(PTRef term) override { return not ufFound; }

        void visit(PTRef term) override {
            if (logic.isUninterpreted(logic.getSymRef(term))) {
                ufFound = true;
            }
        }

        bool ufFound = false;
    } config(logic);
    TermVisitor<UFFinderConfig>(logic, config).visit(term);
    return not config.ufFound;
}
