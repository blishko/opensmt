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
    currentFrame.root = purified;
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

PTRef UFLRATheory::purify(PTRef fla) {
    Purifier purifier(logic);
    purifier.visit(fla);
    auto const & purificationMap = purifier.getPurificationMap();
    vec<PTRef> equalities;
    equalities.capacity(purificationMap.getSize() + 1);
    for (PTRef key : purificationMap.getKeys()) {
        equalities.push(logic.mkEq(key, purificationMap[key]));
    }
    equalities.push(Substitutor(logic, purificationMap).rewrite(fla));
    return logic.mkAnd(equalities);
}
