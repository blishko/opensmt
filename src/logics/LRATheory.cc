#include "Theory.h"

//
// Unit propagate with simplifications and split equalities into
// inequalities.  If partitions cannot mix, only do the splitting to
// inequalities.
//
bool LRATheory::simplify(const vec<PFRef>& formulas, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    if (this->keepPartitions()) {
        vec<PTRef> & flas = currentFrame.formulas;
        for (int i = 0; i < flas.size(); ++i) {
            PTRef & fla = flas[i];
            PTRef old = flas[i];
            lralogic.simplifyAndSplitEq(old, fla);
            lralogic.transferPartitionMembership(old, fla);
        }
        currentFrame.root = getLogic().mkAnd(flas);
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        auto subs_res = computeSubstitutions(coll_f);
        // get substitutions as equalities
        auto const & subst = subs_res.usedSubstitution;
        auto const & entries = subst.getKeysAndValsPtrs();
        vec<PTRef> args;
        for (auto * entry : entries) {
            if (entry->data.sgn != l_True) { // disabled substitution
                continue;
            }
            args.push(lralogic.mkEq(entry->key, entry->data.tr));
        }
        getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
        args.push(subs_res.result);
        PTRef addedSubs = lralogic.mkAnd(args);
        lralogic.simplifyAndSplitEq(addedSubs, currentFrame.root);
    }
    return true;
}


