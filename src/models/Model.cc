//
// Created by Martin Blicha on 12.06.20.
//

#include "Model.h"

PTRef Model::evaluate(PTRef term) {
    if (hasDerivedVal(term)) {
        return getDerivedVal(term);
    }

    if (logic.isConstant(term)) {
        return term;
    }

    if (logic.isVar(term)) {
        if (hasVarVal(term)) {
            return getVarVal(term);
        }
        // else - unknown var, let the customized behaviour handle this case
        return handleUnknownVar(term);
    }
    else {
        // complex term not seen before, compute and store the value
        const Pterm & t = logic.getPterm(term);
        SymRef symbol = t.symb();
        vec<PTRef> nargs;
        for (int i = 0; i < t.size(); ++i) {
            PTRef narg = evaluate(t[i]);
            nargs.push(narg);
        }
        PTRef val = handleComplexTerm(symbol, nargs);
        addDerivedVal(term, val);
        return val;
    }
}


PTRef ModelWithDefaults::handleUnknownVar(PTRef var) {
    PTRef defaultVal = logic.getDefaultValuePTRef(var);
        // cache value and return
    addDerivedVal(var, defaultVal);
    return defaultVal;
}

PTRef ModelWithDefaults::handleComplexTerm(SymRef symbol, vec<PTRef> & args) {
    char* msg;
    PTRef res = logic.insertTerm(symbol, args, &msg);
    assert(res != PTRef_Undef);
    return res;
}

PTRef ExplicitModel::handleComplexTerm(SymRef symbol, vec<PTRef> & args) {
    // Arguments might contain unknown value (PTRef_Undef) but the result might still be valid value in special cases

    // AND with False argument is False
    if (logic.isAnd(symbol) && std::find(args.begin(), args.end(), logic.getTerm_false()) != args.end()) {
        return logic.getTerm_false();
    }

    // OR with True argument is True
    if (logic.isOr(symbol) && std::find(args.begin(), args.end(), logic.getTerm_true()) != args.end()) {
        return logic.getTerm_true();
    }
    // MB: TODO: other connectives needed?

    // Otherwise, unknown argument means unknown value of complex term
    if (std::find(args.begin(), args.end(), PTRef_Undef) != args.end()) {
        return PTRef_Undef;
    }

    char* msg;
    PTRef res = logic.insertTerm(symbol, args, &msg);
    assert(res != PTRef_Undef);
    return res;
}