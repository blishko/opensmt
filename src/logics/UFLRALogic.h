//
// Created by Martin Blicha on 14.07.21.
//

#ifndef OPENSMT_UFLRALOGIC_H
#define OPENSMT_UFLRALOGIC_H

#endif //OPENSMT_UFLRALOGIC_H

#include "LRALogic.h"

class UFLRALogic : public LRALogic {
public:
    const opensmt::Logic_t getLogic() const override {
        return opensmt::Logic_t::QF_UFLRA;
    }

    // TODO: Unify this with Logic::isUF
    bool isInterpreted(SymRef sym) const {
        return hasSortNum(sym) and not isVar(sym) and not isUF(sym);
    }

    bool isUninterpreted(SymRef sym) const {
        return isUF(sym) and getSym(sym).nargs() > 0;
    }

    bool isNumVarLike(SymRef tr) const override { return isNumVarOrIte(tr) or isUninterpreted(tr); }

    bool isUFEquality(PTRef tr) const override { return Logic::isUFEquality(tr); }
    bool isTheoryEquality(PTRef tr) const override { return LALogic::isTheoryEquality(tr) or Logic::isTheoryEquality(tr); }
    bool isUF(SymRef sr) const override { return Logic::isUF(sr); }

};