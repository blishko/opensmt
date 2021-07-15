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

    bool isInterpreted(SymRef sym) const {
        return hasSortNum(sym) and not isVar(sym) and not isUF(sym);
    }

    bool isUninterpreted(SymRef sym) const {
        return isUF(sym) and getSym(sym).nargs() > 0;
    }

    bool isNumVarLike(SymRef tr) const override { return isNumVarOrIte(tr) or isUninterpreted(tr); }

};