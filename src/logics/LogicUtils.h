//
// Created by Martin Blicha on 08.07.20.
//

#ifndef OPENSMT_LOGICUTILS_H
#define OPENSMT_LOGICUTILS_H

#include "LALogic.h"


class LALogicUtils {

    LALogic& logic;

public:
    LALogicUtils(LALogic & logic) : logic{logic} {}

    Logic::implicant_t compactImplicant(Logic::implicant_t implicant);



};


#endif //OPENSMT_LOGICUTILS_H
