//
// Created by Martin Blicha on 15.07.20.
//

#ifndef OPENSMT_CHCINTERPRETER_H
#define OPENSMT_CHCINTERPRETER_H

#include "ChcSystem.h"
#include "Theory.h"
#include "SMTConfig.h"
#include "Options.h"

#include <engine/Engine.h> // TODO: remove this and create an engine factory

#include <memory>

class LetBinder {
    PTRef currentValue;
    std::vector<PTRef>* shadowedValues;
public:
    LetBinder(PTRef val) : currentValue(val), shadowedValues(nullptr) {}
    ~LetBinder() { delete shadowedValues; }
    LetBinder(const LetBinder&) = delete;
    LetBinder& operator=(const LetBinder&) = delete;
    LetBinder(LetBinder&&) = default;
    LetBinder& operator=(LetBinder&&) = default;
    PTRef getValue() const { return currentValue; }
    bool hasShadowValue() const { return shadowedValues && !shadowedValues->empty(); }
    void restoreShadowedValue() { assert(hasShadowValue()); currentValue = shadowedValues->back(); shadowedValues->pop_back(); }
    void addValue(PTRef val) {
        if (not shadowedValues) {
            shadowedValues = new std::vector<PTRef>();
        }
        shadowedValues->push_back(currentValue);
        currentValue = val;
    }
};

class LetRecords {
    std::unordered_map<const char*, LetBinder, StringHash, Equal<const char*> > letBinders;
    std::vector<const char*> knownBinders;
    std::vector<std::size_t> frameLimits;

    bool has(const char* name) const { return letBinders.count(name) != 0; }
public:
    PTRef getOrUndef(const char* letSymbol) const {
        auto it = letBinders.find(letSymbol);
        if (it != letBinders.end()) {
            return it->second.getValue();
        }
        return PTRef_Undef;
    }
    void pushFrame() { frameLimits.push_back(knownBinders.size()); }
    void popFrame() {
        auto limit = frameLimits.back();
        frameLimits.pop_back();
        while (knownBinders.size() > limit) {
            const char* binder = knownBinders.back();
            knownBinders.pop_back();
            assert(this->has(binder));
            auto& values = letBinders.at(binder);
            if (values.hasShadowValue()) {
                values.restoreShadowedValue();
            } else {
                letBinders.erase(binder);
            }
        }
    }

    void addBinding(const char* name, PTRef arg) {
        knownBinders.push_back(name);
        if (not this->has(name)) {
            letBinders.insert(std::make_pair(name, LetBinder(arg)));
        } else {
            letBinders.at(name).addValue(arg);
        }
    }
};

class ChcInterpreterContext {
public:
    std::unique_ptr<ChcSystem> interpretSystemAst(const ASTNode * root);

    ChcInterpreterContext(Logic & logic, Options const & opts): logic(logic), opts(opts) {}

private:
    Logic & logic;
    Options const & opts;
    std::unique_ptr<ChcSystem> system;
    bool doExit = false;
    LetRecords letRecords;

    void interpretCommand(ASTNode& node);

    void interpretDeclareFun(ASTNode& node);

    void interpretAssert(ASTNode& node);

    void interpretCheckSat();

    void reportError(std::string msg);

    SRef getSort(ASTNode& sortNode);

    PTRef parseTerm(ASTNode const& node);

    // Building CHCs and helper methods

    ChClause chclauseFromPTRef(PTRef ref);

    bool isUninterpretedPredicate(PTRef ref) const;

    std::unique_ptr<Engine> getEngine() const;
};

class ChcInterpreter {
public:
    std::unique_ptr<ChcSystem> interpretSystemAst(Logic & logic, const ASTNode * root);

    ChcInterpreter(Options const & opts) : opts(opts) {}

private:
    Options const & opts;
};


#endif //OPENSMT_CHCINTERPRETER_H