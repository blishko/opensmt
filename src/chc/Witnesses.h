//
// Created by Martin Blicha on 02.09.20.
//

#include "Model.h"
#include "ChcGraph.h"

class WitnessModel {
    std::unique_ptr<Model> model;
public:
    WitnessModel() = default;
    explicit WitnessModel(std::unique_ptr<Model> model) : model(std::move(model)) {}

    PTRef evaluate(PTRef fla) const { return model->evaluate(fla); }
};

class InvalidityWitness {
public:
    class ErrorPath {
        std::vector<EId> path;
    public:
//        std::vector<VId> getVertices() const;
        std::vector<EId> getEdges() const { return path; }
//        vec<PTRef> getEdgeFormulas() const;
        void setPath(std::vector<EId> npath) { this->path = std::move(npath); }
        bool isEmpty() const { return path.empty(); }
    };
    void setErrorPath(ErrorPath path) { errorPath = std::move(path); }

    ErrorPath const & getErrorPath() const { return errorPath; }

private:
    ErrorPath errorPath;
};

class SystemInvalidityWitness {
public:
    class Derivation { // Terminology based on Interpolation Strength Revisited
        // Derivation rule is 'positive hyper-resolution'
        // Antecedents are: one nucleus (with n negative literals) and n satellites, each with single positive literal
    public:
    	struct DerivationStep {
            enum class StepType {INPUT, DERIVED};
            std::size_t index;
            StepType type;
            std::vector<std::size_t> satellites;
            std::size_t nucleus;
            ChClause clause;
        };

        void addDerivationStep(DerivationStep step) {
            derivationSteps.push_back(std::move(step));
        }
        DerivationStep &        operator[](std::size_t index)       { assert(index < derivationSteps.size()); return derivationSteps[index]; }
        DerivationStep const &  operator[](std::size_t index) const { assert(index < derivationSteps.size()); return derivationSteps[index]; }
        DerivationStep &        last()       { assert(size() > 0); return derivationSteps[size() - 1]; }
        DerivationStep const &  last() const { assert(size() > 0); return derivationSteps[size() - 1]; }
        std::size_t size() const { return derivationSteps.size(); }
    
private:
        std::vector<DerivationStep> derivationSteps;
    };

private:
    Derivation derivation;
    WitnessModel model;

public:
    void setModel(WitnessModel model_) { model = std::move(model_); }
    void setDerivation(Derivation derivation_) { derivation = std::move(derivation_); }

    Derivation const & getDerivation() const { return derivation; }
    WitnessModel const & getModel() const { return model; }

    void print(std::ostream & out, Logic & logic) const;
};

SystemInvalidityWitness graphToSystemInvalidityWitness(InvalidityWitness const & witness, ChcGraphContext & ctx);

class ValidityWitness {
    std::unordered_map<PTRef, PTRef, PTRefHash> interpretations;
public:
    using entry_type = decltype(interpretations)::value_type;
    using definitions_type = std::unordered_map<PTRef, PTRef, PTRefHash>;

    ValidityWitness() {}

    explicit ValidityWitness(std::unordered_map<PTRef, PTRef, PTRefHash> interpretations)
        : interpretations(std::move(interpretations)) {}

    template<typename TFun>
    void run(TFun fun) const {
        for (auto const & entry : interpretations) {
            fun(entry);
        }
    }

    definitions_type getDefinitions() const { return interpretations; }
};