#ifndef TERMMAPPER_H
#define TERMMAPPER_H
#include "Map.h"
#include "SolverTypes.h"
#include "Pterm.h"
#include "Logic.h"
class TermMapper {
  private:
    Logic&      logic;
  public:
    TermMapper(Logic& l) : logic(l) {}

    Map<Var,PTRef,VarHash,Equal<Var> >        varToTerm;
    Map<Var,TRef,VarHash,Equal<Var> >         varToTheorySymbol;
    Map<PTRef,Var,PTRefHash,Equal<PTRef> >    termToVar;
    void getTerm(PTRef, PTRef&, bool&) const;
    Var  getVar(PTRef) const;
    Lit  getLit(PTRef) const;
};

#endif