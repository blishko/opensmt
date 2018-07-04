#ifndef LIALOGIC_H
#define LIALOGIC_H

#include "Logic.h"
#include "Real.h"
#include "Integer.h"
#include "LALogic.h"





/*
class LIANonLinearException
{
    char* reason;
public:
    LIANonLinearException(const char* reason_) {
        asprintf(&reason, "Term %s is non-linear", reason_);
    }
    virtual char* what() const
    {
        char* out;
        asprintf(&out, "%s", reason);
        return out;
    }
    ~LIANonLinearException() { free(reason); }
};
 */


class LIALogic: public LALogic
{
  protected:
    Logic_t logic_type;
    vec<opensmt::Integer*> integers;//PS. replace this with Number?
    SymRef              sym_Int_ZERO;
    SymRef              sym_Int_ONE;
    SymRef              sym_Int_NEG;
    SymRef              sym_Int_MINUS;
    SymRef              sym_Int_PLUS;
    SymRef              sym_Int_TIMES;
    SymRef              sym_Int_DIV;
    //SymRef              sym_Int_MOD;
    //SymRef              sym_Int_ABS;
    SymRef              sym_Int_EQ;
    SymRef              sym_Int_LEQ;
    SymRef              sym_Int_LT;
    SymRef              sym_Int_GEQ;
    SymRef              sym_Int_GT;
    SymRef              sym_Int_ITE;

    SRef                sort_INTEGER;

    PTRef               term_Int_ZERO;
    PTRef               term_Int_ONE;

    static const char*  tk_int_zero;
    static const char*  tk_int_one;
    static const char*  tk_int_neg;
    static const char*  tk_int_minus;
    static const char*  tk_int_plus;
    static const char*  tk_int_times;
    static const char*  tk_int_div;
    //static const char*  tk_int_mod;
    //static const char*  tk_int_abs;
    static const char*  tk_int_leq;
    static const char*  tk_int_lt;
    static const char*  tk_int_geq;
    static const char*  tk_int_gt;

    static const char*  s_sort_integer;
    static const char*  e_nonlinear_term;

    bool split_eq;
    //Map<PTRef,bool,PTRefHash> lia_split_inequalities;
    //void visit(PTRef, Map<PTRef,PTRef,PTRefHash>&);

  public:
    LIALogic (SMTConfig& c);
    ~LIALogic () {
        for (int i = 0; i < integers.size(); i++) delete integers[i];
    }

    virtual const char*   getName()         const override { return getLogic().str; }
    virtual const Logic_t getLogic()        const override { return QF_LIA; }

    //virtual bool        okForBoolVar    (PTRef) const;
    virtual PTRef       insertTerm      (SymRef sym, vec<PTRef>& terms, char** msg) override;

    virtual PTRef       mkConst         (const char* name, const char **msg) override;
    virtual PTRef       mkConst         (SRef s, const char* name) override;
    virtual PTRef       mkConst         (const opensmt::Integer& c) { char* rat; opensmt::stringToRational(rat, c.get_str().c_str()); PTRef tr = mkConst(getSort_num(), rat); free(rat); return tr; }
    virtual PTRef       mkConst         (const char* num) override { return mkConst(getSort_num(), num); }
    virtual PTRef       mkNumVar        (const char* name) override { return mkVar(getSort_num(), name); }

    virtual bool isBuiltinSort(SRef sr) const override { return sr == sort_INTEGER || Logic::isBuiltinSort(sr); }
    //virtual bool isBuiltinConstant(SymRef sr) const { return (isIntegerConst(sr) || Logic::isBuiltinConstant(sr)); }
    //virtual bool isBuiltinFunction(SymRef sr) const;

    //bool  isIntegerConst(SymRef sr)      const { return isConstant(sr) && hasSortInt(sr); }
    //bool  isIntegerConst(PTRef tr)       const { return isIntegerConst(getPterm(tr).symb()); }
    virtual bool  isNonnegNumConst(PTRef tr) const override { return isNumConst(tr) && getNumConst(tr) >= 0; }


    //SRef   declareSort_Integer(char** msg);
    virtual SRef   getSort_num()  const override {return sort_INTEGER;}
    const opensmt::Number& getNumConst(PTRef tr) const override {return getIntegerConst(tr);}
    const opensmt::Integer& getIntegerConst(PTRef tr) const;


    bool        isIntPlus(SymRef sr)  const { return sr == sym_Int_PLUS; }
    //bool      isIntPlus(PTRef tr)   const { return isIntPlus(getPterm(tr).symb()); }
    bool        isNumPlus(PTRef tr)   const override { return isIntPlus(getPterm(tr).symb()); }
    bool        isIntMinus(SymRef sr) const { return sr == sym_Int_MINUS; }
    //bool      isIntMinus(PTRef tr)  const { return isIntMinus(getPterm(tr).symb()); }
    bool        isNumMinus(PTRef tr)  const override { return isIntMinus(getPterm(tr).symb()); }
    bool        isIntNeg(SymRef sr)   const { return sr == sym_Int_NEG; }
    //bool      isIntNeg(PTRef tr)    const { return isIntNeg(getPterm(tr).symb()); }
    bool        isNumNeg(PTRef tr)    const override { return isIntNeg(getPterm(tr).symb()); }
    bool        isIntTimes(SymRef sr) const { return sr == sym_Int_TIMES; }
    //bool      isIntTimes(PTRef tr)  const { return isIntTimes(getPterm(tr).symb()); }
    bool        isNumTimes(PTRef tr)  const override { return isIntTimes(getPterm(tr).symb()); }
    bool        isIntDiv(SymRef sr)   const { return sr == sym_Int_DIV; }
    //bool        isIntDiv(PTRef tr)    const { return isIntDiv(getPterm(tr).symb()); }
    bool        isNumDiv(PTRef tr)    const override { return isIntDiv(getPterm(tr).symb()); }
    bool        isIntEq(SymRef sr)    const { return isEquality(sr) && (sym_store[sr][0] == sort_INTEGER); }
    //bool      isIntEq(PTRef tr)     const { return isIntEq(getPterm(tr).symb()); }
    bool        isNumEq(PTRef tr)     const override { return isIntEq(getPterm(tr).symb()); }
    bool        isIntLeq(SymRef sr)   const { return sr == sym_Int_LEQ; }
    //bool      isIntLeq(PTRef tr)    const { return isIntLeq(getPterm(tr).symb()); }
    bool        isNumLeq(PTRef tr)    const override { return isIntLeq(getPterm(tr).symb()); }
    bool        isIntLt(SymRef sr)    const { return sr == sym_Int_LT; }
    //bool      isIntLt(PTRef tr)     const { return isIntLt(getPterm(tr).symb()); }
    bool        isNumLt(PTRef tr)     const override { return isIntLt(getPterm(tr).symb()); }
    bool        isIntGeq(SymRef sr)   const { return sr == sym_Int_GEQ; }
    //bool      isIntGeq(PTRef tr)    const { return isIntGeq(getPterm(tr).symb()); }
    bool        isNumGeq(PTRef tr)    const override { return isIntGeq(getPterm(tr).symb()); }
    bool        isIntGt(SymRef sr)    const { return sr == sym_Int_GT; }
    //bool      isIntGt(PTRef tr)     const { return isIntGt(getPterm(tr).symb()); }
    bool        isNumGt(PTRef tr)     const override { return isIntGt(getPterm(tr).symb()); }
    bool        isIntVar(SymRef sr)   const { return isVar(sr) && sym_store[sr].rsort() == sort_INTEGER; }
    //bool      isIntVar(PTRef tr)    const { return isIntVar(getPterm(tr).symb()); }
    bool        isNumVar(PTRef tr)    const override { return isIntVar(getPterm(tr).symb());}
    //bool      isIntMod(SymRef sr)   const { return sr == sym_Int_MOD; }
    //bool      isIntMod(PTRef tr)    const { return isIntMod(getPterm(tr).symb()); }
    //bool      isIntABS(SymRef sr)   const { return sr == sym_int_ABS; }
    //bool      isIntABS(PTRef tr)    const { return isIntABS(getPterm(tr).symb()); }
    bool        isIntZero(SymRef sr)  const { return sr == sym_Int_ZERO; }
    //bool      isIntZero(PTRef tr)   const { return tr == term_Int_ZERO; }
    bool        isNumZero(PTRef tr)   const override { return tr == term_Int_ZERO; }
    bool        isIntOne(SymRef sr)   const { return sr == sym_Int_ONE; }
    //bool      isIntOne(PTRef tr)    const { return tr == term_Int_ONE; }
    bool        isNumOne(PTRef tr)    const override { return tr == term_Int_ONE; }


    // Integer terms are of form c, a, or (* c a) where c is a constant and a is a variable.
    //bool        isIntegerTerm(PTRef tr) const;

    bool        hasSortInt(SymRef sr) const { return sym_store[sr].rsort() == sort_INTEGER; }
    bool        hasSortNum(PTRef tr) const override { return hasSortInt(getPterm(tr).symb()); }

    //bool        isUFEquality(PTRef tr) const { return !isIntEq(tr) && Logic::isUFEquality(tr); }
    //bool        isTheoryEquality(PTRef tr) const { return isIntEq(tr); }

    //virtual bool isAtom(PTRef tr) const { return isIntEq(tr) || isIntLt(tr) || isIntGt(tr) || isIntLeq(tr) || isIntGeq(tr) || Logic::isAtom(tr); }

    // UFs are the functions that have no interpretation in integers.
    //bool        isUF(PTRef tr)  const { return isUF(term_store[tr].symb()); }
    //bool        isUF(SymRef sr) const { return !sym_store[sr].isInterpreted();}


    PTRef       getTerm_NumZero() const override { return term_Int_ZERO; }
    PTRef       getTerm_NumOne()  const override { return term_Int_ONE; }

    /*
    PTRef       mkIntNeg(PTRef, char**);
    PTRef       mkIntNeg(PTRef tr) {char* msg; PTRef trn = mkIntNeg(tr, &msg); assert(trn != PTRef_Undef); return trn; }
    PTRef       mkIntMinus(const vec<PTRef>&, char**);
    PTRef       mkIntMinus(const vec<PTRef>& args) { char *msg; PTRef tr = mkIntMinus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkIntMinus(const PTRef a1, const PTRef a2) { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkIntMinus(tmp); }
    PTRef       mkIntPlus(const vec<PTRef>&, char**);
    PTRef       mkIntPlus(const vec<PTRef>& args) { char *msg; PTRef tr = mkIntPlus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkIntPlus(const std::vector<PTRef>& args) { vec<PTRef> tmp; for(PTRef arg : args) {tmp.push(arg);} return mkIntPlus(tmp);}
    PTRef       mkIntTimes(const vec<PTRef>&, char**);
    PTRef       mkIntTimes(const vec<PTRef>& args) { char *msg; PTRef tr = mkIntTimes(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkIntTimes(const PTRef p1, const PTRef p2) { vec<PTRef> tmp; tmp.push(p1); tmp.push(p2); return mkIntTimes(tmp); }
    PTRef       mkIntTimes(const std::vector<PTRef>& args) { vec<PTRef> tmp; for(PTRef arg : args) {tmp.push(arg);} return mkIntTimes(tmp);}
   // PTRef       mkIntDiv(const vec<PTRef>&, char**);
   // PTRef       mkIntDiv(const vec<PTRef>& args) { char *msg; PTRef tr = mkIntDiv(args, &msg); assert(tr != PTRef_Undef); return tr; }
   // PTRef       mkIntDiv(const PTRef nom, const PTRef den) { vec<PTRef> tmp; tmp.push(nom), tmp.push(den); return mkIntDiv(tmp); }
    PTRef       mkIntLeq(const vec<PTRef>&, char**);
    PTRef       mkIntLeq(const vec<PTRef>& args) { char* msg; PTRef tr = mkIntLeq(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkIntLeq(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkIntLeq(tmp); }
    PTRef       mkIntGeq(const vec<PTRef>&, char**);
    PTRef       mkIntGeq(const vec<PTRef>& args) { char* msg; PTRef tr = mkIntGeq(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkIntGeq(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkIntGeq(tmp); }
    PTRef       mkIntLt(const vec<PTRef>&, char**);
    PTRef       mkIntLt(const vec<PTRef>& args) { char* msg; PTRef tr = mkIntLt(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkIntLt(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkIntLt(tmp); }
    PTRef       mkIntGt(const vec<PTRef>&, char**);
    PTRef       mkIntGt(const vec<PTRef>& args) { char* msg; PTRef tr = mkIntGt(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkIntGt(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkIntGt(tmp); }
*/
    //virtual bool        isIntNegated(PTRef tr) const;

    //virtual void        splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac) const;
    //virtual PTRef       normalizeSum(PTRef sum); // Use for normalizing leq terms: sort the sum and divide all terms with the first factor
    //virtual PTRef       normalizeMul(PTRef mul); // Use for normalizing leq terms of form 0 <= c*v

    // Logic specific simplifications: conjoin Ites, make substitutions
    // and split equalities
    virtual bool simplify(PTRef root, PTRef& root_out);

    //virtual PTRef getNTerm(char* rat_str) override;

    //lbool retrieveSubstitutions(vec<PtAsgn>& facts, Map<PTRef,PtAsgn,PTRefHash>& substs);
    //lbool arithmeticElimination(vec<PTRef>&, Map<PTRef,PtAsgn,PTRefHash>&);
    //void simplifyAndSplitEq(PTRef, PTRef&);
    //virtual void termSort(vec<PTRef>& v) const;
    //virtual bool okToPartition(PTRef tr) const; // Partitioning hints from logic
    //virtual void serializeLogicData(int*& logicdata_buf) const;
    //void deserializeLogicData(const int* logicdata_buf);

    //virtual char* printTerm_       (PTRef tr, bool ext, bool s) const;
    //virtual char* printTerm        (PTRef tr)                 const { return printTerm_(tr, false, false); }
    //virtual char* printTerm        (PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }
};

// Determine for two multiplicative terms (* k1 v1) and (* k2 v2), v1 !=
// v2 which one is smaller, based on the PTRef of v1 and v2.  (i.e.
// v1.ptref <  v2.ptref iff (* k1 v1) < (* k2 v2))
/*
class LIALessThan_deepPTRef {
    const LIALogic& l;
  public:
    LIALessThan_deepPTRef(const LIALogic* l) : l(*l) {}
    bool operator ()  (PTRef& x_, PTRef& y_) {
        uint32_t id_x;
        uint32_t id_y;
        if (l.isIntTimes(x_)) {
            PTRef c_x;
            PTRef v_x;
            l.splitTermToVarAndConst(x_, v_x, c_x);
            id_x = v_x.x;
        } else {
            id_x = x_.x;
        }
        if (l.isIntTimes(y_)) {
            PTRef c_y;
            PTRef v_y;
            l.splitTermToVarAndConst(y_, v_y, c_y);
            id_y = v_y.x;
        } else {
            id_y = y_.x;
        }
        return id_x < id_y;
    }*/

/*
class LIASimplifyConst {
  protected:
    LIALogic& l;
    PTRef simplifyConstOp(const vec<PTRef>& const_terms, char** msg);
    virtual void Op(opensmt::Integer& s, const opensmt::Integer& v) const = 0;
    virtual opensmt::Integer getIdOp() const = 0;
    virtual void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const = 0;
  public:
    LIASimplifyConst(LIALogic& log) : l(log) {}
    void simplify(SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new, char** msg);
};

class LIASimplifyConstSum : public LIASimplifyConst {
    void Op(opensmt::Integer& s, const opensmt::Integer& v) const { s += v; }
    opensmt::Integer getIdOp() const { return 0; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    LIASimplifyConstSum(LIALogic& log) : LIASimplifyConst(log) {}
};

class LIASimplifyConstTimes : public LIASimplifyConst {
    void Op(opensmt::Integer& s, const opensmt::Integer& v) const { s *= v; }
    opensmt::Integer getIdOp() const { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    LIASimplifyConstTimes(LIALogic& log) : LIASimplifyConst(log) {}
};

class SimplifyConstDiv : public SimplifyConst {
    void Op(opensmt::Integer& s, const opensmt::Integer& v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    opensmt::Integer getIdOp() const { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstDiv(LIALogic& log) : SimplifyConst(log) {}
};
 */

#endif
