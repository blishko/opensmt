#ifndef LABOUNDS_H
#define LABOUNDS_H

#include "Delta.h"
#include "LARefs.h"
#include "LAVar.h"

//
// Bound index type.  The bounds are ordered in a list, and indexed using a number in the list.
// To determine if a given bound is higher than another, it suffices to check the current bound index
// and the new index.  However, we need special values for no lower bound and no upper bound.
//
// The values are a little special.  Two least significant bits encode whether this is the lowest
// bound, the highest bound, or a normal bound.  Lowest bound is 00, highest bound is 11, and
// normal bound is 01.
//

class LABound
{
    BoundType type;    // Upper / lower
    int bidx;     // The index in variable's bound list
    int id;       // The unique id of the bound
    LVRef var;
    FastRational boundVal;
    BoundInfo info;

    Delta toDelta() const {
        if (info == BoundInfo::INFINITE) {
            return isUpper() ? Delta_PlusInf : Delta_MinusInf;
        }
        if (info == BoundInfo::NONSTRICT) {
            return Delta(boundVal, 0);
        }
        assert(info == BoundInfo::STRICT);
        return Delta(boundVal, isUpper() ? -1 : 1);
    }

    bool isUpper() const { return type == BoundType::UPPER; }
public:
    struct Infinity {};

    struct BLIdx { int x; };
    LABound(BoundType type, LVRef var, int id, Real val, bool strict);
    LABound(BoundType type, LVRef var, int id, Infinity inf);
    inline void setIdx(BLIdx i)  { bidx = i.x; }
    inline BLIdx getIdx() const { return {bidx}; }
    bool isUpperFor(Delta const & val) const {
        assert(type == BoundType::UPPER);
        return (info == BoundInfo::INFINITE)
        || (val.R() < boundVal)
        || (val.R() == boundVal && val.D() < 0)
        || (val.R() == boundVal && val.D() == 0 && info == BoundInfo::NONSTRICT);
    }
    bool isLowerFor(Delta const & val) const {
        assert(type == BoundType::LOWER);
        return info == BoundInfo::INFINITE || val.R() > boundVal
               || (val.R() == boundVal && val.D() > 0)
               || (val.R() == boundVal && val.D() == 0 && info == BoundInfo::NONSTRICT);
    }
    bool isStrictUpperFor(Delta const & val) const {
        assert(type == BoundType::UPPER);
        return info == BoundInfo::INFINITE || val.R() < boundVal
               || (val.R() == boundVal && val.D() < 0 && info == BoundInfo::NONSTRICT);
    }
    bool isStrictLowerFor(Delta const & val) const {
        assert(type == BoundType::LOWER);
        return info == BoundInfo::INFINITE || val.R() > boundVal
               || (val.R() == boundVal && val.D() > 0 && info == BoundInfo::NONSTRICT);
    }

    inline BoundType getType() const { return type; }
    inline LVRef getLVRef() const { return var; }
    int getId() const { return id; }
    char* print() const;
    bool isMinusInf() const { return isInf() && type == BoundType::LOWER; }
    bool isPlusInf()  const { return isInf() && type == BoundType::UPPER; }
    bool isInf()      const { return info == BoundInfo::INFINITE; }
    Delta getDiffToMatch(Delta const& val) const {
        assert(info != BoundInfo::INFINITE);
        if (info == BoundInfo::NONSTRICT) {
            return Delta(boundVal - val.R(), - val.D());
        }
        bool upper = type == BoundType::UPPER;
        Real deltaDiff = [&]() -> Real {
           if (val.D().isZero()) { return upper ? -1 : 1; }
           if ((val.D() < 0) == upper) { return 0; }
           return (upper ? Real(-1) : Real(1)) - val.D();
        }();
        return Delta(boundVal - val.R(), deltaDiff);
//        return delta - val;
    }
    char* printValue() const { return toDelta().printValue(); }
    bool hasSameValueAs(LABound const & other) const { return this->toDelta() == other.toDelta(); }
    inline Real getValue() const { return boundVal; }

    inline friend bool operator<( const LABound &a, const LABound &b ) {
        return a.toDelta() < b.toDelta();
    }
};

class LABoundAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_bounds;
    static int laboundWord32Size() ;/*{
        return (sizeof(LABound)) / sizeof(uint32_t); }*/
public:
    LABoundAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_bounds(0) {}
    LABoundAllocator() : n_bounds(0) {}
    inline unsigned getNumBounds() const;// { return n_bounds; }

    LABoundRef alloc(BoundType type, LVRef var, Real val, bool strict);
    LABoundRef alloc(BoundType type, LVRef var, LABound::Infinity inf);
    inline LABound&       operator[](LABoundRef r)       { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    inline const LABound& operator[](LABoundRef r) const { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
    inline LABound*       lea       (LABoundRef r);
    inline const LABound* lea       (LABoundRef r) const ;
    inline LABoundRef     ael       (const LABound* t) ;
    inline void clear() {}
};

class LABoundList
{
    friend class LABoundListAllocator;
    friend class LABoundStore; // Needed so that I can sort the bounds in the list
    LVRef          v; // Do we need this?
    struct {
        unsigned reloc   : 1;
        unsigned sz      : 31;
    };
    LABoundListRef reloc_target;
    LABoundRef     bounds[0];
public:
    inline bool           reloced   ()                 const ;
    inline LABoundListRef relocation()                 const ;
    inline void           relocate  (LABoundListRef r)   ;
    inline unsigned       size      ()                 const ;
           LABoundRef     operator[](int i)            const;
    inline LVRef          getVar    ()                 const ;
    inline LABoundList              (LVRef v, const vec<LABoundRef>& bs);
};

class bound_lessthan {
    LABoundAllocator& ba;
public:
    bound_lessthan(LABoundAllocator& ba) : ba(ba) {}
    inline bool operator() (LABoundRef r1, LABoundRef r2) const;
};

class LABoundListAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_boundlists;
    static int boundlistWord32Size(int size);
public:
    LABoundListAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_boundlists(0) {}
    LABoundListAllocator() : n_boundlists(0) {}

    void moveTo(LABoundListAllocator& to);

    LABoundListRef alloc(const LVRef v, const vec<LABoundRef>& bs);
    LABoundListRef alloc(LABoundList& from);
    inline LABoundList&       operator[](LABoundListRef r)   ;
    inline const LABoundList& operator[](LABoundListRef r) const;
    inline LABoundList*       lea(LABoundListRef r)        ;
    inline const LABoundList* lea(LABoundListRef r) const  ;
    inline LABoundListRef     ael(const LABoundList* t)    ;

    void free(LABoundListRef tid);
    void reloc(LABoundListRef& tr, LABoundListAllocator& to);
};

class LABoundRefPair {
public:
    LABoundRef pos;
    LABoundRef neg;
    bool operator== (const LABoundRefPair& o) const { return (pos == o.pos) && (neg == o.neg); }
};

class LABoundStore
{
public:
    struct BoundInfo { LVRef v; LABoundRef ub; LABoundRef lb; };
private:
    vec<BoundInfo> in_bounds;
    LABoundAllocator ba{1024};
    LABoundListAllocator bla{1024};
    vec<LABoundListRef> var_bound_lists;
    LAVarStore &lvstore;
public:
    LABoundStore(LAVarStore &lvstore) : lvstore(lvstore) {}
    void buildBounds();
    void updateBound(BoundInfo bi); // Update a single bound.
//    inline LABoundRef getLowerBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].lbound()]; }
//    inline LABoundRef getUpperBound(const LVRef v) const { return bla[lva[v].getBounds()][lva[v].ubound()]; }
    inline LABound& operator[] (LABoundRef br) { return ba[br]; }
    inline const LABound& operator[] (LABoundRef br) const { return ba[br]; }
    // Debug
    char* printBound(LABoundRef br) const; // Print the bound br
    char* printBounds(LVRef v) const; // Print all bounds of v
    LABoundListRef getBounds(LVRef v) const;
    LABoundRef getBoundByIdx(LVRef v, int it) const;
    int getBoundListSize(LVRef v) ;
    bool isUnbounded(LVRef v) const;
    // Construct an upper bound v ~ c and its negation \neg (v ~ c), where ~ is < if strict and <= if !strict
    BoundInfo allocBoundPair(LVRef v, const opensmt::Real& c, bool strict) {
        LABoundRef ub = ba.alloc(BoundType::UPPER, v, c, strict);
        LABoundRef lb = ba.alloc(BoundType::LOWER, v, c, !strict);
        in_bounds.push(BoundInfo{v, ub, lb});
        return in_bounds.last();
    }
    int nVars() const { return lvstore.numVars(); }
};


#endif
