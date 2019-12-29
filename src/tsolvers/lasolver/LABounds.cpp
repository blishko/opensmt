#include "LABounds.h"
#include "LRALogic.h"

LABound::LABound(BoundType type, LVRef var, int id, Real val, bool strict)
    : type(type)
    , bidx(UINT32_MAX)
    , id(id)
    , var(var)
    , boundVal(val)
    , info(strict ? BoundInfo::STRICT : BoundInfo::NONSTRICT)
{}

LABound::LABound(BoundType type, LVRef var, int id, Infinity inf)
    : type(type)
    , bidx(UINT32_MAX)
    , id(id)
    , var(var)
    , boundVal(0)
    , info(BoundInfo::INFINITE)
{}

char* LABound::print() const
{
    char* str_out;
    char* v_str_lvr;
    int written = asprintf(&v_str_lvr, "v%d", this->getLVRef().x);
    assert(written >= 0);
    char* v_str;
    written = asprintf(&v_str, "%s", v_str_lvr);
    assert(written >= 0); (void)written;
    free(v_str_lvr);

    if (this->isMinusInf())
        written = asprintf(&str_out, "- Inf <= %s", v_str);
    else if (this->isPlusInf())
        written = asprintf(&str_out, "%s <= + Inf", v_str);
    else {
        opensmt::Real r = boundVal;
        opensmt::Real s = info == BoundInfo::NONSTRICT ? 0 : type == BoundType::LOWER ? 1 : -1;
        if ((type == BoundType::LOWER) && (s == 0))
            written = asprintf(&str_out, "%s <= %s", r.get_str().c_str(), v_str);
        if ((type == BoundType::LOWER) && (s != 0))
            written = asprintf(&str_out, "%s < %s", r.get_str().c_str(), v_str);
        if ((type == BoundType::UPPER) && (s == 0))
            written = asprintf(&str_out, "%s <= %s", v_str, r.get_str().c_str());
        if ((type == BoundType::UPPER) && (s != 0))
            written = asprintf(&str_out, "%s < %s", v_str, r.get_str().c_str());
    }
    assert(written >= 0); (void)written;
    free(v_str);
    return str_out;
}

LABoundRef LABoundAllocator::alloc(BoundType type, LVRef var, Real val, bool strict)
{
    uint32_t v = RegionAllocator<uint32_t>::alloc(laboundWord32Size());
    LABoundRef id = {v};
    new (lea(id)) LABound(type, var, n_bounds++, std::move(val), strict);
    return id;
}

LABoundRef LABoundAllocator::alloc(BoundType type, LVRef var, LABound::Infinity inf)
{
    uint32_t v = RegionAllocator<uint32_t>::alloc(laboundWord32Size());
    LABoundRef id = {v};
    new (lea(id)) LABound(type, var, n_bounds++, inf);
    return id;
}

LABoundList::LABoundList(LVRef v, const vec<LABoundRef>& bs)
    : v(v)
    , reloc(0)
    , sz(bs.size())
{
    for (int i = 0; i < bs.size(); i++)
        bounds[i] = bs[i];
}

void LABoundListAllocator::moveTo(LABoundListAllocator& to)
{
    to.n_boundlists = n_boundlists;
    RegionAllocator<uint32_t>::moveTo(to);
}

LABoundListRef LABoundListAllocator::alloc(const LVRef v, const vec<LABoundRef>& bs)
{
    uint32_t b = RegionAllocator<uint32_t>::alloc(boundlistWord32Size(bs.size()));
    LABoundListRef id = {b};
    new (lea(id)) LABoundList(v, bs);
    return id;
}

LABoundListRef LABoundListAllocator::alloc(LABoundList& from)
{
    vec<LABoundRef> tmp;
    for (int i = 0; i < from.size(); i++)
        tmp.push(from[i]);
    return alloc(from.getVar(), tmp);
}

void LABoundListAllocator::free(LABoundListRef tid)
{
    LABoundList& b = operator[](tid);
    RegionAllocator<uint32_t>::free(boundlistWord32Size(b.size()));
}

void LABoundListAllocator::reloc(LABoundListRef& tr, LABoundListAllocator& to)
{
    LABoundList& bl = operator[](tr);
    if (bl.reloced()) { tr = bl.relocation(); return; }
    tr = to.alloc(bl);
    bl.relocate(tr);
    to[tr].sz = bl.size();
    to[tr].v  = bl.getVar();
}


void LABoundStore::updateBound(BoundInfo bi) {
    // Fix this to do a linear traverse
    vec<LABoundRef> new_bounds;
    LABoundListRef blr = var_bound_lists[getVarId(bi.v)];

    for (int i = 0; i < bla[blr].size(); i++)
        new_bounds.push(bla[blr][i]);

    new_bounds.push(bi.ub);
    new_bounds.push(bi.lb);

    LABoundListRef br = bla.alloc(bi.v, new_bounds);
    var_bound_lists[getVarId(bi.v)] = br;
    sort<LABoundRef,bound_lessthan>(bla[br].bounds, bla[br].size(), bound_lessthan(ba));

    for (int j = 0; j < bla[br].size(); j++)
        ba[bla[br][j]].setIdx(LABound::BLIdx{j});
}

void LABoundStore::buildBounds()
{
    VecMap<LVRef, BoundInfo, LVRefHash> bounds_map;

    for (int i = 0; i < in_bounds.size(); i++) {
        LVRef v = in_bounds[i].v;
        if (!bounds_map.has(v))
            bounds_map.insert(v, vec<BoundInfo>());
        bounds_map[v].push(in_bounds[i]);
    }
    vec<LVRef> keys;
    bounds_map.getKeys(keys);
    for (int i = 0; i < keys.size(); i++) {
        vec<LABoundRef> refs;
        LABoundRef lb_minusInf = ba.alloc(BoundType::LOWER, keys[i], LABound::Infinity{});
        LABoundRef ub_plusInf = ba.alloc(BoundType::UPPER, keys[i], LABound::Infinity{});
        refs.push(lb_minusInf);
        refs.push(ub_plusInf);
        for (int j = 0; j < bounds_map[keys[i]].size(); j++) {
            BoundInfo &info = bounds_map[keys[i]][j];
            refs.push(info.ub);
            refs.push(info.lb);
        }
        LABoundListRef br = bla.alloc(keys[i], refs);

        while (var_bound_lists.size() <= getVarId(keys[i]))
            LABoundStore::var_bound_lists.push(LABoundListRef_Undef);
        var_bound_lists[getVarId(keys[i])] = br;
        sort<LABoundRef,bound_lessthan>(bla[br].bounds, bla[br].size(), bound_lessthan(ba));

        for (int j = 0; j < bla[br].size(); j++)
            ba[bla[br][j]].setIdx(LABound::BLIdx{j});

        // Check that the bounds are correctly ordered
#ifdef DO_BOUNDS_CHECK
        vec<LABoundRef> lowerbounds;
        vec<LABoundRef> upperbounds;
        for (int j = 1; j < bla[br].size() - 1; j++) {
            LABoundRef tmp = bla[br].bounds[j];
            if (ba[tmp].getType() == bound_l)
                lowerbounds.push(tmp);
            else
                upperbounds.push(tmp);
        }
        for (int j = 0; j < lowerbounds.size()-1; j++) {
            LABoundRef bound_higher = lowerbounds[j+1];
            LABoundRef bound_lower = lowerbounds[j];
            PTRef ref_higher = ba[bound_higher].getSign() == l_False ? logic.mkNot(ba[bound_higher].getPTRef()) : ba[bound_higher].getPTRef();
            PTRef ref_lower = ba[bound_lower].getSign() == l_False ? logic.mkNot(ba[bound_lower].getPTRef()) : ba[bound_lower].getPTRef();
//            printf("Checking that %s -> %s\n", printBound(bound_higher), printBound(bound_lower));
            logic.implies(ref_higher, ref_lower);
        }
        for (int j = 0; j < upperbounds.size()-1; j++) {
            LABoundRef bound_higher = upperbounds[j+1];
            LABoundRef bound_lower = upperbounds[j];
            PTRef ref_higher = ba[bound_higher].getSign() == l_False ? logic.mkNot(ba[bound_higher].getPTRef()) : ba[bound_higher].getPTRef();
            PTRef ref_lower = ba[bound_lower].getSign() == l_False ? logic.mkNot(ba[bound_lower].getPTRef()) : ba[bound_lower].getPTRef();
//            printf("Checking that %s -> %s\n", printBound(bound_lower), printBound(bound_higher));
            logic.implies(ref_lower, ref_higher);
        }
#endif

    }

    // make sure all variables have at least the trivial bounds
    for (unsigned i = 0; i < lvstore.numVars(); i++) {
        LVRef ref {i};
        auto id = getVarId(ref);
        while (var_bound_lists.size() <= id)
            var_bound_lists.push(LABoundListRef_Undef);

        if (var_bound_lists[id] == LABoundListRef_Undef) {
            vec<LABoundRef> refs;
            LABoundRef lb_minusInf = ba.alloc(BoundType::LOWER, keys[i], LABound::Infinity{});
            LABoundRef ub_plusInf = ba.alloc(BoundType::UPPER, keys[i], LABound::Infinity{});
            refs.push(lb_minusInf);
            refs.push(ub_plusInf);
            LABoundListRef br = bla.alloc(ref, refs);
            var_bound_lists[id] = br;
        }
    }
}

LABoundRef
LABoundList::operator[](int i) const
{
    return bounds[i];
}

// Debug

char*
LABoundStore::printBound(LABoundRef br) const
{
    return ba[br].print();
}

char* LABoundStore::printBounds(LVRef v) const
{
    LABoundListRef blr = var_bound_lists[getVarId(v)];
    char* bounds_str = (char*) malloc(1);
    bounds_str[0] = '\0';
    for (int i = 0; i < bla[blr].size(); i++) {
        LABoundRef br = bla[blr][i];
        char* tmp;
        char* tmp2 = printBound(br);
        int written = asprintf(&tmp, "%s(%s) ", bounds_str, tmp2);
        assert(written >= 0); (void)written;
        free(bounds_str);
        free(tmp2);
        bounds_str = tmp;
    }
    return bounds_str;
}




int LABoundAllocator::laboundWord32Size() {
    return (sizeof(LABound)) / sizeof(uint32_t); }

inline unsigned LABoundAllocator::getNumBounds() const { return n_bounds; }

inline LABound*       LABoundAllocator::lea       (LABoundRef r)       { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
inline const LABound* LABoundAllocator::lea       (LABoundRef r) const { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
inline LABoundRef     LABoundAllocator::ael       (const LABound* t)   { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundRef rf; rf.x = r; return rf; }

inline bool           LABoundList::reloced   ()                 const { return reloc; }
inline LABoundListRef LABoundList::relocation()                 const { return reloc_target; }
inline void           LABoundList::relocate  (LABoundListRef r)       { reloc = 1; reloc_target = r; }
inline unsigned       LABoundList::size      ()                 const { return sz; }

inline LVRef          LABoundList::getVar    ()                 const { return v; }

inline bool bound_lessthan::operator() (LABoundRef r1, LABoundRef r2) const { return ba[r1] < ba[r2]; }

int LABoundListAllocator::boundlistWord32Size(int size) {
    return (sizeof(LABoundList) + (sizeof(LABoundRef)*size)) / sizeof(uint32_t); }

inline LABoundList&       LABoundListAllocator::operator[](LABoundListRef r)       { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
inline const LABoundList& LABoundListAllocator::operator[](LABoundListRef r) const { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
inline LABoundList*       LABoundListAllocator::lea(LABoundListRef r)              { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
inline const LABoundList* LABoundListAllocator::lea(LABoundListRef r) const        { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
inline LABoundListRef     LABoundListAllocator::ael(const LABoundList* t)          { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundListRef rf; rf.x = r; return rf; }

//inline LABound& LABoundStore::operator[] (LABoundRef br) { return ba[br]; }
LABoundListRef LABoundStore::getBounds(LVRef v) const { return var_bound_lists[getVarId(v)]; }
LABoundRef LABoundStore::getBoundByIdx(LVRef v, int it) const { return bla[getBounds(v)][it]; }
int LABoundStore::getBoundListSize(LVRef v) { return bla[getBounds(v)].size(); }
bool LABoundStore::isUnbounded(LVRef v) const { return ( (bla[getBounds(v)].size() == 2) && (ba[bla[getBounds(v)][0]].isMinusInf()) && (ba[bla[getBounds(v)][1]].isPlusInf()) ); }
