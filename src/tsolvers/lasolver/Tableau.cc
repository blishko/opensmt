//
// Created by Martin Blicha on 31.03.18.
//

#include "Tableau.h"
#include <iostream>

using namespace opensmt;
namespace {
    template<class C, class E>
    inline bool contains(const C & container, const E & elem){
        return container.find(elem) != container.end();
    }

    inline bool isOne(const opensmt::Real & r){
        return r == 1;
    }
}

void Tableau::nonbasicVar(LVRef v) {
    if(isNonBasic(v)) {return;}
    assert(!isProcessed(v));
    newNonbasicVar(v);
}

void Tableau::newNonbasicVar(LVRef v) {
    assert(!isProcessed(v));
    ensureTableauReadyFor(v);
    assert(!cols[v.x]);
    cols[v.x] = std::unique_ptr<Column>(new Column());
    varTypes[getVarId(v)] = VarType::NONBASIC;
}

void Tableau::newRow(LVRef v, std::unique_ptr<Row> poly) {
    assert(!isProcessed(v));
    ensureTableauReadyFor(v);
    addRow(v, std::move(poly));
    varTypes[getVarId(v)] = VarType::QUASIBASIC;

}

std::size_t Tableau::getNumOfCols() const {
    return cols.size();
}

std::size_t Tableau::getPolySize(LVRef basicVar) const {
    return getRowPoly(basicVar).size();
}

const opensmt::Real & Tableau::getCoeff(LVRef basicVar, LVRef nonBasicVar) const {
    return getRowPoly(basicVar).getCoeff(nonBasicVar);
}

const Tableau::column_t & Tableau::getColumn(LVRef nonBasicVar) const {
    assert(cols[nonBasicVar.x]);
    return *cols[nonBasicVar.x];
}

const Polynomial & Tableau::getRowPoly(LVRef basicVar) const {
    return getRow(basicVar).getPoly();
}

Polynomial & Tableau::getRowPoly(LVRef basicVar) {
    return getRow(basicVar).getPoly();
}

Tableau::Row & Tableau::getRow(LVRef basicVar) {
    assert(rows[basicVar.x]);
    return *rows[basicVar.x];
}

Tableau::Row const & Tableau::getRow(LVRef basicVar) const {
    assert(rows[basicVar.x]);
    return *rows[basicVar.x];
}


const Tableau::rows_t & Tableau::getRows() const {
    return rows;
}

std::vector<LVRef> Tableau::getNonBasicVars() const {
    std::vector<LVRef> res;
    res.resize(varTypes.size());
    for (unsigned i = 0; i < varTypes.size(); ++i) {
        if (varTypes[i] == VarType::NONBASIC) {
            res.push_back(LVRef{i});
        }
    }
    return res;
}

void Tableau::addRow(LVRef v, std::unique_ptr<Row> p) {
    assert(!rows[v.x]);
    rows[v.x] = std::move(p);
}

//std::unique_ptr<Tableau::Row> Tableau::removeRow(LVRef v) {
//    assert(rows[v.x]);
//    std::unique_ptr<Row> res;
//    assert(!res);
//    res.swap(rows[v.x]);
//    return res;
//}

void Tableau::moveRowFromTo(LVRef from, LVRef to) {
    assert(!rows[to.x]);
    assert(rows[from.x]);
    rows[to.x] = std::move(rows[from.x]);
}

void Tableau::moveColFromTo(LVRef from, LVRef to) {
    assert(!cols[to.x]);
    assert(cols[from.x]);
    cols[to.x] = std::move(cols[from.x]);
}

bool Tableau::isProcessed(LVRef v) const {
    return varTypes.size() > getVarId(v) && varTypes[getVarId(v)] != VarType::NONE;
}

/**
 * Changes the row corresponding to basic variable bv so that now it corresponds to the non-basic variable nv, which
 * is about to become the new basicc variable.
 * After this method executes, bv has no row and nv has a row with correct polynomial representation and correct column indices
 * (except the column still belongs to non-basic variable?!)
 *
 * @param bv Row variable
 * @param nv Column variable
 */
void Tableau::updateRowFor(LVRef bv, LVRef nv) {
    Row & row = getRow(bv);
    Polynomial & poly = row.getPoly();
    // locate the variable to replace
    auto it = poly.findTermForVar(nv);
    // remember the index for updating also the column indices
    auto index = it - poly.begin();
    auto columnIndex = row.getColumnIndices()[index];
    // replace the variable
    it->var = bv;
    replaceRowFromColumnAtWith(columnIndex, nv, nv);
    // update the coefficient -> normalize the polynomial so that the coeff at it is -1 and compute the new coeff
    Real bvCoeff{1};
    if (!isOne(it->coeff)) {
        bvCoeff /= it->coeff;
        poly.divideBy(it->coeff);
    }
    poly.negate();
    it->coeff = std::move(bvCoeff);
    // Now we need to restore the invariant that the terms are sorted
    bool bubbleBackward = (bv.x < nv.x);
    Polynomial::TermCmp cmp;
    auto colIndIt = row.getColumnIndices().begin() + index;
    if (bubbleBackward) {
        while(it != poly.begin() && cmp(*it, *(it - 1))) {
            std::iter_swap(it, it -1);
            std::iter_swap(colIndIt, colIndIt - 1);
            --it; --colIndIt;
        }
    }
    else {
        // bubbleForward
        while(it + 1 != poly.end() && cmp(*(it + 1), *it)) {
            std::iter_swap(it, it + 1);
            std::iter_swap(colIndIt, colIndIt + 1);
            ++it; ++colIndIt;
        }
    }
    // Now the sorted invariant is restored
#ifndef NDEBUG
    assert(poly.size() == row.getColumnIndices().size());
    assert(std::is_sorted(poly.begin(), poly.end(), cmp));
    for(int i = 0; i < poly.size(); ++i) {
        LVRef varInPoly = poly[i].var;
        LVRef columnVar = varInPoly == bv ? nv : varInPoly;
        LVRef expected = varInPoly == bv ? nv : bv;
        Column const & column = getColumn(columnVar);
        Column::Entry e = column[row.getColumnIndices()[i]];
        assert(e.isValid() && Column::Entry::entryToLVRef(e) == expected);
    }
#endif //NDEBUG
    // Move the row to the new variable that it corresponds to
    moveRowFromTo(bv, nv);
}

std::pair<int, opensmt::Real> Tableau::removeVarFromRow(LVRef colVar, LVRef rowVar) {
    Row & row = getRow(rowVar);
    Polynomial & poly = row.getPoly();
    auto it = poly.findTermForVar(colVar);
    auto index = it - poly.begin();
    auto colIndIt = row.getColumnIndices().begin() + index;
    std::pair<int, opensmt::Real> res;
    res.first = row.getColumnIndices()[index];
    row.getColumnIndices().erase(colIndIt);
    res.second = std::move(it->coeff);
    poly.poly.erase(it);
    return res;
}

void Tableau::pivot(LVRef bv, LVRef nv) {
    assert(isBasic(bv));
    assert(isNonBasic(nv));
    varTypes[getVarId(bv)] = VarType::NONBASIC;
    varTypes[getVarId(nv)] = VarType::BASIC;
    assert(cols[nv.x]);
    assert(!cols[bv.x]);
    assert(rows[bv.x]);
    assert(!rows[nv.x]);

    // update row to correspond to nv instead of bv
    updateRowFor(bv, nv);
    // move the column from nv to bv
    moveColFromTo(nv, bv);

    {
        auto const & row = getRow(nv);
        assert(row.getPoly().size() == row.getColumnIndices().size());
        auto termIt = row.getPoly().begin();
        auto indIt = row.getColumnIndices().begin();
        auto end = row.getPoly().end();
        // update column information regarding this one poly
        for (; termIt != end; ++termIt, ++indIt) {
            auto var = termIt->var;
            assert(cols[var.x]);
            replaceRowFromColumnAtWith(*indIt, var, nv);
//        removeRowFromColumn(bv, var);
//        addRowToColumn(nv, var);
        }
    }
    std::vector<Polynomial::Term> storage;
    // for all (active) rows containing nv, substitute
    auto const & col = getColumn(bv);
    auto size = col.size();
    for (auto it = col.begin(); it != col.end(); ++it) {
        auto const& entry = *it;
        if (entry.isFree()) { continue; }
        LVRef rowVar = entry.entryToLVRef(entry);
        assert(!isQuasiBasic(rowVar));
        if(rowVar == nv || isQuasiBasic(rowVar)) {
            continue;
        }
        // update the polynomials
        auto & row = getRow(rowVar);
        const auto indexCoeffPair = removeVarFromRow(nv, rowVar);
        assert(indexCoeffPair.first == (it - col.begin()));
        removeRowFromColumnAt(indexCoeffPair.first, bv);
        // also columna information must be removed
        row.merge(getRow(nv), indexCoeffPair.second,
                // informAdded
                   [this, bv, rowVar](LVRef addedVar) {
//                       if (addedVar == bv) { return -1; }
                       assert(cols[addedVar.x]);
                       assert(!contains(getColumn(addedVar), rowVar));
                       return addRowToColumn(rowVar, addedVar);
                   },
                // informRemoved
                   [this, rowVar](LVRef removedVar, int index) {
                       assert(cols[removedVar.x]);
                       assert(contains(getColumn(removedVar), rowVar));
                       removeRowFromColumnAt(index, removedVar);
                   }
                   , storage
        );
    }
    assert(!cols[nv.x]);
    assert(cols[bv.x]);
    assert(!rows[bv.x]);
    assert(rows[nv.x]);
}

void Tableau::clear() {
    this->rows.clear();
    this->cols.clear();
    this->varTypes.clear();
}

bool Tableau::isBasic(LVRef v) const
    {return varTypes.size() > getVarId(v) && varTypes[getVarId(v)] == VarType::BASIC;}
bool Tableau::isNonBasic(LVRef v) const
    {return varTypes.size() > getVarId(v) && varTypes[getVarId(v)] == VarType::NONBASIC;}
bool Tableau::isQuasiBasic(LVRef v) const
    {return varTypes.size() > getVarId(v) && varTypes[getVarId(v)] == VarType::QUASIBASIC;}

void Tableau::print() const {
    std::cout << "Rows:\n";
    for(unsigned i = 0; i != rows.size(); ++i) {
        if (!rows[i]) { continue; }
        std::cout << "Var of the row: " << i << ';';
        for (const auto & term : this->getRowPoly(LVRef{i})) {
            std::cout << "( " << term.coeff << " | " << term.var.x << " ) ";
        }
        std::cout << '\n';
    }
    std::cout << '\n';
    std::cout << "Columns:\n";
    for(unsigned i = 0; i != cols.size(); ++i) {
        if(!cols[i]) { continue; }
        std::cout << "Var of the column: " << i << "; Contains: ";
        for (auto entry : getColumn(LVRef{i})) {
            if (entry.isFree()) { continue; }
            std::cout << Column::Entry::entryToLVRef(entry).x << ' ';
        }
        std::cout << '\n';
    }
    std::cout << '\n';
}

bool Tableau::checkConsistency() const {
    bool res = true;
    for(unsigned i = 0; i < cols.size(); ++i) {
        LVRef var {i};
        if (isNonBasic(var)) {
            res &= (cols[i] != nullptr);
            assert(res);
            for(auto entry : *cols[i]) {
                if (entry.isFree()) { continue; }
                LVRef row = Column::Entry::entryToLVRef(entry);
                res &= this->getRowPoly(row).contains(var);
                assert(res);
            }
        }
        else{
            assert(!cols[i]);
        }
    }

    for(unsigned i = 0; i < rows.size(); ++i) {
        LVRef var {i};
        if(isQuasiBasic(var)) {
            continue;
        }
        if (!rows[i]) { assert(isNonBasic(var)); continue; }
        res &= isBasic(var);
        assert(res);
        assert(getRowPoly(var).size() == getRow(var).getColumnIndices().size());
        for (auto const & term : getRowPoly(var)) {
            auto termVar = term.var;
            res &= isNonBasic(termVar) && cols[termVar.x];
            assert(res);
            res &= contains(getColumn(termVar), var);
            assert(res);
        }
    }
    return res;
}

// Makes sures the representing polynomial of this row contains only nonbasic variables
void Tableau::normalizeRow(LVRef v) {
    assert(isQuasiBasic(v)); // Do not call this for non quasi rows
    Row & row = getRow(v);
    Polynomial & rowPoly = row.getPoly();
    std::vector<Polynomial::Term> toEliminate;
    for (auto & term : rowPoly) {
        if (isQuasiBasic(term.var)) {
            normalizeRow(term.var);
            toEliminate.push_back(term);
        }
        if (isBasic(term.var)) {
            toEliminate.push_back(term);
        }
    }
    if (!toEliminate.empty()) {
        Polynomial p;
        for (auto & term : toEliminate) {
            p.merge(getRowPoly(term.var), term.coeff, [](LVRef) {}, [](LVRef) {});
            p.addTerm(term.var, -term.coeff);
        }
        rowPoly.merge(p, 1, [](LVRef) {}, [](LVRef) {});
    }
}

// Eliminates basic variables from representation of this row.
void Tableau::quasiToBasic(LVRef v) {
    assert(isQuasiBasic(v));
    normalizeRow(v);
    Row & row = getRow(v);
    for (auto & term : row.getPoly()) {
        LVRef var = term.var;
        row.getColumnIndices().push_back(addRowToColumn(v, var));
    }
    varTypes[getVarId(v)] = VarType::BASIC;
    assert(isBasic(v));
    assert(checkConsistency());
}

void Tableau::basicToQuasi(LVRef v) {
    assert(checkConsistency());
    assert(isBasic(v));
    varTypes[getVarId(v)] = VarType::QUASIBASIC;
    assert(isQuasiBasic(v));

    auto termIt = getRow(v).getPoly().begin();
    auto end = getRow(v).getPoly().end();
    auto indIt = getRow(v).getColumnIndices().begin();
    while (termIt != end) {
        LVRef var = termIt->var;
        assert(isNonBasic(var));
        removeRowFromColumnAt(*indIt, var);
        ++termIt;
        ++indIt;
    }
    getRow(v).getColumnIndices().clear();
    assert(checkConsistency());
}

void Tableau::ensureTableauReadyFor(LVRef v) {
    auto id = getVarId(v);
    while(cols.size() <= id) {
        cols.emplace_back();
    }
    while(rows.size() <= id) {
        rows.emplace_back();
    }
    while(varTypes.size() <= id) {
        varTypes.push_back(VarType::NONE);
    }
}

uint32_t Column::getFreeSlotIndex() {
    auto ret = free;
    if (ret >= 0) {
        Entry e = rows[free];
        assert(e.isFree());
        free = Entry::freeEntryToIndex(e);
        assert(free < 0 || static_cast<std::size_t>(free) < rows.size());
        return ret;
    }
    ret = rows.size();
    rows.emplace_back();
    return ret;
}

Column::Entry Column::Entry::indexToFreeEntry(int index) {
    Entry ret;
    ret.tag = Entry::Tag::Free;
    ret.data = index;
    return ret;
}
