//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_TABLEAU_H
#define OPENSMT_TABLEAU_H


#include "Polynomial.h"
#include "LAVar.h"
#include "Real.h"

#include <unordered_map>
#include <set>
#include <vector>
#include <functional>
#include <memory>

class Column{
    friend class Tableau;
public:
    struct Entry {
        enum class Tag : unsigned char {Valid, Free};
        Tag tag;
        int data;

        Entry(LVRef v): tag{Tag::Valid}, data{static_cast<int>(v.x)} { }
        Entry(): tag{Tag::Valid}, data{0} { }
        inline bool isFree()   const    { return tag == Tag::Free; }
        inline bool isValid()  const    { return tag == Tag::Valid; }

        static Entry LVRefToEntry(LVRef v) { return Entry(v); }
        static LVRef entryToLVRef(Entry e) {
            assert(e.isValid());
            unsigned int val = e.data;
            return LVRef{val};
        }
        static int freeEntryToIndex(Entry e) { assert(e.isFree()); return e.data; }
        static Entry indexToFreeEntry(int i);
    };
private:
    std::vector<Entry> rows;
    int32_t free = -1; // pointer to head of a free list, -1 means no free list
    uint32_t nelems = 0; // the real number of elements;

    uint32_t getFreeSlotIndex();

    using iterator_t = std::vector<Entry>::iterator;
    using const_iterator_t = std::vector<Entry>::const_iterator;



public:
    int addRow(LVRef row) {
        auto index = getFreeSlotIndex();
        rows[index] = Entry::LVRefToEntry(row);
        ++nelems;
        return index;
    }

    void removeRowAt(int index) {
        assert(index >= 0 && static_cast<std::size_t>(index) < rows.size() && rows[index].isValid());
        rows[index] = Entry::indexToFreeEntry(free);
        free = index;
        --nelems;
    }

    void replaceRowAtWith(int index, LVRef newRow) {
        assert(index >= 0 && static_cast<std::size_t>(index) < rows.size() && rows[index].isValid());
        rows[index] = Entry::LVRefToEntry(newRow);
    }

    void clear() {
        rows.clear();
        free = -1;
        nelems = 0;
    }

    bool empty() const {
        return nelems == 0;
    }

    unsigned int size() const {
        return nelems;
    }

    const Entry& operator[](unsigned index) const { assert(index < rows.size()); return rows[index]; }

    iterator_t begin() { return rows.begin(); }
    iterator_t end() { return rows.end(); }

    const_iterator_t begin() const { return rows.cbegin(); }
    const_iterator_t end() const { return rows.cend(); }
//
    const_iterator_t find(LVRef row) const { return std::find_if(begin(), end(),
            [row](Entry e) { return e.isValid() && Entry::entryToLVRef(e) == row; }); }
};

class Tableau{

public:
    class Row {
        Polynomial poly;
        std::vector<int> columnIndices;

    public:
        Polynomial & getPoly() { return poly; }
        Polynomial const & getPoly() const { return poly; }
        decltype(columnIndices) & getColumnIndices() { return columnIndices; }
        decltype(columnIndices) const & getColumnIndices() const { return columnIndices; }

        template<typename ADD, typename REM>
        void merge(const Row &other, const opensmt::Real &coeff, ADD informAdded,
                                 REM informRemoved, std::vector<Polynomial::Term>& storage);

        };

protected:

    // using column_t = std::unordered_set<LVRef, LVRefHash>;
    using column_t = Column;
    using rows_t = std::vector<std::unique_ptr<Row>>;
//    using vars_t = std::unordered_set<LVRef, LVRefHash>;
    using vars_t = std::set<LVRef, LVRefComp>;

public:
    void newNonbasicVar(LVRef v);
    void nonbasicVar(LVRef v);
    void newRow(LVRef v, std::unique_ptr<Row> poly);
    std::size_t getNumOfCols() const;
    std::size_t getPolySize(LVRef basicVar) const;
    const opensmt::Real & getCoeff(LVRef basicVar, LVRef nonBasicVar) const;
    const column_t & getColumn(LVRef nonBasicVar) const;
    const Polynomial & getRowPoly(LVRef basicVar) const;
    Polynomial & getRowPoly(LVRef basicVar);
    Row & getRow(LVRef basicVar);
    Row const & getRow(LVRef basicVar) const;
    const rows_t & getRows() const;

    void clear();
    void pivot(LVRef bv, LVRef nv);
    bool isBasic(LVRef v) const;
    bool isNonBasic(LVRef v) const;
    bool isQuasiBasic(LVRef v) const;

    bool isProcessed(LVRef v) const;

    void quasiToBasic(LVRef v);
    void basicToQuasi(LVRef v);

    // debug
    void print() const;
    bool checkConsistency() const;
    std::vector<LVRef> getNonBasicVars() const;

private:
    std::vector<std::unique_ptr<column_t>> cols;
    rows_t rows;

    enum class VarType:char {
        NONE, BASIC, NONBASIC, QUASIBASIC
    };
    std::vector<VarType> varTypes;
    void ensureTableauReadyFor(LVRef v);

    void addRow(LVRef v, std::unique_ptr<Row> p);
//    std::unique_ptr<Row> removeRow(LVRef v);
    void moveRowFromTo(LVRef from, LVRef to);
    void moveColFromTo(LVRef from, LVRef to);
    int addRowToColumn(LVRef row, LVRef col) { assert(cols[col.x]); return cols[col.x]->addRow(row); }
    void replaceRowFromColumnAtWith(int i, LVRef col, LVRef nrow) { assert(cols[col.x]); cols[col.x]->replaceRowAtWith(i, nrow); }
    void removeRowFromColumnAt(int i, LVRef col) { assert(cols[col.x]); cols[col.x]->removeRowAt(i); }
    void clearColumn(LVRef col) { assert(cols[col.x]); cols[col.x]->clear();}
    void normalizeRow(LVRef row);
    void updateRowFor(LVRef bv, LVRef nv);
    std::pair<int, opensmt::Real> removeVarFromRow(LVRef colVar, LVRef rowVar);
};

template<typename ADD, typename REM>
void Tableau::Row::merge(const Tableau::Row &other, const opensmt::Real &coeff, ADD informAdded,
                       REM informRemoved, std::vector<Polynomial::Term>& storage) {
    storage.reserve(this->poly.size() + other.poly.size());
    std::vector<int> nColIndices;
    nColIndices.reserve(storage.capacity());
    assert(this->poly.size() == this->columnIndices.size());
    assert(other.poly.size() == other.columnIndices.size());
    auto myColIndIt = this->columnIndices.begin();
    auto myColIndEnd = this->columnIndices.end();
    auto myIt = std::make_move_iterator(poly.begin());
    auto otherIt = other.poly.begin();
    auto myEnd = std::make_move_iterator(poly.end());
    auto otherEnd = other.poly.end();
    Polynomial::TermCmp cmp;
    auto handleAdded = [&nColIndices, &informAdded](LVRef toAdd) {
        int nIndex = informAdded(toAdd);
        if (nIndex >= 0) {
            nColIndices.push_back(nIndex);
        }
    };
    while(true) {
        if (myIt == myEnd) {
            for (auto it = otherIt; it != otherEnd; ++it) {
                storage.emplace_back(it->var, it->coeff * coeff);
                handleAdded(it->var);
            }
            break;
        }
        if (otherIt == otherEnd) {
            storage.insert(storage.end(), myIt, myEnd);
            nColIndices.insert(nColIndices.end(), myColIndIt, myColIndEnd);
            break;
        }
        if (cmp(*myIt, *otherIt)) {
            storage.emplace_back(*myIt);
            nColIndices.push_back(*myColIndIt);
            ++myIt;
            ++myColIndIt;
        }
        else if (cmp(*otherIt, *myIt)) {
            storage.emplace_back(otherIt->var, otherIt->coeff * coeff);
            handleAdded(otherIt->var);
            ++otherIt;
        }
        else {
            assert(myIt->var == otherIt->var);
            auto mergedCoeff = otherIt->coeff * coeff;
            mergedCoeff += myIt->coeff;
            if (mergedCoeff.isZero()) {
                informRemoved(myIt->var, *myColIndIt);
            }
            else {
                storage.emplace_back(myIt->var, std::move(mergedCoeff));
                nColIndices.push_back(*myColIndIt);
            }
            ++myColIndIt;
            ++myIt;
            ++otherIt;
        }
    }
    std::vector<Polynomial::Term>(std::make_move_iterator(storage.begin()), std::make_move_iterator(storage.end())).swap(poly.poly);
    nColIndices.swap(this->columnIndices);
    storage.clear();
}


#endif //OPENSMT_TABLEAU_H
