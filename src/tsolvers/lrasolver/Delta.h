/*********************************************************************
 Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>
       , Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
       , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

 OpenSMT2 -- Copyright (C) 2012 - 2015, Antti Hyvarinen
                           2008 - 2012, Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef DELTA_H
#define DELTA_H

#include "Real.h"

using opensmt::Real;

//
// Class to keep the delta values and bounds values for the LAVar
//
class Delta
{
private:
    Real r;     // main value
    Real d;     // delta to keep track of < / <= difference
    bool infinite;// infinite bit
    bool positive;// +/- infinite bit

    inline bool isLess( const Real &c ) const;    //basic function to use in comparison with Real operator
    inline bool isGreater( const Real &c ) const; //basic function to use in comparison with Real operator

public:

    // possible types of initial Delta values;
    typedef enum
    {
        UPPER, LOWER, ZERO
    } deltaType;

    inline Delta( deltaType p );                  // Constructor (true for +inf; false for -inf)
    inline Delta();                               // Same as Delta(UPPER)
    inline Delta( const Real &v );                // Constructor for Real delta
    inline Delta( const Real &v, const Real &d ); // Constructor for Real delta with strict part
    inline Delta( const Delta &a );               // Copy constructor
    inline ~Delta( );                             // Destructor

    inline const Real& R( ) const;                // main value
    inline const Real& D( ) const;                // delta to keep track of < / <= difference
    inline bool hasDelta( ) const;                // TRUE is delta != 0
    inline bool isMinusInf( ) const;              // True if -inf
    inline bool isPlusInf( ) const;               // True if +inf
    inline bool isInf( ) const;                   // True if inf (any)
    void negate() { if (!isInf()) {r.negate(); d.negate();} else { positive = !positive; } }
    void reset();

    inline Delta& operator=( const Delta &a );    //Assign operator
    inline Delta& operator=(Delta &&) noexcept;            // Move assign operator
    inline Delta( Delta &&);                      // Move constructor
    inline Delta (Real &&);                       // Move constructor from Real

    // Comparisons overloading
    inline friend bool operator<( const Delta &a, const Delta &b );
    inline friend bool operator<=( const Delta &a, const Delta &b );
    inline friend bool operator>( const Delta &a, const Delta &b );
    inline friend bool operator>=( const Delta &a, const Delta &b );
    inline friend bool operator==( const Delta &a, const Delta &b );
    inline friend bool operator!=( const Delta &a, const Delta &b );

    inline friend bool operator<( const Delta &a, const Real &c );
    inline friend bool operator<=( const Delta &a, const Real &c );
    inline friend bool operator>( const Delta &a, const Real &c );
    inline friend bool operator>=( const Delta &a, const Real &c );

    inline friend bool operator<( const Real &c, const Delta &a );
    inline friend bool operator<=( const Real &c, const Delta &a );
    inline friend bool operator>( const Real &c, const Delta &a );
    inline friend bool operator>=( const Real &c, const Delta &a );

    // Arithmetic overloadings
    inline friend Delta operator+=( Delta &a, const Delta &b );
    inline friend Delta operator-=( Delta &a, const Delta &b );
    inline friend Delta operator-( const Delta &a, const Delta &b );
    inline friend Delta operator+( const Delta &a, const Delta &b );
    inline friend Delta operator*( const Real &c, const Delta &a );
    inline friend Delta operator*( const Delta &a, const Real &c );
    inline friend Delta operator/( const Delta &a, const Real &c );

    void print( std::ostream & out ) const;            // print the Delta
    char* printValue() const;
    inline friend std::ostream & operator<<( std::ostream & out, const Delta & b )
    {
        b.print( out );
        return out;
    }

};


// main value
inline const Real& Delta::R( ) const
{
    assert(!infinite);
    return r;
}

// delta value (to keep track of < / <= difference)
inline const Real& Delta::D( ) const
{
    assert( !infinite );
    return d;
}

bool Delta::hasDelta( ) const
{
    return !infinite && ( !D( ).isZero() );
}

bool Delta::isPlusInf( ) const
{
    return infinite && positive;
}

bool Delta::isMinusInf( ) const
{
    return infinite && !positive;
}

bool Delta::isInf( ) const
{
    return infinite;
}

// Arithmetic operators definitions.
Delta operator+=( Delta &a, const Delta &b )
{
    assert( !a.isInf( ) );
    assert( !b.isInf( ) );
    if ( !( a.isInf( ) || b.isInf( ) ) )
    {
        a.r += b.R( );
        a.d += b.D( );
    }
    return a;
}

Delta operator-=( Delta &a, const Delta &b )
{
    assert( !a.isInf( ) );
    assert( !b.isInf( ) );
    if ( !( a.isInf( ) || b.isInf( ) ) )
    {
        a.r -= b.R( );
        a.d -= b.D( );
    }
    return a;
}

Delta operator-( const Delta &a, const Delta &b )
{
    if (a.isInf()) { return a; }
    if (b.isInf()) { Delta res = b; res.negate(); return res; }
    // none is infinite
    return Delta( a.R( ) - b.R( ), a.D( ) - b.D( ) );
//    if ( !( a.isInf( ) || b.isInf( ) ) )
//        return Delta( a.R( ) - b.R( ), a.D( ) - b.D( ) );
//    else
//        return a;
}

Delta operator+( const Delta &a, const Delta &b )
{
    if ( !( a.isInf( ) || b.isInf( ) ) )
        return Delta( a.R( ) + b.R( ), a.D( ) + b.D( ) );
    else
        return a;
}

Delta operator*( const Real &c, const Delta &a )
{
    if( !( a.isInf( ) ) )
        return Delta( c * a.R( ), c * a.D( ) );
    else
    {
        Delta res = a;
        if (c < 0) {
            res.negate();
        }
        return res;
    }
}

Delta operator*( const Delta &a, const Real &c )
{
    return c * a;
}

Delta operator/( const Delta &a, const Real &c )
{
    if( !( a.isInf( ) ) )
        return Delta( a.R( ) / c, a.D( ) / c );
    else
        return a;
}

// Comparison operators definitions.
// Most are implemented via calls to basic operators.
//
bool operator<( const Delta &a, const Delta &b )
{
    if( a.isPlusInf( ) || b.isMinusInf( ) )
        return false;
    if (a.isMinusInf( ) || b.isPlusInf( ) || a.R() < b.R() || (a.R() == b.R() && a.D() < b.D()))
        return true;
    else
        return false;
//
//  if( a.isPlusInf( ) )
//    return false;
//  else if( b.isMinusInf( ) )
//    return false;
//  else if( a.isMinusInf( ) )
//    return true;
//  else if( b.isPlusInf( ) )
//    return true;
//  else if( a.R( ) < b.R( ) )
//    return true;
//  else if( a.R( ) == b.R( ) && a.D( ) < b.D( ) )
//    return true;
//  else
//    return false;
}

bool operator<=( const Delta &a, const Delta &b )
{
    return !( b < a );
}

bool operator>( const Delta &a, const Delta &b )
{
    return b < a;
}

bool operator>=( const Delta &a, const Delta &b )
{
    return !( a < b );
}

bool operator==( const Delta &a, const Delta &b )
{
    if( (a.isInf( ) ^ b.isInf( ))
     || (a.isPlusInf( ) && b.isMinusInf( ))
     || (b.isPlusInf( ) && a.isMinusInf( )) )
        return false;
    else if(( a.isPlusInf( ) && b.isPlusInf( ) )
        || ( a.isMinusInf( ) && b.isMinusInf( ) )
        || ( a.R( ) == b.R( ) && a.D( ) == b.D( ) ))
        return true;
    else
        return false;
}

bool operator!=( const Delta &a, const Delta &b )
{
    return !(a == b);
}

bool operator<( const Delta &a, const Real &c )
{
    return a.isLess( c );
}

bool operator<=( const Delta &a, const Real &c )
{
    return !( a > c );
}

bool operator>( const Delta &a, const Real &c )
{
    return a.isGreater( c );
}

bool operator>=( const Delta &a, const Real &c )
{
    return !( a < c );
}

bool operator<( const Real &c, const Delta &a )
{
    return a > c;
}

bool operator<=( const Real &c, const Delta &a )
{
    return a >= c;
}

bool operator>( const Real &c, const Delta &a )
{
    return a < c;
}

bool operator>=( const Real &c, const Delta &a )
{
    return a <= c;
}

//
// basic function to use in comparison with Real
//
bool Delta::isLess( const Real &c ) const
{
    if( isPlusInf( ) )
        return false;
    else if( isMinusInf( ) )
        return true;
    else if( R( ) < c )
        return true;
    else if( R( ) == c && D( ) < 0 )
        return true;
    else
        return false;
}

//
// basic function to use in comparison with Real
//
bool Delta::isGreater( const Real &c ) const
{
    if( isMinusInf( ) )
        return false;
    else if( isPlusInf( ) )
        return true;
    else if( R( ) > c )
        return true;
    else if( R( ) == c && D( ) > 0 )
        return true;
    else
        return false;
}

Delta::Delta() : infinite{false}, positive{false}, r{0}, d{0} {}

//
// Default constructor (true for +inf; false for -inf)
//
Delta::Delta( deltaType p ) : infinite {p!=ZERO}, positive {p == UPPER}, r{0}, d{0} {}

//
// Constructor for Real delta
//
Delta::Delta( const Real &v ) : infinite{false}, positive{false}, r{v}, d{0} {}


//
// Constructor for Real delta with strict bit
//
Delta::Delta( const Real &v_r, const Real &v_d ) : infinite{false}, positive{false}, r{v_r}, d{v_d} {}


//
// Copy constructor
//
Delta::Delta( const Delta &a ) : infinite {a.infinite}, positive {a.positive}, r{a.r}, d{a.d} {}


// Assign operator
Delta& Delta::operator=( const Delta &a )
{
    if ( this != &a )
    {
        infinite = a.infinite;
        positive = a.positive;
        if ( !( infinite ) )
        {
            r = a.r;
            d = a.d;
        }
    }
    return *this;
}

// move constructor
Delta::Delta(Delta && other) = default;

// move constructor from real
Delta::Delta(Real && other) : infinite{false}, positive {false}, r{std::move(other)}, d{0}{ }

// move assign
Delta & Delta::operator=(Delta && other) noexcept {
    std::swap(this->infinite, other.infinite);
    std::swap(this->positive, other.positive);
    this->r = std::move(other.r);
    this->d = std::move(other.d);
    return *this;
}

// Destructor
Delta::~Delta( ) = default;

static Delta Delta_PlusInf  = Delta(Delta::UPPER);
static Delta Delta_MinusInf = Delta(Delta::LOWER);

#endif
