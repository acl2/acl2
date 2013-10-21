// ESIM Symbolic Hardware Simulator
// Copyright (C) 2010-2013 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// This program is free software; you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation; either version 2 of the License, or (at your option) any later
// version.  This program is distributed in the hope that it will be useful but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
// more details.  You should have received a copy of the GNU General Public
// License along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
//
// fourval.h -- Arbitrary (but fixed) width four-valued integer type
//
// Original authors: Nikhil Patil <npatil@centtech.com>
//                   Jared Davis <jared@centtech.com>

#pragma once
#include "bits.h"
#include <iostream>

// We use a simple onset/offset encoding:
//
//   ONSET    OFFSET     VALUE
// -------------------------------
//     1        1          X
//     1        0          1
//     0        1          0
//     0        0          Z
// -------------------------------

template <unsigned N>
class fourval {
public:

    bit<N> onset;
    bit<N> offset;

    // Default constructor initializes the value to all good, Boolean zeros.
    fourval<N>()
	: onset(bit<N>::zero()),
	  offset(~bit<N>::zero())
    {}

    // Promotion from bit<N> into a pure Boolean fourval<N>
    explicit fourval<N>(bit<N> on)
	: onset(on),
	  offset(~on)
    {}

    // Explicit construction of fourval<N> with control over onset/offset
    explicit fourval<N>(bit<N> on, bit<N> off)
      : onset(on),
        offset(off)
    {}


    // Some useful fourval<N> constructors for all 0s, 1s, Xes, Zs.

    static fourval<N> all_0() {
	return fourval<N>(bit<N>::zero(), ~bit<N>::zero());
    }

    static fourval<N> all_1() {
	return fourval<N>(~bit<N>::zero(), bit<N>::zero());
    }

    static fourval<N> all_X() {
	return fourval<N>(~bit<N>::zero(), ~bit<N>::zero());
    }

    static fourval<N> all_Z() {
	return fourval<N>(bit<N>::zero(), bit<N>::zero());
    }


    bool isPureBoolean() const {
	// Returns true iff every bit is 1 or 0---that is, if no bit
	// anywhere is ever X or Z.
	return onset == ~offset;
    }

    bit<N> pureBooleanMask() const {
	// Returns an N-bit mask, where mask[i] == 1 exactly when the ith
	// bit is Boolean-valued, i.e., not X or Z.
	return onset ^ offset;
    }


    // Some basic operators.  BOZO, it would probably be convenient to
    // have many additional operators, e.g., +, -, *, &, etc., perhaps
    // with Verilog semantics for X handling.

    bool operator ==(const fourval<N> &that) const {
	return onset == that.onset
    	    && offset == that.offset;
    }

    bool operator !=(const fourval<N> &that) const {
        return !(*this == that);
    }
};

template<unsigned N>
std::ostream& operator<< (std::ostream& stream, const fourval<N>& x)
{
    stream << N << "'b";
    unsigned i = N;
    while(i)
    {
	--i;
	bool on = x.onset.getBit(i);
	bool off = x.offset.getBit(i);
	char c = (on && off) ? 'X'
	       : (on && !off) ? '1'
	       : (!on && off) ? '0'
	       : 'Z';
	stream << c;
    }
    return stream;
}

