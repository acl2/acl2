// ESIM Symbolic Hardware Simulator
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
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

