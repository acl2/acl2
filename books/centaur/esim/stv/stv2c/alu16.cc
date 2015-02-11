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
// alu16.cc -- Test bench of the C++ code for the alu16 module
//
// Original author: Jared Davis <jared@centtech.com>

#include "alu16_test.h"
#include <iostream>
using namespace std;

#define VERBOSE 0

// This is a test bench to see if our C++ translation of alu16.v seems to be
// correct.  I don't bother to test the COUNT operation because it has a "bug"
// that I don't want to reimplement.

static const uint8_t OP_PLUS = 0;
static const uint8_t OP_MINUS = 1;
static const uint8_t OP_BITAND = 2;
static const uint8_t OP_BITOR = 3;
static const uint8_t OP_BITXOR = 4;
static const uint8_t OP_MIN = 5;
static const uint8_t OP_COUNT = 6;
static const uint8_t OP_MULT = 7;

bool check_all(const fourval<16>& a, const fourval<16>& b);

fourval<16> plus_spec(const fourval<16>& a, const fourval<16>& b);
fourval<16> minus_spec(const fourval<16>& a, const fourval<16>& b);
fourval<16> bitand_spec(const fourval<16>& a, const fourval<16>& b);
fourval<16> bitor_spec(const fourval<16>& a, const fourval<16>& b);
fourval<16> bitxor_spec(const fourval<16>& a, const fourval<16>& b);
fourval<16> min_spec(const fourval<16>& a, const fourval<16>& b);
fourval<16> mult_spec(const fourval<16>& a, const fourval<16>& b);

int main()
{
    bool ok = true;

    uint16_t stop = VERBOSE ? 100 : 10000;

    cout << "-- Pure Boolean checks --" << endl;
    for(uint16_t i = 0; i < stop; ++i)
    {
	if (VERBOSE) { cout << endl; }
	uint16_t rand1 = rand();
	uint16_t rand2 = rand();
	fourval<16> a = fourval<16>(rand1);
	fourval<16> b = fourval<16>(rand2);
	if (VERBOSE) { cout << "A is " << a << endl; }
	if (VERBOSE) { cout << "B is " << b << endl; }
	ok &= check_all(a,b);
    }

    cout << "-- Pure random onset/offset checks --" << endl;
    for(uint16_t i = 0; i < stop; ++i)
    {
	if (VERBOSE) { cout << endl; }
	uint16_t rand1 = rand();
	uint16_t rand2 = rand();
	uint16_t rand3 = rand();
	uint16_t rand4 = rand();
	fourval<16> a = fourval<16>(rand1, rand2);
	fourval<16> b = fourval<16>(rand3, rand4);
	if (VERBOSE) { cout << "A is " << a << endl; }
	if (VERBOSE) { cout << "B is " << b << endl; }
	ok &= check_all(a,b);
    }

    cout << "-- Almost pure-Boolean checks. --" << endl;
    for(uint16_t i = 0; i < stop; ++i)
    {
	if (VERBOSE) { cout << endl; }
	uint16_t rand1 = rand();
	uint16_t rand2 = rand();
	fourval<16> a = fourval<16>(rand1);
	fourval<16> b = fourval<16>(rand2);
	if (i % 2) {
	    uint16_t place = i % 16;
	    b.onset.cpyBit(place, b.offset.getBit(place));
	}
	else {
	    uint16_t place = i % 16;
	    b.offset.cpyBit(place, b.onset.getBit(place));
	}
	if (VERBOSE) { cout << "A is " << a << endl; }
	if (VERBOSE) { cout << "B is " << b << endl; }
	ok &= check_all(a,b);
    }

    if (ok) {
	cout << "Checks passed." << endl;
	exit(0);
    }
    else {
	cout << "Checks failed." << endl;
	exit(1);
    }
}

bool check_all(const fourval<16>& a, const fourval<16>& b)
{
    bool ok = true;

    alu16_test_ins in;
    alu16_test_outs out;
    fourval<16> spec;
    in.a = a;
    in.b = b;

    in.op = fourval<3>(OP_PLUS);
    alu16_test_run(in, out);
    spec = plus_spec(a,b);
    if (VERBOSE) { cout << "+    " << out.res << endl; }
    if (out.res != spec) {
	cout << "Mismatch for plus(" << a << ", " << b << "): "
	     << out.res << " vs. " << spec << endl;
	ok = false;
    }

    in.op = fourval<3>(OP_MINUS);
    alu16_test_run(in, out);
    spec = minus_spec(a,b);
    if (VERBOSE) { cout << "-    " << out.res << endl; }
    if (out.res != spec) {
	cout << "Mismatch for minus(" << a << ", " << b << "): "
	     << out.res << " vs. " << spec << endl;
	ok = false;
    }

    in.op = fourval<3>(OP_BITAND);
    alu16_test_run(in, out);
    spec = bitand_spec(a,b);
    if (VERBOSE) { cout << "&    " << out.res << endl; }
    if (out.res != spec) {
	cout << "Mismatch for bitand(" << a << ", " << b << "): "
	     << out.res << " vs. " << spec << endl;
	ok = false;
    }

    in.op = fourval<3>(OP_BITOR);
    alu16_test_run(in, out);
    spec = bitor_spec(a,b);
    if (VERBOSE) { cout << "|    " << out.res << endl; }
    if (out.res != spec) {
	cout << "Mismatch for bitor(" << a << ", " << b << "): "
	     << out.res << " vs. " << spec << endl;
	ok = false;
    }

    in.op = fourval<3>(OP_BITXOR);
    alu16_test_run(in, out);
    spec = bitxor_spec(a,b);
    if (VERBOSE) { cout << "^    " << out.res << endl; }
    if (out.res != spec) {
	cout << "Mismatch for bitxor(" << a << ", " << b << "): "
	     << out.res << " vs. " << spec << endl;
	ok = false;
    }

    in.op = fourval<3>(OP_MIN);
    alu16_test_run(in, out);
    spec = min_spec(a,b);
    if (VERBOSE) { cout << "^    " << out.res << endl; }
    if (out.res != spec) {
	cout << "Mismatch for min(" << a << ", " << b << "): "
	     << out.res << " vs. " << spec << endl;
	ok = false;
    }

    in.op = fourval<3>(OP_MULT);
    alu16_test_run(in, out);
    spec = mult_spec(a,b);
    if (VERBOSE) { cout << "*    " << out.res << endl; }
    if (out.res != mult_spec(a,b)) {
	cout << "Mismatch for mult(" << a << ", " << b << "): "
	     << out.res << " vs. " << spec << endl;
	ok = false;
    }

    return ok;
}

fourval<16> plus_spec(const fourval<16>& a, const fourval<16>& b)
{
    if (a.isPureBoolean() && b.isPureBoolean())
    {
	const bit<16>& aval = a.onset;
	const bit<16>& bval = b.onset;
	const bit<16> ans = aval + bval;
	return fourval<16>(ans);
    }
    else
    {
	return fourval<16>::all_X();
    }
}

fourval<16> minus_spec(const fourval<16>& a, const fourval<16>& b)
{
    if (a.isPureBoolean() && b.isPureBoolean())
    {
	const bit<16>& aval = a.onset;
	const bit<16>& bval = b.onset;
	const bit<16> ans = aval - bval;
	return fourval<16>(ans);
    }
    else
    {
	return fourval<16>::all_X();
    }
}

fourval<16> bitand_spec(const fourval<16>& a, const fourval<16>& b)
{
    fourval<16> ans;
    for(int i = 0;i < 16;++i) {
	bool a1 = a.onset.getBit(i);
	bool a0 = a.offset.getBit(i);
	bool b1 = b.onset.getBit(i);
	bool b0 = b.offset.getBit(i);
	bool ans1;
	bool ans0;
	if (!a1 && a0) { // A is false, so it's false
	    ans1 = false;
	    ans0 = true;
	}
	else if (!b1 && b0) { // B is false, so it's false
	    ans1 = false;
	    ans0 = true;
	}
	else if (a1 && !a0 && b1 && !b0) { // Both are 1, so it's true
	    ans1 = true;
	    ans0 = false;
	}
	else { // else X
	    ans1 = true;
	    ans0 = true;
	}
	ans.onset.cpyBit(i, ans1);
	ans.offset.cpyBit(i, ans0);
    }
    return ans;
}

fourval<16> bitor_spec(const fourval<16>& a, const fourval<16>& b)
{
    fourval<16> ans;
    for(int i = 0;i < 16;++i) {
	bool a1 = a.onset.getBit(i);
	bool a0 = a.offset.getBit(i);
	bool b1 = b.onset.getBit(i);
	bool b0 = b.offset.getBit(i);
	bool ans1;
	bool ans0;
	if (a1 && !a0) { // A is true, so it's true
	    ans1 = true;
	    ans0 = false;
	}
	else if (b1 && !b0) { // B is true, so it's true
	    ans1 = true;
	    ans0 = false;
	}
	else if (!a1 && a0 && !b1 && b0) { // Both are 0, so it's false
	    ans1 = false;
	    ans0 = true;
	}
	else { // else X
	    ans1 = true;
	    ans0 = true;
	}
	ans.onset.cpyBit(i, ans1);
	ans.offset.cpyBit(i, ans0);
    }
    return ans;
}

fourval<16> bitxor_spec(const fourval<16>& a, const fourval<16>& b)
{
    fourval<16> ans;
    for(int i = 0;i < 16;++i) {
	bool a1 = a.onset.getBit(i);
	bool a0 = a.offset.getBit(i);
	bool b1 = b.onset.getBit(i);
	bool b0 = b.offset.getBit(i);
	bool ans1;
	bool ans0;
	if (a1 != a0 && b1 != b0) { // Good boolean values
	    ans1 = a1 != b1;
	    ans0 = a1 == b1;
	}
	else { // Anything else is X.
	    ans1 = true;
	    ans0 = true;
	}
	ans.onset.cpyBit(i, ans1);
	ans.offset.cpyBit(i, ans0);
    }
    return ans;
}

fourval<16> min_spec(const fourval<16>& a, const fourval<16>& b)
{
    // The alu16.v definition is (abus < bbus) ? abus : bbus.  Per Verilog
    // semantics, the comparison operator yields X if either operand has any X
    // bit.  In that case, the ?: operator semantics are that we merge any bits
    // that agree on good Boolean values.  But VL uses (by default) a more
    // conservative semantics, where X ? a : b always returns Xes.

    if (a.isPureBoolean() && b.isPureBoolean())
    {
	const bit<16>& aval = a.onset;
	const bit<16>& bval = b.onset;
	const bit<16> ans = aval < bval ? aval : bval;
	return fourval<16>(ans);
    }
    else
    {
	return fourval<16>::all_X();
    }
}

fourval<16> mult_spec(const fourval<16>& a, const fourval<16>& b)
{
    if (a.isPureBoolean() && b.isPureBoolean())
    {
	uint16_t aval = (uint16_t)a.onset;
	uint16_t bval = (uint16_t)b.onset;
	uint16_t ans = aval * bval;
	return fourval<16>(ans);
    }
    else
    {
	return fourval<16>::all_X();
    }
}
