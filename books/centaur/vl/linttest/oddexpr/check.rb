#!/usr/bin/env ruby

# VL Verilog Toolkit
# Copyright (C) 2008-2015 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
#
# Original author: Jared Davis <jared@centtech.com>

require 'require_relative' if RUBY_VERSION =~ /1\.8/
require_relative '../utils'

outlaw_bad_warnings()

def fine(modname, wirename)
  outlaw_warning(modname, "VL-WARN-ODDEXPR", wirename)
end

def warn(modname, wirename)
  match_warning(modname, "VL-WARN-ODDEXPR", wirename)
end

fine(:m0, "xxplus1")
fine(:m0, "xxplus2")
warn(:m0, "xxplus3")
fine(:m0, "xxplus4")
fine(:m0, "xxplus5")
warn(:m0, "xxplus6")
warn(:m0, "xxplus7")
warn(:m0, "xxplus8")
warn(:m0, "xxplus9")
warn(:m0, "xxplusA")

fine(:m0, "xxminus1")  # I've gone back and forth on this.  I think we don't want to warn.
fine(:m0, "xxminus2")
warn(:m0, "xxminus3")
fine(:m0, "xxminus4")
fine(:m0, "xxminus5")
warn(:m0, "xxminus6")
warn(:m0, "xxminus7")
warn(:m0, "xxminus8")
warn(:m0, "xxminus9")
warn(:m0, "xxminusA")

warn(:m0, "xxshl1")
warn(:m0, "xxshl2")
warn(:m0, "xxshl3")
fine(:m0, "xxshl4")
fine(:m0, "xxshl5")
warn(:m0, "xxshl6")
warn(:m0, "xxshl7")
warn(:m0, "xxshl8")
warn(:m0, "xxshl9")
warn(:m0, "xxshlA")

warn(:m0, "xxshr1")
warn(:m0, "xxshr2")
warn(:m0, "xxshr3")
fine(:m0, "xxshr4")
fine(:m0, "xxshr5")
warn(:m0, "xxshr6")
warn(:m0, "xxshr7")
warn(:m0, "xxshr8")
warn(:m0, "xxshr9")
warn(:m0, "xxshrA")


fine(:m0, "xxlt1")
fine(:m0, "xxlt2")
fine(:m0, "xxlt3")
warn(:m0, "xxlt4")
warn(:m0, "xxlt5")
fine(:m0, "xxlt6")
fine(:m0, "xxlt7")
fine(:m0, "xxlt8")
fine(:m0, "xxlt9")
fine(:m0, "xxltA")


fine(:m0, "yylt1")
fine(:m0, "yylt2")
fine(:m0, "yylt3")
warn(:m0, "yylt4")
warn(:m0, "yylt5")
warn(:m0, "yylt6")
warn(:m0, "yylt7")
warn(:m0, "yylt8")
fine(:m0, "yylt9")
fine(:m0, "yyltA")


fine(:m0, "xxeq1")
fine(:m0, "xxeq2")
fine(:m0, "xxeq3")
warn(:m0, "xxeq4")
warn(:m0, "xxeq5")
fine(:m0, "xxeq6")
warn(:m0, "xxeq7")
fine(:m0, "xxeq8")
fine(:m0, "xxeq9")
fine(:m0, "xxeqA")

fine(:m0, "yyeq1")
fine(:m0, "yyeq2")
fine(:m0, "yyeq3")
warn(:m0, "yyeq4")
warn(:m0, "yyeq5")
warn(:m0, "yyeq6")
warn(:m0, "yyeq7")
warn(:m0, "yyeq8")
fine(:m0, "yyeq9")
fine(:m0, "yyeqA")


warn(:m0, "xxand1")
warn(:m0, "xxand2")
warn(:m0, "xxand3")
fine(:m0, "xxand4")
fine(:m0, "xxand5")
fine(:m0, "xxand6")
warn(:m0, "xxand7")
fine(:m0, "xxand8")
#warn(:m0, "xxand9")
#warn(:m0, "xxandA")


warn(:m0, "yyand1")
warn(:m0, "yyand2")
warn(:m0, "yyand3")
warn(:m0, "yyand4")
warn(:m0, "yyand5")
fine(:m0, "yyand6")
warn(:m0, "yyand7")
fine(:m0, "yyand8")
#warn(:m0, "yyand9")
#warn(:m0, "yyandA")



test_passed()





# Improve oddexpr check:

# We should be able to filter these out easily:  Comparison that obviously
# you intend to have (A >= B) & (B >= C) precedence.

#     - :CHECK-TYPE: a >= b & b >= c

# And these: comparisons where you are checking the same LHS against
# several RHSes:

#     - :CHECK-TYPE: freshSym[i] == mem[r].a | freshSym[i] == mem[r].b

# And maaaybe these?  If you're comparing something to a constant and
# anding it with something, that seems probably OK?

#      - :CHECK-TYPE: ccRBRetPtrEnc_C == 32'd0 & ccRBxRetVld_P[0]
#      - :CHECK-TYPE: ccRBRetPtrEnc_C == 32'd1 & ccRBxRetVld_P[1]

# It should also mergesort the things:

#      - :CHECK-PRECEDENCE: PASZ - 12 + 1
#      - :CHECK-PRECEDENCE: PASZ - 12 + 1
#      - :CHECK-PRECEDENCE: PASZ - 12 + 1
#      - :CHECK-PRECEDENCE: PASZ - 12 + 1
#      - :CHECK-PRECEDENCE: PASZ - 12 + 1

# Another really dumb heuristic might be, for things like this:

#      - :CHECK-TYPE: TpA_Descr_TB.Addr.tag == leAddr.tag | ForceIdxCompare_TpA_TB

# Are the left and right sides of the == sort of vaguely similar in name?
# If so maybe there's no problem.  Actually an "Are the last name components
# identical" check might be really pretty reasonable.


# These look really valuable:

#      - :CHECK-TYPE: leValid[0] & 0 == ExtLoad_DataDoneId

# Maybe this can be higher priority because you'd generally write it the
# flipped around way.  Ah, well, it does look right after all.

# This is probably never an error, i.e., ``1 << xx'' is almost surely intended.

#      - :CHECK-PRECEDENCE: lePushValidsPerReq[1] | 1'd1 << L1dLoad_Reqs[0].Id

# Or maybe there just should be some type checking here... like for instance: if
# it's an AND of LHS & (B == C), where B and C are the same width but not zero
# width, or maybe a special case for integers also, and LHS is one bit, then
# probably you know what the hell you're doing.
