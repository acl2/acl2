#!/usr/bin/env ruby

# VL Lint Parse Error Check
# Copyright (C) 2016 Apple, Inc.
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
# Original author: Jared Davis

require 'require_relative'
require_relative '../utils'

# Make sure that we get the parse error reported for m0
match_warning(:m0, "VL-PARSE-ERROR", "")

# Make sure that we still process m1 even though it comes after a module with a parse error
match_warning_ss(:m1, "VL-LUCID-SPURIOUS", "some_spurious_wire")

# Make sure we get a parse error reported for m2
# This was previously failing because elaboration would end up throwing away module m2.
match_warning(:m2, "VL-PARSE-ERROR", "")

# Make sure we still process m3 even though it comes after and instantiates a module with a parse error
match_warning_ss(:m3, "VL-LUCID-SPURIOUS", "another_spurious_wire")

outlaw_warning(:m4, "VL-PARSE-ERROR", "")

test_passed()
