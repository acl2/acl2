#!/usr/bin/env ruby

# VL Verilog Toolkit
# Copyright (C) 2008-2014 Centaur Technology
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
outlaw_warning_global("VL-PROGRAMMING-ERROR")

def find_major_fussy_warning(substring)
  raise "No warnings for top" unless WARNINGS.has_key?(:top)
  wlist = WARNINGS[:top]
  wlist.each do |w|
    if ((w[:type].include?("VL-FUSSY")) and
        (not w[:type].include?("MINOR")) and
        (w[:text].include?(substring)))
      return w
    end
  end
  return false
end

def find_minor_fussy_warning(substring)
  raise "No warnings for top" unless WARNINGS.has_key?(:top)
  wlist = WARNINGS[:top]
  wlist.each do |w|
    if ((w[:type].include?("VL-FUSSY")) and
        (w[:type].include?("MINOR")) and
        (w[:text].include?(substring)))
      return w
    end
  end
  return false
end

def fuss(substring)

  major = find_major_fussy_warning(substring)
  if (major)
    puts "OK: #{substring}: found major fussy warning: #{major[:type]}"
  else
    raise "FAIL: #{substring}: no major fussy warning"
  end

  minor = find_minor_fussy_warning(substring)
  if (minor)
    raise "FAIL: fussy warning for #{substring} is minor instead of major:\n         #{major[:type]} -- #{major[:text]}"
  else
    puts "OK: #{substring}: no minor fussy warning"
  end

end

def normal(substring)

  major = find_major_fussy_warning(substring)
  if (major)
    raise "FAIL: #{substring}: unexpected major fussy warning:\n     #{major[:type]} -- #{major[:text]}"
  else
    puts "OK: #{substring}: no major fussy warnings"
  end

  minor = find_minor_fussy_warning(substring)
  if (minor)
    raise "FAIL: #{substring}: unexpected minor fussy warning:\n     #{minor[:type]} -- #{minor[:text]}"
  else
    puts "OK: #{substring}: no minor fussy warnings"
  end

end

def minor(substring)

  major = find_major_fussy_warning(substring)
  if (major)
    raise "FAIL: #{substring}: unexpected major fussy warning:\n     #{major[:type]} -- #{major[:text]}"
  else
    puts "OK: #{substring}: no major fussy warnings"
  end

  minor = find_minor_fussy_warning(substring)
  if (minor)
    puts "OK: #{substring}: found minor fussy warning: #{minor[:type]}"
  else
    raise "FAIL: #{substring}: no minor fussy warning"
  end

end


fuss("and_warn1")
fuss("and_warn2")
fuss("and_warn3")
fuss("and_warn4")
fuss("and_warn5")

normal("and_normal1")
normal("and_normal2")
normal("and_normal3")
normal("and_normal4")

normal("andc_normal1")
normal("andc_normal2")
normal("andc_normal3")

fuss("andc_warn1")
fuss("andc_warn2")
fuss("andc_warn3")
fuss("andc_warn4")

minor("andc_minor1")
minor("andc_minor2")

normal("lt_normal1")
normal("lt_normal2")
normal("lt_normal3")

fuss("lt_warn1")
fuss("lt_warn2")

minor("ltc_minor1")
minor("ltc_minor2")


normal("cond_normal1")
normal("cond_normal2")
normal("cond_normal3")
normal("cond_normal4")

fuss("cond_warn1")
fuss("cond_warn2")
fuss("cond_warn3")

test_passed()



