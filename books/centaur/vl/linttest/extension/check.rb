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

def find_major_extension_warning(substring)
  raise "No warnings for top" unless WARNINGS.has_key?(:top)
  wlist = WARNINGS[:top]
  wlist.each do |w|
    if ((w[:type].include?("VL-WARN-EXTENSION")) and
        (not w[:type].include?("MINOR")) and
        (w[:text].include?(substring)))
      return w
    end
  end
  return false
end

def find_minor_extension_warning(substring)
  raise "No warnings for top" unless WARNINGS.has_key?(:top)
  wlist = WARNINGS[:top]
  wlist.each do |w|
    if ((w[:type].include?("VL-WARN-EXTENSION")) and
        (w[:type].include?("MINOR")) and
        (w[:text].include?(substring)))
      return w
    end
  end
  return false
end

def major(substring)

  major = find_major_extension_warning(substring)
  if (major)
    puts "OK: #{substring}: found major extension warning: #{major[:type]}"
  else
    raise "FAIL: #{substring}: no major extension warning"
  end

  minor = find_minor_extension_warning(substring)
  if (minor)
    raise "FAIL: extension warning for #{substring} is minor instead of major:\n         #{minor[:type]} -- #{minor[:text]}"
  else
    puts "OK: #{substring}: no minor extension warning"
  end

end

def normal(substring)

  major = find_major_extension_warning(substring)
  if (major)
    raise "FAIL: #{substring}: unexpected major extension warning:\n     #{major[:type]} -- #{major[:text]}"
  else
    puts "OK: #{substring}: no major extension warnings"
  end

  minor = find_minor_extension_warning(substring)
  if (minor)
    raise "FAIL: #{substring}: unexpected minor extension warning:\n     #{minor[:type]} -- #{minor[:text]}"
  else
    puts "OK: #{substring}: no minor extension warnings"
  end

end

def minor(substring)

  major = find_major_extension_warning(substring)
  if (major)
    raise "FAIL: #{substring}: unexpected major extension warning:\n     #{major[:type]} -- #{major[:text]}"
  else
    puts "OK: #{substring}: no major extension warnings"
  end

  minor = find_minor_extension_warning(substring)
  if (minor)
    puts "OK: #{substring}: found minor extension warning: #{minor[:type]}"
  else
    raise "FAIL: #{substring}: no minor extension warning"
  end

end


normal("as_normal1")
normal("as_normal2")
normal("as_normal3")
normal("as_normal4")
normal("as_normal5")
normal("as_normal6")

major("as_warn1")
major("as_warn2")
major("as_warn3")



test_passed()



