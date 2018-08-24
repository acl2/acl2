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

require 'oj'

# Warning file loading -------------------------------------------------

def read_whole_file(filename)
  file = File.open(filename)
  text = file.read
  file.close
  return text
end

def read_json_file(filename)
  ret = Oj.load(read_whole_file(filename), :symbol_keys=>true)
  return ret
end

def check_warning_syntax(w)
  raise "Warning isn't even a hash: #{w}" unless w.kind_of?(Hash)
  raise "Bad tag on warning: #{w}" unless w[:tag] == "warning"
  raise "Bad warning type on #{w}" unless w[:type].kind_of?(String)
  raise "Bad text on #{w}" unless w[:text].kind_of?(String)
end

def check_warning_list_syntax(wlist)
  wlist.each { |w| check_warning_syntax(w) }
end

def check_json_file(data)
  raise "Data file isn't even a hash" unless data.kind_of?(Hash)
  raise "Data file has no :warnings" unless data.has_key?(:warnings)
  raise "Data file has no :locations" unless data.has_key?(:locations)
  warnings = data[:warnings]
  raise "Warnings aren't a hash" unless warnings.kind_of?(Hash)
  warnings.each do |modname, wlist|
    raise "Modname isn't a symbol: #{modname}" unless modname.kind_of?(Symbol)
    check_warning_list_syntax(wlist)
  end
  locations = data[:locations]
  locations.each do |modname, loc|
    raise "Modname isn't a symbol: #{modname}" unless modname.kind_of?(Symbol)
  end
end

raise "vl-warnings.json does not exist" unless File.exists?("vl-warnings.json")
ans = read_json_file("vl-warnings.json")
check_json_file(ans)
WARNINGS = ans[:warnings]
LOCATIONS = ans[:locations]

def flat_global_warnings()
  ret = []
  WARNINGS.each do |modname, wlist|
    ret.concat(wlist)
  end
  return ret
end

FLAT_WARNINGS = flat_global_warnings()


# Convenience functions for check.rb scripts ---------------------------------

def test_passed()
  File.open("vl-warnings.ok", "w") { |file|
    file.write("Test successful.")
  }
end

def assert(condition)
  raise "Assertion failed" unless condition
end

def some_warning_matches(type, substring, wlist)
  wlist.each do |w|
    if ((type == "*" or w[:type] == type) and
        (substring == "*" or w[:text].include?(substring)))
      return w
    end
  end
  return false
end

def match_warning(mod, type, substring)
  raise "Invalid description name: #{mod}" unless WARNINGS.has_key?(mod) or LOCATIONS.has_key?(mod)
  wlist = WARNINGS[mod] || []
  ok = some_warning_matches(type, substring, wlist)
  if ok
    puts "#{mod}: OK: matched #{type}, #{substring}"
  else
    raise "ERROR: failed to match required warning: #{mod}, #{type}, #{substring}"
  end
end

def outlaw_warning(mod, type, substring)
  raise "Invalid description name: #{mod}" unless WARNINGS.has_key?(mod) or LOCATIONS.has_key?(mod)
  wlist = WARNINGS[mod] || []
  found = some_warning_matches(type, substring, wlist)
  if found
    raise "ERROR: found outlawed warning: #{mod}, #{type}, #{substring}:\n     #{found[:type]} -- #{found[:text]}"
  else
    puts "#{mod}: OK: none match #{type}, #{substring}"
  end
end

def outlaw_warning_global(type)
  FLAT_WARNINGS.each { |w|
    if (w[:type] == type)
      raise "Found outlawed global warning #{w[:type]} (from #{w[:fn]}) -- #{w[:text]}"
    end
  }
end

def outlaw_bad_warnings()
  outlaw_warning_global("VL-PARSE-ERROR")
  outlaw_warning_global("VL-PARSE-FAILED")
  outlaw_warning_global("VL-BAD-MODULE-ITEM")
  outlaw_warning_global("VL-NAMESPACE-ERROR")
  outlaw_warning_global("VL-BAD-VARIABLES")
  outlaw_warning_global("VL-BAD-INSTANCE")
  outlaw_warning_global("VL-TRICKY-SCOPE")
end


# -----------------------------------------------------------------------------

# Alternatives to the above, where you can give a substring of the type, e.g.,
# using these with "VL-LUCID-UNSET" will match "VL-LUCID-UNSET" and also
# "VL-LUCID-UNSET-VARIABLE", etc.

def some_warning_matches_ss(type_substring, substring, wlist)
  wlist.each do |w|
    if ((type_substring == "*" or w[:type].include?(type_substring)) and
        (substring == "*" or w[:text].include?(substring)))
      return w
    end
  end
  return false
end

def match_warning_ss(mod, type_substring, substring)
  raise "Invalid description name: #{mod}" unless WARNINGS.has_key?(mod) or LOCATIONS.has_key?(mod)
  wlist = WARNINGS[mod] || []
  ok = some_warning_matches_ss(type_substring, substring, wlist)
  if ok
    puts "#{mod}: OK: matched #{type_substring}, #{substring}"
  else
    raise "ERROR: failed to match required warning: #{mod}, #{type_substring}, #{substring}"
  end
end

def outlaw_warning_ss(mod, type_substring, substring)
  raise "Invalid description name: #{mod}" unless WARNINGS.has_key?(mod) or LOCATIONS.has_key?(mod)
  wlist = WARNINGS[mod] || []
  found = some_warning_matches_ss(type_substring, substring, wlist)
  if found
    raise "ERROR: found outlawed warning: #{mod}, #{type_substring}, #{substring}:\n     #{found[:type]} -- #{found[:text]}"
  else
    puts "#{mod}: OK: none match #{type_substring}, #{substring}"
  end
end



