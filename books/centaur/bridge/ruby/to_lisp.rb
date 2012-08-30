#!/usr/bin/env ruby

# Copyright (C) 2012 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
#
# Original author: Jared Davis <jared@centtech.com>


# This adds .to_lisp() to integers, strings, arrays.  The .to_lisp method
# always produces a string.  The intent is that this string can be given to a
# Lisp parser to get a basic Lisp version of the Ruby object.

class NilClass

  def to_lisp
    return "NIL"
  end

end


class Integer

  def to_lisp
    return self.to_s();
  end

end


class String

  def to_lisp
    ret = "\""
    self.each_char { |c|
      if c == "\\"
        ret << "\\\\"
      elsif c == "\""
        ret << "\\\""
      else
        ret << c
      end
    }
    ret << "\""
    return ret
  end

end


class Array

  def to_lisp
    ret = "("
    nchars = 0
    last = self.length
    self.each_with_index { |s,i|

      slisp = s.to_lisp
      nchars = nchars + slisp.length
      ret << slisp

      # Use spaces to separate elements, but not after the last element.
      break if (i == last - 1)

      if (nchars > 75)
        ret << "\n"
        nchars = 0
      else
        ret << " "
      end
    }
    ret << ")"
    return ret
  end

end


class Hash

  def to_lisp
    ret = "("
    nchars = 0
    keys = self.keys
    last = keys.length

    keys.each_with_index { |k,i|
      klisp = k.to_lisp
      vlisp = self.fetch(k).to_lisp
      nchars = nchars + klisp.length + vlisp.length + 5   # to account for "(", " . ", and ")"
      ret << "("
      ret << klisp
      ret << " . "
      ret << vlisp
      ret << ")"

      # Use spaces to separate elements, but not after the last element.
      break if (i == last - 1)
      if (nchars > 75)
        ret << "\n"
        nchars = 0
      else
        ret << " "
      end
    }
    ret << ")"
    return ret
  end

end
