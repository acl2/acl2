#!/usr/bin/env ruby

# Copyright (C) 2012 Centaur Technology
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
