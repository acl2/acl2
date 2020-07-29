; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "ihsext-basics"))
(local (include-book "std/testing/assert-bang" :dir :system))

(defsection bitops/part-select
  :parents (bitops)
  :short "This book provides a readable nice macro for extracting a portion of
an integer.  You could use it to, e.g., extract bits 15-8 as a byte.")

(defsection part-select
  :parents (bitops/part-select)
  :short "Select a portion of bits from an integer that represents a bit
vector"

  :long "<p>@('part-select') is a macro that lets you write code to extract
parts of vectors.  For instance:</p>

@({
     (part-select foo :low 10 :high 17)   ;; Like foo[17:10] in Verilog
})

<p>You can also using an index/size, e.g.:</p>

@({
     (part-select foo :low 10 :width 7)   ;; Like foo[16:10] in Verilog
})

@(def part-select)"

  (defun-inline part-select-width-low (x width low)
    "Don't call this directly -- use the part-select macro instead."
    (declare (xargs :guard (and (integerp x)
                                (natp width)
                                (natp low))))
    (mbe :logic (loghead width (logtail low x))
         :exec (logand (1- (ash 1 width))
                       (ash x (- low)))))

  (defun-inline part-select-low-high (x low high)
    "Don't call this directly -- use the part-select macro instead."
    (declare (xargs :guard (and (integerp x)
                                (natp low)
                                (natp high)
                                (<= low high))))
    (part-select-width-low x (+ 1 (- high low)) low))

  (defmacro part-select (x &key low high width)
    (cond ((and high width)
           (er hard? 'part-select "Can't use :high and :width together"))
          ((and low high)
           `(part-select-low-high ,x ,low ,high))
          ((and low width)
           `(part-select-width-low ,x ,width ,low))
          (t
           (er hard? 'part-select
               "Need at least :low and :width, or else :low and :high"))))

  (add-macro-alias part-select part-select-width-low$inline))

(local
 (progn

   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 0 :width 16) #ux_DDDD))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 16 :width 16) #ux_CCCC))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 32 :width 16) #ux_BBBB))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 48 :width 16) #ux_AAAA))

   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 0  :high 15) #ux_DDDD))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 16 :high 31) #ux_CCCC))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 32 :high 47) #ux_BBBB))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 48 :high 63) #ux_AAAA))))

(defun ccl-bug-1273-test (n)
  (declare (type (unsigned-byte 80) n))
  (part-select n :low 64 :high 78))

(make-event
    (progn$ (or (equal (ccl-bug-1273-test (1- (expt 2 80))) 32767)
                (cw "~%~%WARNING (centaur/bitops/part-select.lisp): CCL Bug 1273 Detected!~%~
                        Please upgrade CCL to Version 16356 or later. For details see:~%   ~
                            - http://trac.clozure.com/ccl/ticket/1273~%   ~
                            - http://trac.clozure.com/ccl/changeset/16356~%~%"))
            '(value-triple :invisible))
    :check-expansion t)
