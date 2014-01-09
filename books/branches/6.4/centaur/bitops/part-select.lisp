; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "ihsext-basics"))
(local (include-book "misc/assert" :dir :system))

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
               "Need at least :low and :width, or else :low and :high")))))

(local
 (progn

   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 0 :width 16) #ux_DDDD))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 16 :width 16) #ux_CCCC))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 32 :width 16) #ux_BBBB))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 48 :width 16) #ux_AAAA))

   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 0  :high 15) #ux_DDDD))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 16 :high 31) #ux_CCCC))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 32 :high 47) #ux_BBBB))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 48 :high 63) #ux_AAAA))

   ))

