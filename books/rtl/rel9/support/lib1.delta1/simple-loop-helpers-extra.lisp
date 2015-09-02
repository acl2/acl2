; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(IN-PACKAGE "ACL2")

(include-book "../lib1/rtl")
(include-book "../lib1/rtlarr")
(include-book "../lib1/bits")


(defthm bitn-setbitn-setbitn
  (implies (and (<  j w)
                (<= 0 j)
                (integerp w)
                (integerp j))
           (equal (bitn (setbitn x w j y)
                        j)
                  (bitn y 0)))
  :hints (("Goal" :in-theory (enable setbitn BITN-CAT))))
