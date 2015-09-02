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

(in-package "RTL")

;Did we say we'd keep log= enabled?  Will this cause lots of splitting on ifs?

(defund log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

;or did we say we'd keep log= disabled?
(defthm log=-same
  (equal (log= x x) 1)
  :hints (("Goal" :in-theory (enable log=))))
