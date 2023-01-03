; A (very simple) verified R1CS constraint
;
; Copyright (C) 2019-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "r1cs")
(include-book "rules")
;(include-book "kestrel/crypto/r1cs/gadgets" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; Assume the vector is just [1, x, y].  The constraint is then: x * y = y.
;; Would be a constant but we can't eval.
(defun constraint-for-xy=y ()
  (r1cs-constraint (list 0 1 0) ;A
                   (list 0 0 1) ;B
                   (list 0 0 1) ;C
                   ))

;test (cannot just eval due to unknown prime):
(thm
 (implies (primep prime)
          (r1cs-constraint-holdsp (constraint-for-xy=y)
                                  (acons 'x 1 (acons 'y 1 nil)) ;'((x . 1) (y . 1))
                                  '(x y)
                                  prime))
 :hints (("Goal" :in-theory (enable r1cs-constraint-holdsp
                                    ;;car-becomes-nth-of-0
                                    ))))

(defthm constraint-for-xy=y-correct
  (implies (and (pfield::fep x prime)
                (pfield::fep y prime)
                (primep prime))
           (iff (r1cs-constraint-holdsp (constraint-for-xy=y)
                                        (acons 'x x (acons 'y y nil))
                                        '(x y)
                                        prime)
                (equal (pfield::mul x y prime) y)))
  :hints (("Goal" :in-theory (enable R1CS-CONSTRAINT-HOLDSP))))
