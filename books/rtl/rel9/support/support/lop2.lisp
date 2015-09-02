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

(in-package "ACL2")

(include-book "lop1") ;BOZO
(include-book "lior0");BOZO
(local (include-book "lop2-proofs"))

(defthm lop-thm-1-original
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (= e (expo a))
                (< (expo b) e)
                (= lambda
                   (lior0 (* 2 (mod a (expt 2 e)))
                         (lnot (* 2 b) (1+ e))
                         (1+ e))))
           (or (= (expo (- a b)) (expo lambda))
               (= (expo (- a b)) (1- (expo lambda)))))
  :rule-classes ())
