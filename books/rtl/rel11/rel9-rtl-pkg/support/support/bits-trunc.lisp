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

;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "RTL")

;BOZO include less...
(include-book "log")
(include-book "float")
(include-book "trunc")
(include-book "land0")
(local (include-book "bits-trunc-proofs"))



(defthm bits-trunc-2
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0)
                )
           (= (trunc x k)
              (* (expt 2 (- n k))
                 (bits x (1- n) (- n k)))))
  :rule-classes ())

(defthm bits-trunc-original
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x) (> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0)
                )
           (= (trunc x k)
              (land0 x (- (expt 2 m) (expt 2 (- n k))) n)))
  :rule-classes ())
