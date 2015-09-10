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

;don't need everything in this book!
(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "nniq"))
(local (include-book "arith2"))
;(local (include-book "type"))
(local (include-book "ground-zero"))
(local (include-book "floor"))
(local (include-book "integerp"))
(local (include-book "rationalp"))
(local (include-book "unary-divide"))
(local (include-book "expt"))
(local (include-book "expo"))
(local (include-book "power2p"))
(local (include-book "fl"))

(local (in-theory (enable expt-minus)))

(defun fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

;more general vesions of this below.  kill this one?
(defthm fl-simp
  (implies (case-split (rationalp x))
           (equal (FL (* 1/2 (FL (* X (/ (EXPT 2 N))))))
                  (FL (* 1/2 X (/ (EXPT 2 N))))))
  :hints (("Goal" :in-theory (disable fl-def-linear)
           :use
           ((:instance fl-unique
                       (x (* 1/2 (FL (* X (/ (EXPT 2 N))))))
                       (n (FL (* 1/2 X (/ (EXPT 2 N))))))
            (:instance fl-def-linear (x (* 1/2 X (/ (EXPT 2 N)))))))))



(encapsulate
 ()
 (local (defthm fl-shift-fl-case-1
          (implies (<= 0 m)
                   (equal (FL (* (FL X) (/ (expt 2 m))))
                          (FL (* X (/ (EXPT 2 m))))))
          :hints (("Goal" :cases ((rationalp x))))
          ))

 (local (defthm fl-shift-fl-case-2
          (implies (AND (< m 0)
                        (case-split (INTEGERP M))
                        )
                   (equal (FL (* (FL X) (/ (expt 2 m))))
                          (* (FL x) (/ (expt 2 m)))))
          :hints  (("Goal" :in-theory (disable fl-int)
                    :use (:instance fl-int (x (* (/ (expt 2 m)) (FL X))))))))



;can this be extended to let the out fl be of a sum?
;leave the case-1 event enabled too (not integerp hyp)?
 (defthm fl-shift-fl
   (implies (case-split (INTEGERP M))
            (equal (FL (* (/ (expt 2 m)) (FL X)))
                   (if (<= 0 m)
                       (FL (* (/ (EXPT 2 m)) X))
                     (* (/ (expt 2 m)) (FL x)))))
   :hints (("Goal" :cases ((< m 0))))
   )
 )


#|
(defthm fl-shift-fl-case-1-gen
  (implies (and (rationalp x)
                (rationalp y)
                (integerp m)
                (<= 0 m)
                )
           (equal (fl (* (/ (expt 2 m)) (+ y (* 2 (fl (* 1/2 x))))))
                  (fl (* (/ (expt 2 m)) (+ y x)))))
  :otf-flg t
 :hints (("Goal" :in-theory (disable  FL-DEF-LINEAR-PART-1
                                       FL-DEF-LINEAR-PART-2
                                       FL-WEAK-MONOTONE
;                                        LESS-THAN-MULTIPLY-THROUGH-BY-inverted-factor-FROM-LEFT-HAND-SIDE
                                       )
          :use (
          (:instance FL-DEF-LINEAR-part-1
                     (x (+ (* X (/ (EXPT 2 M)))
                           (* Y (/ (EXPT 2 M))))))
          (:instance FL-DEF-LINEAR-part-1
                     (x x))
          (:instance FL-DEF-LINEAR-part-2
                     (x (+ (* X (/ (EXPT 2 M)))
                           (* Y (/ (EXPT 2 M))))))
          (:instance FL-DEF-LINEAR-part-2
                     (x x))

          (:instance fl-unique
                     (x (* (/ (expt 2 m)) (+ y (* 2 (FL (* 1/2 X))))))
                     (n (FL (* (/ (EXPT 2 m)) (+ y X)))))))))
|#

(defthm fl-shift-fl-2-factors
  (implies (AND ;(case-split (rationalp x))
                (case-split (INTEGERP M))
                (case-split (INTEGERP n))
                )
           (equal (FL (* (/ (expt 2 m)) (expt 2 n) (FL X)))
                  (if (<= 0 (- m n))
                      (FL (* (/ (EXPT 2 (- m n))) X))
                    (* (/ (expt 2 (- m n))) (FL x)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '( fl-shift-fl  ;EXPO-COMPARISON-REWRITE-TO-BOUND
                                              ))
           :use (:instance fl-shift-fl (m (- m n))))))

(defthm fl-shift-fl-2-factors-2
  (implies (AND ;(case-split (rationalp x))
                (case-split (INTEGERP M))
                (case-split (INTEGERP n))
                )
           (equal (FL (* (expt 2 n) (/ (expt 2 m)) (FL X)))
                  (if (<= 0 (- m n))
                      (fl (* (/ (EXPT 2 (- m n))) X))
                    (* (/ (expt 2 (- m n))) (FL x)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '( fl-shift-fl EXPO-COMPARISON-REWRITE-TO-BOUND))
           :use (:instance fl-shift-fl (m (- m n))))))



;(FL (* 2 (/ (EXPT 2 K)) (FL (* 1/2 X))))


(defthm fl-shift-fl-by-1
  (EQUAL (FL (* 1/2 (FL X)))
         (FL (* 1/2 X)))
  :hints (("Goal" :use (:instance fl-shift-fl (m 1)))))



