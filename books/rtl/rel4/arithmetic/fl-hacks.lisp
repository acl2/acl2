;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

#|
This book contains a few hacks about fl which aren't used elsewhere in support/.

|#

(in-package "ACL2")

(include-book "ground-zero")
;(include-book "basic") ;drop?

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(local (include-book "inverted-factor"))
(local (include-book "nniq"))
(local (include-book "numerator"))
(local (include-book "denominator"))
(local (include-book "fp2"))
(local (include-book "predicate"))
(local (include-book "product"))
(local (include-book "unary-divide"))
(local (include-book "rationalp"))
(local (include-book "integerp"))
(local (include-book "fl")) ;drop?
(local (include-book "mod"))
(local (include-book "even-odd"))
(local (include-book "meta/meta-plus-equal" :dir :system))

(local (include-book "arith"))

;used anywhere?
;exported in lib/basic
(defthm fl-m-1
  (implies (and (< 0 n) ;(not (equal n 0))
                (integerp m)
                (integerp n)
                )
           (= (fl (- (/ (1+ m) n)))
              (1- (- (fl (/ m n))))))
  :otf-flg t
  :rule-classes ()
  :hints (
          ("goal" :in-theory (disable fl-def-linear-part-2
                                      LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE)
           :use ((:instance  fl-of-fraction-min-change
                             (p (+ 1 m)) (q n))
                 (:instance fl-unique (x (* M (/ N)))
                            (n (+ -1 (+ (/ N) (* M (/ N))))))
                 (:instance fl-unique (x (+ (/ N) (* M (/ N))))
                            (n (FL (* M (/ N)))))

                 ))))

;remove?  doesn't seem to be used anywhere or exported in lib/
;just a special case of the above...
(defthm fl-lemma
    (implies (integerp m)
	     (= (fl (- (/ (1+ m) 2)))
		(1- (- (fl (/ m 2))))))
  :rule-classes ()
  :hints (("goal" :use (:instance fl-m-1 (n 2)))))




