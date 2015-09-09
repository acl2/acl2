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
(include-book "../lib2/bits")

(local (include-book "../lib2/top"))
(local (include-book "../../arithmetic/top"))


(local
  (defthmd bits_alt-mbe-lemma-subgoal-2
    (IMPLIES (AND (INTEGERP J)
                  (INTEGERP I)
                  (INTEGERP X)
                  (< I J))
             (EQUAL (FL (* (/ (EXPT 2 J))
                           (MOD X (EXPT 2 (+ 1 I)))))
                    0))))


(encapsulate ()
             ;; a proof for logone-ones-g

             (local (encapsulate ()

                                 (encapsulate ()
                                              (local (include-book "../support/log"))
                                              (defthm bitn-logand
                                                (implies (and (integerp x) ; (>= x 0)
                                                              (integerp y) ; (>= y 0)
                                                              (integerp n) (>= n 0)
                                                              )
                                                         (equal (bitn (logand x y) n)
                                                                (logand (bitn x n) (bitn y n)))))


                                              )




                                 (encapsulate ()
                                              (local (include-book "../support/merge"))

                                              (defthmd logand-1-x
                                                (implies (bvecp x 1)
                                                         (equal (logand 1 x) x)))

                                              )




                                 (encapsulate ()
                                              (local (include-book "../support/logand"))

                                              (defthm logand-bnd
                                                (implies (<= 0 x)
                                                         (<= (logand x y) x))
                                                :rule-classes :linear
                                                )


                                              (defthm logand-commutative
                                                (equal (logand j i)
                                                       (logand i j)))


                                              (defthm logand-non-negative
                                                (implies (or (<= 0 x)
                                                             (<= 0 y)
                                                             )
                                                         (<= 0 (logand x y))))


                                              (DEFTHM LOGAND-NON-NEGATIVE-INTEGER-TYPE-PRESCRIPTION
                                                (IMPLIES (OR (<= 0 I) (<= 0 J))
                                                         (AND (<= 0 (LOGAND I J))
                                                              (INTEGERP (LOGAND I J))))
                                                :RULE-CLASSES (:TYPE-PRESCRIPTION))

                                              )



                                 (encapsulate ()
                                              (local (include-book "../support/badguys"))

                                              (defun sumbits-badguy (x y k)
                                                (if (zp k)
                                                    0 ; arbitrary
                                                  (if (not (equal (bitn x (1- k)) (bitn y (1- k))))
                                                      (1- k)
                                                    (sumbits-badguy x y (1- k)))))


                                              (defthmd sumbits-badguy-is-correct
                                                (implies (and (bvecp x k)
                                                              (bvecp y k)
                                                              (equal (bitn x (sumbits-badguy x y k))
                                                                     (bitn y (sumbits-badguy x y k)))
                                                              (integerp k)
                                                              (< 0 k))
                                                         (equal (equal x y) t))
                                                :hints (("Goal"
                                                         :use sumbits-badguy-is-correct-lemma
                                                         :in-theory (enable sumbits-thm))))

                                              (defthmd sumbits-badguy-bounds
                                                (implies (and (integerp k)
                                                              (< 0 k))
                                                         (let ((badguy (sumbits-badguy x y k)))
                                                           (and (integerp badguy)
                                                                (<= 0 badguy)
                                                                (< badguy k)))))
                                              )


                                 (encapsulate ()
                                              (local (include-book "../lib2/bits"))
                                              (defthmd bitn-mod
                                                (implies (and (< k n)
                                                              (integerp n)
                                                              (integerp k))
                                                         (equal (bitn (mod x (expt 2 n)) k)
                                                                (bitn x k)))))



                                 (defthmd logand-ones-g-lemma-lemma
                                   (implies (and (<= 0 k)
                                                 (<= k (+ -1 n))
                                                 (integerp n)
                                                 (> n 0)
                                                 (integerp k))
                                            (equal (bitn (+ -1 (expt 2 n)) k) 1))
                                   :hints (("Goal" :in-theory (e/d (bitn bits
                                                                         expt-2-reduce-leading-constant)
                                                                   (bits-n-n-rewrite)))))



                                 (defthmd logand-ones-g-lemma-1
                                   (implies (and (<= 0 k)
                                                 (<= k (+ -1 n))
                                                 (< 0 n)
                                                 (integerp n)
                                                 (integerp x)
                                                 (integerp k))
                                            (equal (bitn (logand x (+ -1 (expt 2 n))) k)
                                                   (bitn (mod x (expt 2 n)) k)))
                                   :hints (("Goal" :in-theory (e/d (bitn-logand
                                                                    bitn-mod
                                                                    logand-1-x
                                                                    logand-ones-g-lemma-lemma)
                                                                   ()))))



                                 (defthmd sumbits-badguy-fact
                                   (implies (and (<= 0 k)
                                                 (<= k n)
                                                 (< 0 n)
                                                 (integerp n)
                                                 (integerp x)
                                                 (integerp k))
                                            (equal (bitn (logand x (+ -1 (expt 2 n)))
                                                         (sumbits-badguy (logand x (+ -1 (expt 2 n)))
                                                                         (mod x (expt 2 n))
                                                                         k))
                                                   (bitn (mod x (expt 2 n))
                                                         (sumbits-badguy (logand x (+ -1 (expt 2 n)))
                                                                         (mod x (expt 2 n)) k))))
                                   :hints (("Goal" :in-theory (e/d (logand-ones-g-lemma-1)
                                                                   (bitn-logand bitn-mod)))))



                                 (defthm logand-ones-g-lemma-2
                                   (implies (and (integerp x)
                                                 (natp n))
                                            (bvecp (logand x (+ -1 (expt 2 n))) n))
                                   :hints (("Goal"
                                            :cases ((equal (logand x (+ -1 (expt 2 n)))
                                                           (logand (+ -1 (expt 2 n)) x))))
                                           ("Subgoal 1"
                                            :in-theory (e/d (bvecp)
                                                            (logand-bnd
                                                             logand-commutative
                                                             logand-non-negative))
                                            :use ((:instance logand-bnd
                                                             (x (+ -1 (expt 2 n)))
                                                             (y x))
                                                  (:instance logand-non-negative
                                                             (x x)
                                                             (y (+ -1 (expt 2 n))))))))



                                 (defthm logand-ones-g-lemma-3
                                   (implies (integerp x)
                                            (bvecp (mod x (expt 2 n)) n))
                                   :hints (("Goal" :in-theory (enable bvecp))))
                                 ))

             (defthmd logand-ones-g
               (implies (and (integerp i)
                             (case-split (integerp i))
                             )
                        (equal (logand i (1- (expt 2 n)))
                               (mod i (expt 2 n))))
               :hints (("Goal" :in-theory (e/d (sumbits-badguy-fact)
                                               (sumbits-badguy-is-correct
                                                bitn-mod
                                                bitn-logand
                                                logand-1-x))
                        :cases ((not (and (integerp n)
                                          (> n 0)))))
                       ("Subgoal 2"  :use ((:instance sumbits-badguy-is-correct
                                                      (x (logand i (+ -1 (expt 2 n))))
                                                      (y (mod i (expt 2 n)))
                                                      (k n))))
                       ("Subgoal 1.1" :in-theory (enable acl2::binary-logand))))


             )




(local
 (defthmd bits_alt-mbe-lemma-subgoal-1-lemma-1
   (IMPLIES (AND (INTEGERP J)
                 (INTEGERP I)
                 (INTEGERP X)
                 (<= J I))
            (EQUAL (FL (* (/ (EXPT 2 J))
                          (MOD X (EXPT 2 (+ 1 I)))))
                   (mod (FL (* X (EXPT 2 (* -1 J))))
                        (EXPT 2 (+ 1 I (* -1 J))))))
   :hints (("Goal" :in-theory (e/d (mod
                                    expt-minus)
                                   ())))))




(local
 (defthmd bits_alt-mbe-lemma-subgoal-1-lemma-2
   (IMPLIES (AND (INTEGERP J)
                 (INTEGERP I)
                 (INTEGERP X)
                 (<= J I))
            (EQUAL (LOGAND (FL (* X (EXPT 2 (* -1 J))))
                           (+ -1 (EXPT 2 (+ 1 I (* -1 J)))))
                   (mod (FL (* X (EXPT 2 (* -1 J))))
                        (EXPT 2 (+ 1 I (* -1 J))))))
   :hints (("Goal" :in-theory (e/d (mod expt-minus
                                        logand-ones-g)
                                   ())))))



(local
 (defthmd bits_alt-mbe-lemma-subgoal-1
   (IMPLIES (AND (INTEGERP J)
                 (INTEGERP I)
                 (INTEGERP X)
                 (<= J I))
            (EQUAL (FL (* (/ (EXPT 2 J))
                          (MOD X (EXPT 2 (+ 1 I)))))
                   (LOGAND (FL (* X (EXPT 2 (* -1 J))))
                           (+ -1 (EXPT 2 (+ 1 I (* -1 J)))))))
   :hints (("Goal" :in-theory (e/d (bits_alt-mbe-lemma-subgoal-1-lemma-2
                                    bits_alt-mbe-lemma-subgoal-1-lemma-1
                                    ) ())))))





(defund bits_alt (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))
                  :guard-hints (("Goal" :in-theory (e/d
                                                    (bits_alt-mbe-lemma-subgoal-1
                                                     bits_alt-mbe-lemma-subgoal-2) ())))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))



(defthmd bits_alt-is-bits
  (equal (bits_alt x i j)
         (bits x i j))
  :hints (("Goal" :in-theory (e/d (bits_alt bits)
                                  ()))))




(defthm bits_alt-nonnegative-integerp-type
  (and (<= 0 (bits_alt x i j))
       (integerp (bits_alt x i j)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-nonnegative-integerp-type)))))

(in-theory (disable (:type-prescription bits_alt)))

(defthm bits_alt-bvecp
    (implies (and (<= (+ 1 i (- j)) k)
		  (case-split (integerp k)))
	     (bvecp (bits_alt x i j) k))
    :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                    ())
             :use ((:instance bits-bvecp)))))


;;Here is a variation of bits_alt-bvecp that is less general but does not
;;require an integerp hypothesis:
(defthm bits_alt-bvecp-simple
  (implies (equal k (+ 1 i (* -1 j)))
           (bvecp (bits_alt x i j) k))
    :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                    ())
             :use ((:instance bits-bvecp-simple)))))

(defthm mod-bits_alt-equal
  (implies (= (mod x (expt 2 (1+ i)))
	      (mod y (expt 2 (1+ i))))
	   (= (bits_alt x i j) (bits_alt y i j)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance mod-bits-equal)))))

(defthmd mod-bits_alt-equal-cor
    (implies (and (integerp x)
		  (integerp n)
		  (integerp i)
		  (integerp j)
		  (< i n))
	     (equal (bits_alt (mod x (expt 2 n)) i j)
		    (bits_alt x i j)))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance mod-bits-equal-cor)))))

(defthmd bits_alt-mod
  (implies (and (case-split (integerp x))
		(case-split (integerp i)))
	   (equal (bits_alt x i 0)
		  (mod x (expt 2 (1+ i)))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-mod)))))


(defthmd bits_alt-bits_alt-sum
  (implies (and (integerp x)
                (integerp y)
                (integerp i))
	   (equal (bits_alt (+ (bits_alt x i 0) y) i 0)
		  (bits_alt (+ x y) i 0)))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-bits-sum)))))


(defthmd bits_alt-mod-2
  (implies (and (integerp x)
                (integerp i)
                (integerp j)
                (>= i j))
           (equal (bits_alt x (1- i) j)
                  (- (fl (/ x (expt 2 j)))
                     (* (expt 2 (- i j))
                        (fl (/ x (expt 2 i)))))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-mod-2)))))


(defthm bits_alt-neg
  (implies (and (< i 0)
                (integerp x))
           (equal (bits_alt x i j) 0))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-neg)))))

;;;
;;; may want to write an macro that does this proof step!!!
;;;

(defthm bits_alt-with-indices-in-the-wrong-order
  (implies (< i j)
	   (equal (bits_alt x i j)
		  0))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-with-indices-in-the-wrong-order)))))

(defthmd bvecp-bits_alt-0
  (implies (bvecp x j)
	   (equal (bits_alt x i j) 0))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bvecp-bits-0)))))

(defthm bits_alt-0
  (equal (bits_alt 0 i j) 0)
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-0)))))

;;;;;;
;;;;;;  Thu Feb  5 15:06:32 2009
;;;;;;


(local
 (defthmd fl-small-neg
   (implies (and (real/rationalp x)
                 (<= -1 x)
                 (< x 0))
            (equal (fl x)
                   -1))
   :hints (("Goal" :in-theory (e/d (fl floor)
                                   (floor-fl))))))

(defthmd neg-bits_alt-1
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (< x 0)
                (>= x (- (expt 2 j)))
                (>= i j))
           (equal (bits_alt x i j)
                  (+ -1 (expt 2 (+ 1 i (* -1 j))))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   fl-small-neg)
                                  ())
           :cases ((< (/ (expt 2 (+ 1 i)))
                      (/ (expt 2 j))))
           :use ((:instance BITS-MOD-2
                            (i (+ 1 i))
                            (j j))))))



(defthmd bits_alt-minus-1
  (implies (and (natp i)
                (natp j)
                (>= i j))
           (equal (bits_alt -1 i j)
                  (+ -1  (expt 2 (+ 1 i (* -1 j))))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits fl-small-neg)
                                  ())
           :use ((:instance bits-mod-2
                            (x -1)
                            (i (+ 1 i))
                            (j j))))))




(defthm bits_alt-tail
  (implies (and (bvecp x (1+ i))
                (case-split (acl2-numberp i)))
           (equal (bits_alt x i 0) x))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-tail)))))


;;;;
;;;;

;; (i-am-here) ;; Mon Feb 23 16:31:22 2009


(defthm bits_alt-tail-2
  (implies (and (integerp x)
                (natp i)
                (< x (expt 2 i))
                (>= x (- (expt 2 (+ 1 i)))))
           (equal (bits_alt x i 0)
                  (if (>= x 0)
                      x
                    (+ x (expt 2 (+ 1 i))))))
   :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                    bits-mod
                                    fl-small-neg
                                    mod)
                                   ()))
           ("Subgoal 2"
            :cases ((<= -1 (* x (/ (expt 2 (+ 1 i)))))))
           ("Subgoal 2.2" :in-theory (e/d (expt-2-reduce-leading-constant) ()))
           ("Subgoal 1" :in-theory (e/d (expt-2-reduce-leading-constant) ()))))


(defthm bits_alt-drop-from-minus
  (implies (and (bvecp x (1+ i))
                (bvecp y (1+ i))
                (<= y x)
                (case-split (acl2-numberp i)))
           (equal (bits_alt (+ x (* -1 y)) i 0)
                  (+ x (* -1 y))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-drop-from-minus)))))


(defthmd bits_alt-shift-down-1
  (implies (and (<= 0 j)
		(integerp i)
		(integerp j)
		(integerp k))
	   (equal (bits_alt (fl (/ x (expt 2 k))) i j)
		  (bits_alt x (+ i k) (+ j k))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-shift-down-1)))))


(defthmd bits_alt-shift-down-2
  (implies (and (integerp x)
                (natp i)
                (natp k))
           (equal (fl (/ (bits_alt x (+ i k) 0) (expt 2 k)))
                  (bits_alt (fl (/ x (expt 2 k))) i 0)))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   bits-mod)
                                  ()))))


(defthm bits_alt-shift-up-1
  (implies (and (integerp k)
		(integerp i)
		(integerp j))
	   (equal (bits_alt (* (expt 2 k) x) i j)
		  (bits_alt x (- i k) (- j k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-shift-up-1)))))


(defthm bits_alt-shift-up-2
  (implies (and (integerp x)
		(natp k)
		(integerp i))
	   (equal (* (expt 2 k) (bits_alt x i 0))
		  (bits_alt (* (expt 2 k) x) (+ i k) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-shift-up-2)))))


(defthmd bits_alt-plus-mult-1
  (implies (and (bvecp x k)
		(<= k m)
		(integerp y)
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp k)))
	   (equal (bits_alt (+ x (* y (expt 2 k))) n m)
		  (bits_alt y (- n k) (- m k))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-plus-mult-1)))))


(defthm bits_alt-plus-mult-2
  (implies (and (< n k)
		(integerp y)
		(integerp k))
	   (equal (bits_alt (+ x (* y (expt 2 k))) n m)
		  (bits_alt x n m)))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-plus-mult-2)))))

(defthmd bits_alt-plus-mult-2-rewrite
   (implies (and (syntaxp (quotep c))
                 (equal (mod c (expt 2 (1+ n))) 0))
            (equal (bits_alt (+ c x) n m)
                   (bits_alt x n m)))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-plus-mult-2-rewrite)))))

(defthm bits_alt-plus-bits_alt
    (implies (and (integerp m)
		  (integerp p)
		  (integerp n)
		  (<= m p)
		  (<= p n))
	     (= (bits_alt x n m)
		(+ (bits_alt x (1- p) m)
		   (* (expt 2 (- p m)) (bits_alt x n p)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-plus-bits)))))


(defthm bits_alt-bits_alt
  (implies (and (case-split (<= 0 l))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp l)))
	   (equal (bits_alt (bits_alt x i j) k l)
		  (if (<= k (- i j))
		      (bits_alt x (+ k j) (+ l j))
		    (bits_alt x i (+ l j)))))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-bits)))))



;;bits_alt-match can prove things like this:
;;(thm (implies (equal 12 (bits_alt x 15 6))
;;		(equal 4 (bits_alt x 8 6))))
;;See also bits_alt-dont-match.

(defthmd bits_alt-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits_alt x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(equal k (bits_alt k2 (+ i (- j2)) (+ (- j2) j)))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits_alt x i j))
		  t))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-match)))))

;;bits_alt-dont-match can prove things like this:
;;(thm (implies (equal 7 (bits_alt x 8 6))
;;		(not (equal 4 (bits_alt x 15 6)))))
;;See also bits_alt-match.

(defthmd bits_alt-dont-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits_alt x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(not (equal k (bits_alt k2 (+ i (- j2)) (+ (- j2) j))))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits_alt x i j))
		  nil))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits)
                                  ())
           :use ((:instance bits-dont-match)))))

;;;;;
;;;;;


;;;**********************************************************************
;;;				BITN_ALT
;;;**********************************************************************

(local
 (defthmd evenp-sum
   (implies (and (evenp x)
                 (evenp y))
            (evenp (- x y)))
   :hints (("Goal" :in-theory (e/d (evenp) ())))))

(local
 (defthmd evenp-2-factor
   (implies (integerp x)
            (evenp (* 2 x)))
   :hints (("Goal" :in-theory (e/d (evenp) ())))))

(local
 (defthmd bitn_alt-mbe-subgoal-2-lemma
   (IMPLIES (AND (INTEGERP N)
                 (INTEGERP X)
                (evenp (FL (* X (EXPT 2 (* -1 N))))))
            (evenp (BITN X N)))
  :hints (("Goal" :in-theory (e/d (bitn expt-minus
                                        evenp-2-factor)
                                  (bits-n-n-rewrite))
           :use ((:instance bits-mod-2
                            (x x)
                            (i (+ 1 n))
                            (j n))
                 (:instance evenp-sum
                            (x (fl (* x (/ (expt 2 n)))))
                            (y (* 2 (fl (* x (/ (expt 2 (+ 1 n)))))))))))))




(defthmd bitn_alt-mbe-subgoal-2
  (IMPLIES (AND (INTEGERP N)
                (INTEGERP X)
                (evenp (FL (* X (EXPT 2 (* -1 N))))))
           (EQUAL (BITN X N) 0))
  :hints (("Goal" :use ((:instance bitn-0-1
                                   (x x)
                                   (n n))
                        (:instance bitn_alt-mbe-subgoal-2-lemma))
           :in-theory (e/d (evenp) ()))))



(local
 (defthmd not-evenp-sum
   (implies (and (not (evenp x))
                 (evenp y))
            (not (evenp (- x y))))
   :hints (("Goal" :in-theory (e/d (evenp) ())))))


(local
 (defthmd bitn_alt-mbe-subgoal-1-lemma
   (IMPLIES (AND (INTEGERP N)
                 (INTEGERP X)
                 (not (evenp (FL (* X (EXPT 2 (* -1 N)))))))
            (not (evenp (BITN X N))))
  :hints (("Goal" :in-theory (e/d (bitn expt-minus
                                        evenp-2-factor)
                                  (bits-n-n-rewrite))
           :use ((:instance bits-mod-2
                            (x x)
                            (i (+ 1 n))
                            (j n))
                 (:instance not-evenp-sum
                            (x (fl (* x (/ (expt 2 n)))))
                            (y (* 2 (fl (* x (/ (expt 2 (+ 1 n)))))))))))))




(defthmd bitn_alt-mbe-subgoal-1
  (IMPLIES (AND (INTEGERP N)
                (INTEGERP X)
                (NOT (evenp (FL (* X (EXPT 2 (* -1 N)))))))
           (EQUAL (BITN X N) 1))
  :hints (("Goal" :use ((:instance bitn-0-1
                                   (x x)
                                   (n n))
                        (:instance bitn_alt-mbe-subgoal-1-lemma))
           :in-theory (e/d (evenp) ()))))



(defund bitn_alt (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))
                  :guard-hints (("Goal" :in-theory (e/d (bitn_alt-mbe-subgoal-1
                                                         bitn_alt-mbe-subgoal-2
                                                         bits_alt-is-bits) ())))))
  (mbe :logic (bits_alt x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defthmd bitn_alt-is-bitn
  (equal (bitn_alt x n)
         (bitn x n))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   bitn_alt
                                   bits_alt)
                                  ()))))



(defthm bitn_alt-nonnegative-integer
  (and (integerp (bitn_alt x n))
       (<= 0 (bitn_alt x n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-nonnegative-integer)))))

(in-theory (disable (:type-prescription bitn_alt)))

(defthm bits_alt-n-n-rewrite
  (equal (bits_alt x n n)
	 (bitn_alt x n))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   bitn_alt-is-bitn) ())
           :use ((:instance bits-n-n-rewrite)))))

(defthmd bitn_alt-def
  (implies (case-split (integerp n))
	   (equal (bitn_alt x n)
		  (mod (fl (/ x (expt 2 n))) 2)))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-def)))))

;;A recursive formulation:

(defthmd bitn_alt-rec-0
  (implies (integerp x)
	   (equal (bitn_alt x 0) (mod x 2)))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-rec-0)))))


(defthmd bitn_alt-rec-pos
    (implies (< 0 n)
	     (equal (bitn_alt x n)
		    (bitn_alt (fl (/ x 2)) (1- n))))
  :rule-classes ((:definition :controller-alist ((bitn_alt t t))))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-rec-pos)))))

;;Use this to induce case-splitting:

(defthm bitn_alt-0-1
    (or (equal (bitn_alt x n) 0)
	(equal (bitn_alt x n) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-0-1)))))

(defthm bitn_alt-bvecp
  (implies (and (<= 1 k)
		(case-split (integerp k)))
	   (bvecp (bitn_alt x n) k))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-bvecp)))))

;;The following is a special case of bitn_alt-bvecp.
;;It is useful as a :forward-chaining rule in concert with bvecp-0-1 and
;;bvecp-1-0.
(defthm bitn_alt-bvecp-forward
  (bvecp (bitn_alt x n) 1)
  :rule-classes ((:forward-chaining :trigger-terms ((bitn_alt x n))))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-bvecp-forward)))))

(defthm bitn_alt-neg
  (implies (and (< n 0)
                (integerp x))
           (equal (bitn_alt x n) 0))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-neg)))))


(defthm bitn_alt-0
  (equal (bitn_alt 0 k) 0)
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-0)))))

(defthm bitn_alt-bvecp-1
    (implies (bvecp x 1)
	     (equal (bitn_alt x 0) x))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-bvecp-1)))))

(defthm bitn_alt-bitn_alt-0
    (equal (bitn_alt (bitn_alt x n) 0)
	   (bitn_alt x n))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-bitn-0)))))

(defthmd bitn_alt-mod
    (implies (and (< k n)
		  (integerp n)
		  (integerp k))
	     (equal (bitn_alt (mod x (expt 2 n)) k)
		    (bitn_alt x k)))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-mod)))))

(defthm bvecp-bitn_alt-0
    (implies (bvecp x n)
	     (equal (bitn_alt x n) 0))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bvecp-bitn-0)))))



(defthm neg-bitn_alt-1
  (implies (and (integerp x)
                (integerp n)
                (< x 0)
                (>= x (- (expt 2 n))))
           (equal (bitn_alt x n) 1))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn
                                   bits_alt-is-bits
                                   bitn
                                   ) (bits-n-n-rewrite))
           :use ((:instance neg-bits_alt-1
                            (x x)
                            (i n)
                            (j n))))))


(defthmd bitn_alt-shift
  (implies (and (integerp n)
                (integerp k))
           (equal (bitn_alt (* x (expt 2 k)) (+ n k))
                  (bitn_alt x n)))
   :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
            :use ((:instance bitn-shift)))))


(defthmd bitn_alt-shift-down
  (implies (and (natp i)
		(integerp k))
	   (equal (bitn_alt (fl (/ x (expt 2 k))) i)
		  (bitn_alt x (+ i k))))
   :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
            :use ((:instance bitn-shift-down)))))

(defthm bitn_alt-bits_alt
  (implies (and (<= k (- i j))
		(case-split (<= 0 k))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k)))
	   (equal (bitn_alt (bits_alt x i j) k)
		  (bitn_alt x (+ j k))))
   :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                    bitn_alt-is-bitn) ())
            :use ((:instance bitn-bits)))))

(defthmd bitn_alt-plus-bits_alt
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits_alt x n m)
		(+ (* (bitn_alt x n) (expt 2 (- n m)))
		   (bits_alt x (1- n) m))))
   :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                    bitn_alt-is-bitn) ())
            :use ((:instance bitn-plus-bits)))))

(defthm bits_alt-plus-bitn_alt
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits_alt x n m)
		(+ (bitn_alt x m)
		   (* 2 (bits_alt x n (1+ m))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   bitn_alt-is-bitn) ())
           :use ((:instance bits-plus-bitn)))))

(defun sumbits_alt (x n)
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn_alt x (1- n)))
       (sumbits_alt x (1- n)))))

(local
 (defthmd sumbits_alt-is-sumbits
   (equal (sumbits_alt x n)
          (sumbits x n))
   :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())))))


(defthmd sumbits_alt-bits_alt
  (implies (and (integerp x)
                (natp n)
                (> n 0))
           (equal (sumbits_alt x n)
                  (bits_alt x (1- n) 0)))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   binary-cat
                                   sumbits_alt-is-sumbits) (cat-bitn-bits))
            :induct (sumbits x n))
           ("Subgoal *1/2"
            :use ((:instance cat-bitn-bits
                             (x x)
                             (j (+ -1 n))
                             (m 1)
                             (k (+ -2 n))
                             (l 0)
                             (n (+ -1 n)))))))

(defthmd sumbits_alt-thm
    (implies (and (bvecp x n)
		  (natp n)
		  (> n 0))
	     (equal (sumbits_alt x n)
		    x))
   :hints (("Goal" :in-theory (e/d (sumbits_alt-is-sumbits) ())
            :use ((:instance sumbits-thm)))))


; The lemmas sumbits_alt-badguy-is-correct and sumbits_alt-badguy-bounds, below, let
; one prove equality of two bit vectors of width k by proving each of these has
; the same value at bit i, for arbitrary i from 0 to k-1.

(defun sumbits_alt-badguy (x y k)
  (if (zp k)
      0
    (if (not (equal (bitn_alt x (1- k)) (bitn_alt y (1- k))))
        (1- k)
      (sumbits_alt-badguy x y (1- k)))))


(defthmd sumbits_alt-badguy-is-sumbits-badguy
  (equal (sumbits_alt-badguy x y k)
         (sumbits-badguy x y k))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ()))))


(defthmd sumbits_alt-badguy-is-correct
  (implies (and (bvecp x k)
                (bvecp y k)
                (equal (bitn_alt x (sumbits_alt-badguy x y k))
                       (bitn_alt y (sumbits_alt-badguy x y k)))
                (integerp k)
                (< 0 k))
           (equal (equal x y) t))
  :hints (("Goal" :in-theory (e/d (sumbits_alt-badguy-is-sumbits-badguy
                                   bitn_alt-is-bitn) ())
           :use ((:instance sumbits-badguy-is-correct)))))

(defthmd sumbits_alt-badguy-bounds
  (implies (and (integerp k)
                (< 0 k))
           (let ((badguy (sumbits_alt-badguy x y k)))
             (and (integerp badguy)
                  (<= 0 badguy)
                  (< badguy k))))
  :hints (("Goal" :in-theory (e/d (sumbits_alt-badguy-is-sumbits-badguy
                                   bitn_alt-is-bitn) ())
           :use ((:instance sumbits-badguy-bounds)))))

;; from existing file.

(defun all-bits-p (b k)
  (if (zp k)
      t
    (and (or (= (nth (1- k) b) 0)
	     (= (nth (1- k) b) 1))
	 (all-bits-p b (1- k)))))

(defun sum-b (b k)
  (if (zp k)
      0
    (+ (* (expt 2 (1- k)) (nth (1- k) b))
       (sum-b b (1- k)))))

(defthmd sum-bitn_alt
  (implies (and (natp n)
		(all-bits-p b n)
	        (natp k)
		(< k n))
           (equal (bitn_alt (sum-b b n) k)
	          (nth k b)))
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn)
                                  ())
           :use ((:instance sum-bitn)))))


(defthmd bvecp-bitn_alt-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
		  (natp n))
	     (equal (bitn_alt x n) 1))
    :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
             :use ((:instance bvecp-bitn-1)))))

(defthmd bvecp-bitn_alt-2
  (implies (and (bvecp x n)
		(< k n)
		(<= (- (expt 2 n) (expt 2 k)) x)
		(integerp n)
		(integerp k))
	   (equal (bitn_alt x k) 1))
  :rule-classes ((:rewrite :match-free :all))
    :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
             :use ((:instance bvecp-bitn-2)))))

;;;;

;;;
;;; the leading 0.
;;;
(local
 (defthmd fl-neg-fact-2
   (implies (and (<= -2 x)
                 (< x -1)
                 (rationalp x))
            (equal (fl x)
                   -2))))




(defthmd neg-bitn_alt-0-lemma
  (implies (and (integerp x)
                (natp n)
                (< x (- (expt 2 n)))
                (>= x (- (expt 2 (1+ n)))))
            (evenp (bitn x n)))
  :hints (("Goal" :in-theory (e/d (fl-neg-fact-2
                                   evenp-2-factor
                                   bitn)
                                  (bits-n-n-rewrite
                                   REARRANGE-NEGATIVE-COEFS-EQUAL
                                   MOVE-NEGATIVE-CONSTANT-1
                                   evenp))
           :cases ((not (and (<= -2 (* x (/ (expt 2 n))))
                             (< (* x (/ (expt 2 n))) -1)))))
          ("Subgoal 2" :use ((:instance bits-mod-2
                                        (x x)
                                        (i (+ 1 n))
                                        (j n))
                             (:instance evenp-sum
                                        (x -2)
                                        (y (* 2 (fl (* x (/ (expt 2 (+ 1
                                                                       n))))))))))
          ("Subgoal 1" :in-theory (e/d (expt-2-reduce-leading-constant) ()))))

;;;;
;;;; could have other way to prove this.
;;;;
(defthm neg-bitn_alt-0
  (implies (and (integerp x)
                (natp n)
                (< x (- (expt 2 n)))
                (>= x (- (expt 2 (1+ n)))))
            (equal (bitn_alt x n) 0))
  :hints (("Goal" :use ((:instance neg-bitn_alt-0-lemma)
                        (:instance bitn-0-1))
           :in-theory (e/d (bitn_alt-is-bitn) ()))))

(local
 (defthmd mod-x-is
  (implies (and (integerp x)
                (integerp n)
                (integerp k)
                (< k n)
                (< x (- (expt 2 k) (expt 2 n)))
                (>= x (- (expt 2 n))))
           (and (<= 0 (mod x (expt 2 n)))
                (< (mod x (expt 2 n))
                   (expt 2 k))))
  :hints (("Goal" :in-theory (e/d (mod fl-small-neg) ())
           :cases ((not (and (<= -1 (* x (/ (expt 2 n))))
                             (< x 0))))))))




(defthm neg-bitn_alt-2
  (implies (and (integerp x)
                (integerp n)
                (integerp k)
                (< k n)
                (< x (- (expt 2 k) (expt 2 n)))
                (>= x (- (expt 2 n))))
	     (equal (bitn_alt x k) 0))
  :hints (("Goal"  :cases ((bvecp (mod x (expt 2 n)) k)))
          ("Subgoal 2" :in-theory (e/d (bvecp) ())
           :use ((:instance mod-x-is)))
          ("Subgoal 1" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance bitn-mod)))))


(defthmd bitn_alt-expt
    (implies (case-split (integerp n))
	     (equal (bitn_alt (expt 2 n) n)
		    1))
   :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
            :use ((:instance bitn-expt)))))

(defthmd bitn_alt-expt-0
  (implies (and (not (equal i n))
		(case-split (integerp i)))
	   (equal (bitn_alt (expt 2 i) n)
		  0))
   :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
            :use ((:instance bitn-expt-0)))))

(defthm bitn_alt-plus-expt-1
    (implies (and (rationalp x)
		  (integerp n))
	     (not (equal (bitn_alt (+ x (expt 2 n)) n)
			 (bitn_alt x n))))
    :rule-classes ()
    :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
            :use ((:instance bitn-plus-expt-1)))))

(defthmd bitn_alt-plus-mult
    (implies (and (< n m)
		  (integerp m)
		  (integerp k))
	     (equal (bitn_alt (+ x (* k (expt 2 m))) n)
		    (bitn_alt x n)))
    :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
            :use ((:instance bitn-plus-mult)))))

(defthmd bitn_alt-plus-mult-rewrite
    (implies (and (syntaxp (quotep c))
		  (equal (mod c (expt 2 (1+ n))) 0))
	     (equal (bitn_alt (+ c x) n)
		    (bitn_alt x n)))
    :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
            :use ((:instance bitn-plus-mult-rewrite)))))




;;;**********************************************************************
;;;			     CAT
;;;**********************************************************************


(defund binary-cat_alt (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits_alt x (1- m) 0))
         (bits_alt y (1- n) 0))
    0))


(defthmd binary-cat_alt-is-binary-cat
  (equal (binary-cat_alt x m y n)
         (binary-cat x m y n))
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits
                                   binary-cat_alt
                                   binary-cat)
                                  ()))))


;;Definition of the macro, cat_alt:

;;X is a list of alternating data values and sizes.  CAT_ALT-SIZE returns the
;;formal sum of the sizes.  X must contain at least 1 data/size pair, but we do
;;not need to specify this in the guard, and leaving it out of that guard
;;simplifies the guard proof.

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))


(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat_alt (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits_alt ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat_alt ,@x))
        (t
         `(binary-cat_alt ,(car x)
                      ,(cadr x)
                      (cat_alt ,@(cddr x))
                      ,(cat-size (cddr x))))))


(defthm cat_alt-nonnegative-integer-type
  (and (integerp (cat_alt x m y n))
       (<= 0 (cat_alt x m y n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat) ())
           :use ((:instance cat-nonnegative-integer-type)))))


(in-theory (disable (:type-prescription binary-cat_alt)))

(defthm cat_alt-bvecp
  (implies (and (<= (+ m n) k)
		(case-split (integerp k)))
	   (bvecp (cat_alt x m y n) k))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat) ())
           :use ((:instance cat-bvecp)))))

(defthm cat_alt-with-n-0
  (equal (binary-cat_alt x m y 0)
	 (bits_alt x (1- m) 0))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits) ())
           :use ((:instance cat-with-n-0)))))

(defthm cat_alt-with-m-0
  (equal (binary-cat_alt x 0 y n)
	 (bits_alt y (1- n) 0))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits) ())
           :use ((:instance cat-with-m-0)))))

(defthm cat_alt-0
  (implies (and (case-split (bvecp y n))
		(case-split (integerp n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (cat_alt 0 m y n) y))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat)
                                  ())
           :use ((:instance cat-0)))))

(defthmd cat_alt-bits_alt-1
    (equal (cat_alt (bits_alt x (1- m) 0) m y n)
	   (cat_alt x m y n))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance cat-bits-1)))))

(defthmd cat_alt-bits_alt-2
    (equal (cat_alt x m (bits_alt y (1- n) 0) n)
	   (cat_alt x m y n))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance cat-bits-2)))))



(defthm cat_alt-associative
  (implies (and (case-split (<= (+ m n) p))
		(case-split (<= 0 m))
		(case-split (<= 0 n))
		(case-split (<= 0 q))
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp p))
		(case-split (integerp q)))
	   (equal (cat_alt (cat_alt x m y n) p z q)
		  (cat_alt x m (cat_alt y n z q) (+ n q))))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat)
                                  ())
           :use ((:instance cat-associative)))))

(defthmd cat_alt-equal-constant
  (implies (and (syntaxp (and (quotep k)
			      (quotep m)
			      (quotep n)))
		(case-split (bvecp y n))
		(case-split (bvecp x m))
		(case-split (< k (expt 2 (+ m n)))) ;not a problem hyp, since k, m and n are constants
		(case-split (integerp k))
		(case-split (<= 0 k))
		(case-split (integerp m))
		(case-split (<= 0 m))
		(case-split (integerp n))
		(case-split (<= 0 n)))
	   (equal (equal k (cat_alt x m y n))
		  (and (equal y (bits_alt k (1- n) 0))
		       (equal x (bits_alt k (+ -1 m n) n)))))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance cat-equal-constant)))))

(defthmd cat_alt-equal-rewrite
  (implies (and (case-split (bvecp x1 m))
		(case-split (bvecp y1 n))
		(case-split (bvecp x2 m))
		(case-split (bvecp y2 n))
		(case-split (integerp n))
		(case-split (<= 0 n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (equal (cat_alt x1 m y1 n)
			 (cat_alt x2 m y2 n))
		  (and (equal x1 x2)
		       (equal y1 y2))))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat)
                                  ())
           :use ((:instance cat-equal-rewrite)))))

(defthm cat_alt-bits_alt-bits_alt
  (implies (and (equal j (1+ k))
		(equal n (+ 1 (- l) k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (<= l k))
		(case-split (integerp i))
		(case-split (integerp k))
		(case-split (integerp l))
		(case-split (integerp m)))
	   (equal (cat_alt (bits_alt x i j) m (bits_alt x k l) n)
		  (bits_alt x i l)))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance cat-bits-bits)))))

(defthm cat_alt-bitn_alt-bits_alt
    (implies (and (equal j (1+ k))
		  (equal n (+ 1 (- l) k))
		  (case-split (<= 1 m))
		  (case-split (<= l k))
		  (case-split (integerp j))
		  (case-split (integerp k))
		  (case-split (integerp l))
		  (case-split (integerp m)))
	     (equal (cat_alt (bitn_alt x j) m (bits_alt x k l) n)
		    (bits_alt x j l)))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bitn_alt-is-bitn
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance cat-bitn-bits)))))

(defthm cat_alt-bits_alt-bitn_alt
  (implies (and (equal j (1+ k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp m)))
	   (equal (cat_alt (bits_alt x i j) m (bitn_alt x k) 1)
		  (bits_alt x i k)))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bitn_alt-is-bitn
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance cat-bits-bitn)))))

(defthm cat_alt-bitn_alt-bitn_alt
  (implies (and (equal i (1+ j))
		(case-split (integerp i))
		(case-split (integerp j)))
	   (equal (cat_alt (bitn_alt x i) 1 (bitn_alt x j) 1)
		  (bits_alt x i j)))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits
                                   bitn_alt-is-bitn)
                                  ())
           :use ((:instance cat-bitn-bitn)))))

(defthmd bits_alt-cat_alt
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i))
		(case-split (natp j)))
	   (equal (bits_alt (cat_alt x m y n) i j)
		  (if (< i n)
		      (bits_alt y i j)
		    (if (>= j n)
			(bits_alt x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat_alt (bits_alt x (if (< i (+ m n))
					(- i n)
				      (1- m)) 0)
			    (1+ (- i n))
			    (bits_alt y (1- n) j)
			    (- n j))))))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance bits-cat)))))


(defthm bits_alt-cat_alt-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(syntaxp (quotep j))
		(natp n)
		(natp m)
		(natp i)
		(natp j))
	   (equal (bits_alt (cat_alt x m y n) i j)
		  (if (< i n)
		      (bits_alt y i j)
		    (if (>= j n)
			(bits_alt x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat_alt (bits_alt x (if (< i (+ m n))
				       (- i n)
				     (1- m)) 0)
			   (1+ (- i n))
			   (bits_alt y (1- n) j)
			   (- n j))))))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance bits-cat-constants)))))

(defthmd bitn_alt-cat_alt
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i)))
	   (equal (bitn_alt (cat_alt x m y n) i)
		  (if (< i n)
		      (bitn_alt y i)
		    (if (< i (+ m n))
		      (bitn_alt x (- i n))
		    0))))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bitn_alt-is-bitn)
                                  ())
           :use ((:instance bitn-cat)))))

(defthm bitn_alt-cat_alt-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(natp n)
		(natp m)
		(natp i))
	   (equal (bitn_alt (cat_alt x m y n) i)
		  (if (< i n)
		      (bitn_alt y i)
		    (if (< i (+ m n))
		      (bitn_alt x (- i n))
		    0))))
  :hints (("Goal" :in-theory (e/d (binary-cat_alt-is-binary-cat
                                   bitn_alt-is-bitn)
                                  ())
           :use ((:instance bitn-cat-constants)))))

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat_alt, which can't
; be changed because of the guard of bits_alt.
(defund mulcat_alt (l n x)
  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat_alt (mulcat_alt l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits_alt x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat_alt (mulcat_alt l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))


(defthmd mulcat_alt-is-mul-cat
  (equal (mulcat_alt l n x)
         (mulcat l n x))
  :hints (("Goal" :in-theory (e/d (mulcat_alt
                                   binary-cat_alt-is-binary-cat
                                   mulcat) ()))))

(defthm mulcat_alt-nonnegative-integer-type
  (and (integerp (mulcat_alt l n x))
       (<= 0 (mulcat_alt l n x)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (e/d (mulcat_alt-is-mul-cat)
                                  ())
           :use ((:instance mulcat-nonnegative-integer-type)))))


(in-theory (disable (:type-prescription mulcat_alt)))

(defthmd mulcat_alt-bits_alt
    (implies (and (integerp l)
		  (integerp x))
	     (equal (mulcat_alt l n (bits_alt x (1- l) 0))
		    (mulcat_alt l n x)))
  :hints (("Goal" :in-theory (e/d (mulcat_alt-is-mul-cat
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance mulcat-bits)))))

(defthm mulcat_alt-bvecp
  (implies (and (>= p (* l n))
		(case-split (integerp p))
		(case-split (natp l)))
	   (bvecp (mulcat_alt l n x) p))
  :hints (("Goal" :in-theory (e/d (mulcat_alt-is-mul-cat)
                                  ())
           :use ((:instance mulcat-bvecp)))))


(defthm mulcat_alt-1
    (implies (natp l)
	     (equal (mulcat_alt l 1 x)
		    (bits_alt x (1- l) 0)))
  :hints (("Goal" :in-theory (e/d (mulcat_alt-is-mul-cat
                                   bits_alt-is-bits)
                                  ())
           :use ((:instance mulcat-1)))))

(defthm mulcat_alt-0
  (equal (mulcat_alt l n 0) 0)
  :hints (("Goal" :in-theory (e/d (mulcat_alt-is-mul-cat)
                                  ())
           :use ((:instance mulcat-0)))))



(defthm mulcat_alt-n-1
  (implies (case-split (<= 0 n))
	   (equal (mulcat_alt 1 n 1)
		  (1- (expt 2 n))))
  :hints (("Goal" :in-theory (e/d (mulcat_alt-is-mul-cat)
                                  ())
           :use ((:instance mulcat-n-1)))))

(defthm bitn_alt-mulcat_alt-1
  (implies (and (< m n)
		(case-split (bvecp x 1))
		(case-split (natp m))
		(case-split (integerp n)))
	   (equal (bitn_alt (mulcat_alt 1 n x) m)
		  x))
  :hints (("Goal" :in-theory (e/d (mulcat_alt-is-mul-cat
                                   bitn_alt-is-bitn)
                                  ())
           :use ((:instance bitn-mulcat-1)))))


;; (i-am-here)  Fri Feb 13 12:04:51 2009

;; new addition.

(local
 (defthm bits-bits-times-1
   (implies (and (integerp x)
                 (integerp y)
                 (natp i))
            (= (bits (* (bits x i 0) y) i 0)
               (bits (* x y) i 0)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance mod-mod-times (a x) (b y) (n (expt 2 (1+ i)))))
            :in-theory (enable bits-mod)))))

(defthmd bits_alt-bits_alt-times
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i))
	     (equal (bits_alt (* (bits_alt x i 0) y) i 0)
                    (bits_alt (* x y) i 0)))
  :hints (("Goal" :use (bits-bits-times-1)
           :in-theory (e/d (bits_alt-is-bits) ()))))

