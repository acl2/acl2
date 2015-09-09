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

(include-book "../lib2/basic") ;; no change from rel8

(local (include-book "bits-new"))


;;;**********************************************************************
;;;				BVECP
;;;**********************************************************************


(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defthm bvecp-forward
  (implies (bvecp x k)
	   (and (integerp x)
		(<= 0 x)
		(< x (expt 2 k))))
  :rule-classes :forward-chaining)

(defthmd bvecp-monotone
    (implies (and (bvecp x n)
		  (<= n m)
		  (case-split (integerp m)))
	     (bvecp x m)))

(defthmd bvecp-shift-down
    (implies (and (bvecp x n)
		  (natp n)
		  (natp k))
	     (bvecp (fl (/ x (expt 2 k))) (- n k))))

(defthmd bvecp-shift-up
    (implies (and (bvecp x (- n k))
		  (natp k)
		  (integerp n))
	     (bvecp (* x (expt 2 k)) n)))

(defthm bvecp-product
    (implies (and (bvecp x m)
		  (bvecp y n))
	     (bvecp (* x y) (+ m n)))
  :rule-classes ())

(defthmd bvecp-1-rewrite
  (equal (bvecp x 1)
	 (or (equal x 0) (equal x 1))))

(defthm bvecp-1-0
  (implies (and (bvecp x 1)
		(not (equal x 1)))
	   (equal x 0))
  :rule-classes :forward-chaining)

(defthm bvecp-0-1
  (implies (and (bvecp x 1)
		(not (equal x 0)))
	   (equal x 1))
  :rule-classes :forward-chaining)


;;;**********************************************************************
;;;			    BITS
;;;**********************************************************************
(encapsulate ()

             (local (include-book "../../arithmetic/top"))
  (local (encapsulate ()



                      (defthmd bits-mbe-lemma-subgoal-2
                        (IMPLIES (AND (INTEGERP J)
                                      (INTEGERP I)
                                      (INTEGERP X)
                                      (< I J))
                                 (EQUAL (FL (* (/ (EXPT 2 J))
                                               (MOD X (EXPT 2 (+ 1 I)))))
                                        0)))

                      (encapsulate ()

                                   (local (encapsulate ()

                                                       (encapsulate ()
                                                                    (local (include-book "log-new"))
                                                                    (defthm bitn_alt-logand
                                                                      (implies (and (integerp x) ; (>= x 0)
                                                                                    (integerp y) ; (>= y 0)
                                                                                    (integerp n) ;
                                                                                    )
                                                                               (equal (bitn_alt (logand x y) n)
                                                                                      (logand (bitn_alt x n) (bitn_alt y n)))))


                                                                    )


                                                       (encapsulate ()
                                                                    (local (include-book "log-new"))

                                                                    (defthmd logand-1-x_alt
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

                                                                    ;;


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







                                                       (defund bvequal (v1 v2 n)
                                                         (equal (sumbits_alt v1 n)
                                                                (sumbits_alt v2 n)))


                                                       (defthm bvequal-then-equal
                                                         (implies (and (bvequal x y n)
                                                                       (bvecp x n)
                                                                       (bvecp y n)
                                                                       (natp n))
                                                                  (equal x y))
                                                         :hints (("Goal" :use ((:instance sumbits_alt-thm
                                                                                          (x x))
                                                                               (:instance sumbits_alt-thm
                                                                                          (x y)))
                                                                  :in-theory (enable bvequal)))
                                                         :rule-classes nil)



                                                       (encapsulate ()
                                                                    (local (include-book "bits-new"))
                                                                    (defthmd bitn_alt-mod
                                                                      (implies (and (< k n)
                                                                                    (integerp n)
                                                                                    (integerp k))
                                                                               (equal (bitn_alt (mod x (expt 2 n)) k)
                                                                                      (bitn_alt x k)))))



                                                       (defthmd logand-ones-g-lemma-lemma
                                                         (implies (and (<= 0 k)
                                                                       (<= k (+ -1 n))
                                                                       (integerp n)
                                                                       (> n 0)
                                                                       (integerp k))
                                                                  (equal (bitn_alt (+ -1 (expt 2 n)) k) 1))
                                                         :hints (("Goal" :in-theory (e/d (bitn_alt bits_alt
                                                                                                   expt-2-reduce-leading-constant)
                                                                                         (bits_alt-n-n-rewrite)))))


                                                       (defthmd logand-ones-g-lemma-1
                                                         (implies (and (<= 0 k)
                                                                       (<= k (+ -1 n))
                                                                       (< 0 n)
                                                                       (integerp n)
                                                                       (integerp x)
                                                                       (integerp k))
                                                                  (equal (bitn_alt (logand x (+ -1 (expt 2 n))) k)
                                                                         (bitn_alt (mod x (expt 2 n)) k)))
                                                         :hints (("Goal" :in-theory (e/d (bitn_alt-logand
                                                                                          bitn_alt-mod
                                                                                          logand-1-x_alt
                                                                                          logand-ones-g-lemma-lemma)
                                                                                         ()))))


                                                       (defthm logand-ones-bvequal
                                                         (implies (and (<= 0 k)
                                                                       (<= k n)
                                                                       (< 0 n)
                                                                       (integerp n)
                                                                       (integerp x)
                                                                       (integerp k))
                                                                  (bvequal (logand x (+ -1 (expt 2 n)))
                                                                           (mod x (expt 2 n))
                                                                           k))
                                                         :hints (("Goal" :in-theory (e/d
                                                                                     (logand-ones-g-lemma-1
                                                                                      bvequal) ()))))



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
                                     :hints (("Goal" :in-theory (e/d (logand-ones-bvequal) ())
                                              :cases ((not (and (integerp n)
                                                                (> n 0)))))
                                             ("Subgoal 2"  :use ((:instance bvequal-then-equal
                                                                            (x (logand i (+ -1 (expt 2 n))))
                                                                            (y (mod i (expt 2 n)))
                                                                            (n n))))
                                             ("Subgoal 1.1" :in-theory (enable acl2::binary-logand))))


                                   )


                      (local
                       (defthmd bits-mbe-lemma-subgoal-1-lemma-1
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
                       (defthmd bits-mbe-lemma-subgoal-1-lemma-2
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



                      (defthmd bits-mbe-lemma-subgoal-1
                        (IMPLIES (AND (INTEGERP J)
                                      (INTEGERP I)
                                      (INTEGERP X)
                                       (<= J I))
                                 (EQUAL (FL (* (/ (EXPT 2 J))
                                               (MOD X (EXPT 2 (+ 1 I)))))
                                        (LOGAND (FL (* X (EXPT 2 (* -1 J))))
                                                (+ -1 (EXPT 2 (+ 1 I (* -1 J)))))))
                        :hints (("Goal" :in-theory (e/d (bits-mbe-lemma-subgoal-1-lemma-2
                                                         bits-mbe-lemma-subgoal-1-lemma-1
                                                         ) ()))))



                      ))

  (defund bits (x i j)
    (declare (xargs :guard (and (integerp x)
                                (integerp i)
                                (integerp j))
                    :guard-hints (("Goal" :in-theory (e/d
                                                      (bits-mbe-lemma-subgoal-1
                                                       ash
                                                       bits-mbe-lemma-subgoal-2) ())))))
    (mbe :logic (if (or (not (integerp i))
                        (not (integerp j)))
                    0
                  (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
         :exec  (if (< i j)
                    0
                  (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

  )


(local
 (defthm bits_alt-is-bits
   (equal (bits_alt x i j)
          (bits x i j))
   :hints (("Goal" :in-theory (e/d (bits_alt bits) ())))))



(defthm bits-nonnegative-integerp-type
  (and (<= 0 (bits x i j))
       (integerp (bits x i j)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use ((:instance bits_alt-nonnegative-integerp-type)))))

(in-theory (disable (:type-prescription bits)))

(defthm bits-bvecp
    (implies (and (<= (+ 1 i (- j)) k)
		  (case-split (integerp k)))
	     (bvecp (bits x i j) k))
    :hints (("Goal" :use ((:instance bits_alt-bvecp)))))

;;Here is a variation of bits-bvecp that is less general but does not
;;require an integerp hypothesis:
(defthm bits-bvecp-simple
  (implies (equal k (+ 1 i (* -1 j)))
           (bvecp (bits x i j) k))
  :hints (("Goal" :use ((:instance bits_alt-bvecp-simple)))))

(defthm mod-bits-equal
  (implies (= (mod x (expt 2 (1+ i)))
	      (mod y (expt 2 (1+ i))))
	   (= (bits x i j) (bits y i j)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-bits_alt-equal)))))

(defthmd mod-bits-equal-cor
    (implies (and (integerp x)
		  (integerp n)
		  (integerp i)
		  (integerp j)
		  (< i n))
	     (equal (bits (mod x (expt 2 n)) i j)
		    (bits x i j)))
  :hints (("Goal" :use ((:instance mod-bits_alt-equal-cor)))))

(defthmd bits-mod
  (implies (and (case-split (integerp x))
		(case-split (integerp i)))
	   (equal (bits x i 0)
		  (mod x (expt 2 (1+ i)))))
  :hints (("Goal" :use ((:instance bits_alt-mod)))))

(defthmd bits-bits-sum
  (implies (and (integerp x)
                (integerp y)
                (integerp i))
	   (equal (bits (+ (bits x i 0) y) i 0)
		  (bits (+ x y) i 0)))
  :hints (("Goal" :use ((:instance bits_alt-bits_alt-sum)))))


(defthmd bits-bits-times
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i))
	     (equal (bits (* (bits x i 0) y) i 0)
                    (bits (* x y) i 0)))
  :hints (("Goal" :use ((:instance bits_alt-bits_alt-times)))))

(defthmd bits-mod-2
  (implies (and (integerp x)
                (integerp i)
                (integerp j)
                (>= i j))
           (equal (bits x (1- i) j)
                  (- (fl (/ x (expt 2 j)))
                     (* (expt 2 (- i j))
                        (fl (/ x (expt 2 i)))))))
  :hints (("Goal" :use ((:instance bits_alt-mod-2)))))

(defthm bits-neg
  (implies (and (< i 0)
                (integerp x))
           (equal (bits x i j) 0))
  :hints (("Goal" :use ((:instance bits_alt-neg)))))

(defthm bits-with-indices-in-the-wrong-order
  (implies (< i j)
	   (equal (bits x i j)
		  0))
  :hints (("Goal" :use ((:instance bits_alt-with-indices-in-the-wrong-order)))))

(defthmd bvecp-bits-0
  (implies (bvecp x j)
	   (equal (bits x i j) 0))
  :hints (("Goal" :use ((:instance bvecp-bits_alt-0)))))

(defthm bits-0
  (equal (bits 0 i j) 0)
  :hints (("Goal" :use ((:instance bits_alt-0)))))

(defthmd neg-bits-1
    (implies (and (integerp x)
		  (natp i)
		  (natp j)
		  (< x 0)
		  (>= x (- (expt 2 j)))
		  (>= i j))
	     (equal (bits x i j)
                    (+ -1 (expt 2 (+ 1 i (* -1 j))))))
  :hints (("Goal" :use ((:instance neg-bits_alt-1)))))

(defthmd bits-minus-1
    (implies (and (natp i)
		  (natp j)
		  (>= i j))
	     (equal (bits -1 i j)
                    (+ -1 (expt 2 (+ 1 i (* -1 j))))))
  :hints (("Goal" :use ((:instance bits_alt-minus-1)))))

(defthm bits-tail
  (implies (and (bvecp x (1+ i))
		(case-split (acl2-numberp i)))
	   (equal (bits x i 0) x))
  :hints (("Goal" :use ((:instance bits_alt-tail)))))

(defthm bits-tail-2
    (implies (and (integerp x)
		  (natp i)
		  (< x (expt 2 i))
		  (>= x (- (expt 2 (+ 1 i)))))
	     (equal (bits x i 0)
		    (if (>= x 0)
			x
		      (+ x (expt 2 (+ 1 i))))))
  :hints (("Goal" :use ((:instance bits_alt-tail-2)))))

(defthm bits-drop-from-minus
  (implies (and (bvecp x (1+ i))
                (bvecp y (1+ i))
                (<= y x)
		(case-split (acl2-numberp i)))
	   (equal (bits (+ x (* -1 y)) i 0)
		  (+ x (* -1 y))))
  :hints (("Goal" :use ((:instance bits_alt-drop-from-minus)))))

(defthmd bits-shift-down-1
  (implies (and (<= 0 j)
		(integerp i)
		(integerp j)
		(integerp k))
	   (equal (bits (fl (/ x (expt 2 k))) i j)
		  (bits x (+ i k) (+ j k))))
  :hints (("Goal" :use ((:instance bits_alt-shift-down-1)))))

(defthmd bits-shift-down-2
  (implies (and (integerp x)
		(natp i)
		(natp k))
	   (equal (fl (/ (bits x (+ i k) 0) (expt 2 k)))
		  (bits (fl (/ x (expt 2 k))) i 0)))
  :hints (("Goal" :use ((:instance bits_alt-shift-down-2)))))

(defthm bits-shift-up-1
  (implies (and (integerp k)
		(integerp i)
		(integerp j))
	   (equal (bits (* (expt 2 k) x) i j)
		  (bits x (- i k) (- j k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits_alt-shift-up-1)))))

(defthm bits-shift-up-2
  (implies (and (integerp x)
		(natp k)
		(integerp i))
	   (equal (* (expt 2 k) (bits x i 0))
		  (bits (* (expt 2 k) x) (+ i k) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits_alt-shift-up-2)))))

(defthmd bits-plus-mult-1
  (implies (and (bvecp x k)
		(<= k m)
		(integerp y)
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp k)))
	   (equal (bits (+ x (* y (expt 2 k))) n m)
		  (bits y (- n k) (- m k))))
  :hints (("Goal" :use ((:instance bits_alt-plus-mult-1)))))

(defthm bits-plus-mult-2
  (implies (and (< n k)
		(integerp y)
		(integerp k))
	   (equal (bits (+ x (* y (expt 2 k))) n m)
		  (bits x n m)))
  :hints (("Goal" :use ((:instance bits_alt-plus-mult-2)))))

(defthmd bits-plus-mult-2-rewrite
   (implies (and (syntaxp (quotep c))
                 (equal (mod c (expt 2 (1+ n))) 0))
            (equal (bits (+ c x) n m)
                   (bits x n m)))
  :hints (("Goal" :use ((:instance bits_alt-plus-mult-2-rewrite)))))

(defthm bits-plus-bits
    (implies (and (integerp m)
		  (integerp p)
		  (integerp n)
		  (<= m p)
		  (<= p n))
	     (= (bits x n m)
		(+ (bits x (1- p) m)
		   (* (expt 2 (- p m)) (bits x n p)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits_alt-plus-bits_alt)))))

(defthm bits-bits
  (implies (and (case-split (<= 0 l))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp l)))
	   (equal (bits (bits x i j) k l)
		  (if (<= k (- i j))
		      (bits x (+ k j) (+ l j))
		    (bits x i (+ l j)))))
  :hints (("Goal" :use ((:instance bits_alt-bits_alt)))))

;;bits-match can prove things like this:
;;(thm (implies (equal 12 (bits x 15 6))
;;		(equal 4 (bits x 8 6))))
;;See also bits-dont-match.

(defthmd bits-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(equal k (bits k2 (+ i (- j2)) (+ (- j2) j)))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits x i j))
		  t))
  :hints (("Goal" :use ((:instance bits_alt-match)))))

;;bits-dont-match can prove things like this:
;;(thm (implies (equal 7 (bits x 8 6))
;;		(not (equal 4 (bits x 15 6)))))
;;See also bits-match.

(defthmd bits-dont-match
  (implies (and (syntaxp (and (quotep i)
			      (quotep j)
			      (quotep k)))
		(equal (bits x i2 j2) k2) ;i2, j2, and k2 are free vars
		(syntaxp (and (quotep i2)
			      (quotep j2)
			      (quotep k2)))
		(<= j2 j) (<= j i) (<= i i2)
		(not (equal k (bits k2 (+ i (- j2)) (+ (- j2) j))))
		(<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
		(integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2))
	   (equal (equal k (bits x i j))
		  nil))
  :hints (("Goal" :use ((:instance bits_alt-dont-match)))))

;;
;; Thu Feb  5 10:09:26 2009: from lib2/bits.lisp
;;

(defun bitvec (x n)
   (if (bvecp x n) x 0))

;;;**********************************************************************
;;;				BITN
;;;**********************************************************************

(encapsulate ()

 (local (include-book "../../arithmetic/top"))


 (local (encapsulate ()
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
                      (defthmd bitn-mbe-subgoal-2-lemma
                        (IMPLIES (AND (INTEGERP N)
                                      (INTEGERP X)
                                      (evenp (FL (* X (EXPT 2 (* -1 N))))))
                                 (evenp (BITN_alt X N)))
                        :hints (("Goal" :in-theory (e/d (bitn_alt expt-minus
                                                                  evenp-2-factor)
                                                        (bits_alt-n-n-rewrite
                                                         bits_alt-is-bits))
                                 :use ((:instance bits_alt-mod-2
                                                  (x x)
                                                  (i (+ 1 n))
                                                  (j n))
                                       (:instance evenp-sum
                                                  (x (fl (* x (/ (expt 2 n)))))
                                                  (y (* 2 (fl (* x (/ (expt 2 (+ 1 n)))))))))))))


                     (defthmd bitn-mbe-subgoal-2
                       (IMPLIES (AND (INTEGERP N)
                                     (INTEGERP X)
                                     (evenp (FL (* X (EXPT 2 (* -1 N))))))
                                (EQUAL (BITN_alt X N) 0))
                       :hints (("Goal" :use ((:instance bitn_alt-0-1
                                                        (x x)
                                                        (n n))
                                             (:instance bitn-mbe-subgoal-2-lemma))
                                :in-theory (e/d (evenp) ()))))

                     ))

 (local (encapsulate ()
                     (local
                      (defthmd not-evenp-sum
                        (implies (and (not (evenp x))
                                      (evenp y))
                                 (not (evenp (- x y))))
                        :hints (("Goal" :in-theory (e/d (evenp) ())))))

                     (local
                      (defthmd evenp-2-factor
                        (implies (integerp x)
                                 (evenp (* 2 x)))
                        :hints (("Goal" :in-theory (e/d (evenp) ())))))


                     (local
                      (defthmd bitn-mbe-subgoal-1-lemma
                        (IMPLIES (AND (INTEGERP N)
                                      (INTEGERP X)
                                      (not (evenp (FL (* X (EXPT 2 (* -1 N)))))))
                                 (not (evenp (BITN_alt X N))))
                        :hints (("Goal" :in-theory (e/d (bitn_alt expt-minus
                                                                  evenp-2-factor)
                                                        (bits_alt-n-n-rewrite
                                                         bits_alt-is-bits))
                                 :use ((:instance bits_alt-mod-2
                                                  (x x)
                                                  (i (+ 1 n))
                                                  (j n))
                                       (:instance not-evenp-sum
                                                  (x (fl (* x (/ (expt 2 n)))))
                                                  (y (* 2 (fl (* x (/ (expt 2 (+ 1 n)))))))))))))




                     (defthmd bitn-mbe-subgoal-1
                       (IMPLIES (AND (INTEGERP N)
                                     (INTEGERP X)
                                     (NOT (evenp (FL (* X (EXPT 2 (* -1 N)))))))
                                (EQUAL (BITN_alt X N) 1))
                       :hints (("Goal" :use ((:instance bitn_alt-0-1
                                                        (x x)
                                                        (n n))
                                             (:instance bitn-mbe-subgoal-1-lemma))
                                :in-theory (e/d (evenp) ()))))
                     ))



 (defund bitn (x n)
   (declare (xargs :guard (and (integerp x)
                               (integerp n))
                   :guard-hints (("Goal" :in-theory (e/d (bitn-mbe-subgoal-1
                                                          bitn-mbe-subgoal-2
                                                          ash
                                                          ) (bits_alt-is-bits))
                                  :use ((:instance bits_alt-is-bits
                                                   (x x) (i n) (j n)))))))
   (mbe :logic (bits x n n)
        :exec  (if (evenp (ash x (- n))) 0 1)))

 )


(local
 (defthm bitn_alt-is-bitn
   (equal (bitn_alt x n)
          (bitn x n))
   :hints (("Goal" :in-theory (e/d (bitn_alt bitn) ())))))


(defthm bitn-nonnegative-integer
  (and (integerp (bitn x n))
       (<= 0 (bitn x n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use ((:instance bitn_alt-nonnegative-integer)))))

(in-theory (disable (:type-prescription bitn)))

(defthm bits-n-n-rewrite
  (equal (bits x n n)
	 (bitn x n))
  :hints (("Goal" :use ((:instance bits_alt-n-n-rewrite)))))

(defthmd bitn-def
  (implies (case-split (integerp n))
	   (equal (bitn x n)
		  (mod (fl (/ x (expt 2 n))) 2)))
  :hints (("Goal" :use ((:instance bitn_alt-def)))))

;;A recursive formulation:

(defthmd bitn-rec-0
  (implies (integerp x)
	   (equal (bitn x 0) (mod x 2)))
  :hints (("Goal" :use ((:instance bitn_alt-rec-0)))))

(defthmd bitn-rec-pos
    (implies (< 0 n)
	     (equal (bitn x n)
		    (bitn (fl (/ x 2)) (1- n))))
  :rule-classes ((:definition :controller-alist ((bitn t t))))
  :hints (("Goal" :use ((:instance bitn_alt-rec-pos)))))

;;Use this to induce case-splitting:

(defthm bitn-0-1
    (or (equal (bitn x n) 0)
	(equal (bitn x n) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn_alt-0-1)))))

(defthm bitn-bvecp
  (implies (and (<= 1 k)
		(case-split (integerp k)))
	   (bvecp (bitn x n) k))
  :hints (("Goal" :use ((:instance bitn_alt-bvecp)))))

;;The following is a special case of bitn-bvecp.
;;It is useful as a :forward-chaining rule in concert with bvecp-0-1 and
;;bvecp-1-0.
(defthm bitn-bvecp-forward
  (bvecp (bitn x n) 1)
  :rule-classes ((:forward-chaining :trigger-terms ((bitn x n))))
  :hints (("Goal" :use ((:instance bitn_alt-bvecp-forward)))))

(defthm bitn-neg
  (implies (and (< n 0)
                (integerp x))
           (equal (bitn x n) 0))
  :hints (("Goal" :use ((:instance bitn_alt-neg)))))

(defthm bitn-0
  (equal (bitn 0 k) 0)
  :hints (("Goal" :use ((:instance bitn_alt-0)))))

(defthm bitn-bvecp-1
    (implies (bvecp x 1)
	     (equal (bitn x 0) x))
  :hints (("Goal" :use ((:instance bitn_alt-bvecp-1)))))

(defthm bitn-bitn-0
    (equal (bitn (bitn x n) 0)
	   (bitn x n))
  :hints (("Goal" :use ((:instance bitn_alt-bitn_alt-0)))))

(defthmd bitn-mod
    (implies (and (< k n)
		  (integerp n)
		  (integerp k))
	     (equal (bitn (mod x (expt 2 n)) k)
		    (bitn x k)))
  :hints (("Goal" :use ((:instance bitn_alt-mod)))))

(defthm bvecp-bitn-0
    (implies (bvecp x n)
	     (equal (bitn x n) 0))
  :hints (("Goal" :use ((:instance bvecp-bitn_alt-0)))))

(defthm neg-bitn-1
    (implies (and (integerp x)
                  (integerp n)
                  (< x 0)
		  (>= x (- (expt 2 n))))
	     (equal (bitn x n) 1))
  :hints (("Goal" :use ((:instance neg-bitn_alt-1)))))

(defthmd bitn-shift
  (implies (and (integerp n)
		(integerp k))
	   (equal (bitn (* x (expt 2 k)) (+ n k))
		  (bitn x n)))
  :hints (("Goal" :use ((:instance bitn_alt-shift)))))

(defthmd bitn-shift-down
  (implies (and (natp i)
		(integerp k))
	   (equal (bitn (fl (/ x (expt 2 k))) i)
		  (bitn x (+ i k))))
  :hints (("Goal" :use ((:instance bitn_alt-shift-down)))))

(defthm bitn-bits
  (implies (and (<= k (- i j))
		(case-split (<= 0 k))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k)))
	   (equal (bitn (bits x i j) k)
		  (bitn x (+ j k))))
  :hints (("Goal" :use ((:instance bitn_alt-bits_alt)))))

(defthmd bitn-plus-bits
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits x n m)
		(+ (* (bitn x n) (expt 2 (- n m)))
		   (bits x (1- n) m))))
  :hints (("Goal" :use ((:instance bitn_alt-plus-bits_alt)))))

(defthm bits-plus-bitn
    (implies (and (<= m n)
		  (integerp m)
		  (integerp n))
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits_alt-plus-bitn_alt)))))

(defun sumbits (x n)
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn x (1- n)))
       (sumbits x (1- n)))))


(local
 (defthm sumbits_alt-is-sumbits
   (equal (sumbits_alt x n)
          (sumbits x n))))

(defthmd sumbits-bits
    (implies (and (integerp x)
		  (natp n)
		  (> n 0))
	     (equal (sumbits x n)
		    (bits x (1- n) 0)))
  :hints (("Goal" :use ((:instance sumbits_alt-bits_alt)))))

(defthmd sumbits-thm
    (implies (and (bvecp x n)
		  (natp n)
		  (> n 0))
	     (equal (sumbits x n)
		    x))
  :hints (("Goal" :use ((:instance sumbits_alt-thm)))))

; The lemmas sumbits-badguy-is-correct and sumbits-badguy-bounds, below, let
; one prove equality of two bit vectors of width k by proving each of these has
; the same value at bit i, for arbitrary i from 0 to k-1.

(defun sumbits-badguy (x y k)
  (if (zp k)
      0
    (if (not (equal (bitn x (1- k)) (bitn y (1- k))))
        (1- k)
      (sumbits-badguy x y (1- k)))))

(local
 (defthm sumbits-badguy-is-sumbits_alt-badguys
   (equal (sumbits_alt-badguy x y k)
          (sumbits-badguy x y k))))


(defthmd sumbits-badguy-is-correct
  (implies (and (bvecp x k)
                (bvecp y k)
                (equal (bitn x (sumbits-badguy x y k))
                       (bitn y (sumbits-badguy x y k)))
                (integerp k)
                (< 0 k))
           (equal (equal x y) t))
  :hints (("Goal" :use ((:instance sumbits_alt-badguy-is-correct)))))

(defthmd sumbits-badguy-bounds
  (implies (and (integerp k)
                (< 0 k))
           (let ((badguy (sumbits-badguy x y k)))
             (and (integerp badguy)
                  (<= 0 badguy)
                  (< badguy k))))
  :hints (("Goal" :use ((:instance sumbits_alt-badguy-bounds)))))

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

(defthmd sum-bitn
  (implies (and (natp n)
		(all-bits-p b n)
	        (natp k)
		(< k n))
           (equal (bitn (sum-b b n) k)
	          (nth k b)))
  :hints (("Goal" :use ((:instance sum-bitn_alt)))))

(defthmd bvecp-bitn-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
		  (natp n))
	     (equal (bitn x n) 1))
  :hints (("Goal" :use ((:instance bvecp-bitn_alt-1)))))

(defthmd bvecp-bitn-2
  (implies (and (bvecp x n)
		(< k n)
		(<= (- (expt 2 n) (expt 2 k)) x)
		(integerp n)
		(integerp k))
	   (equal (bitn x k) 1))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :use ((:instance bvecp-bitn_alt-2)))))

(defthm neg-bitn-0
    (implies (and (integerp x)
		  (natp n)
		  (< x (- (expt 2 n)))
		  (>= x (- (expt 2 (1+ n)))))
	     (equal (bitn x n) 0))
  :hints (("Goal" :use ((:instance neg-bitn_alt-0)))))

(defthm neg-bitn-2
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (< k n)
		  (< x (- (expt 2 k) (expt 2 n)))
		  (>= x (- (expt 2 n))))
	     (equal (bitn x k) 0))
  :hints (("Goal" :use ((:instance neg-bitn_alt-2)))))

(defthmd bitn-expt
    (implies (case-split (integerp n))
	     (equal (bitn (expt 2 n) n)
		    1))
  :hints (("Goal" :use ((:instance bitn_alt-expt)))))

(defthmd bitn-expt-0
  (implies (and (not (equal i n))
		(case-split (integerp i)))
	   (equal (bitn (expt 2 i) n)
		  0))
  :hints (("Goal" :use ((:instance bitn_alt-expt-0)))))

(defthm bitn-plus-expt-1
    (implies (and (rationalp x)
		  (integerp n))
	     (not (equal (bitn (+ x (expt 2 n)) n)
			 (bitn x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn_alt-plus-expt-1)))))

(defthmd bitn-plus-mult
    (implies (and (< n m)
		  (integerp m)
		  (integerp k))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn x n)))
  :hints (("Goal" :use ((:instance bitn_alt-plus-mult)))))

(defthmd bitn-plus-mult-rewrite
    (implies (and (syntaxp (quotep c))
		  (equal (mod c (expt 2 (1+ n))) 0))
	     (equal (bitn (+ c x) n)
		    (bitn x n)))
  :hints (("Goal" :use ((:instance bitn_alt-plus-mult-rewrite)))))


;;;**********************************************************************
;;;			     CAT
;;;**********************************************************************

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(local
 (defthm binary-cat_alt-is-binary-cat
   (equal (binary-cat_alt x m y n)
          (binary-cat x m y n))
   :hints (("Goal" :in-theory (e/d (binary-cat binary-cat_alt))))))


;;Definition of the macro, cat:

;;X is a list of alternating data values and sizes.  CAT-SIZE returns the
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

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))

(defthm cat-nonnegative-integer-type
  (and (integerp (cat x m y n))
       (<= 0 (cat x m y n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use ((:instance cat_alt-nonnegative-integer-type)))))

(in-theory (disable (:type-prescription binary-cat)))

(defthm cat-bvecp
  (implies (and (<= (+ m n) k)
		(case-split (integerp k)))
	   (bvecp (cat x m y n) k))
  :hints (("Goal" :use ((:instance cat_alt-bvecp)))))

(defthm cat-with-n-0
  (equal (binary-cat x m y 0)
	 (bits x (1- m) 0))
  :hints (("Goal" :use ((:instance cat_alt-with-n-0)))))

(defthm cat-with-m-0
  (equal (binary-cat x 0 y n)
	 (bits y (1- n) 0))
  :hints (("Goal" :use ((:instance cat_alt-with-m-0)))))

(defthm cat-0
  (implies (and (case-split (bvecp y n))
		(case-split (integerp n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (cat 0 m y n) y))
  :hints (("Goal" :use ((:instance cat_alt-0)))))

(defthmd cat-bits-1
    (equal (cat (bits x (1- m) 0) m y n)
	   (cat x m y n))
  :hints (("Goal" :use ((:instance cat_alt-bits_alt-1)))))

(defthmd cat-bits-2
    (equal (cat x m (bits y (1- n) 0) n)
	   (cat x m y n))
  :hints (("Goal" :use ((:instance cat_alt-bits_alt-2)))))

(defthm cat-associative
  (implies (and (case-split (<= (+ m n) p))
		(case-split (<= 0 m))
		(case-split (<= 0 n))
		(case-split (<= 0 q))
		(case-split (integerp m))
		(case-split (integerp n))
		(case-split (integerp p))
		(case-split (integerp q)))
	   (equal (cat (cat x m y n) p z q)
		  (cat x m (cat y n z q) (+ n q))))
  :hints (("Goal" :use ((:instance cat_alt-associative)))))

(defthmd cat-equal-constant
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
	   (equal (equal k (cat x m y n))
		  (and (equal y (bits k (1- n) 0))
		       (equal x (bits k (+ -1 m n) n)))))
  :hints (("Goal" :use ((:instance cat_alt-equal-constant)))))

(defthmd cat-equal-rewrite
  (implies (and (case-split (bvecp x1 m))
		(case-split (bvecp y1 n))
		(case-split (bvecp x2 m))
		(case-split (bvecp y2 n))
		(case-split (integerp n))
		(case-split (<= 0 n))
		(case-split (integerp m))
		(case-split (<= 0 m)))
	   (equal (equal (cat x1 m y1 n)
			 (cat x2 m y2 n))
		  (and (equal x1 x2)
		       (equal y1 y2))))
  :hints (("Goal" :use ((:instance cat_alt-equal-rewrite)))))

(defthm cat-bits-bits
  (implies (and (equal j (1+ k))
		(equal n (+ 1 (- l) k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (<= l k))
		(case-split (integerp i))
		(case-split (integerp k))
		(case-split (integerp l))
		(case-split (integerp m)))
	   (equal (cat (bits x i j) m (bits x k l) n)
		  (bits x i l)))
  :hints (("Goal" :use ((:instance cat_alt-bits_alt-bits_alt)))))

(defthm cat-bitn-bits
    (implies (and (equal j (1+ k))
		  (equal n (+ 1 (- l) k))
		  (case-split (<= 1 m))
		  (case-split (<= l k))
		  (case-split (integerp j))
		  (case-split (integerp k))
		  (case-split (integerp l))
		  (case-split (integerp m)))
	     (equal (cat (bitn x j) m (bits x k l) n)
		    (bits x j l)))
  :hints (("Goal" :use ((:instance cat_alt-bitn_alt-bits_alt)))))

(defthm cat-bits-bitn
  (implies (and (equal j (1+ k))
		(case-split (<= (+ 1 (- j) i) m))
		(case-split (<= j i))
		(case-split (integerp i))
		(case-split (integerp j))
		(case-split (integerp k))
		(case-split (integerp m)))
	   (equal (cat (bits x i j) m (bitn x k) 1)
		  (bits x i k)))
  :hints (("Goal" :use ((:instance cat_alt-bits_alt-bitn_alt)))))

(defthm cat-bitn-bitn
  (implies (and (equal i (1+ j))
		(case-split (integerp i))
		(case-split (integerp j)))
	   (equal (cat (bitn x i) 1 (bitn x j) 1)
		  (bits x i j)))
  :hints (("Goal" :use ((:instance cat_alt-bitn_alt-bitn_alt)))))

(defthmd bits-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i))
		(case-split (natp j)))
	   (equal (bits (cat x m y n) i j)
		  (if (< i n)
		      (bits y i j)
		    (if (>= j n)
			(bits x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat (bits x (if (< i (+ m n))
					(- i n)
				      (1- m)) 0)
			    (1+ (- i n))
			    (bits y (1- n) j)
			    (- n j))))))
  :hints (("Goal" :use ((:instance bits_alt-cat_alt)))))

(defthm bits-cat-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(syntaxp (quotep j))
		(natp n)
		(natp m)
		(natp i)
		(natp j))
	   (equal (bits (cat x m y n) i j)
		  (if (< i n)
		      (bits y i j)
		    (if (>= j n)
			(bits x (if (< i (+ m n))
				    (- i n)
				  (1- m))
			      (- j n))
		      (cat (bits x (if (< i (+ m n))
				       (- i n)
				     (1- m)) 0)
			   (1+ (- i n))
			   (bits y (1- n) j)
			   (- n j))))))
  :hints (("Goal" :use ((:instance bits_alt-cat_alt-constants)))))

(defthmd bitn-cat
  (implies (and (case-split (natp n))
		(case-split (natp m))
		(case-split (natp i)))
	   (equal (bitn (cat x m y n) i)
		  (if (< i n)
		      (bitn y i)
		    (if (< i (+ m n))
		      (bitn x (- i n))
		    0))))
  :hints (("Goal" :use ((:instance bitn_alt-cat_alt)))))

(defthm bitn-cat-constants
  (implies (and (syntaxp (quotep n))
		(syntaxp (quotep m))
		(syntaxp (quotep i))
		(natp n)
		(natp m)
		(natp i))
	   (equal (bitn (cat x m y n) i)
		  (if (< i n)
		      (bitn y i)
		    (if (< i (+ m n))
		      (bitn x (- i n))
		    0))))
  :hints (("Goal" :use ((:instance bitn_alt-cat_alt-constants)))))

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits.

(local (include-book "../../arithmetic/top"))

(defund mulcat (l n x)
  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat (mulcat l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))

(local
 (defthm mulcat_alt-is-mulcat
   (equal (mulcat_alt l n x)
          (mulcat l n x))
   :hints (("Goal" :in-theory (e/d (mulcat_alt mulcat) ())))))


(defthm mulcat-nonnegative-integer-type
  (and (integerp (mulcat l n x))
       (<= 0 (mulcat l n x)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :use ((:instance mulcat_alt-nonnegative-integer-type)))))

(in-theory (disable (:type-prescription mulcat)))

(defthmd mulcat-bits
    (implies (and (integerp l)
		  (integerp x))
	     (equal (mulcat l n (bits x (1- l) 0))
		    (mulcat l n x)))
  :hints (("Goal" :use ((:instance mulcat_alt-bits_alt)))))

(defthm mulcat-bvecp
  (implies (and (>= p (* l n))
		(case-split (integerp p))
		(case-split (natp l)))
	   (bvecp (mulcat l n x) p))
  :hints (("Goal" :use ((:instance mulcat_alt-bvecp)))))

(defthm mulcat-1
    (implies (natp l)
	     (equal (mulcat l 1 x)
		    (bits x (1- l) 0)))
  :hints (("Goal" :use ((:instance mulcat_alt-1)))))

(defthm mulcat-0
  (equal (mulcat l n 0) 0)
  :hints (("Goal" :use ((:instance mulcat_alt-0)))))

(defthm mulcat-n-1
  (implies (case-split (<= 0 n))
	   (equal (mulcat 1 n 1)
		  (1- (expt 2 n))))
  :hints (("Goal" :use ((:instance mulcat_alt-n-1)))))


(defthm bitn-mulcat-1
  (implies (and (< m n)
		(case-split (bvecp x 1))
		(case-split (natp m))
		(case-split (integerp n)))
	   (equal (bitn (mulcat 1 n x) m)
		  x))
  :hints (("Goal" :use ((:instance bitn_alt-mulcat_alt-1)))))

