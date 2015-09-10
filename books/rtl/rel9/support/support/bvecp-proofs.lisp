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

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(local (include-book "../../arithmetic/top"))

(local (in-theory (enable expt-minus)))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defthm bvecp-with-n-not-a-positive-integer
  (implies (or (not (integerp k))
               (<= k 0))
           (equal (bvecp x k)
                  (equal 0 x)))
  :hints (("Goal" :cases ((< x 1))
           :in-theory (enable bvecp))))

(defthm bvecp-0
  (bvecp 0 k)
  :hints (("Goal" :in-theory (enable bvecp))))

;drop?
;just a special case of bvecp-with-n-not-a-positive-integer
(defthm bvecp-0-thm
  (equal (bvecp x 0)
         (equal x 0))
  :hints (("Goal" :in-theory (enable bvecp))))

(defthm bvecp-ones
  (implies (case-split (<= 0 k))
           (bvecp (1- (expt 2 k)) k))
    :hints (("goal" :in-theory (enable bvecp))))

(encapsulate
 ()
;k1 is a free var
 (local (defthm bvecp-longer-aux
          (implies (and (bvecp x k1)
                        (<= k1 k2)
                        (case-split (integerp k1))
                        (case-split (integerp k2))
                        )
                   (bvecp x k2))
          :rule-classes ((:rewrite :match-free :all))
          :hints (("Goal" :use (:instance expt-compare (lhs (expt 2 k1)) (rhs (expt 2 k2)))
                   :in-theory (set-difference-theories
                               (enable bvecp)
                               '(EXPT-COMPARE))
                   ))))
;k1 is a free var
 (defthm bvecp-longer
   (implies (and (bvecp x k1)
                 (<= k1 k2)
                 (case-split (integerp k2))
                 )
            (bvecp x k2))
   :rule-classes ((:rewrite :match-free :all))
   :hints (("Goal" :cases ((integerp k1)))))
 )

;expensive and so disabled
;no free var
(defthmd bvecp-one-longer
  (implies (and (integerp k)
                (bvecp x (- k 1)))
           (bvecp x k))
  :hints (("Goal" :in-theory (disable bvecp-longer)
           :use ((:instance bvecp-longer (k2 k) (k1 (- k 1))))))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 2))))


(defthm bvecp-of-non-integer
  (implies (not (integerp x))
           (not (bvecp x k)))
    :hints (("Goal" :in-theory (enable bvecp))))

;gen (replace n+1 with an arbitrary integer > n)?
(defthm bvecp-expt-2-n
  (implies (and (case-split (integerp n))
                (case-split (<= 0 n))
                )
           (bvecp (expt 2 n) (+ 1 n)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bvecp expt-split)
                              '(a15)))))

(defthm bvecp-if ; see comment in bvecp.lisp
  (equal (bvecp (if test x y) k)
         (if test (bvecp x k) (bvecp y k))))


; The following are analogous to mk-bvarr etc. in rtlarr.lisp.

;better name?
(defund mk-bvec (r k)
  (declare (xargs :guard (integerp k)))
  (if (bvecp r k) r 0))

(defthm mk-bvec-is-bvecp
  (bvecp (mk-bvec r k) k)
  :hints (("Goal" :in-theory (enable mk-bvec))))

(defthm mk-bvec-identity
  (implies (bvecp r k)
           (equal (mk-bvec r k) r))
  :hints (("Goal" :in-theory (enable mk-bvec))))

;BOZO make a version to shift by a constant!
(defthm bvecp-shift
  (implies (and (integerp x) ;note!
		(<= 0 m)
		(case-split (integerp m))
		(case-split (integerp n))
		)
	   (equal (bvecp (* x (expt 2 m)) n)
		  (bvecp x (- n m))))
  :hints (("Goal" :in-theory (enable bvecp expt-split))))

(defthm bvecp-shift-alt
  (implies (and (integerp x) ;note!
		(<= 0 m)
		(case-split (integerp m))
		(case-split (integerp n))
		)
	   (equal (bvecp (* (expt 2 m) x) n)
		  (bvecp x (- n m))))
  :hints (("Goal" :in-theory (enable bvecp expt-split))))

;gen this!
;BOZO will this unify (* 2 x) with 0??
(defthm bvecp-shift-by-2
  (implies (and (syntaxp (not (quotep x))) ;prevents loops...
                (integerp x)
		(<= 0 m) ;gen?
		(case-split (integerp m))
		(case-split (integerp n))
		)
	   (equal (bvecp (* 2 x) n)
		  (bvecp x (- n 1))))
  :hints (("Goal" :in-theory (enable bvecp expt-split))))


;gen?
;in general, rewrite (bvecp k n) where k is a constant to a fact about n
(defthm bvecp-1
  (implies (and (<= 1 n)
                (integerp n))
           (bvecp 1 n))
  :hints (("Goal" :in-theory (enable bvecp))))

;n is a free variable
;Disabled since may cause expensive backchaining.
(defthmd natp-bvecp
  (implies (bvecp x n)
           (natp x))
  :hints (("Goal" :in-theory (enable bvecp)))
  :rule-classes ((:rewrite :match-free :once)))

#|
;kill this rule?
;could just open bvecp instead of using this rule?
(defthmd bvecp<=
    (implies (and (natp n) ;gen?
		  (bvecp x n))
	     (<= x (1- (expt 2 n))))
  :hints (("Goal" :in-theory (enable bvecp))))
|#

(defthmd bvecp-forward
  (implies (bvecp x k)
           (and (integerp x)
                (<= 0 x)
                (< x (expt 2 k)))) ;tigher-bound?
  :hints (("Goal" :in-theory (enable bvecp)))
  :rule-classes :forward-chaining)

(defthm bvecp-product
  (implies (and (bvecp x m)
                (bvecp y n)
                )
           (bvecp (* x y) (+ m n)))
  :rule-classes ()
  :hints (("Goal" :cases ((and (integerp m) (equal 0 y) (integerp n))
                          (and (integerp m) (equal 0 y) (not (integerp n)))
                          (and (integerp m) (not (equal 0 y)) (integerp n))
                          (and (integerp m) (not (equal 0 y)) (not (integerp n)))
                          (and (not (integerp m))(equal 0 y) (integerp n))
                          (and (not (integerp m)) (equal 0 y) (not (integerp n)))
                          (and (not (integerp m)) (not (equal 0 y)) (integerp n))
                          (and (not (integerp m)) (not (equal 0 y)) (not (integerp n)))
                          )
           :in-theory (enable bvecp natp expt-split))))

(defthmd bvecp-1-rewrite
  (equal (bvecp x 1)
	 (or (equal x 0) (equal x 1)))
  :hints (("Goal" :in-theory (enable bvecp))))

;make another for not-equal-0 implies equal-1?
(defthm bvecp-1-0
    (implies (and (bvecp x 1)
		  (not (equal x 1)))
	     (equal x 0))
  :rule-classes :forward-chaining
  :hints (("Goal" :use bvecp-1-rewrite)))


(defthm bvecp+1
    (implies (and (natp n)
		  (bvecp x n))
	     (bvecp x (+ 1 n)))
  :hints (("Goal" :in-theory (enable bvecp expt-split))))

;same as bvecp-longer.decide which param names to use.  j and k??
(defthmd bvecp-monotone
    (implies (and (bvecp x n)
		  (<= n m)
                  (case-split (integerp m))
                  )
	     (bvecp x m)))


;This bounds the amount of carry out that we can have from the sum.
(defthm bvecp-sum-of-bvecps
  (implies (and (bvecp x (1- k))
                (bvecp y (1- k))
                (case-split (integerp k)))
           (bvecp (+ x y) k))
  :hints (("Goal" :in-theory (enable bvecp expt-split)))
  )


;add rule that (not (natp x)) implies (not (bvecp x k)) ??

;exported in lib/
(defthmd bvecp-0-1
  (implies (and (bvecp x 1)
                (not (equal x 0)))
           (equal x 1))
  :rule-classes :forward-chaining)
