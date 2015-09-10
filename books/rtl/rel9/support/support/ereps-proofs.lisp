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

; Eric Smith, David Russinoff, with contributions and suggestions by Matt Kaufmann
; AMD, June 2001
;this file was previously called repsproofs.lisp
;perhaps the more hierarchical defns (e.g., erepp2) should be exported

(include-book "rtl")
(include-book "float") ;to get the defns...

; bias of a q bit exponent field is 2^(q-1)-1
(defund bias (q) (- (expt 2 (- q 1)) 1) )

(local (include-book "bias"))
(local (include-book "merge"))
(local (include-book "cat"))
(local (include-book "bvecp"))
(local (include-book "bits"))
(local (include-book "bitn"))
(local (include-book "../../arithmetic/top")) ;try
(include-book "mulcat")

(local (in-theory (enable bits-tail)))
(local (in-theory (disable sgn))) ;move up?
(local (in-theory (enable expt-split expt-minus)))

;;Encoding of floating-point numbers with explicit leading one:
;;bit vectors of length p+q+1, consisting of 1-bit sign field,
;;q-bit exponent field (bias = 2**(q-1)-1), and p-bit significand field.

(defund esgnf  (x p q) (bitn x (+ p q)))
(defund eexpof (x p q) (bits x (1- (+ p q)) p))
(defund esigf  (x p)   (bits x (1- p) 0))

;;;**********************************************************************
;;;                       REPRESENTABLE NUMBERS
;;;**********************************************************************

(defund erepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (bvecp (+ (expo x) (bias q)) q)
       (exactp x p)))


;;;**********************************************************************
;;;                      VALID ENCODINGS
;;;**********************************************************************

(defund eencodingp (x p q)
  (and (bvecp x (+ p q 1))
       (= (bitn x (- p 1)) 1)))

; sig, expo, and sgn are defined in float.lisp
(defund eencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
	    (+ (expo x) (bias q))
	    q)
       (1+ q)
       (* (sig x) (expt 2 (- p 1)))
       p) )

(defund edecode (x p q)
  (* (if (= (esgnf x p q) 0) 1 -1)
     (esigf x p)
     (expt 2 (+ 1 (- p) (eexpof x p q) (- (bias q))))))

;BOZO move.  handle this better
(defthm cancel-hack
  (implies (and (not (equal 0 y))
                (rationalp x)
                (rationalp y)
                (rationalp w)
                (rationalp z))
                (equal (EQUAL 0 (+ (* X y) (* w y z)))
                       (EQUAL 0 (+ x (* w z)))))
  :hints (("Goal" :in-theory (disable ACL2::CANCEL_TIMES-EQUAL-CORRECT)
           :use (:instance  mult-both-sides-of-equal (c y) (a 0) (b (+ x (* w z)))))))

(defthm edecode-eencode
  (implies (and (erepp x p q)
                (integerp p)
;                (>= p 0)
                (integerp q)
;                (>= q 0) ;gen!
                )
           (equal (edecode (eencode x p q) p q)
                  x))
  :hints (("Goal" :in-theory (enable only-0-is-0-or-negative-exact
                                     edecode eencode erepp esgnf eexpof esigf sgn bits-minus-alt))))

(defthm eencode-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (>= p 0)
                (integerp q)
                (> q 0)
                )
           (equal (eencode (edecode x p q) p q)
                  x))
  :otf-flg t
  :hints (("Goal" :in-theory (enable bvecp-forward
                                     bitn-negative-bit-of-integer
                                     edecode eencode esigf eexpof eencodingp esgnf sgn cat-split-equality))))

(defthm erepp-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (erepp (edecode x p q) p q))
  :hints (("Goal" :in-theory (enable erepp edecode eencodingp esigf eexpof esgnf))))

(defthm eencodingp-eencode
  (implies (and (erepp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (eencodingp (eencode x p q) p q) )
  :hints (("Goal" :in-theory (e/d (eencodingp eencode erepp sgn bitn-shift-eric) ()))))

(defthm expo-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (equal (expo (edecode x p q))
                  (- (eexpof x p q) (bias q))
                  ))
  :hints (("Goal" :in-theory (enable edecode eexpof esigf esgnf eencodingp))))

(defthm sig-edecode
  (implies (and (eencodingp  x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (equal (sig (edecode x p q))
                  (/ (esigf x p) (expt 2 (- p 1)))))
  :hints (("Goal" :in-theory (enable sig esigf eexpof edecode esgnf eencodingp))))

(defthm sgn-edecode
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (equal (sgn (edecode  x p q))
                  (if (= (esgnf x p q) 0) 1 -1)))
  :hints (("Goal" :in-theory (enable sgn edecode esgnf esigf eencodingp))))

(defthm eencodingp-not-zero
  (implies (and (eencodingp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 0))
           (not (equal (edecode x p q) 0)))
  :hints (("Goal" :in-theory (enable eencodingp edecode esigf esgnf))))


;Rebiasing proofs:

(defund rebias-expo (expo old new)
  (+ expo (- (bias new) (bias old))))

(defthm natp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (natp (rebias-expo x m n)))
    :hints (("goal" :in-theory (e/d ( expt-split rebias-expo bvecp natp bias
                                                  ) (expt-compare))
		  :use (:instance expt-weak-monotone (n m) (m n)))))

(defthm natp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (natp (rebias-expo x n m)))
    :hints (("goal" :in-theory (enable rebias-expo bvecp natp bias))))


(defthm bvecp-rebias-up
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x m))
	     (bvecp (rebias-expo x m n) n))
  :hints (("goal" :in-theory (e/d ( ;expt
                                   expt-split
                                     rebias-expo bvecp bias)
                                  (expt-compare))
		  :use (:instance expt-weak-monotone (n m) (m n)))))


(defthm bvecp-rebias-down
    (implies (and (natp n)
		  (natp m)
		  (< 0 m)
		  (<= m n)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (bvecp (rebias-expo x n m) m))
  :hints (("goal" :in-theory (enable ;expt
                              expt-split
                                     rebias-expo bvecp bias))))
(local (defthm rebias-lemma-1
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 1))
	     (< (bits x (- n 2) 0) (expt 2 (1- m))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-plus-bits (n (1- n)) (m 0)))))))

(local (defthm rebias-lemma-3
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 1))
	     (bvecp (bits x (- n 2) 0) (1- m)))
  :rule-classes ()
  :hints (("Goal" :use (rebias-lemma-1
;			rebias-lemma-2
                        )
		  :in-theory (e/d (bvecp) (BITS-SLICE-ZERO-GEN))))))

(local (defthm rebias-lemma-4
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 1))
	     (equal (bits x (- n 2) 0)
		    (bits x (- m 2) 0)))
    :rule-classes nil
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable natp)
                              '(bits-bits
                                ))
		  :use (rebias-lemma-3
			(:instance bits-bits (i (- n 2)) (j 0) (k (- m 2)) (l 0)))))))

(local (defthm rebias-lemma-5
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 1))
	     (equal x (+ (expt 2 (1- n)) (bits x (- m 2) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories (enable natp) '())
		  :use (rebias-lemma-4
			(:instance bitn-plus-bits (n (1- n)) (m 0)))))))

(local (defthm rebias-lemma-6
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 1))
	     (equal (rebias-expo x n m)
		    (cat (bitn x (1- n)) 1
			 (bits x (- m 2) 0)
			 (1- m))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rebias-expo bias cat)
		  :use (rebias-lemma-5)))))

(local (defthm rebias-lemma-7
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (equal (bits x (+ -2 n) 0)
		    x))
    :rule-classes nil
    :hints (("Goal" :use ((:instance bitn-plus-bits (n (1- n)) (m 0)))))))

(local (defthm rebias-lemma-8
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (equal (bits x (+ -2 n) 0)
		    (+ (* (expt 2 (1- m))
			  (bits x (- n 2) (1- m)))
		       (bits x (- m 2) 0))))
    :rule-classes nil
    :hints (("Goal" :use ((:instance bits-plus-bits (n (+ -2 n)) (p (1- m)) (m 0)))))))

(local (defthm rebias-lemma-9
    (implies (and ;(natp n)
		  (natp m)
		  ;(> n m)
		  (> m 1)
		  ;(bvecp x n)
                  )
	     (and (integerp (bits x (- m 2) 0))
		  (< (bits x (- m 2) 0)
		     (expt 2 (1- m)))))
  :hints (("Goal" :use ((:instance bits-bvecp (i (- m 2)) (j 0) (k (1- m))))
		  :in-theory (union-theories (disable bits-bvecp) '(bvecp natp))))))

(local (defthm rebias-lemma-10
    (implies (and (integerp x)
		  (integerp y)
		  (< x y))
	     (<= x (1- y)))
  :rule-classes ()))

(local (defthm rebias-lemma-11
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n))
	     (INTEGERP (EXPT 2 (+ -2 M))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable natp)))))


(local (defthm rebias-lemma-12
    (implies (and; (natp n)
		  (natp m)
		 ; (> n m)
		  (> m 1)
		  ;(bvecp x n)
                  )
	     (<= (bits x (- m 2) 0)
		 (1- (expt 2 (1- m)))))
  :hints (("Goal" :in-theory (union-theories (disable rebias-lemma-9 expt) '(natp))
		  :use (rebias-lemma-9
			rebias-lemma-11
			(:instance rebias-lemma-10 (x (bits x (- m 2) 0)) (y (expt 2 (1- m)))))))))

(local (defthm rebias-lemma-13
              (implies (and (natp n)
                            (natp m)
                            (> n m)
                            (> m 1)
                            (bvecp x n)
                            (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
                            (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
                            (= (bitn x (1- n)) 0))
                       (<= (bits x (+ -2 n) 0)
                           (+ (* (expt 2 (1- m))
                                 (bits x (- n 2) (1- m)))
                              (1- (expt 2 (- m 1))))))
              :rule-classes ()
              :hints (("Goal" :in-theory (disable rebias-lemma-12)
                       :use (rebias-lemma-8
                             rebias-lemma-12)))))

(local (defthm rebias-lemma-14
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (or (> (bits x (- n 2) (1- m))
		    (- (expt 2 (- n m)) 2))
		 (<= (bits x (- n 2) 0)
		     (+ (* (- (expt 2 (- n m)) 2)
			   (expt 2 (1- m)))
			(1- (expt 2 (1- m)))))))
  :rule-classes ()
  :hints (("Goal" :use (rebias-lemma-13)))))

(local (defthm rebias-lemma-15
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (or (> (bits x (- n 2) (1- m))
		    (- (expt 2 (- n m)) 2))
		 (<= (bits x (- n 2) 0)
		     (+ (- (expt 2 (- n 1))
			   (* 2 (expt 2 (1- m))))
			(1- (expt 2 (1- m)))))))
  :rule-classes ()
  :hints (("Goal" :use (rebias-lemma-14
			(:instance expt-split (r 2) (i (- n m)) (j (1- m))))))))

(local (defthm rebias-lemma-16
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (or (> (bits x (- n 2) (1- m))
		    (- (expt 2 (- n m)) 2))
		 (< (bits x (- n 2) 0)
		    (- (expt 2 (1- n)) (expt 2 (1- m))))))
  :rule-classes ()
  :hints (("goal" :use (rebias-lemma-15)))))

(local (defthm rebias-lemma-17
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (equal (< x
		     (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (< (bits x (+ -2 n) 0)
		     (- (expt 2 (1- n))
			(expt 2 (1- m))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable ;rebias-lemma-7
                              )
           :use (rebias-lemma-7)))))

(local (defthm rebias-lemma-18
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (> (bits x (- n 2) (1- m))
		(- (expt 2 (- n m)) 2)))
  :rule-classes ()
  :hints (("Goal" :use (rebias-lemma-16
			rebias-lemma-17)))))

(local (defthm rebias-lemma-19
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (and ;(integerp (bits x (- n 2) (1- m)))
		  (< (bits x (- n 2) (1- m)) (expt 2 (- n m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bvecp
                                   ) ( bits-bvecp
                                       BITS-SLICE-ZERO-GEN
                                       ))
		  :use ((:instance bits-bvecp (i (- n 2)) (j (1- m)) (k (- n m))))))))

(local (defthm rebias-lemma-20
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1))
	     (integerp (expt 2 (- n m))))
  :rule-classes ()))

(local (defthm rebias-lemma-21
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (= (bits x (- n 2) (1- m))
		(1- (expt 2 (- n m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bvecp)
                              '(;natp
                                expt-2-integerp
                                ;; Matt K.: ACL2 v2-8-alpha-12-30-03 needs two
                                ;; more rules to be disabled, as follows.  I
                                ;; haven't investigated why, but given the rule
                                ;; expt-2-integerp disabled just above, a
                                ;; reasonable explanation is that ACL2 simply
                                ;; does a better job now of using the rules
                                ;; below (to rewrite a hypothesis to T that is,
                                ;; in fact, needed).
                                EXPT-2-POSITIVE-INTEGER-TYPE ; new
                                A14 ; new
                                EXPT-QUOTIENT-INTEGERP-ALT
                                EXPT2-INTEGER
                                EXPT-SPLIT
                                POWER2-INTEGER
                                BVECP-TIGHTEN
                                LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE
                                ))
		  :use (rebias-lemma-18
			rebias-lemma-20
			rebias-lemma-19)))))

(local (defthm rebias-lemma-22
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (= x
		(+ (* (1- (expt 2 (- n m)))
		      (expt 2 (1- m)))
		   (bits x (- m 2) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable ;rebias-lemma-7
                              )
           :use (rebias-lemma-21
			rebias-lemma-7
			(:instance bits-plus-bits (n (+ -2 n)) (p (1- m)) (m 0)))))))

(local (defthm rebias-lemma-23
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (= x
		(+ (- (expt 2 (1- m)))
		   (expt 2 (1- n))
		   (bits x (- m 2) 0))))
  :rule-classes ()
  :hints (("Goal" :use (rebias-lemma-22
			(:instance expt-split (r 2) (i (- n m)) (j (1- m))))))))

(local (defthm rebias-lemma-24
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m))))
		  (= (bitn x (1- n)) 0))
	     (equal (rebias-expo x n m)
		    (cat (bitn x (1- n)) 1
			 (bits x (- m 2) 0)
			 (1- m))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rebias-expo bias cat)
		  :use (rebias-lemma-23)))))

(defthm rebias-down
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x n)
		  (< x (+ (expt 2 (1- n)) (expt 2 (1- m))))
		  (>= x (- (expt 2 (1- n)) (expt 2 (1- m)))))
	     (equal (rebias-expo x n m)
		    (cat (bitn x (1- n))
			 1
			 (bits x (- m 2) 0)
			 (1- m))))
  :rule-classes ()
  :hints (("Goal" :use (rebias-lemma-6
			rebias-lemma-24
			(:instance bitn-0-1 (n (1- n)))))))


(local (defthm rebias-up-1
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m)
		  (= (bitn x (1- m)) 1))
	     (equal (cat (cat 1 1 0 (- n m)) (+ 1 (- n m))
                          (bits x (- m 2) 0)
                          (1- m))
		    (+ (expt 2 (1- n))
		       (bits x (- m 2) 0))))
    :rule-classes ()
    :hints (("Goal" :in-theory (enable cat)
             :use ((:instance expt-split (r 2) (i (- n m)) (j (1- m))))))))

(local (defthm rebias-up-2
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m)
		  (= (bitn x (1- m)) 1))
	     (equal (cat (cat 1 1 0 (- n m)) (+ 1 (- n m))
			 (bits x (- m 2) 0)
			 (1- m))
		    (rebias-expo x m n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rebias-expo bias)
		  :use (rebias-up-1
			(:instance bitn-plus-bits (n (1- m)) (m 0)))))))

;BOZO move
(defthmd bits-of-minus-1
  (implies (and (integerp i)
                (integerp j)
                (<= j i)
                (<= 0 j)
                )
           (equal (bits -1 i j)
                  (1- (expt 2 (+ 1 i (- j))))))
  :hints (("Goal" :in-theory (enable bits))))

(local (defthm rebias-up-3
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m)
		  (= (bitn x (1- m)) 0))
	     (equal (cat (cat 0 1 (1- (expt 2 (- n m))) (- n m)) (+ 1 (- n m))
			 (bits x (- m 2) 0)
			 (1- m))
		    (rebias-expo x m n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (rebias-expo cat bias) (expt-compare)) ;BOZO investigate loopA
		  :use ((:instance bits-of-minus-1 (j 0) (i (+ -1 N (* -1 M))))
                        (:instance bitn-plus-bits (n (1- m)) (m 0))
			(:instance expt-split (r 2) (i (- n m)) (j (1- m))))))))


(defthm rebias-up
    (implies (and (natp n)
		  (natp m)
		  (> n m)
		  (> m 1)
		  (bvecp x m))
	     (equal (rebias-expo x m n)
		    (cat (cat (bitn x (1- m))
			      1
			      (mulcat 1 (- n m) (lnot (bitn x (1- m)) 1))
			      (- n m))
			 (1+ (- n m))
			 (bits x (- m 2) 0)
			 (1- m))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable bvecp-tighten ;expo-shift-eric
                                      EXPT-SPLIT
                                      BITS-BVECP-WHEN-X-IS
                                      BITS-SLICE-ZERO-GEN
                                      BITN-KNOWN-NOT-0-REPLACE-WITH-1)
		  :use (rebias-up-2
			rebias-up-3
			(:instance bitn-0-1 (n (1- m)))))))
