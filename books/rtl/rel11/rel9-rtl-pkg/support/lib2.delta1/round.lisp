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

(include-book "float")

(set-enforce-redundancy t)

(local (include-book "round-proofs"))


(set-inhibit-warnings "theory")
(local (in-theory nil))




;;;**********************************************************************
;;;                         Truncation
;;;**********************************************************************


(defund trunc (x n)
  (declare (xargs :guard (integerp n)
                  :verify-guards nil))
  (* (sgn x)
     (fl (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defthmd trunc-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n))
                )
           (integerp (trunc x n)))
  :rule-classes :type-prescription)

(defthmd trunc-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (trunc x n)
		    (* (sgn x)
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n))))))

(defthmd abs-trunc
  (equal (abs (trunc x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))


(defthm trunc-to-0
    (implies (and ;(rationalp x)
		  (integerp n)
		  (<= n 0))
	     (equal (trunc x n) 0)))


(defthmd sgn-trunc
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (sgn (trunc x n))
		    (sgn x))))


(defthm trunc-positive
   (implies (and (< 0 x)
                 (case-split (rationalp x))
                 (case-split (integerp n))
                 (case-split (< 0 n))
                 )
            (< 0 (trunc x n)))
   :rule-classes (:rewrite :linear))


(defthm trunc-negative
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< (trunc x n) 0))
  :rule-classes (:rewrite :linear))


(defthm trunc-0
  (equal (trunc 0 n) 0))


(defthmd trunc-minus
  (equal (trunc (* -1 x) n)
         (* -1 (trunc x n))))


(defthmd trunc-shift
  (implies (integerp n)
           (equal (trunc (* x (expt 2 k)) n)
                  (* (trunc x n) (expt 2 k)))))


(defthmd trunc-upper-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (<= (abs (trunc x n)) (abs x)))
  :rule-classes :linear)

(defthmd trunc-upper-pos
    (implies (and (<= 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (trunc x n) x))
  :rule-classes :linear)


(defthm expo-trunc
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (equal (expo (trunc x n))
                    (expo x))))


(defthmd trunc-lower-bound
    (implies (and (rationalp x)
		  (integerp n))
	     (> (abs (trunc x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear)


(defthmd trunc-lower-2
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (> (abs (trunc x n)) (* (abs x) (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthmd trunc-lower-2-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (trunc x n) (* x (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)


(defthm trunc-diff
    (implies (and (rationalp x)
		  (integerp n)
                  (> N 0))
	     (< (abs (- x (trunc x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm trunc-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- x (trunc x n)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())


(defthm trunc-exactp-a
  (exactp (trunc x n) n))


(defthm trunc-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- x (trunc x n))) (- (expo x) n)))
  :rule-classes ())


(defthm trunc-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (trunc x n))
		  (exactp x n)))
  :rule-classes ())


(defthmd trunc-exactp-c
    (implies (and (exactp a n)
		  (<= a x)
                  (rationalp x)
		  (integerp n)
		  (rationalp a))
	     (<= a (trunc x n))))


(defthmd trunc-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n))
           (<= (trunc x n) (trunc y n)))
  :rule-classes :linear)


(defthm trunc-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (- x (expt 2 (- (expo x) n)))
		(trunc x n)))
  :rule-classes ())


(defthmd trunc-trunc
    (implies (and (>= n m)
                  (integerp n)
		  (integerp m))
	     (equal (trunc (trunc x n) m)
		    (trunc x m))))


(defthm plus-trunc
    (implies (and (rationalp x)
		  (>= x 0)
		  (rationalp y)
		  (>= y 0)
		  (integerp k)
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (= (+ x (trunc y k))
		(trunc (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())


(defthm minus-trunc-1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x (+ k (- (expo x) (expo y)))))
	     (equal (- x (trunc y k))
		    (- (trunc (- y x) (+ k (- (expo (- x y)) (expo y)))))))
  :rule-classes ())


(defthm bits-trunc
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0))
           (= (trunc x k)
              (* (expt 2 (- n k))
                 (bits x (1- n) (- n k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits_alt-trunc)))))

;;; Fri Feb 13 14:02:03 2009
;;;
;;; Some truly new result.



;; (defthmd logand-expt-3-g
;;     (implies (and (integerp x)
;; 		  (natp n)
;; 		  (natp k)
;; 		  (< k n))
;; 	     (equal (logand x (+ (expt 2 n) (- (expt 2 k))))
;; 		    (* (expt 2 k) (bits x (1- n) k)))))
;;
;; (DEFTHM TRUNC-LAND
;;                       (IMPLIES (AND (>= X (EXPT 2 (1- N)))
;;                                     (< X (EXPT 2 N))
;;                                     (INTEGERP X)
;;                                     (> X 0)
;;                                     (INTEGERP M)
;;                                     (>= M N)
;;                                     (INTEGERP N)
;;                                     (> N K)
;;                                     (INTEGERP K)
;;                                     (> K 0))
;;                                (= (TRUNC X K)
;;                                   (LAND X (- (EXPT 2 M) (EXPT 2 (- N K)))
;;                                         N)))
;;                       :RULE-CLASSES NIL)

(defthm trunc-logand
  (implies (and (>= x (expt 2 (1- n)))
                (< x (expt 2 n))
                (integerp x) ;(> x 0)
                (integerp m) (>= m n)
                (integerp n) (> n k)
                (integerp k) (> k 0))
           (= (trunc x k)
              (logand x (- (expt 2 m) (expt 2 (- n k))))))
  :rule-classes ())


(defthmd trunc-split
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp m)
                (> m k)
                (integerp k)
                (> k 0))
           (equal (trunc x m)
                  (+ (trunc x k)
                     (* (expt 2 (- n m))
                        (bits x (1- (- n k)) (- n m))))))
  :hints (("Goal" :use ((:instance trunc-split_alt)))))

;;;**********************************************************************
;;;                    Rounding Away from Zero
;;;**********************************************************************


(defund away (x n)
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defthmd away-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n))
                )
           (integerp (away x n)))
  :rule-classes :type-prescription)

(defthmd away-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (away x n)
		    (* (sgn x)
		       (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n))))))

(defthmd abs-away
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (abs (away x n))
		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))))


(defthm away-to-0
  (implies (and (<= n 0)
                (rationalp x)
                (integerp n)
                )
           (equal (away x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n)))))))


(defthmd sgn-away
  (equal (sgn (away x n))
         (sgn x)))

(defthm away-positive
  (implies (and (< 0 x)
                (case-split (rationalp x))
                )
           (< 0 (away x n)))
  :rule-classes (:rewrite :linear))

(defthm away-negative
    (implies (and (< x 0)
                  (case-split (rationalp x))
                  )
	     (< (away x n) 0))
    :rule-classes (:rewrite :linear))

(defthm away-0
  (equal (away 0 n) 0))


(defthmd away-minus
  (= (away (* -1 x) n) (* -1 (away x n))))


(defthmd away-shift
    (implies (integerp n)
	     (= (away (* x (expt 2 k)) n)
		(* (away x n) (expt 2 k)))))


(defthmd away-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (abs (away x n)) (abs x)))
  :rule-classes :linear)

(defthmd away-lower-pos
    (implies (and (>= x 0)
                  (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (away x n) x))
  :rule-classes :linear)


(defthmd away-upper-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (away x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear)


(defthmd away-upper-2
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (< (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)


(defthmd away-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (away x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear)

(defthmd away-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- (away x n) x) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear)


(defthm away-expo-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (natp n))
	     (<= (abs (away x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ())


(defthmd expo-away-lower-bound
    (implies (and (rationalp x)
		  (natp n))
	     (>= (expo (away x n)) (expo x)))
  :rule-classes :linear)


(defthmd expo-away-upper-bound
    (implies (and (rationalp x)
		  (natp n))
	     (<= (expo (away x n)) (1+ (expo x))))
  :rule-classes :linear)


(defthmd expo-away
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (away x n))
                    (expo x))))


(defthm away-exactp-a
    (implies (case-split (< 0 n))
	     (exactp (away x n) n)))


(defthmd away-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- (away x n) x)) (- (expo x) n)))
  :rule-classes :linear)


(defthm away-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (away x n))
		  (exactp x n)))
  :rule-classes ())


(defthmd away-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (away x n))))


(defthmd away-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (<= x y))
	     (<= (away x n) (away y n)))
  :rule-classes :linear)


(defthm trunc-away
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (= (away x n)
		(+ (trunc x n)
		   (expt 2 (+ (expo x) 1 (- n))))))
  :rule-classes ())


(defthm away-midpoint
    (implies (and (natp n)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (away x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ())


(defthmd away-away
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (away (away x n) m)
		    (away x m))))


(defthm plus-away
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (away y k))
              (away (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())


(defthm minus-trunc-2
  (implies (and (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (< y x)
                (integerp k)
                (> k 0)
                (> (+ k (- (expo (- x y)) (expo y))) 0)
                (= n (+ k (- (expo x) (expo y)))) ;; why we need "n"??
                (exactp x (+ k (- (expo x) (expo y)))))
           (equal (- x (trunc y k))
                  (away (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :rule-classes ())

(defthm trunc-plus-minus
    (implies (and (rationalp x)
                  (rationalp y)
                  (not (= x 0))
                  (not (= y 0))
                  (not (= (+ x y) 0))
                  (integerp k)
                  (> k 0)
                  (= k1 (+ k (- (expo x) (expo y))))
                  (= k2 (+ k (expo (+ x y)) (* -1 (expo y))))
                  (exactp x k1)
                  (> k2 0))
             (equal (+ x (trunc y k))
                    (if (= (sgn (+ x y)) (sgn y))
                        (trunc (+ x y) k2)
                      (away (+ x y) k2))))
    :rule-classes ())


(defthm away-imp
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (= (away x n)
		(trunc (+ x
			  (expt 2 (- (1+ (expo x)) n))
			  (- (expt 2 (- (1+ (expo x)) m))))
		       n)))
  :rule-classes ())

;;;**********************************************************************
;;;                    Unbiased Rounding
;;;**********************************************************************

(defun re (x)
  (- x (fl x)))


(defund near (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(trunc x n)
      (if (> f 1/2)
	  (away x n)
	(if (evenp z)
	    (trunc x n)
	  (away x n))))))


(defthm near-choice
    (or (= (near x n) (trunc x n))
	(= (near x n) (away x n)))
  :rule-classes ())


(defthmd sgn-near
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (near x n))
		    (sgn x))))

(defthm near-positive
    (implies (and (< 0 x)
                  (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (< 0 (near x n)))
  :rule-classes (:type-prescription :linear))

(defthmd near-negative
  (implies (and (< x 0)
                (< 0 n)
                (rationalp x)
                (integerp n)
		)
           (< (near x n) 0))
  :rule-classes (:type-prescription :linear))

(defthm near-0
  (equal (near 0 n)
         0))


(defthm near-exactp-a
    (implies (< 0 n)
	     (exactp (near x n) n)))


(defthm near-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (near x n))
		  (exactp x n)))
  :rule-classes ())


(defthmd near-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  )
	     (>= a (near x n))))


(defthmd near-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (near x n))))



(defthm expo-near
    (implies (and (rationalp x)
		  (> n 0)
                  (integerp n)
		  (not (= (abs (near x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (near x n))
                    (expo x)))
  :rule-classes ())

;;
;; druss: the following may be wrong.
;;
;; (defthm expo-near
;;     (implies (and (rationalp x)
;; 		  (natp n)
;; 		  (not (= (abs (near x n)) (expt 2 (1+ (expo x))))))
;; 	     (equal (expo (near x n))
;;                     (expo x)))
;;   :rule-classes ())


(defthm near<=away
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (near x n) (away x n)))
  :rule-classes ())


(defthm near>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (near x n) (trunc x n)))
  :rule-classes ())


(defthmd near-shift
    (implies (and (rationalp x)
                  (integerp n)
		  (integerp k))
	     (= (near (* x (expt 2 k)) n)
		(* (near x n) (expt 2 k)))))


(defthmd near-minus
  (equal (near (* -1 x) n)
         (* -1 (near x n))))



(defthm near1-a
    (implies (and (< (abs (- x (trunc x n))) ;; note the abs
                     (abs (- (away x n) x)))
                  (rationalp x)
		  (integerp n))
	     (equal (near x n)
                    (trunc x n)))
  :rule-classes ())


(defthm near1-b
  (implies (and (> (abs (- x (trunc x n)))
                   (abs (- (away x n) x)))
                (rationalp x)
                (integerp n))
           (equal (near x n)
                  (away x n)))
  :rule-classes ())


(defthm near2
    (implies (and (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (>= (abs (- x y)) (abs (- x (near x n)))))
  :rule-classes ())


(defthm near-est
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (near x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ())


(defthm near-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  ;(<= 0 x) ;; not necessary
		  (integerp n)
		  (> n 0))
	     (<= (near x n) (near y n))))

(defund near-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (near x n) (near y n)) 2)
    (expt 2 (expo y))))


(defthm near-near-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (near x n) (near y n))))
	     (and (<= x (near-witness x y n))
		  (<= (near-witness x y n) y)
		  (exactp (near-witness x y n) (1+ n))))
  :rule-classes ())


(defthm near-near
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (integerp n)
		  (integerp k)
		  (> k 0)
		  (>= n k)
		  (< 0 a)
		  (< a x)
		  (< 0 y)
		  (< y (fp+ a (1+ n)))
		  (exactp a (1+ n)))
	     (<= (near y k) (near x k)))
  :rule-classes ())


(defthm near-boundary
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (< 0 x)
		  (< x a)
		  (< a y)
		  (integerp n)
		  (> n 0)
		  (exactp a (1+ n))
		  (not (exactp a n)))
	     (< (near x n) (near y n)))
  :rule-classes ())


(defthm near-exact
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (near x n) (1- n)))
  :rule-classes ())


(defund near+ (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (trunc x n)
    (away x n)))


(defthm near+-choice
    (or (= (near+ x n) (trunc x n))
	(= (near+ x n) (away x n)))
  :rule-classes ())


(defthm near+<=away
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (near+ x n) (away x n)))
  :rule-classes ())


(defthm near+>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (near+ x n) (trunc x n)))
  :rule-classes ())


(defthmd near+-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (near+ (* x (expt 2 k)) n)
		(* (near+ x n) (expt 2 k)))))


(defthmd near+-minus
  (= (near+ (* -1 x) n) (* -1 (near+ x n))))

(defthm near+-positive
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (near+ x n) 0))
  :rule-classes :linear)

(defthm near+-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (near+ x n) 0))
  :rule-classes :linear)

(defthm near+-0
  (equal (near+ 0 n) 0))

(defthm near+-0-0
  (implies (and (case-split (< 0 n))
                (case-split (rationalp x))
                (case-split (integerp n)))
           (equal (equal (near+ x n) 0)
		  (equal x 0)))
  :rule-classes ())


(defthm sgn-near+
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (near+ x n))
		    (sgn x))))


(defthm near+-exactp-a
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (exactp (near+ x n) n)))


(defthm near+-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (near+ x n))
		  (exactp x n)))
  :rule-classes ())


(defthm near+-exactp-c
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (near+ x n))))


(defthm near+-exactp-d
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (near+ x n))))


(defthm expo-near+
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (near+ x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (near+ x n))
                    (expo x)))
  :rule-classes ())



(defthm near+1-a
    (implies (and (rationalp x)
		  (integerp n)
		  ; (> n 0) ;; not necessary
		  (< (abs (- x (trunc x n)))
                     (abs (- (away x n) x)))) ;; note the abs
	     (= (near+ x n) (trunc x n)))
  :rule-classes ())


(defthm near+1-b
    (implies (and (rationalp x)
		  (integerp n)
		  ;; (> n 0)
		  (> (abs (- x (trunc x n)))
                     (abs (- (away x n) x))))
	     (= (near+ x n) (away x n)))
  :rule-classes ())


(defthm near+2
    (implies (and  (exactp y n)
                   (rationalp x)
                   (rationalp y)
		  (integerp n)
		  (> n 0))

	     (>= (abs (- x y)) (abs (- x (near+ x n)))))
  :rule-classes ())


(defthm near+-est
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (<= (abs (- x (near+ x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ())


(defthm near+-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                ;(< 0 x)
                (natp n))
           (<= (near+ x n) (near+ y n))))


(defthm near+-midpoint
    (implies (and (rationalp x)
		  (integerp n)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (equal (near+ x n) (away x n)))
  :rule-classes ())


(defthm near-power-a
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())


(defthm near-power-b
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (trunc (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())


(defthm near+-power
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near+ x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())


(defthm near-plus
  (implies (and (exactp x (1- (+ k (- (expo x) (expo y)))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (near y k))
              (near (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())


(defthm near+-plus
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k))
           (= (+ x (near+ y k))
              (near+ (+ x y)
                    (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())


(defthm near-trunc
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (near x n)
		(if (and (exactp x (1+ n)) (not (exactp x n)))
		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
  :rule-classes ())


(defthm near+trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (= (near+ x n)
		(trunc (+ x (expt 2 (- (expo x) n))) n)))
  :rule-classes ())


(defthm near+-trunc-cor
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
                  (> n m)
		  (> m 0))
	     (= (near+ (trunc x n) m)
		(near+ x m)))
  :rule-classes ())

;;;**********************************************************************
;;;                          Sticky Rounding
;;;**********************************************************************


(defund sticky (x n)
  (cond ((exactp x (1- n)) x)
	(t (+ (trunc x (1- n))
              (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))


(defthm sgn-sticky
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (sticky x n))
		    (sgn x))))

(defthmd sticky-positive
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (> (sticky x n) 0))
  :rule-classes :linear)

(defthmd sticky-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (< (sticky x n) 0))
  :rule-classes :linear)

(defthm sticky-0
  (equal (sticky 0 n) 0))


(defthmd sticky-minus
  (equal (sticky (* -1 x) n) (* -1 (sticky x n))))


(defthm sticky-shift
    (implies (and (rationalp x)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (sticky (* (expt 2 k) x) n)
		(* (expt 2 k) (sticky x n))))
  :rule-classes ())


(defthm expo-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp n) (> n 0))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ())


(defthm sticky-exactp-a
    (implies (and (rationalp x)
		  (integerp n) (> n 0))
	     (exactp (sticky x n) n))
  :rule-classes ())


(defthm sticky-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (sticky x n))
		  (exactp x n)))
  :rule-classes ())


(defthmd sticky-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (sticky x n) (sticky y n)))
  :rule-classes :linear)


(defthm sticky-exactp-m
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
		  (> n m)
		  (> m 0))
	     (iff (exactp (sticky x n) m)
		  (exactp x m)))
  :rule-classes ())


(defthm trunc-sticky
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (trunc (sticky x n) m)
		(trunc x m)))
  :rule-classes ())


(defthm away-sticky
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (away (sticky x n) m)
		(away x m)))
  :rule-classes ())


(defthm near-sticky
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near (sticky x n) m)
		(near x m)))
  :rule-classes ())


(defthm near+-sticky
    (implies (and (rationalp x)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near+ (sticky x n) m)
		(near+ x m)))
  :rule-classes ())


(defthm sticky-sticky
    (implies (and (rationalp x)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (= (sticky (sticky x n) m)
		(sticky x m)))
  :rule-classes ())


(defthm sticky-plus
    (implies (and (rationalp x)
		  (rationalp y)
		  (not (= y 0))
		  (not (= (+ x y) 0))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ())

;;;**********************************************************************
;;;                    IEEE Rounding
;;;**********************************************************************


(defun inf (x n)
  (if (>= x 0)
      (away x n)
    (trunc x n)))


(defthmd inf-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (>= (inf x n) x))
  :rule-classes :linear)


(defun minf (x n)
  (if (>= x 0)
      (trunc x n)
    (away x n)))

(defthmd minf-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n)))
	     (<= (minf x n) x))
  :rule-classes :linear)

(defund IEEE-mode-p (mode)
  (member mode '(trunc inf minf near)))

(defun common-rounding-mode-p (mode)
  (or (IEEE-mode-p mode) (equal mode 'away) (equal mode 'near+)))

(defthmd ieee-mode-p-implies-common-rounding-mode-p
  (implies (IEEE-mode-p mode)
           (common-rounding-mode-p mode)))

(defund rnd (x mode n)
  (case mode
    (away (away x n))
    (near+ (near+ x n))
    (trunc (trunc x n))
    (inf (inf x n))
    (minf (minf x n))
    (near (near x n))
    (otherwise 0)))

(defthm rationalp-rnd
  (rationalp (rnd x mode n))
  :rule-classes (:type-prescription))


(defthm rnd-choice
  (implies (and (rationalp x)
                (integerp n)
                (common-rounding-mode-p mode))
           (or (= (rnd x mode n) (trunc x n))
	       (= (rnd x mode n) (away x n))))
  :rule-classes ())


(defthmd sgn-rnd
    (implies (and (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rnd x mode n))
		    (sgn x))))

(defthm rnd-positive
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (common-rounding-mode-p mode))
           (> (rnd x mode n) 0))
  :rule-classes (:type-prescription))

(defthm rnd-negative
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-rounding-mode-p mode))
	     (< (rnd x mode n) 0))
  :rule-classes (:type-prescription))

(defthm rnd-0
  (equal (rnd 0 mode n)
         0))

; Unlike the above, we leave the following two as rewrite rules because we may
; want to use the rewriter to relieve their hypotheses.

(defthm rnd-non-pos
    (implies (<= x 0)
	     (<= (rnd x mode n) 0))
  :rule-classes (:rewrite :type-prescription :linear))

(defthm rnd-non-neg
    (implies (<= 0 x)
	     (<= 0 (rnd x mode n)))
  :rule-classes (:rewrite :type-prescription :linear))

(defund flip (m)
  (case m
    (inf 'minf)
    (minf 'inf)
    (t m)))

(defthm ieee-mode-p-flip
    (implies (ieee-mode-p m)
	     (ieee-mode-p (flip m))))

(defthm common-rounding-mode-p-flip
    (implies (common-rounding-mode-p m)
	     (common-rounding-mode-p (flip m))))


(defthmd rnd-minus
  (equal (rnd (* -1 x) mode n)
         (* -1 (rnd x (flip mode) n))))


(defthm rnd-exactp-a
    (implies (< 0 n)
	     (exactp (rnd x mode n) n)))


(defthm rnd-exactp-b
  (implies (and (rationalp x)
                (common-rounding-mode-p mode)
                (integerp n)
                (> n 0))
           (equal (equal x (rnd x mode n))
		  (exactp x n))))


(defthmd rnd-exactp-c
    (implies (and (rationalp x)
		  (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rnd x mode n))))


(defthmd rnd-exactp-d
    (implies (and (rationalp x)
		  (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (rnd x mode n))))


(defthm rnd<=away
    (implies (and (rationalp x)
		  (>= x 0)
		  (common-rounding-mode-p mode)
		  (natp n))
	     (<= (rnd x mode n) (away x n)))
  :rule-classes ())


(defthm rnd>=trunc
    (implies (and (rationalp x)
		  (> x 0) ;;
		  (common-rounding-mode-p mode)
                  (INTEGERP N)
                  (> N 0))
	     (>= (rnd x mode n) (trunc x n)))
  :rule-classes ())


(defthmd rnd-diff
  (implies (and (rationalp x)
                (integerp n)
                (> n 0)
                (common-rounding-mode-p mode))
           (< (abs (- x (rnd x mode n))) (expt 2 (- (1+ (expo x)) n)))))


(defthm expo-rnd
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-rounding-mode-p mode)
		  (not (= (abs (rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (= (expo (rnd x mode n))
		(expo x)))
  :rule-classes ())


(defthmd rnd-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (common-rounding-mode-p mode)
                  (INTEGERP N)
                  (> N 0))
	     (<= (rnd x mode n) (rnd y mode n))))


(defthm rnd-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (common-rounding-mode-p mode)
		  (integerp k))
	     (= (rnd (* x (expt 2 k)) mode n)
		(* (rnd x mode n) (expt 2 k))))
  :rule-classes ())


(defthm plus-rnd
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y))))
                (common-rounding-mode-p mode))
           (= (+ x (rnd y mode k))
              (rnd (+ x y)
                   mode
                   (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())


(defthmd rnd-sticky
  (implies (and (common-rounding-mode-p mode)
                (rationalp x)
                (integerp m)
		(> m 0)
                (integerp n)
		(>= n (+ m 2)))
           (equal (rnd (sticky x n) mode m)
                  (rnd x mode m))))

(defun rnd-const (e mode n)
  (case mode
    ((near near+) (expt 2 (- e n)))
    ((inf away) (1- (expt 2 (1+ (- e n)))))
    (otherwise 0)))


(defthm rnd-const-thm
    (implies (and (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (rnd x mode n)
		(if (and (eql mode 'near)
			 (exactp x (1+ n))
			 (not (exactp x n)))
		    (trunc (+ x (rnd-const (expo x) mode n)) (1- n))
		  (trunc (+ x (rnd-const (expo x) mode n)) n))))
  :rule-classes ())

;;;;


(defun roundup (x mode n)
  (case mode
    (near+ (= (bitn x (- (expo x) n)) 1))
    (near (and (= (bitn x (- (expo x) n)) 1)
               (or (not (exactp x (1+ n)))
                   (= (bitn x (- (1+ (expo x)) n)) 1))))
    ((inf away) (not (exactp x n)))
    (otherwise ())))




(defthm roundup-thm
    (implies (and (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 1)
		  (integerp x)
		  (> x 0)
		  (>= (expo x) n))
	     (= (rnd x mode n)
                (if (roundup x mode n)
                    (fp+ (trunc x n) n)
                  (trunc x n))))
  :rule-classes ()
  :hints (("Goal" :use roundup_alt-thm)))



;;;**********************************************************************
;;;                         Denormal Rounding
;;;**********************************************************************


(defund drnd (x mode p q)
  (rnd x mode (+ p (expo x) (- (expo (spn q))))))


(defthmd drnd-minus
  (equal (drnd (* -1 x) mode p q)
         (* -1 (drnd x (flip mode) p q))))


(defthm drnd-exactp-a
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-rounding-mode-p mode))
           (or (drepp (drnd x mode p q) p q)
               (= (drnd x mode p q) 0)
               (= (drnd x mode p q) (* (sgn x) (spn q)))))
  :rule-classes nil)


(defthmd drnd-exactp-b
  (implies (and (rationalp x)
	        (drepp x p q)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-rounding-mode-p mode))
           (equal (drnd x mode p q)
                  x)))


(defthmd drnd-exactp-c
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
		(rationalp a)
                (drepp a p q)
		(>= a x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-rounding-mode-p mode))
           (>= a (drnd x mode p q))))


(defthmd drnd-exactp-d
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
		(rationalp a)
                (drepp a p q)
		(<= a x)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-rounding-mode-p mode))
           (<= a (drnd x mode p q))))


(defthm drnd-trunc
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (<= (abs (drnd x 'trunc p q))
               (abs x))))


(defthm drnd-away
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (>= (abs (drnd x 'away p q))
               (abs x))))


(defthm drnd-minf
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (<= (drnd x 'minf p q)
               x)))


(defthm drnd-inf
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (rationalp x)
                (<= (abs x) (spn q)))
           (>= (drnd x 'inf p q)
               x)))


(defthm drnd-diff
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (common-rounding-mode-p mode))
           (< (abs (- x (drnd x mode p q))) (spd p q))))


(defthm drnd-near-est
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp a p q))
           (>= (abs (- x a)) (abs (- x (drnd x 'near p q))))))


(defthm drnd-near+-est
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp a p q))
           (>= (abs (- x a)) (abs (- x (drnd x 'near+ p q))))))



(defthm drnd-sticky
    (implies (and (common-rounding-mode-p mode)
		  (natp p)
		  (> p 1)
		  (natp q)
		  (> q 0)
		  (rationalp x)
                  (<= (abs x) (spn q))
		  (natp n)
		  (>= n (+ p (expo x) (- (expo (spn q))) 2)))
	     (equal (drnd (sticky x n) mode p q)
		    (drnd x mode p q)))
  :rule-classes ())


(defthmd drnd-rewrite
  (implies (and (rationalp x)
                (<= (abs x) (spn q))
                (common-rounding-mode-p mode)
                (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (equal (drnd x mode p q)
                  (- (rnd (+ x (* (sgn x) (spn q))) mode p)
		     (* (sgn x) (spn q))))))




(defthmd drnd-tiny
  (implies (and (common-rounding-mode-p mode)
                (natp p)
                (> p 1)
                (natp q)
                (> q 0)
                (rationalp x)
                (< 0 x)
                (< x (/ (spd p q) 2)))
           (equal (drnd x mode p q)
                  (if (member mode '(away inf))
                      (spd p q)
                     0))))

(defthm drnd-tiny-equal
    (implies (and (common-rounding-mode-p mode)
                  (natp p)
                  (> p 1) ;;
                  (natp q)
                  (> q 0)
                  (rationalp x)
                  (< 0 x)
                  (< (abs x) (/ (spd p q) 2))
                  (rationalp y)
                  (< 0 y)
                  (< (abs y) (/ (spd p q) 2)))
             (equal (drnd x mode p q)
                    (drnd y mode p q)))
    :rule-classes nil)

