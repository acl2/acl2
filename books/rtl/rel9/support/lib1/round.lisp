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

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(include-book "reps")

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))
;(set-inhibit-warnings) ; restore theory warnings (optional)


;;;**********************************************************************
;;;                            TRUNC
;;;**********************************************************************

(defund trunc (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(defthmd trunc-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (trunc x n)
		    (* (sgn x)
		       (fl (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n))))))

;replaces trunc-pos
;BOZO now a rewrite rule too; okay?
(defthm trunc-positive
   (implies (and (< 0 x)
                 (case-split (rationalp x))
                 (case-split (integerp n))
                 (case-split (< 0 n))
                 )
            (< 0 (trunc x n)))
   :rule-classes (:rewrite :linear))

;replaces trunc-neg
;BOZO now a rewrite rule too; okay?
(defthm trunc-negative
  (implies (and (< x 0)
                (case-split (rationalp x))
                (case-split (integerp n))
                (case-split (< 0 n)))
           (< (trunc x n) 0))
  :rule-classes (:rewrite :linear))

(defthm trunc-0
  (equal (trunc 0 n) 0))

(defthmd sgn-trunc
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n)
		  )
	     (equal (sgn (trunc x n))
		    (sgn x))))

(defthmd trunc-minus
  (equal (trunc (* -1 x) n)
         (* -1 (trunc x n))))

(defthmd abs-trunc
  (equal (abs (trunc x n))
         (* (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))


(defthm trunc-exactp-a
  (exactp (trunc x n) n))

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
		  (rationalp a)
		  )
	     (<= a (trunc x n))))

;we called int-trunc
(defthmd trunc-integer-type-prescription
  (implies (and (>= (expo x) n)
                (case-split (integerp n))
                )
           (integerp (trunc x n)))
  :rule-classes :type-prescription)

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

(defthmd trunc-lower-1
    (implies (and (rationalp x)
		  (integerp n))
	     (> (abs (trunc x n)) (- (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear)

(defthmd trunc-lower-pos
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (> (trunc x n) (* x (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthmd trunc-lower-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (abs (trunc x n)) (* (abs x) (- 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthmd trunc-lower-4
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (>= (trunc x n) (- x (* (abs x) (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthm trunc-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- x (trunc x n))) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm trunc-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- x (trunc x n)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes ())

(defthm trunc-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- x (trunc x n))) (- (expo x) n)))
  :rule-classes ())

(defthmd trunc-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (integerp n)
                )
           (<= (trunc x n) (trunc y n)))
  :rule-classes :linear)

(defthmd trunc-shift
  (implies (integerp n)
           (equal (trunc (* x (expt 2 k)) n)
                  (* (trunc x n) (expt 2 k)))))

(defthm expo-trunc
    (implies (and (< 0 n)
                  (rationalp x)
		  (integerp n)
		  )
	     (equal (expo (trunc x n))
                    (expo x))))

(defthmd trunc-trunc
    (implies (and (>= n m)
                  (integerp n)
		  (integerp m)
		  )
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

(defthm plus-trunc-alt
  (implies (and (exactp x (+ j (expo x) (- (expo (+ x y)))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp j))
           (= (trunc (+ x y) j)
              (+ x
                 (trunc y (+ j (- (expo (+ x y))) (expo y))))))
  :rule-classes ())

(defthmd plus-trunc-corollary
  (implies (and (< y (expt 2 (- (1+ (expo x)) n)))
                (exactp x n)
                (rationalp x)
                (> x 0)
                (rationalp y)
                (>= y 0)
                (integerp n))
           (= (trunc (+ x y) n) x)))

(defthm trunc-plus
    (implies (and (rationalp y)
		  (> y 0)
		  (integerp e)
		  (< y (expt 2 e))
		  (integerp m)
		  (> m 0)
		  (integerp k)
		  (> k 0)
		  (<= m (1+ k)))
	     (= (trunc (+ (expt 2 e) (trunc y k)) m)
		(trunc (+ (expt 2 e) y) m)))
  :rule-classes ())

(defthm trunc-n+k
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (> k 0)
		  (integerp n)
		  (>= n k)
		  ;;this isn't really needed, but it won't hurt me.
		  (not (exactp x n))
		  (= e (- (1+ (expo x)) n))
		  (= z (trunc (- x (trunc x n)) n)))
	     (= (- (trunc x (+ n k)) (trunc x n))
		(* (1- (sig (trunc (+ (expt 2 e) z) (1+ k))))
		   (expt 2 e))))
  :rule-classes ())


(defthm bits-trunc
  (implies (and (= n (1+ (expo x)))
                (>= x 0)
                (integerp k)
                (> k 0)
                )
           (= (trunc x k)
              (* (expt 2 (- n k))
                 (bits x (1- n) (- n k)))))
  :rule-classes ())

(defthm trunc-land
    (implies (and (>= x (expt 2 (1- n)))
		  (< x (expt 2 n))
                  (integerp x) (> x 0)
		  (integerp m) (>= m n)
		  (integerp n) (> n k)
		  (integerp k) (> k 0)
		  )
	     (= (trunc x k)
		(land x (- (expt 2 m) (expt 2 (- n k))) n)))
  :rule-classes ())


(defthm trunc-away-a
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (- x (expt 2 (- (expo x) n)))
		(trunc x n)))
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
                        (bits x (1- (- n k)) (- n m)))))))

;;;**********************************************************************
;;;                            AWAY
;;;**********************************************************************

(defund away (x n)
  (* (sgn x) (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(defthmd away-rewrite
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (away x n)
		    (* (sgn x)
		       (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))
		       (expt 2 (- (1+ (expo x)) n))))))

;replaces away-pos
;BOZO wasn't a rewrite rule..
(defthm away-positive
  (implies (and (< 0 x)
                (case-split (rationalp x))
                )
           (< 0 (away x n)))
  :rule-classes (:rewrite :linear))

;replaces away-neg
;BOZO wasn't a rewrite rule..
(defthm away-negative
    (implies (and (< x 0)
                  (case-split (rationalp x))
                  )
	     (< (away x n) 0))
    :rule-classes (:rewrite :linear))

(defthm away-0
  (equal (away 0 n) 0))

(defthmd sgn-away
  (equal (sgn (away x n))
         (sgn x)))

(defthmd away-minus
  (= (away (* -1 x) n) (* -1 (away x n))))

(defthmd abs-away
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (abs (away x n))
		    (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))))



(defthm away-exactp-a
    (implies (case-split (< 0 n))
	     (exactp (away x n) n)))

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
		  (rationalp a)
		  )
	     (>= a (away x n))))

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

;; ;; (defthmd expo-away-lower-bound
;; ;;     (implies (and (rationalp x)
;; ;; 		  (integerp n)
;; ;; 		  (> n 0))
;; ;; 	     (>= (expo (away x n)) (expo x)))
;; ;;   :rule-classes :linear)


(defthmd expo-away-lower-bound
    (implies (and (rationalp x)
                  (natp n))
	     (>= (expo (away x n)) (expo x)))
  :rule-classes :linear)


(defthmd away-upper-1
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

(defthmd away-upper-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
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

(defthmd away-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- (away x n) x)) (- (expo x) n)))
  :rule-classes :linear)

(defthm away-exactp-d
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ())


(defthm expo-away
    (implies (and (rationalp x)
		  (natp n)
		  (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
	     (equal (expo (away x n))
                    (expo x))))


;; (defthm expo-away
;;     (implies (and (rationalp x)
;; 		  (not (= x 0))
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
;; 	     (equal (expo (away x n))
;;                    (expo x)))
;;   :rule-classes ())


(defthmd away-monotone
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (<= x y))
	     (<= (away x n) (away y n)))
  :rule-classes :linear)

(defthmd away-shift
    (implies (integerp n)
	     (= (away (* x (expt 2 k)) n)
		(* (away x n) (expt 2 k)))))

(defthmd away-away
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (away (away x n) m)
		    (away x m))))

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

(defthm plus-away-alt
  (implies (and (exactp x (+ j (expo x) (- (expo (+ x y)))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp j))
           (= (away (+ x y) j)
              (+ x
                 (away y (+ j (- (expo (+ x y))) (expo y))))))
  :rule-classes ())

(defthmd plus-away-corollary
  (implies (and (< y (expt 2 (- (1+ (expo x)) n)))
                (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (integerp n)
                (exactp x n))
           (= (away (+ x y) n)
              (fp+ x n))))

(defthm trunc-away-b
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (away x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ())

(defthm trunc-away
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (= (away x n)
		(+ (trunc x n)
		   (expt 2 (+ (expo x) 1 (- n))))))
  :rule-classes ())

;bad name?
(defthm minus-trunc-4
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< y x)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (away (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :rule-classes ())

;BOZO move to away section?
(defthm minus-trunc-5
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (- (trunc (- y x) (+ k (- (expo (- x y)) (expo y)))))))
  :rule-classes ())


;;;**********************************************************************
;;;                            NEAR
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


(defthm near1-a
  (implies (and (< (abs (- x (trunc x n)))
                   (abs (- (away x n) x)))
                (rationalp x)
                (integerp n))
           (equal (near x n)
                  (trunc x n)))
  :rule-classes ())


(defthm near1-b
  (implies (and (> (abs (- x (trunc x n))) (abs (- (away x n) x)))
                (rationalp x)
                (integerp n))
           (equal (near x n)
                  (away x n)))
  :rule-classes ())

(defthm near-choice
    (or (= (near x n) (trunc x n))
	(= (near x n) (away x n)))
  :rule-classes ())

(defthm near-pos
    (implies (and (< 0 x)
                  (< 0 n)
                  (rationalp x)
		  (integerp n))
	     (< 0 (near x n)))
  :rule-classes (:TYPE-PRESCRIPTION :LINEAR))

(defthmd near-neg
  (implies (and (< x 0)
                (< 0 n)
                (rationalp x)
                (integerp n)
		)
           (< (near x n) 0))
  :rule-classes (:TYPE-PRESCRIPTION :LINEAR))

(defthm near-0
  (equal (near 0 n)
         0))

(defthmd sgn-near-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (near x n))
		    (sgn x))))

(defthmd near-minus
  (equal (near (* -1 x) n)
         (* -1 (near x n))))

(defthm near-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (near x n))
		  (exactp x n)))
  :rule-classes ())

(defthm near-exactp-a
    (implies (< 0 n)
	     (exactp (near x n) n)))

(defthmd near-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  ;; (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  )
	     (>= a (near x n))))

(defthmd near-exactp-d
    (implies (and (rationalp x)
		  ;;(> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (near x n))))

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

;was called monotone-near
(defthm near-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  ;; (< 0 x)
		  (integerp n)
		  (> n 0))
	     (<= (near x n) (near y n))))

(defthmd near-shift
    (implies (and (rationalp x)
                  (integerp n)
		  (integerp k))
	     (= (near (* x (expt 2 k)) n)
		(* (near x n) (expt 2 k)))))

(defthm near2
  (implies (and (exactp y n)
                (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0))
           (>= (abs (- x y)) (abs (- x (near x n)))))
  :rule-classes ())

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

(defthm near-est
    (implies (and (integerp n) (> n 0)
		  (rationalp x) )
                  ;;(> x 0))
	     (<= (abs (- x (near x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ())

(defthm near-a-a
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (>= (near x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ())

(defthm near-a-b
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (<= (near x n) a))
  :rule-classes ())

(defthm near-a-c
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (>= (near x n) a))
  :rule-classes ())

(defthm near-exact
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp n) (> n 1)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (exactp (near x n) (1- n)))
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

(defthm near-trunc
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (near x n)
		(if (and (exactp x (1+ n)) (not (exactp x n)))
		    (trunc (+ x (expt 2 (- (expo x) n))) (1- n))
		  (trunc (+ x (expt 2 (- (expo x) n))) n))))
  :rule-classes ())


;;;**********************************************************************
;;;                            NEAR+
;;;**********************************************************************

(defund near+ (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (trunc x n)
    (away x n)))

(defthm near+trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (= (near+ x n)
		(trunc (+ x (expt 2 (- (expo x) n))) n)))
  :rule-classes ())

(defthm sgn-near+-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (= (near+ x n)
		(* (sgn x) (near+ (abs x) n))))
  :rule-classes ())

(defthm sgn-near+
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (near+ x n))
		    (sgn x))))

(defthm near+-pos
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (near+ x n) 0))
  :rule-classes :linear)

;BOZO make :t-p?
(defthm near+-neg
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (near+ x n) 0))
  :rule-classes :linear)

(defthm near+-0-0
  (implies (and (case-split (< 0 n))
                (case-split (rationalp x))
                (case-split (integerp n))
                )
           (equal (equal (near+ x n) 0)
		  (equal x 0)))
  :rule-classes ())

(defthm near+-0
  (equal (near+ 0 n) 0))

(defthmd near+-minus
  (= (near+ (* -1 x) n) (* -1 (near+ x n))))

(defthmd near+-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (near+ (* x (expt 2 k)) n)
		(* (near+ x n) (expt 2 k)))))


(defthm near+-choice
    (or (= (near+ x n) (trunc x n))
	(= (near+ x n) (away x n)))
  :rule-classes ())

(defthm near+1-a
    (implies (and (rationalp x)
		  (integerp n)
 		  (< (abs (- x (trunc x n))) (abs (- (away x n) x))))
	     (= (near+ x n) (trunc x n)))
  :rule-classes ())

(defthm near+1-b
    (implies (and (rationalp x)
		  (integerp n)
 		  (> (abs (- x (trunc x n))) (abs (- (away x n) x))))
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


(defthm near+2
  (implies (and (exactp y n)
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


;was called monotone-near+

;; (defthm near+-monotone
;;   (implies (and (<= x y)
;;                 (rationalp x)
;;                 (rationalp y)
;;                 (< 0 x)
;;                 (integerp n)
;;                 (> n 0))
;;            (<= (near+ x n) (near+ y n))))

(defthm near+-monotone
   (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                ;(integerp n)
                (natp n))
           (<= (near+ x n) (near+ y n))))


(defthm near+-power
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near+ x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm near+-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (near+ x n))
		  (exactp x n)))
  :rule-classes ())

(defthm near+-exactp-a
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (exactp (near+ x n) n)))

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

;; (defthm near+-exactp-c
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (rationalp a)
;; 		  (exactp a n)
;; 		  (>= a x))
;; 	     (>= a (near+ x n))))

;; (defthm near+-exactp-d
;;     (implies (and (rationalp x)
;; 		  (> x 0)
;; 		  (integerp n)
;; 		  (> n 0)
;; 		  (rationalp a)
;; 		  (exactp a n)
;; 		  (<= a x))
;; 	     (<= a (near+ x n))))


;;;**********************************************************************
;;;                           STICKY
;;;**********************************************************************

(defund sticky (x n)
  (cond ((exactp x (1- n)) x)
	(t (+ (trunc x (1- n))
              (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))

(defthm sticky-1
  (implies (rationalp x)
           (equal (sticky x 1)
                  (* (sgn x) (expt 2 (expo x))))))

(defthmd sticky-pos
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
                  (> n 0))
	     (> (sticky x n) 0))
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

(defthm sticky-exactp
    (implies (and (rationalp x) ;; (>= x 0)
		  (integerp n) (> n 0))
	     (exactp (sticky x n) n))
  :rule-classes ())

(defthm sticky-exactp-m
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
		  (> n m)
		  (> m 0))
	     (iff (exactp (sticky x n) m)
		  (exactp x m)))
  :rule-classes ())

(defthm expo-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp n) (> n 0))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ())

(defthm trunc-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (trunc (sticky x n) m)
		(trunc x m)))
  :rule-classes ())

(defthm away-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (away (sticky x n) m)
		(away x m)))
  :rule-classes ())

(defthm away-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (away (sticky x n) m)
		(away x m)))
  :rule-classes ())


(defthm near-sticky
    (implies (and (rationalp x) ;; (> x 0)
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


(defthm sticky-plus-original ;; Fri Oct 13 14:40:05 2006
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
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

(defthm minus-sticky
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ())

(defthm sticky-lemma
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
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

(defthmd sticky-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (natp n))
           (<= (sticky x n) (sticky y n)))
  :rule-classes :linear)

;;;**********************************************************************
;;;                              ODDR
;;;**********************************************************************

;was called "odd" but that name conflicted with another function we wanted (a recursive version of oddp)
(defund oddr (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x)))))
    (if (evenp z)
	(* (sgn x) (1+ z) (expt 2 (- (1+ (expo x)) n)))
      (* (sgn x) z (expt 2 (- (1+ (expo x)) n))))))

(defthm oddr-pos
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< 0 (oddr x n)))
  :rule-classes ())

(defthm oddr>=trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (oddr x n) (trunc x n)))
  :rule-classes ())

;keep disabled..
(defthmd oddr-rewrite
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n)
		  (< 0 n))
	     (equal (oddr x n)
		    (let ((z (fl (* (expt 2 (- (1- n) (expo x))) x))))
		      (if (evenp z)
			  (* (1+ z) (expt 2 (- (1+ (expo x)) n)))
			(* z (expt 2 (- (1+ (expo x)) n))))))))

(defthm oddr-other
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 1))
	     (= (oddr x n)
		(+ (trunc x (1- n))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ())

(defthm expo-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (equal (expo (oddr x n)) (expo x))))

(defthm exactp-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (exactp (oddr x n) n))
  :rule-classes ())

(defthm not-exactp-oddr
    (implies (and (rationalp x)
		  (integerp n)
		  (> x 0)
		  (> n 1))
	     (not (exactp (oddr x n) (1- n))))
  :rule-classes ())

(defthm trunc-oddr
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (> n m))
	     (= (trunc (oddr x n) m)
		(trunc x m)))
  :rule-classes ())

(defun kp (k x y)
  (+ k (- (expo (+ x y)) (expo y))))

(defthm oddr-plus
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (> x 0)
		  (> y 0)
		  (> k 1)
		  (> (+ (1- k) (- (expo x) (expo y))) 0)
		  (exactp x (+ (1- k) (- (expo x) (expo y)))))
	     (= (+ x (oddr y k))
		(oddr (+ x y) (kp k x y))))
  :rule-classes ())

(defthm trunc-trunc-oddr
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (trunc x k) (trunc (oddr y m) k)))
  :rule-classes ())

(defthm away-away-oddr
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (away x k) (away (oddr y m) k)))
  :rule-classes ())

(defthm near-near-oddr
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp k)
		  (> x y)
		  (> y 0)
		  (> k 0)
		  (>= (- m 2) k))
	     (>= (near x k) (near (oddr y m) k)))
  :rule-classes ())


;;;**********************************************************************
;;;        IEEE Rounding (most theorems also apply to AWAY and NEAR+)
;;;**********************************************************************

(defun inf (x n)
  (if (>= x 0)
      (away x n)
    (trunc x n)))

(defun minf (x n)
  (if (>= x 0)
      (trunc x n)
    (away x n)))

(defund ieee-mode-p (mode)
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

(defthm rnd-pos
  (implies (and (< 0 x)
                (rationalp x)
                (integerp n)
                (> n 0)
                (common-rounding-mode-p mode))
           (> (rnd x mode n) 0))
  :RULE-CLASSES (:TYPE-PRESCRIPTION))

(defthm rnd-neg
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-rounding-mode-p mode))
	     (< (rnd x mode n) 0))
  :RULE-CLASSES (:TYPE-PRESCRIPTION))

(defthm rnd-0
  (equal (rnd 0 mode n)
         0))

(defthmd sgn-rnd
    (implies (and; (rationalp x)
		  (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (rnd x mode n))
		    (sgn x))))

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

;a very similar rule was called rnd-flip
;enable?
(defthmd rnd-minus
  (equal (rnd (* -1 x) mode n)
         (* -1 (rnd x (flip mode) n))))

(defthm rnd-exactp-b
  (implies (and (rationalp x)
                (common-rounding-mode-p mode)
                (integerp n)
                (> n 0))
           (equal (equal x (rnd x mode n))
		  (exactp x n))))

(defthm rnd-exactp-a
    (implies (< 0 n)
	     (exactp (rnd x mode n) n)))

(defthmd rnd-exactp-c
    (implies (and (rationalp x)
		  ;(> x 0)
		  (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (rnd x mode n))))

(defthmd rnd-exactp-d
    (implies (and (rationalp x)
		  ;(> x 0)
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
		  (> x 0)
		  (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (>= (rnd x mode n) (trunc x n)))
  :rule-classes ())


(defthmd rnd-monotone
    (implies (and (<= x y)
                  (rationalp x)
		  (rationalp y)
		  (common-rounding-mode-p mode)
                  (integerp n)
                  (> n 0))
	     (<= (rnd x mode n) (rnd y mode n))))

(defthm exactp-rnd
    (implies (and (rationalp x)
		  (common-rounding-mode-p mode)
		  (integerp n)
		  (> n 0))
	     (exactp (rnd x mode n) n)))

(defthm rnd-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (common-rounding-mode-p mode)
		  (integerp k))
	     (= (rnd (* x (expt 2 k)) mode n)
		(* (rnd x mode n) (expt 2 k))))
  :rule-classes ())

(defthm expo-rnd
    (implies (and (rationalp x)
		  ;; (not (= x 0))
		  (integerp n)
		  (> n 0)
		  (common-rounding-mode-p mode)
		  (not (= (abs (rnd x mode n))
			  (expt 2 (1+ (expo x))))))
	     (= (expo (rnd x mode n))
		(expo x)))
  :rule-classes ())

(defthm expo-rnd-bnd
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-rounding-mode-p mode))
	     (>= (expo (rnd x mode n))
		 (expo x)))
  :rule-classes ())

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

(defun roundup (x mode n)
; Returns T when we should add an ulp after truncating x to n digits.
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

(defthmd rnd-diff
  (implies (and (rationalp x)
                (integerp n)
                (> n 0)
                (common-rounding-mode-p mode))
           (< (abs (- x (rnd x mode n))) (expt 2 (- (1+ (expo x)) n)))))

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



;;;**********************************************************************
;;;                         Denormal Rounding
;;;**********************************************************************

(defund drnd-original (x mode n k)
  (- (rnd (+ x (* (sgn x) (expt 2 (- 2 (expt 2 (1- k)))))) mode n)
     (* (sgn x) (expt 2 (- 2 (expt 2 (1- k)))))))

(defthm drnd-original-0
  (equal (drnd-original 0 mode n k)
         0))

; a very similar rule was called drnd-original-flip
(defthmd drnd-original-minus
  (equal (drnd-original (* -1 x) mode n k)
         (* -1 (drnd-original x (flip mode) n k))))

(defthm drnd-original-sticky
    (implies (and (common-rounding-mode-p mode)
		  (natp n)
		  (> n 0)
		  (natp m)
		  (> m 1)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (<= (expo x) (- 1 (expt 2 (1- k))))
		  (<= (expo x) (- m (+ n (expt 2 (1- k))))))
	     (equal (drnd-original (sticky x m) mode n k)
		    (drnd-original x mode n k)))
  :rule-classes ())

(defthm drnd-original-tiny-equal
    (implies (and (ieee-mode-p m)
		  (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (< (abs x) (expt 2 (- 2 (+ n (expt 2 (1- k))))))
		  (rationalp y)
		  (< (abs y) (expt 2 (- 2 (+ n (expt 2 (1- k))))))
		  (equal (sgn x) (sgn y)))
	     (equal (drnd-original x m n k)
		    (drnd-original y m n k)))
  :rule-classes ())


(defund spn (q)
  (expt 2 (- 1 (bias q))))

;;These next three show that spn really is what it claims to be

(defthm positive-spn
  (> (spn q) 0)
  :rule-classes ( :linear))


(defthmd nrepp-spn
  (implies (and (integerp p)
                (> p 0)
                (integerp q)
                (> q 1))
           (nrepp (spn q) p q)))



(defund spd (p q)
     (expt 2 (+ 2 (- (bias q)) (- p))))

;;These next three show that spd really is what it claims to be

(defthm positive-spd
  (implies (and (integerp p)
                (> p 1)
                (> q 0))
           (> (spd p q) 0))
  :rule-classes :linear)

;; (defthm positive-spd
;;   (implies (and (integerp p)
;;                 (> p 1)
;;                 (integerp q)
;;                 (> q 0))
;;            (> (spd p q) 0))
;;     :rule-classes  :linear)

(defthm drepp-spd
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (drepp (spd p q) p q)))

(defthm smallest-spd
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp r p q))
           (>= (abs r) (spd p q))))

;DRND returns a denormal, or zero, or the smallest normal:

(defthm drnd-original-type
  (implies (and (rationalp x)
                (<= (abs x) (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (or (drepp (drnd-original x mode n k) n k)
               (= (drnd-original x mode n k) 0)
               (= (drnd-original x mode n k) (* (sgn x) (spn k)))))
  :rule-classes ())

(defthmd drnd-original-rewrite
  (implies (and (rationalp x)
                (<= (abs x) (spn k))
                (common-rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (equal (drnd-original x mode n k)
                  (rnd x
                       mode
                       (+ n
                          (- (expo (spn k)))
                          (expo x))))))

(defthm drnd-original-of-drepp-is-NOP
  (implies (and (drepp x n k)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (equal (drnd-original x mode n k)
                  x)))

(defthm drnd-original-spn-is-spn-general
  (implies (and (= (abs x) (spn k))
                (common-rounding-mode-p mode)
                (integerp n)
                (>= n 1)
                (integerp k)
                (> k 0)
                (rationalp x))
           (= (drnd-original x mode n k) x)))

(defthm drnd-original-trunc-never-goes-away-from-zero
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k)))
           (<= (abs (drnd-original x 'trunc n k))
               (abs x))))

(defthm drnd-original-away-never-goes-toward-zero
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k)))
           (>= (abs (drnd-original x 'away n k))
               (abs x))))

(defthm drnd-original-inf-never-goes-down
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k)))
           (>= (drnd-original x 'inf n k)
               x)))

(defthm drnd-original-minf-never-goes-up
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k)))
           (<= (drnd-original x 'minf n k)
               x)))

(defthm drnd-original-trunc-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k))
                (drepp a n k)
                (<= (abs a) (abs x))
                )
           (<= (abs a)
               (abs (drnd-original x 'trunc n k)))))

(defthm drnd-original-away-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k))
                (drepp a n k)
                (>= (abs a) (abs x))
                )
           (>= (abs a) (abs (drnd-original x 'away n k)))))


(defthm drnd-original-inf-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k))
                (drepp a n k)
                (>= a x))
           (>= a (drnd-original x 'inf n k))))

(defthm drnd-original-minf-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k))
                (drepp a n k)
                (<= a x))
           (<= a (drnd-original x 'minf n k))))

(defthm drnd-original-diff
  (implies (and (rationalp x)
                (<= (ABS X) (SPN K))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (< (abs (- x (drnd-original x mode n k))) (spd n k))))

(defund next-denormal (x n k)
  (+ x (spd n k)))

;;NEXT-DENORMAL behaves as expected:

(defthm denormal-spacing
  (implies (and (integerp n)
                (integerp k)
                (> k 0)
                (> n 1)
                (drepp x n k)
                (drepp x+ n k)
                (>= x 0)
                (> x+ x))
           (>= x+ (next-denormal x n k))))

(defthm no-denormal-is-closer-than-what-drnd-original-near-returns
  (implies (and (rationalp x)
                (<= (abs x) (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp a n k))
           (>= (abs (- x a)) (abs (- x (drnd-original x 'near n k))))))


