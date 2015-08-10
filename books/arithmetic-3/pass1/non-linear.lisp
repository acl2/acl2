; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; non-linear.lisp
;;
;;
;; This book contains a minimal theory for use in the non-linear
;; extension to the linear arithmetic decision procedure.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


(local (include-book "basic-arithmetic"))
(local (include-book "expt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm arith-associativity-of-*
  (equal (* (* x y) z)
	 (* x (* y z))))

(defthm arith-commutativity-of-*
  (equal (* x y)
	 (* y x)))

(defthm arith-commutativity-2-of-*
  (equal (* x y z)
	 (* y x z)))



(defthm arith-unicity-of-1
  (and (equal (* 1 x)
	      (fix x))
       (equal (* x 1)
	      (fix x))))

(defthm arith-times-zero
  (and (equal (* 0 x)
	      0)
       (equal (* x 0)
	      0)))


(defthm arith-inverse-of-*-1
  (implies (and (rationalp x) (not (equal x 0)))
	   (equal (* x (/ x))
		  1)))

(defthm arith-inverse-of-*-2
  (implies (and (rationalp x) (not (equal x 0)))
	   (equal (* x (/ x) y)
		  (fix y))))

(defthm arith-inverse-of-*-3
  (implies (and (rationalp x) (not (equal x 0)))
	   (equal (* x y (/ x))
		  (fix y))))


(defthm arith-functional-self-inversion-of-/
  (equal (/ (/ x))
	 (fix x)))

(defthm arith-distributivity-of-/-over-*
  (equal (/ (* x y))
	 (* (/ x) (/ y))))


(defthm arith-functional-commutativity-of-minus-*-right
  (equal (* x (- y))
	 (- (* x y))))

(defthm arith-functional-commutativity-of-minus-*-left
  (equal (* (- x) y)
         (- (* x y))))

(defthm arith-reciprocal-minusa
  (equal (/ (- x))
         (- (/ x))))


(defthm arith-distributivity-1
  (equal (* x (+ y z)) (+ (* x y) (* x z))))

(defthm arith-distributivity-2
  (equal (* (+ y z) x) (+ (* x y) (* x z))))

(defthm arith-fold-consts-in-*
  (implies (and (syntaxp (quotep c))
		(syntaxp (quotep d)))
	   (equal (* c d x) (* (* c d) x))))



(defthm arith-expt-0
 (and (equal (expt x 0)
	     1)
      (equal (expt 0 i)
	     (if (zip i)
		 1
	         0))))

(defthm arith-expt-1
  (and (equal (expt x 1)
	      (fix x))
       (equal (expt 1 i)
	      1)))

(defthm arith-expt-minus-1
  (equal (expt x -1)
	 (/ x)))

(defthm arith-functional-commutativity-of-expt-/
  (equal (/ (expt r i))
         (expt (/ r) i)))

(local
 (in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-EXPT-/-BASE)))

(defthm arith-expt-minus-exponent
  (equal (expt r (- i))
	 (expt (/ r) i)))

(defthm arith-expt-negative-constant-exponent
  (implies (syntaxp (quotep i))
	   (equal (expt (/ r) (* i j))
                  (expt r (* (- i) j)))))

(defthm arith-exponents-multiply
  (implies (and (integerp i)
                (integerp j))
           (equal (expt (expt r i) j)
                  (expt r (* i j)))))

(defthm arith-distributivity-of-expt-over-*
  (equal (expt (* a b) i)
         (* (expt a i)
            (expt b i))))


(defthm arith-fix-revealed
  (implies (acl2-numberp x)
	   (equal (fix x) x)))


(defthm arith-Rational-implies2
  (implies (rationalp x)
           (equal (* (numerator x) (/ (denominator x))) x)))

(defthm arith-exponents-add-1
  (implies (and (integerp i)
		(integerp j)
		(not (equal (+ i j) 0)))
	   (equal (expt r (+ i j))
		  (* (expt r i)
		     (expt r j)))))

(defthm arith-exponents-add-for-nonpos-exponentsa
  (implies (and (<= i 0)
		(<= j 0)
		(integerp i)
		(integerp j))
	   (equal (expt r (+ i j))
		  (* (expt r i)
		     (expt r j)))))

(defthm arith-exponents-add-for-nonneg-exponentsa
  (implies (and (<= 0 i)
		(<= 0 j)
		(integerp i)
		(integerp j))
	   (equal (expt r (+ i j))
		  (* (expt r i)
		     (expt r j)))))

(defthm arith-exponents-add-2
  (implies (and (not (equal 0 r))
		(acl2-numberp r)
		(integerp i)
		(integerp j))
	   (equal (expt r (+ i j))
		  (* (expt r i)
		     (expt r j)))))

(in-theory (disable arith-associativity-of-* arith-commutativity-of-*
		    arith-commutativity-2-of-* arith-unicity-of-1
		    arith-times-zero arith-inverse-of-*-1
		    arith-inverse-of-*-2 arith-inverse-of-*-3
		    arith-functional-self-inversion-of-/
		    arith-distributivity-of-/-over-*
		    arith-functional-commutativity-of-minus-*-right
		    arith-functional-commutativity-of-minus-*-left
		    arith-reciprocal-minusa arith-distributivity-1
		    arith-distributivity-2 arith-fold-consts-in-*
		    arith-expt-0
		    arith-expt-1
		    arith-expt-minus-1
		    arith-functional-commutativity-of-expt-/
		    arith-expt-minus-exponent
		    arith-expt-negative-constant-exponent
		    arith-exponents-multiply
		    arith-distributivity-of-expt-over-*
		    arith-fix-revealed arith-Rational-implies2
		    arith-exponents-add-1
		    arith-exponents-add-for-nonpos-exponentsa
		    arith-exponents-add-for-nonneg-exponentsa
		    arith-exponents-add-2))

(in-arithmetic-theory '((:REWRITE arith-associativity-of-*)
		       (:REWRITE arith-commutativity-of-*)
		       (:REWRITE arith-commutativity-2-of-*)
		       (:REWRITE arith-unicity-of-1)
		       (:REWRITE arith-times-zero)
		       (:REWRITE arith-inverse-of-*-1)
		       (:REWRITE arith-inverse-of-*-2)
		       (:REWRITE arith-inverse-of-*-3)
		       (:REWRITE arith-functional-self-inversion-of-/ )
		       (:REWRITE arith-distributivity-of-/-over-*)
		       (:REWRITE arith-functional-commutativity-of-minus-*-right)
		       (:REWRITE arith-functional-commutativity-of-minus-*-left)
		       (:REWRITE arith-reciprocal-minusa)
		       (:REWRITE arith-distributivity-1)
		       (:REWRITE arith-distributivity-2)
		       (:REWRITE arith-fold-consts-in-*)
		       (:REWRITE arith-expt-0)
		       (:REWRITE arith-expt-1)
		       (:REWRITE arith-expt-minus-1)
		       (:REWRITE arith-functional-commutativity-of-expt-/)
		       (:REWRITE arith-expt-minus-exponent)
		       (:REWRITE arith-expt-negative-constant-exponent)
		       (:REWRITE arith-exponents-multiply)
		       (:REWRITE arith-distributivity-of-expt-over-*)
		       (:REWRITE arith-fix-revealed)
		       (:REWRITE arith-Rational-implies2)
		       (:REWRITE arith-exponents-add-1)
		       (:REWRITE arith-exponents-add-for-nonpos-exponentsa)
		       (:REWRITE arith-exponents-add-for-nonneg-exponentsa)
		       (:REWRITE arith-exponents-add-2)))