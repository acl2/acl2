; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; expt-helper.lisp
;;
;;
;; This book contains some messy proofs which I want to hide.
;; There is probably nothing to be gained by looking at it.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "../pass1/top"))

(local
 (include-book "default-hint"))

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

(local
 (in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
		     FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT)))

(local
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
                       ;(:REWRITE arith-functional-commutativity-of-minus-*-right)
                       ;(:REWRITE arith-functional-commutativity-of-minus-*-left)
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
                        (:REWRITE arith-exponents-add-2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun ind (x)
   (if (integerp x)
       (cond ((equal x 0) t)
	     ((equal x -1) t)
	     ((equal x 1) t)
	     ((< 0 x) (ind (- x 2)))
	     ((< x 0) (ind (+ x 2))))
       t)))

(local
 (encapsulate
  ()

  (local
   (defthm hack1a
     (implies (integerp x)
	      (integerp (+ -1 x)))))

  (local
   (defthm hack1b
     (implies (integerp x)
	      (integerp (+ x 1)))))

  (defthm odd-and-even
    (implies (and (integerp x)
		  (not (integerp (* 1/2 x))))
	     (integerp (+ -1/2 (* 1/2 x))))  ; (* 1/2 (- x 1))))
    :hints (("Goal" :induct (ind x))
	    ("Subgoal *1/5'''" :use ((:instance hack1a
						(x (+ 1/2 R)))))
	    ("Subgoal *1/4'''":use ((:instance hack1b
					       (x (+ -3/2 R))))))
    :rule-classes :type-prescription)

  ))


(encapsulate
 ()

 (local
  (defthm expt-x-2
    (implies (and (rationalp x)
		  (not (equal x 0)))
	     (< 0 (expt x 2)))))

 (local
  (defthm <-0-expt-x-2
    (implies (and (< r 0)
		  (rationalp r)
		  (integerp i))
	     (< 0 (expt (expt r i) 2)))
    :hints (("Goal" :use ((:instance expt-x-2
				     (x (expt r i))))))))

 (defthm expt-type-prescription-negative-base-even-exponent
   (implies (and (< r 0)
		 (rationalp r)
		 (integerp i)
		 (integerp (* 1/2 i)))
	    (< 0 (expt r i)))
   :rule-classes (:type-prescription :generalize)
   :hints (("Goal" :use ((:instance <-0-expt-x-2
				    (i (* 1/2 i)))))))

 (local
  (defthm reduce
    (implies (and (integerp i)
		  (rationalp r)
		  (not (equal r 0)))
	     (equal (expt r i)
		    (* r (expt r (- i 1)))))))

 (defthm expt-type-prescription-negative-base-odd-exponent
   (implies (and (< r 0)
		 (rationalp r)
		 (integerp i)
		 (not (integerp (* 1/2 i))))
	    (< (expt r i) 0))
   :rule-classes (:type-prescription :generalize)
   :hints (("Goal" :use ((:instance
			  expt-type-prescription-negative-base-even-exponent
				    (r r)
				    (i (- i 1)))
			 (:instance reduce))
	    :in-theory (disable reduce))))

 )




(local
 (in-theory (enable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
		     FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT)))

(defthm expt-negative-base-even-exponent
  (implies (and (integerp i)
		(integerp (* 1/2 i)))
	   (equal (expt (- r) i)
		  (expt r i)))
  :hints (("Goal" :induct (ind i))))

(encapsulate
 ()

 (local
  (defthm expt-negative-base-odd-exponent-hack
      (implies (and (integerp i)
                    (not (integerp (* 1/2 i))))
               (equal (expt (* -1 r) i)
                      (* -1 (expt  r i))))
    :hints (("Goal" :induct (ind i)))
    :rule-classes nil))

 (local
  (defthm hack654
      (equal (* -1 x)
             (- x))))

 (defthm expt-negative-base-odd-exponent
     (implies (and (integerp i)
                   (not (integerp (* 1/2 i))))
              (equal (expt (- r) i)
                     (- (expt  r i))))
   :hints (("Goal" :use expt-negative-base-odd-exponent-hack)))

 )