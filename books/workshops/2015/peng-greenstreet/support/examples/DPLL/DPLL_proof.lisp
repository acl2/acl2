;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

(in-package "ACL2")
(include-book "global")

(deftheory before-arith (current-theory :here))
(include-book "arithmetic/top-with-meta" :dir :system)
(deftheory after-arith (current-theory :here))

(deftheory arithmetic-book-only (set-difference-theories (theory 'after-arith) (theory 'before-arith)))

;; for the clause processor to work
(add-include-book-dir :cp "../../")
(include-book "top" :dir :cp)
(tshell-ensure)

;; functions
;; n can be a rational value when c starts from non-integer value
(defun fdco (n v0 dv g1)
  (/ (* (mu) (+ 1 (* *alpha* (+ v0 dv)))) (+ 1 (* *beta* n g1))))

(defun B-term-expt (h)
  (expt (gamma) (- h)))

(defun B-term-rest (h v0 dv g1)
  (- (* (mu) (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* (+ (* h g1) (equ-c v0)))))) 1))

(defun B-term (h v0 dv g1)
  (* (B-term-expt h) (B-term-rest h v0 dv g1)))

(defun B-sum (h_lo h_hi v0 dv g1)
  (declare (xargs :measure (if (or (not (integerp h_hi)) (not (integerp h_lo)) (< h_hi h_lo))
			       0
			       (1+ (- h_hi h_lo)))))
  (if (or (not (integerp h_hi)) (not (integerp h_lo)) (> h_lo h_hi))  0
      (+ (B-term h_hi v0 dv g1) (B-term (- h_hi) v0 dv g1) (B-sum h_lo (- h_hi 1) v0 dv g1))))

(defun B-expt (n)
  (expt (gamma) (- n 2)))

(defun B (n v0 dv g1)
  (* (B-expt n)
     (B-sum 1 (- n 2) v0 dv g1)))

;; parameter list functions
(defmacro basic-params-equal (n n-value &optional (v0 'nil) (dv 'nil) (g1 'nil) (phi0 'nil) (other 'nil))
  (list 'and
	(append
	 (append
	  (append
	   (append (list 'and
			 (list 'integerp n))
		   (if (equal g1 'nil) nil (list (list 'rationalp g1))))
	   (if (equal v0 'nil) nil (list (list 'rationalp v0))))
	  (if (equal phi0 'nil) nil (list (list 'rationalp phi0))))
	 (if (equal dv 'nil) nil (list (list 'rationalp dv))))
	(append
	 (append
	  (append
	   (append
	    (append
	     (append
	      (append
	       (append
		(list 'and
		      (list 'equal n n-value))
		(if (equal g1 'nil) nil (list (list 'equal g1 '1/3200))))
	       (if (equal v0 'nil) nil (list (list '>= v0 '9/10))))
	      (if (equal v0 'nil) nil (list (list '<= v0 '11/10))))
	     (if (equal dv 'nil) nil (list (list '>= dv (list '- (list 'dv0))))))
	    (if (equal dv 'nil) nil (list (list '<= dv (list 'dv0)))))
	   (if (equal phi0 'nil) nil (list (list '>= phi0 '0))))
	  (if (equal phi0 'nil) nil (list (list '< phi0 (list '- (list 'fdco (list '1+ (list 'm '640 v0 g1)) v0 dv g1) '1)))))
	 (if (equal other 'nil) nil (list other)))))

(defmacro basic-params (n nupper &optional (v0 'nil) (dv 'nil) (g1 'nil) (phi0 'nil) (other 'nil))
  (list 'and
	(append
	 (append
	  (append
	   (append (list 'and
			 (list 'integerp n))
		   (if (equal g1 'nil) nil (list (list 'rationalp g1))))
	   (if (equal v0 'nil) nil (list (list 'rationalp v0))))
	  (if (equal dv 'nil) nil (list (list 'rationalp dv))))
	 (if (equal phi0 'nil) nil (list (list 'rationalp phi0))))
	(append
	 (append
	 (append
	  (append
	   (append
	     (append
	      (append
	       (append
		(append (list 'and
			     (list '>= n nupper))
			(list (list '<= n '640)))
		       (if (equal g1 'nil) nil (list (list 'equal g1 '1/3200))))
	       (if (equal v0 'nil) nil (list (list '>= v0 '9/10))))
	      (if (equal v0 'nil) nil (list (list '<= v0 '11/10))))
	     (if (equal dv 'nil) nil (list (list '>= dv (list '- (list 'dv0))))))
	    (if (equal dv 'nil) nil (list (list '<= dv (list 'dv0)))))
	   (if (equal phi0 'nil) nil (list (list '>= phi0 '0))))
	  (if (equal phi0 'nil) nil (list (list '< phi0 (list '- (list 'fdco (list '1+ (list 'm '640 v0 g1)) v0 dv g1) '1)))))
	 (if (equal other 'nil) nil (list other)))))

(encapsulate ()

(local (in-theory (disable arithmetic-book-only)))

(local
(include-book "arithmetic-5/top" :dir :system)
)

(local
(defthm B-term-neg-lemma1
  (implies (basic-params h 1 v0 dv g1)
	   (< (+ (* (B-term-expt h) (B-term-rest h v0 dv g1))
	   	 (* (B-term-expt (- h)) (B-term-rest (- h) v0 dv g1)))
	      0)
	   )
  :hints
  (("Goal"
    :clause-processor
    (Smtlink clause
  			 '( (:expand ((:functions ((B-term-rest rationalp)
  						   (gamma rationalp)
  						   (mu rationalp)
  						   (equ-c rationalp)
  						   (dv0 rationalp)))
  				      (:expansion-level 1)))
  			    (:python-file "B-term-neg-lemma1") ;;mktemp
  			    (:let ((expt_gamma_h (B-term-expt h) rationalp)
  				   (expt_gamma_minus_h (B-term-expt (- h)) rationalp)))
  			    (:hypothesize ((<= expt_gamma_minus_h (/ 1 5))
					   (> expt_gamma_minus_h 0)
  					   (equal (* expt_gamma_minus_h expt_gamma_h) 1)))
			   (:use ((:let ())
				  (:hypo (()))
				  (:main ()))))
			 )
    ))
  )
)

(defthm B-term-neg
  (implies (basic-params h 1 v0 dv g1)
	   (< (+ (B-term h v0 dv g1) (B-term (- h) v0 dv g1)) 0))
  :hints (("Goal"
	   :use ( (:instance B-term)
		 (:instance B-term-neg-lemma1)
		  )))
  :rule-classes :linear)
)

(defthm B-sum-neg
  (implies (basic-params n-minus-2 1 v0 dv g1)
	   (< (B-sum 1 n-minus-2 v0 dv g1) 0))
  :hints (("Goal"
	   :in-theory (disable B-term)
	   :induct ())))

(encapsulate ()

(local ;; B = B-expt*B-sum
 (defthm B-neg-lemma1
   (implies (basic-params n 3 v0 dv g1)
	    (equal (B n v0 dv g1)
		   (* (B-expt n)
		      (B-sum 1 (- n 2) v0 dv g1))))))

(local
 (defthm B-expt->-0
   (implies (basic-params n 3)
	    (> (B-expt n) 0))
   :rule-classes :linear))

(local
 (defthm B-neg-lemma2
   (implies (and (rationalp a)
		 (rationalp b)
		 (> a 0)
		 (< b 0))
	    (< (* a b) 0))
   :rule-classes :linear))

(local
 (defthm B-neg-type-lemma3
   (implies (and (and (rationalp n-minus-2) (rationalp v0) (rationalp g1) (rationalp dv)))
	    (rationalp (B-sum 1 n-minus-2 v0 dv g1)))
   :rule-classes :type-prescription))

(local
 (defthm B-neg-type-lemma4
   (implies (basic-params n 3)
	    (rationalp (B-expt n)))
   :rule-classes :type-prescription))

(defthm B-neg
  (implies (basic-params n 3 v0 dv g1)
	   (< (B n v0 dv g1) 0))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable B-expt B-sum B-sum-neg B-expt->-0)
	   :use ((:instance B-sum-neg (n-minus-2 (- n 2)))
		 (:instance B-expt->-0)
		 (:instance B-neg-type-lemma3 (n-minus-2 (- n 2)))
		 (:instance B-neg-type-lemma4)
		 (:instance B-neg-lemma2 (a (B-expt n))
			                 (b (B-sum 1 (+ -2 n) v0 dv g1)))))))
)

(defun A (n phi0 v0 dv g1)
  (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
     (* (expt (gamma) (- (* 2 n) 2))
	(- (fdco (m n v0 g1) v0 dv g1) 1))
     (* (expt (gamma) (- (* 2 n) 3))
	(- (fdco (1+ (m n v0 g1)) v0 dv g1) 1))))

(defun phi-2n-1 (n phi0 v0 dv g1)
  (+ (A n phi0 v0 dv g1) (B n v0 dv g1)))

(defun delta (n v0 dv g1)
  (+ (- (* (expt (gamma) (* 2 n))
	   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
	(* (expt (gamma) (* 2 n)) 
	   (- (fdco (m n v0 g1) v0 dv g1) 1)))
     (- (* (expt (gamma) (- (* 2 n) 1))
	   (- (fdco (m n v0 g1) v0 dv g1) 1))
	(* (expt (gamma) (- (* 2 n) 1))
	   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
     (* (expt (gamma) (1- n))
	(+ (* (expt (gamma) (1+ (- n)))
	      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))
		 1))
	   (* (expt (gamma) (1- n))
	      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0)))))
		 1))))))

(defun delta-1 (n v0 dv g1)
  (+ (* (expt (gamma) (* 2 n))
	(- (fdco (1- (m n v0 g1)) v0 dv g1)
	   (fdco (m n v0 g1) v0 dv g1)))
     (* (expt (gamma) (- (* 2 n) 1))
	(- (fdco (m n v0 g1) v0 dv g1)
	   (fdco (1+ (m n v0 g1)) v0 dv g1)))
     (* (* (expt (gamma) (1- n)) (expt (gamma) (1+ (- n))))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
     (* (* (expt (gamma) (1- n)) (expt (gamma) (1- n)))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))

(defun delta-2 (n v0 dv g1)
  (+ (* (expt (gamma) (* 2 n))
	(- (fdco (1- (m n v0 g1)) v0 dv g1)
	   (fdco (m n v0 g1) v0 dv g1)))
     (* (expt (gamma) (- (* 2 n) 1))
	(- (fdco (m n v0 g1) v0 dv g1)
	   (fdco (1+ (m n v0 g1)) v0 dv g1)))
     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1)
     (* (expt (gamma) (+ -1 n -1 n))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))

(defun delta-3 (n v0 dv g1)
  (* (expt (gamma) (+ -1 n -1 n))
     (+ (* (expt (gamma) 2)
	   (- (fdco (1- (m n v0 g1)) v0 dv g1)
	      (fdco (m n v0 g1) v0 dv g1)))
	(* (expt (gamma) 1)
	   (- (fdco (m n v0 g1) v0 dv g1)
	      (fdco (1+ (m n v0 g1)) v0 dv g1)))
	(* (expt (gamma) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))

(defun delta-3-inside (n v0 dv g1)
  (+ (* (expt (gamma) 2)
	   (- (fdco (1- (m n v0 g1)) v0 dv g1)
	      (fdco (m n v0 g1) v0 dv g1)))
	(* (expt (gamma) 1)
	   (- (fdco (m n v0 g1) v0 dv g1)
	      (fdco (1+ (m n v0 g1)) v0 dv g1)))
	(* (expt (gamma) (- 2 (* 2 n)))
	   (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
	(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))

(defun delta-3-inside-transform (n v0 dv g1)
  (/ 
   (+ (* (expt (gamma) 2)
	 (- (fdco (1- (m n v0 g1)) v0 dv g1)
	    (fdco (m n v0 g1) v0 dv g1)))
      (* (expt (gamma) 1)
	 (- (fdco (m n v0 g1) v0 dv g1)
	    (fdco (1+ (m n v0 g1)) v0 dv g1)))
      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
   (- 1
      (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
	 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))))))

;; rewrite delta term
(encapsulate ()

(local
;; considering using smtlink for the proof, probably simpler
(defthm delta-rewrite-1-lemma1
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (1- n))
			(+ (* (expt (gamma) (1+ (- n)))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))
				 1))
			   (* (expt (gamma) (1- n))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0)))))
				 1)))))
		    (+ (* (expt (gamma) (* 2 n))
			  (- (fdco (1- (m n v0 g1)) v0 dv g1)
			     (fdco (m n v0 g1) v0 dv g1)))
		       (* (expt (gamma) (- (* 2 n) 1))
			  (- (fdco (m n v0 g1) v0 dv g1)
			     (fdco (1+ (m n v0 g1)) v0 dv g1)))
		       (* (* (expt (gamma) (1- n)) (expt (gamma) (1+ (- n))))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
		       (* (* (expt (gamma) (1- n)) (expt (gamma) (1- n)))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))))
  :hints
  (("Goal"
    :clause-processor
    (Smtlink clause
			 '( (:expand ((:functions ((m integerp)
						   (gamma rationalp)
						   (mu rationalp)
						   (equ-c rationalp)
						   (fdco rationalp)
						   (dv0 rationalp)))
				      (:expansion-level 1)))
			    (:python-file "delta-rewrite-1-lemma1") ;;mktemp
			    (:let ((expt_gamma_2n
				    (expt (gamma) (* 2 n))
				     rationalp)
				   (expt_gamma_2n_minus_1
				    (expt (gamma) (- (* 2 n) 1))
				     rationalp)
				   (expt_gamma_n_minus_1
				    (expt (gamma) (1- n))
				     rationalp)
				   (expt_gamma_1_minus_n
				    (expt (gamma) (1+ (- n)))
				     rationalp)
				   ))
			    (:hypothesize ()))
			 )
    )))
)

(local
(defthm delta-rewrite-1
  (implies (basic-params n 3 v0 dv g1)
	   (equal (delta n v0 dv g1)
		  (delta-1 n v0 dv g1))))
)

(local
(defthm delta-rewrite-2-lemma1
  (implies (basic-params n 3)
	   (equal (* (expt (gamma) (1- n))
		     (expt (gamma) (1+ (- n))))
		  1))
  :hints (("Goal"
	   :use ((:instance expt-minus
	   		    (r (gamma))
	   		    (i (- (1+ (- n))))))
	   )))
)

(local
(defthm delta-rewrite-2-lemma2
  (implies (basic-params n 3)
 	   (equal (* (expt (gamma) (1- n))
 		     (expt (gamma) (1- n)))
		  (expt (gamma) (+ -1 n -1 n))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance exponents-add-for-nonneg-exponents
	   		    (i (1- n))
	   		    (j (1- n))
	   		    (r (gamma))))
	   :in-theory (disable exponents-add-for-nonneg-exponents)
	   ))
  )
)

(local
(defthm delta-rewrite-2-lemma3
  (implies (basic-params n 3)
	   (equal (+ A
		     B
		     (* (* (expt (gamma) (1- n))
			   (expt (gamma) (1+ (- n))))
			C)
		     (* (* (expt (gamma) (1- n))
			   (expt (gamma) (1- n)))
			D))
		  (+ A B C
		     (* (expt (gamma) (+ -1 n -1 n)) D))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-2-lemma1)
		 (:instance delta-rewrite-2-lemma2)))))
)

(local
(defthm delta-rewrite-2
  (implies (basic-params n 3 v0 dv g1)
	   (equal (delta-1 n v0 dv g1)
		  (delta-2 n v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-2-lemma3
			    (A (* (expt (gamma) (* 2 n))
				  (- (fdco (1- (m n v0 g1)) v0 dv g1)
				     (fdco (m n v0 g1) v0 dv g1))))
			    (B (* (expt (gamma) (- (* 2 n) 1))
				  (- (fdco (m n v0 g1) v0 dv g1)
				     (fdco (1+ (m n v0 g1)) v0 dv g1))))
			    (C (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				     (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			    (D (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				     (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))))))
)

(local
(defthm delta-rewrite-3-lemma1-lemma1
  (implies (basic-params n 3)
	   (equal (expt (gamma) (+ (+ -1 n -1 n) 2))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 2))))
  :hints (("Goal"
	   :use ((:instance exponents-add-for-nonneg-exponents
			    (i (+ -1 n -1 n))
			    (j 2)
			    (r (gamma))))
	   :in-theory (disable exponents-add-for-nonneg-exponents
			       delta-rewrite-2-lemma2))))
)

(local
(defthm delta-rewrite-3-lemma1-stupidlemma
  (implies (basic-params n 3)
	   (equal (* 2 n) (+ (+ -1 n -1 n) 2))))
)

(local
(defthm delta-rewrite-3-lemma1
  (implies (basic-params n 3)
	   (equal (expt (gamma) (* 2 n))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 2))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3-lemma1-lemma1)
		 (:instance delta-rewrite-3-lemma1-stupidlemma)))))
)

(local
 (defthm delta-rewrite-3-lemma2-lemma1-lemma1
   (implies (basic-params n 3)
	    (>= (+ n n) 2))))

(local
 (defthm delta-rewrite-3-lemma2-lemma1-stupidlemma
   (implies (basic-params n 3)
	    (>= (+ -1 n -1 n) 0))
   :hints (("GOal"
	    :use ((:instance delta-rewrite-3-lemma2-lemma1-lemma1))))))

(local
 (defthm delta-rewrite-3-lemma2-lemma1-lemma2
   (implies (basic-params n 3)
	    (integerp (+ -1 n -1 n)))
   ))

(local
 (defthm delta-rewrite-3-lemma2-lemma1-lemma3
   (implies (basic-params n 3)
	    (>= (+ -1 n -1 n) 0))
   :hints (("Goal"
	    :use ((:instance delta-rewrite-3-lemma2-lemma1-stupidlemma))))))

(local
(defthm delta-rewrite-3-lemma2-lemma1
  (implies (basic-params n 3)
	   (equal (expt (gamma) (+ (+ -1 n -1 n) 1))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 1))))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3-lemma2-lemma1-lemma2)
		 (:instance delta-rewrite-3-lemma2-lemma1-lemma3)
		 (:instance exponents-add-for-nonneg-exponents
			    (i (+ -1 n -1 n))
			    (j 1)
			    (r (gamma))))
	   )))
)

(local
(defthm delta-rewrite-3-lemma2-stupidlemma
  (implies (basic-params n 3)
	   (equal (- (* 2 n) 1)
		  (+ (+ -1 n -1 n) 1))))
)

(local
(defthm delta-rewrite-3-lemma2
  (implies (basic-params n 3)
	   (equal (expt (gamma) (- (* 2 n) 1))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (expt (gamma) 1))))
  :hints (("Goal"
  	   :use ((:instance delta-rewrite-3-lemma2-lemma1)
  		 (:instance delta-rewrite-3-lemma2-stupidlemma))
  	   :in-theory (disable delta-rewrite-2-lemma2)))
  )
)

(local
(defthm delta-rewrite-3-lemma3
  (implies (basic-params n 3)
	   (equal (* (expt (gamma) (- 2 (* 2 n)))
		     (expt (gamma) (+ -1 n -1 n)))
		  1))
  :hints (("Goal"
	   :use ((:instance expt-minus
			    (r (gamma))
			    (i (- (- 2 (* 2 n)))))))))
)

(local
(defthm delta-rewrite-3
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n v0 g1)) v0 dv g1)
			   (fdco (m n v0 g1) v0 dv g1)))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n v0 g1) v0 dv g1)
			   (fdco (1+ (m n v0 g1)) v0 dv g1)))
		     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1)
		     (* (expt (gamma) (+ -1 n -1 n))
			(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))
		  (* (expt (gamma) (+ -1 n -1 n))
		     (+ (* (expt (gamma) 2)
			   (- (fdco (1- (m n v0 g1)) v0 dv g1)
			      (fdco (m n v0 g1) v0 dv g1)))
			(* (expt (gamma) 1)
			   (- (fdco (m n v0 g1) v0 dv g1)
			      (fdco (1+ (m n v0 g1)) v0 dv g1)))
			(* (expt (gamma) (- 2 (* 2 n)))
			   (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				 (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			      (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))))
  :hints
  (("Goal"
    :in-theory (disable delta-rewrite-2-lemma1)
    :do-not-induct t
    :clause-processor
    (Smtlink clause
			 '( (:expand ((:functions ((m integerp)
						   (gamma rationalp)
						   (mu rationalp)
						   (equ-c rationalp)
						   (fdco rationalp)
						   (dv0 rationalp)))
				      (:expansion-level 1)))
			    (:python-file "delta-rewrite-3")
			    (:let ((expt_gamma_2n
				    (expt (gamma) (* 2 n))
				     rationalp)
				   (expt_gamma_2n_minus_1
				    (expt (gamma) (- (* 2 n) 1))
				     rationalp)
				   (expt_gamma_2n_minus_2
				    (expt (gamma) (+ -1 n -1 n))
				     rationalp)
				   (expt_gamma_2
				    (expt (gamma) 2)
				     rationalp)
				   (expt_gamma_1
				    (expt (gamma) 1)
				     rationalp)
				   (expt_gamma_2_minus_2n
				    (expt (gamma) (- 2 (* 2 n)))
				     rationalp)
				   ))
			    (:hypothesize ((equal expt_gamma_2n
					  	  (* expt_gamma_2n_minus_2 expt_gamma_2))
					   (equal expt_gamma_2n_minus_1
					  	  (* expt_gamma_2n_minus_2 expt_gamma_1))
					   (equal (* expt_gamma_2_minus_2n expt_gamma_2n_minus_2)
						  1)))
			    (:use ((:type ())
				   (:hypo ((delta-rewrite-3-lemma1)
					   (delta-rewrite-3-lemma2)
					   (delta-rewrite-3-lemma3)))
				   (:main ()))))
			 ))))
)

(local
(defthm delta-rewrite-4
  (implies (basic-params n 3 v0 dv g1)
	   (equal (delta-2 n v0 dv g1)
		  (delta-3 n v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-3)))))
)

(defthm delta-rewrite-5
  (implies (basic-params n 3 v0 dv g1)
	   (equal (delta n v0 dv g1)
		  (delta-3 n v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-1)
		 (:instance delta-rewrite-2)
		 (:instance delta-rewrite-3)
		 (:instance delta-rewrite-4)))))
)

(encapsulate ()

(local
(defthm delta-<-0-lemma1-lemma
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n v0 g1)) v0 dv g1)
				(fdco (m n v0 g1) v0 dv g1)))
			  (* (expt (gamma) 1)
			     (- (fdco (m n v0 g1) v0 dv g1)
				(fdco (1+ (m n v0 g1)) v0 dv g1)))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
		       0)
		    (< (* (expt (gamma) (+ -1 n -1 n))
			  (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 dv g1)
				   (fdco (m n v0 g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 dv g1)
				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
			     (* (expt (gamma) (- 2 (* 2 n)))
				(- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				      (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1)))
		       0)))
  :hints (("Goal"
	   :clause-processor
	   (Smtlink clause
				'( (:expand ((:functions ((m integerp)
							  (gamma rationalp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (fdco rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "delta-smaller-than-0-lemma1-lemma")
				  (:let ((expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (+ -1 n -1 n))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)
					 (expt_gamma_1
					  (expt (gamma) 1)
					   rationalp)
					 (expt_gamma_2_minus_2n
					  (expt (gamma) (- 2 (* 2 n)))
					   rationalp)
					 ))
				  (:hypothesize ((> expt_gamma_2n_minus_2 0))))
				))))
)

(local
(defthm delta-<-0-lemma1
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (delta-3-inside n v0 dv g1) 0)
		    (< (delta-3 n v0 dv g1) 0))))
)

(local
(defthm delta-<-0-lemma2-lemma
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 dv g1)
				   (fdco (m n v0 g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 dv g1)
				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (+ (* (expt (gamma) 2)
			     (- (fdco (1- (m n v0 g1)) v0 dv g1)
				(fdco (m n v0 g1) v0 dv g1)))
			  (* (expt (gamma) 1)
			     (- (fdco (m n v0 g1) v0 dv g1)
				(fdco (1+ (m n v0 g1)) v0 dv g1)))
			  (* (expt (gamma) (- 2 (* 2 n)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			  (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
		       0)))
  :hints (("Goal"
	   :clause-processor
	   (Smtlink clause
				'( (:expand ((:functions ((m integerp)
							  (gamma rationalp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (fdco rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "delta-smaller-than-0-lemma2-lemma")
				  (:let ((expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (+ -1 n -1 n))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)
					 (expt_gamma_1
					  (expt (gamma) 1)
					   rationalp)
					 (expt_gamma_2_minus_2n
					  (expt (gamma) (- 2 (* 2 n)))
					   rationalp)
					 ))
				  (:hypothesize ((> expt_gamma_2_minus_2n 0))))
				))))
)

(local
(defthm delta-<-0-lemma2
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (delta-3-inside-transform n v0 dv g1)
		       (expt (gamma) (- 2 (* 2 n))))
		    (< (delta-3-inside n v0 dv g1) 0)))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma2-lemma)))))
)

(local
;; This is for proving 2n < gamma^(2-2n)
(defthm delta-<-0-lemma3-lemma1
  (implies (and (integerp k)
		(>= k 6))
	   (< k (expt (/ (gamma)) (- k 2)))))
)

(local
 (defthm delta-<-0-lemma3-lemma2-stupidlemma
   (implies (basic-params n 3)
	    (>= n 3))))

(local
 (defthm delta-<-0-lemma3-lemma2-stupidlemma-omg
   (implies (and (rationalp a) (rationalp b) (>= a b))
	    (>= (* 2 a) (* 2 b)))))

(local
 (defthm delta-<-0-lemma3-lemma2-lemma1
   (implies (basic-params n 3)
	    (>= (* 2 n) 6))
   :hints (("Goal"
	    :use ((:instance delta-<-0-lemma3-lemma2-stupidlemma)
		  (:instance delta-<-0-lemma3-lemma2-stupidlemma-omg
			     (a n)
			     (b 3))
		  ))))
 )

(local
(defthm delta-<-0-lemma3-lemma2
  (implies (basic-params n 3)
	   (< (* 2 n)
	      (expt (/ (gamma)) (- (* 2 n) 2))))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma3-lemma1
			   (k (* 2 n)))
		 (:instance delta-<-0-lemma3-lemma2-lemma1))))
  :rule-classes :linear)
)

(local
(defthm delta-<-0-lemma3-lemma3-stupidlemma
  (equal (expt a n) (expt (/ a) (- n))))
)

(local
(defthm delta-<-0-lemma3-lemma3
  (implies (basic-params n 3)
	   (equal (expt (/ (gamma)) (- (* 2 n) 2))
		  (expt (gamma) (- 2 (* 2 n)))))
  :hints (("Goal"
	   :use ((:instance delta-<-0-lemma3-lemma3-stupidlemma
			    (a (/ (gamma)))
			    (n (- (* 2 n) 2))))
	   :in-theory (disable delta-<-0-lemma3-lemma3-stupidlemma))))
)

(local
(defthm delta-<-0-lemma3-lemma4-stupidlemma
  (implies (and (< a b) (equal b c)) (< a c)))
)

(local
(defthm delta-<-0-lemma3-lemma4
  (implies (basic-params n 3)
	   (< (* 2 n)
	      (expt (gamma) (- 2 (* 2 n)))))
  :hints (("Goal"
	   :do-not '(preprocess simplify)
	   :use ((:instance delta-<-0-lemma3-lemma2)
		 (:instance delta-<-0-lemma3-lemma3)
		 (:instance delta-<-0-lemma3-lemma4-stupidlemma
			    (a (* 2 n))
			    (b (expt (/ (gamma)) (- (* 2 n) 2)))
			    (c (expt (gamma) (- 2 (* 2 n))))))
	   :in-theory (disable delta-<-0-lemma3-lemma2
			       delta-<-0-lemma3-lemma3
			       delta-<-0-lemma3-lemma4-stupidlemma)))
  :rule-classes :linear)
)

(local
(defthm delta-<-0-lemma3
  (implies (basic-params n 3 v0 dv g1)
	   (implies (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 dv g1)
				   (fdco (m n v0 g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 dv g1)
				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
		       (* 2 n))
		    (< (/ (+ (* (expt (gamma) 2)
				(- (fdco (1- (m n v0 g1)) v0 dv g1)
				   (fdco (m n v0 g1) v0 dv g1)))
			     (* (expt (gamma) 1)
				(- (fdco (m n v0 g1) v0 dv g1)
				   (fdco (1+ (m n v0 g1)) v0 dv g1)))
			     (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				   (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
			  (- 1
			     (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				(1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
		       (expt (gamma) (- 2 (* 2 n))))))
  :hints (("Goal"
	   :clause-processor
	   (Smtlink clause
				'( (:expand ((:functions ((m integerp)
							  (gamma rationalp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (fdco rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "delta-smaller-than-0-lemma3")
				  (:let ((expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (+ -1 n -1 n))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)
					 (expt_gamma_1
					  (expt (gamma) 1)
					   rationalp)
					 (expt_gamma_2_minus_2n
					  (expt (gamma) (- 2 (* 2 n)))
					   rationalp))
					 )
				  (:hypothesize ((< (* 2 n) expt_gamma_2_minus_2n)))
				  (:use ((:type ())
				   	 (:hypo ((delta-<-0-lemma3-lemma4)))
				   	 (:main ())))
				  )
				)
	   :in-theory (disable delta-<-0-lemma3-lemma1
	   		       delta-<-0-lemma3-lemma3-stupidlemma
	   		       delta-<-0-lemma3-lemma2
	   		       delta-<-0-lemma3-lemma3
			       delta-<-0-lemma3-lemma4-stupidlemma)
	   )))
)

(local
(defthm delta-<-0-lemma4
  (implies (basic-params n 3 v0 dv g1)
	   (< (/ (+ (* (expt (gamma) 2)
		       (- (fdco (1- (m n v0 g1)) v0 dv g1)
			  (fdco (m n v0 g1) v0 dv g1)))
		    (* (expt (gamma) 1)
		       (- (fdco (m n v0 g1) v0 dv g1)
			  (fdco (1+ (m n v0 g1)) v0 dv g1)))
		    (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
			  (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))
		 (- 1
		    (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
		       (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0)))))))
	      (* 2 n)))
  :hints (("Goal"
	   :clause-processor
	   (Smtlink clause
				'( (:expand ((:functions ((m integerp)
							  (gamma rationalp)
							  (mu rationalp)
							  (equ-c rationalp)
							  (fdco rationalp)
							  (dv0 rationalp)))
					     (:expansion-level 1)))
				  (:python-file "delta-smaller-than-0-lemma4")
				  (:let ((expt_gamma_2n
					  (expt (gamma) (* 2 n))
					   rationalp)
					 (expt_gamma_2n_minus_1
					  (expt (gamma) (- (* 2 n) 1))
					   rationalp)
					 (expt_gamma_2n_minus_2
					  (expt (gamma) (+ -1 n -1 n))
					   rationalp)
					 (expt_gamma_2
					  (expt (gamma) 2)
					   rationalp)
					 (expt_gamma_1
					  (expt (gamma) 1)
					   rationalp)
					 (expt_gamma_2_minus_2n
					  (expt (gamma) (- 2 (* 2 n)))
					   rationalp))
					 )
				  (:hypothesize ((equal expt_gamma_1 1/5)
						 (equal expt_gamma_2 1/25))))
				)
	   :in-theory (disable delta-<-0-lemma3-lemma1
	   		       delta-<-0-lemma3-lemma3-stupidlemma
	   		       delta-<-0-lemma3-lemma2
	   		       delta-<-0-lemma3-lemma3
			       delta-<-0-lemma3-lemma4-stupidlemma
			       delta-<-0-lemma3-lemma4))))
)


(defthm delta-<-0
  (implies (basic-params n 3 v0 dv g1)
	   (< (delta n v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance delta-rewrite-5)
		 (:instance delta-<-0-lemma4)
		 (:instance delta-<-0-lemma3)
		 (:instance delta-<-0-lemma2)
		 (:instance delta-<-0-lemma1))
	   :in-theory (disable delta-<-0-lemma3-lemma1
	   		       delta-<-0-lemma3-lemma3-stupidlemma
	   		       delta-<-0-lemma3-lemma2
	   		       delta-<-0-lemma3-lemma3
			       delta-<-0-lemma3-lemma4-stupidlemma
			       delta-<-0-lemma3-lemma4)
	  )))
) ;; delta < 0 thus is proved

;; prove phi(2n+1) = gamma^2*A+gamma*B+delta
(encapsulate ()

(local
(defthm split-phi-2n+1-lemma1-lemma1
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (A (+ n 1) phi0 v0 dv g1)
		  (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n v0 g1) v0 dv g1) 1))))))
)

(local
(defthm split-phi-2n+1-lemma1-lemma2
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (+ (* (expt (gamma) (+ (* 2 n) 1)) phi0)
		     (* (expt (gamma) (* 2 n))
			(- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
		     (* (expt (gamma) (- (* 2 n) 1))
			(- (fdco (m n v0 g1) v0 dv g1) 1)))
		  (+ (* (+ (* (expt (gamma) (- (* 2 n) 1)) phi0)
			   (* (expt (gamma) (- (* 2 n) 2))
			      (- (fdco (m n v0 g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 3))
			      (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
			(expt (gamma) 2))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1))))))
  )
)

(local
(defthm split-phi-2n+1-lemma1-A
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (A (+ n 1) phi0 v0 dv g1)
		  (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
		     (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma1
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (* (expt (gamma) (- n 1))
		     (B-sum 1 (- n 1) v0 dv g1)))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma2
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (* (expt (gamma) (- n 1))
		     (+ (B-term (- n 1) v0 dv g1)
			(B-term (- (- n 1)) v0 dv g1)
			(B-sum 1 (- n 2) v0 dv g1))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma3
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (expt (gamma) (- n 1))
			(B-sum 1 (- n 2) v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(B-term (- n 1) v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(B-term (- (- n 1)) v0 dv g1))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma4
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (gamma) (expt (gamma) (- n 2))
			(B-sum 1 (- n 2) v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(+ (B-term (- n 1) v0 dv g1)
			   (B-term (- (- n 1)) v0 dv g1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-lemma5
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (gamma) (B n v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(+ (B-term (- n 1) v0 dv g1)
			   (B-term (- (- n 1)) v0 dv g1)))))))
)

(local
(defthm split-phi-2n+1-lemma2-B
  (implies (basic-params n 3 v0 dv g1)
	   (equal (B (+ n 1) v0 dv g1)
		  (+ (* (gamma) (B n v0 dv g1))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 dv g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 dv g1))))))))
)

(local
(defthm split-phi-2n+1-lemma3-delta-stupidlemma
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 dv g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 dv g1)))))
		  (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (1- n))
			(+ (* (expt (gamma) (1+ (- n)))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (1- n)) (equ-c v0))))) 1))
			   (* (expt (gamma) (1- n))
			      (- (/ (* (mu) (1+ (* *alpha* (+ v0 dv))))
				    (1+ (* *beta* (+ (* g1 (- 1 n)) (equ-c v0))))) 1))))))))
)

(local
(defthm split-phi-2n+1-lemma3-delta
  (implies (basic-params n 3 v0 dv g1)
	   (equal (+ (- (* (expt (gamma) (* 2 n))
			   (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			(* (expt (gamma) (* 2 n))
			   (- (fdco (m n v0 g1) v0 dv g1) 1)))
		     (- (* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (m n v0 g1) v0 dv g1) 1))
			(* (expt (gamma) (- (* 2 n) 1))
			   (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
		     (* (expt (gamma) (- n 1))
			(+ (* (expt (gamma) (- (- n 1)))
			      (B-term-rest (- n 1) v0 dv g1))
			   (* (expt (gamma) (- n 1))
			      (B-term-rest (- (- n 1)) v0 dv g1)))))
		  (delta n v0 dv g1)))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma3-delta-stupidlemma)
		 (:instance delta)))))
)

(local
(defthm split-phi-2n+1-lemma4
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (A (+ n 1) phi0 v0 dv g1)
		     (B (+ n 1) v0 dv g1)))))
)

(local
(defthm split-phi-2n+1-lemma5
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
			(- (* (expt (gamma) (* 2 n))
			      (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			   (* (expt (gamma) (* 2 n))
			      (- (fdco (m n v0 g1) v0 dv g1) 1)))
			(- (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (m n v0 g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1))))
		     (+ (* (gamma) (B n v0 dv g1))
			(* (expt (gamma) (- n 1))
			   (+ (* (expt (gamma) (- (- n 1)))
				 (B-term-rest (- n 1) v0 dv g1))
			      (* (expt (gamma) (- n 1))
				 (B-term-rest (- (- n 1)) v0 dv g1))))))))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma1-A)
		 (:instance split-phi-2n+1-lemma2-B)))))
)

(local 
(defthm split-phi-2n+1-lemma6
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
		  (+ (* (A n phi0 v0 dv g1) (gamma) (gamma))
		     (* (gamma) (B n v0 dv g1))
		     (+ (- (* (expt (gamma) (* 2 n))
			      (- (fdco (1- (m n v0 g1)) v0 dv g1) 1))
			   (* (expt (gamma) (* 2 n))
			      (- (fdco (m n v0 g1) v0 dv g1) 1)))
			(- (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (m n v0 g1) v0 dv g1) 1))
			   (* (expt (gamma) (- (* 2 n) 1))
			      (- (fdco (1+ (m n v0 g1)) v0 dv g1) 1)))
			(* (expt (gamma) (- n 1))
			   (+ (* (expt (gamma) (- (- n 1)))
				 (B-term-rest (- n 1) v0 dv g1))
			      (* (expt (gamma) (- n 1))
				 (B-term-rest (- (- n 1)) v0 dv g1)))))))))
)

(defthm split-phi-2n+1
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (equal (phi-2n-1 (1+ n) phi0 v0 dv g1)
 		  (+ (* (gamma) (gamma) (A n phi0 v0 dv g1))
		     (* (gamma) (B n v0 dv g1)) (delta n v0 dv g1))))
  :hints (("Goal"
	   :use ((:instance split-phi-2n+1-lemma6)
		 (:instance split-phi-2n+1-lemma3-delta)))))

)

;; prove gamma^2*A + gamma*B < 0
(encapsulate ()

(local
(defthm except-for-delta-<-0-lemma1
  (implies (and (and (rationalp c)
		     (rationalp a)
		     (rationalp b))
		(and (> c 0)
		     (< c 1)
		     (< (+ A B) 0)
		     (< B 0)))
	   (< (+ (* c c A) (* c B)) 0))
  :hints (("Goal"
	   :clause-processor
	   (Smtlink clause
				'( (:expand ((:function ())
					     (:expansion-level 1)))
				  (:python-file "except-for-delta-smaller-than-0-lemma1")
				  (:let ())
				  (:hypothesize ()))
				)))
  :rule-classes :linear)
)

(defthm except-for-delta-<-0
  (implies (basic-params n 3 v0 dv g1 phi0 (< (phi-2n-1 n phi0 v0 dv g1) 0))
	   (< (+ (* (gamma) (gamma) (A n phi0 v0 dv g1))
		 (* (gamma) (B n v0 dv g1)))
	      0))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance except-for-delta-<-0-lemma1
			    (c (gamma))
			    (A (A n phi0 v0 dv g1))
			    (B (B n v0 dv g1)))
		 (:instance B-neg)))))
)

;; for induction step 
(encapsulate ()

(defthm phi-2n+1-<-0-inductive
  (implies (basic-params n 3 v0 dv g1 phi0 (< (phi-2n-1 n phi0 v0 dv g1) 0))
	   (< (phi-2n-1 (1+ n) phi0 v0 dv g1) 0))
  :hints (("Goal"
 	   :use ((:instance split-phi-2n+1)
		 (:instance delta-<-0)
		 (:instance except-for-delta-<-0)))))

(defthm phi-2n+1-<-0-inductive-corollary
  (implies (basic-params n 3 v0 dv g1 phi0
                         (< (+ (A n phi0 v0 dv g1)
                               (* (B-expt n)
                                  (B-sum 1 (+ -1 -1 n) v0 dv g1)))
                            0))
           (< (+ (A (+ 1 n) phi0 v0 dv g1)
                 (* (B-expt (+ 1 n))
                    (B-sum 1 (+ -1 n) v0 dv g1))) 0))
  :hints (("Goal"
           :use ((:instance phi-2n+1-<-0-inductive)))))

(defthm phi-2n+1-<-0-base-lemma
  (IMPLIES (AND (RATIONALP V0)
              (RATIONALP PHI0)
              (RATIONALP DV)
              (<= 1 (* 10/9 V0))
              (<= V0 11/10)
              (<= (- (* 8000 DV)) 1)
              (<= (* 8000 DV) 1)
              (<= 0 PHI0)
              (< PHI0
                 (+ -1 (/ (+ 2561/3200 V0))
                    (* DV (/ (+ 2561/3200 V0)))
                    (* V0 (/ (+ 2561/3200 V0))))))
         (< (+ (* 1/3125 PHI0)
               (/ (+ 3201/3200 V0))
               (* 1/125 (/ (+ 1599/1600 V0)))
               (* 1/25 (/ (+ 3199/3200 V0)))
               (* 1/625 (/ (+ 3197/3200 V0)))
               (* DV (/ (+ 3201/3200 V0)))
               (* V0 (/ (+ 3201/3200 V0)))
               (* 1/125 DV (/ (+ 1599/1600 V0)))
               (* 1/125 V0 (/ (+ 1599/1600 V0)))
               (* 1/25 DV (/ (+ 3199/3200 V0)))
               (* 1/25 V0 (/ (+ 3199/3200 V0)))
               (* 1/625 DV (/ (+ 3197/3200 V0)))
               (* 1/625 V0 (/ (+ 3197/3200 V0))))
            656/625))
  :hints (("Goal"
	   :clause-processor
  	   (Smtlink clause
  				'( (:expand ((:function ())
  					     (:expansion-level 1)))
  				  (:python-file "phi-2n+1-smaller-than-0-base")
  				  (:let ())
  				  (:hypothesize ()))
          )))
  )

(defthm phi-2n+1-<-0-base
    (implies (basic-params-equal n 2 v0 dv g1 phi0)
	   (< (phi-2n-1 (1+ n) phi0 v0 dv g1) 0))
  :hints (("Goal"
           :use ((:instance phi-2n+1-<-0-base-lemma))))
  )

(defthm phi-2n+1-<-0-lemma-stupid-lemma1
  (IMPLIES
 (AND
     (IMPLIES
          (AND (AND (INTEGERP N)
                    (RATIONALP G1)
                    (RATIONALP V0)
                    (RATIONALP PHI0)
                    (RATIONALP DV))
               (EQUAL N 2)
               (EQUAL G1 1/3200)
               (<= 9/10 V0)
               (<= V0 11/10)
               (<= -1/8000 DV)
               (<= DV 1/8000)
               (<= 0 PHI0)
               (< PHI0
                  (+ -1
                     (* (FIX (+ 1 (FIX (+ V0 DV))))
                        (/ (+ 1
                              (FIX (* (+ 1
                                         (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                            (/ G1))
                                         -640)
                                      G1))))))))
          (< (PHI-2N-1 (+ 1 N) PHI0 V0 DV G1) 0))
     (EQUAL N 2)
     (NOT (OR (NOT (INTEGERP N)) (< N 1)))
     (IMPLIES
          (AND (AND (INTEGERP (+ -1 N))
                    (RATIONALP G1)
                    (RATIONALP V0)
                    (RATIONALP DV)
                    (RATIONALP PHI0))
               (<= 2 (+ -1 N))
               (<= (+ -1 N) 640)
               (EQUAL G1 1/3200)
               (<= 9/10 V0)
               (<= V0 11/10)
               (<= -1/8000 DV)
               (<= DV 1/8000)
               (<= 0 PHI0)
               (< PHI0
                  (+ -1
                     (* (FIX (+ 1 (FIX (+ V0 DV))))
                        (/ (+ 1
                              (FIX (* (+ 1
                                         (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                            (/ G1))
                                         -640)
                                      G1))))))))
          (< (+ (A (FIX N) PHI0 V0 DV 1/3200)
                (* (B-EXPT (FIX N))
                   (B-SUM 1 (+ -1 -1 N) V0 DV 1/3200)))
             0))
     (INTEGERP N)
     (RATIONALP G1)
     (RATIONALP V0)
     (RATIONALP DV)
     (RATIONALP PHI0)
     (<= 2 N)
     (<= N 640)
     (EQUAL G1 1/3200)
     (<= 9/10 V0)
     (<= V0 11/10)
     (<= -1/8000 DV)
     (<= DV 1/8000)
     (<= 0 PHI0)
     (< PHI0
        (+ -1
           (* (FIX (+ 1 (FIX (+ V0 DV))))
              (/ (+ 1
                    (FIX (* (+ 1
                               (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                  (/ G1))
                               -640)
                            G1))))))))
 (< (+ (A (+ 1 N) PHI0 V0 DV 1/3200)
       (* (B-EXPT (+ 1 N))
          (B-SUM 1 (+ -1 N) V0 DV 1/3200)))
    0)))

(defthm phi-2n+1-<-0-lemma-stupid-lemma2
  (IMPLIES
 (AND
     (IMPLIES
          (AND (AND (INTEGERP N)
                    (RATIONALP G1)
                    (RATIONALP V0)
                    (RATIONALP DV)
                    (RATIONALP PHI0))
               (<= 3 N)
               (<= N 640)
               (EQUAL G1 1/3200)
               (<= 9/10 V0)
               (<= V0 11/10)
               (<= -1/8000 DV)
               (<= DV 1/8000)
               (<= 0 PHI0)
               (< PHI0
                  (+ -1
                     (* (FIX (+ 1 (FIX (+ V0 DV))))
                        (/ (+ 1
                              (FIX (* (+ 1
                                         (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                            (/ G1))
                                         -640)
                                      G1)))))))
               (< (+ (A N PHI0 V0 DV G1)
                     (* (B-EXPT N)
                        (B-SUM 1 (+ -1 -1 N) V0 DV G1)))
                  0))
          (< (+ (A (+ 1 N) PHI0 V0 DV G1)
                (* (B-EXPT (+ 1 N))
                   (B-SUM 1 (+ -1 N) V0 DV G1)))
             0))
     (< 2 N)
     (NOT (OR (NOT (INTEGERP N)) (< N 1)))
     (IMPLIES
          (AND (AND (INTEGERP (+ -1 N))
                    (RATIONALP G1)
                    (RATIONALP V0)
                    (RATIONALP DV)
                    (RATIONALP PHI0))
               (<= 2 (+ -1 N))
               (<= (+ -1 N) 640)
               (EQUAL G1 1/3200)
               (<= 9/10 V0)
               (<= V0 11/10)
               (<= -1/8000 DV)
               (<= DV 1/8000)
               (<= 0 PHI0)
               (< PHI0
                  (+ -1
                     (* (FIX (+ 1 (FIX (+ V0 DV))))
                        (/ (+ 1
                              (FIX (* (+ 1
                                         (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                            (/ G1))
                                         -640)
                                      G1))))))))
          (< (+ (A (FIX N) PHI0 V0 DV 1/3200)
                (* (B-EXPT (FIX N))
                   (B-SUM 1 (+ -1 -1 N) V0 DV 1/3200)))
             0))
     (INTEGERP N)
     (RATIONALP G1)
     (RATIONALP V0)
     (RATIONALP DV)
     (RATIONALP PHI0)
     (<= 2 N)
     (<= N 640)
     (EQUAL G1 1/3200)
     (<= 9/10 V0)
     (<= V0 11/10)
     (<= -1/8000 DV)
     (<= DV 1/8000)
     (<= 0 PHI0)
     (< PHI0
        (+ -1
           (* (FIX (+ 1 (FIX (+ V0 DV))))
              (/ (+ 1
                    (FIX (* (+ 1
                               (* (+ (FIX (* (+ 1 (FIX V0)) 1)) -1)
                                  (/ G1))
                               -640)
                            G1))))))))
 (< (+ (A (+ 1 N) PHI0 V0 DV 1/3200)
       (* (B-EXPT (+ 1 N))
          (B-SUM 1 (+ -1 N) V0 DV 1/3200)))
    0)))

(defthm phi-2n+1-<-0-lemma
  (IMPLIES (basic-params n 2 v0 dv g1 phi0)
           (< (+ (A (+ 1 n) phi0 V0 DV 1/3200)
                 (* (B-EXPT (+ 1 N))
                    (B-SUM 1 (+ -1 N) V0 DV 1/3200)))
              0))
  :hints (("Goal"
           :do-not '(simplify)
           :in-theory (disable B-expt)
           :induct (B-sum 1 N V0 DV 1/3200)
           )
          ("Subgoal *1/2"
           :cases ((< n 2) (equal n 2) (> n 2)))
          ("Subgoal *1/2.2"
           :use ((:instance phi-2n+1-<-0-base)
                 (:instance phi-2n+1-<-0-lemma-stupid-lemma1)))
          ("Subgoal *1/2.1"
           :use ((:instance phi-2n+1-<-0-inductive-corollary)
                 (:instance phi-2n+1-<-0-lemma-stupid-lemma2)))
          ))

(defthm phi-2n+1-<-0
  (implies (basic-params n 2 v0 dv g1 phi0)
	   (< (phi-2n-1 (1+ n) phi0 v0 dv g1) 0))
  :hints (("Goal"
           :use ((:instance phi-2n+1-<-0-lemma))))
  )

(defthm phi-2n-1-<-0
  (implies (basic-params n 3 v0 dv g1 phi0)
	   (< (phi-2n-1 n phi0 v0 dv g1) 0))
  :hints (("Goal"
	   :use ((:instance phi-2n+1-<-0
			    (n (1- n)))))))
)
