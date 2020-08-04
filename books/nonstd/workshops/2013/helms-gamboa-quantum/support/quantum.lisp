(in-package "ACL2")

(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "arithmetic/top" :dir :system)


(defthm *-real-complex
  (implies (and (realp x)
		(realp a)
		(realp b))
	   (equal (* x (complex a b))
		  (complex (* a x) (* b x))))
  :hints (("Goal"
	   :use ((:instance COMPLEX-DEFINITION
			    (x a)
			    (y b))
		 (:instance COMPLEX-DEFINITION
			    (x (* a x))
			    (y (* b x)))
		 )))
  )

(defthm conjugate-/-0
  (implies (and (not (complexp (* a (/ x))))
		(complexp a)
		(realp x))
	   (equal x 0))
  :rule-classes :forward-chaining
  )

(defthm conjugate-quotient
  (implies (and (acl2-numberp a)
		(realp x))
	   (equal (conjugate (/ a x))
		  (/ (conjugate a)
		     x))))

;; The following sequence of theorems indicate how poor ACL2 is in
;; reasoning about the complex numbers.  This first one simply says
;; how to add complex numbers.

(local
 (defthm +-complex
   (implies (and (realp i) (realp j) (realp r) (realp s))
	    (equal (+ (complex i j) (complex r s))
		   (complex (+ i r) (+ j s))))
   :hints (("Goal"
	    :use ((:instance complex-definition (x i) (y j))
		  (:instance complex-definition (x r) (y s))
		  (:instance complex-definition (x (+ i r)) (y (+ j s))))))))

;; Next, we'll look at multiplying complex numbers.  Here's the first
;; step in multiplying (a+bi) * (r+si)....

(local
 (defthm *-complex-lemma-1
   (implies (and (realp a) (realp b) (realp r) (realp s))
	    (equal (* (complex a b) (complex r s))
		   (* (+ a (* #C(0 1) b)) (+ R (* #C(0 1) S)))))
   :hints (("Goal"
	    :use ((:instance complex-definition (x a) (y b))
		  (:instance complex-definition (x r) (y s)))))))

;; ...the next step is to factor everything out, remembering that
;; i^2=-1....

(local
 (defthm *-complex-lemma-2
   (implies (and (realp a) (realp b) (realp r) (realp s))
	    (equal (complex (- (* a r) (* b s))
			    (+ (* a s) (* b r)))
		   (+ (+ (* a R) (- (* b S)))
		      (* #C(0 1) (+ (* a S) (* b R))))))
   :hints (("Goal"
	    :use ((:instance complex-definition
			     (x (- (* a r) (* b s)))
			     (y (+ (* a s) (* b r)))))))))

;; And so now we can get a formula for the product of two complex
;; numbers.

(local
 (defthm *-complex
   (implies (and (realp i) (realp j) (realp r) (realp s))
	    (equal (* (complex i j) (complex r s))
		   (complex (- (* i r) (* j s))
			    (+ (* i s) (* j r)))))))



(defthm x-*-x-conjugate-non-negative
  (implies (acl2-numberp x)
	   (<= 0 (* x (conjugate x))))
  :hints (("Goal"
	   :cases ((realp x)))
	  ("Subgoal 2''"
	   :use ((:instance complex-definition
			    (x (realpart x))
			    (y (- (imagpart x))))
		 (:instance complex-definition
			    (x (realpart x))
			    (y (imagpart x)))))
	  )
  :rule-classes (:linear :rewrite)
  )

(defthm x-*-x-conjugate-positive
  (implies (and (acl2-numberp x)
		(not (equal x 0)))
	   (< 0 (* x (conjugate x))))
  :hints (("Goal"
	   :cases ((realp x)))
	  ("Subgoal 2''"
	   :use ((:instance complex-definition
			    (x (realpart x))
			    (y (- (imagpart x))))
		 (:instance complex-definition
			    (x (realpart x))
			    (y (imagpart x)))))
	  )
  :rule-classes (:linear :rewrite)
  )

(defthm x-*-x-conjugate-real
  (and (realp (* x (conjugate x)))
       (<= 0 (* x (conjugate x))))
  :hints (("Goal"
	   :cases ((not (acl2-numberp x)) (equal x 0))))
  :rule-classes (:type-prescription :rewrite))

(in-theory (disable conjugate))

(defthm /-sqrt-/-sqrt
  (implies (and (realp x)
		(<= 0 x))
	   (equal (* (/ (acl2-sqrt x))
		     (/ (acl2-sqrt x)))
		  (/ x)))
  :hints (("Goal"
	   :use ((:instance sqrt-sqrt)
		 (:instance (:theorem (implies (and (realp x)
						    (<= 0 x))
					       (equal (* (/ x) (/ x))
						      (/ (* x x)))))
			    (x (acl2-sqrt x))))
	   :in-theory (disable sqrt-sqrt)
	   )))



;; The representation of a quantum state with n qubits, where each vector
;; is a basis vector in a Hilbert space of n dimensions:
;; ((alpha . |1>) . ((alpha . |2>) . ((... . ...) . ((alpha . |n>) . nil))))

;; Basis vectors of qubit states are represented as boolean lists:
;; '(nil t nil) = |010>

(defun qustatep (x)
  (if (endp x)
      (null x)
    (if (and (acl2-numberp (caar x))
	     (boolean-listp (cdar x))
	     (if (consp (cdr x))
		 (equal (len (cdar x)) (len (cdadr x)))
	       t)
	     (qustatep (cdr x)))
	t
      nil)))

;; Normalization functions have been updated to handle the new
;; state representation.
;; Does not yet handle adding multiple basis vectors.

(defun mapcons (q qstates)
  (if (consp qstates)
      (cons (cons q (car qstates))
	    (mapcons q (cdr qstates)))
    nil))

(defun get-states (n)
  (if (zp n)
      (list nil)
    (append (mapcons nil (get-states (1- n)))
	    (mapcons t   (get-states (1- n))))))

(defun collect-amplitudes (qstate x)
  (if (consp x)
      (if (equal (cdar x) qstate)
	  (+ (caar x) (collect-amplitudes qstate (cdr x)))
	(collect-amplitudes qstate (cdr x)))
    0))

(defun sort-and-merge-qstates (x qstates)
  (if (consp qstates)
      (cons (cons (collect-amplitudes (car qstates) x)
		  (car qstates))
	    (sort-and-merge-qstates x (cdr qstates)))
    nil)
  )

(defun sort-and-merge (x)
  (sort-and-merge-qstates x (get-states (1- (len (car x))))))

(defun qustate-amplitudes-sum-squares (x)
  (if (endp x)
      0
    (+ (* (caar x) (conjugate (caar x))) (qustate-amplitudes-sum-squares (cdr x)))))

(defun qustate-norm (x)
  (acl2-sqrt (qustate-amplitudes-sum-squares x)))

(defun qustate-norm-e (x e)
  (sqrt-iter (qustate-amplitudes-sum-squares x) e))

(defun qustate-scale (s x)
  (if (endp s)
      nil
    (cons (cons (* (caar s) x)
		(cdar s))
	  (qustate-scale (cdr s) x))))

#|
(defun qustate-scale-alpha-n (s n x)
  (if (endp s)
      s
    (if (nth n (cdar s))
	(cons (car s) (qustate-scale-alpha-n (cdr s) n x))
      (cons (cons (* (caar s) x) (cdar s)) (qustate-scale-alpha-n (cdr s) n x)))))

(defun qustate-scale-beta-n (s n x)
  (if (endp s)
      s
    (if (nth n (cdar s))
	(cons (cons (* (caar s) x) (cdar s)) (qustate-scale-beta-n (cdr s) n x))
      (cons (car s) (qustate-scale-beta-n (cdr s) n x)))))
|#

(defun qustate-normalize-amplitudes (x)
  (qustate-scale x (/ (qustate-norm x))))

(defun qustate-normalize (x)
  (qustate-normalize-amplitudes (sort-and-merge x)))

(defun qustate-normalize-amplitudes-e (x e)
  (qustate-scale x (/ (qustate-norm-e x e))))

(defun qustate-normalize-e (x e)
  (qustate-normalize-amplitudes-e (sort-and-merge x) e))

(defun uniform-qstate (n)
  (qustate-normalize (mapcons 1 (get-states n))))

(defun uniform-qstate-e (n e)
  (qustate-normalize-e (mapcons 1 (get-states n)) e))

(defun zero-qstate (n)
  (cons (cons 1 (car (get-states n)))
	(mapcons 0 (cdr (get-states n)))))

(defun one-qstate (n)
  (reverse (cons (cons 1 (car (reverse (get-states n))))
		 (mapcons 0 (cdr (reverse (get-states n)))))))

;; qustate-alpha-n returns the alpha for |0> of qubit n in state s

(defun qustate-alpha-n (s n)
  (if (endp s)
      0
    (if (nth n (cdar s))
	(qustate-alpha-n (cdr s) n)
      (+ (caar s) (qustate-alpha-n (cdr s) n)))))

;; qustate-beta-n returns the beta for |1> of qubit n in state s

(defun qustate-beta-n (s n)
  (if (endp s)
      0
    (if (nth n (cdar s))
	(+ (caar s) (qustate-beta-n (cdr s) n))
      (qustate-beta-n (cdr s) n))))

;; qustate-coefficients returns (alpha . beta) for alpha|0> + beta|1>
;; of qubit n in state s. Essentially a qubit.

(defun qustate-coefficients (s n)
  (cons (qustate-alpha-n s n) (qustate-beta-n s n)))

;; I'm not sure if ACL2 already has a function like del-nth-list
;; but I haven't found one.

(defun del-nth-list (n lst)
  (if (endp lst)
      nil
    (if (zp n)
	(cdr lst)
      (cons (car lst)
	    (del-nth-list (- n 1) (cdr lst))))))

;; For index-of-X-swap, v is a basis vector in which the nth
;; (0 based index) bit needs to be flipped. (|10> to |11> for n = 1)
;; i is index to increment.

(defun index-of-X-swap (s v n i)
  (if (endp s) nil
    (if (and (equal (nth n v) (not (nth n (cdar s))))
	     (equal (del-nth-list n (cdar s))
		    (del-nth-list n v)))
	i
      (index-of-X-swap (cdr s) v n (+ i 1)))))

;; Unfortunately, swapping coefficients of the basis vectors makes
;; the NOT gates messy. Assumes state is normalized.
;; Preserves order of basis vectors.

;; Cannot prove termination of gates due to update-nth possibly increasing
;; length of s where (< n (len s)).
;; Could possibly fix with update-nth-if-n<len that preserves length.

(defun update-nth-if-n<len (n x s)
  (if (endp s)
      nil
    (if (> n (len s))
	s
      (if (zp n)
	  (cons x (cdr s))
	(cons (car s)(update-nth-if-n<len (- n 1) x (cdr s)))))))

(defthm update-nth-if-n<len-preserves-len
  (implies (true-listp s)
	   (equal (len (update-nth-if-n<len n x s)) (len s))))

(defthm len-cdr-update-nth-if-n<len-<-len
  (implies (consp s)
	   (< (len (cdr (update-nth-if-n<len n x s))) (len s))))

;; For NOT gates, if there exists in s an index to a basis vector equal to the current
;; vector with the correctly flipped n bit, then replace the alpha of the current vector
;; with the alpha of s[i] and recurse on the cdr of the list returned from update-nth-if-n<len.

(defun qu-X-gate (s n r) (declare (ignorable r) (xargs :measure (len s)))
  (if (endp s)
      nil
    (if (index-of-X-swap s (cdar s) n 0)
	(cons (cons (car (nth (index-of-X-swap s (cdar s) n 0) s))
		    (cdar s))
	      (qu-X-gate (cdr (update-nth-if-n<len (index-of-X-swap s (cdar s) n 0)
						   (cons (caar s)
							 (cdr (nth (index-of-X-swap s (cdar s) n 0)
								   s)))
						   s))
			 n r))
      (cons (car s) (qu-X-gate (cdr s) n r)))))

(defun qu-CN-gate (s c n r) (declare (ignorable r) (xargs :measure (len s)))
  (if (endp s)
      nil
    (if (nth c (cdar s))
	(if (index-of-X-swap s (cdar s) n 0)
	    (cons (cons (car (nth (index-of-X-swap s (cdar s) n 0) s))
			(cdar s))
		  (qu-CN-gate (cdr (update-nth-if-n<len (index-of-X-swap s (cdar s) n 0)
							(cons (caar s)
							      (cdr (nth (index-of-X-swap s (cdar s) n 0) s)))
							s))
			      c n r))
	  (cons (car s) (qu-CN-gate (cdr s) c n r)))
      (cons (car s) (qu-CN-gate (cdr s) c n r)))))

(defun qu-Z-gate-helper (av n r)
  (declare (ignorable r))
  (let* ((a (car av))
	 (v (cdr av))
	 ;(pre (butlast v (- (len v) n)))
	 (q (nth n v))
	 ;(post (nthcdr (1+ n) v))
	 )
    (if (not q)
	av
      (cons (- a) v))))

(defun qu-Z-gate (s n r)
  (declare (ignorable r))
  (if (endp s)
      nil
    (cons (qu-Z-gate-helper (car s) n r)
	  (qu-Z-gate (cdr s) n r))))


;; qu-H-gate-test is not usable in execution since it uses acl2-sqrt.

(defun qu-H-gate-helper (av n r)
  (declare (ignorable r))
  (let* ((a (car av))
	 (v (cdr av))
	 (pre (butlast v (- (len v) n)))
	 (q (nth n v))
	 (post (nthcdr (1+ n) v))
	 )
    (if (not q)
	(list (cons (/ a (acl2-sqrt 2))
		    (append pre
			    (cons nil post)))
	      (cons (/ a (acl2-sqrt 2))
		    (append pre
			    (cons t post))))
      (list (cons (/ a (acl2-sqrt 2))
		  (append pre
			  (cons nil post)))
	    (cons (- (/ a (acl2-sqrt 2)))
		  (append pre
			  (cons t post)))))))

(defun qu-H-gate (s n r)
  (declare (ignorable r))
  (if (endp s)
      nil
    (append (qu-H-gate-helper (car s) n r)
	    (qu-H-gate (cdr s) n r))))

(defun qu-H-gate-e-helper (av n e r)
  (declare (ignorable r))
  (let* ((a (car av))
	 (v (cdr av))
	 (pre (butlast v (- (len v) n)))
	 (q (nth n v))
	 (post (nthcdr (1+ n) v))
	 )
    (if (not q)
	(list (cons (/ a (sqrt-iter 2 e))
		    (append pre
			    (cons nil post)))
	      (cons (/ a (sqrt-iter 2 e))
		    (append pre
			    (cons t post))))
      (list (cons (/ a (sqrt-iter 2 e))
		  (append pre
			  (cons nil post)))
	    (cons (- (/ a (sqrt-iter 2 e)))
		  (append pre
			  (cons t post)))))))

(defun qu-H-gate-e (s n e r)
  (declare (ignorable r))
  (if (endp s)
      nil
    (append (qu-H-gate-e-helper (car s) n e r)
	    (qu-H-gate-e (cdr s) n e r))))


#|
(defun qu-H-gate-test (s n r) (declare (ignorable r))
  (if (endp s)
      nil
    (qustate-scale-alpha-n (qustate-scale-beta-n s n (/ (- (car (qustate-coefficients s n))
							   (cdr (qustate-coefficients s n)))
							(acl2-sqrt 2)))
			   n
			   (/ (+ (car (qustate-coefficients s n))
				 (cdr (qustate-coefficients s n)))
			      (acl2-sqrt 2)))))

(defun qu-H-gate (s n e r) (declare (ignorable r))
  (if (endp s)
      nil
    (qustate-scale-alpha-n (qustate-scale-beta-n s n (/ (- (car (qustate-coefficients s n))
							   (cdr (qustate-coefficients s n)))
							(sqrt-iter 2 e)))
			   n
			   (/ (+ (car (qustate-coefficients s n))
				 (cdr (qustate-coefficients s n)))
			      (sqrt-iter 2 e)))))
|#



(defun qu-I-gate (s n r) (declare (ignorable n r))
  s)

;; A simple circuit example to demonstrate quantum gates

(defun qubit-Bell-state-circuit (s c n r)
  (qustate-normalize (qu-CN-gate (qustate-normalize (qu-H-gate s c r)) c n r)))


(defun qu-collapse (s n q)
  (if (endp s)
      nil
    (if (equal (nth n (cdar s)) q)
	(cons (car s)
	      (qu-collapse (cdr s) n q))
      (qu-collapse (cdr s) n q))))

(defun qu-M-gate (s n r)
  (declare (ignorable n r))
  (let ((s1 (qu-collapse s n nil))
	(s2 (qu-collapse s n t)))
    (if (< r (qustate-amplitudes-sum-squares s1))
	s1
      s2)))

#|
(defun qubit-extract-aux (s n)
  (if (endp s)
      nil
    (cons (list (caar s)
		(nth n (cdar s)))
	  (qubit-extract-aux (cdr s) n))))

(defun qubit-extract (s n)
  (qustate-normalize (qubit-extract-aux s n)))


(defun qubit-extract-e (s n e)
  (qustate-normalize-e (qubit-extract-aux s n) e))
|#

(defun qstate-circuit-aux (circuit qstate rs)
  (if (endp circuit)
      qstate
    (let ((op (caar circuit))
          (args (cdar circuit)))
      (qstate-circuit-aux (cdr circuit)
                         (qustate-normalize
                          (case op
                            (X  (qu-X-gate qstate (car args) 0))
                            (Z  (qu-Z-gate qstate (car args) 0))
                            (CN (qu-CN-gate qstate (car args) (cadr args) 0))
                            (H  (qu-H-gate qstate (car args) 0))
                            (I  (qu-I-gate qstate (car args) 0))
                            (M  (qu-M-gate qstate (car args) (car rs)))))
                         (if (equal op 'M)
                             (cdr rs)
                           rs)))))

(defun qstate-circuit (circuit qstate rs)
  (qstate-circuit-aux circuit (qustate-normalize qstate) rs))

(defun qstate-circuit-e-aux (circuit qstate e rs)
  (if (endp circuit)
      qstate
    (let ((op (caar circuit))
	  (args (cdar circuit)))
      (qstate-circuit-e-aux (cdr circuit)
			   (qustate-normalize-e
			    (case op
			      (X  (qu-X-gate qstate (car args) 0))
			      (CN (qu-CN-gate qstate (car args) (cadr args) 0))
			      (H  (qu-H-gate-e qstate (car args) e 0))
			      (I  (qu-I-gate qstate (car args) 0))
			      (M  (qu-M-gate qstate (car args) (car rs))))
			    e)
			   e
			   (if (equal op 'M)
			       (cdr rs)
			     rs)))))

(defun qstate-circuit-e (circuit qstate e rs)
  (qstate-circuit-e-aux circuit (qustate-normalize-e qstate e) e rs))

;; The tensor function takes a list of two qubits and returns the product vector
;; in the form of a nil terminated list.
;; Future work should take any number of qubits.

#|
(defun qstate-tensor-product (x)
  (cons (* (caar x) (cadr x))
	(cons (* (caar x) (cddr x))
	      (cons (* (cdar x) (cadr x))
		    (cons (* (cdar x) (cddr x))
			  nil)))))
|#

(defun qstate-tensor-product-aux (q y)
  (if (endp y)
      nil
    (cons (cons (* (car q) (caar y))
		(append (cdr q) (cdar y)))
	  (qstate-tensor-product-aux q (cdr y)))))

(defun qstate-tensor-product (x y)
  (if (endp x)
      nil
    (append (qstate-tensor-product-aux (car x) y)
	    (qstate-tensor-product (cdr x) y))))


(defun make-qubit (alpha beta)
  (list (list alpha nil)
	(list beta  t)))

#|
(qu-CN-gate (cons (cons 0 '(nil nil nil))
		  (cons (cons 1 '(nil nil t))
			(cons (cons 2 '(nil t nil))
			      (cons (cons 3 '(nil t t))
				    (cons (cons 4 '(t nil nil))
					  (cons (cons 5 '(t nil t))
						(cons (cons 6 '(t t nil))
						      (cons (cons 7 '(t t t)) nil))))))))
	    0 2 '())

(qu-X-gate (cons (cons 1 '(nil nil nil))
		 (cons (cons 1 '(nil nil t))
		       (cons (cons 1 '(nil t nil))
			     (cons (cons 1 '(nil t t))
				   (cons (cons 1 '(t nil nil))
					 (cons (cons 2 '(t nil t))
					       (cons (cons 1 '(t t nil))
						     (cons (cons 1 '(t t t)) nil))))))))
	   2 '())


(qu-H-gate-e (cons (cons 0 '(nil nil nil))
		   (cons (cons 1 '(nil nil t))
			 (cons (cons 2 '(nil t nil))
			       (cons (cons 3 '(nil t t))
				     (cons (cons 4 '(t nil nil))
					   (cons (cons 5 '(t nil t))
						 (cons (cons 6 '(t t nil))
						       (cons (cons 7 '(t t t)) nil))))))))
	    2 1/10000 nil)



(defconst *eps* 1/1000)

(qstate-circuit-e '( (H 1)
		    (CN 1 2)
		    (CN 0 1)
		    (H 0)
		    (M 0)
		    (M 1)
		    )
		 (qstate-tensor-product (uniform-qstate-e 1 *eps*)
				       (zero-qstate 2))
		 *eps*
		 '(1/4 3/4))

|#

(defthm *-complex-2
  (implies (and (complexp x)
		(complexp y))
	   (equal (* x y)
		  (complex (- (* (realpart x) (realpart y))
			      (* (imagpart x) (imagpart y)))
			   (+ (* (realpart x) (imagpart y))
			      (* (imagpart x) (realpart y))))))
  :hints (("Goal"
	   :use ((:instance *-complex
			    (i (realpart x))
			    (j (imagpart x))
			    (r (realpart y))
			    (s (imagpart y)))
		 )
	   :in-theory (disable *-complex))))

(defthm complexp-complex
  (equal (complexp (complex x y))
	 (not (equal (realfix y) 0))))

(local
 (defthm conjugate-*-recognize-zero-lemma
   (implies (and (realp x1)
		 (realp x2)
		 (realp y1)
		 (realp y2)
		 (equal (+ (* x2 y1)
			   (* y2 x1))
			0))
	    (equal (+ (- (* x2 y1))
		      (- (* y2 x1)))
		   0))))

(defthm realpart-complex-*-real
  (implies (and (realp x)
		(complexp y))
	   (equal (realpart (* x y))
		  (* x (realpart y)))))

(defthm realpart-complex-*-not-complex
  (implies (and (not (complexp x))
		(complexp y))
	   (equal (realpart (* x y))
		  (* x (realpart y))))
  :hints (("Goal"
	   :cases ((realp x))))
  )

(defthm realpart-complex-*-not-complex-2
  (implies (and (not (complexp x))
		(complexp y))
	   (equal (realpart (* y x))
		  (* x (realpart y))))
  :hints (("Goal"
	   :cases ((realp x))))
  )

(defthm imagpart-complex-*-real
  (implies (and (realp x)
		(complexp y))
	   (equal (imagpart (* x y))
		  (* x (imagpart y)))))

(defthm imagpart-complex-*-not-complex
  (implies (and (not (complexp x))
		(complexp y))
	   (equal (imagpart (* x y))
		  (* x (imagpart y))))
  :hints (("Goal"
	   :cases ((realp x))))
  )

(defthm imagpart-complex-*-not-complex-2
  (implies (and (not (complexp x))
		(complexp y))
	   (equal (imagpart (* y x))
		  (* x (imagpart y))))
  )


(defthm *-real-complex-2
  (implies (and (realp x)
		(realp a)
		(realp b))
	   (equal (* x (complex a (- b)))
		  (complex (* a x) (- (* b x)))))
  :hints (("Goal"
	   :use ((:instance COMPLEX-DEFINITION
			    (x a)
			    (y (- b)))
		 (:instance COMPLEX-DEFINITION
			    (x (* a x))
			    (y (- (* b x))))
		 )))
  )

(defthm *-not-complex-complex-2
  (implies (and (not (complexp x))
		(realp a)
		(realp b))
	   (equal (* x (complex a (- b)))
		  (complex (* a x) (- (* b x)))))
  :hints (("Goal"
	   :cases ((realp x))))
  )

(defthmd *-real-complex-is-real->-must-be-zero
  (implies (and (realp x)
		(complexp y)
		(not (complexp (* x y))))
	   (equal (equal x 0) t)))

(defthm conjugate-*
  (equal (conjugate (* x y))
	 (* (conjugate x)
	    (conjugate y)))
  :hints (("Goal"
; Matt K. mod: required with the change after v7-4 to the definition of conjugate
;	   :use ((:instance *-real-complex-is-real->-must-be-zero (x x) (y y))
;		 (:instance *-real-complex-is-real->-must-be-zero (x y) (y x)))
           :cases ((and (complex/complex-rationalp x)
                        (complex/complex-rationalp y)))
	   :in-theory (enable conjugate))
	   )
  )

(defthm qustate-amplitudes-sum-squares-of-append
  (equal (qustate-amplitudes-sum-squares (append x y))
	 (+ (qustate-amplitudes-sum-squares x)
	    (qustate-amplitudes-sum-squares y))))


(defthm qstate-amplitudes-tensor-product-aux
  (equal (qustate-amplitudes-sum-squares (qstate-tensor-product-aux q y))
	 (* (car q) (conjugate (car q)) (qustate-amplitudes-sum-squares y))))

(defthm qstate-amplitudes-tensor-product
  (equal (qustate-amplitudes-sum-squares (qstate-tensor-product x y))
	 (* (qustate-amplitudes-sum-squares x)
	    (qustate-amplitudes-sum-squares y))))

(defthm qustate-norm-tensor-product
  (equal (qustate-norm (qstate-tensor-product x y))
	 (* (qustate-norm x)
	    (qustate-norm y))))

(defthm qustate-amplitudes-zero-qstate
  (equal (qustate-amplitudes-sum-squares (zero-qstate n))
	 1))

(defthm qustate-norm-zero-qstate
  (equal (qustate-norm (zero-qstate n))
	 1))

#|
I don't think I need these, and they're more trouble than they're worth for now:

(defthm qustate-amplitudes-one-qstate
  (equal (qustate-amplitudes-sum-squares (one-qstate n))
	 1))

(defthm qustate-norm-one-qstate
  (equal (qustate-norm (one-qstate n))
	 1))
|#

(defthm qustate-amplitudes-make-qubit
  (equal (qustate-amplitudes-sum-squares (make-qubit alpha beta))
	 (+ (* alpha (conjugate alpha))
	    (* beta  (conjugate beta)))))

(defthm qustate-norm-make-qubit
  (equal (qustate-norm (make-qubit alpha beta))
	 (acl2-sqrt (+ (* alpha (conjugate alpha))
		       (* beta  (conjugate beta))))))

(defthm realpart-not-complex
  (implies (and (acl2-numberp x)
		(not (complexp x)))
	   (equal (realpart x) x)))

(defthm realpart--
  (equal (realpart (- x))
	 (- (realpart x)))
  :hints (("Goal"
	   :use ((:instance *-real-complex
			    (x -1)
			    (a (realpart x))
			    (b (imagpart x)))))))

(defthm imagpart--
  (equal (imagpart (- x))
	 (- (imagpart x)))
  :hints (("Goal"
	   :use ((:instance *-real-complex
			    (x -1)
			    (a (realpart x))
			    (b (imagpart x)))))))

(defthm complex-swap-signs
  (implies (and (realp x)
		(realp y))
	   (equal (complex (- x) y)
		  (- (complex x (- y)))))
  :hints (("Goal"
	   :use ((:instance *-real-complex
			    (x -1)
			    (a (- x))
			    (b y))))))

(defthm conjugate--
  (implies (acl2-numberp x)
	   (equal (conjugate (- x))
		  (- (conjugate x))))
  :hints (("Goal"
	   :in-theory (enable conjugate)))
  )

(defthm conjugate-real
  (implies (realp x)
	   (equal (conjugate x) x))
  :hints (("Goal" :in-theory (enable conjugate))))

(defthm prod-/-sqrt-/-sqrt
  (implies (and (realp x)
		(<= 0 x)
		;(acl2-numberp y)
		)
	   (equal (* (/ (acl2-sqrt x))
		     (/ (acl2-sqrt x))
		     y)
		  (/ y x))))

(defthm qstate-amplitudes-H-gate-helper
  (equal (qustate-amplitudes-sum-squares (qu-H-gate-helper av n r))
	 (* (car av) (conjugate (car av))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable acl2-sqrt)
	   ))
  )

(defthm qstate-amplitudes-H-gate
  (equal (qustate-amplitudes-sum-squares (qu-H-gate s n r))
	 (qustate-amplitudes-sum-squares s))
  :hints (("Goal"
	   :in-theory (disable qu-H-gate-helper))))

(defthm qstate-norm-H-gate
  (equal (qustate-norm (qu-H-gate s n r))
	 (qustate-norm s)))

(defthm qustate-scale-by-1
  (implies (qustatep x)
	   (equal (qustate-scale x 1)
		  x)))

(defthm qustate-normalize-idempotent
  (implies (and (qustatep x)
		(equal (qustate-norm x) 1))
	   (equal (qustate-normalize-amplitudes x)
		  x)))




(defthm qustate-norm-teleport-initial-instance
  (equal (qustate-norm (qstate-tensor-product (make-qubit alpha beta)
					      (zero-qstate 2)))
	 (acl2-sqrt (+ (* alpha (conjugate alpha))
		       (* beta  (conjugate beta))))))

(defthm qustate-norm-teleport-initial-instance-even-better
  (implies (equal (+ (* alpha (conjugate alpha))
		     (* beta  (conjugate beta)))
		  1)
	   (equal (qustate-norm (qstate-tensor-product (make-qubit alpha beta)
						       (zero-qstate 2)))
		  1)))

(defthm qustate-normalize-teleport-initial-instance
  (implies (equal (+ (* alpha (conjugate alpha))
		     (* beta  (conjugate beta)))
		  1)
	   (equal (qustate-normalize (qstate-tensor-product (make-qubit alpha beta)
							    (zero-qstate 2)))
		  (qstate-tensor-product (make-qubit alpha beta)
					 (zero-qstate 2)))))


(defthm quantum-teleport-lemma-1
  (implies (equal (+ (* alpha (conjugate alpha))
		     (* beta  (conjugate beta)))
		  1)
	   (equal (qstate-circuit circuit
				  (qstate-tensor-product (make-qubit alpha beta)
							 (zero-qstate 2))
				  rs)
		  (qstate-circuit-aux circuit
				      (qstate-tensor-product (make-qubit alpha beta)
							     (zero-qstate 2))
				      rs)
		  ))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable qstate-circuit-aux
			       qstate-tensor-product
			       make-qubit
			       zero-qstate
			       (zero-qstate)
			       qustate-normalize)
	   )))

(defthm quantum-teleport-lemma-2
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta))
	   (equal (qstate-tensor-product (make-qubit alpha beta)
					 (zero-qstate 2))
		  (list (list alpha NIL NIL NIL)
			(list 0     NIL NIL T  )
			(list 0     NIL T   NIL)
			(list 0     NIL T   T  )
			(list beta  T   NIL NIL)
			(list 0     T   NIL T  )
			(list 0     T   T   NIL)
			(list 0     T   T   T  )))))


(defthm quantum-teleport-lemma-3
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		)
	   (equal (qustate-norm (list (list alpha NIL NIL NIL)
				      (list 0     NIL NIL T  )
				      (list 0     NIL T   NIL)
				      (list 0     NIL T   T  )
				      (list beta  T   NIL NIL)
				      (list 0     T   NIL T  )
				      (list 0     T   T   NIL)
				      (list 0     T   T   T  )))
		  1))
  :hints (("Goal"
	   :use ((:instance quantum-teleport-lemma-2)
		 (:instance qustate-norm-teleport-initial-instance-even-better))
	   :in-theory nil)))



(in-theory (disable acl2-sqrt (acl2-sqrt)))

(defthm quantum-teleport-lemma-4
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		)
	   (equal (qu-H-gate (list (list alpha NIL NIL NIL)
				   (list 0     NIL NIL T  )
				   (list 0     NIL T   NIL)
				   (list 0     NIL T   T  )
				   (list beta  T   NIL NIL)
				   (list 0     T   NIL T  )
				   (list 0     T   T   NIL)
				   (list 0     T   T   T  ))
			     1
			     0)
		  (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
			(list (/ alpha (acl2-sqrt 2)) NIL T   NIL)
			(list 0                       NIL NIL T  )
			(list 0                       NIL T   T  )
			(list 0                       NIL NIL NIL)
			(list 0                       NIL T   NIL)
			(list 0                       NIL NIL T)
			(list 0                       NIL T   T)
			(list (/ beta  (acl2-sqrt 2)) T   NIL NIL)
			(list (/ beta  (acl2-sqrt 2)) T   T   NIL)
			(list 0                       T   NIL T  )
			(list 0                       T   T   T  )
			(list 0                       T   NIL NIL)
			(list 0                       T   T   NIL)
			(list 0                       T   NIL T)
			(list 0                       T   T   T))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable (qu-h-gate))
	   )))

(defthm quantum-teleport-lemma-5
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		)
	   (equal (sort-and-merge (qu-H-gate (list (list alpha NIL NIL NIL)
						   (list 0     NIL NIL T  )
						   (list 0     NIL T   NIL)
						   (list 0     NIL T   T  )
						   (list beta  T   NIL NIL)
						   (list 0     T   NIL T  )
						   (list 0     T   T   NIL)
						   (list 0     T   T   T  ))
					     1
					     0))
		  (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
			(list 0                       NIL NIL T  )
			(list (/ alpha (acl2-sqrt 2)) NIL T   NIL)
			(list 0                       NIL T   T  )
			(list (/ beta  (acl2-sqrt 2)) T   NIL NIL)
			(list 0                       T   NIL T  )
			(list (/ beta  (acl2-sqrt 2)) T   T   NIL)
			(list 0                       T   T   T  ))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable qu-h-gate (qu-h-gate))
	   )))

(defthm quantum-teleport-lemma-6
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		)
	   (equal (qustate-norm (sort-and-merge (qu-H-gate (list (list alpha NIL NIL NIL)
								 (list 0     NIL NIL T  )
								 (list 0     NIL T   NIL)
								 (list 0     NIL T   T  )
								 (list beta  T   NIL NIL)
								 (list 0     T   NIL T  )
								 (list 0     T   T   NIL)
								 (list 0     T   T   T  ))
							   1
							   0)))
		  1))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable quantum-teleport-lemma-4 sort-and-merge qu-h-gate (qu-h-gate))
	   )))

(defthm quantum-teleport-lemma-7
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		;(realp r1) (<= 0 r1) (<= r1 1)
		;(realp r2) (<= 0 r2) (<= r2 1)
		)
	   (equal (qstate-circuit-aux (cons '(H 1) circuit)
				      (list (list alpha NIL NIL NIL)
					    (list 0     NIL NIL T  )
					    (list 0     NIL T   NIL)
					    (list 0     NIL T   T  )
					    (list beta  T   NIL NIL)
					    (list 0     T   NIL T  )
					    (list 0     T   T   NIL)
					    (list 0     T   T   T  ))
				      rs)
		  (qstate-circuit-aux circuit
				      (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
					    (list 0                       NIL NIL T  )
					    (list (/ alpha (acl2-sqrt 2)) NIL T   NIL)
					    (list 0                       NIL T   T  )
					    (list (/ beta  (acl2-sqrt 2)) T   NIL NIL)
					    (list 0                       T   NIL T  )
					    (list (/ beta  (acl2-sqrt 2)) T   T   NIL)
					    (list 0                       T   T   T  ))
				      rs)))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable quantum-teleport-lemma-4
			       qu-h-gate (qu-h-gate)
			       qustate-normalize-amplitudes sort-and-merge (sort-and-merge))
	   )))

(defthm quantum-teleport-lemma-8
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		;(realp r1) (<= 0 r1) (<= r1 1)
		;(realp r2) (<= 0 r2) (<= r2 1)
		)
	   (equal (qstate-circuit-aux (cons '(CN 1 2) circuit)
				      (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
					    (list 0                       NIL NIL T  )
					    (list (/ alpha (acl2-sqrt 2)) NIL T   NIL)
					    (list 0                       NIL T   T  )
					    (list (/ beta  (acl2-sqrt 2)) T   NIL NIL)
					    (list 0                       T   NIL T  )
					    (list (/ beta  (acl2-sqrt 2)) T   T   NIL)
					    (list 0                       T   T   T  ))
				      rs)
		  (qstate-circuit-aux circuit
				      (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
					    (list 0                       NIL NIL T  )
					    (list 0                       NIL T   NIL)
					    (list (/ alpha (acl2-sqrt 2)) NIL T   T)
					    (list (/ beta  (acl2-sqrt 2)) T   NIL NIL)
					    (list 0                       T   NIL T  )
					    (list 0                       T   T   NIL)
					    (list (/ beta  (acl2-sqrt 2)) T   T   T  ))
				      rs)))
  )

(defthm quantum-teleport-lemma-9
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		;(realp r1) (<= 0 r1) (<= r1 1)
		;(realp r2) (<= 0 r2) (<= r2 1)
		)
	   (equal (qstate-circuit-aux (cons '(CN 0 1) circuit)
				      (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
					    (list 0                       NIL NIL T  )
					    (list 0                       NIL T   NIL)
					    (list (/ alpha (acl2-sqrt 2)) NIL T   T)
					    (list (/ beta  (acl2-sqrt 2)) T   NIL NIL)
					    (list 0                       T   NIL T  )
					    (list 0                       T   T   NIL)
					    (list (/ beta  (acl2-sqrt 2)) T   T   T  ))
				      rs)
		  (qstate-circuit-aux circuit
				      (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
					    (list 0                       NIL NIL T  )
					    (list 0                       NIL T   NIL)
					    (list (/ alpha (acl2-sqrt 2)) NIL T   T)
					    (list 0                       T   NIL NIL)
					    (list (/ beta  (acl2-sqrt 2)) T   NIL T  )
					    (list (/ beta  (acl2-sqrt 2)) T   T   NIL)
					    (list 0                       T   T   T  ))
				      rs)))
  )

(defthm quantum-teleport-lemma-10
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		)
	   (equal (qu-H-gate (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
				   (list 0                       NIL NIL T  )
				   (list 0                       NIL T   NIL)
				   (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
				   (list 0                       T   NIL NIL)
				   (list (/ beta  (acl2-sqrt 2)) T   NIL T  )
				   (list (/ beta  (acl2-sqrt 2)) T   T   NIL)
				   (list 0                       T   T   T  ))
			     0
			     0)
		  (list (list (/ alpha 2)     NIL NIL NIL)
			(list (/ alpha 2)     T   NIL NIL)
			(list 0               NIL NIL T  )
			(list 0               T   NIL T  )
			(list 0               NIL T   NIL)
			(list 0               T   T   NIL)
			(list (/ alpha 2)     NIL T   T  )
			(list (/ alpha 2)     T   T   T  )
			(list 0               NIL NIL NIL)
			(list 0               T   NIL NIL)
			(list (/ beta  2)     NIL NIL T  )
			(list (- (/ beta  2)) T   NIL T  )
			(list (/ beta  2)     NIL T   NIL)
			(list (- (/ beta  2)) T   T   NIL)
			(list 0               NIL T   T  )
			(list 0               T   T   T  ))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable (qu-h-gate))
	   )))

(defthm quantum-teleport-lemma-11
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		)
	   (equal (sort-and-merge (qu-H-gate (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
						   (list 0                       NIL NIL T  )
						   (list 0                       NIL T   NIL)
						   (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
						   (list 0                       T   NIL NIL)
						   (list (/ beta  (acl2-sqrt 2)) T   NIL T  )
						   (list (/ beta  (acl2-sqrt 2)) T   T   NIL)
						   (list 0                       T   T   T  ))
					     0
					     0))
		  (list (list (/ alpha 2)    NIL NIL NIL)
			(list (/ beta 2)     NIL NIL T  )
			(list (/ beta 2)     NIL T   NIL)
			(list (/ alpha 2)    NIL T   T  )
			(list (/ alpha 2)    T   NIL NIL)
			(list (- (/ beta 2)) T   NIL T  )
			(list (- (/ beta 2)) T   T   NIL)
			(list (/ alpha 2)    T   T   T  ))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-10))
	   :in-theory (disable quantum-teleport-lemma-10
			       qu-h-gate (qu-h-gate))
	   )))

(defthm quantum-teleport-lemma-12
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		)
	   (equal (qustate-norm (sort-and-merge (qu-H-gate (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
								 (list 0                       NIL NIL T  )
								 (list 0                       NIL T   NIL)
								 (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
								 (list 0                       T   NIL NIL)
								 (list (/ beta  (acl2-sqrt 2)) T   NIL T  )
								 (list (/ beta  (acl2-sqrt 2)) T   T   NIL)
								 (list 0                       T   T   T  ))
							   0
							   0)))
		  1))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-11))
	   :in-theory (disable quantum-teleport-lemma-11
			       qu-h-gate (qu-h-gate))
	   )))

(defthm quantum-teleport-lemma-13
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		;(realp r1) (<= 0 r1) (<= r1 1)
		;(realp r2) (<= 0 r2) (<= r2 1)
		)
	   (equal (qstate-circuit-aux (cons '(H 0) circuit)
				      (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
					    (list 0                       NIL NIL T  )
					    (list 0                       NIL T   NIL)
					    (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
					    (list 0                       T   NIL NIL)
					    (list (/ beta  (acl2-sqrt 2)) T   NIL T  )
					    (list (/ beta  (acl2-sqrt 2)) T   T   NIL)
					    (list 0                       T   T   T  ))
				      rs)
		  (qstate-circuit-aux circuit
				      (list (list (/ alpha 2)    NIL NIL NIL)
					    (list (/ beta 2)     NIL NIL T  )
					    (list (/ beta 2)     NIL T   NIL)
					    (list (/ alpha 2)    NIL T   T  )
					    (list (/ alpha 2)    T   NIL NIL)
					    (list (- (/ beta 2)) T   NIL T  )
					    (list (- (/ beta 2)) T   T   NIL)
					    (list (/ alpha 2)    T   T   T  ))
				      rs)))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-11)
		 (:instance quantum-teleport-lemma-12))
	   :in-theory (disable quantum-teleport-lemma-10
			       quantum-teleport-lemma-11
			       quantum-teleport-lemma-12
			       qu-h-gate (qu-h-gate)
			       qustate-normalize-amplitudes sort-and-merge (sort-and-merge))
	   )))

(defthm quantum-teleport-lemma-14
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qu-M-gate (list (list (/ alpha 2)    NIL NIL NIL)
				   (list (/ beta 2)     NIL NIL T  )
				   (list (/ beta 2)     NIL T   NIL)
				   (list (/ alpha 2)    NIL T   T  )
				   (list (/ alpha 2)    T   NIL NIL)
				   (list (- (/ beta 2)) T   NIL T  )
				   (list (- (/ beta 2)) T   T   NIL)
				   (list (/ alpha 2)    T   T   T  ))
			     0
			     r1)
		  (if (< r1 1/2)
		      (list (list (/ alpha 2)    NIL NIL NIL)
			    (list (/ beta 2)     NIL NIL T  )
			    (list (/ beta 2)     NIL T   NIL)
			    (list (/ alpha 2)    NIL T   T  ))
		    (list (list (/ alpha 2)    T   NIL NIL)
			  (list (- (/ beta 2)) T   NIL T  )
			  (list (- (/ beta 2)) T   T   NIL)
			  (list (/ alpha 2)    T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable (qu-m-gate))
	   )))

(defthm quantum-teleport-lemma-15
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (sort-and-merge (qu-M-gate (list (list (/ alpha 2)    NIL NIL NIL)
						   (list (/ beta 2)     NIL NIL T  )
						   (list (/ beta 2)     NIL T   NIL)
						   (list (/ alpha 2)    NIL T   T  )
						   (list (/ alpha 2)    T   NIL NIL)
						   (list (- (/ beta 2)) T   NIL T  )
						   (list (- (/ beta 2)) T   T   NIL)
						   (list (/ alpha 2)    T   T   T  ))
					     0
					     r1))
		  (if (< r1 1/2)
		      (list (list (/ alpha 2)    NIL NIL NIL)
			    (list (/ beta 2)     NIL NIL T  )
			    (list (/ beta 2)     NIL T   NIL)
			    (list (/ alpha 2)    NIL T   T  )
			    (list 0              T   NIL NIL)
			    (list 0 		 T   NIL T  )
			    (list 0 		 T   T   NIL)
			    (list 0 		 T   T   T  ))
		    (list (list 0              NIL NIL NIL)
			  (list 0              NIL NIL T  )
			  (list 0              NIL T   NIL)
			  (list 0              NIL T   T  )
			  (list (/ alpha 2)    T   NIL NIL)
			  (list (- (/ beta 2)) T   NIL T  )
			  (list (- (/ beta 2)) T   T   NIL)
			  (list (/ alpha 2)    T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-14))
	   :in-theory (disable quantum-teleport-lemma-14
			       qu-m-gate (qu-m-gate))
	   )))

;; Proved by tau-system
(defthm quantum-teleport-lemma-16
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (+ (* 1/4 ALPHA (CONJUGATE ALPHA))
		     (* 1/4 ALPHA (CONJUGATE ALPHA))
		     (* 1/4 BETA (CONJUGATE BETA))
		     (* 1/4 BETA (CONJUGATE BETA)))
		  1/2))
  )


(defthm quantum-teleport-lemma-17
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qustate-norm (sort-and-merge (qu-M-gate (list (list (/ alpha 2)    NIL NIL NIL)
								 (list (/ beta 2)     NIL NIL T  )
								 (list (/ beta 2)     NIL T   NIL)
								 (list (/ alpha 2)    NIL T   T  )
								 (list (/ alpha 2)    T   NIL NIL)
								 (list (- (/ beta 2)) T   NIL T  )
								 (list (- (/ beta 2)) T   T   NIL)
								 (list (/ alpha 2)    T   T   T  ))
							   0
							   r1)))
		  (/ (acl2-sqrt 2))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-15))
	   :in-theory (disable quantum-teleport-lemma-15
			       qu-m-gate (qu-m-gate)
			       sort-and-merge (sort-and-merge)
			       )
	   )))

(defthm 2-/-sqrt-2
  (equal (* 2 (/ (acl2-sqrt 2)))
	 (acl2-sqrt 2)))

(defthm 2-/-sqrt-2-*-x
  (equal (* 2 (/ (acl2-sqrt 2)) x)
	 (* (acl2-sqrt 2) x))
  :hints (("Goal"
	   :use ((:instance (:theorem (implies (equal x1 x2) (equal (* x1 y) (* x2 y))))
			    (x1 (* 2 (/ (acl2-sqrt 2))))
			    (x2 (acl2-sqrt 2))
			    (y x))
		 (:instance 2-/-sqrt-2))
	   :in-theory (disable 2-/-sqrt-2))))

(defthm quantum-teleport-lemma-18
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qustate-normalize (qu-M-gate (list (list (/ alpha 2)    NIL NIL NIL)
						      (list (/ beta 2)     NIL NIL T  )
						      (list (/ beta 2)     NIL T   NIL)
						      (list (/ alpha 2)    NIL T   T  )
						      (list (/ alpha 2)    T   NIL NIL)
						      (list (- (/ beta 2)) T   NIL T  )
						      (list (- (/ beta 2)) T   T   NIL)
						      (list (/ alpha 2)    T   T   T  ))
						0
						r1))
		  (if (< r1 1/2)
		      (list (list (/ alpha (acl2-sqrt 2))    NIL NIL NIL)
			    (list (/ beta (acl2-sqrt 2))     NIL NIL T  )
			    (list (/ beta (acl2-sqrt 2))     NIL T   NIL)
			    (list (/ alpha (acl2-sqrt 2))    NIL T   T  )
			    (list 0              	     T   NIL NIL)
			    (list 0 		 	     T   NIL T  )
			    (list 0 		 	     T   T   NIL)
			    (list 0 		 	     T   T   T  ))
		    (list (list 0              		   NIL NIL NIL)
			  (list 0              		   NIL NIL T  )
			  (list 0              		   NIL T   NIL)
			  (list 0              		   NIL T   T  )
			  (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
			  (list (- (/ beta (acl2-sqrt 2))) T   NIL T  )
			  (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
			  (list (/ alpha (acl2-sqrt 2))    T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-15)
		 (:instance quantum-teleport-lemma-17))
	   :in-theory (disable quantum-teleport-lemma-15
			       quantum-teleport-lemma-17
			       qu-m-gate (qu-m-gate)
			       sort-and-merge (sort-and-merge)
			       qustate-norm (qustate-norm)
			       equal-/))))


(defthm quantum-teleport-lemma-19
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		;(realp r1) (<= 0 r1) (<= r1 1)
		;(realp r2) (<= 0 r2) (<= r2 1)
		)
	   (equal (qstate-circuit-aux (cons '(M 0) circuit)
				      (list (list (/ alpha 2)    NIL NIL NIL)
					    (list (/ beta 2)     NIL NIL T  )
					    (list (/ beta 2)     NIL T   NIL)
					    (list (/ alpha 2)    NIL T   T  )
					    (list (/ alpha 2)    T   NIL NIL)
					    (list (- (/ beta 2)) T   NIL T  )
					    (list (- (/ beta 2)) T   T   NIL)
					    (list (/ alpha 2)    T   T   T  ))
				      (cons r1 rs))
		  (if (< r1 1/2)
		      (qstate-circuit-aux circuit
					  (list (list (/ alpha (acl2-sqrt 2))    NIL NIL NIL)
						(list (/ beta (acl2-sqrt 2))     NIL NIL T  )
						(list (/ beta (acl2-sqrt 2))     NIL T   NIL)
						(list (/ alpha (acl2-sqrt 2))    NIL T   T  )
						(list 0              	     T   NIL NIL)
						(list 0 		 	     T   NIL T  )
						(list 0 		 	     T   T   NIL)
						(list 0 		 	     T   T   T  ))
					  rs)
		    (qstate-circuit-aux circuit
					(list (list 0              		   NIL NIL NIL)
					      (list 0              		   NIL NIL T  )
					      (list 0              		   NIL T   NIL)
					      (list 0              		   NIL T   T  )
					      (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
					      (list (- (/ beta (acl2-sqrt 2))) T   NIL T  )
					      (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
					      (list (/ alpha (acl2-sqrt 2))    T   T   T  ))
					rs))))
  :hints (("Goal" :do-not-induct t
	   :use (;(:instance quantum-teleport-lemma-11)
		 (:instance quantum-teleport-lemma-18))
	   :in-theory (disable ;quantum-teleport-lemma-11
			       quantum-teleport-lemma-18
			       qu-h-gate (qu-h-gate)
			       qustate-normalize (qustate-normalize)
			       sort-and-merge (sort-and-merge))
	   )))





(defthm quantum-teleport-lemma-20
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qu-M-gate (list (list (/ alpha (acl2-sqrt 2))    NIL NIL NIL)
				   (list (/ beta (acl2-sqrt 2))     NIL NIL T  )
				   (list (/ beta (acl2-sqrt 2))     NIL T   NIL)
				   (list (/ alpha (acl2-sqrt 2))    NIL T   T  )
				   (list 0              	    T   NIL NIL)
				   (list 0 		 	    T   NIL T  )
				   (list 0 		 	    T   T   NIL)
				   (list 0 		 	    T   T   T  ))
			     1
			     r2)
		  (if (< r2 1/2)
		      (list (list (/ alpha (acl2-sqrt 2))    NIL NIL NIL)
			    (list (/ beta (acl2-sqrt 2))     NIL NIL T  )
			    (list 0              	     T   NIL NIL)
			    (list 0 		 	     T   NIL T  ))
		    (list (list (/ beta (acl2-sqrt 2))  NIL T   NIL)
			  (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
			  (list 0 		 	T   T   NIL)
			  (list 0 		 	T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable (qu-m-gate))
	   )))


(defthm quantum-teleport-lemma-21
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (sort-and-merge (qu-M-gate (list (list (/ alpha (acl2-sqrt 2))    NIL NIL NIL)
						   (list (/ beta (acl2-sqrt 2))     NIL NIL T  )
						   (list (/ beta (acl2-sqrt 2))     NIL T   NIL)
						   (list (/ alpha (acl2-sqrt 2))    NIL T   T  )
						   (list 0              	    T   NIL NIL)
						   (list 0 		 	    T   NIL T  )
						   (list 0 		 	    T   T   NIL)
						   (list 0 		 	    T   T   T  ))
					     1
					     r2))
		  (if (< r2 1/2)
		      (list (list (/ alpha (acl2-sqrt 2))    NIL NIL NIL)
			    (list (/ beta (acl2-sqrt 2))     NIL NIL T  )
			    (list 0                          NIL T   NIL)
			    (list 0                          NIL T   T  )
			    (list 0              	     T   NIL NIL)
			    (list 0 		 	     T   NIL T  )
			    (list 0                          T   T   NIL)
			    (list 0                          T   T   T  ))
		    (list (list 0 		 	NIL NIL NIL)
			  (list 0 		 	NIL NIL T  )
			  (list (/ beta (acl2-sqrt 2))  NIL T   NIL)
			  (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
			  (list 0 		 	T   NIL NIL)
			  (list 0 		 	T   NIL T  )
			  (list 0 		 	T   T   NIL)
			  (list 0 		 	T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-20))
	   :in-theory (disable quantum-teleport-lemma-20
			       qu-m-gate (qu-m-gate))
	   )))

(defthm numberp-conjugate
  (implies (acl2-numberp x)
	   (acl2-numberp (conjugate x)))
  :hints (("Goal"
	   :in-theory (enable conjugate))))

;; Proved by tau-system
(defthm quantum-teleport-lemma-22
  (implies (and (acl2-numberp a1)
		(acl2-numberp a2)
		(acl2-numberp b1)
		(acl2-numberp b2)
		(equal (+ (* a1 a2) (* b1 b2)) 1))
	   (equal (+ (* 1/2 a1 a2)
		     (* 1/2 b1 b2))
		  1/2)))

(defthm quantum-teleport-lemma-23
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qustate-norm (sort-and-merge (qu-M-gate (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
								 (list (/ beta (acl2-sqrt 2))  NIL NIL T  )
								 (list (/ beta (acl2-sqrt 2))  NIL T   NIL)
								 (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
								 (list 0              	       T   NIL NIL)
								 (list 0 		       T   NIL T  )
								 (list 0 		       T   T   NIL)
								 (list 0 		       T   T   T  ))
							   1
							   r2)))
		  (/ (acl2-sqrt 2))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-21))
	   :in-theory (disable quantum-teleport-lemma-21
			       qu-m-gate (qu-m-gate)
			       sort-and-merge (sort-and-merge)
			       )
	   )
	  ))


(defthm quantum-teleport-lemma-24
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qustate-normalize (qu-M-gate (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
						      (list (/ beta (acl2-sqrt 2))  NIL NIL T  )
						      (list (/ beta (acl2-sqrt 2))  NIL T   NIL)
						      (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
						      (list 0              	    T   NIL NIL)
						      (list 0 		       	    T   NIL T  )
						      (list 0 		       	    T   T   NIL)
						      (list 0 		       	    T   T   T  ))
						1
						r2))
		  (if (< r2 1/2)
		      (list (list alpha NIL NIL NIL)
			    (list beta  NIL NIL T  )
			    (list 0     NIL T   NIL)
			    (list 0     NIL T   T  )
			    (list 0     T   NIL NIL)
			    (list 0 	T   NIL T  )
			    (list 0     T   T   NIL)
			    (list 0     T   T   T  ))
		    (list (list 0     NIL NIL NIL)
			  (list 0     NIL NIL T  )
			  (list beta  NIL T   NIL)
			  (list alpha NIL T   T  )
			  (list 0     T   NIL NIL)
			  (list 0     T   NIL T  )
			  (list 0     T   T   NIL)
			  (list 0     T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-21)
		 (:instance quantum-teleport-lemma-23))
	   :in-theory (disable quantum-teleport-lemma-21
			       quantum-teleport-lemma-23
			       qu-m-gate (qu-m-gate)
			       sort-and-merge (sort-and-merge)
			       qustate-norm (qustate-norm)
			       equal-/))))


(defthm quantum-teleport-lemma-25
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		;(realp r1) (<= 0 r1) (<= r1 1)
		;(realp r2) (<= 0 r2) (<= r2 1)
		)
	   (equal (qstate-circuit-aux (cons '(M 1) circuit)
				      (list (list (/ alpha (acl2-sqrt 2)) NIL NIL NIL)
						      (list (/ beta (acl2-sqrt 2))  NIL NIL T  )
						      (list (/ beta (acl2-sqrt 2))  NIL T   NIL)
						      (list (/ alpha (acl2-sqrt 2)) NIL T   T  )
						      (list 0              	    T   NIL NIL)
						      (list 0 		       	    T   NIL T  )
						      (list 0 		       	    T   T   NIL)
						      (list 0 		       	    T   T   T  ))
				      (cons r2 rs))
		  (if (< r2 1/2)
		      (qstate-circuit-aux circuit
					  (list (list alpha NIL NIL NIL)
						(list beta  NIL NIL T  )
						(list 0     NIL T   NIL)
						(list 0     NIL T   T  )
						(list 0     T   NIL NIL)
						(list 0 	T   NIL T  )
						(list 0     T   T   NIL)
						(list 0     T   T   T  ))
					  rs)
		    (qstate-circuit-aux circuit
					(list (list 0     NIL NIL NIL)
					      (list 0     NIL NIL T  )
					      (list beta  NIL T   NIL)
					      (list alpha NIL T   T  )
					      (list 0     T   NIL NIL)
					      (list 0     T   NIL T  )
					      (list 0     T   T   NIL)
					      (list 0     T   T   T  ))
					rs))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-24))
	   :in-theory (disable quantum-teleport-lemma-24
			       qu-h-gate (qu-h-gate)
			       qustate-normalize (qustate-normalize)
			       sort-and-merge (sort-and-merge))
	   )))

(defthm quantum-teleport-lemma-26
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qu-M-gate (list (list 0              	    NIL NIL NIL)
				   (list 0              	    NIL NIL T  )
				   (list 0              	    NIL T   NIL)
				   (list 0              	    NIL T   T  )
				   (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
				   (list (- (/ beta (acl2-sqrt 2))) T   NIL T  )
				   (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
				   (list (/ alpha (acl2-sqrt 2))    T   T   T  ))
			     1
			     r2)
		  (if (< r2 1/2)
		      (list (list 0              	     NIL NIL NIL)
			    (list 0              	     NIL NIL T  )
			    (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
			    (list (- (/ beta (acl2-sqrt 2))) T   NIL T  ))
		    (list (list 0              	    	   NIL T   NIL)
			  (list 0              	    	   NIL T   T  )
			  (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
			  (list (/ alpha (acl2-sqrt 2))    T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable (qu-m-gate))
	   )))

(defthm quantum-teleport-lemma-27
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (sort-and-merge (qu-M-gate (list (list 0              	    NIL NIL NIL)
						   (list 0              	    NIL NIL T  )
						   (list 0              	    NIL T   NIL)
						   (list 0              	    NIL T   T  )
						   (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
						   (list (- (/ beta (acl2-sqrt 2))) T   NIL T  )
						   (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
						   (list (/ alpha (acl2-sqrt 2))    T   T   T  ))
					     1
					     r2))
		  (if (< r2 1/2)
		      (list (list 0              	     NIL NIL NIL)
			    (list 0              	     NIL NIL T  )
			    (list 0                          NIL T   NIL)
			    (list 0                          NIL T   T  )
			    (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
			    (list (- (/ beta (acl2-sqrt 2))) T   NIL T  )
			    (list 0                          T   T   NIL)
			    (list 0                          T   T   T  ))
		    (list (list 0 		 	   NIL NIL NIL)
			  (list 0 		 	   NIL NIL T  )
			  (list 0                          NIL T   NIL)
			  (list 0                          NIL T   T  )
			  (list 0 		 	   T   NIL NIL)
			  (list 0 		 	   T   NIL T  )
			  (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
			  (list (/ alpha (acl2-sqrt 2))    T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-26))
	   :in-theory (disable quantum-teleport-lemma-26
			       qu-m-gate (qu-m-gate))
	   )))

(defthm quantum-teleport-lemma-28
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qustate-norm (sort-and-merge (qu-M-gate (list (list 0              	    	  NIL NIL NIL)
								 (list 0              	    	  NIL NIL T  )
								 (list 0              	    	  NIL T   NIL)
								 (list 0              	    	  NIL T   T  )
								 (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
								 (list (- (/ beta (acl2-sqrt 2))) T   NIL T  )
								 (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
								 (list (/ alpha (acl2-sqrt 2))    T   T   T  ))
							   1
							   r2)))
		  (/ (acl2-sqrt 2))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-27))
	   :in-theory (disable quantum-teleport-lemma-27
			       qu-m-gate (qu-m-gate)
			       sort-and-merge (sort-and-merge)
			       )
	   )
	  ))

(defthm quantum-teleport-lemma-29
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qustate-normalize (qu-M-gate (list (list 0          	    	       NIL NIL NIL)
						      (list 0          	    	       NIL NIL T  )
						      (list 0          	    	       NIL T   NIL)
						      (list 0          	    	       NIL T   T  )
						      (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
						      (list (- (/ beta (acl2-sqrt 2))) T   NIL T  )
						      (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
						      (list (/ alpha (acl2-sqrt 2))    T   T   T  ))
						1
						r2))
		  		  (if (< r2 1/2)
		      (list (list 0        NIL NIL NIL)
			    (list 0        NIL NIL T  )
			    (list 0        NIL T   NIL)
			    (list 0        NIL T   T  )
			    (list alpha    T   NIL NIL)
			    (list (- beta) T   NIL T  )
			    (list 0        T   T   NIL)
			    (list 0        T   T   T  ))
		    (list (list 0 	 NIL NIL NIL)
			  (list 0 	 NIL NIL T  )
			  (list 0        NIL T   NIL)
			  (list 0        NIL T   T  )
			  (list 0 	 T   NIL NIL)
			  (list 0 	 T   NIL T  )
			  (list (- beta) T   T   NIL)
			  (list alpha    T   T   T  )))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-27)
		 (:instance quantum-teleport-lemma-28))
	   :in-theory (disable quantum-teleport-lemma-27
			       quantum-teleport-lemma-28
			       qu-m-gate (qu-m-gate)
			       sort-and-merge (sort-and-merge)
			       qustate-norm (qustate-norm)
			       equal-/))))

(defthm quantum-teleport-lemma-30
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		;(realp r1) (<= 0 r1) (<= r1 1)
		;(realp r2) (<= 0 r2) (<= r2 1)
		)
	   (equal (qstate-circuit-aux (cons '(M 1) circuit)
				      (list (list 0          	    	       NIL NIL NIL)
					    (list 0          	    	       NIL NIL T  )
					    (list 0          	    	       NIL T   NIL)
					    (list 0          	    	       NIL T   T  )
					    (list (/ alpha (acl2-sqrt 2))    T   NIL NIL)
					    (list (- (/ beta (acl2-sqrt 2))) T   NIL T  )
					    (list (- (/ beta (acl2-sqrt 2))) T   T   NIL)
					    (list (/ alpha (acl2-sqrt 2))    T   T   T  ))
				      (cons r2 rs))
		  (if (< r2 1/2)
		      (qstate-circuit-aux circuit
					  (list (list 0        NIL NIL NIL)
						(list 0        NIL NIL T  )
						(list 0        NIL T   NIL)
						(list 0        NIL T   T  )
						(list alpha    T   NIL NIL)
						(list (- beta) T   NIL T  )
						(list 0        T   T   NIL)
						(list 0        T   T   T  ))
					  rs)
		    (qstate-circuit-aux circuit
					(list (list 0 	 NIL NIL NIL)
					      (list 0 	 NIL NIL T  )
					      (list 0        NIL T   NIL)
					      (list 0        NIL T   T  )
					      (list 0 	 T   NIL NIL)
					      (list 0 	 T   NIL T  )
					      (list (- beta) T   T   NIL)
					      (list alpha    T   T   T  ))
					rs))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance quantum-teleport-lemma-29))
	   :in-theory (disable quantum-teleport-lemma-29
			       qu-h-gate (qu-h-gate)
			       qustate-normalize (qustate-normalize)
			       sort-and-merge (sort-and-merge))
	   )))

(defthm quantum-teleport-lemma-31
  (equal (qstate-circuit-aux nil qstate rs) qstate))

(defthm quantum-teleport-main-lemma
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qstate-circuit '( (H 1)
				     (CN 1 2)
				     (CN 0 1)
				     (H 0)
				     (M 0)
				     (M 1) )
				  (qstate-tensor-product (make-qubit alpha beta)
							 (zero-qstate 2))
				  (list* r1 r2 rs))
		  (if (< r1 1/2)
		      (if (< r2 1/2)
			  (list (list alpha NIL NIL NIL)
				(list beta  NIL NIL T  )
				(list 0     NIL T   NIL)
				(list 0     NIL T   T  )
				(list 0     T   NIL NIL)
				(list 0 	T   NIL T  )
				(list 0     T   T   NIL)
				(list 0     T   T   T  ))
			(list (list 0     NIL NIL NIL)
			      (list 0     NIL NIL T  )
			      (list beta  NIL T   NIL)
			      (list alpha NIL T   T  )
			      (list 0     T   NIL NIL)
			      (list 0     T   NIL T  )
			      (list 0     T   T   NIL)
			      (list 0     T   T   T  )))
		    (if (< r2 1/2)
			(list (list 0        NIL NIL NIL)
			      (list 0        NIL NIL T  )
			      (list 0        NIL T   NIL)
			      (list 0        NIL T   T  )
			      (list alpha    T   NIL NIL)
			      (list (- beta) T   NIL T  )
			      (list 0        T   T   NIL)
			      (list 0        T   T   T  ))
		      (list (list 0 	 NIL NIL NIL)
			    (list 0 	 NIL NIL T  )
			    (list 0        NIL T   NIL)
			    (list 0        NIL T   T  )
			    (list 0 	 T   NIL NIL)
			    (list 0 	 T   NIL T  )
			    (list (- beta) T   T   NIL)
			    (list alpha    T   T   T  ))))))
  :hints  (("Goal"
	    :use ((:instance quantum-teleport-lemma-1
			     (circuit '( (H 1)
				     (CN 1 2)
				     (CN 0 1)
				     (H 0)
				     (M 0)
				     (M 1) ))
			     (rs (list* r1 r2 rs)))
		  (:instance quantum-teleport-lemma-2)
		  (:instance quantum-teleport-lemma-7
			     (circuit '( (CN 1 2)
				     (CN 0 1)
				     (H 0)
				     (M 0)
				     (M 1) ))
			     (rs (list* r1 r2 rs)))
		  (:instance quantum-teleport-lemma-8
			     (circuit '( (CN 0 1)
				     (H 0)
				     (M 0)
				     (M 1) ))
			     (rs (list* r1 r2 rs)))
		  (:instance quantum-teleport-lemma-9
			     (circuit '( (H 0)
				     (M 0)
				     (M 1) ))
			     (rs (list* r1 r2 rs)))
		  (:instance quantum-teleport-lemma-13
			     (circuit '( (M 0)
				     (M 1) ))
			     (rs (list* r1 r2 r2)))
		  (:instance quantum-teleport-lemma-19
			     (circuit '( (M 1) ))
			     (rs (list* r2 rs)))
		  (:instance quantum-teleport-lemma-25
			     (circuit nil)
			     (rs rs))
		  (:instance quantum-teleport-lemma-30
			     (circuit nil)
			     (rs rs))
		  )
	    :in-theory (disable quantum-teleport-lemma-1
				quantum-teleport-lemma-2
				quantum-teleport-lemma-7
				quantum-teleport-lemma-8
				quantum-teleport-lemma-9
				quantum-teleport-lemma-13
				quantum-teleport-lemma-19
				quantum-teleport-lemma-25
				quantum-teleport-lemma-30
				qstate-tensor-product (qstate-tensor-product)
				make-qubit (make-qubit)
				zero-qstate (zero-qstate)
				qstate-circuit (qstate-circuit)
				qustate-normalize (qustate-normalize))))
  )


(defun quantum-teleportation-alice (alpha beta r1 r2)
  (qstate-circuit '( (H 1)
                     (CN 1 2)
                     (CN 0 1)
                     (H 0)
                     (M 0)
                     (M 1) )
                  (qstate-tensor-product (make-qubit alpha beta)
                                         (zero-qstate 2))
                  (list r1 r2)))

(defthm quantum-teleportation-alice-value
  (implies (and (acl2-numberp alpha)
                (acl2-numberp beta)
                (equal (+ (* alpha (conjugate alpha))
                          (* beta  (conjugate beta)))
                       1))
           (equal (quantum-teleportation-alice alpha beta r1 r2)
                  (if (< r1 1/2)
                      (if (< r2 1/2)
                          (list (list alpha NIL NIL NIL)
                                (list beta  NIL NIL T  )
                                (list 0     NIL T   NIL)
                                (list 0     NIL T   T  )
                                (list 0     T   NIL NIL)
                                (list 0         T   NIL T  )
                                (list 0     T   T   NIL)
                                (list 0     T   T   T  ))
                        (list (list 0     NIL NIL NIL)
                              (list 0     NIL NIL T  )
                              (list beta  NIL T   NIL)
			      (list alpha NIL T   T  )
			      (list 0     T   NIL NIL)
			      (list 0     T   NIL T  )
			      (list 0     T   T   NIL)
			      (list 0     T   T   T  )))
		    (if (< r2 1/2)
			(list (list 0        NIL NIL NIL)
			      (list 0        NIL NIL T  )
			      (list 0        NIL T   NIL)
			      (list 0        NIL T   T  )
			      (list alpha    T   NIL NIL)
			      (list (- beta) T   NIL T  )
			      (list 0        T   T   NIL)
			      (list 0        T   T   T  ))
		      (list (list 0 	 NIL NIL NIL)
			    (list 0 	 NIL NIL T  )
			    (list 0        NIL T   NIL)
			    (list 0        NIL T   T  )
			    (list 0 	 T   NIL NIL)
			    (list 0 	 T   NIL T  )
			    (list (- beta) T   T   NIL)
			    (list alpha    T   T   T  ))))))
  :hints (("Goal"
	   :use ((:instance quantum-teleport-main-lemma (rs nil)))
	   :in-theory (disable quantum-teleport-main-lemma
			       qstate-tensor-product (qstate-tensor-product)
			       make-qubit (make-qubit)
			       zero-qstate (zero-qstate)
			       qstate-circuit (qstate-circuit)
			       qustate-normalize (qustate-normalize))))
  )

(in-theory (disable quantum-teleportation-alice))

(defthm qustate-norm-teleportation-alice
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qustate-norm (quantum-teleportation-alice alpha beta r1 r2))
		  1)))

(defthm qustate-normalize-teleportation-alice
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (qustate-normalize (quantum-teleportation-alice alpha beta r1 r2))
		  (quantum-teleportation-alice alpha beta r1 r2))))

(defun extract-possible-states (qstate)
  (if (endp qstate)
      nil
    (if (equal (caar qstate) 0)
	(extract-possible-states (cdr qstate))
      (cons (car qstate)
	    (extract-possible-states (cdr qstate))))))

(defun extract-qubit (qstate n)
  (if (endp qstate)
      nil
    (cons (nth n (cdar qstate))
	  (extract-qubit (cdr qstate) n))))

(defun all-dups (l)
  (if (or (endp l)
	  (endp (cdr l)))
      t
    (and (equal (car l) (cadr l))
	 (all-dups (cdr l)))))

(defun get-deterministic-qubit (qstate n)
  (let ((bits (extract-qubit (extract-possible-states qstate) n)))
    (if (all-dups bits)
	(car bits)
      'error)))

(defthm quantum-teleportation-alice-value-case-1a
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		(< r1 1/2)
		(< r2 1/2))
	   (equal (get-deterministic-qubit (quantum-teleportation-alice alpha beta r1 r2) 0)
		  nil))
  :hints (("Goal"
	   :in-theory (disable ;qustate-normalize-amplitudes
			       ;quantum-teleportation-alice-value
			       )))
  )

(defthm quantum-teleportation-alice-value-case-1b
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		(< r1 1/2)
		(< r2 1/2))
	   (equal (get-deterministic-qubit (quantum-teleportation-alice alpha beta r1 r2) 0)
		  nil))
  :hints (("Goal"
	   :in-theory (disable ;qustate-normalize-amplitudes
			       ;quantum-teleportation-alice-value
			       )))
  )

(defthm quantum-teleportation-alice-value-case-2a
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		(< r1 1/2)
		(not (< r2 1/2)))
	   (equal (get-deterministic-qubit (quantum-teleportation-alice alpha beta r1 r2) 0)
		  nil))
  :hints (("Goal"
	   :in-theory (disable ;qustate-normalize-amplitudes
			       ;quantum-teleportation-alice-value
			       )))
  )

(defthm quantum-teleportation-alice-value-case-2b
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		(< r1 1/2)
		(not (< r2 1/2)))
	   (equal (get-deterministic-qubit (quantum-teleportation-alice alpha beta r1 r2) 1)
		  t))
  :hints (("Goal"
	   :in-theory (disable ;qustate-normalize-amplitudes
			       ;quantum-teleportation-alice-value
			       )))
  )

(defthm quantum-teleportation-alice-value-case-3a
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		(not (< r1 1/2))
		(< r2 1/2))
	   (equal (get-deterministic-qubit (quantum-teleportation-alice alpha beta r1 r2) 0)
		  t))
  :hints (("Goal"
	   :in-theory (disable ;qustate-normalize-amplitudes
			       ;quantum-teleportation-alice-value
			       )))
  )

(defthm quantum-teleportation-alice-value-case-3b
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		(not (< r1 1/2))
		(< r2 1/2))
	   (equal (get-deterministic-qubit (quantum-teleportation-alice alpha beta r1 r2) 1)
		  nil))
  :hints (("Goal"
	   :in-theory (disable ;qustate-normalize-amplitudes
			       ;quantum-teleportation-alice-value
			       )))
  )

(defthm quantum-teleportation-alice-value-case-4a
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		(not (< r1 1/2))
		(not (< r2 1/2)))
	   (equal (get-deterministic-qubit (quantum-teleportation-alice alpha beta r1 r2) 0)
		  t))
  :hints (("Goal"
	   :in-theory (disable ;qustate-normalize-amplitudes
			       ;quantum-teleportation-alice-value
			       )))
  )

(defthm quantum-teleportation-alice-value-case-4b
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1)
		(not (< r1 1/2))
		(not (< r2 1/2)))
	   (equal (get-deterministic-qubit (quantum-teleportation-alice alpha beta r1 r2) 1)
		  t))
  :hints (("Goal"
	   :in-theory (disable ;qustate-normalize-amplitudes
			       ;quantum-teleportation-alice-value
			       )))
  )

(defun quantum-teleportation-bob (qstate q1 q2)
  (cond ((and (not q1) (not q2))
	 qstate)
	((and (not q1) q2)
	 (qstate-circuit '( (X 2) ) qstate nil))
	((and q1 (not q2))
	 (qstate-circuit '( (Z 2) ) qstate nil))
	((and q1 q2)
	 (qstate-circuit '( (X 2) (Z 2) ) qstate nil))
	))

(defun quantum-teleportation-protocol (alpha beta r1 r2)
  (let* ((qstate (quantum-teleportation-alice alpha beta r1 r2))
	 (q1 (get-deterministic-qubit qstate 0))
	 (q2 (get-deterministic-qubit qstate 1)))
    (quantum-teleportation-bob qstate q1 q2)))




(defthm quantum-teleportation-protocol-works-lemma
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (quantum-teleportation-protocol alpha beta r1 r2)
		  (if (< r1 1/2)
		      (if (< r2 1/2)
			  (list (list alpha NIL NIL NIL)
				(list beta  NIL NIL T  )
				(list 0     NIL T   NIL)
				(list 0     NIL T   T  )
				(list 0     T   NIL NIL)
				(list 0 	T   NIL T  )
				(list 0     T   T   NIL)
				(list 0     T   T   T  ))
			(list (list 0     NIL NIL NIL)
			      (list 0     NIL NIL T  )
			      (list alpha NIL T   NIL)
			      (list beta  NIL T   T  )
			      (list 0     T   NIL NIL)
			      (list 0     T   NIL T  )
			      (list 0     T   T   NIL)
			      (list 0     T   T   T  )))
		    (if (< r2 1/2)
			(list (list 0        NIL NIL NIL)
			      (list 0        NIL NIL T  )
			      (list 0        NIL T   NIL)
			      (list 0        NIL T   T  )
			      (list alpha    T   NIL NIL)
			      (list beta     T   NIL T  )
			      (list 0        T   T   NIL)
			      (list 0        T   T   T  ))
		      (list (list 0 	 NIL NIL NIL)
			    (list 0 	 NIL NIL T  )
			    (list 0        NIL T   NIL)
			    (list 0        NIL T   T  )
			    (list 0 	 T   NIL NIL)
			    (list 0 	 T   NIL T  )
			    (list alpha     T   T   NIL)
			    (list beta     T   T   T  ))))))
  )


(defun narrow-to-qubit-helper (qstate n)
  (if (endp qstate)
      nil
    (if (equal (caar qstate) 0)
	(narrow-to-qubit-helper (cdr qstate) n)
      (cons (list (caar qstate)
		  (nth n (cdar qstate)))
	    (narrow-to-qubit-helper (cdr qstate) n)))))

(defun narrow-to-qubit (qstate n)
  (qustate-normalize (narrow-to-qubit-helper qstate n)))

(defthm quantum-teleportation-protocol-works
  (implies (and (acl2-numberp alpha)
		(acl2-numberp beta)
		(equal (+ (* alpha (conjugate alpha))
			  (* beta  (conjugate beta)))
		       1))
	   (equal (narrow-to-qubit (quantum-teleportation-protocol alpha beta r1 r2) 2)
		  (make-qubit alpha beta)))
  :hints (("Goal"
	   :in-theory (disable quantum-teleportation-protocol)))
  )

