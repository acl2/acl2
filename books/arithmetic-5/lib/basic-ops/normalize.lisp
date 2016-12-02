; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; normalize.lisp
;;;
;;; There are two classes of rules in this book:
;;;
;;; 1. Specialized:
;;;    normalize-terms-such-as-a/a+b-+-b/a+b
;;;    normalize-terms-such-as-1/ax+bx
;;;    These are a couple of fairly messy bind-free rules.
;;;
;;;    normalize-terms-such-as-a/a+b-+-b/a+b
;;;
;;;      assuming a and b are acl2-numberp
;;;      (+ (* a (/ (+ a b))) (* b (/ (+ a b)))) ==> (if (equal (+ a b) 0) 0 1)
;;;      (+ (* a (/ (+ a b))) c (* b (/ (+ a b)))) ==> (if (equal (+ a b) 0) c (+ c 1))
;;;
;;;      We are, in affect, undoing distributivity in certain cases.
;;;
;;;    normalize-terms-such-as-1/ax+bx
;;;
;;;      assuming a, b, and x are acl2-numberp
;;;      (/ (+ x (* b x))) ==> (* (/ x) (/ (+ 1 b)))
;;;      (/ (+ (* a x) (* b x))) ==> (* (/ (+ a b)) (/ x))
;;;
;;;      We are, in affect, undoing distributivity when the term is under
;;;      a division.
;;;
;;; 2. Normal:
;;;    Concerned with finding ``like'' pieces of sums or products
;;;    and combining the found pieces in order to normalize the
;;;    sum or product.
;;;
;;;    See common.lisp for a short description of the general strategy
;;;    used in these rules.
;;;
;;;    We assume in the examples below, that everything is know to be an
;;;    acl2-number.
;;;
;;;    A simple examples of gathering like terms:
;;;    (+ a b (* 3 a)) ===> (+ b (* 4 a))
;;;
;;;    For normalizing products there are two distinct behaviours.
;;;
;;;    Under the default theory, gather-exponents, exponents
;;;    consisting of sums are gathered together, e.g.,
;;;    (* (expt x m) (expt x n)) ===> (expt x (+ m n)).
;;;    (* a b (expt a n)) ===> (* b (expt a (+ n 1)))
;;;
;;;    Under the other theory, scatter-exponents, exponents
;;;    consisting of sums are broken apart or scattered, e.g.,
;;;    (expt x (+ m n)) ===> (* (expt x m) (expt x n)).
;;;    (* a b (expt a n)) no change
;;;
;;;    Under both theories:
;;;    (* a b b) ===> (* a (expt b 2))
;;;    (* b (expt a (* 2 n)) (expt a n)) ===> (* b (expt a (* 3 n)))
;;;
;;;    These two theories are defined in top, using rules from this
;;;    book and elsewhere.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "common")

(local
 (include-book "basic"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory (enable collect-+)))

(local
 (in-theory (enable collect-*)))

(set-state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; normalize-terms-such-as-a/a+b-+-b/a+b

#|

;;; I can now do the first two, but not the third or fourth.  Is
;;; there no end to this madness?

(thm
(IMPLIES (AND (NOT (EQUAL N 0))
              (INTEGERP N)
              (<= 0 N))
         (EQUAL 1 (+ (/ (+ 1 N)) (* N (/ (+ 1 N)))))))

(thm
(IMPLIES (AND (NOT (EQUAL N 0))
              (INTEGERP N)
              (<= 0 N)
	      (acl2-numberp c))
         (EQUAL c (+ (* 2 c (/ (+ 2 N))) (* c N (/ (+ 2 N)))))))

(thm
(IMPLIES (AND (NOT (EQUAL N 0))
              (INTEGERP N)
              (<= 0 N)
	      (acl2-numberp c))
         (EQUAL 2 (+ (* 4 (/ (+ 2 N))) (* 2 N (/ (+ 2 N)))))))

(thm
 (IMPLIES (AND (INTEGERP N) (< 0 N))
         (EQUAL (+ (/ (+ 1 N)) (/ (+ N (EXPT N 2))))
                (/ N))))
|#

;;; assuming a and b are acl2-numberp
;;; (+ (* a (/ (+ a b))) (* b (/ (+ a b)))) ==> (if (equal (+ a b) 0) 0 1)
;;; (+ (* a (/ (+ a b))) c (* b (/ (+ a b)))) ==> (if (equal (+ a b) 0) c (+ c 1))

;;; We are, in affect, undoing distributivity in certain cases.

(defun factors-other-than-denominator (addend denominator)
  (declare (xargs :guard t))

  ;; Addend is, at least initially, a product.  We return a list of
  ;; all of addend's factors except denominator.

  (cond ((and (true-listp addend)
	      (eq (ffn-symb addend) 'BINARY-*))
	 (if (and (and (true-listp (arg1 addend))
		       (eq (ffn-symb (arg1 addend)) 'UNARY-/))
		  (equal (arg1 (arg1 addend)) denominator))
	     (factors (arg2 addend))
	   (cons (arg1 addend)
		 (factors-other-than-denominator (arg2 addend) denominator))))
	((and (true-listp addend)
	      (eq (ffn-symb addend) 'UNARY-/)
	      (equal (arg1 addend) denominator))
	 nil)
	(t
	 (list addend))))

(defun number-of-addends (sum)
  (declare (xargs :guard t))
  (if (and (true-listp sum)
	   (eq (fn-symb sum) 'BINARY-+))
      (+ 1 (number-of-addends (fargn sum 2)))
    1))

(defun find-denominators-with-sums (addend denominator-list
                                    number-of-addends-in-sum)
  (declare (xargs :guard (integerp number-of-addends-in-sum)))

  ;; To a first approximation, we return a list of all those factors
  ;; of addend which are of the form (/ (+ ..)).  In reality, we
  ;; return a list of the (+ ...)s.  Number-of-addends-in-sum is an
  ;; optimization.  Since this function is in support of
  ;; normalize-terms-such-as-a/a+b-+-b/a+b, we don't bother to return
  ;; those numerators which are ``too long.'' Consider the term
  ;; (+ (* a (/ (+ a b c)) (/ (+ a b))) (* b (/ (+ a b c)) (/ (+ a b)))).
  ;; When this function is called, number-of-addends-in-sum will be 2,
  ;; and we return ((+ a b)).  We do not include (+ a b c) because
  ;; it contains three addends in the sum, and we would not be able
  ;; to find instances of all three among the two addends of the
  ;; original term.

  (cond ((or (variablep addend)
             (fquotep addend))
         denominator-list)
        ((and (true-listp addend)
	      (eq (ffn-symb addend) 'BINARY-*))
         (if (and (true-listp (arg1 addend))
		  (eq (fn-symb (arg1 addend)) 'UNARY-/)
                  (true-listp (arg1 (arg1 addend)))
                  (eq (fn-symb (arg1 (arg1 addend))) 'BINARY-+)
                  (<= (number-of-addends (arg1 (arg1 addend)))
                      number-of-addends-in-sum))
             (find-denominators-with-sums (arg2 addend)
                                          (cons (arg1 (arg1 addend))
                                                denominator-list)
                                          number-of-addends-in-sum)
           (find-denominators-with-sums (arg2 addend)
                                        denominator-list
                                        number-of-addends-in-sum)))
        ((and (true-listp addend)
	      (eq (fn-symb addend) 'UNARY-/)
              (true-listp (arg1 addend))
	      (eq (fn-symb (arg1 addend)) 'BINARY-+)
              (<= (number-of-addends (arg1 addend))
                  number-of-addends-in-sum))
         (cons (arg1 addend) denominator-list))
        (t
         denominator-list)))

(local
 (defthm find-denominators-with-sums-thm
   (implies (true-list-listp denominator-list)
	    (true-list-listp (find-denominators-with-sums addend denominator-list n)))))

(defun remainder-aaa (sum factors to-be-found remainder)

  ;; Modified by Jared 2015-04-30 to add true-listp guard, due to
  ;; set-equal changes.
  (declare (xargs :guard (true-listp factors)))

  ;; Consider that the term
  ;; (+ (* a x (/ (+ a b))) (* b x (/ (+ a b))) c),
  ;; where c is really some big hairy term, has been seen by
  ;; normalize-terms-such-as-a/a+b-+-b/a+b.  When we get here, sum is
  ;; (+ (* b x (/ (+ a b))) c), factors is ((/ (+ a b)) x),
  ;; to-be-found is (b), and remainder is nil.  In this example, we
  ;; compare (b (/ (+ a b)) x) --- from to-be-found and factors ---
  ;; with (b (/ (+ a b)) x) --- the factors in the first addend of
  ;; sum.  Since they match we step both.  If they didn't we would
  ;; step only sum and accumulate the addend onto remainder.  The next
  ;; iteration we are done, and return c.  Note that, just as for
  ;; normalize-terms-such-as-a/a+b-+-b/a+b-fn-2, we are relying on the
  ;; sorting of things into term-order.

  (cond ((atom to-be-found)
	 (cond ((and remainder sum)
		(list 'BINARY-+ remainder sum))
	       (remainder
		remainder)
	       (sum
		sum)
	       (t
		''0)))
        ((null sum)
         nil)
	((and (true-listp sum)
	      (eq (fn-symb sum) 'BINARY-+))
	 (if (set-equal (factors (arg1 sum))
			(cons (car to-be-found) factors))
	     (remainder-aaa (arg2 sum)
			    factors
			    (cdr to-be-found)
			    remainder)
	   (remainder-aaa (arg2 sum)
			  factors
			  to-be-found
			  (if (null remainder)
                              (arg1 sum)
                            (list 'BINARY-+ (arg1 sum) remainder)))))
	((null (cdr to-be-found))
	 (if (set-equal (factors sum)
			(cons (car to-be-found) factors))
	     (if remainder
                 remainder
               ''0)
	   nil))
	(t
	 nil)))

(defun normalize-terms-such-as-a/a+b-+-b/a+b-fn-2 (denominator addend rest)
  (declare (xargs :guard (true-listp denominator)))

  ;; Denominator is a denominator as found by
  ;; find-denominators-with-sums.  Addend and sum are the x and y of
  ;; normalize-terms-such-as-a/a+b-+-b/a+b respectively.  Consider the
  ;; that the term (+ (* a x (/ (+ a b))) (* b x (/ (+ a b))) c),
  ;; where c is really some big hairy term, has been seen by
  ;; normalize-terms-such-as-a/a+b-+-b/a+b.  Upon entry, denominator
  ;; will be (+ a b), addend will be (* a x (/ (+ a b))), and rest
  ;; will be (+ (* b x (/ (+ a b))) c).

  ;; Before proceeding, we make one important observation.  Due to the
  ;; fact that ACL2 sorts the addends of both denominator and the
  ;; original term into term-order, the addends of denominator and the
  ;; addends of the original term are lined up with eachother in the
  ;; sense that the a and the b appear in the same order in both.
  ;; This allows us to carry out our search in a much more efficient
  ;; manner, marching down both denominator and addend + sum in
  ;; lock-step.

  ;; We now return to our discussion of this function.  Factors1 and
  ;; factors2 will be bound to (* a x) and a respectively.  Factors
  ;; will then be bound to (x).  X is the ``extra'' piece left over
  ;; after removing a from the numerator of addend.  We now want to
  ;; find a similar match for b in rest.  This is done by
  ;; remainder-aaa, which returns c as the remainder.

  ;; See normalize-terms-such-as-a/a+b-+-b/a+b for a discussion of why
  ;; we return the binding we do.

  ;; The first branch of the cond below is a special case for things
  ;; like:
#|
(thm
(IMPLIES (AND (NOT (EQUAL N 0))
              (INTEGERP N)
              (<= 0 N))
         (EQUAL 1 (+ (/ (+ 1 N)) (* N (/ (+ 1 N)))))))

(thm
(IMPLIES (AND (NOT (EQUAL N 0))
              (INTEGERP N)
              (<= 0 N)
	      (acl2-numberp c))
         (EQUAL c (+ (* c (/ (+ 1 N))) (* c N (/ (+ 1 N)))))))
|#

  (let ((factors1 (factors-other-than-denominator addend denominator))
        (factors2 (factors (arg1 denominator))))
    (cond ((equal factors2 '('1))
	   (let* ((factors factors1)
		  (remainder (remainder-aaa rest
					    (cons (list 'UNARY-/ denominator) factors)
					    (addends (arg2 denominator))
					    nil)))
	     (if remainder
		 (list (cons 'factor (make-product factors))
		       (cons 'denominator denominator)
		       (cons 'remainder remainder)
		       (cons 'a (fargn denominator 1)))
	       nil)))
	  ((intersectp-equal factors1 factors2)
	   (let* ((factors (set-difference-equal factors1 factors2))
		  (remainder (remainder-aaa rest
					    (cons (list 'UNARY-/ denominator) factors)
					    (addends (arg2 denominator))
					    nil)))
	     (if remainder
		 (list (cons 'factor (make-product factors))
		       (cons 'denominator denominator)
		       (cons 'remainder remainder)
		       (cons 'a (fargn denominator 1)))
	       nil)))
	  (t
	   nil))))

(defun normalize-terms-such-as-a/a+b-+-b/a+b-fn-1 (denominator-list addend rest)
  (declare (xargs :guard (and (true-list-listp denominator-list))))
  (if (endp denominator-list)
      nil
    (let ((binding-alist
           (normalize-terms-such-as-a/a+b-+-b/a+b-fn-2 (car denominator-list)
                                                       addend rest)))
      (if binding-alist
          binding-alist
        (normalize-terms-such-as-a/a+b-+-b/a+b-fn-1 (cdr denominator-list)
                                                    addend rest)))))

;;; We do not catch things such as
;;; (+ (* a x (/ (+ a (* b x)))) (* b (expt x 2) (/ (+ a (* b x)))))
;;; even though this is the same as
;;; (* x (+ (* a (/ (+ a (* b x)))) (* b x (/ (+ a (* b x))))))
;;; Writing the bind-free function which would find such (probably rare)
;;; patterns as this would be more work than I am willing to do right now.
;;; I leave this note in case I feel up to it later, or perhaps you are
;;; looking for a challange and would be willing to undertake the task
;;; and submit the result to the ACL2 maintainers.

;;; In the example:
;;;(thm
;;; (implies (and (acl2-numberp a)
;;;               (acl2-numberp b))
;;;          (equal (+ (* a (/ (+ a b))) (* b (/ (+ a b))))
;;;                 y))
;;; :otf-flg t)
;;;  normalize-terms-such-as-a/a+b-+-b/a+b-fn returns
;;;((FACTOR QUOTE 1)
;;; (DENOMINATOR BINARY-+ A B)
;;; (REMAINDER QUOTE 0)
;;; (A . A))

;;; Disable the associative and commutative rules for addition.
;;; In the example:
;;; (thm
;;;  (implies (and (acl2-numberp a)
;;;                (acl2-numberp b)
;;;                (acl2-numberp c)
;;;                (acl2-numberp x))
;;;           (equal (+ (* x a (/ (+ a b))) c (* x b (/ (+ a b))))
;;;                  y))
;;;  :otf-flg t)
;;;  normalize-terms-such-as-a/a+b-+-b/a+b-fn returns
;;;((FACTOR . X)
;;; (DENOMINATOR BINARY-+ A B)
;;; (REMAINDER . C)
;;; (A . A))

;;; Disable the associative and commutative rules for addition.
;;; In the example:
;;; (thm
;;;  (implies (and (acl2-numberp a)
;;;                (acl2-numberp b)
;;;                (acl2-numberp c)
;;;                (acl2-numberp x))
;;;           (equal (+ (* x a (/ (+ a b c)))
;;;                     (* x b (/ (+ a b c)))
;;;                     (* x c (/ (+ a b c))))
;;;                  y))
;;;  :otf-flg t)
;;;  normalize-terms-such-as-a/a+b-+-b/a+b-fn returns
;;;((FACTOR . X)
;;; (DENOMINATOR BINARY-+ A B)
;;; (REMAINDER . C)
;;; (A . A))

(defun normalize-terms-such-as-a/a+b-+-b/a+b-fn (x y)
  (declare (xargs :guard t))
      (normalize-terms-such-as-a/a+b-+-b/a+b-fn-1
       (find-denominators-with-sums x
                                    nil
                                    (+ 1 (number-of-addends y)))
       x
       y))

;;; I use distribute-* in the fifth hypothesis of
;;; normalize-terms-such-as-a/a+b-+-b/a+b:
;;;   (equal y
;;;          (+ (* factor (distribute-* (+ denominator (- a))
;;;                                        (/ denominator)))
;;;             remainder)))
;;; in order ot ensure that the two subterms denominator and
;;; (/ denominator) do not cancel each other off, causing the
;;; hypothesis to not be relieved.  The rule
;;; distribute-*-distributes-2 ensures that distribution occurs
;;; as expected, and the rule distribute-*-distributes-1 replaces
;;; distribute-* with * after this occurs.  I thereby prevent the
;;; rule |(* a (/ a))| in basic.lisp from gettingin the way.

(defun distribute-* (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (* x y))

(defthm distribute-*-distributes-1
  (equal (distribute-* x y)
	 (* x y)))

(defthm distribute-*-distributes-2
   (equal (distribute-* (+ x y) z)
	  (+ (* x z) (distribute-* y z))))

(in-theory (disable distribute-*))

;;; assuming a, b, and c are acl2-numberp
;;; (+ (* a (/ (+ a b))) c (* b (/ (+ a b)))) ==> (if (equal (+ a b) 0) c (+ c 1))

(encapsulate
 ()

 (local
  (include-book "../../support/top"))

 ;; We compare the equalities with x and y seperately in order to
 ;; avoid looping.  The seemingly ``extra'' variable a allows us to do
 ;; this.

 (defthm normalize-terms-such-as-a/a+b-+-b/a+b
     (implies (and (bind-free
                    (normalize-terms-such-as-a/a+b-+-b/a+b-fn x y)
                    (factor denominator remainder a))
                   (acl2-numberp remainder)
                   (acl2-numberp denominator)
                   (equal x (* factor a (/ denominator)))
                   (equal y
                          (+ (* factor (distribute-* (+ denominator (- a))
                                                     (/ denominator)))
                             remainder)))
              (equal (+ x y)
                     (if (equal denominator 0)
                         remainder
                       (+ factor remainder)))))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; normalize-terms-such-as-1/ax+bx

;;; assuming a, b, and x are acl2-numberp
;;; (/ (+ x (* b x))) ==> (* (/ x) (/ (+ 1 b)))
;;; (/ (+ (* a x) (* b x))) ==> (* (/ (+ a b)) (/ x))

;;; We are, in affect, undoing distributivity when the term is under
;;; a division.

;;; In the example
;;; (thm
;;;  (implies (and (acl2-numberp a)
;;;                (acl2-numberp b)
;;;                (acl2-numberp x))
;;;           (equal (/ (+ (* a x) (* b x)))
;;;                  y))
;;;  :otf-flg t)
;;; normalize-terms-such-as-1/ax+bx-fn returns
;;; ((COMMON . X)
;;;  (REMAINDER BINARY-+ A B))

(defun normalize-terms-such-as-1/ax+bx-fn (sum)
  (declare (xargs :guard t))

  ;; We look for any factors common to each addend of sum.  If we
  ;; find any, we return a binding list with common bound to the
  ;; product of these factors, and remainder bound to the original
  ;; sum but with the common factors removed from each addend.

  (if (and (true-listp sum)
	   (eq (ffn-symb sum) 'BINARY-+))
      (let ((common-factors (common-factors (factors (arg1 sum))
                                            (arg2 sum))))
        (if common-factors
            (let ((common (make-product common-factors))
                  (remainder (remainder common-factors sum)))
              (list (cons 'common common)
                    (cons 'remainder remainder)))
          nil))
    nil))

;;; assuming a, b, and x are acl2-numberp
;;; (/ (+ x (* b x))) ==> (* (/ x) (/ (+ 1 b)))
;;; (/ (+ (* a x) (* b x))) ==> (* (/ (+ a b)) (/ x))

(defthm normalize-terms-such-as-1/ax+bx
    (implies (and (bind-free
                   (normalize-terms-such-as-1/ax+bx-fn sum)
                   (common remainder))
                  (equal sum
                         (* common remainder)))
             (equal (/ sum)
                    (* (/ common) (/ remainder)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Normalize sums

(local
 (in-theory (disable matching-addend-p)))

(defun find-matching-addend (to-match x mfc state)
  (declare (xargs :guard t))
  (cond ((and (true-listp x)
	      (eq (fn-symb x) 'BINARY-+))
         (cond ((and (matching-addend-p to-match (arg1 x))
		     ;; prevent various odd loops
		     (stable-under-rewriting-sums (arg1 x) mfc state))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-+)
                (find-matching-addend to-match (arg2 x)
				      mfc state))
               ((and (matching-addend-p to-match (arg2 x))
		     (stable-under-rewriting-sums (arg2 x) mfc state))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((and (matching-addend-p to-match x)
	      (stable-under-rewriting-sums x mfc state))
         (list (cons 'match x)))
        (t
         nil)))

;;; Note that since we rewrite from the inside out, we only have to
;;; check whether x matches some addend of y.

(defthm normalize-addends
    (implies (and (syntaxp (in-term-order-+ y mfc state))
                  (bind-free
		   (find-matching-addend (addend-pattern x) y
					 mfc state)
		   (match)))
             (equal (+ x y)
                    (+ (bubble-down x match) y))))

(theory-invariant
 (if (active-runep '(:definition arith-5-active-flag))
     (or (not (active-runep '(:rewrite normalize-addends)))
         (and (active-runep '(:rewrite bubble-down-+-bubble-down))
              (active-runep '(:rewrite bubble-down-+-match-1))
              (active-runep '(:rewrite bubble-down-+-match-2))
              (not (active-runep '(:rewrite bubble-down)))
              (not (active-runep '(:executable-counterpart bubble-down)))))
   t)
 :error nil)

(local
 (in-theory (disable normalize-addends)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Normalize products, gathering exponents

(local
 (in-theory (disable matching-factor-gather-exponents-p)))

(defun find-matching-factor-gather-exponents (to-match x mfc state)
  (declare (xargs :guard t))
  (cond ((eq (fn-symb x) 'BINARY-*)
         (cond ((and (matching-factor-gather-exponents-p to-match (arg1 x))
		     ;; prevent various odd loops
		     (stable-under-rewriting-products (arg1 x) mfc state))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-*)
                (find-matching-factor-gather-exponents to-match (arg2 x)
						       mfc state))
               ((and (matching-factor-gather-exponents-p to-match (arg2 x))
		     (stable-under-rewriting-products (arg2 x) mfc state))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((and (matching-factor-gather-exponents-p to-match x)
	      (stable-under-rewriting-products x mfc state))
         (list (cons 'match x)))
        (t
         nil)))

(defthm normalize-factors-gather-exponents
    (implies (and (syntaxp (in-term-order-* y mfc state))
                  (bind-free
		   (find-matching-factor-gather-exponents
		    (factor-pattern-gather-exponents x) y mfc state)
		   (match)))
             (equal (* x y)
                    (* (bubble-down x match) y))))

(theory-invariant
 (if (active-runep '(:definition arith-5-active-flag))
     (or (not (active-runep '(:rewrite normalize-factors-gather-exponents)))
         (and (active-runep '(:rewrite bubble-down-*-bubble-down))
              (active-runep '(:rewrite bubble-down-*-match-1))
              (active-runep '(:rewrite bubble-down-*-match-2))
              (not (active-runep '(:rewrite bubble-down)))
              (not (active-runep '(:executable-counterpart bubble-down)))))
   t)
 :error nil)

(local
 (in-theory (disable normalize-factors-gather-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Normalize products, scattering exponents

(local
 (in-theory (disable matching-factor-scatter-exponents-p)))

(defun find-matching-factor-scatter-exponents (to-match x mfc state)
  (declare (xargs :guard t))
  (cond ((eq (fn-symb x) 'BINARY-*)
         (cond ((and (matching-factor-scatter-exponents-p to-match (arg1 x))
		     ;; Prevent various odd loops.
		     (stable-under-rewriting-sums (arg1 x) mfc state))
                (list (cons 'match (arg1 x))))
               ((eq (fn-symb (arg2 x)) 'BINARY-*)
                (find-matching-factor-scatter-exponents to-match (arg2 x)
							mfc state))
               ((and (matching-factor-scatter-exponents-p to-match (arg2 x))
		     (stable-under-rewriting-sums (arg2 x) mfc state))
                (list (cons 'match (arg2 x))))
               (t
                nil)))
        ((and (matching-factor-scatter-exponents-p to-match x)
	      (stable-under-rewriting-sums x mfc state))
         (list (cons 'match x)))
        (t
         nil)))

(defthm normalize-factors-scatter-exponents
    (implies (and (syntaxp (in-term-order-* y mfc state))
                  (bind-free
		   (find-matching-factor-scatter-exponents
		    (factor-pattern-scatter-exponents x) y mfc state)
		   (match)))
             (equal (* x y)
                    (* (bubble-down x match) y))))

(theory-invariant
 (if (active-runep '(:definition arith-5-active-flag))
     (or (not (active-runep '(:rewrite normalize-scatter-exponents)))
         (and (active-runep '(:rewrite bubble-down-*-bubble-down))
              (active-runep '(:rewrite bubble-down-*-match-1))
              (active-runep '(:rewrite bubble-down-*-match-2))
              (not (active-runep '(:rewrite bubble-down)))
              (not (active-runep '(:executable-counterpart bubble-down)))))
   t)
 :error nil)

(local
 (in-theory (disable normalize-factors-scatter-exponents)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(theory-invariant
 (if (active-runep '(:definition arith-5-active-flag))
     (not (and (active-runep '(:rewrite normalize-factors-gather-exponents))
               (active-runep '(:rewrite normalize-factors-scatter-exponents))))
   t)
 :error nil)
