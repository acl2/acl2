; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; simplify.lisp
;;;
;;;
;;; This book contains three types of rules:
;;; 1. simplify-terms-such-as-ax+bx-rel-0
;;;
;;;    assuming a, b, and x are acl2-numberp
;;;    (equal (+ x (* b x)) 0) ==> (or (equal x 0) (equal (+ 1 b) 0))
;;;    (equal (+ (* a x) (* b x)) 0) ==> (or (equal x 0) (equal (+ a b) 0))
;;;
;;; 2. Cancel "like" terms on either side of an equality or inequality.
;;;
;;;    A couple of simple example of cancelling like terms:
;;;
;;;    (equal (+ a (* 2 c) d)
;;;           (+ b c d))
;;;    ===>
;;;    (equal (+ a c)
;;;           b)
;;;
;;;    Note that just as for normailze.liso, there are two distinct
;;;    behaviours for cancelling like factors:
;;;
;;;    Under the default theory, gather-exponents:
;;;
;;;    (equal (* a (expt b n))
;;;           (* c (expt b m)))
;;;    ===>
;;;    (equal (* a (expt b (- n m)))
;;;           c)
;;;
;;;    Under the other theory, scatter-exponents
;;;
;;;    (equal (* a (expt b n))
;;;           (* c (expt b m)))
;;;    ===>
;;;    no change
;;;
;;;    Under both theories:
;;;
;;;    (equal (* a (expt b (* 2 n)))
;;;           (* c (expt b n)))
;;;    ===>
;;;    (equal (* a (expt b n))
;;;           (* c))
;;;
;;;    (equal (* a (expt c 2) d)
;;;           (* b c d))
;;;    ===>
;;;    (equal (* a c)
;;;           b)
;;;
;;; 3. Move "negative" terms form one side of an equality or
;;;    inequality to the other.
;;;
;;;    A couple of simple example of moving a negative term to the
;;;    other side:
;;;
;;;    (< (+ a (- b) c)
;;;       (+ d e))
;;;    ===>
;;;    (< (+ a c)
;;;       (+ b d e))
;;;
;;;    Under the default theory, gather-exponents, we do not move
;;;    ``negative'' exponents to the other side.  It has proved too
;;;    dificult to prevent loops in the general case, and so we avoid
;;;    the issue entirely.  We could certainly catch the ``simple''
;;;    cases, but have not done so.
;;;
;;;    Under the other theory, scatter-exponents:
;;;
;;;    (equal (* a (/ b) c)
;;;           (* d e))
;;;    ===>
;;;    (equal (* a c)
;;;           (* b d e))
;;;
;;;    (equal (* a (expt b (- n)) c)
;;;           (* d (expt b m)))
;;;    ===>
;;;    (equal (* a c)
;;;           (* d (expt b m) (expt b n)))
;;;
;;;    Note that for multiplication, division or exponentiation to a negative
;;;    power is considered to be negative.
;;;
;;; See common.lisp for a short description of the general strategy
;;; used in the last two of these types.
;;;
;;; The certification of this book could probably be sped up a good
;;; bit.  It is rather slow.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "common")

(local
 (include-book "simplify-helper"))

(local
 (include-book "basic"))

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm rewrite-equal-<-to-iff-<
     (equal (equal (< a b)
                   (< c d))
            (iff (< a b)
                 (< c d)))))

(local
 (encapsulate
  ()

  (local (include-book "../../support/top"))

  (defthm equal-*-/-1
      (equal (equal (* (/ x) y) z)
             (if (equal (fix x) 0)
                 (equal z 0)
               (and (acl2-numberp z)
                    (equal (fix y) (* x z))))))

  (defthm equal-*-/-2
      (equal (equal (* y (/ x)) z)
             (if (equal (fix x) 0)
                 (equal z 0)
               (and (acl2-numberp z)
                    (equal (fix y) (* z x))))))

  ))

(local
 (encapsulate
  ()

  (local (include-book "../../support/top"))

  (defthm equal-*-1
    (implies (not (equal (fix x) 0))
      (equal (equal (* x y) (* x z))
	     (equal (fix y) (fix z)))))

  (defthm equal-*-2
    (implies (not (equal (fix x) 0))
      (equal (equal (* y x) (* z x))
	     (equal (fix y) (fix z)))))

  ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; simplify-terms-such-as-ax+bx-rel-0

;;; assuming a, b, and x are acl2-numberp
;;; (equal (+ x (* b x)) 0) ==> (or (equal x 0) (equal (+ 1 b) 0))
;;; (equal (+ (* a x) (* b x)) 0) ==> (or (equal x 0) (equal (+ a b) 0))

;;; We are, in affect, undoing distributivity when the term is being
;;; compared to zero.

;;; In the example
;;; (thm
;;;  (implies (and (acl2-numberp a)
;;;                (acl2-numberp b)
;;;                (acl2-numberp x))
;;;           (equal (+ (* a x) (* b x))
;;;                  0))
;;;  :otf-flg t)
;;; simplify-terms-such-as-ax+bx-rel-0-fn returns
;;; ((COMMON . X)
;;;  (REMAINDER BINARY-+ A B))

(defun simplify-terms-such-as-ax+bx-rel-0-fn (sum)
  (declare (xargs :guard t))

  ;; We look for any factors common to each addend of sum.  If we
  ;; find any, we return a binding list with common bound to the
  ;; product of these factors, and remainder bound to the original
  ;; sum but with the common factors removed from each addend.

  (if (eq (fn-symb sum) 'BINARY-+)
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
;;; (equal (+ x (* b x)) 0) ==> (or (equal x 0) (equal (+ 1 b) 0))
;;; (equal (+ (* a x) (* b x)) 0) ==> (or (equal x 0) (equal (+ a b) 0))

(defthm simplify-terms-such-as-ax+bx-=-0
    (implies (and (bind-free
                   (simplify-terms-such-as-ax+bx-rel-0-fn sum)
                   (common remainder))
                  (acl2-numberp common)
                  (acl2-numberp remainder)
                  (equal sum
                         (* common remainder)))
             (equal (equal sum 0)
                    (or (equal common 0)
                        (equal remainder 0)))))

(defthm simplify-terms-such-as-ax+bx-<-0-rational-remainder
    (implies (and (bind-free
                   (simplify-terms-such-as-ax+bx-rel-0-fn sum)
                   (common remainder))
                  (acl2-numberp common)
                  (real/rationalp remainder)
                  (equal sum
                         (* common remainder)))
             (equal (< sum 0)
                    (cond ((< common 0)
                           (< 0 remainder))
                          ((< 0 common)
                           (< remainder 0))
                          (t
                           nil)))))

(defthm simplify-terms-such-as-ax+bx-<-0-rational-common
    (implies (and (bind-free
                   (simplify-terms-such-as-ax+bx-rel-0-fn sum)
                   (common remainder))
                  (real/rationalp common)
                  (acl2-numberp remainder)
                  (equal sum
                         (* common remainder)))
             (equal (< sum 0)
                    (cond ((< common 0)
                           (< 0 remainder))
                          ((< 0 common)
                           (< remainder 0))
                          (t
                           nil))))
    :hints (("Goal" :use (:instance simplify-terms-such-as-ax+bx-<-0-rational-remainder
				    (common remainder)
				    (remainder common)))))

(defthm simplify-terms-such-as-0-<-ax+bx-rational-remainder
    (implies (and (bind-free
                   (simplify-terms-such-as-ax+bx-rel-0-fn sum)
                   (common remainder))
                  (acl2-numberp common)
                  (real/rationalp remainder)
                  (equal sum
                         (* common remainder)))
             (equal (< 0 sum)
                    (cond ((< 0 common)
                           (< 0 remainder))
                          ((< common 0)
                           (< remainder 0))
                          (t
                           nil)))))

(defthm simplify-terms-such-as-0-<-ax+bx-rational-common
    (implies (and (bind-free
                   (simplify-terms-such-as-ax+bx-rel-0-fn sum)
                   (common remainder))
                  (real/rationalp common)
                  (acl2-numberp remainder)
                  (equal sum
                         (* common remainder)))
             (equal (< 0 sum)
                    (cond ((< 0 common)
                           (< 0 remainder))
                          ((< common 0)
                           (< remainder 0))
                          (t
                           nil))))
    :hints (("Goal" :use (:instance simplify-terms-such-as-0-<-ax+bx-rational-remainder
				    (common remainder)
				    (remainder common)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; simplify-sums-equal and simplify-sums-<

;;; We wish to cancel like addends from both sides of af an equality
;;; or inequality.  We scan the sums on either side of the relation,
;;; and construct a pair of addend-info-lists.  We then find the first
;;; match in these lists and cancel it.

(defun addend-val (addend)
  (declare (xargs :guard t))

  ;; We wish to subtract the ``smaller'' of two matching addends.
  ;;

  (cond ((variablep addend)
	 (list 0 1 0))
	((constant-p addend)
	 (let ((val (unquote addend)))
	   (if (rationalp val)		; OK, no constant reals
	       (list 0 0 (abs val))
	     (list 0 0 1))))
	((eq (ffn-symb addend) 'UNARY--)
	 (addend-val (arg1 addend)))
	((and (eq (ffn-symb addend) 'BINARY-*)
	      (constant-p (arg1 addend)))
	 (let ((val (unquote (arg1 addend))))
	   (if (rationalp val)
	       (list (abs val) 0 0)
	     (list 1 0 0))))
	(t
	 (list 0 1 0))))

(defun addend-info-entry (x)
  (declare (xargs :guard t))
  (list (addend-pattern x) (addend-val x) x))

(defun addend-info-list (x)
  (declare (xargs :guard t))
  (if (eq (fn-symb x) 'BINARY-+)
      (cons (addend-info-entry (arg1 x))
            (addend-info-list (arg2 x)))
    (list (addend-info-entry x))))

(local
 (encapsulate
  ()

  (local
   (defthm temp-1
     (good-val-triple-p (addend-val x))))

  (defthm addend-info-list-thm
    (info-list-p (addend-info-list x)))
  ))

(defun assoc-addend (x info-list)
  (declare (xargs :guard (info-list-p info-list)))
  (cond ((endp info-list)
         nil)
        ((matching-addend-patterns-p x (caar info-list))
         (car info-list))
        (t
         (assoc-addend x (cdr info-list)))))

(defun first-match-in-addend-info-lists (info-list1 info-list2 mfc state)
  (declare (xargs :guard (and (info-list-p info-list1)
                              (info-list-p info-list2))
		  :guard-hints (("Goal" :in-theory (disable good-val-triple-p
							    negate-match
							    val-<)))))
  (if (endp info-list1)
      nil
    (let ((temp (assoc-addend (car (car info-list1)) info-list2)))
      (if temp
	  (cond ((and ;; We want the ``smaller'' match
		      (val-< (cadr (car info-list1))
			     (cadr temp))
		      ;; prevent various odd loops
		      (stable-under-rewriting-sums (negate-match
						    (caddr (car info-list1)))
						   mfc state))
		 (list (cons 'x (negate-match (caddr (car info-list1))))))
		((stable-under-rewriting-sums (negate-match
					       (caddr temp))
					      mfc state)
		 (list (cons 'x (negate-match (caddr temp)))))
		(t
		 (first-match-in-addend-info-lists (cdr info-list1) info-list2
						   mfc state)))
        (first-match-in-addend-info-lists (cdr info-list1) info-list2
					  mfc state)))))

(defun find-matching-addends (lhs rhs mfc state)
  (declare (xargs :guard t
		  :verify-guards nil))
  (let* ((info-list1 (addend-info-list lhs))
         (info-list2 (if info-list1
			 (addend-info-list rhs)
		       nil)))
    (if info-list2
	(first-match-in-addend-info-lists info-list1 info-list2
					  mfc state)
      nil)))

 (verify-guards find-matching-addends)

(defthm simplify-sums-equal
    (implies (and (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
		  (syntaxp (in-term-order-+ lhs mfc state))
		  (syntaxp (in-term-order-+ rhs mfc state))
                  (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (bind-free
                   (find-matching-addends lhs rhs mfc state)
                   (x)))
             (equal (equal lhs rhs)
                    (equal (+ x lhs) (+ x rhs)))))

(local
 (in-theory (disable simplify-sums-equal)))

(defthm simplify-sums-<
    (implies (and (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (syntaxp (in-term-order-+ lhs mfc state))
		  (syntaxp (in-term-order-+ rhs mfc state))
                  (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (bind-free
                   (find-matching-addends lhs rhs mfc state)
                   (x)))
             (equal (< lhs rhs)
                    (< (+ x lhs) (+ x rhs)))))

(local
 (in-theory (disable simplify-sums-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun negative-addend-p (x)
  (declare (xargs :guard t))
  (or (and (eq (fn-symb x) 'UNARY--)
           (or (variablep (arg1 x))
              (not (equal (ffn-symb (arg1 x)) 'UNARY--))))
      (and (eq (fn-symb x) 'BINARY-*)
           (rational-constant-p (arg1 x))
           (< (unquote (arg1 x)) 0))))

(defun find-negative-addend1 (x mfc state)
  (declare (xargs :guard t))
  (cond ((not (eq (fn-symb x) 'BINARY-+))
         (if (and (negative-addend-p x)
		  ;; prevent various odd loops
		  (stable-under-rewriting-sums (negate-match x)
					       mfc state))
             (list (cons 'x (negate-match x)))
           nil))
        ((and (negative-addend-p (arg1 x))
	      (stable-under-rewriting-sums (negate-match (arg1 x))
					   mfc state))
         (list (cons 'x (negate-match (arg1 x)))))
        ((eq (fn-symb (arg2 x)) 'BINARY-+)
         (find-negative-addend1 (arg2 x) mfc state))
        ((and (negative-addend-p (arg2 x))
	      (stable-under-rewriting-sums (negate-match (arg2 x))
					   mfc state))
         (list (cons 'x (negate-match (arg2 x)))))
        (t
         nil)))

(defun find-negative-addend (lhs rhs mfc state)
  (declare (xargs :guard t))
  (let ((temp1 (find-negative-addend1 lhs mfc state)))
    (if temp1
        temp1
      (let ((temp2 (find-negative-addend1 rhs mfc state)))
        (if temp2
            temp2
          nil)))))

(defthm prefer-positive-addends-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (in-term-order-+ lhs mfc state))
		  (syntaxp (in-term-order-+ rhs mfc state))
                  (syntaxp (or (equal (fn-symb lhs) 'BINARY-+)
                               (equal (fn-symb rhs) 'BINARY-+)))
                  (bind-free
                   (find-negative-addend lhs rhs mfc state)
                   (x)))
             (equal (equal lhs rhs)
                    (equal (+ x lhs) (+ x rhs)))))

(local
 (in-theory (disable prefer-positive-addends-equal)))


(defthm prefer-positive-addends-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (in-term-order-+ lhs mfc state))
		  (syntaxp (in-term-order-+ rhs mfc state))
                  (syntaxp (or (equal (fn-symb lhs) 'BINARY-+)
                               (equal (fn-symb rhs) 'BINARY-+)))
                  (bind-free
                   (find-negative-addend lhs rhs mfc state)
                   (x)))
             (equal (< lhs rhs)
                    (< (+ x lhs) (+ x rhs)))))

(local
 (in-theory (disable prefer-positive-addends-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm simplify-products-gather-exponents-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (syntaxp (in-term-order-* lhs mfc state))
		  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free
                   (find-matching-factors-gather-exponents lhs rhs mfc state)
                   (x))
		  ;; Something is not right if x = +/-1.  This will
		  ;; presumably be rewritten away later.  We abort
		  ;; for now.
		  (syntaxp (not (equal x ''1)))
		  (syntaxp (not (equal x ''-1)))
                  (case-split (acl2-numberp x))
		  (case-split (not (equal x 0))))
             (equal (equal lhs rhs)
		    (equal (* x lhs) (* x rhs)))))

(local
 (in-theory (disable simplify-products-gather-exponents-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm simplify-products-gather-exponents-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (syntaxp (in-term-order-* lhs mfc state))
		  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free
                   (find-rational-matching-factors-gather-exponents lhs rhs
                                                                    mfc state)
                   (x))
		  ;; Something is not right if x = +/-1.  This will
		  ;; presumably be rewritten away later.  We abort
		  ;; for now.
		  (syntaxp (not (equal x ''1)))
		  (syntaxp (not (equal x ''-1)))
                  (case-split (real/rationalp x))
		  (case-split (not (equal x 0))))
             (equal (< lhs rhs)
                    (cond ((< 0 x)
                           (< (* x lhs) (* x rhs)))
                          (t
                           (< (* x rhs) (* x lhs)))))))

(local
 (in-theory (disable simplify-products-gather-exponents-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm simplify-products-scatter-exponents-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (syntaxp (in-term-order-* lhs mfc state))
		  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free
                   (find-matching-factors-scatter-exponents lhs rhs mfc state)
                   (x))
		  (syntaxp (not (equal x ''1)))
		  (syntaxp (not (equal x ''-1)))
                  (case-split (acl2-numberp x))
		  (case-split (not (equal x 0))))
             (equal (equal lhs rhs)
		    (equal (* x lhs) (* x rhs)))))

(local
 (in-theory (disable simplify-products-scatter-exponents-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm simplify-products-scatter-exponents-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (not (quotep lhs)))
                  (syntaxp (not (quotep rhs)))
                  (syntaxp (in-term-order-* lhs mfc state))
		  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free
                   (find-rational-matching-factors-scatter-exponents lhs rhs
                                                                    mfc state)
                   (x))
		  (syntaxp (not (equal x ''1)))
		  (syntaxp (not (equal x ''-1)))
                  (case-split (real/rationalp x))
		  (case-split (not (equal x 0))))
             (equal (< lhs rhs)
                    (cond ((< 0 x)
                           (< (* x lhs) (* x rhs)))
                          (t
                           (< (* x rhs) (* x lhs)))))))

(local
 (in-theory (disable simplify-products-scatter-exponents-<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
;;; We do not include theorems such as the below
;;; prefer-positive-exponents-gather-exponents-equal because it is too
;;; difficult to prevent looping.

;;; Add an example here!!!

(defthm prefer-positive-exponents-gather-exponents-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
                  (syntaxp (in-term-order-* lhs mfc state))
		  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free
                   (find-rational-negative-factor-gather-exponents lhs rhs
                                                                   mfc state)
                   (x))
                  (case-split (rationalp x))
		  (case-split (not (equal x 0))))
             (equal (equal lhs rhs)
		    (equal (* (/ x) lhs) (* (/ x) rhs)))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This should probably be refactored and cleaned up.  Do I have
;;; divisive-factor-p defined anywhere already?  Am I consistent in
;;; my notions?  Is it consistent with invert-match?

(defun find-divisive-factor-scatter-exponents2 (x mfc state)
  (declare (xargs :guard t))
  (cond ((or (variablep x)
             (fquotep x))
         nil)
	;; Is this correct?
        ((eq (ffn-symb x) 'UNARY--)
	 (find-divisive-factor-scatter-exponents2 (arg1 x) mfc state))
        ((eq (ffn-symb x) 'UNARY-/)
	 (if (stable-under-rewriting-products (invert-match x) mfc state)
	     (list (cons 'x (invert-match x)))
	   nil))
        ((eq (ffn-symb x) 'EXPT)
         (cond ((eq (fn-symb (arg1 x)) 'UNARY-/)
                (if (stable-under-rewriting-products (invert-match x) mfc state)
		    (list (cons 'x (invert-match x)))
		  nil))
               ((and (quotep (arg1 x))
		     (consp (cdr (arg1 x)))
                     (not (integerp (cadr (arg1 x))))
                     (rationalp (cadr (arg1 x))) ; OK, no realp constants
                     (eql (numerator (cadr (arg1 x))) 1))
                (if (stable-under-rewriting-products (invert-match x) mfc state)
		    (list (cons 'x (invert-match x)))
		  nil))
               ((eq (fn-symb (arg2 x)) 'UNARY--)
                (if (stable-under-rewriting-products (invert-match x) mfc state)
		    (list (cons 'x (invert-match x)))
		  nil))
               ((and (eq (fn-symb (arg2 x)) 'BINARY-*)
                     (rational-constant-p (arg1 (arg2 x)))
                     (< (unquote (arg1 (arg2 x))) 0))
                (if (stable-under-rewriting-products (invert-match x) mfc state)
		    (list (cons 'x (invert-match x)))
		  nil))
               (t
                nil)))
        ((eq (ffn-symb x) 'BINARY-*)
         (let ((temp (find-divisive-factor-scatter-exponents2 (arg1 x)
							      mfc state)))
           (if temp
               temp
             (find-divisive-factor-scatter-exponents2 (arg2 x)
						      mfc state))))
        (t
         nil)))

(defun find-divisive-factor-scatter-exponents1 (x mfc state)
  (declare (xargs :guard t))
  (cond ((or (variablep x)
             (fquotep x))
         nil)
        ((eq (ffn-symb x) 'BINARY-+)
         (let ((temp (find-divisive-factor-scatter-exponents2 (arg1 x)
							      mfc state)))
           (if temp
               temp
             (find-divisive-factor-scatter-exponents1 (arg2 x)
						      mfc state))))
        (t
         (find-divisive-factor-scatter-exponents2 x mfc state))))

(defun find-divisive-factor-scatter-exponents (lhs rhs mfc state)
  (declare (xargs :guard t))
  (let ((temp1 (find-divisive-factor-scatter-exponents1 lhs mfc state)))
    (if temp1
        temp1
      (let ((temp2 (find-divisive-factor-scatter-exponents1 rhs mfc state)))
        (if temp2
            temp2
          nil)))))

(defthm prefer-positive-exponents-scatter-exponents-equal
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
;                  (syntaxp (not (equal rhs ''0)))
;                  (syntaxp (not (equal lhs ''0)))
                  (syntaxp (in-term-order-* lhs mfc state))
		  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free
                   (find-divisive-factor-scatter-exponents lhs rhs
							   mfc state)
                   (x))
		  (syntaxp (not (equal x ''1)))
		  (syntaxp (not (equal x ''-1)))
                  (case-split (acl2-numberp x))
		  (case-split (not (equal x 0))))
             (equal (equal lhs rhs)
		    (equal (* x lhs) (* x rhs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This should probably be refactored and cleaned up.  Do I have
;;; divisive-factor-p defined anywhere already?

(defun find-rational-divisive-factor-scatter-exponents2 (x mfc state)
  (declare (xargs :guard t))
  (cond ((or (variablep x)
             (fquotep x))
         nil)
        ((eq (ffn-symb x) 'UNARY--)
	 (find-rational-divisive-factor-scatter-exponents2 (arg1 x) mfc state))
        ((eq (ffn-symb x) 'UNARY-/)
	 (if (and (proveably-real/rational 'x `((x . ,x)) mfc state)
		  (stable-under-rewriting-products (invert-match x) mfc state))
	     (list (cons 'x (invert-match x)))
	   nil))
        ((eq (ffn-symb x) 'EXPT)
         (cond ((eq (fn-symb (arg1 x)) 'UNARY-/)
                (if (and (proveably-real/rational 'x `((x . ,x)) mfc state)
			 (stable-under-rewriting-products (invert-match x) mfc state))
		    (list (cons 'x (invert-match x)))
		  nil))
               ((and (quotep (arg1 x))
		     (consp (cdr (arg1 x)))
                     (not (integerp (cadr (arg1 x))))
                     (rationalp (cadr (arg1 x))) ; OK, no realp constants
                     (eql (numerator (cadr (arg1 x))) 1))
                (if (and (proveably-real/rational 'x `((x . ,x)) mfc state)
			 (stable-under-rewriting-products (invert-match x) mfc state))
		    (list (cons 'x (invert-match x)))
		  nil))
               ((eq (fn-symb (arg2 x)) 'UNARY--)
                (if (and (proveably-real/rational 'x `((x . ,x)) mfc state)
			 (stable-under-rewriting-products (invert-match x) mfc state))
		    (list (cons 'x (invert-match x)))
		  nil))
               ((and (eq (fn-symb (arg2 x)) 'BINARY-*)
                     (rational-constant-p (arg1 (arg2 x)))
                     (< (unquote (arg1 (arg2 x))) 0))
                (if (and (proveably-real/rational 'x `((x . ,x)) mfc state)
			 (stable-under-rewriting-products (invert-match x) mfc state))
		    (list (cons 'x (invert-match x)))
		  nil))
               (t
                nil)))
        ((eq (ffn-symb x) 'BINARY-*)
         (let ((temp (find-rational-divisive-factor-scatter-exponents2 (arg1 x) mfc state)))
           (if temp
               temp
             (find-rational-divisive-factor-scatter-exponents2 (arg2 x) mfc state))))
        (t
         nil)))

(defun find-rational-divisive-factor-scatter-exponents1 (x mfc state)
  (declare (xargs :guard t))
  (cond ((or (variablep x)
             (fquotep x))
         nil)
        ((eq (ffn-symb x) 'BINARY-+)
         (let ((temp (find-rational-divisive-factor-scatter-exponents2 (arg1 x) mfc state)))
           (if temp
               temp
             (find-rational-divisive-factor-scatter-exponents1 (arg2 x) mfc state))))
        (t
         (find-rational-divisive-factor-scatter-exponents2 x mfc state))))

(defun find-rational-divisive-factor-scatter-exponents (lhs rhs mfc state)
  (declare (xargs :guard t))
  (let ((temp1 (find-rational-divisive-factor-scatter-exponents1 lhs mfc state)))
    (if temp1
        temp1
      (let ((temp2 (find-rational-divisive-factor-scatter-exponents1 rhs mfc state)))
        (if temp2
            temp2
          nil)))))

(defthm prefer-positive-exponents-scatter-exponents-<
    (implies (and (acl2-numberp lhs)
                  (acl2-numberp rhs)
;                  (syntaxp (not (equal rhs ''0)))
;                  (syntaxp (not (equal lhs ''0)))
                  (syntaxp (in-term-order-* lhs mfc state))
		  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free
                   (find-rational-divisive-factor-scatter-exponents lhs rhs
                                                                    mfc state)
                   (x))		  (syntaxp (not (equal x ''1)))
		  (syntaxp (not (equal x ''-1)))
                  (case-split (real/rationalp x))
		  (case-split (not (equal x 0))))
             (equal (< lhs rhs)
                    (cond ((< 0 x)
                           (< (* x lhs) (* x rhs)))
                          (t
                           (< (* x rhs) (* x lhs)))))))

(defthm prefer-positive-exponents-scatter-exponents-<-2
    (implies (and (real/rationalp lhs)
                  (real/rationalp rhs)
;                  (syntaxp (not (equal rhs ''0)))
;                  (syntaxp (not (equal lhs ''0)))
                  (syntaxp (in-term-order-* lhs mfc state))
		  (syntaxp (in-term-order-* rhs mfc state))
                  (bind-free
                   (find-divisive-factor-scatter-exponents lhs rhs
							   mfc state)
                   (x))
		  (syntaxp (not (equal x ''1)))
		  (syntaxp (not (equal x ''-1)))
                  (case-split (acl2-numberp x))
		  (case-split (not (equal x 0))))
             (equal (< lhs rhs)
                    (cond ((< 0 x)
                           (< (* x lhs) (* x rhs)))
                          (t
                           (< (* x rhs) (* x lhs))))))
    :hints (("Goal" :in-theory (enable big-helper-2))))
