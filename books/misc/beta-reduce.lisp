;;
;; Copyright (C) 2020, David Greve
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;;

;; The following book provides a proof of correctness for a simple
;; beta-reduction routine for a generic ACL2 evaluator.  Any user
;; defined ACL2 evaluator should support functional instantiation of
;; this result, allowing this beta reduction routine to be used
;; with any ACL2 evaluator, for example in proving a :meta rule.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defevaluator beta-eval beta-eval-list
  nil)

(defun pseudo-termp-key (arg term)
  (declare (type t arg term))
  (if arg (pseudo-term-listp term)
    (pseudo-termp term)))

(local
 (encapsulate nil
   (local (defun pos-ac-ind (x n)
            (if (endp x) n
              (list (pos-ac-ind (cdr x) (+ 1 n))
                    (pos-ac-ind (cdr x) 1)))))

   (defthm position-equal-ac-iff-zero
     (implies (and n
                   (syntaxp (not (equal n ''0))))
              (iff (position-equal-ac k x n)
                   (position-equal-ac k x 0)))
     :hints (("goal" :induct (pos-ac-ind x n))))

   (local (defthm blah
            (implies (syntaxp (and (quotep a) (quotep b)))
                     (equal (+ a b c)
                            (+ (+ a b) c)))))

   (local (defun pos-ac-ind2 (x n)
            (if (endp x) n
              (list (pos-ac-ind2 (cdr x) (+ 1 n))
                    (pos-ac-ind2 (cdr x) 0)))))

   (defthm position-equal-ac-redef
     (equal (position-equal-ac k x n)
            (cond ((endp x) nil)
                  ((equal k (car x)) n)
                  (t (let ((res (position-equal-ac k (cdr x) 0)))
                       (and res (+ 1 n res))))))
     :hints (("goal" :induct (pos-ac-ind2 x n)))
     :rule-classes ((:definition :clique (position-equal-ac)
                     :controller-alist ((position-equal-ac nil t nil)))))

   (defthm position-equal-ac-iff-member
     (implies n
              (iff (position-equal-ac k x n)
                   (member k x))))

   (defthm nth-of-position-is-assoc-of-pairlis
     (implies (member k x)
              (equal (nth (position-equal-ac k x 0) y)
                     (cdr (assoc k (pairlis$ x y)))))
     :hints (("goal" :induct (pairlis$ x y))))))

(defun beta-reduce-term (arg term keys vals)
  (declare (type (satisfies true-listp) keys vals))
  (declare (xargs :guard (pseudo-termp-key arg term)))
  (cond
   (arg
    (cond
     ((endp term) nil)
     (t (cons (beta-reduce-term nil (car term) keys vals)
	      (beta-reduce-term arg (cdr term) keys vals)))))
   (t
    (cond
     ((and (symbolp term) term)
      (let ((hit (assoc-eq term (pairlis$ keys vals))))
        (if hit (cdr hit) '(quote nil))))
     ((atom term) term)
     ((eq (car term) 'quote) term)
     ((consp (car term))
      (cons (car term) (beta-reduce-term t (CDR term) keys vals)))
     (t
      (cons (car term) (beta-reduce-term t (cdr term) keys vals)))))))

(defun lambda-expr-p (term)
  (declare (type t term))
  (and (consp term)
       (consp (car term))
       (equal (len (car term)) 3)))

(local
 (encapsulate
     ()

(defun beta-eval-key (arg term alist)
  (cond
   (arg
    (cond
     ((endp term) nil)
     (t (cons (beta-eval-key nil (car term) alist)
	      (beta-eval-key arg (cdr term) alist)))))
   (t
    (cond
     ((and (symbolp term) term)
      (cdr (assoc-eq term alist)))
     ((atom term) nil)
     ((eq (car term) 'quote) (car (cdr term)))
     ((consp (car term))
      (beta-eval (car (cdr (cdr (car term))))
                   (pairlis$ (car (cdr (car term)))
                             (beta-eval-key t (cdr term) alist))))
     (t (beta-eval term alist))))))

(defthmd beta-eval-key-reduction
  (equal (beta-eval-key arg term alist)
	 (if arg (beta-eval-list term alist)
	   (beta-eval term alist))))

(defthm append-nil-fix
  (equal (beta-eval-list (append list nil) a1)
	 (beta-eval-list list a1)))

(defthm late-binding-reduction
  (implies
   (equal (len keys) (len vals))
   (equal (beta-eval (cdr (assoc-eq term (pairlis$ keys vals))) a1)
	  (if (member term keys)
	      (cdr (assoc-eq term (pairlis$ keys (beta-eval-list vals a1))))
	    (beta-eval nil a1)))))

(defthm assoc-eq-pairlis$-non-member
  (implies
   (not (member term keys))
   (equal (assoc-eq term (pairlis$ keys vals))
	  nil)))

(defthm not-assoc-vals-irrelevant
  (implies
   (not (assoc-equal term (pairlis$ keys vals)))
   (not (assoc-equal term (pairlis$ keys (beta-eval-list vals a1))))))

(defthm assoc-beta-eval
  (implies
   (assoc-equal term (pairlis$ keys vals))
   (equal (cdr (assoc-equal term (pairlis$ keys (beta-eval-list vals a1))))
          (beta-eval (cdr (assoc-equal term (pairlis$ keys vals))) a1))))
            
(defthmd beta-eval-key-beta-reduce-term-2
  (equal (beta-eval-key arg (beta-reduce-term arg term keys vals) a1)
         (beta-eval-key arg term (pairlis$ keys (beta-eval-key t vals a1))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
	   :do-not-induct t
	   :induct (beta-reduce-term arg term keys vals)
	   :expand (:free (x) (hide x))
	   :in-theory (e/d (beta-eval-constraint-0
                            beta-eval-constraint-6
			    beta-eval-key-reduction)
			   nil))))

;; does lambda-expr need to do anything interesting in the case of
;; a lambda application?
(defun para-lambda-expr-p (term keys vals expr)
  (declare (type t term))
  (and (consp expr)
       (consp (car expr))
       (equal (len (car expr)) 3)
       (equal (cadr (car expr)) keys)
       (equal (caddr (car expr)) term)
       (equal (cdr expr) vals)))

(defun para-map-lambda-p (term keys vals expr)
  (declare (type t term))
  (if (consp term)
      (and (consp expr)
	   (para-lambda-expr-p (car term) keys vals (car expr))
	   (para-map-lambda-p (cdr term) keys vals (cdr expr)))
    (not (consp expr))))

(defun para-lambda-expr-key-p (arg term keys vals expr)
  (declare (type t term))
  (if arg (para-map-lambda-p term keys vals expr)
    (para-lambda-expr-p term keys vals expr)))

(defthm beta-eval-key-lambda-expr
  (implies
   (para-lambda-expr-key-p arg term keys vals expr)
   (equal (beta-eval-key arg expr a1)
	  (beta-eval-key arg term (pairlis$ keys (beta-eval-key t vals a1)))))
  :hints (("Goal" :in-theory (enable beta-eval-key-reduction))))

(defthmd lambda-expr-p-to-para-lambda-expr-key-p
  (equal (lambda-expr-p term)
	 (para-lambda-expr-key-p nil (car (cdr (cdr (car term)))) (car (cdr (car term))) (cdr term) term))
  :hints (("goal" :in-theory (enable lambda-expr-p para-lambda-expr-key-p))))

(in-theory (disable lambda-expr-p para-lambda-expr-key-p))

(defthmd beta-eval-lambda-expr-helper
  (implies
   (lambda-expr-p term)
   (equal (beta-eval-key nil term a1)
	  (beta-eval-key nil (car (cdr (cdr (car term))))
			   (pairlis$ (car (cdr (car term)))
				     (beta-eval-key t (cdr term) a1)))))
  :hints (("Goal"
           :in-theory
           (e/d (lambda-expr-p-to-para-lambda-expr-key-p) (beta-eval-key)))))

(defthm beta-eval-lambda-expr
  (implies
   (lambda-expr-p term)
   (equal (beta-eval term a1)
	  (beta-eval (car (cdr (cdr (car term))))
		       (pairlis$ (car (cdr (car term)))
				 (beta-eval-list (cdr term) a1)))))
  :hints (("Goal" :use beta-eval-lambda-expr-helper
	   :in-theory (enable beta-eval-key-reduction))))

(defthm beta-eval-beta-reduce-term
  (equal (beta-eval (beta-reduce-term nil term keys vals) a1)
         (beta-eval term (pairlis$ keys (beta-eval-list vals a1))))
  :hints (("Goal" :use (:instance beta-eval-key-beta-reduce-term-2
                                  (arg nil))
           :in-theory (enable beta-eval-key-reduction))))

(defthm beta-eval-to-beta-reduce-term
  (implies
   (and
    (lambda-expr-p term)
    (pseudo-termp term))
   (equal (beta-eval term a1)
	  (beta-eval (beta-reduce-term nil (car (cdr (cdr (car term))))
				       (car (cdr (car term)))
				       (cdr term)) a1))))

))

(defthm beta-eval-beta-reduce-term
  (equal (beta-eval (beta-reduce-term nil term keys vals) a1)
         (beta-eval term (pairlis$ keys (beta-eval-list vals a1)))))

(defthm beta-eval-beta-reduce-term-list
  (implies
   key
   (equal (beta-eval-list (beta-reduce-term key term keys vals) a1)
          (beta-eval-list term (pairlis$ keys (beta-eval-list vals a1)))))
  :hints (("Goal" :induct (len term))))

(defund beta-reduce-lambda-expr (term)
  (declare (type (satisfies lambda-expr-p) term)
	   (type (satisfies pseudo-termp) term)
	   (xargs :guard-hints (("Goal" :in-theory (enable lambda-expr-p)))))
  (beta-reduce-term nil (car (cdr (cdr (car term))))
		    (car (cdr (car term)))
		    (cdr term)))

(defthm beta-eval-to-beta-reduce-lambda-expr
  (implies
   (and
    (lambda-expr-p term)
    (pseudo-termp term))
   (equal (beta-eval term a1)
	  (beta-eval (beta-reduce-lambda-expr term) a1)))
  :hints (("Goal" :in-theory (e/d (beta-reduce-lambda-expr)
				  (beta-reduce-term)))))

(local
 (encapsulate
  ()

  ;; Here we show that it can be used to create a meta rule if only we
  ;; could trigger :meta rules on calls of lambdas.

  (defun beta-reduce-wrapper (term)
    (declare (type (satisfies pseudo-termp) term))
    (if (lambda-expr-p term)
        (beta-reduce-lambda-expr term)
      term))

  (defthm *meta*-beta-reduce-hide
    (implies
     (pseudo-termp term)
     (equal (beta-eval term a)
            (beta-eval (beta-reduce-wrapper term) a)))
    :rule-classes
    ;; ((:meta :trigger-fns nil))
    nil
    )

  ))

;; The primary theorem exported from this file can be instantiated
;; with any ACL2 evaluator to produce the desired result.
;;

(defmacro beta-reduction-theorem (ev ev-lst)
  (let ((name (packn-pos (list ev "-TO-BETA-REDUCE-LAMBDA-EXPR") ev)))
    `(defthm ,name
       (implies
	(and
	 (lambda-expr-p term)
	 (pseudo-termp term))
	(equal (,ev term a1)
	       (,ev (beta-reduce-lambda-expr term) a1)))
       :hints (("Goal"
                :in-theory (enable ,(packn (list ev "-CONSTRAINT-0")))
                :use (:functional-instance
                      beta-eval-to-beta-reduce-lambda-expr
                      (beta-eval ,ev)
                      (beta-eval-list ,ev-lst)))))))

;;
;; Now call beta-reduction-theorem on an evaluator and the -list
;; version of the evaluator, as illsutrated below, and you get the
;; correctness of beta reduction for that evaluator.
;;

(local
 (encapsulate
     ()

   (defevaluator test test-list
     nil)

   (beta-reduction-theorem test test-list)

   ))

(encapsulate
    ()

(local
(defun pseudo-term-alistp (alist)
  (declare (type t alist))
  (if (consp alist)
      (let ((entry (car alist)))
	(and (consp entry)
	     (pseudo-termp (cdr entry))
	     (pseudo-term-alistp (cdr alist))))
    (null alist))))

(local
(defthm pseudo-termp-cdr-assoc-pseudo-term-alistp
  (implies
   (pseudo-term-alistp alist)
   (pseudo-termp (cdr (assoc key alist))))))

(local
(defthm pseudo-term-alistp-pairlis$
  (implies
   (pseudo-term-listp vals)
   (pseudo-term-alistp (pairlis$ keys vals)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((pairlis$ keys vals))))))

(local
(defthm length-to-len
  (implies
   (true-listp x)
   (equal (length x) (len x)))))

(local (in-theory (disable length)))

(local
(defthm open-pseudo-termp-on-cons
  (equal (pseudo-termp (cons a list))
	 (let ((x (cons a list)))
	   (cond ((equal (car x) 'quote)
		  (and (consp (cdr x))
		       (equal (cddr x) nil)))
		 ((true-listp x)
		  (and (pseudo-term-listp (cdr x))
		       (cond ((symbolp (car x)) t)
			     ((true-listp (car x))
			      (and (equal (len (car x)) 3)
				   (equal (caar x) 'lambda)
				   (symbol-listp (cadar x))
				   (pseudo-termp (caddar x))
				   (equal (len (cadar x))
					  (len (cdr x)))))
			     (t nil))))
		 (t nil))))))

(defthm len-beta-reduce-term
  (implies
   arg
   (equal (len (acl2::beta-reduce-term arg term keys vals))
	  (len term))))

(defthm pseudo-termp-key-beta-reduce-term
  (implies
   (and
    (pseudo-term-listp vals)
    (acl2::pseudo-termp-key arg term))
   (acl2::pseudo-termp-key arg (acl2::beta-reduce-term arg term keys vals)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((acl2::beta-reduce-term arg term keys vals)))))

(local
(defthm pseudo-termp-key-implies-pseudo-termp
  (implies
   (acl2::pseudo-termp-key nil term)
   (pseudo-termp term))
  :rule-classes (:rewrite :forward-chaining)))

(local
(defthm pseudo-termp-key-implies-pseudo-term-listp
  (implies
   (acl2::pseudo-termp-key t list)
   (pseudo-term-listp list))
  :rule-classes (:rewrite :forward-chaining)))

(defthm pseudo-termp-beta-reduce-lambda-expr
  (implies
   (pseudo-termp term)
   (pseudo-termp (acl2::beta-reduce-lambda-expr term)))
  :hints (("Goal" :in-theory (enable acl2::beta-reduce-lambda-expr))))

(defun beta-reduce-pseudo-termp-switch (arg term)
  (declare (xargs :guard (acl2::pseudo-termp-key arg term)
		  :verify-guards nil))
  (cond
   (arg
    (cond
     ((endp term) nil)
     (t (cons (beta-reduce-pseudo-termp-switch nil (car term))
	      (beta-reduce-pseudo-termp-switch arg (cdr term))))))
   (t
    (cond
     ((symbolp term) term)
     ((atom term) term)
     ((eq (car term) 'quote) term)
     ((consp (car term))
      (acl2::beta-reduce-lambda-expr `((lambda ,(cadr (car term)) ,(beta-reduce-pseudo-termp-switch nil (caddr (car term))))
				       ,@(beta-reduce-pseudo-termp-switch t (CDR term)))))
     (t
      (cons (car term) (beta-reduce-pseudo-termp-switch t (cdr term))))))))

(defthm len-beta-reduce-pseudo-termp-switch
  (implies
   arg
   (equal (len (beta-reduce-pseudo-termp-switch arg term))
	  (len term))))

(defthm pseudo-termp-key-beta-reduce-pseudo-termp-switch
  (implies
   (acl2::pseudo-termp-key arg term)
   (acl2::pseudo-termp-key arg (beta-reduce-pseudo-termp-switch arg term))))

(defthm true-listp-beta-reduce-pseudo-termp-switch
  (implies
   arg
   (true-listp (beta-reduce-pseudo-termp-switch arg term))))

(local
(defthm pseudo-term-listp-append
  (implies
   (true-listp x)
   (equal (pseudo-term-listp (append x y))
	  (and (pseudo-term-listp x)
	       (pseudo-term-listp y))))))


(verify-guards beta-reduce-pseudo-termp-switch
	       :hints (("Goal" :in-theory (enable LAMBDA-EXPR-P))))


(defun beta-reduce-pseudo-termp (term)
  (beta-reduce-pseudo-termp-switch nil term))

(defthm pseudo-termp-beta-reduce-pseudo-termp
  (implies
   (pseudo-termp term)
   (pseudo-termp (beta-reduce-pseudo-termp term)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((beta-reduce-pseudo-termp term)))))

(in-theory (disable beta-reduce-pseudo-termp))

(defun beta-reduce-pseudo-term-listp (list)
  (if (endp list) nil
    (cons (beta-reduce-pseudo-termp (car list))
	  (beta-reduce-pseudo-term-listp (cdr list)))))

(defthm pseudo-term-listp-beta-reduce-pseudo-term-listp
  (implies
   (pseudo-term-listp list)
   (pseudo-term-listp (beta-reduce-pseudo-term-listp list)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((beta-reduce-pseudo-term-listp list)))))

)

(defxdoc beta-reduce
  :short "A beta-reduction routine and associated proof of correctness"
  :parents (meta-functions)
  :long "<p> This book provides a proof of correctness for a simple
beta-reduction routine under a generic ACL2 evaluator.  Any user defined
ACL2 evaluator should support functional instantiation of this result,
allowing this beta reduction routine to be used with any ACL2
evaluator, for example in proving a :meta rule.  </p>")
