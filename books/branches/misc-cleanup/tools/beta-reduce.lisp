;; Contributed by David Greve

;; The following book provides a proof of correctness for a simple
;; beta-reduction routine for a generic ACL2 evaluator.  Any user
;; defined ACL2 evaluator should support functional instantiation of
;; this result, allowing this beta reduction routine to be used
;; with any ACL2 evaluator, for example in proving a :meta rule.

(in-package "ACL2")

(defevaluator beta-eval beta-eval-list
  nil)

(defun pseudo-termp-key (arg term)
  (declare (type t arg term))
  (if arg (pseudo-term-listp term)
    (pseudo-termp term)))

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
      (if (member term keys)
	  (cdr (assoc-eq term (pairlis$ keys vals)))
	'(quote nil)))
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
     ((eq (car term) 'quote) (CAR (CDR term)))
     ((consp (car term))
      (beta-eval (CAR (CDR (CDR (CAR term))))
                   (PAIRLIS$ (CAR (CDR (CAR term)))
                             (BETA-EVAL-key t (CDR term) alist))))
     (t (beta-eval term alist))))))

(defthmd beta-eval-key-reduction
  (equal (beta-eval-key arg term alist)
	 (if arg (beta-eval-list term alist)
	   (beta-eval term alist))))

(defun wf-beta-term (arg term)
  (cond
   (arg 
    (cond 
     ((endp term) t)
     (t (and (wf-beta-term nil (car term))
	     (wf-beta-term arg (cdr term))))))
   (t
    (cond
     ((symbolp term) t)
     ((atom term) nil)
     ((eq (car term) 'quote) t)
     ((consp (car term))
      (wf-beta-term t (CDR term)))
     (t (wf-beta-term t (cdr term)))))))

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

(defthmd beta-eval-key-beta-reduce-term
  (implies
   (and
    (wf-beta-term arg term)
    (equal (len keys) (len vals)))
   (equal (beta-eval-key arg (beta-reduce-term arg term keys vals) a1)
	  (beta-eval-key arg term (pairlis$ keys 
					    (beta-eval-key t vals a1)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
	   :do-not-induct t
	   :induct (beta-reduce-term arg term keys vals)
	   :expand (:free (x) (hide x))
	   :in-theory (e/d (beta-eval-constraint-0 
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
	 (para-lambda-expr-key-p nil (CAR (CDR (CDR (CAR term)))) (CAR (CDR (CAR term))) (cdr term) term))
  :hints (("goal" :in-theory (enable lambda-expr-p para-lambda-expr-key-p))))

(in-theory (disable lambda-expr-p para-lambda-expr-key-p))

(defthmd beta-eval-lambda-expr-helper
  (implies
   (lambda-expr-p term)
   (equal (beta-eval-key nil term a1)
	  (beta-eval-key nil (CAR (CDR (CDR (CAR term))))
			   (pairlis$ (CAR (CDR (CAR term))) 
				     (beta-eval-key t (cdr term) a1)))))
  :hints (("Goal"
           :in-theory
           (e/d (lambda-expr-p-to-para-lambda-expr-key-p) (beta-eval-key)))))

(defthm beta-eval-lambda-expr
  (implies
   (lambda-expr-p term)
   (equal (beta-eval term a1)
	  (beta-eval (CAR (CDR (CDR (CAR term))))
		       (pairlis$ (CAR (CDR (CAR term))) 
				 (beta-eval-list (cdr term) a1)))))
  :hints (("Goal" :use beta-eval-lambda-expr-helper
	   :in-theory (enable beta-eval-key-reduction))))

(defthm pseudo-termp-key-implies-wf-beta-term
  (implies
   (pseudo-termp-key arg term)
   (wf-beta-term arg term))
  :hints (("Goal" :induct (wf-beta-term arg term))))

(defthm beta-eval-beta-reduce-term
  (implies
   (and
    (wf-beta-term nil term)
    (equal (len keys) (len vals)))
   (equal (beta-eval (beta-reduce-term nil term keys vals) a1)
	  (beta-eval term (pairlis$ keys (beta-eval-list vals a1)))))
  :hints (("Goal" :use (:instance beta-eval-key-beta-reduce-term
				  (arg nil))
	   :in-theory (enable beta-eval-key-reduction))))

(defthm beta-eval-to-beta-reduce-term
  (implies
   (and
    (lambda-expr-p term)
    (pseudo-termp term))
   (equal (beta-eval term a1)
	  (beta-eval (beta-reduce-term nil (CAR (CDR (CDR (CAR term)))) 
				       (CAR (CDR (CAR term)))
				       (cdr term)) a1))))

))

(defund beta-reduce-lambda-expr (term)
  (declare (type (satisfies lambda-expr-p) term)
	   (type (satisfies pseudo-termp) term)
	   (xargs :guard-hints (("Goal" :in-theory (enable lambda-expr-p)))))
  (beta-reduce-term nil (CAR (CDR (CDR (CAR term))))
		    (CAR (CDR (CAR term)))
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

