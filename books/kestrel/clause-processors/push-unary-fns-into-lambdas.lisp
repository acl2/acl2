; A simple clause-processor to push calls of unary functions into lambda bodies
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/if-eval" :dir :system) ; because we are going to process a whole clause
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(local (include-book "kestrel/terms-light/logic-termp" :dir :system))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/utilities/arities-okp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))

(local (in-theory (disable alistp disjoin disjoin2
                           symbol-listp
                           member-equal
                           pairlis$
                           repeat
                           all-vars
                           len)))

(local (in-theory (enable symbolp-when-member-equal-and-symbol-listp)))

(local
  ;; for when all the keys are bound to the same value
  (defthm assoc-equal-of-pairlis$-of-repeat-of-len
    (implies (member-equal key keys)
             (equal (assoc-equal key (pairlis$ keys (repeat (len keys) val)))
                    (cons key val)))
    :hints (("Goal" :in-theory (enable assoc-equal pairlis$ len)))))

;todo: move
(defthm arities-okp-of-nil
  (arities-okp nil w)
  :hints (("Goal" :in-theory (enable arities-okp))))

;; Wrap UNARY-FN around TERM but if TERM is a lambda, push UNARY-FN into the lambda body.
(defund push-unary-fn-into-lambda-bodies (unary-fn term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp unary-fn))))
  (if (variablep term)
      `(,unary-fn ,term)
      (let ((fn (ffn-symb term)))
        (if (consp fn) ;; Term is ((lambda <formals> <body>) ...args...)
            `((lambda ,(lambda-formals fn) ,(push-unary-fn-into-lambda-bodies unary-fn (lambda-body fn))) ,@(fargs term))
            `(,unary-fn ,term)))))

(defthm free-vars-in-term-of-push-unary-fn-into-lambda-bodies
    (implies (not (equal unary-fn 'quote))
             (equal (free-vars-in-term (push-unary-fn-into-lambda-bodies unary-fn term))
                    (free-vars-in-term term)))
  :hints (("Goal" :in-theory (enable push-unary-fn-into-lambda-bodies))))

(local
  (defthm logic-fnsp-of-push-unary-fn-into-lambda-bodies
    (implies (and (logic-termp term w) ; weaken?
                  (logicp unary-fn w)
                  (symbolp unary-fn)
                  (not (equal 'quote unary-fn))
                  (arities-okp (acons unary-fn 1 nil) w))
             (logic-fnsp (push-unary-fn-into-lambda-bodies unary-fn term) w))
    :hints (("Goal" :in-theory (enable push-unary-fn-into-lambda-bodies len logic-termp)))))

(local
  (defthm termp-of-push-unary-fn-into-lambda-bodies
    (implies (and (logic-termp term w) ; weaken?
                  (logicp unary-fn w)
                  (symbolp unary-fn)
                  (not (equal 'quote unary-fn))
                  (arities-okp (acons unary-fn 1 nil)
                               w))
             (termp (push-unary-fn-into-lambda-bodies unary-fn term) w))
    :hints (("Goal" :in-theory (enable push-unary-fn-into-lambda-bodies len logic-termp)))))


;todo: prove from the 2 pieces
;; Supports the :well-formedness-guarantee.
(defthm logic-termp-of-push-unary-fn-into-lambda-bodies
  (implies (and (logic-termp term w)
                (logicp unary-fn w)
                (symbolp unary-fn)
                (not (equal 'quote unary-fn))
                (arities-okp (acons unary-fn 1 nil)
                             w))
           (logic-termp (push-unary-fn-into-lambda-bodies unary-fn term) w))
  :hints (("Goal" :in-theory (enable push-unary-fn-into-lambda-bodies len))))

(defthm pseudo-termp-of-push-unary-fn-into-lambda-bodies
  (implies (and (pseudo-termp term)
                (symbolp unary-fn)
                ;; (not (equal 'quote unary-fn))
                )
           (pseudo-termp (push-unary-fn-into-lambda-bodies unary-fn term)))
  :hints (("Goal" :in-theory (enable push-unary-fn-into-lambda-bodies len))))

;; The point here is to recur on a different alist for lambdas.
(local
 (defund push-unary-fn-into-lambda-bodies-induct (unary-fn term alist)
   (declare (irrelevant alist))
   (if (variablep term)
       `(,unary-fn ,term)
       (let ((fn (ffn-symb term)))
         (if (consp fn) ;; Term is ((lambda <formals> <body>) ...args...)
             `((lambda ,(lambda-formals fn) ,(push-unary-fn-into-lambda-bodies-induct
                                               unary-fn (lambda-body fn)
                                               (pairlis$ (lambda-formals fn) (if-eval-list (fargs term) alist))
                                               ))
               ,@(fargs term))
             `(,unary-fn ,term))))))

;; Correctness of push-unary-fn-into-lambda-bodies
(defthm if-eval-of-push-unary-fn-into-lambda-bodies
  (implies (not (equal 'quote unary-fn))
           (equal (if-eval (push-unary-fn-into-lambda-bodies unary-fn term) a)
                  (if-eval `(,unary-fn ,term) a)))
  :hints (("Goal"
           :induct (push-unary-fn-into-lambda-bodies-induct unary-fn term a)
           :in-theory (e/d (push-unary-fn-into-lambda-bodies-induct
                            push-unary-fn-into-lambda-bodies
                            if-eval-of-fncall-args)
                           (if-eval-of-fncall-args-back)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
  ;; Push calls of any of the unary-fns into lambda bodies
  ;; todo: dive into lambda bodies?
  ;; todo: fix indenting:
  (defund push-unary-fns-into-lambdas-in-term (term unary-fns)
    (declare (xargs :guard (and (pseudo-termp term)
                                (or (symbol-listp unary-fns) (eq :all unary-fns)))))
    (if (variablep term)
        term
      (let ((fn (ffn-symb term)))
        (if (eq 'quote fn)
            term
          ;; function call or lambda:
          ;; first apply to the args:
          (let ((new-args (push-unary-fns-into-lambdas-in-terms (fargs term) unary-fns)))
            (if (and (symbolp fn)
                     (or (eq :all unary-fns)
                         (member-eq fn unary-fns))
                     (= 1 (len (fargs term))))
                ;; it's a call of a unary function we've been told to handle:
                (let ((arg (farg1 term)))
                  (if t ;(and (consp arg)
                         ;  (consp (ffn-symb arg)) ; test for lambda.  arg is: ((lambda <formals> <body>) <args>)
                         ;  )
                      ;; todo: may often do nothing be re-cons:
                      (push-unary-fn-into-lambda-bodies fn arg)
                    `(,fn ,@new-args)))
              `(,fn ,@new-args)))))))

  (defund push-unary-fns-into-lambdas-in-terms (terms unary-fns)
    (declare (xargs :guard (and (pseudo-term-listp terms)
                                (or (symbol-listp unary-fns) (eq :all unary-fns)))))
    (if (endp terms)
        nil
      (cons (push-unary-fns-into-lambdas-in-term (first terms) unary-fns)
            (push-unary-fns-into-lambdas-in-terms (rest terms) unary-fns)))))

(defthm len-of-push-unary-fns-into-lambdas-in-terms
  (equal (len (push-unary-fns-into-lambdas-in-terms terms unary-fns))
         (len terms))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-lambdas-in-terms len))))

(local (make-flag push-unary-fns-into-lambdas-in-term))

(defthm-flag-push-unary-fns-into-lambdas-in-term
  (defthm pseudo-termp-of-push-unary-fns-into-lambdas-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (push-unary-fns-into-lambdas-in-term term unary-fns)))
    :flag push-unary-fns-into-lambdas-in-term)
  (defthm pseudo-term-listp-of-push-unary-fns-into-lambdas-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (push-unary-fns-into-lambdas-in-terms terms unary-fns)))
    :flag push-unary-fns-into-lambdas-in-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((pseudo-termp term)
                    (pseudo-term-listp (cdr term))
                    (push-unary-fns-into-lambdas-in-term term unary-fns))
           :in-theory (enable push-unary-fns-into-lambdas-in-term
                              push-unary-fns-into-lambdas-in-terms
                              (:d len)
                              pseudo-termp ; todo
                              termp
                              ))))

;; Supports the :well-formedness-guarantee.
(defthm-flag-push-unary-fns-into-lambdas-in-term
  (defthm logic-termp-of-push-unary-fns-into-lambdas-in-term
    (implies (logic-termp term w)
             (logic-termp (push-unary-fns-into-lambdas-in-term term unary-fns) w))
    :flag push-unary-fns-into-lambdas-in-term)
  (defthm logic-term-listp-of-push-unary-fns-into-lambdas-in-terms
    (implies (logic-term-listp terms w)
             (logic-term-listp (push-unary-fns-into-lambdas-in-terms terms unary-fns) w))
    :flag push-unary-fns-into-lambdas-in-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable push-unary-fns-into-lambdas-in-term
                              push-unary-fns-into-lambdas-in-terms
                              (:d len)
                              logic-termp ; todo
                              termp
                              ))))

;; can help when we know the length
(local
  (defthm if-eval-list-when-not-empty
    (implies (< 0 (len terms)) ; since we have info about len
             (equal (if-eval-list terms a)
                    (cons (if-eval (first terms) a)
                          (if-eval-list (rest terms) a))))
    :hints (("Goal" :in-theory (enable len)))))

(local
  (defthm len-helper
    (implies (equal 1 (len terms)) ; since we have info about len
             (not (consp (cdr terms))))
    :hints (("Goal" :expand (LEN (CDR TERMS))
             :in-theory (enable len)))))

;; Supports the :well-formedness-guarantee.
(defthm-flag-push-unary-fns-into-lambdas-in-term
  (defthm if-eval-of-push-unary-fns-into-lambdas-in-term
    (implies (alistp a)
             (equal (if-eval (push-unary-fns-into-lambdas-in-term term unary-fns) a)
                    (if-eval term a)))
    :flag push-unary-fns-into-lambdas-in-term)
  (defthm if-eval-list-of-push-unary-fns-into-lambdas-in-terms
    (implies (alistp a)
             (equal (if-eval-list (push-unary-fns-into-lambdas-in-terms terms unary-fns) a)
                    (if-eval-list terms a)))
    :flag push-unary-fns-into-lambdas-in-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (push-unary-fns-into-lambdas-in-term
                              push-unary-fns-into-lambdas-in-terms
                              ;(:d len)
                              logic-termp ; todo
                              termp
                              IF-EVAL-OF-FNCALL-ARGS
                              )
                           (IF-EVAL-OF-FNCALL-ARGS-BACK)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund push-unary-fns-into-lambdas-in-literals (clause unary-fns)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (or (symbol-listp unary-fns) (eq :all unary-fns)))))
  (if (endp clause)
      nil
    (cons (push-unary-fns-into-lambdas-in-term (first clause) unary-fns)
          (push-unary-fns-into-lambdas-in-literals (rest clause) unary-fns))))

;; Supports the :well-formedness-guarantee.
(defthm logic-term-listp-of-push-unary-fns-into-lambdas-in-literals
  (implies (logic-term-listp clause w)
           (logic-term-listp (push-unary-fns-into-lambdas-in-literals clause unary-fns)
                             w))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-lambdas-in-literals))))

(defthm pseudo-term-list-listp-of-push-unary-fns-into-lambdas-in-literals
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (push-unary-fns-into-lambdas-in-literals clause unary-fns)))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-lambdas-in-literals))))

;; Correctness theorem
;strengthen to equal?
(defthm if-eval-of-disjoin-of-push-unary-fns-into-lambdas-in-literals
  (implies (and (alistp a)
                (pseudo-term-listp clause))
           (iff (if-eval (disjoin (push-unary-fns-into-lambdas-in-literals clause unary-fns)) a)
                (if-eval (disjoin clause) a)))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-lambdas-in-literals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Return a list of one clause (like the one we started with but with the unary
;; functions pushed).
(defund push-unary-fns-into-lambdas-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (progn$ ;(cw "Len of clause is ~x0.~%" (len clause))
          ;(cw "Literals are ~x0.~%" clause)
          (list (push-unary-fns-into-lambdas-in-literals clause :all))))

;; Supports the :well-formedness-guarantee.
(defthm logic-term-list-listp-of-push-unary-fns-into-lambdas-clause-processor
  (implies (and (logic-term-listp clause w)
                )
           (logic-term-list-listp (push-unary-fns-into-lambdas-clause-processor clause) w))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-lambdas-clause-processor))))

(defthm pseudo-term-list-listp-of-push-unary-fns-into-lambdas-clause-processor
  (implies (pseudo-term-listp clause)
           (pseudo-term-list-listp (push-unary-fns-into-lambdas-clause-processor clause)))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-lambdas-clause-processor))))

;; Main theorem
(defthm push-unary-fns-into-lambdas-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (if-eval (conjoin-clauses (push-unary-fns-into-lambdas-clause-processor clause)) a))
           (if-eval (disjoin clause) a))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee logic-term-list-listp-of-push-unary-fns-into-lambdas-clause-processor))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-lambdas-clause-processor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parity trick is from :doc Using-computed-hints-6
(defun push-unary-fns-into-lambdas-for-all-goals (parity)
  (if parity
      `(:computed-hint-replacement ((push-unary-fns-into-lambdas-for-all-goals nil))
        :clause-processor (acl2::push-unary-fns-into-lambdas-clause-processor clause))
    ;; turn it back on:
    `(:computed-hint-replacement ((push-unary-fns-into-lambdas-for-all-goals t))
      :no-op t)))
