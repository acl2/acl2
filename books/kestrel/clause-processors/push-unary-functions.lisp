; A simple clause-processor to push calls of unary functions into IF branches
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/if-eval" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(local (include-book "kestrel/terms-light/logic-termp" :dir :system))
(local (include-book "kestrel/utilities/arities-okp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
;(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))

;; TODO: Add support for unary-fns being :all.

(local (in-theory (disable alistp disjoin disjoin2
                           symbol-listp
                           member-equal
                           pairlis$
                           repeat)))

(local (in-theory (enable symbolp-when-member-equal-and-symbol-listp)))

;todo: move or make local
(defthm assoc-equal-of-pairlis$-of-repeat
  (implies (member-equal key keys)
           (equal (assoc-equal key (pairlis$ keys (repeat (len keys) val)))
                  (cons key val)))
  :hints (("Goal" :in-theory (enable pairlis$ repeat assoc-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Handle additional calls of UNARY-FN in TERM?
(defund apply-unary-fn-to-if-branches (unary-fn term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp unary-fn))))
  (if (and (call-of 'if term)
           (= 3 (len (fargs term))))
      `(if ,(farg1 term)
           ,(apply-unary-fn-to-if-branches unary-fn (farg2 term))
         ,(apply-unary-fn-to-if-branches unary-fn (farg3 term)))
    `(,unary-fn ,term)))

;; Supports the :well-formedness-guarantee.
(defthm logic-termp-of-apply-unary-fn-to-if-branches
  (implies (and (logic-termp term w)
                (logicp unary-fn w)
                (symbolp unary-fn)
                (not (equal 'quote unary-fn))
                (arities-okp (acons unary-fn 1 nil)
                             w))
           (logic-termp (apply-unary-fn-to-if-branches unary-fn term) w))
  :hints (("Goal" :in-theory (enable apply-unary-fn-to-if-branches))))

(defthm pseudo-termp-of-apply-unary-fn-to-if-branches
  (implies (and (pseudo-termp term)
                (symbolp unary-fn)
                ;; (not (equal 'quote unary-fn))
                )
           (pseudo-termp (apply-unary-fn-to-if-branches unary-fn term)))
  :hints (("Goal" :in-theory (enable apply-unary-fn-to-if-branches))))

;; Correctness theorem
(defthm if-eval-of-apply-unary-fn-to-if-branches
  (implies (not (equal 'quote unary-fn))
           (equal (if-eval (apply-unary-fn-to-if-branches unary-fn term) a)
                  (if-eval `(,unary-fn ,term) a)))
  :hints (("Goal" :in-theory (e/d (apply-unary-fn-to-if-branches
                                   if-eval-of-fncall-args)
                                  (if-eval-of-fncall-args-back)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Push calls of any of the unary-fns into IF branches
;; todo: dive into lambda bodies?
(defund push-unary-fns-into-ifs-in-term (term unary-fns)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp unary-fns))))
  (if (variablep term)
      term
    (let ((fn (ffn-symb term)))
      (if (eq 'quote fn)
          term
        (if (and (eq 'if fn)
                 (= 3 (len (fargs term))))
            `(if ,(push-unary-fns-into-ifs-in-term (farg1 term) unary-fns)
                 ,(push-unary-fns-into-ifs-in-term (farg2 term) unary-fns)
               ,(push-unary-fns-into-ifs-in-term (farg3 term) unary-fns))
          (if (and (symbolp fn)
                   (member-eq fn unary-fns)
                   (= 1 (len (fargs term))))
              (apply-unary-fn-to-if-branches fn (farg1 term))
            ;; todo: do more here?  we currently only handle unary calls in top-level ifs
            term))))))

;; Supports the :well-formedness-guarantee.
(defthm logic-termp-of-push-unary-fns-into-ifs-in-term
  (implies (and (logic-termp term w)
                (arities-okp '((if . 3))
                             w))
           (logic-termp (push-unary-fns-into-ifs-in-term term unary-fns) w))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-ifs-in-term))))

(defthm pseudo-termp-of-push-unary-fns-into-ifs-in-term
  (implies (pseudo-termp term)
           (pseudo-termp (push-unary-fns-into-ifs-in-term term unary-fns)))
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (enable push-unary-fns-into-ifs-in-term))))

;; Correctness theorem
(defthm if-eval-of-push-unary-fns-into-ifs-in-term
  (implies (and (alistp a)
                (pseudo-termp term)
                )
           (equal (if-eval (push-unary-fns-into-ifs-in-term term unary-fns) a)
                  (if-eval term a)))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-ifs-in-term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund push-unary-fns-into-ifs-in-literals (clause unary-fns)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (symbol-listp unary-fns))))
  (if (endp clause)
      nil
    (cons (push-unary-fns-into-ifs-in-term (first clause) unary-fns)
          (push-unary-fns-into-ifs-in-literals (rest clause) unary-fns))))

;; Supports the :well-formedness-guarantee.
(defthm logic-term-listp-of-push-unary-fns-into-ifs-in-literals
  (implies (and (logic-term-listp clause w)
                (arities-okp '((if . 3)) w))
           (logic-term-listp (push-unary-fns-into-ifs-in-literals clause unary-fns)
                             w))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-ifs-in-literals))))

(defthm pseudo-term-list-listp-of-push-unary-fns-into-ifs-in-literals
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (push-unary-fns-into-ifs-in-literals clause unary-fns)))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-ifs-in-literals))))

;; Correctness theorem
;strengthen to equal?
(defthm if-eval-of-disjoin-of-push-unary-fns-into-ifs-in-literals
  (implies (and (alistp a)
                (pseudo-term-listp clause))
           (iff (if-eval (disjoin (push-unary-fns-into-ifs-in-literals clause unary-fns)) a)
                (if-eval (disjoin clause) a)))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-ifs-in-literals
                                     ;; disjoin
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Return a list of one clause (like the one we started with but with the unary
;; function O-P pushed).
;; TODO: Deprecate in favor of the more general push-unary-fns-clause-processor.
(defund push-o-p-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (progn$ ;(cw "Len of clause is ~x0.~%" (len clause))
          ;(cw "Literals are ~x0.~%" clause)
          (list (push-unary-fns-into-ifs-in-literals clause '(o-p)))))

;; Supports the :well-formedness-guarantee.
(defthm logic-term-list-listp-of-push-o-p-clause-processor
  (implies (and (logic-term-listp clause w)
                (arities-okp '((o-p . 1)
                               (if . 3))
                             w))
           (logic-term-list-listp (push-o-p-clause-processor clause) w))
  :hints (("Goal" :in-theory (enable push-o-p-clause-processor))))

(defthm pseudo-term-list-listp-of-push-o-p-clause-processor
  (implies (pseudo-term-listp clause)
           (pseudo-term-list-listp (push-o-p-clause-processor clause)))
  :hints (("Goal" :in-theory (enable push-o-p-clause-processor))))

;; Main theorem
(defthm push-o-p-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (if-eval (conjoin-clauses (push-o-p-clause-processor clause)) a))
           (if-eval (disjoin clause) a))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee logic-term-list-listp-of-push-o-p-clause-processor))
  :hints (("Goal" :in-theory (enable push-o-p-clause-processor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Return a list of one clause (which is like the clause we started with but with the unary
;; supplied functions pushed).
(defund push-unary-fns-into-ifs-clause-processor (clause unary-fns)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (progn$ ;(cw "Len of clause is ~x0.~%" (len clause))
          ;(cw "Literals are ~x0.~%" clause)
   (if (not (symbol-listp unary-fns))
       (prog2$ (er hard? 'push-unary-fns-into-ifs-clause-processor "The unary-fns are not symbols: ~x0." unary-fns)
               (list clause))
     (list (push-unary-fns-into-ifs-in-literals clause unary-fns)))))

;; Supports the :well-formedness-guarantee.
(defthm logic-term-list-listp-of-push-unary-fns-into-ifs-clause-processor
  (implies (and (logic-term-listp clause w)
                (arities-okp '((if . 3)) w))
           (logic-term-list-listp (push-unary-fns-into-ifs-clause-processor clause unary-fns) w))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-ifs-clause-processor))))

(defthm pseudo-term-list-listp-of-push-unary-fns-into-ifs-clause-processor
  (implies (pseudo-term-listp clause)
           (pseudo-term-list-listp (push-unary-fns-into-ifs-clause-processor clause unary-fns)))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-ifs-clause-processor))))

;; Main theorem
(defthm push-unary-fns-into-ifs-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (if-eval (conjoin-clauses (push-unary-fns-into-ifs-clause-processor clause unary-fns)) a))
           (if-eval (disjoin clause) a))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee logic-term-list-listp-of-push-unary-fns-into-ifs-clause-processor))
  :hints (("Goal" :in-theory (enable push-unary-fns-into-ifs-clause-processor))))
