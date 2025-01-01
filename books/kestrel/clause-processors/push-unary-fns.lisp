; A clause-processor to push unary function calls into lambda bodies and ifs
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
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(local (include-book "kestrel/terms-light/logic-termp" :dir :system))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/utilities/arities-okp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; TODO: Optimize (e.g., using cons-with-hint)

(local (in-theory (disable alistp disjoin disjoin2
                           symbol-listp
                           member-equal
                           pairlis$
                           all-vars
                           len)))

(local (in-theory (enable symbolp-when-member-equal-and-symbol-listp)))

(mutual-recursion
  ;; Wrap ther WRAPPER-FN around term but push it inward through IFs and LAMBDAs.  Also, push unary fns in subterms.
  (defun push-unary-fns-and-wrap (term wrapper-fn unary-fns)
    (declare (xargs :guard (and (pseudo-termp term)
                                (symbolp wrapper-fn)
                                (or (symbol-listp unary-fns)
                                    (eq :all unary-fns)))
                    :measure (make-ord 1 (+ 1 (acl2-count term)) 1)))
    (if (variablep term)
        `(,wrapper-fn ,term) ; just wrap
      (let ((fn (ffn-symb term)))
        (if (eq 'quote fn)
            `(,wrapper-fn ,term) ; just wrap (could try to eval)
          (if (and (eq 'if fn)
                   (= 3 (len (fargs term))))
              ;; push into IF banches:
              `(if ,(push-unary-fns-in-term (farg1 term) unary-fns)
                   ,(push-unary-fns-and-wrap (farg2 term) wrapper-fn unary-fns)
                 ,(push-unary-fns-and-wrap (farg3 term) wrapper-fn unary-fns))
            (if (consp fn) ; term is ((lambda <formals> <body>) ...args...)
                `((lambda ,(lambda-formals fn) ,(push-unary-fns-and-wrap (lambda-body fn) wrapper-fn unary-fns)) ,@(push-unary-fns-in-terms (fargs term) unary-fns))
              ;; not a special term:
              `(,wrapper-fn ,(push-unary-fns-in-term term unary-fns))))))))

  (defun push-unary-fns-in-term (term unary-fns)
    (declare (xargs :guard (and (pseudo-termp term)
                                (or (symbol-listp unary-fns)
                                    (eq :all unary-fns)))
                    :measure (make-ord 1 (+ 1 (acl2-count term)) 0)))
    (if (variablep term)
        term
      (let ((fn (ffn-symb term)))
        (if (eq 'quote fn)
            term
          (if (consp fn) ; term is ((lambda <formals> <body>) ...args...)
              `((lambda ,(lambda-formals fn) ,(push-unary-fns-in-term (lambda-body fn) unary-fns)) ,@(push-unary-fns-in-terms (fargs term) unary-fns))
            (if (and (symbolp fn) ; drop?
                     (= 1 (len (fargs term)))
                     (or (eq :all unary-fns)
                         (member-eq fn unary-fns)))
                ;; unary function call to push:
                (push-unary-fns-and-wrap (farg1 term) fn unary-fns)
              ;; normal function call:
              `(,fn ,@(push-unary-fns-in-terms (fargs term) unary-fns))))))))

  (defun push-unary-fns-in-terms (terms unary-fns)
    (declare (xargs :guard (and (pseudo-term-listp terms)
                                (or (symbol-listp unary-fns)
                                    (eq :all unary-fns)))
                    :measure (make-ord 1 (+ 1 (acl2-count terms)) 0)))
    (if (endp terms)
        nil
      (cons (push-unary-fns-in-term (first terms) unary-fns)
            (push-unary-fns-in-terms (rest terms) unary-fns)))))

(defthm len-of-push-unary-fns-in-terms
  (equal (len (push-unary-fns-in-terms terms unary-fns))
         (len terms))
  :hints (("Goal" :in-theory (enable push-unary-fns-in-terms (:i len)))))

(local (make-flag push-unary-fns-and-wrap))

(defthm-flag-push-unary-fns-and-wrap
  (defthm free-vars-in-term-of-push-unary-fns-and-wrap
    (implies (and (pseudo-termp term)
                  (symbolp wrapper-fn)
                  (not (equal wrapper-fn 'quote)))
             (equal (free-vars-in-term (push-unary-fns-and-wrap term wrapper-fn unary-fns))
                    (free-vars-in-term term)))
    :flag push-unary-fns-and-wrap)
  (defthm free-vars-in-term-of-push-unary-fns-in-term
    (implies (pseudo-termp term)
             (equal (free-vars-in-term (push-unary-fns-in-term term unary-fns))
                    (free-vars-in-term term)))
    :flag push-unary-fns-in-term)
  (defthm free-vars-in-terms-of-push-unary-fns-in-terms
    (implies (pseudo-term-listp terms)
             (equal (free-vars-in-terms (push-unary-fns-in-terms terms unary-fns))
                    (free-vars-in-terms terms)))
    :flag push-unary-fns-in-terms)
  :hints (("Goal" :expand ((free-vars-in-term term)
                           (free-vars-in-terms (cdr term)))
           :in-theory (enable logic-termp termp free-vars-in-term))))

;; ;; Supports the :well-formedness-guarantee.
(defthm-flag-push-unary-fns-and-wrap
  (defthm logic-termp-of-push-unary-fns-and-wrap
    (implies (and (logic-termp term w)
                  (symbolp wrapper-fn)
                  (not (equal wrapper-fn 'quote))
                  (arities-okp (acons wrapper-fn 1 nil) w))
             (logic-termp (push-unary-fns-and-wrap term wrapper-fn unary-fns) w))
    :flag push-unary-fns-and-wrap)
  (defthm logic-termp-of-push-unary-fns-in-term
    (implies (logic-termp term w)
             (logic-termp (push-unary-fns-in-term term unary-fns) w))
    :flag push-unary-fns-in-term)
  (defthm logic-term-listp-of-push-unary-fns-in-terms
    (implies (logic-term-listp terms w)
             (logic-term-listp (push-unary-fns-in-terms terms unary-fns) w))
    :flag push-unary-fns-in-terms)
  :hints (("Goal" :in-theory (enable LOGIC-TERMP termp))))

(defthm-flag-push-unary-fns-and-wrap
  (defthm pseudo-termp-of-push-unary-fns-and-wrap
    (implies (and (pseudo-termp term)
                  (symbolp wrapper-fn)
                  (not (equal wrapper-fn 'quote)))
             (pseudo-termp (push-unary-fns-and-wrap term wrapper-fn unary-fns)))
    :flag push-unary-fns-and-wrap)
  (defthm pseudo-termp-of-push-unary-fns-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (push-unary-fns-in-term term unary-fns)))
    :flag push-unary-fns-in-term)
  (defthm pseudo-term-listp-of-push-unary-fns-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (push-unary-fns-in-terms terms unary-fns)))
    :flag push-unary-fns-in-terms)
  :hints (("Goal" :in-theory (enable PSEUDO-TERMP termp))))

;; the point is to recur on a different alist for lambdas:
(local
  (mutual-recursion
    ;; Wrap ther WRAPPER-FN around term but push it inward through IFs and LAMBDAs.  Also, push unary fns in subterms.
    (defun induct-push-unary-fns-and-wrap (term wrapper-fn unary-fns alist)
      (declare (xargs :measure (make-ord 1 (+ 1 (acl2-count term)) 1))
               (irrelevant alist))
      (if (variablep term)
          `(,wrapper-fn ,term) ; just wrap
        (let ((fn (ffn-symb term)))
          (if (eq 'quote fn)
              `(,wrapper-fn ,term) ; just wrap (could try to eval)
            (if (and (eq 'if fn)
                     (= 3 (len (fargs term))))
                ;; push into IF banches:
                `(if ,(induct-push-unary-fns-in-term (farg1 term) unary-fns alist)
                     ,(induct-push-unary-fns-and-wrap (farg2 term) wrapper-fn unary-fns alist)
                   ,(induct-push-unary-fns-and-wrap (farg3 term) wrapper-fn unary-fns alist))
              (if (consp fn) ; term is ((lambda <formals> <body>) ...args...)
                  `((lambda ,(lambda-formals fn) ,(induct-push-unary-fns-and-wrap (lambda-body fn) wrapper-fn unary-fns
                                                                                  (pairlis$ (lambda-formals fn) (if-eval-list (fargs term) alist))))
                    ,@(induct-push-unary-fns-in-terms (fargs term) unary-fns alist))
                ;; not a special term:
                `(,wrapper-fn ,(induct-push-unary-fns-in-term term unary-fns alist))))))))

    (defun induct-push-unary-fns-in-term (term unary-fns alist)
      (declare (xargs :measure (make-ord 1 (+ 1 (acl2-count term)) 0))
               (irrelevant alist))
      (if (variablep term)
          term
        (let ((fn (ffn-symb term)))
          (if (eq 'quote fn)
              term
            (if (consp fn) ; term is ((lambda <formals> <body>) ...args...)
                `((lambda ,(lambda-formals fn) ,(induct-push-unary-fns-in-term (lambda-body fn) unary-fns
                                                                               (pairlis$ (lambda-formals fn) (if-eval-list (fargs term) alist))))
                  ,@(induct-push-unary-fns-in-terms (fargs term) unary-fns alist))
              (if (and (symbolp fn) ; drop?
                       (= 1 (len (fargs term)))
                       (or (eq :all unary-fns)
                           (member-eq fn unary-fns)))
                  ;; unary function call to push:
                  (induct-push-unary-fns-and-wrap (farg1 term) fn unary-fns alist)
                ;; normal function call:
                `(,fn ,@(induct-push-unary-fns-in-terms (fargs term) unary-fns alist))))))))

    (defun induct-push-unary-fns-in-terms (terms unary-fns alist)
      (declare (xargs :measure (make-ord 1 (+ 1 (acl2-count terms)) 0))
               (irrelevant alist))
      (if (endp terms)
          nil
        (cons (induct-push-unary-fns-in-term (first terms) unary-fns alist)
              (induct-push-unary-fns-in-terms (rest terms) unary-fns alist))))))

(local (make-flag induct-push-unary-fns-and-wrap))

;; Correctness theorem
(defthm-flag-induct-push-unary-fns-and-wrap
  (defthm if-eval-of-push-unary-fns-and-wrap
    (implies (and (alistp alist)
                  (pseudo-termp term)
                  (symbolp wrapper-fn)
                  (not (equal wrapper-fn 'quote)))
             (equal (if-eval (push-unary-fns-and-wrap term wrapper-fn unary-fns) alist)
                    (if-eval `(,wrapper-fn ,term) alist)))
    :flag induct-push-unary-fns-and-wrap)
  (defthm if-eval-of-push-unary-fns-in-term
    (implies (and (alistp alist)
                  (pseudo-termp term))
             (equal (if-eval (push-unary-fns-in-term term unary-fns) alist)
                    (if-eval term alist)))
    :flag induct-push-unary-fns-in-term)
  (defthm if-eval-list-of-push-unary-fns-in-terms
    (implies (and (alistp alist)
                  (pseudo-term-listp terms))
             (equal (if-eval-list (push-unary-fns-in-terms terms unary-fns) alist)
                    (if-eval-list terms alist)))
    :flag induct-push-unary-fns-in-terms)
  :hints (("Goal" :in-theory (e/d (push-unary-fns-in-terms if-eval-of-fncall-args)
                                  (if-eval-of-fncall-args-back)))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lifts it to clauses
(defund push-unary-fns-in-literals (clause unary-fns)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (or (symbol-listp unary-fns) (eq :all unary-fns)))))
  (if (endp clause)
      nil
    (cons (push-unary-fns-in-term (first clause) unary-fns)
          (push-unary-fns-in-literals (rest clause) unary-fns))))

;; Supports the :well-formedness-guarantee.
(defthm logic-term-listp-of-push-unary-fns-in-literals
  (implies (logic-term-listp clause w)
           (logic-term-listp (push-unary-fns-in-literals clause unary-fns)
                             w))
  :hints (("Goal" :in-theory (enable push-unary-fns-in-literals))))

(defthm pseudo-term-list-listp-of-push-unary-fns-in-literals
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (push-unary-fns-in-literals clause unary-fns)))
  :hints (("Goal" :in-theory (enable push-unary-fns-in-literals))))

;; Correctness theorem
;strengthen to equal?
(defthm if-eval-of-disjoin-of-push-unary-fns-in-literals
  (implies (and; (symbol-listp unary-fns)
                (alistp a)
                (pseudo-term-listp clause))
           (iff (if-eval (disjoin (push-unary-fns-in-literals clause unary-fns)) a)
                (if-eval (disjoin clause) a)))
  :hints (("Goal" :in-theory (enable push-unary-fns-in-literals))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Return a list of one clause (like the one we started with but with the unary
;; functions pushed).
(defund push-unary-fns-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (progn$ ;(cw "Len of clause is ~x0.~%" (len clause))
          ;(cw "Literals are ~x0.~%" clause)
          (list (push-unary-fns-in-literals clause :all))))

;; Supports the :well-formedness-guarantee.
(defthm logic-term-list-listp-of-push-unary-fns-clause-processor
  (implies (logic-term-listp clause w)
           (logic-term-list-listp (push-unary-fns-clause-processor clause) w))
  :hints (("Goal" :in-theory (enable push-unary-fns-clause-processor))))

(defthm pseudo-term-list-listp-of-push-unary-fns-clause-processor
  (implies (pseudo-term-listp clause)
           (pseudo-term-list-listp (push-unary-fns-clause-processor clause)))
  :hints (("Goal" :in-theory (enable push-unary-fns-clause-processor))))

;; Main theorem
(defthm push-unary-fns-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (if-eval (conjoin-clauses (push-unary-fns-clause-processor clause)) a))
           (if-eval (disjoin clause) a))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee logic-term-list-listp-of-push-unary-fns-clause-processor))
  :hints (("Goal" :in-theory (enable push-unary-fns-clause-processor))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Apply the push-unary-fns clause-processor to all goals.
;; (The parity trick used here is from :doc Using-computed-hints-6.)
;; TODO: Should we just do it in the conclusion of each goal?
(defun push-unary-fns-for-all-goals (parity)
  (if parity
      ;; Apply the clause-processor and turn the parity to nil so that next time
      ;; other proof processes get a chanve:
      `(:computed-hint-replacement ((push-unary-fns-for-all-goals nil))
        :clause-processor (acl2::push-unary-fns-clause-processor clause))
    ;; Do nothing (ensure other proof processes get a change) but arrange to
    ;; have the clause-processor hint fire on subsequent goals:
    `(:computed-hint-replacement ((push-unary-fns-for-all-goals t))
      :no-op t)))
