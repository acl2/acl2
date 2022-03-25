; An assistant to help find simple proofs
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "non-trivial-formals")
(include-book "free-vars-in-term")
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(mutual-recursion
 ;; Looks inside lambda bodies in a limited way (can return a term that is
 ;; inside a lambda if the lambda doesn't change the meaning of the term [by
 ;; non-trivially binding any of the term's vars]).  Result may include
 ;; lambda-applications.  Result includes no duplicates.
 ;; TODO: Rename to function-call-subterms.
 (defun find-all-fn-call-subterms (term dead-vars)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-listp dead-vars))
                   :verify-guards nil ; done below
                   ))
   (cond ((variablep term) nil) ;we exclude vars (no point in let binding a variable)
         ((quotep term) nil) ;we exclude constants (no point in let binding a constant)
         ((flambda-applicationp term)
          (let* ((args-result (find-all-fn-call-subterms-lst (fargs term) dead-vars))
                 (body-result (find-all-fn-call-subterms (lambda-body (ffn-symb term))
                                                         (union-eq (non-trivial-formals (lambda-formals (ffn-symb term)) (fargs term))
                                                                   dead-vars))))
            (if (not (intersection-eq (free-vars-in-term term) dead-vars))
                (add-to-set-equal term (union-equal body-result args-result))
              ;; term mentions vars whose meaning is changed by an overarching
              ;; lambda, so drop (we could try harder, by substituting, but
              ;; that could blow up):
              (union-equal body-result args-result))))
         (t ;; it's a regular function call:
          (let* ((args-result (find-all-fn-call-subterms-lst (fargs term) dead-vars)))
            (if (not (intersection-eq (free-vars-in-term term) dead-vars))
                (add-to-set-equal term args-result)
              ;; term mentions vars whose meaning is changed by an overarching
              ;; lambda, so drop (we could try harder, by substituting, but
              ;; that could blow up):
              args-result)))))
 (defun find-all-fn-call-subterms-lst (terms dead-vars)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-listp dead-vars))))
   (if (endp terms)
       nil
     (union-equal (find-all-fn-call-subterms (first terms) dead-vars)
                  (find-all-fn-call-subterms-lst (rest terms) dead-vars)))))

(make-flag find-all-fn-call-subterms)

(defthm-flag-find-all-fn-call-subterms
  (defthm pseudo-term-listp-of-find-all-fn-call-subterms
    (implies (pseudo-termp term)
             (pseudo-term-listp (find-all-fn-call-subterms term dead-vars)))
    :flag find-all-fn-call-subterms)
  (defthm pseudo-term-listp-of-find-all-fn-call-subterms-lst
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (find-all-fn-call-subterms-lst terms dead-vars)))
    :flag find-all-fn-call-subterms-lst))

(defthm-flag-find-all-fn-call-subterms
  (defthm true-listp-of-find-all-fn-call-subterms
    (true-listp (find-all-fn-call-subterms term dead-vars))
    :flag find-all-fn-call-subterms)
  (defthm true-listp-of-find-all-fn-call-subterms-lst
    (true-listp (find-all-fn-call-subterms-lst terms dead-vars))
    :flag find-all-fn-call-subterms-lst))

(verify-guards find-all-fn-call-subterms)
