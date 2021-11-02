; Changes all calls of a function to be on its (lambda-bound) formals
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This is useful when generating C code with ATC.

(include-book "tools/flag" :dir :system)
(include-book "kestrel/utilities/non-trivial-bindings" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; Ensures that all calls of TARGET-FN are on actuals that are just its formals
;; (lambda-bound as needed).  Consider calling reconstruct-lets-in-term after
;; calling this.
(mutual-recursion
 (defund let-bind-formals-in-calls-in-term (term target-fn target-fn-formals)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbolp target-fn)
                               (symbol-listp target-fn-formals))
                   :measure (acl2-count term)))
   (if (or (variablep term)
           (fquotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((fn (ffn-symb term))
            (new-args (let-bind-formals-in-calls-in-terms (fargs term) target-fn target-fn-formals)))
       (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((new-lambda-body (let-bind-formals-in-calls-in-term (lambda-body fn) target-fn target-fn-formals))) ;;apply recursively to the lambda body
             `((lambda ,(lambda-formals fn) ,new-lambda-body) ,@new-args))
         (if (and (eq fn target-fn)
                  (= (len (fargs term))
                     (len target-fn-formals)))
             (let* ((bindings (non-trivial-bindings target-fn-formals new-args)) ; don't need to bind any var whose correspondong arg is itself
                    (lambda-formals (strip-cars bindings))
                    (new-args (strip-cdrs bindings)))
               `((lambda ,lambda-formals (,fn ,@target-fn-formals)) ,@new-args))
           ;;not a lambda application, so just rebuild the function call:
           `(,fn ,@new-args))))))

 (defund let-bind-formals-in-calls-in-terms (terms target-fn target-fn-formals)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbolp target-fn)
                               (symbol-listp target-fn-formals))
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (let-bind-formals-in-calls-in-term (first terms) target-fn target-fn-formals)
           (let-bind-formals-in-calls-in-terms (rest terms) target-fn target-fn-formals)))))

(defthm len-of-let-bind-formals-in-calls-in-terms
  (equal (len (let-bind-formals-in-calls-in-terms terms target-fn target-fn-formals))
         (len terms))
  :hints (("Goal" :in-theory (enable (:i len)
                                     let-bind-formals-in-calls-in-terms))))

(make-flag let-bind-formals-in-calls-in-term)

;; Let binding formals preserves pseudo-termp.
(defthm-flag-let-bind-formals-in-calls-in-term
  (defthm pseudo-termp-of-let-bind-formals-in-calls-in-term
    (implies (and (pseudo-termp term)
                  (symbol-listp target-fn-formals))
             (pseudo-termp (let-bind-formals-in-calls-in-term term target-fn target-fn-formals)))
    :flag let-bind-formals-in-calls-in-term)
  (defthm pseudo-term-listp-of-let-bind-formals-in-calls-in-terms
    (implies (and (pseudo-term-listp terms)
                  (symbol-listp target-fn-formals))
             (pseudo-term-listp (let-bind-formals-in-calls-in-terms terms target-fn target-fn-formals)))
    :flag let-bind-formals-in-calls-in-terms)
  :hints (("Goal" :in-theory (enable let-bind-formals-in-calls-in-term
                                     let-bind-formals-in-calls-in-terms))))
