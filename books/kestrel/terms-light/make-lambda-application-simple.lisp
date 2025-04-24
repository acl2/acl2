; A simple utility to make a lambda application (drops ignored vars)
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also make-lambda-term-simple.
;; See proof of correctness in make-lambda-application-simple-proof.lisp

;; This does the following to the lambda:
;; 1. Remove any bindings of variables not free in the body.
;; 2. Add bindings of any additional free vars in the body, to ensure the lambda is closed.
;; 3. Replace a trivial lambda (all vars bound to themselves) with its body.

(include-book "free-vars-in-term")
(include-book "filter-formals-and-actuals")
(local (include-book "filter-formals-and-actuals-proofs"))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make a term that wraps BODY in a binding of the FORMALS to the ACTUALS, but make a LAMBDA instead of a LET.
;; Similar to make-lambda-application, but make-lambda-application is worse because of the accumulator in all-vars1.
;; Similar to make-lambda-term-simple, but this avoids adding unnecessary bindings.
;; Note that, despite the name, the result is not always a lambda application.
(defund make-lambda-application-simple (formals actuals body)
  (declare (xargs :guard (and (pseudo-termp body)
                              (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (equal (len formals)
                                     (len actuals)))))
  (let ((free-vars (free-vars-in-term body)))
    ;; Removes any formals not mentioned in the body (and their actuals):
    (mv-let (reduced-formals reduced-actuals)
      (filter-formals-and-actuals formals actuals free-vars)
      (if (equal reduced-formals reduced-actuals) ; also handles the case where reduced-formals is empty
          body ; no need to make a lambda at all (it would be trivial)
        ;; Binds the formals to their actuals and any extra-vars to themselves
        ;; (extra vars ensure the lambda is closed):
        (let* ((extra-vars (set-difference-eq free-vars formals))
               (new-formals (append reduced-formals extra-vars))
               (new-actuals (append reduced-actuals extra-vars)))
          `((lambda ,new-formals ,body) ,@new-actuals))))))

(defthm pseudo-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals)
                (equal (len actuals) (len formals)))
           (pseudo-termp (make-lambda-application-simple formals actuals body)))
  :hints (("Goal" :in-theory (enable make-lambda-application-simple))))

;; (make-lambda-application-simple '(x y) '((+ '1 x) (+ '1 y)) '(cons x y))
;; (make-lambda-application-simple '(x y) '((+ '1 x) (+ '1 y)) ''2) ; doesn't make a lambda
;; (make-lambda-application-simple '(x y) '(x y) '(cons x y)) ; doesn't make a lambda
;; (make-lambda-application-simple nil nil '(cons x y)) ; doesn't make a lambda
