; A simple utility to make a lambda application (does not drop ignored vars)
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This is used in specifying other operations.
;; See also make-lambda-application-simple.

(include-book "free-vars-in-term")
(include-book "lambdas-closed-in-termp")
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; Makes a lambda that binds the FORMALS to the ACTUALS in the BODY (and binds extra vars as needed to make the lambda closed).
;; Similar to make-lambda-term, but make-lambda-term is worse because of the accumulator in all-vars1.
;; We could consider not making a lambda when FORMALS is nil, but perhaps we should keep this simple, given the name.
(defund make-lambda-term-simple (formals actuals body)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (equal (len formals)
                                     (len actuals))
                              (pseudo-termp body))))
  (let* ((free-vars (free-vars-in-term body))
         (extra-vars (set-difference-eq free-vars formals)))
    ;; Binds the formals to their actuals and all other vars to themselves:
    `((lambda ,(append formals extra-vars) ,body) ,@actuals ,@extra-vars)))

(defthm pseudo-termp-of-make-lambda-term-simple
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals)
                (equal (len actuals) (len formals)))
           (pseudo-termp (make-lambda-term-simple formals actuals body)))
  :hints (("Goal" :in-theory (enable make-lambda-term-simple))))

(defthm lambdas-closed-in-termp-of-make-lambda-term-simple
  (implies (and (pseudo-termp body)
                (lambdas-closed-in-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals)
                (lambdas-closed-in-termsp actuals)
                (equal (len actuals) (len formals)))
           (lambdas-closed-in-termp (make-lambda-term-simple formals actuals body)))
  :hints (("Goal" :in-theory (enable make-lambda-term-simple lambdas-closed-in-termp))))
