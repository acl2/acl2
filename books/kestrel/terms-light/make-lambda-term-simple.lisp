; A simple utility to make a lambda application (does not drop ignored vars)
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also make-lambda-application-simple

(include-book "free-vars-in-term")
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; Similar to make-lambda-term, but make-lambda-term is worse because of the accumulator in all-vars1.
;; TODO: Don't make a lambda when FORMALS is nil.
(defund make-lambda-term-simple (formals actuals body)
  (declare (xargs :guard (and (pseudo-termp body)
                              (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (equal (len formals)
                                     (len actuals)))))
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
