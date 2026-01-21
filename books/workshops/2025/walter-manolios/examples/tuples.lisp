;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-records
  (:use :cl :z3)
  (:import-from :z3 :expect-error))

(in-package :z3-records)

;; You *must* do this BEFORE calling register-tuple-sort.
;; Additionally, you must redo any register-tuple-sort calls if you
;; call solver-init after them.
(solver-init)

;; Z3 supports named tuples. Here we register one with name :blah and
;; 2 fields, a and b.
(register-tuple-sort :blah ((a . :int) (b . :bool)))

;; Here's an example of a case where we have a variable that is of a
;; tuple sort, and we have some constraints on the values of its fields.
(solver-push)
(z3-assert
 (r :blah)
 (and (= (tuple-get :blah a r) 5)
      (tuple-get :blah b r)))
(check-sat)
(get-model)
;; Note that the value of the tuple returned here is quoted. This is
;; so that the value produced by check-sat can be used directly as let
;; bindings.
(get-model-as-assignment)
(solver-pop)

;; Here's a (contrived) example where we construct a tuple value and
;; check that it is equal to another tuple value.
(solver-push)
(z3-assert
 (a :int b :bool)
 (= (tuple-val :blah 123 nil)
    (tuple-val :blah a b)))
(check-sat)
(get-model)
(solver-pop)

;; To reiterate the first comment, if you call solver-init again after
;; register-tuple-sort, you will not be able to use the tuple sort
;; without calling its corresponding register-tuple-sort again.

(solver-init)
;; The following z3-assert errors out, explaining that you need to
;; re-register :blah.
(expect-error
 (z3-assert (r :blah)
            (= (tuple-get :blah a r) 5)))
