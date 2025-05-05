;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-regex
  (:use :cl :z3))

(in-package :z3-regex)

(solver-init)

;; Z3 has some support for regular expressions over sequences. This
;; includes strings.

(solver-push)
;; Note that re-empty takes in a regex sort, NOT the sequence sort that the regex is over.
;; The empty regex accepts no strings.
(z3-assert
 (x :string)
 (seq.in.re x (re.empty (:regex :string))))
(check-sat)
(solver-pop)

(solver-push)
;; The full regex accepts all strings.
(z3-assert
 (x :string)
 (seq.in.re x (re.full (:regex :string))))
(check-sat)
(get-model)
(solver-pop)

(solver-push)
;; A satisfying assignment for x is a string of length greater than 3
;; containing alternating pairs of letters from {a, b} and letters
;; from {d, e}.
(z3-assert
 (x :string)
 (and (> (str.len x) 3)
      (seq.in.re x (re.+ (re.++ (re.range "a" "b") (re.range "d" "e"))))))
(check-sat)
(get-model)
(solver-pop)

(solver-push)
;; We can write regexes over arbitrary sequences too.
;; Here we want a sequence of integers of length greater than 3 such
;; that it consists of 0 or more occurrences of the element 0 followed
;; by between 1 and 10 occurrences of the pattern (4 2).
(z3-assert
 (x (:seq :int))
 (and (> (seq.len x) 3)
      (seq.in.re x (re.++ (re.* (seq.to.re (seq 0)))
                          (re-loop (seq.to.re (seq 4 2)) 1 10)))))
(check-sat)
;; Note that the model is displayed as a concatenation of a bunch of
;; seq.unit calls. When converting the model back to Lisp values, this
;; will be handled by the interface so you instad get back a list of
;; values.
(get-model)
(get-model-as-assignment)
(solver-pop)

;; Regular expressions *must* be constant expressions.
;; The following 2 examples crash due to this.
#|
(solver-push)
(z3-assert
 (x (:regex :string))
 (and (seq.in.re "Hello, World!" x)
      (seq.in.re "Goodbye, World!" x)))
(check-sat)
(solver-pop)
|#

#|
(solver-push)
(z3-assert
 (x :string y :string)
 (seq.in.re y (re-loop (seq-to-re x) 2 4)))
(check-sat)
(get-model)
(solver-pop)
|#
