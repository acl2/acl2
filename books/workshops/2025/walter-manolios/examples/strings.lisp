;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-strings
  (:use :cl :z3))

(in-package :z3-strings)

(solver-init)

(solver-push)
(z3-assert
 (v :string)
 (= v "Hello, World!"))
(check-sat)
(get-model)
(solver-pop)

;; Strings are just a specialized sequence type - you can perform all
;; the normal sequence operations on them.
;; Note that the string type is equivalent to (:seq (_ :bitvec 8)) - i.e. 8-bit bitvectors
;; It's often easier to use seq-at instead of seq-nth. seq-at will
;; return a length-1 subsequence at the given offset, as opposed to
;; the element at that offset.
(solver-push)
(z3-assert
 ;; A sequence variable must have the element sort specified
 (v :string)
 (= (str.len v) 20))
;; Sequences are converted to CL lists.
(check-sat)
(get-model)
(get-model-as-assignment)
(solver-pop)

;; For convenience, many of the string operations can be referred to using the names given in Z3's tutorial (https://rise4fun.com/Z3/tutorial/sequences)
;; For example, you can write str.++ instead of seq-concat; they both will produce the same AST.
(solver-push)
(z3-assert
 (x y :string)
 (= (str.++ x y) "Hello, World!"))
(check-sat)
(get-model)
(solver-pop)

;; Note the use of seq.at instead of seq.nth
(solver-push)
(z3-assert
 (x :string)
 (and (> (str.len x) 2)
      (= (str.at x 2) "a")))
(check-sat)
(get-model)
(solver-pop)

;; Note that seq-at is underspecified if the index is out of bounds.
(solver-push)
(z3-assert
 (x y :string)
 (and
  (<= (str.len x) 3)
  (= (str.at x 4) y)))
(check-sat)
(get-model)
(solver-pop)

;; Z3 also provides lexicographic comparison operators
(solver-push)
(z3-assert
 (x y z :string)
 (and
  (str.prefixof "a" x)
  (str.prefixof "ab" y)
  (str.prefixof "a" z)
  (str.< x y)
  (str.< y z)))
(check-sat)
(get-model)
(solver-pop)

;; And you can convert between strings and integers
(solver-push)
(z3-assert
 (x :string y :int)
 (and (= x (int.to.str 5))
      (= y (str.to.int "3"))))
(check-sat)
(get-model)
(solver-pop)

;; Here's an example taken almost verbatim from the Z3 sequences tutorial (https://rise4fun.com/Z3/tutorial/sequences).
(solver-push)
(z3-assert (a b c :string)
           (and (= (str.++ a b) "abcd")
                (= (str.++ b c) "cdef")
                (not (= b ""))))
(check-sat)
(get-model)
(solver-pop)
