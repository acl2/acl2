; Some tests of case-match
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;; Normal example
(defun foo (x)
  (case-match x
    (3 'x-is-three)
    (('cons y z) (declare (ignore y z)) 'x-is-a-call-of-cons)
    (& 'x-is-something-else)))

(assert-equal (foo '3) 'x-is-three)
(assert-equal (foo '(cons x y)) 'x-is-a-call-of-cons)
(assert-equal (foo '(blah x y)) 'x-is-something-else)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun foo2 (x)
  (case-match x
    ;; test that multiple ampersands don't have to match the same thing:
    (('cons & &) 'x-is-a-call-of-cons)
    (& 'x-is-something-else)))

(assert-equal (foo2 '(cons x y)) 'x-is-a-call-of-cons)
(assert-equal (foo2 '(blah x y)) 'x-is-something-else)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A test with multiple declares.  Previously, :doc case-match disallowed this,
;; though it worked fine.
(defun foo3 (x)
  (case-match x
    (('cons y z) (declare (ignore y)) (declare (ignore z)) 'x-is-a-call-of-cons)
    (& 'x-is-something-else)))

(assert-equal (foo3 '(cons x y)) 'x-is-a-call-of-cons)
(assert-equal (foo3 '(blah x y)) 'x-is-something-else)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Illegal: First arg of case-match is not a symbol.
(must-fail
 (defun foo4 (x)
   (case-match (+ 1 x)
     (3 'x-is-three)
     (& 'x-is-something-else))))

;; Illegal: First arg of case-match is not symbol.
;; Could perhaps be made legal.
(must-fail
 (defun foo4b (x)
   (case-match '(foo bar)
     (3 'x-is-three)
     (& 'x-is-something-else))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Okay, since nil is a symbol, even though it's not a variable.
(defun foo5 ()
  (case-match nil
    (nil "nil")
    (& "something-else")))

(assert-equal (foo5) "nil")

;; Okay, since t is a symbol, even though it's not a variable.
(defun foo6 ()
  (case-match t
    (nil "nil")
    (t "t")
    (& "something-else")))

(assert-equal (foo6) "t")

;; Okay, since :key is a symbol, even though it's not a variable.
(defun foo7 ()
  (case-match :key
    (:key ":key")
    (& "something-else")))

(assert-equal (foo7) ":key")

;; Okay, since *c* is a symbol, even though it's not a variable.
(defconst *c* 7)
(defun foo8 ()
  (case-match *c*
    (7 "seven")
    (& "something-else")))

(assert-equal (foo8) "seven")
