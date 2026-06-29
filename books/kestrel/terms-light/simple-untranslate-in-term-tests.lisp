; Tests for simple-untranslate-in-term
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "simple-untranslate-in-term")
(include-book "std/testing/assert-equal" :dir :system)

;; Self-quoting constants get unquoted:
(assert-equal (simple-untranslate-in-term ''3) 3)
(assert-equal (simple-untranslate-in-term ''"foo") "foo")
(assert-equal (simple-untranslate-in-term ''#\a) #\a)
(assert-equal (simple-untranslate-in-term '':key) :key)
(assert-equal (simple-untranslate-in-term ''t) t)
(assert-equal (simple-untranslate-in-term ''nil) nil)

;; Quoted SYMBOLS (other than t / nil / keywords) stay quoted:
(assert-equal (simple-untranslate-in-term ''foo) ''foo)

;; Quoted CONSes stay quoted (no descent into the constant):
(assert-equal (simple-untranslate-in-term ''(a b c)) ''(a b c))

;; Plain variables and atoms pass through:
(assert-equal (simple-untranslate-in-term 'x) 'x)

;; Arithmetic alias replacement:
(assert-equal (simple-untranslate-in-term '(binary-+ x y)) '(+ x y))
(assert-equal (simple-untranslate-in-term '(binary-* x y)) '(* x y))
(assert-equal (simple-untranslate-in-term '(unary-- x)) '(- x))
(assert-equal (simple-untranslate-in-term '(unary-/ x)) '(/ x))

;; Composition: unquoting happens inside the rewritten arithmetic call:
(assert-equal (simple-untranslate-in-term '(binary-+ '1 x)) '(+ 1 x))

;; Non-arithmetic calls just have their args walked:
(assert-equal (simple-untranslate-in-term '(foo '1 (binary-+ '2 x)))
              '(foo 1 (+ 2 x)))

;; LET walks each binding's value plus the body, leaves variable names alone:
(assert-equal (simple-untranslate-in-term '(let ((x (binary-+ y z)))
                                             (binary-+ '1 x)))
              '(let ((x (+ y z)))
                 (+ 1 x)))

;; LET with an IGNORE declaration: the declare passes through unchanged.
(assert-equal (simple-untranslate-in-term '(let ((x (binary-+ y z)))
                                             (declare (ignore x))
                                             '7))
              '(let ((x (+ y z)))
                 (declare (ignore x))
                 7))

;; LET*: bindings walked, body walked.
(assert-equal (simple-untranslate-in-term '(let* ((x (binary-+ y z))
                                                  (w (binary-* x '2)))
                                             (binary-+ x w)))
              '(let* ((x (+ y z))
                      (w (* x 2)))
                 (+ x w)))

;; MV-LET: value form walked, body walked.
(assert-equal (simple-untranslate-in-term '(mv-let (x y)
                                             (cons '3 (cons '4 'nil))
                                             (binary-+ x y)))
              '(mv-let (x y)
                 (cons 3 (cons 4 nil))
                 (+ x y)))

;; MV-LET with ignore: declare passes through, body walked.
(assert-equal (simple-untranslate-in-term '(mv-let (x y)
                                             (cons '3 (cons '4 'nil))
                                             (declare (ignore x))
                                             y))
              '(mv-let (x y)
                 (cons 3 (cons 4 nil))
                 (declare (ignore x))
                 y))
