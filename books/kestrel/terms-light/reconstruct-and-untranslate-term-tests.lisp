; Tests for reconstruct-and-untranslate-term
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "reconstruct-and-untranslate-term")
(include-book "std/testing/assert-equal" :dir :system)

;; These tests mirror the "todo: untranslate" expectations in
;; reconstruct-lets-in-term-tests.lisp, with the readability pass applied.

;; :trans (let ((x (+ y z))) (+ 1 x))
(assert-equal (reconstruct-and-untranslate-term
               '((lambda (x) (binary-+ '1 x)) (binary-+ y z)))
              '(let ((x (+ y z))) (+ 1 x)))

;; :trans (let ((x (+ y z))) (declare (ignore x)) 7)
(assert-equal (reconstruct-and-untranslate-term
               '((lambda (x) '7) (hide (binary-+ y z))))
              '(let ((x (+ y z)))
                 (declare (ignore x))
                 7))

;; Trivial formal + the only let binding (corresponds to (let ((x z)) (+ x 1)) in surface):
(assert-equal (reconstruct-and-untranslate-term
               '((lambda (x y) (binary-+ x '1)) z y))
              '(let ((x z)) (+ x 1)))

;; :trans (mv-let (x y) (mv 3 4) (+ x y))
(assert-equal (reconstruct-and-untranslate-term
               '((lambda (mv)
                   ((lambda (x y) (binary-+ x y))
                    (mv-nth '0 mv)
                    (mv-nth '1 mv)))
                 (cons '3 (cons '4 'nil))))
              '(mv-let (x y)
                 (cons 3 (cons 4 nil)) ; the MV got lost — restore via restore-mv-lets-in-term
                 (+ x y)))

;; :trans (mv-let (x y) (mv 3 4) (declare (ignore x)) y)
(assert-equal (reconstruct-and-untranslate-term
               '((lambda (mv)
                   ((lambda (x y) y)
                    (hide (mv-nth '0 mv))
                    (mv-nth '1 mv)))
                 (cons '3 (cons '4 'nil))))
              '(mv-let (x y) (cons 3 (cons 4 nil)) (declare (ignore x)) y))

;; :trans (mv-let (x y) (mv 3 4) (let ((z (+ x y))) (* 2 z)))
(assert-equal (reconstruct-and-untranslate-term
               '((lambda (mv)
                   ((lambda (x y)
                      ((lambda (z) (binary-* '2 z))
                       (binary-+ x y)))
                    (mv-nth '0 mv)
                    (mv-nth '1 mv)))
                 (cons '3 (cons '4 'nil))))
              '(mv-let (x y)
                 (cons 3 (cons 4 nil))
                 (let ((z (+ x y))) (* 2 z))))

;; :trans (mv-let (x y) (let ((z 3)) (mv z 4)) (+ x y))
(assert-equal (reconstruct-and-untranslate-term
               '((lambda (mv)
                   ((lambda (x y) (binary-+ x y))
                    (mv-nth '0 mv)
                    (mv-nth '1 mv)))
                 ((lambda (z) (cons z (cons '4 'nil)))
                  '3)))
              '(mv-let (x y)
                 (let ((z 3)) (cons z (cons 4 nil)))
                 (+ x y)))
