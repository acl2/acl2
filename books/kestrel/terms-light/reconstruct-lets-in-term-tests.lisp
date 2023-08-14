; Tests for reconstruct-lets-in-term
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add more tests

(include-book "reconstruct-lets-in-term")
(include-book "std/testing/assert-equal" :dir :system)

;; :trans (let ((x (+ y z))) (+ 1 x))
(assert-equal (reconstruct-lets-in-term '((lambda (x) (binary-+ '1 x)) (binary-+ y z)))
              ;; todo: untranslate:
              '(let ((x (binary-+ y z))) (binary-+ '1 x)))

;; A test with an ignored var.
;; ;; :trans (let ((x (+ y z))) (declare (ignore x)) 7)
(assert-equal (reconstruct-lets-in-term '((lambda (x) '7) (hide (binary-+ y z))))
              ;; todo: untranslate:
              '(let ((x (binary-+ y z)))
                 (declare (ignore x))
                 '7))

;; A test with a trivial formal that is also ignored (should not get an ignore
;; declaration for y since y is a trivial lambda formal and will not even be
;; bound in the let):
(assert-equal (reconstruct-lets-in-term '((lambda (x y) (binary-+ x '1)) z y))
              ;; todo: untranslate:
              '(let ((x z)) (binary-+ x '1)))


;; A test with just an mv-let
;; :trans (mv-let (x y) (mv 3 4) (+ x y))
(assert-equal (reconstruct-lets-in-term '((lambda (mv)
                                            ((lambda (x y) (binary-+ x y))
                                             (mv-nth '0 mv)
                                             (mv-nth '1 mv)))
                                          (cons '3 (cons '4 'nil))))
              ;; todo: untranslate:
              '(mv-let (x y)
                 (cons '3 (cons '4 'nil)) ; todo: the MV got lost.  we could restore it since we know 2 values are needed
                 (binary-+ x y)))

;; A test with an mv-let with an ignored var:
;; :trans (mv-let (x y) (mv 3 4) (declare (ignore x)) y)
(assert-equal (reconstruct-lets-in-term '((lambda (mv)
                                            ((lambda (x y) y)
                                             (hide (mv-nth '0 mv))
                                             (mv-nth '1 mv)))
                                          (cons '3 (cons '4 'nil))))
              '(mv-let (x y) (cons '3 (cons '4 'nil)) (declare (ignore x)) y))

;; A test with an mv-let and a let (the let is in the body of the mv-let):
;; :trans (mv-let (x y) (mv 3 4) (let ((z (+ x y))) (* 2 z)))
(assert-equal (reconstruct-lets-in-term '((lambda (mv)
                                            ((lambda (x y)
                                               ((lambda (z) (binary-* '2 z))
                                                (binary-+ x y)))
                                             (mv-nth '0 mv)
                                             (mv-nth '1 mv)))
                                          (cons '3 (cons '4 'nil))))
              ;; todo: untranslate:
              '(mv-let (x y)
                 (cons '3 (cons '4 'nil)) ; todo: the MV got lost.  we could restore it since we know 2 values are needed
                 (let ((z (binary-+ x y))) (binary-* '2 z))))

;; Another test with an mv-let and a let (the let is in the "term" of the mv-let):
;; :trans (mv-let (x y) (let ((z 3)) (mv z 4)) (+ x y))
(assert-equal (reconstruct-lets-in-term '((lambda (mv)
                                            ((lambda (x y) (binary-+ x y))
                                             (mv-nth '0 mv)
                                             (mv-nth '1 mv)))
                                          ((lambda (z) (cons z (cons '4 'nil)))
                                           '3)))
              ;; todo: untranslate:
              '(mv-let (x y) (let ((z '3)) (cons z (cons '4 'nil))) (binary-+ x y)))
