; Some tests of b*
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; normal case
(defun test-hyphen-binder (x)
  (b* ((- (cw "hi")))
    x))

;; more than one form after the binder (implicit progn)
(defun test-hyphen-binder2 (x)
  (b* ((- (cw "hi") (cw "there") ))
    x))

;; no forms after the binder.  apparently, this is legal!
(defun test-hyphen-binder0 (x)
  (b* ((- ))
    x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; normal case
(defun test-var-binder (x)
  (b* ((y x))
    y))

;; Illegal: more than one form given to bind Y.
(must-fail
 (defun test-var-binder2 (x)
  (b* ((y 3 x))
    y)))

;; Illegal: no forms given to bind Y.
(must-fail
 (defun test-var-binder0 (x)
   (b* ((y))
     y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; normal case
(defun test-mv-binder (x)
  (b* (((mv a b) (mv 3 x)))
    (list a b)))

;; Illegal: more than one form after the binder (implicit progn).
;; TODO: Should this be allowed?
(must-fail
 (defun test-mv-binder2 (x)
  (b* (((mv a b) (cw "hi") (mv 3 x)))
    (list a b))))

;; Illegal: no term given to bind A and B.
(must-fail
 (defun test-mv-binder0 (x)
  (b* (((mv a b)))
    (list a b))))

;; Illegal: only one var bound by the mv.
;; TODO: Should this be allowed (just use a let)?
(must-fail
 (defun test-mv-binder-single-var (x)
   (b* (((mv a) 3))
     (list a x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The use of & causes the CW to be completely ignored.  No printing is done
;; when this is called.
(defun test-&-binder (x)
  (b* ((& (cw "hello")))
    x))

;; Variant with no expressions
(defun test-&-binder0 (x)
  (b* ((&))
    x))

;; Variant with more than 1 expression.  Still no printing is done.
(defun test-&-binder2 (x)
  (b* ((& (cw "hello") (cw "world")))
    x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The use of ?!y causes the CW to be completely ignored.  No printing is done
;; when this is called.
(defun test-?!y-binder (x)
  (b* ((?!y (cw "hello")))
    x))

;; Variant with no expressions
;; Illegal! TODO: Treat this like & ?
(must-fail
 (defun test-?!y-binder0 (x)
   (b* ((?!y))
     x)))

;; Variant with more than 1 expression.
;; Illegal! TODO: Treat this like & ?
(must-fail
 (defun test-?!y-binder2 (x)
   (b* ((?!y (cw "hello") (cw "world")))
     x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The use of ?! causes the CW to be completely ignored.  No printing is done
;; when this is called.
(defun test-?!-binder (x)
  (b* ((?! (cw "hello")))
    x))

;; Variant with no expressions
;; Illegal! TODO: Treat this like & ?
(must-fail
 (defun test-?!-binder0 (x)
   (b* ((?!))
     x)))

;; Variant with more than 1 expression.
;; Illegal! TODO: Treat this like & ?
(must-fail
 (defun test-?!-binder2 (x)
   (b* ((?! (cw "hello") (cw "world")))
     x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Typical case
(defun test-list-binder (x)
  (b* (((list a b c) x))
    (+ a b c)))

(defun test-list-binder-no-vars (x)
  (b* (((list) x))
    x))

(defun test-list-binder-1-var (x)
  (b* (((list a) x))
    a))

;; Illegal, no binding expression
(must-fail
 (defun test-list-binder0 (x)
  (b* (((list a)))
    a)))

;; Illegal, more than 1 binding expression:
(must-fail
 (defun test-list-binder2 (x)
  (b* (((list a) (cw "hi") x))
    a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Typical case
(defun test-er-binder (x state)
  (declare (xargs :stobjs state))
  (b* (((er a) (mv nil x state)))
    ;; must return an error triple, since the ER binder creates a branch that does:
    (mv nil (cons 3 a) state)))

;; Alternate form (explicit error value given):
(defun test-er-binder-with-iferr (x state)
  (declare (xargs :stobjs state))
  (b* (((er a :iferr 7) (mv nil x state)))
    ;; must return an error triple, since the ER binder creates a branch that does:
    (mv nil (cons 3 a) state)))

;; Illegal: no binding expressions given
(must-fail
 (defun test-er-binder0 (x state)
   (declare (xargs :stobjs state))
   (b* (((er a)))
     (mv nil (cons 3 a) state))))

;; Illegal: more than 1 expression given:
(must-fail
 (defun test-er-binder2 (x state)
   (declare (xargs :stobjs state))
   (b* (((er a) (mv nil x state) (mv nil x state)))
     (mv nil (cons 3 a) state))))

;; Illegal: no variable given
(must-fail
 (defun test-er-binder-n-vars (x state)
   (declare (xargs :stobjs state))
   (b* (((er) (mv nil x state)))
     (mv nil (cons 3 a) state))))

;; Illegal: more than 1 variable given
(must-fail
 (defun test-er-binder-n-vars (x state)
   (declare (xargs :stobjs state))
   (b* (((er a b) (mv nil x state)))
     (mv nil (cons a b) state))))
