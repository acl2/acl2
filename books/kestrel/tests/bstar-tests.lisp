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
