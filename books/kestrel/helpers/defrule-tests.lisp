; Tests of defrule
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; As of Jan 2026, the documentation for defrule does not fully describe how
;; it works, so this file tests various aspects of it.

(include-book "std/util/defrule" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-fail-with-hard-error" :dir :system)

;; A simple test
(defrule test-basic (equal (car (cons x y)) x))

;; Test :hints (not actually needed for this theorem):
(defrule test-hints (equal (car (cons x y)) x) :hints (("Goal" :in-theory (enable append))))

;; defrule DOES seem to support :otf-flg
(defrule test-otf-flg (equal (car (cons x y)) x) :otf-flg t)

;; defrule can't have 2 bodies
(must-fail-with-hard-error (defrule two-bodies (equal (car (cons x y)) x) (equal (car (cons x2 y)) 2)))

;; body can't be a keyword
(must-fail-with-hard-error (defrule keyword :key :rule-classes nil))

;; it works if we quote the keyword body:
(defrule keyword2 ':key :rule-classes nil)

;; TODO: Uncomment and update these 2 if/when :otf-flg is restricted to booleans.

;; ;; Try putting the body between a keyword arg and its associated value:
;; ;wow!  this works.
;; ; This uses t as the body and (equal (car (cons x y)) x) as the :of-flg !
;; ;; TODO: This may soon be an error
;; (defrule body-between-arg-and-val :otf-flg (equal (car (cons x y)) x) t :rule-classes nil)

;; ;; fails but only due to rule-classes
;; (must-fail (defrule body-between-arg-and-val2 :otf-flg (equal (car (cons x y)) x) t))
