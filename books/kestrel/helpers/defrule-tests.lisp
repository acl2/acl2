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

;; This tries putting the body between a keyword arg and its associated value, which
;; is not supported by defrule.
;; This is interpreted as having T for the body and (equal (car (cons x y)) x) as the :otf-flg.
(must-fail (defrule body-between-arg-and-val :otf-flg (equal (car (cons x y)) x) t))

;; Variant of the above that ensures the failure is not just due to T being
;; illegal for the body of a rewrite rule.
(must-fail (defrule body-between-arg-and-val2 :otf-flg (equal (car (cons x y)) x) t :rule-classes nil))
