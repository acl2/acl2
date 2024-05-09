; Some tests of defrule
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

(must-fail (defrule d1 (equal x x))) ; not a suitable rewrite rule

;;ok
(deftest (defrule d1 (equal x x) :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; test with e/d with no items
(deftest
  ;; No encapsulate generated
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :e/d ()))

;; test with e/d with 1 item
(deftest
  ;; Defrule puts in (local (in-theory (e/d* nil nil (natp))))).
  ;; Apparently defrule always does the :enables, then the :disables, then the :e/d.
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :e/d ((natp))))

;; test with e/d with more than 2 items
(deftest
  ;; Defule puts in (local (in-theory (e/d* nil nil (natp) (posp) (expt))))
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :e/d ((natp) (posp) (expt))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test with :enable and :disable (:enable comes first)
(deftest
  ;; defrule generates a (local (in-theory (e/d* (posp) (natp))))
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :enable posp
    :disable natp))

;; Test with :enable and :disable (:disable comes first)
;; The local in-theory is identical to the above.
(deftest
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :disable natp
    :enable posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest
  ;; Test with :enable and :e/d (:enable comes first)
  ;; Generates (local (in-theory (e/d* (posp) nil (natp) (expt))))
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :enable posp
    :e/d ((natp) (expt))))

(deftest
  ;; Test with :enable and :e/d (:e/d comes first)
  ;; The local in-theory is identical to the above.
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :e/d ((natp) (expt))
    :enable posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftest
  ;; Test with :disable and :e/d (:disable comes first)
  ;; Generates (local (in-theory (e/d* nil (posp) (natp) (expt))))
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :disable posp
    :e/d ((natp) (expt))))

(deftest
  ;; Test with :disable and :e/d (:e/d comes first)
  ;; The local in-theory is identical to the above.
  (defrule my-car-cons
    (equal (car (cons x y)) x)
    :e/d ((natp) (expt))
    :disable posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Fails due to multiple :enables
(must-fail
 (defrule my-car-cons
   (equal (car (cons x y)) x)
   :enable natp
   :enable posp)
 :expected :hard)

;; Fails due to multiple :disables
(must-fail
 (defrule my-car-cons
   (equal (car (cons x y)) x)
   :disable natp
   :disable posp)
 :expected :hard)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simple test with :instructions
(defrule d1
  (equal x x)
  :rule-classes nil
  :instructions (:s))

;; Can't have both :hints and :instructions
(must-fail
 (defrule d2
   (equal x x)
   :rule-classes nil
   :hints (("Goal" :in-theory (enable natp)))
   :instructions (:s)))
