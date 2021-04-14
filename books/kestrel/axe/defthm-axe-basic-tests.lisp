; Tests of defthm-axe-basic
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defthm-axe-basic")
(include-book "kestrel/axe/rules-in-rule-lists" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defthm-axe-basic test
    (equal (car (cons x y))
           x)
    :rules (car-cons equal-same)))

;; Test :rule-lists
(deftest
  (defthm-axe-basic test
    (equal (car (cons x y))
           x)
    :rule-lists ((car-cons equal-same))))

(deftest
  (must-fail
   (defthm-axe-basic test
     (equal (car (cons x y))
            y ;; should be x
            )
     :rules (car-cons equal-same))))

;; Correct theorem but no rules given to prove it
(deftest
  (must-fail
   (defthm-axe-basic test
     (equal (car (cons x y))
            x))))

;; Test the use of a 0-ary function to indicate a list of rules.
(deftest
  (defun rules1 ()
    '(car-cons equal-same))

  (defthm-axe-basic test
    (equal (car (cons x y))
           x)
    :rules ((rules1))))


(deftest
  (defun rules1 ()
    '(car-cons equal-same))

  (defthm-axe-basic test
    (equal (car (cons x y))
           x)
    :rules ((rules1))))

(deftest
  (defun rules1 ()
    '(car-cons equal-same))

  (defthm-axe-basic test
    (equal (car (cons x y))
           x)
    :rule-lists (((rules1)))))

;; Test :eval
(deftest
  (defthm-axe-basic test
    (:eval '(equal (car (cons x y))
                   x))
    :rules (car-cons equal-same)))

;; Test :eval
(deftest
  (defun create-form ()
    '(equal (car (cons x y))
                   x))
  (defthm-axe-basic test
    (:eval (create-form))
    :rules (car-cons equal-same)))
