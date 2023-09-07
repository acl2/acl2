; Some tests regarding hints
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;; fails, because of the (in-theory nil)
(must-fail
 (deftest
   (in-theory nil)
   (defthm my-car-cons
     (equal (car (cons x y)) x))))

;; works, despite the (in-theory nil)
(deftest
  (in-theory nil)
  (defthm my-car-cons
    (equal (car (cons x y)) x)
    :hints (("Goal" :in-theory (enable car-cons)))))

;; works because the empty Goal hint does not shadow the one below
(deftest
  (in-theory nil)
  (defthm my-car-cons
    (equal (car (cons x y)) x)
    :hints (("Goal")
            ("Goal" :in-theory (enable car-cons)))))

;; shows that multiple empty hints are ignored
(deftest
  (in-theory nil)
  (defthm my-car-cons
   (equal (car (cons x y)) x)
   :hints (("Goal")
           ("Goal")
           ("Goal")
           ("Goal" :in-theory (enable car-cons)))))

;; Fails because the :in-theory hint is hidden by the :use hint.
(must-fail
 (deftest
   (in-theory nil)
   (defthm my-car-cons
     (equal (car (cons x y)) x)
     :hints (("Goal" :use binary-append)
             ("Goal" :in-theory (enable car-cons))))))

;; I thought this would fail, because the :no-op hint would shadow the later
;; hint, but see what :doc hints-and-the-waterfall says about when the
;; "settled-down" process applies.
;; Indeed, if you do (set-gag-mode nil), you see two hint messages get
;; printed.
(deftest
  (in-theory nil)
  (defthm my-car-cons
    (equal (car (cons x y)) x)
    :hints (("Goal" :no-op t)
            ("Goal" :in-theory (enable car-cons)))))
