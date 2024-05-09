; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is based on the "Test :in-theory" part of test2.lisp, but using
; rulesets instead.

(in-package "ACL2")

(include-book "tools/rulesets" :dir :system)

; Test that the third list from an e/d call isn't dropped.
(defthmd app-assoc-1
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d (append nth)
                                  (car-cons)
                                  (car-cons)))))

; Same as above, but keys should be :enable and :disable, not :enable* or
; :disable*.
(defthmd app-assoc-2
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d* (append nth)
                                   (car-cons)
                                   (car-cons)))))

(def-ruleset r1 '(append car-cons))

(encapsulate
  ()

  (local (in-theory (disable* r1)))

  (defthmd app-assoc-3
    (equal (append (append x y) z)
           (append x y z))
    :hints (("Goal" :in-theory (enable* r1 nth)))))

(defthmd app-assoc-4
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d* (nth app-assoc-3)
                                   (nth r1)))))

(in-theory (disable* r1))

(deftheory t1 '(append car-cons))

(defthmd app-assoc-5
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d* (nth app-assoc-3)
                                   (t1)))))


(defthmd app-assoc-6
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (enable* t1))))

(defthmd app-assoc-7
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (enable t1))))
