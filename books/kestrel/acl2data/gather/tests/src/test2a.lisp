; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is based on the "Test :in-theory" part of test2.lisp, but using
; rulesets instead.

(in-package "ACL2")

(include-book "tools/rulesets" :dir :system)

(in-theory (disable* append car-cons))

(defthm app-assoc-rewrite
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (enable* append car-cons nth))))

(defthm app-assoc-backwards
  (equal (append x y z)
         (append (append x y) z))
  :hints (("Goal" :in-theory (enable* append car-cons nth))))

(defthm app-assoc-1
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d* (append car-cons nth)
                                   (app-assoc-backwards))))
  :rule-classes nil)

(defthm app-assoc-2
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d* nil
                                   (app-assoc-backwards))))
  :rule-classes nil)

(defthm app-assoc-3
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d* nil
                                   (nth app-assoc-backwards))))
  :rule-classes nil)

(in-theory (disable* app-assoc-backwards app-assoc-rewrite))

(defthm app-assoc-4
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d* (nth app-assoc-rewrite)
                                   nil)))
  :rule-classes nil)

(def-ruleset r1 '(nth app-assoc-rewrite))

(defthm app-assoc-4a
  (equal (append (append x y) z)
         (append x y z))
  :hints (("Goal" :in-theory (e/d* (r1)
                                   nil)))
  :rule-classes nil)
