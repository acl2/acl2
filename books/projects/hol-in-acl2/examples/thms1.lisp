; Copyright (C) 2025, Matt Kaufmann and Konrad Slind
; Written by Matt Kaufmann and Konrad Slind
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book gives an example of a theorem that can be proved about translations
; of HOL functions.  It is essentially superseded by the corresponding defhol
; and defgoal forms in ex1.lisp.

(in-package "ZF")

(include-book "ex1")

(in-theory (disable hol::hp-comma))

(defthm fst-comma
  (implies
   (and (hpp x hta)
        (equal (hp-type x) (typ a))
        (hpp y hta)
        (equal (hp-type y) (typ b))
        (alist-subsetp (hol::ex1$hta) hta)
        (force (hol::ex1$prop)))
   (equal (hap*
           (hol::fst (typ (:arrow* (:hash a b) a)))
           (hap* (hol::comma (typ (:arrow* a b (:hash a b)))) x y))
          x)))
