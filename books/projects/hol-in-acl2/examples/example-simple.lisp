; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "HOL")

(include-book "../acl2/theories")

; Example: Suppose the current HOL theory is THY1.

; val C = ⊢ ∀(f :α -> β -> γ) (x :β) (y :α). flip f x y = f y x: thmw

; Note that the type of flip is determined by taking the types of f, x, and y
; to the type of (f y x), hence:
; (α -> β -> γ) -> β -> α -> γ.

; The following is equivalent to:
; (open-theory simple :hta-term (hta0))
(open-theory simple)

(defhol
  :fns ((c (:arrow* (:arrow* a b c) b a c)))
  :defs ((:forall ((f (:arrow* a b c)) (x b) (y a))
           (equal (hap* (c (typ (:arrow* (:arrow* a b c) b a c))) f x y)
                  (hap* f y x)))))

(close-theory)

(set-enforce-redundancy t)

(defthm c$type
  (implies (force (simple$prop))
           (and (hpp (c (typ (:arrow* (:arrow* a b c) b a c)))
                     (simple$hta))
                (equal (hp-type (c (typ (:arrow* (:arrow* a b c) b a c))))
                       (typ (:arrow* (:arrow* a b c) b a c))))))

(defthm hol{c}
  (implies (and (hpp f hta)
                (equal (hp-type f) (typ (:arrow* a b c)))
                (hpp x hta)
                (equal (hp-type x) (typ b))
                (hpp y hta)
                (equal (hp-type y) (typ a))
                (alist-subsetp (simple$hta) hta)
                (force (simple$prop)))
           (equal (hap* (c (typ (:arrow* (:arrow* a b c) b a c))) f x y)
                  (hap* f y x))))
