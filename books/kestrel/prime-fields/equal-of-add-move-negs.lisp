; Prime fields library: Non-bind-free rules to move negated addends
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; NOTE: The rules in this file may be subsumed by the bind-free rules and in
;; fact may interfere with them.

(include-book "prime-fields")
(local (include-book "prime-fields-rules"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "equal-of-add-cancel"))

;todo: more like this
(defthm equal-of-0-and-add-of-add-of-neg
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (posp p))
           (equal (equal 0 (add x (add y (neg z p) p) p))
                  (equal (mod z p)
                         (add x y p))))
  :hints (("Goal" :use (:instance equal-of-add-and-add-cancel-1-gen
                                  (x z)
                                  (y (add x (add y (neg z p) p) p))
                                  (z 0))
           :in-theory (disable equal-of-add-and-add-cancel-1-gen
                               EQUAL-OF-ADD-CANCEL-1))))

(defthm equal-of-0-and-add-of-add-of-add-of-neg
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp w)
                (posp p))
           (equal (equal 0 (add x (add y (add w (neg z p) p) p) p))
                  (equal (mod z p)
                         (add x (add y w p) p))))
  :hints (("Goal" :use (:instance equal-of-add-and-add-cancel-1-gen
                                  (x z)
                                  (y (add x (add y (add w (neg z p) p) p) p))
                                  (z 0))
           :in-theory (disable equal-of-add-and-add-cancel-1-gen
                               EQUAL-OF-ADD-CANCEL-1))))

(defthm equal-of-0-and-add-of-add-of-add-of-add-of-neg
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp w)
                (integerp v)
                (posp p))
           (equal (equal 0 (add x (add y (add w (add v (neg z p) p) p) p) p))
                  (equal (mod z p)
                         (add x (add y (add w v p) p) p))))
  :hints (("Goal" :use (:instance equal-of-add-and-add-cancel-1-gen
                                  (x z)
                                  (y (add x (add y (add w (add v (neg z p) p) p) p) p))
                                  (z 0))
           :in-theory (disable equal-of-add-and-add-cancel-1-gen
                               EQUAL-OF-ADD-CANCEL-1))))

(defthm move-neg-rule-3
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
                (integerp v)
                (integerp w)
                (posp p))
           (equal (equal (add x (add y (add (neg z p) w p) p) p)
                         v)
                  (and (fep v p)
                       (equal (add x (add y w p) p)
                              (add v z p)))))
  :hints (("Goal" :use (:instance equal-of-add-and-add-cancel-1-gen
                                  (x z)
                                  (y (add x (add y (add (neg z p) w p) p) p))
                                  (z v))
           :in-theory (e/d (equal-of-<-and-fep) (equal-of-add-and-add-cancel-1-gen
                                                 EQUAL-OF-ADD-CANCEL-1)))))
