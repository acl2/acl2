; More rules about all-equal$
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This file mixes all-equal$ with other non-built-in functions

(include-book "all-equal-dollar")
(include-book "repeat")

(defthm all-equal$-of-repeat
  (all-equal$ item (repeat n item))
  :hints (("Goal" :in-theory (e/d (repeat) (;cons-onto-repeat ;looped
                                            )))))

;gross proof?
(defthmd all-equal$-of-car-same-becomes-equal-of-repeat
  (implies (true-listp lst)
           (equal (all-equal$ (car lst) lst)
                  (equal lst (repeat (len lst) (car lst)))))
  :hints (("Goal" :in-theory (e/d (repeat)
                                  ( ;DAGIFY-INSIDE-HIDE-META-RULE
                                   )))))

(defthmd all-equal$-when-true-listp
  (implies (true-listp k2)
           (equal (all-equal$ k1 k2)
                  (equal k2 (repeat (len k2) k1))))
  :hints (("Goal" :in-theory (enable all-equal$ repeat))))

(defthm equal-of-repeat-of-len-same
  (equal (equal x (repeat (len x) item))
         (and (true-listp x)
              (all-equal$ item x)))
  :hints (("Goal" :in-theory (enable true-listp))))

(theory-invariant (incompatible (:rewrite all-equal$-when-true-listp) (:rewrite equal-of-repeat-of-len-same)))

(defthm nthcdr-when-all-equal$
  (implies (and (all-equal$ x lst)
                (natp n)
                (< n (len lst))
                (true-listp lst))
           (equal (nthcdr n lst)
                  (repeat (- (len lst) n) x)))
  :hints (("Goal" :in-theory (e/d (all-equal$-when-true-listp) (equal-of-repeat-of-len-same)))))
