; A lightweight book about the built-in-function position-equal-ac
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable position-equal-ac))

(defthm natp-of-position-equal-ac-under-iff
  (implies (natp acc)
           (iff (natp (position-equal-ac item lst acc))
                (member-equal item lst)))
  :hints (("Goal" :in-theory (enable member-equal position-equal-ac))))

(defthm integerp-of-position-equal-ac-under-iff
  (implies (integerp acc)
           (iff (integerp (position-equal-ac item lst acc))
                (member-equal item lst)))
  :hints (("Goal" :in-theory (enable member-equal position-equal-ac))))

(defthm position-equal-ac-under-iff
  (iff (position-equal-ac item lst acc)
       (member-equal item lst))
  :hints (("Goal" :in-theory (enable position-equal-ac))))

;improve?
;rename?
(defthm position-equal-ac-bound
  (implies (position-equal-ac item lst acc) ;item is present
           (< (position-equal-ac item lst acc)
              (+ acc (len lst))))
  :hints (("Goal" :in-theory (enable position-equal-ac))))

;improve?
;rename?
(defthm position-equal-ac-bound-special
  (implies (position-equal-ac item lst 0) ;item is present
           (< (position-equal-ac item lst 0)
              (len lst)))
  :hints (("Goal" :use (:instance position-equal-ac-bound (acc 0)))))

(defthm position-equal-ac-when-not-member-equal
  (implies (not (member-equal item lst))
           (equal (position-equal-ac item lst acc)
                  nil))
  :hints (("Goal" :in-theory (enable position-equal-ac))))

(defthm position-equal-ac-of-car-same
  (equal (position-equal-ac (car lst) lst acc)
         (if (consp lst) (fix acc) nil))
  :hints (("Goal" :in-theory (enable position-equal-ac))))

(local
 (defthm nth-of-position-equal-ac-same-helper
   (implies (member-equal item lst)
            (equal (nth (- (position-equal-ac item lst acc)
                           acc)
                        lst)
                   item))
   :hints (("Goal" :in-theory (enable position-equal-ac)))))

(defthm nth-of-position-equal-ac-of-0-same
  (equal (nth (position-equal-ac item lst 0) lst)
         (if (member-equal item lst)
             item
           (car lst) ; unusual case
           ))
  :hints (("Goal" :use (:instance nth-of-position-equal-ac-same-helper (acc 0))
           :in-theory (disable nth-of-position-equal-ac-same-helper))))
