; A lightweight book about the built-in-function position-equal-ac
;
; Copyright (C) 2015-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable position-equal-ac))

(defthm natp-of-position-equal-ac-under-iff
  (implies (natp acc)
           (iff (natp (position-equal-ac item lst acc))
                (member-equal item lst)))
  :hints (("Goal" :in-theory (enable member-equal position-equal-ac))))

(defthm integerp-of-position-equal-ac-under-iff
  (implies (natp acc)
           (iff (integerp (position-equal-ac item lst acc))
                (member-equal item lst)))
  :hints (("Goal" :in-theory (enable member-equal position-equal-ac))))

(defthm position-equal-ac-under-iff
  (implies acc
           (iff (position-equal-ac item lst acc)
                (member-equal item lst)))
  :hints (("Goal" :in-theory (enable position-equal-ac))))

;improve?
(defthm position-equal-ac-bound
  (implies (and (POSITION-EQUAL-ac item lst acc) ;item is present
                )
           (< (POSITION-EQUAL-ac item lst acc)
              (+ acc (len lst))))
  :hints (("Goal" :in-theory (enable position-equal-ac))))

;improve?
(defthm position-equal-ac-bound-special
  (implies (and (POSITION-EQUAL-ac item lst 0) ;item is present
                )
           (< (POSITION-EQUAL-ac item lst 0)
              (len lst)))
  :hints (("Goal" :use (:instance position-equal-ac-bound (acc 0)))))
