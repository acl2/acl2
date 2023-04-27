; Lists of field elements
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "fep") ; reduce?

;; Recognize a true list of field elements.
(defund fe-listp (elems prime)
  (declare (xargs :guard (primep prime)))
  (if (atom elems)
      (equal elems nil)
    (and (fep (first elems) prime)
         (fe-listp (rest elems) prime))))

;for acl2, not Axe
(defthm fep-when-fe-listp-and-member-equal
  (implies (and (syntaxp (acl2::variablep x)) ;for now, we only generate the fe-listp assumptions for vars
                (fe-listp free p)
                (acl2::member-equal x free))
           (fep x p))
  :hints (("Goal" :in-theory (enable fe-listp))))

(defthm fep-of-car-when-fe-listp
  (implies (fe-listp elems prime)
           (equal (fep (car elems) prime)
                  (consp elems)))
  :hints (("Goal" :in-theory (enable fe-listp))))

(defthm fe-listp-forward-to-true-listp
  (implies (fe-listp elems prime)
           (true-listp elems))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fe-listp))))

;; Could disable but the free var makes this fairly cheap
(defthm true-listp-when-fe-listp
  (implies (fe-listp elems prime)
           (true-listp elems)))

(defthm fe-listp-when-not-consp
  (implies (not (consp elems))
           (equal (fe-listp elems prime)
                  (null elems)))
  :hints (("Goal" :in-theory (enable fe-listp))))

(defthm fe-listp-of-cons
  (equal (fe-listp (cons elem elems) prime)
         (and (fep elem prime)
              (fe-listp elems prime)))
  :hints (("Goal" :in-theory (enable fe-listp))))
