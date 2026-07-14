; Tests of the tool in def-array-support.lisp
;
; Copyright (C) 2023-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "def-array-support")
(include-book "std/testing/must-be-redundant" :dir :system)

(def-array-support uchar)

;; Ensure the call to def-array-support generated the expected stuff:
(acl2::must-be-redundant
 ;; (defthm nth-of-uchar-list-from-integer-list
 ;;   (implies (and (natp n) (< n (len x)))
 ;;            (equal (nth n (c::uchar-list-from-integer-list x))
 ;;                   (c::uchar-from-integer (nth n x)))))
 (defthm uchar-list-fix-of-update-nth
   (implies (and (natp n) (< n (len list)))
            (equal (c::uchar-list-fix (update-nth n value list))
                   (update-nth n (c::uchar-fix value)
                               (c::uchar-list-fix list)))))
 (defthm nth-of-uchar-array->elements-becomes-uchar-array-read
   (implies (and (c::uchar-arrayp array)
                 (natp x)
                 (c::sint-integerp x)
                 (> (len (c::uchar-array->elements array))
                    x))
            (equal (nth x (c::uchar-array->elements array))
                   (c::uchar-array-read array (c::sint-from-integer x)))))
 ;; (defthm uchar-array->elements-of-uchar-array-integer-write
 ;;   (implies
 ;;    (and (c::uchar-arrayp array)
 ;;         (natp index)
 ;;         (< index
 ;;            (len (c::uchar-array->elements array))))
 ;;    (equal
 ;;     (c::uchar-array->elements (c::uchar-array-integer-write array index element))
 ;;     (update-nth index (c::uchar-fix element)
 ;;                 (c::uchar-array->elements array))))
 ;;   )
 ;; (defthmd uchar-array-of-of-update-nth-becomes-uchar-array-integer-write
 ;;   (implies (and (c::uchar-listp x)
 ;;                 (natp n)
 ;;                 (< n (len x)))
 ;;            (equal (c::uchar-array-of (update-nth n y x))
 ;;                   (c::uchar-array-integer-write (c::uchar-array-of x)
 ;;                                         n y)))
 ;;   )
 ;; (theory-invariant (incompatible (:rewrite update-nth->uchar-array-integer-write)
 ;;                                 (:definition c::uchar-array-integer-write)))
 (defthm uchar-array-of-of-update-nth-becomes-uchar-array-write
   (implies (and (c::uchar-listp x)
                 (natp n)
                 (< n (len x))
                 (c::sint-integerp n))
            (equal (c::uchar-array-of (update-nth n y x))
                   (c::uchar-array-write (c::uchar-array-of x)
                                              (c::sint-from-integer n)
                                              y)))
   )
 ;; (defthm
 ;;   len-of-uchar-array->elements-of-uchar-array-integer-write
 ;;   (equal (len (c::uchar-array->elements (c::uchar-array-integer-write array i x)))
 ;;          (len (c::uchar-array->elements array)))
 ;;   )
 ;; (defthm
 ;;   len-of-uchar-array->elements-of-uchar-array-write
 ;;   (equal
 ;;    (len (c::uchar-array->elements (c::uchar-array-write array i x)))
 ;;    (len (c::uchar-array->elements array)))
 ;;   )

 (defthm uchar-array->elements-of-uchar-array-of
  (equal (c::uchar-array->elements (c::uchar-array-of elements))
         (if (consp elements)
             (c::uchar-list-fix elements)
           (list (c::uchar-from-integer 0))))))
