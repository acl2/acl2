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
 ;;            (equal (nth n (uchar-list-from-integer-list x))
 ;;                   (uchar-from-integer (nth n x)))))
 (defthm uchar-list-fix-of-update-nth
   (implies (and (natp n) (< n (len list)))
            (equal (uchar-list-fix (update-nth n value list))
                   (update-nth n (uchar-fix value)
                               (uchar-list-fix list)))))
 (defthm nth-of-uchar-array->elements-becomes-uchar-array-read
   (implies (and (uchar-arrayp array)
                 (natp x)
                 (sint-integerp x)
                 (> (len (uchar-array->elements array))
                    x))
            (equal (nth x (uchar-array->elements array))
                   (uchar-array-read array (sint-from-integer x)))))
 ;; (defthm uchar-array->elements-of-uchar-array-integer-write
 ;;   (implies
 ;;    (and (uchar-arrayp array)
 ;;         (natp index)
 ;;         (< index
 ;;            (len (uchar-array->elements array))))
 ;;    (equal
 ;;     (uchar-array->elements (uchar-array-integer-write array index element))
 ;;     (update-nth index (uchar-fix element)
 ;;                 (uchar-array->elements array))))
 ;;   )
 ;; (defthmd uchar-array-of-of-update-nth-becomes-uchar-array-integer-write
 ;;   (implies (and (uchar-listp x)
 ;;                 (natp n)
 ;;                 (< n (len x)))
 ;;            (equal (uchar-array-of (update-nth n y x))
 ;;                   (uchar-array-integer-write (uchar-array-of x)
 ;;                                         n y)))
 ;;   )
 ;; (theory-invariant (incompatible (:rewrite update-nth->uchar-array-integer-write)
 ;;                                 (:definition uchar-array-integer-write)))
 (defthm uchar-array-of-of-update-nth-becomes-uchar-array-write
   (implies (and (uchar-listp x)
                 (natp n)
                 (< n (len x))
                 (sint-integerp n))
            (equal (uchar-array-of (update-nth n y x))
                   (uchar-array-write (uchar-array-of x)
                                              (sint-from-integer n)
                                              y)))
   )
 ;; (defthm
 ;;   len-of-uchar-array->elements-of-uchar-array-integer-write
 ;;   (equal (len (uchar-array->elements (uchar-array-integer-write array i x)))
 ;;          (len (uchar-array->elements array)))
 ;;   )
 ;; (defthm
 ;;   len-of-uchar-array->elements-of-uchar-array-write
 ;;   (equal
 ;;    (len (uchar-array->elements (uchar-array-write array i x)))
 ;;    (len (uchar-array->elements array)))
 ;;   )

 (defthm uchar-array->elements-of-uchar-array-of
  (equal (uchar-array->elements (uchar-array-of elements))
         (if (consp elements)
             (uchar-list-fix elements)
           (list (uchar-from-integer 0))))))
