; More tools to compute DAG sizes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "all-dargp")
(include-book "largest-non-quotep")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

(local (in-theory (disable natp)))

(local (in-theory (enable <=-of-0-when-0-natp
                          acl2-numberp-when-natp
                          integerp-when-natp)))

;; Defines size-arrayp:
(def-typed-acl2-array size-arrayp (natp val) :default-satisfies-predp nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Add to ACC the sizes of all of the DARGS (for a nodenum darg, look up its
;; size in the array, for a quotep darg use a size of 1).
;; See also add-darg-sizes.
(defund add-darg-sizes-with-name (dargs size-array-name size-array acc)
  (declare (xargs :guard (and (true-listp dargs)
                              (all-dargp dargs)
                              (size-arrayp size-array-name size-array (+ 1 (largest-non-quotep dargs)))
                              (natp acc))
                  :split-types t)
           (type (integer 0 *) acc))
  (if (endp dargs)
      acc
    (let ((darg (first dargs)))
      (add-darg-sizes-with-name (rest dargs)
                                size-array-name
                                size-array
                                (+ (if (consp darg) ;check for a quotep, which we say has size 1
                                       1
                                     ;; dargs is a nodenum, so look up its size:
                                     (the (integer 0 *) (aref1 size-array-name size-array darg)))
                                   acc)))))

(defthm natp-of-add-darg-sizes-with-name
  (implies (and (all-dargp dargs)
                (size-arrayp size-array-name size-array (+ 1 (largest-non-quotep dargs)))
                (natp acc))
           (natp (add-darg-sizes-with-name dargs size-array-name size-array acc)))
  :hints (("Goal" :in-theory (enable add-darg-sizes-with-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Add to ACC the sizes of all of the DARGS (for a nodenum darg, look up its
;; size in the array, for a quotep darg use a size of 1).
(defund add-darg-sizes (dargs size-array acc)
  (declare (xargs :guard (and (true-listp dargs)
                              (all-dargp dargs)
                              (size-arrayp 'size-array size-array (+ 1 (largest-non-quotep dargs)))
                              (natp acc))
                  :split-types t
                  :guard-hints (("Goal" :in-theory (disable natp))))
           (type (integer 0 *) acc))
  (if (endp dargs)
      acc
    (let ((darg (first dargs)))
      (add-darg-sizes (rest dargs)
                      size-array
                      (+ (if (consp darg) ;check for a quotep, which we say has size 1
                             1
                           ;; dargs is a nodenum, so look up its size:
                           (the (integer 0 *) (aref1 'size-array size-array darg)))
                         acc)))))

(defthm natp-of-add-darg-sizes
  (implies (and (all-dargp dargs)
                (size-arrayp 'size-array size-array (+ 1 (largest-non-quotep dargs)))
                (natp acc))
           (natp (add-darg-sizes dargs size-array acc)))
  :hints (("Goal" :in-theory (enable add-darg-sizes))))
