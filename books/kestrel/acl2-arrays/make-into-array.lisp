; A function to turn an alist into an array
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

(include-book "make-into-array-with-len") ; todo: reduce
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;Consider adding an option to reuse an existing array if large enough (well, compress1 now does that internally)?
; The length of the resulting array is one more than the max key in the alist, unless the alist is empty, in which case the length is 1.
; TODO: Add an option for slack space
(defund make-into-array (array-name alist)
  (declare (xargs :guard (and (true-listp alist)
                              (bounded-natp-alistp alist (+ -1 *maximum-positive-32-bit-integer*)) ; might be able to drop the -1 if array1p is weakened a bit
                              )
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite))))
           (type symbol array-name))
  (let* ((len (if (consp alist)
                  ;; normal case:
                  (+ 1 (max-key alist 0)) ;could save this max if we know it's a dag-lst...
                ;; compress1 must be given a dimension of at least 1
                1)))
    (make-into-array-with-len array-name alist len)))

(in-theory (disable (:e make-into-array))) ;might blow up

(defthm default-of-make-into-array
  (equal (default array-name (make-into-array array-name alist))
         nil)
  :hints (("Goal" :in-theory (enable make-into-array))))

(defthm array1p-of-make-into-array
  (implies (and (bounded-natp-alistp alist 2147483646)
                (true-listp alist)
                ;alist
                (symbolp array-name)
                )
           (equal (array1p array-name (make-into-array array-name alist))
                  t))
  :hints (("Goal" :in-theory (e/d (array1p compress1 make-into-array) (normalize-array1p-name)))))

(defthm aref1-of-make-into-array
  (implies (and (bounded-natp-alistp alist 2147483646)
                (true-listp alist)
                alist
                (symbolp array-name)
                (natp index)
                (< index (max-key alist 0))
                )
           (equal (aref1 array-name (make-into-array array-name alist) index)
                  (cdr (assoc-equal index alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable array1p ;compress1
                              ARRAY-ORDER
                              make-into-array
                              aref1))))

(defthm dimensions-of-make-into-array
  (equal (dimensions array-name (make-into-array array-name alist))
         (if (consp alist)
             (list (+ 1 (max-key alist 0)))
           (list 1)))
  :hints (("Goal" :in-theory (enable make-into-array))))

(defthm alen1-of-make-into-array
  (equal (alen1 array-name (make-into-array array-name alist))
         (if (consp alist)
             (+ 1 (max-key alist 0))
           1))
  :hints (("Goal" :in-theory (enable make-into-array))))

(defthm make-into-array-of-nil
  (equal (make-into-array array-name nil)
         (make-empty-array array-name 1))
  :hints (("Goal" :in-theory (enable make-into-array MAKE-INTO-ARRAY-WITH-LEN MAKE-EMPTY-ARRAY MAKE-EMPTY-ARRAY-WITH-DEFAULT))))
