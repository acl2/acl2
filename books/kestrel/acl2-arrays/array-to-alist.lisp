; Turning an array into an alist
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

;(include-book "kestrel/utilities/acons-fast" :dir :system)
(include-book "acl2-arrays") ; for alen1 -- reduce?

(defund array-to-alist-aux (n len array-name array acc)
  (declare (xargs :measure (nfix (+ 1 (- len n)))
                  :guard (and (array1p array-name array)
                              (natp n)
                              (natp len)
                              (<= n (+ 1 len))
;                              (alistp acc)
                              (<= len (alen1 array-name array)))))
  (if (or (<= len n)
          (not (natp n))
          (not (natp len)))
      acc
    (let* ((val (aref1 array-name array n)))
      (array-to-alist-aux (+ 1 n) len array-name array (acons-fast n val acc)))))

(defthm alistp-of-array-to-alist-aux
  (implies (alistp acc)
           (alistp (array-to-alist-aux n len array-name array acc)))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm len-of-array-to-alist-aux
  (implies (and (natp len)
                (natp n))
           (equal (len (array-to-alist-aux n len array-name array acc))
                  (+ (nfix (- len n))
                     (len acc))))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm consp-of-array-to-alist-aux
  (implies (and (natp len)
                (natp n))
           (equal (consp (array-to-alist-aux n len array-name array acc))
                  (or (posp (nfix (- len n)))
                      (consp acc))))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

(defthm car-of-array-to-alist-aux
  (equal (car (array-to-alist-aux n len array-name array acc))
         (if (and (natp len)
                  (natp n)
                  (< n len))
             ;; usual case:
             (cons (+ -1 len) (aref1 array-name array (+ -1 len)))
           (car acc)))
  :hints (("Goal" :in-theory (enable array-to-alist-aux))))

;; Creates an alist mapping indices (from LEN-1 down to 0) to their values in the ARRAY.
;; The indices in the result will be decreasing (critical for Axe since the result will often be an Axe DAG).
;; TODO: Can we avoid this, since the array is backed by an alist (albeit with a header node)?  Maybe call compress1 to remove dups, but watch the order?
(defund array-to-alist (array-name array len)
  (declare (xargs :guard (and (array1p array-name array)
                              (natp len)
                              (<= len (alen1 array-name array)))))
  (array-to-alist-aux 0 len array-name array nil))

(defthm len-of-array-to-alist
  (implies (natp len)
           (equal (len (array-to-alist array-name array len))
                  len))
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm true-listp-of-array-to-alist-type
  (true-listp (array-to-alist array-name array len))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm alistp-of-array-to-alist
  (alistp (array-to-alist array-name array len))
  :hints (("Goal" :in-theory (enable array-to-alist))))

(defthm car-of-array-to-alist
  (implies (posp len)
           (equal (car (array-to-alist array-name array len))
                  (cons (+ -1 len) (aref1 array-name array (+ -1 len)))))
  :hints (("Goal" :in-theory (enable array-to-alist))))
