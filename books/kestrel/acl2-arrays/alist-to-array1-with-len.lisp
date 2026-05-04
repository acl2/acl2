; A function to turn an alist into an array
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bounded-nat-alists")
(include-book "constants")
(include-book "alen1")
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "maximum-length"))
(local (include-book "array1p"))
(local (include-book "header"))
(local (include-book "default"))
(local (include-book "dimensions"))
(local (include-book "compress1"))

;; Makes the ALIST, whose keys must all be naturals less than LEN, into an
;; array named NAME, which will have length LEN.  If LEN is greater than one
;; more than the largest key, the resulting array will contain some slack space
;; (empty slots) for the array to grow.
;rename alist-to-array1-with-slack?
;todo: take the default value as an option
(defund alist-to-array1-with-len (name alist len)
  (declare (type symbol name)
           (type (integer 1 1152921504606846974) len)
           (xargs :guard (and (true-listp alist)
                              (bounded-natp-alistp alist len) ;todo: change this to imply true-listp
                              )
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))))
  (compress1 name
             (acons :header
                    (list :dimensions (list len)
                          ;; TODO: Can we do something better here?:
                          :maximum-length (min (* 2 len)
                                               *max-array-maximum-length* ;the disassembled code was shorter with 2147483647 here than with *maximum-positive-32-bit-integer*
                                               )
                          :default nil ; fixme?
                          :name name)
                    alist)))

(in-theory (disable (:e alist-to-array1-with-len))) ;blew up

(defthm array1p-of-alist-to-array1-with-len
  (implies (and (symbolp name)
                (bounded-integer-alistp alist len)
                (posp len)
                (<= len *max-1d-array-length*))
           (array1p name (alist-to-array1-with-len name alist len)))
  :hints (("Goal" :in-theory (enable alist-to-array1-with-len array1p-rewrite))))

(defthm default-of-alist-to-array1-with-len
  (equal (default name1 (alist-to-array1-with-len name2 alist len))
         nil)
  :hints (("Goal" :in-theory (enable array1p compress1 alist-to-array1-with-len))))

(defthm dimensions-of-alist-to-array1-with-len
  (equal (dimensions name1 (alist-to-array1-with-len name2 alist len))
         (list len))
  :hints (("Goal" :in-theory (enable alist-to-array1-with-len))))

(defthm alen1-of-alist-to-array1-with-len
  (equal (alen1 name1 (alist-to-array1-with-len name2 alist len))
         len)
  :hints (("Goal" :in-theory (enable alist-to-array1-with-len))))

(defthm aref1-of-alist-to-array1-with-len
  (implies (and (bounded-natp-alistp alist len)
                (true-listp alist)
                alist
                (symbolp name1)
                (natp index)
                (< index len)
                (integerp len)
                (<= len *max-1d-array-length*) ; todo: drop?
                )
           (equal (aref1 name1 (alist-to-array1-with-len name2 alist len) index)
                  (cdr (assoc-equal index alist))))
  :hints (("Goal" :in-theory (enable alist-to-array1-with-len aref1))))
