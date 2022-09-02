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

(include-book "acl2-arrays") ; todo: reduce
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

;; Makes the ALIST, whose keys must be naturals, into an array named
;; ARRAY-NAME, which will have length LEN.  LEN must exceed the largest key in
;; ALIST.  If LEN is greater than the largest key, the resulting array will
;; contain some slack space (empty slots) for the array to grow.
;rename make-into-array-with-slack?
;todo: add an option to reuse an existing array if large enough?
;todo: adapt this to use max-key like the one above?
;todo: take the default value as an option
(defund make-into-array-with-len (array-name alist len)
  (declare (type (integer 1 2147483646) len)
           (type symbol array-name)
           (xargs :guard (and (true-listp alist)
                              (bounded-natp-alistp alist len) ;todo: change this to imply true-listp
                              )
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))))
  (compress1 array-name
             (acons-fast :header
                         (list :dimensions (list len)
                               ;; TODO: Can we do something better here?:
                               :maximum-length (min (* 2 len)
                                                    *maximum-positive-32-bit-integer* ;the disassembled code was shorter with 2147483647 here than with *maximum-positive-32-bit-integer*
                                                    )
                               :default nil ; ;fixme?
                               :name array-name)
                         alist)))

(in-theory (disable (:e make-into-array-with-len))) ;blew up

(defthm dimensions-of-make-into-array-with-len
  (equal (dimensions array-name (make-into-array-with-len array-name alist len))
         (list len))
  :hints (("Goal" :in-theory (enable make-into-array-with-len))))

(defthm alen1-of-make-into-array-with-len
  (equal (alen1 array-name (make-into-array-with-len array-name alist len))
         len)
  :hints (("Goal" :in-theory (enable make-into-array-with-len))))

(defthm array1p-of-make-into-array-with-len
  (implies (and (symbolp array-name)
                (bounded-integer-alistp alist len)
                (posp len)
                (< len 2147483647))
           (array1p array-name (make-into-array-with-len array-name alist len)))
  :hints (("Goal" :in-theory (enable make-into-array-with-len array1p-rewrite))))

(defthm default-of-make-into-array-with-len
  (equal (default array-name (make-into-array-with-len array-name alist len))
         nil)
  :hints (("Goal" :in-theory (enable array1p compress1 make-into-array-with-len))))

(defthm aref1-of-make-into-array-with-len
  (implies (and (bounded-natp-alistp alist len)
                (true-listp alist)
                alist
                (symbolp array-name)
                (natp index)
                (< index len)
                (integerp len)
                (< len 2147483647) ; todo: drop?
                )
           (equal (aref1 array-name (make-into-array-with-len array-name alist len) index)
                  (cdr (assoc-equal index alist))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :expand (AREF1 ARRAY-NAME ALIST INDEX)
           :in-theory (e/d ( ;array1p ;compress1
                            ARRAY-ORDER
                            make-into-array-with-len
                            ;;aref1
                            ) (array1p NORMALIZE-AREF1-NAME)))))
