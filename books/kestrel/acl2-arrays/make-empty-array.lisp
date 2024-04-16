; Making a new array whose values are all the default value
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alen1")
(local (include-book "array1p"))
(local (include-book "compress1"))
(local (include-book "header"))

;; Make an array where every element is the default.
;; TODO: Rename this, since "empty" here doesn't mean an array of length 0 but rather that the alist is empty.
;according to array1p, the maximum-length field of an array can be at most *maximum-positive-32-bit-integer* = 2147483647
;and the length (first dimension) of the array is at most 2147483646 since it must be strictly smaller than the :maximum-length (why strictly?)
;; Note that array1p disallows arrays of size 0 (why?), so this function does also.
(defund make-empty-array-with-default (name size default)
  (declare (type symbol name)
           (type (integer 1 2147483646) size)
           (xargs :guard-hints (("Goal" :in-theory (enable array1p)))))
  (compress1 name
             (acons :header (list :dimensions (list size)
                                  ;;array1p require the :maximum-length to be at most *MAXIMUM-POSITIVE-32-BIT-INTEGER*
                                  :maximum-length (min (* 2 size) *maximum-positive-32-bit-integer* ;the disassembled code was shorter with 2147483647 here than with *maximum-positive-32-bit-integer*
                                                       )
                                  :default default
                                  ;; no :order given here means the order is effectively <
                                  :name name ;; could perhaps omit this
                                  )
                    nil)))

(in-theory (disable (:e make-empty-array-with-default))) ;; Avoid making arrays during proofs (might be huge)

(defthm array1p-of-make-empty-array-with-default
  (equal (array1p array-name (make-empty-array-with-default array-name len default))
         (and (posp len)
              (<= len 2147483646)
              (symbolp array-name)))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm dimensions-of-make-empty-array-with-default
  (equal (dimensions array-name (make-empty-array-with-default array-name len default))
         (list len))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm alen1-of-make-empty-array-with-default
  (equal (alen1 array-name (make-empty-array-with-default array-name len default))
         len)
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm default-of-make-empty-array-with-default
  (equal (default dag-parent-array-name (make-empty-array-with-default dag-parent-array-name size default))
         default)
  :hints (("Goal" :in-theory (enable make-empty-array-with-default))))

(defthm aref1-of-make-empty-array-with-default
  (implies (and ;(symbolp array-name)
                (natp index) ;gen?
;                (< index len) ;we get nil if the index is out of bounds
                (posp len)
                (< len 2147483647)
                )
           (equal (aref1 array-name (make-empty-array-with-default array-name2 len default) index)
                  default))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable array1p ;compress1
                              array-order
                              make-empty-array-with-default
                              aref1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make an array with SIZE elements (and name NAME), where every index has the value nil.
(defund make-empty-array (name size)
  (declare (type symbol name)
           (type (integer 1 2147483646) size)
           (xargs :guard-hints (("Goal" :in-theory (enable array1p len)))))
  (make-empty-array-with-default name size nil))

(in-theory (disable (:e make-empty-array))) ;; Avoid exposing a constant involving a :header

(defthm array1p-of-make-empty-array
  (equal (array1p array-name (make-empty-array array-name len))
         (and (posp len)
              (<= len 2147483646)
              (symbolp array-name)))
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm dimensions-of-make-empty-array
  (equal (dimensions array-name (make-empty-array array-name len))
         (list len))
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm alen1-of-make-empty-array
  (equal (alen1 array-name (make-empty-array array-name len))
         len)
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm default-of-make-empty-array
  (equal (default dag-parent-array-name (make-empty-array dag-parent-array-name size))
         nil)
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm aref1-of-make-empty-array
  (implies (and ;(symbolp array-name)
                (natp index) ;gen?
;                (< index len) ;we get nil if the index is out of bounds
                (posp len)
                (< len 2147483647)
                )
           (equal (aref1 array-name (make-empty-array array-name2 len) index)
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :in-theory (enable array1p ;compress1
                              array-order
                              make-empty-array
                              aref1))))
