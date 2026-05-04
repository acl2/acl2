; Making a new array whose values are all the default value
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

; Added by Matt K. 8/13/2024: 32-bit CMUCL has smaller value of
; (ARRAY-MAXIMUM-LENGTH-BOUND) than 64-bit Lisps, which causes certification to
; fail, presumably because that bound affects array2p.
; cert_param: (non-cmucl)

(include-book "constants")
(include-book "alen1")
(local (include-book "array1p"))
(local (include-book "compress1"))
;; (local (include-book "header"))

;; Makes a new 1-dimensional array where every element is the default.
;; TODO: Rename this, since "empty" here doesn't mean an array of length 0 but rather that the alist is empty.
;according to array1p, the maximum-length field of an array can be at most (array-maximum-length-bound)
;and the length (first dimension) must be strictly smaller than the :maximum-length (why strictly?)
;; Note that array1p disallows arrays of len 0 (why?), so this function does also.
(defund new-array1-with-default (name len default)
  (declare (type symbol name)
           (type (integer 1 1152921504606846974) len) ; at most *max-1d-array-length*
           (xargs :guard-hints (("Goal" :in-theory (enable array1p)))))
  (compress1 name
             (acons :header (list :dimensions (list len)
                                  ;;array1p requires the :maximum-length to be at most (array-maximum-length-bound)
                                  :maximum-length (min (* 2 len) *max-array-maximum-length* ;the disassembled code was shorter with 2147483647 here than with *maximum-positive-32-bit-integer*
                                                       )
                                  :default default
                                  ;; no :order given here means the order is effectively <
                                  :name name ;; could perhaps omit this
                                  )
                    nil)))

(in-theory (disable (:e new-array1-with-default))) ;; Avoid making arrays during proofs (might be huge)

(defthm array1p-of-new-array1-with-default
  (equal (array1p name (new-array1-with-default name len default))
         (and (posp len)
              (<= len *max-1d-array-length*)
              (symbolp name)))
  :hints (("Goal" :in-theory (enable new-array1-with-default array1p-rewrite))))

(defthm default-of-new-array1-with-default
  (equal (default name1 (new-array1-with-default name2 len default))
         default)
  :hints (("Goal" :in-theory (enable new-array1-with-default))))

(defthm dimensions-of-new-array1-with-default
  (equal (dimensions name1 (new-array1-with-default name2 len default))
         (list len))
  :hints (("Goal" :in-theory (enable new-array1-with-default))))

(defthm alen1-of-new-array1-with-default
  (equal (alen1 name1 (new-array1-with-default name2 len default))
         len)
  :hints (("Goal" :in-theory (enable new-array1-with-default))))

(defthm aref1-of-new-array1-with-default
  (implies (and (natp index) ;gen?
                ;; (< index len) ;we get the default if the index is out of bounds
                (posp len)
                (<= len *max-1d-array-length*))
           (equal (aref1 name1 (new-array1-with-default name2 len default) index)
                  default))
  :hints (("Goal" :in-theory (enable array1p new-array1-with-default))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make an array with LEN elements (and name NAME), where every index has the value nil.
(defund new-array1 (name len)
  (declare (type symbol name)
           (type (integer 1 1152921504606846974) len) ; at most *max-1d-array-length*
           )
  (new-array1-with-default name len nil))

(in-theory (disable (:e new-array1))) ;; Avoid exposing a constant involving a :header

(defthm array1p-of-new-array1
  (equal (array1p name (new-array1 name len))
         (and (posp len)
              (<= len *max-1d-array-length*)
              (symbolp name)))
  :hints (("Goal" :in-theory (enable new-array1))))

;; but see new-array1-with-default
(defthm default-of-new-array1
  (equal (default name1 (new-array1 name2 len))
         nil)
  :hints (("Goal" :in-theory (enable new-array1))))

(defthm dimensions-of-new-array1
  (equal (dimensions name1 (new-array1 name2 len))
         (list len))
  :hints (("Goal" :in-theory (enable new-array1))))

(defthm alen1-of-new-array1
  (equal (alen1 name1 (new-array1 name2 len))
         len)
  :hints (("Goal" :in-theory (enable new-array1))))

(defthm aref1-of-new-array1
  (implies (and (natp index) ;gen?
                ;; (< index len) ;we get nil if the index is out of bounds
                (posp len)
                (<= len *max-1d-array-length*))
           (equal (aref1 name1 (new-array1 name2 len) index)
                  nil))
  :hints (("Goal" :in-theory (enable new-array1))))
