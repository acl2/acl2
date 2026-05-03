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
(defund make-empty-array-with-default (name len default)
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

(in-theory (disable (:e make-empty-array-with-default))) ;; Avoid making arrays during proofs (might be huge)

(defthm array1p-of-make-empty-array-with-default
  (equal (array1p name (make-empty-array-with-default name len default))
         (and (posp len)
              (<= len *max-1d-array-length*)
              (symbolp name)))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default array1p-rewrite))))

(defthm default-of-make-empty-array-with-default
  (equal (default name (make-empty-array-with-default name len default))
         default)
  :hints (("Goal" :in-theory (enable make-empty-array-with-default))))

(defthm dimensions-of-make-empty-array-with-default
  (equal (dimensions name (make-empty-array-with-default name len default))
         (list len))
  :hints (("Goal" :in-theory (enable make-empty-array-with-default))))

(defthm alen1-of-make-empty-array-with-default
  (equal (alen1 name (make-empty-array-with-default name len default))
         len)
  :hints (("Goal" :in-theory (enable make-empty-array-with-default))))

(defthm aref1-of-make-empty-array-with-default
  (implies (and (natp index) ;gen?
                ;; (< index len) ;we get the default if the index is out of bounds
                (posp len)
                (<= len *max-1d-array-length*))
           (equal (aref1 name (make-empty-array-with-default name2 len default) index)
                  default))
  :hints (("Goal" :in-theory (enable array1p make-empty-array-with-default))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make an array with LEN elements (and name NAME), where every index has the value nil.
(defund make-empty-array (name len)
  (declare (type symbol name)
           (type (integer 1 1152921504606846974) len) ; at most *max-1d-array-length*
           )
  (make-empty-array-with-default name len nil))

(in-theory (disable (:e make-empty-array))) ;; Avoid exposing a constant involving a :header

(defthm array1p-of-make-empty-array
  (equal (array1p name (make-empty-array name len))
         (and (posp len)
              (<= len *max-1d-array-length*)
              (symbolp name)))
  :hints (("Goal" :in-theory (enable make-empty-array))))

;; but see make-empty-array-with-default
(defthm default-of-make-empty-array
  (equal (default name (make-empty-array name len))
         nil)
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm dimensions-of-make-empty-array
  (equal (dimensions name (make-empty-array name len))
         (list len))
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm alen1-of-make-empty-array
  (equal (alen1 name (make-empty-array name len))
         len)
  :hints (("Goal" :in-theory (enable make-empty-array))))

(defthm aref1-of-make-empty-array
  (implies (and (natp index) ;gen?
                ;; (< index len) ;we get nil if the index is out of bounds
                (posp len)
                (<= len *max-1d-array-length*))
           (equal (aref1 name (make-empty-array name2 len) index)
                  nil))
  :hints (("Goal" :in-theory (enable make-empty-array))))
