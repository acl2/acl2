; Constants for max array length, etc.
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

;; TODO: Consider making these macros that expand to numbers, for extra speed.

;; The maximum value of an array's "maximum length".
;; See array1p and array2p.
(defconst *max-array-maximum-length* *maximum-positive-32-bit-integer*)

;; The length of the longest possible 1-dimensional array.
;; The -1 is here because array1p requries the length to be strictly less than
;; the :MAXIMUM-LENGTH (why?).
;; See array1p.
(defconst *max-1d-array-length* (+ -1 *max-array-maximum-length*))

;; The largest possible index into a 1-dimensional array (assuming it has the largest possible length).
;; The index must be strictly less than the length.
(defconst *max-1d-array-index* (+ -1 *max-1d-array-length*))
