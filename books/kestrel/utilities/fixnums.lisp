; Material about fixnums
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the built-in function fixnum-bound (= 2^29-1), but that seems
;; intended for 32-bit Lisps.

;; The size of a fixnum is dependent on the Lisp implementataion.
;; Evaluating most-positive-fixnum on CCL and SBCL gives 2^60-1 and 2^62-1, respectively.
;; We choose the more conservative value here.
(defconst *max-fixnum* (+ -1 (expt 2 60)))

;; The size of a fixnum is dependent on the Lisp implementataion.
;; Evaluating most-negative-fixnum on CCL and SBCL gives -(2^60) and -(2^62), respectively.
;; We choose the more conservative value here.
(defconst *min-fixnum* (- (expt 2 60)))

;; Recognizes a number that should be a fixnum in the most important 64-bit Lisps.
(defun fixnump (x)
  (declare (xargs :guard t))
  (signed-byte-p 61 x))

;; sanity check
(thm
 (and (fixnump *min-fixnum*)
      (fixnump *max-fixnum*)))
