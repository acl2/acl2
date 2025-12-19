; Arithmetic negation of a bit-vector
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop-def")

;; "bit-vector unary minus"
;; Compute the (modular) negation / additive inverse of X.
(defund bvuminus (size x)
  (declare (type (integer 0 *) size))
  ;; (bvminus size 0 x)
  (bvchop size (- (ifix x))))
