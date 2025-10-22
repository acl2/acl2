; BV Library: Definition of bvplus
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

;; Compute the sum of X and Y, chopped down to SIZE bits.
(defund bvplus (size x y)
  (declare (type (integer 0 *) size))
  (bvchop size (+ (ifix x) (ifix y))))
