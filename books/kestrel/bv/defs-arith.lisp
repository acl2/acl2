; Definitions of arithmetic operations on bvs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop-def")

(defund bvplus (size x y)
  (declare (type (integer 0 *) size))
  (bvchop size (+ (ifix x) (ifix y))))

(defund bvminus (size x y)
  (declare (type (integer 0 *) size))
  (bvchop size (- (ifix x) (ifix y))))

;; TODO: Consider instead defining bvminus in terms of bvplus and this.
(defun bvuminus (size x)
  (declare (type (integer 0 *) size))
  (bvminus size 0 x))

(defund bvmult (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (bvchop size (* (ifix x) (ifix y))))
