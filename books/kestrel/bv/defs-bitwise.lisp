; BV Library: Definitions of bitwise operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop-def")
(local (include-book "bvchop"))

(defund bvand (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logand (bvchop size x)
          (bvchop size y)))

(defund bvor (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logior (bvchop size x)
          (bvchop size y)))

(defund bvxor (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logxor (bvchop size x)
          (bvchop size y)))

(defund bvnot (size x)
  (declare (type integer x)
           (type (integer 0 *) size))
  (bvchop size (lognot x)))

(defund bitor (x y)
  (declare (type integer x)
           (type integer y))
  (bvor 1 x y))

;todo: define using bvnot?
(defund bitnot (x)
  (declare (type integer x))
  (if (= (bvchop 1 x) 0)
      1
    0))

(defund bitand (x y)
  (declare (type integer x)
           (type integer y))
  (bvand 1 x y))

(defund bitxor (x y)
  (declare (type integer x)
           (type integer y))
  (bvxor 1 x y))
