; Definition of bitwise AND
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the rules in bvand.lisp.

(include-book "bvchop-def")
(local (include-book "logand-b"))
(local (include-book "bvchop"))

(defund bvand (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logand (bvchop size x)
          (bvchop size y)))

(defthm bvand-type
  (and (integerp (bvand size x y))
       (<= 0 (bvand size x y)))
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bvand))) ; bvand-type is at least as good
