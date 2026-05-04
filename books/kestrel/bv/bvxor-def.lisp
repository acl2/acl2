; Definition of bitwise XOR
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the rules in bvxor.lisp.

(include-book "bvchop-def")
(local (include-book "logxor-b"))
(local (include-book "bvchop"))

(defund bvxor (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logxor (bvchop size x)
          (bvchop size y)))

(defthm bvxor-type
  (and (integerp (bvxor size x y))
       (<= 0 (bvxor size x y)))
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bvxor))) ; bvxor-type is at least as good
