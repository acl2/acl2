; Definition of bitwise OR
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the rules in bvor.lisp.

(include-book "bvchop-def")
(local (include-book "logior-b"))
(local (include-book "bvchop"))

(defund bvor (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (logior (bvchop size x)
          (bvchop size y)))

(defthm bvor-type
  (and (integerp (bvor size x y))
       (<= 0 (bvor size x y)))
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bvor))) ; bvor-type is at least as good
