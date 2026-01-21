; Definition of the trim function, an alias for bvchop
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
(local (include-book "bvchop"))

;just an alias for bvchop but only used for trimming (using bvchop caused loops if the rules weren't just right)
(defund trim (size i)
  (declare (type integer i)
           (type (integer 0 *) size))
  (bvchop size i))

;; WARNING: It is important that we *not* have a rule for trim like the
;; bvchop-identity rule we have for bvchop (dropping the function call when we
;; know it has no effect).  Such a rule could lead to loops.

(defthm trim-of-0-arg1
  (equal (trim 0 x)
         0)
  :hints (("Goal" :in-theory (enable trim))))
