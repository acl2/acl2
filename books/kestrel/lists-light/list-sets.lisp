; Rules about list operations that treat lists like sets
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "intersection-equal"))

(defthm not-intersection-equal-of-set-difference-equal-arg1
  (not (intersection-equal (set-difference-equal x y) y)))

(defthm not-intersection-equal-of-set-difference-equal-arg2
  (not (intersection-equal y (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal-commutative-iff))))

(defthm intersection-equal-of-union-equal-iff
  (iff (intersection-equal x (union-equal y z))
       (or (intersection-equal x y)
           (intersection-equal x z)))
  :hints (("Goal" :in-theory (enable union-equal))))
