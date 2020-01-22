; A book about boolif (boolean-valued if-then-else)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "bool-fix")

(defund boolif (test x y)
  (declare (type t test x y))
  (if (if test x y)
      t
    nil))

(defthm booleanp-of-boolif
  (booleanp (boolif x y z)))

(defthm boolif-of-nil-and-t
  (equal (boolif x nil t)
         (not x))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-same-branches
  (equal (boolif test x x)
         (bool-fix x))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-not
  (equal (boolif (not test) x y)
         (boolif test y x))
  :hints (("Goal" :in-theory (enable boolif))))

;do we want this?
(defthm not-of-boolif
  (equal (not (boolif test x y))
         (boolif test (not x) (not y)))
  :hints (("Goal" :in-theory (enable boolif))))

;; Helps justify the STP translation.
(defthm boolif-of-bool-fix-arg1
  (equal (boolif (bool-fix x) y z)
         (boolif x y z))
  :hints (("Goal" :in-theory (enable boolif))))

;; Helps justify the STP translation.
(defthm boolif-of-bool-fix-arg2
  (equal (boolif x (bool-fix y) z)
         (boolif x y z))
  :hints (("Goal" :in-theory (enable boolif))))

;; Helps justify the STP translation.
(defthm boolif-of-bool-fix-arg3
  (equal (boolif x y (bool-fix z))
         (boolif x y z))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-not-same-arg3-alt
  (equal (boolif x y (not x))
         (boolif x y t))
  :hints (("Goal" :in-theory (enable boolif))))

(defthm boolif-of-not-same-arg2-alt
  (equal (boolif x (not x) y)
         (boolif x nil y))
  :hints (("Goal" :in-theory (enable boolif))))
