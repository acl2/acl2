; A book about bool-fix, which coerces a value to a boolean.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bool-fix-def")

(defthm bool-fix-when-booleanp
  (implies (booleanp x)
           (equal (bool-fix x)
                  x))
  :hints (("Goal" :in-theory (enable bool-fix))))

;use a congruence?
(defthm not-of-bool-fix
  (equal (not (bool-fix x))
         (not x))
  :hints (("Goal" :in-theory (enable bool-fix))))

(defthm if-of-bool-fix-arg1
  (equal (if (bool-fix x) y z)
         (if x y z))
  :hints (("Goal" :in-theory (enable bool-fix))))

(defthm bool-fix-of-bool-fix
  (equal (bool-fix (bool-fix x))
         (bool-fix x)))

(defthm bool-fix-iff
  (iff (bool-fix x)
       x)
  :hints (("Goal" :in-theory (enable bool-fix))))

;; This helps justify some things that Axe does:
(defcong iff equal (bool-fix$inline x) 1 :hints (("Goal" :in-theory (enable bool-fix))))
