; A book about bool-fix, which coerces a value to a boolean.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; See also the copyright where bool-fix is defined.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

;Changed this to match the version in the std library.
;maybe this should not be hyphenated by analogy with nfix, etc.
(DEFUND BOOL-FIX$INLINE (X)
  (DECLARE (XARGS :GUARD T))
  (AND X T))

;Added to match the version in the std library.
(DEFMACRO BOOL-FIX (X)
  (LIST 'BOOL-FIX$INLINE X))

(add-macro-alias bool-fix bool-fix$inline)

;; ;; old:
;; (defun bool-fix (x)
;;   (declare (xargs :guard t))
;;   (and x t))

(defthm booleanp-of-bool-fix
  (booleanp (bool-fix x))
  :rule-classes :type-prescription)

(defthm bool-fix-when-booleanp
  (implies (booleanp x)
           (equal (bool-fix x)
                  x))
  :hints (("Goal" :in-theory (enable bool-fix))))

(defthm not-of-bool-fix
  (equal (not (bool-fix x))
         (not x))
  :hints (("Goal" :in-theory (enable bool-fix))))

(defthm bool-fix-iff
  (iff (bool-fix x)
       x)
  :hints (("Goal" :in-theory (enable bool-fix))))

;; This helps justify some things that Axe does:
(defcong iff equal (bool-fix$inline x) 1 :hints (("Goal" :in-theory (enable bool-fix))))
