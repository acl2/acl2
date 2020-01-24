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
(DEFUN BOOL-FIX$INLINE (X)
  (DECLARE (XARGS :GUARD T))
  (AND X T))

;Added to match the version in the std library.
(DEFMACRO BOOL-FIX (X)
  (LIST 'BOOL-FIX$INLINE X))

;; TODO: Add macro alias

;; ;; old:
;; (defun bool-fix (x)
;;   (declare (xargs :guard t))
;;   (and x t))

(defthm booleanp-of-bool-fix
  (booleanp (bool-fix x))
  :rule-classes :type-prescription)
