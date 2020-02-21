; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The .cert file should have no :translate entries for this book, because of
; the use of redefinition.

(in-package "ACL2")

(defun f-redef (x)
  x)

(defttag t)

(progn! (set-ld-redefinition-action '(:doit . :overwrite) state))

(defun f-redef (x)
  (cons x x))
