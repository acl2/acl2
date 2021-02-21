; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Before mid-February, 2021, this book certified but include-book then failed
; with error, "Fast alist stolen by HONS-ACONS!.".
; All is well now.  See also hons-acons-bang-local.lisp.
; For a simpler test involving only hons, see hons.lisp.
; Below, "hab" comes from the filename.

(in-package "ACL2")
(defconst *hab* (hons-acons! 7 8 nil))
