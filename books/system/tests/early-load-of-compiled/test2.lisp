; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Before changes in mid-February 2021, certification failed with the error,
; "Fast alist stolen by HL-HSPACE-RESTORE-FAL-FOR-SERIALIZE.".  We no longer
; cause stolen alist errors or warnings during include-book; see also
; hons-acons-bang-local.lisp.

; Below, "t2" comes from the filename.

(in-package "ACL2")
(make-event
 `(defconst *t2-1* ',(make-fast-alist
                      (hons-copy '((1 . 2))))))
(make-event
 `(defconst *t2-2* ',(make-fast-alist
                      (hons-copy '((1 . 2))))))
