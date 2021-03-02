; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This test, without the local, is essentially from Sol Swords.  See
; fast-alist-hons-copy.lisp; the use of local here just provides an additional
; test, which failed before mid-February 2021 and now succeeds.

; Below, "fahcl" comes from the filename.

(in-package "ACL2")

(local (defun fahcl (x) x))

(make-event
 `(defconst *fahcl* ',(make-fast-alist
                       (hons-copy '(("c" . "d"))))))
