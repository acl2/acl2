; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This very basic test succeeds, both for certify-book and subsequent
; include-book, both before and after the changes to early loading of compiled
; files in mid-February, 2021.  It's included because it seems like a good,
; simple test.

; See also hons-local.lisp.

; Below, "h" comes from the filename.

(in-package "ACL2")

(defconst *h1* (hons 1 2))

(make-event `(defconst *h2* ',(hons 1 2)))
