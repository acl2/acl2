; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This very basic test succeed, both for certify-book and subsequent
; include-book, both before and after the changes to early loading of compiled
; files in mid-February, 2021.  It's included because it seems like a good,
; simple test.

; Below, "fa" comes from the filename.

(in-package "ACL2")

(make-event
 `(defconst *fa* ',(make-fast-alist '((1 . 10) (2 . 20)))))

(assert-event (hons-get 1 *fa*)
              :on-skip-proofs t)
