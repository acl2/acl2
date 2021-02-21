; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This test failed for include-book before mid-February 2021, probably because
; of the special treatment of avoiding the hash-table for already-bound symbols
; -- the "oldp" case formerly in install-for-add-trip-hcomp-build.

; Below, "fal" comes from the filename.

(in-package "ACL2")

(local (defun fal-fn (x) x))

(make-event
 `(defconst *fal* ',(make-fast-alist '((3 . 30) (4 . 40)))))

(assert-event (hons-get 3 *fal*)
              :on-skip-proofs t)
