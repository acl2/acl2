; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Before mid-February 2021, include-book failed after certifying this book,
; with the message: "Fast alist discipline violated in HONS-GET."  The solution
; was to modify install-for-add-trip-hcomp-build to avoid storing definitions
; with quoted bodies into hash tables.  Thus, when later including the book,
; the definition is not taken from the compiled file but is evaluated instead
; based on the event, which comes from the serialized certificate file, where
; fast alists are restored upon reading that file.

; Below, "dfs" comes from the filename.

(in-package "ACL2")

(make-event `(defun dfa ()
               (declare (xargs :guard t))
               ',(make-fast-alist '((1 . t)))))

(assert-event (equal (cdr (hons-get 1 (dfa)))
                     t)
              :on-skip-proofs t)
