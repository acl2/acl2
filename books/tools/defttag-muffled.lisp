; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; If you include this book, then you'll never see a ttag note again in the
; current ACL2 session.  That's arguably horrible, but since a ttag note is
; printed when certifying this book, that behavior isn't any sort of violation.

(in-package "ACL2")

(defttag :defttag-muffled)

(progn!

(set-raw-mode t)

(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (ignore val active-book-name include-bookp deferred-p))
  state)
)
