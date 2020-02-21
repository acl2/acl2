; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(local (include-book "sub1"))

; Trace get-translate-cert-data-record when including this book and you'll see
; that it doesn't hit.  We mention this in the Essay on Cert-data.

(defun f1 (x) (cons x x))
