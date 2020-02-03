; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "sub1")

; Trace get-translate-cert-data-record when including this book and you'll see
; that it DOES get a hit, but under the include-book of sub1 (so, also trace
; include-book-fn).  We mention this in the Essay on Cert-data.

(defun f1 (x) (cons x x))
