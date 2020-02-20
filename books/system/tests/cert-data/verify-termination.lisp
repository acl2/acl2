; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The .cert file shows a single cert-data :translate record for foo, even
; though the same body for foo is encoutered twice during certification.

(in-package "ACL2")

(defun foo-vt (x) (declare (xargs :mode :program)) (cons x x))
(verify-termination foo-vt)
