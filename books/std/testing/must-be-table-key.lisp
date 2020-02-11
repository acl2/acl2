; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "assert")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-be-table-key
  :parents (std/testing)
  :short "A top-level @(tsee assert$)-like command to ensure that
          a @(see table) includes a certain key."
  :long "@(def must-be-table-key)"

  (defmacro must-be-table-key (key table)
    (declare (xargs :guard (and (symbolp key) (symbolp table))))
    `(assert! (assoc-eq ',key (table-alist ',table (w state))))))
