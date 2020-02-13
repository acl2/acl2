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

(defsection must-not-be-table-key
  :parents (std/testing)
  :short "A top-level @(tsee assert$)-like command to ensure that
          a @(see table) does not include a certain key."
  :long "@(def must-not-be-table-key)"

  (defmacro must-not-be-table-key (key table)
    (declare (xargs :guard (and (symbolp key) (symbolp table))))
    `(assert! (not (assoc-eq ',key (table-alist ',table (w state)))))))
