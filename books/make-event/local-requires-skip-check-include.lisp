; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Check part of the certificate's :expansion-alist for
; local-requires-skip-check.lisp.

(in-package "ACL2")

(local (include-book "misc/file-io" :dir :system))

(local (include-book "local-requires-skip-check"))

(include-book "std/testing/must-succeed" :dir :system)

(must-succeed
 (er-let* ((forms (read-list "local-requires-skip-check.cert" 'top state)))
          (let ((erp (not (equal (car (last (cadr (member-eq :expansion-alist
                                                             forms))))
                                 '(9 WITH-OUTPUT :OFF :ALL
                                     (VALUE-TRIPLE 'T))))))
            (mv erp nil state))))
