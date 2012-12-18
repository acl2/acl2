; Check part of the certificate's :expansion-alist for
; local-requires-skip-check.lisp.

(in-package "ACL2")

(local (include-book "misc/file-io" :dir :system))

(local (include-book "local-requires-skip-check"))

(include-book "eval")

(must-succeed
 (er-let* ((forms (read-list "local-requires-skip-check.cert" 'top state)))
          (let ((erp (not (equal (car (last (cadr (member-eq :expansion-alist
                                                             forms))))
                                 '(9 RECORD-EXPANSION
                                     (must-fail
                                      (local
                                       (make-event
                                        '(defun test10 (x) (identity-macro x))
                                        :check-expansion
                                        (defun test10 (x) (cons x x)))
                                       ))
                                     (VALUE-TRIPLE 'T))))))
            (mv erp nil state))))
