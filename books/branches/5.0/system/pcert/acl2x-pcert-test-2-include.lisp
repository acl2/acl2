(in-package "ACL2")

; Define must-succeed (used below).
(include-book "misc/eval" :dir :system)

(must-eval-to-t
 (er-let* ((forms (read-file "acl2x-pcert-test-2.pcert0" state)))
   (value
    (equal (cadr (member-eq :pcert-info forms))
           '((2 RECORD-EXPANSION
                (ENCAPSULATE NIL
                             (LOCAL (MAKE-EVENT '(DEFUN G (X) X)))
                             (DEFUN H (X) X))
                (ENCAPSULATE NIL
                             (RECORD-EXPANSION (LOCAL (MAKE-EVENT '(DEFUN G (X) X)))
                                               (LOCAL (DEFUN G (X) X)))
                             (DEFUN H (X) X))))))))
