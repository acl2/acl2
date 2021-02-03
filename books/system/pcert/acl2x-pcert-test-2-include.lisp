(in-package "ACL2")

(include-book "std/testing/must-eval-to-t" :dir :system)

; We add this for the dependency scanner, though perhaps the dependency of
; acl2x-pcert-test-2-include.pcert0 on acl2x-pcert-test-2.cert in Makefile is
; sufficient.
#||
(include-book "acl2x-pcert-test-2")
||#

(must-eval-to-t
 (er-let*
  ((acl2-pcert (getenv$ "ACL2_PCERT" state)))
  (if (member-equal acl2-pcert '("" nil))
      (value t)
    (er-let*
     ((forms (read-file "acl2x-pcert-test-2.pcert0" state)))
     (value
      (equal (cadr (member-eq :pcert-info forms))
             '((2 RECORD-EXPANSION
                  (ENCAPSULATE NIL
                               (LOCAL (MAKE-EVENT '(DEFUN G (X) X)))
                               (DEFUN H (X) X))
                  (ENCAPSULATE NIL
                               (RECORD-EXPANSION (LOCAL (MAKE-EVENT '(DEFUN G (X) X)))
                                                 (LOCAL (DEFUN G (X) X)))
                               (DEFUN H (X) X))))))))))
