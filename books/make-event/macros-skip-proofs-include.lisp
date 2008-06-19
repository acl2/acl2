; See macros-skip-proofs.lisp.

(in-package "ACL2")

(defconst *encap-expansion*
  '(RECORD-EXPANSION
    (ENCAPSULATE ((LOCAL-FN (X) T))
                 (LOCAL (DEFUN LOCAL-FN (X) X))
                 (LOCAL (MAKE-EVENT '(DEFUN FOO1 (X) X)))
                 (MY-MAC (SKIP-PROOFS (MAKE-EVENT '(DEFUN FOO2 (X) X)
                                                  :CHECK-EXPANSION T)))
                 (SKIP-PROOFS (MY-MAC (MAKE-EVENT '(DEFUN FOO3 (X) X)
                                                  :CHECK-EXPANSION T)))
                 (MAKE-EVENT '(DEFUN FOO4 (X) X)))
    (ENCAPSULATE
     ((LOCAL-FN (X) T))
     (LOCAL (DEFUN LOCAL-FN (X) X))
     (RECORD-EXPANSION (LOCAL (MAKE-EVENT '(DEFUN FOO1 (X) X)))
; Change for v3-4:
;                      (LOCAL (DEFUN FOO1 (X) X)))
                       (LOCAL (value-triple :elided)))
     (RECORD-EXPANSION
      (MY-MAC (SKIP-PROOFS (MAKE-EVENT '(DEFUN FOO2 (X) X)
                                       :CHECK-EXPANSION T)))
      (SKIP-PROOFS (MAKE-EVENT '(DEFUN FOO2 (X) X)
                               :CHECK-EXPANSION (DEFUN FOO2 (X) X))))
     (RECORD-EXPANSION
      (SKIP-PROOFS (MY-MAC (MAKE-EVENT '(DEFUN FOO3 (X) X)
                                       :CHECK-EXPANSION T)))
      (SKIP-PROOFS (MAKE-EVENT '(DEFUN FOO3 (X) X)
                               :CHECK-EXPANSION (DEFUN FOO3 (X) X))))
     (RECORD-EXPANSION (MAKE-EVENT '(DEFUN FOO4 (X) X))
                       (DEFUN FOO4 (X) X)))))

(defconst *macros-expansion-alist*
  `((2 ,@*encap-expansion*)
    (3 ,@*encap-expansion*)))

(include-book "macros-skip-proofs")

(include-book "eval")

(include-book "misc/file-io" :dir :system)

; Uncomment the following when updating to v3-4, and also perhaps remove
; comment above v3-4 above.
#||
(must-succeed
 (er-let* ((forms (read-list "macros-skip-proofs.cert" 'top state)))
          (let ((erp (not (equal (cadr (member-eq :expansion-alist forms))
                                 *macros-expansion-alist*))))
            (mv erp nil state))))
||#
