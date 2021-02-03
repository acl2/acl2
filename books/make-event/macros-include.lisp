; This book checks that expansions are stored as expected.  The constant
; *macros-expansion-alist* below is what we expect to find for the
; :expansion-alist field of macros.cert.  The last form in this file shows how
; we can do useful file IO on behalf of a make-event.

(in-package "ACL2")

; Here is the expected :expansion-alist from macros.cert.
(defconst *macros-expansion-alist*
  '((2 DEFUN FOO (X) X)
    (3 MAKE-EVENT '(DEFUN FOO (X) X)
       :CHECK-EXPANSION (DEFUN FOO (X) X))
    (4 ENCAPSULATE ((LOCAL-FN (X) T))
       (LOCAL (VALUE-TRIPLE :ELIDED))
       (RECORD-EXPANSION (MY-MAC (MAKE-EVENT '(DEFUN FOO2 (X) X)
                                             :CHECK-EXPANSION T))
                         (MAKE-EVENT '(DEFUN FOO2 (X) X)
                                     :CHECK-EXPANSION (DEFUN FOO2 (X) X))))
    (5 ENCAPSULATE NIL
       (RECORD-EXPANSION (MY-MAC (MAKE-EVENT '(DEFUN FOO3 (X) X)))
                         (DEFUN FOO3 (X) X)))
    (7 ENCAPSULATE ((LOCAL-FN (X) T))
       (LOCAL (VALUE-TRIPLE :ELIDED))
       (RECORD-EXPANSION (MY-MAC (MAKE-EVENT '(DEFUN FOO2 (X) X)
                                             :CHECK-EXPANSION T))
                         (MAKE-EVENT '(DEFUN FOO2 (X) X)
                                     :CHECK-EXPANSION (DEFUN FOO2 (X) X))))
    (8 ENCAPSULATE ((LOCAL-FN (X) T))
       (LOCAL (VALUE-TRIPLE :ELIDED))
       (RECORD-EXPANSION (MY-MAC (MAKE-EVENT '(DEFUN FOO2 (X) X)
                                             :CHECK-EXPANSION T))
                         (MAKE-EVENT '(DEFUN FOO2 (X) X)
                                     :CHECK-EXPANSION (DEFUN FOO2 (X) X))))
    (10 WITH-OUTPUT :OFF
        :ALL (VALUE-TRIPLE 'T))
    (11 WITH-OUTPUT :OFF
        :ALL (VALUE-TRIPLE 'T))))

; Include the book whose certificate we want to check.
(include-book "macros")

(include-book "std/testing/must-succeed" :dir :system)

; Define read-list (used below).
(include-book "misc/file-io" :dir :system)

; Check that *macros-expansion-alist*, defined above, is equal to the
; :expansion-alist field of the certificate of the "macros" book.  Skip the
; check if we might be doing provisional certification (not the default
; anyhow), since locals are elided more aggressively in that case.
(must-succeed
 (cond
  ((member-eq (cert-op state)
              '(:create-pcert :convert-pcert))
   (value t))
  (t (er-let* ((forms (read-list "macros.cert" 'top state)))
       (let ((erp (not (equal (cadr (member-eq :expansion-alist forms))
                              *macros-expansion-alist*))))
         (mv erp nil state))))))
