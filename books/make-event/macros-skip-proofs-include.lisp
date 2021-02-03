; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

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

(defconst *encap-expansion-pcert*
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
     (LOCAL (VALUE-TRIPLE :ELIDED)) ; eliding was optional
     (RECORD-EXPANSION (LOCAL (MAKE-EVENT '(DEFUN FOO1 (X) X)))
                       (LOCAL (VALUE-TRIPLE :ELIDED))) ; eliding was optional
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

; Here is the expected :expansion-alist from macros-skip-proofs.cert when
; provisional certification was not used.
(defconst *macros-expansion-alist*
  `((2 ,@*encap-expansion*)
    (3 ,@*encap-expansion*)))

; Here is the expected :expansion-alist from macros-skip-proofs.cert when
; provisional certification was used.
(defconst *macros-expansion-alist-pcert*
  `((2 ,@*encap-expansion-pcert*)
    (3 ,@*encap-expansion-pcert*)))

(include-book "macros-skip-proofs")

(include-book "std/testing/must-succeed" :dir :system)

(include-book "misc/file-io" :dir :system)

#||
(must-succeed
 (mv-let
  (erp val state)
  (read-list "local-elided.pcert" 'top state)
  (declare (ignore val))
  (er-let* ((forms (read-list "macros-skip-proofs.cert" 'top state)))
    (let ((erp (not (equal (cadr (member-eq :expansion-alist forms))
                           (if erp ; no .pcert file
                               *macros-expansion-alist*
                             *macros-expansion-alist-pcert*)))))
      (mv erp nil state)))))
||#
