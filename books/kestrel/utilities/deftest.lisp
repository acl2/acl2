; The deftest utility for isolated tests with extensive guard checking.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "user-interface") ;for cw-event
;; These include-books are not strictly needed but are convenient for users of
;; deftest:
(include-book "std/testing/eval" :dir :system) ;brings in MUST-BE-REDUNDANT
(include-book "std/testing/assert" :dir :system) ;brings in ASSERT-EQUAL and ASSERT!

;; Test whether something like `(encapsulate nil (local ,form)) will give an
;; error because the form is already implicitly local.
(defun cant-be-localp (form)
  (declare (xargs :guard (consp form)))
  (member-eq (car form) *acl2-defaults-table-macros*))

(defun wrap-forms-in-local-when-possible (forms)
  (declare (xargs :guard (true-listp forms)))
  (if (endp forms)
      nil
    (let ((form (first forms)))
      (if (not (consp form))
          (er hard? 'wrap-forms-in-local-when-possible "Unexpected form: ~x0. Expected a cons." form)
        (cons (if (cant-be-localp form)
                  form
                `(local, form))
              (wrap-forms-in-local-when-possible (rest forms)))))))

;todo: maybe use encapsulate-report-errors?
;todo: add verbose option and suppress output if not verbose
(defun deftest-fn (forms)
  (declare (xargs :guard (true-listp forms)))
  `(with-guard-checking-event ;might be slow but does some extensive checking
    :all
    (encapsulate ()
      ,@(wrap-forms-in-local-when-possible forms)
      ;; If we get this far without error, then the test passed:
      (cw-event ":test-passed~%"))))

;; Deftest puts all of the supplied FORMS inside an encapsulate and makes
;; everything local to the deftest.  It is similar to must-succeed* but also
;; turns on extensive guard checking (which can help catch bugs during
;; testing).
(defmacro deftest (&rest forms)
  (deftest-fn forms))
