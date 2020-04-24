(in-package "ACL2")

;;Utilities to test transformations, etc:

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

;; Deftest puts all of its FORMS inside an encapsulate and makes everything
;; local to the deftest. It is similar to must-succeed* but also turns on
;; extensive guard checking (which can help catch bugs during testing).

;; Test whether something like `(encapsulate nil (local ,form)) will give an
;; error because the form is already implicitly local.
(defun cant-be-localp (form)
  (declare (xargs :guard (consp form)))
  (member-eq (car form) *acl2-defaults-table-macros*))

(defun wrap-forms-in-local-when-possible (forms)
  (if (endp forms)
      nil
    (let ((form (first forms)))
      (cons (if (cant-be-localp form)
                form
              `(local, form))
            (wrap-forms-in-local-when-possible (rest forms))))))

(defun deftest-fn (forms)
  `(with-guard-checking-event ;might be slow but does some extensive checking
    :all
    (encapsulate ()
      ,@(wrap-forms-in-local-when-possible forms))))

;; Executes all of the forms but makes them all local to the deftest
(defmacro deftest (&rest forms)
  (deftest-fn forms))
