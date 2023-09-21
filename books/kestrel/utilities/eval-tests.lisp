; A lightweight testing utility
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/magic-ev-term" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)

;; For each of the test-inputs, binds the VARS to the values in the test and then evaluates FORM.
;; Throws an error if any test causes an error or returns nil.
(defun eval-tests-aux (form vars test-inputs state)
  (declare (xargs :guard (and (pseudo-termp form)
                              (symbol-listp vars)
                              (true-list-listp test-inputs))
                  :stobjs state))
  (if (endp test-inputs)
      '(value-triple :ok)
    (let* ((test (first test-inputs)))
      (if (not (equal (len test) (len vars)))
          (er hard? 'eval-tests "Test ~x0 has the wrong length (should have ~x1 values)." test (len vars))
        (let ((alist (pairlis$ vars test)))
          (mv-let (erp res)
            (acl2::magic-ev-term form alist nil t state)
            (if erp
                (er hard? 'eval-tests "Error (~x0) evaluating test form ~x1 with the alist ~x2." erp form alist)
              (if (not res)
                  (er hard? 'eval-tests "Test failed.  The test form ~x0 evaluated to nil with the alist ~x1." form alist)
                (prog2$ (cw "Passed.~%")
                        (eval-tests-aux form vars (rest test-inputs) state))))))))))

(defun eval-tests-fn (form vars test-inputs state)
  (declare (xargs :guard (and (symbol-listp vars)
                              (true-list-listp test-inputs))
                  :mode :program ; because of translate-term
                  :stobjs state))
  (eval-tests-aux (acl2::translate-term form 'eval-tests-fn (w state)) vars test-inputs state))

;; For each of the TEST-INPUTS, this binds the VARS to the values in the
;; test-input and then evaluates FORM.
;; Throws an error if any test causes an error or returns nil.
;; FORM and VARS are not evaluated.  FORM can be untranslated.
;; VARS indicates the order of the values in each test.
(defmacro eval-tests (form vars test-inputs)
  `(make-event (eval-tests-fn ',form ',vars ,test-inputs state)))
