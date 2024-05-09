; A utility to read-in a book using the appropriate package
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-object-from-file" :dir :system)
(include-book "kestrel/file-io-light/read-objects-from-file-with-pkg" :dir :system)

;; Read forms from FILENAME but require the first form to be an IN-PACKAGE form
;; used for interpreting symbols in the rest of the forms.  Returns (mv erp
;; forms state).  Consider first calling something like load-port-file-if-exists
;; to ensure the packages are known.
(defund read-objects-from-book (filename state)
  (declare (xargs :guard (stringp filename) ; includes the .lisp extension
                  :mode :program            ; because of in-package-fn
                  :stobjs state))
  ;; First read just the in-package form:
  (mv-let (erp first-form state)
    (read-object-from-file filename state)
    (if erp
        (mv erp nil state)
      (if (not (and (consp first-form)
                    (eq 'in-package (car first-form))))
          (prog2$ (er hard? 'read-objects-from-book "ERROR: Expected an in-package form but got ~x0." first-form)
                  (mv :missing-in-package nil state))
        (let ((book-package (cadr first-form)))
          ;; Read the book contents after temporarily setting the package to book-package:
          (mv-let (erp forms state)
            (read-objects-from-file-with-pkg filename book-package state)
            (if erp ; error reading forms
                (mv erp nil state)
              ;; No error:
              (mv nil forms state))))))))
