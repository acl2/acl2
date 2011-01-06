(in-package "ACL2")

(defun horrible-include-book-exit (name state)
  (declare (xargs :mode :program :stobjs state))

; This function exits with code 43 if the file 'name' has been included.
; Otherwise, it exits with code 0.

  (mv-let (full-name dir-name familiar-name)
          (parse-book-name (cbd) name ".lisp" state)
          (declare (ignore dir-name familiar-name))
          (if (assoc-equal full-name (global-val 'include-book-alist (w state)))
              (exit 43)
            (exit 0))))