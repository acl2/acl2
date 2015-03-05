

(include-book "grep-command-line")

:q

(defun run-grep ()
  (ccl::gc-verbose nil nil)
  (mv-let (code st)
    (grep-exec (cdr ccl::*command-line-argument-list*) *the-live-state*)
    (declare (ignore st))
    (ccl::quit code)))

(ccl:save-application
 "acl2-grep"
 :toplevel-function #'run-grep
 :prepend-kernel (car ccl::*command-line-argument-list*))

