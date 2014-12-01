(in-package "ACL2")
(include-book "plev")
(include-book "include-raw")
(include-book "xdoc/top" :dir :system)

; The following is already in plev.lisp.
; (defpointer plev-info plev)

(defun plev-info ()
  (declare (xargs :guard t))
  (er hard? 'plev-info "raw lisp definition not installed?"))

(defttag plev-ccl)

(include-raw "plev-ccl-raw.lsp")
