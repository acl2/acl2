(in-package "ACL2")
(include-book "plev")
(include-book "include-raw")

(link-doc-to plev-info print-control plev)

(defun plev-info ()
  (declare (xargs :guard t))
  (er hard? 'plev-info "raw lisp definition not installed?"))

(defttag plev-ccl)

(include-raw "plev-ccl-raw.lsp")
