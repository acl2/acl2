#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "acl2s/package.lsp" :dir :system)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "std/portcullis" :dir :system)
; cert-flags: ? t :ttags :all
(begin-book t :ttags :all);$ACL2s-Preamble$|#

;; Note: This book just gathers in one place all ACL2 books
;; that should be certified to build ACL2s.

;; Books ACL2s depends on.
(in-package "ACL2")

(include-book "system/doc/acl2-doc-wrap" :dir :system)
(include-book "acl2s/mode-acl2s-dependencies-lite" :dir :system)
