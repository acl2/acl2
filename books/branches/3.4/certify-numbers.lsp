; acl2 < certify-numbers.lisp > numbers.log&

; Run this file from the top of the books/ directory, not a subdirectory.

(in-package "ACL2")

:set-cbd "cowles"

(ld "certify.lsp" :ld-error-action :error)

:ubt! 1

:set-cbd "../arithmetic"

(ld "certify.lsp" :ld-error-action :error)

:ubt! 1

:set-cbd "../meta"

(ld "certify.lsp" :ld-error-action :error)

:ubt! 1

:set-cbd "../arithmetic"

(certify-book "top-with-meta" 0 nil)
