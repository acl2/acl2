;; load the user's acl2-customization.lsp, if any
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
;(include-book "../../primes/portcullis")
(include-book "../portcullis")
(reset-prehistory)
(in-package "R1CS")
