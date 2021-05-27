;; load the user's acl2-customization.lsp, if any:
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(ld "../../number-theory/package.lsp")
(reset-prehistory)
(in-package "PRIMES")
