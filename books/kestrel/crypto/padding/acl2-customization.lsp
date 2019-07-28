;; load the user's acl2-customization.lsp, if any
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(ld "package.lsp")
(reset-prehistory)
(in-package "PADDING")
