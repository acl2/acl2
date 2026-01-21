;; load the user's acl2-customization.lsp, if any:
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
;(include-book "projects/x86isa/portcullis/sharp-dot-constants" :dir :system)
(include-book "kestrel/x86/portcullis" :dir :system)
(in-package "X")
(reset-prehistory)
