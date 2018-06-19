;; Shilpi Goel

;; ======================================================================

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(set-deferred-ttag-notes t state)

(ld "cert.acl2" :ld-missing-input-ok t)
(in-package "X86ISA")

;; ======================================================================

(reset-prehistory)
