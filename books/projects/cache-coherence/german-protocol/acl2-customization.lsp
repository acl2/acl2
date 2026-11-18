; This file is not part of the original "cache-coherence/german-protocol"
; project.  We added it to resolve a name conflict by wrapping the project in
; its own package.

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(ld "package.lsp")

(reset-prehistory)

(in-package "CACHE-COHERENCE/GERMAN-PROTOCOL")
