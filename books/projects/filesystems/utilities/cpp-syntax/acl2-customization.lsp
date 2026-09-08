; C++ Syntax Extension
;
; ACL2 customization file for the cpp-syntax directory.
; Auto-loaded by ACL2 when it starts in this directory.
; Sets up the CPP package and switches to it.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(ld "package.lsp")

(reset-prehistory)

(in-package "CPP")
