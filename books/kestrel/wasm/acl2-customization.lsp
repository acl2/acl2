; ACL2 Customization file for this directory
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 ; load the user's ACL2 customization file, if any:
(ld "~/acl2-customization.lsp")
(ld "package.lsp")
(in-package "WASM")
(reset-prehistory)
