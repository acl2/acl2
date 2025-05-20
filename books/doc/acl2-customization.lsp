; ACL2 Customization file for this directory
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Loads the user's acl2-customization.lsp, if any:
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

;; Brings in the PUBLICATIONS package:
(ld "publications.acl2")
