; ACL2 customization file
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; load the user's acl2-customization.lsp, if any
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(include-book "../../../prime-fields/portcullis")
(reset-prehistory)
(in-package "PFIELD")
