; ACL2 customization file for this directory
;
; Copyright (C) 2017-2022 Kestrel Technology, LLC
; Copyright (C) 2023-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; load the user's acl2-customization.lsp, if any
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(include-book "kestrel/axe/arm/portcullis" :dir :system)
(in-package "A")
(reset-prehistory)
