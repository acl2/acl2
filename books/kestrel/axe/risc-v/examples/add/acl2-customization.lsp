; ACL2 customization file for this dir
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; load the user's acl2-customization.lsp, if any:
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(include-book "kestrel/risc-v/portcullis" :dir :system)
(include-book "kestrel/axe/risc-v/portcullis" :dir :system)

(in-package "R")

(reset-prehistory)
