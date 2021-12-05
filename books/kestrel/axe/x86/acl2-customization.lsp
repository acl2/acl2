; ACL2 customization file for this directory
;
; Copyright (C) 2016-2021 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; load the user's acl2-customization.lsp, if any:
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(include-book "kestrel/x86/portcullis" :dir :system)
(in-package "X")
(reset-prehistory)
