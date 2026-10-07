; ACL2 customization file for this directory
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(include-book "../../portcullis") ; for the "ARM" package

(reset-prehistory)

(in-package "ARM")
