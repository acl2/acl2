; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

; This directory has no local package.lsp; the books here use the JSONRPC and
; C (C, C$, C2C) packages from the following portcullis books (cf. cert.acl2).
(include-book "kestrel/jsonrpc/portcullis" :dir :system)
(include-book "kestrel/c/transformation/portcullis" :dir :system)

(reset-prehistory)

(in-package "C2C")
