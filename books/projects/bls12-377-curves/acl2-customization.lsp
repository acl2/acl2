; bls12-377-curves Library
;
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

; Effectively loads the CRYPTO package.
(include-book "kestrel/crypto/portcullis" :dir :system)

(reset-prehistory)

(in-package "CRYPTO")
