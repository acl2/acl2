; bls12-377-curves Library
;
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

; Effectively loads the PRIMES package.
(include-book "kestrel/number-theory/portcullis" :dir :system)

(reset-prehistory)

(in-package "PRIMES")
