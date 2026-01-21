; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; load the user's acl2-customization.lsp, if any:
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(include-book "kestrel/crypto/blake/portcullis" :dir :system)
(include-book "kestrel/crypto/ecurve/portcullis" :dir :system)
(include-book "kestrel/crypto/r1cs/portcullis" :dir :system)
(include-book "projects/poseidon/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)

(in-package "R1CS")

(set-fmt-soft-right-margin 200 state)
(set-fmt-hard-right-margin 200 state)
