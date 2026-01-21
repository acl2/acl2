(in-package "LEO")

; This book must be certified in an environment containing the Leo static
; semantics.

; This book is dependent on the before and after json files.
; (depends-on "${initial-json-file}")
; (depends-on "${canonicalization-json-file}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Named constant for the initial AST.
(defconsts (& *initial-leo-ast* *initial-hash* state)
  (jsonfile-to-formal-and-sha256 "${initial-json-file}" state))

; Named constant for the AST after canonicalization.
(defconsts (& *canonicalized-leo-ast* *canonicalized-hash* state)
  (jsonfile-to-formal-and-sha256 "${canonicalization-json-file}" state))

; sha256sum is run on each file and stored here for reference
(defconst *initial-file-sha256sum* "${initial-json-file-hash}")
(defconst *canonicalized-file-sha256sum* "${canonicalization-json-file-hash}")

; Make sure the file parsed by jsonfile-to-formal-and-sha256
; has the same hash as it did when this theorem file was created.
(assert-event (string-equal *initial-hash* *initial-file-sha256sum*))
(assert-event (string-equal *canonicalized-hash* *canonicalized-file-sha256sum*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Theorem of correct canonicalization.

(defthm canonicalization-theorem
  (file-canop *initial-leo-ast*
              *canonicalized-leo-ast*))
