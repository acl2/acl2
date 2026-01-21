(in-package "LEO")

; This book must be certified in an environment containing the Leo static
; semantics.

; This book is dependent on the before and after json files.
; (depends-on "${canonicalization-json-file}")
; (depends-on "${type-inferenced-json-file}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Named constant for the AST after canonicalization.
(defconsts (& *canonicalized-leo-ast* *canonicalized-hash* state)
  (jsonfile-to-formal-and-sha256 "${canonicalization-json-file}" state))

; Named constant for the AST after type inference.
(defconsts (& *type-inferenced-leo-ast* *type-inferenced-hash* state)
  (jsonfile-to-formal-and-sha256 "${type-inferenced-json-file}" state))

; sha256sum is run on each file and stored here for reference
(defconst *canonicalized-file-sha256sum* "${canonicalization-json-file-hash}")
(defconst *type-inferenced-file-sha256sum* "${type-inferenced-json-file-hash}")

; Make sure the file parsed by jsonfile-to-formal-and-sha256
; has the same hash as it did when this theorem file was created.
(assert-event (string-equal *canonicalized-hash* *canonicalized-file-sha256sum*))
(assert-event (string-equal *type-inferenced-hash* *type-inferenced-file-sha256sum*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Theorem of correct type inference

(defthm type-inferenced-theorem
  (file-typexinfp *canonicalized-leo-ast*
                  *type-inferenced-leo-ast*))
