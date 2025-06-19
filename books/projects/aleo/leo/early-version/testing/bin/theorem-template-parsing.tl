(in-package "LEO")

; This book must be certified in an environment containing the Leo static
; semantics.

; This book is dependent on a Leo source file and an AST file in JSON format.
; (depends-on "${leo-source-file}")
; (depends-on "${initial-json-file}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note, the computations in the defconsts
; are run at book certification time and
; stored in the certificate for this book.

; Named constants for the Leo source file contents and its hash.
;   *source-string* is the source file bytes in UTF-8 format, one char per byte.
;   *source-hash* is a sha256 hash of the source file bytes.
(defconsts (& *source-string* *source-hash* state)
  (read-file-as-string-and-sha256 "${leo-source-file}" state))

; Named constant for the initial AST.
;   *initial-ast* is the AST converted from the JSON file.
;   *initial-ast-hash* is a sha256 hash of the JSON file bytes.
(defconsts (& *initial-ast* *initial-ast-hash* state)
  (jsonfile-to-formal-and-sha256 "${initial-json-file}" state))

; sha256sum is run on each file outside of ACL2 (at template instantiation time)
; and stored here for reference.
(defconst *leo-source-file-sha256sum* "${leo-source-file-hash}")
(defconst *initial-json-file-sha256sum* "${initial-json-file-hash}")

; Make sure the files processed by
; read-file-as-string-and-sha256 and jsonfile-to-formal-and-sha256
; have the same hashes when this book is certified as they did
; when this theorem file (this book) was instantiated / created.
(assert-event (string-equal *source-hash* *leo-source-file-sha256sum*))
(assert-event (string-equal *initial-ast-hash* *initial-json-file-sha256sum*))

; Note, consider capturing environment information, such as
; OS, cl version, acl2 version, leo-acl2 version
; E.g., (sys-call+ "git"  '("rev-parse" "--short" "HEAD") state)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Precompute address validity at book certification time, due to an issue
; with defthm and warrants.

(defconsts (*ast-addresses-valid-p*)  (ast-addresses-valid? *initial-ast*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Theorem of correct parsing.

(defthm parsing-theorem
  (b* (((mv tree lexemes) (parse-from-string+ *source-string*)))
    (and (equal (abnf::tree-list->string lexemes)
                ;; tree-list->string returns a codepoint list
                (acl2::utf8=>ustring (string=>nats *source-string*)))
         (equal (abs-file tree)
                *initial-ast*)
         ;; The leo parser is supposed to fail if an address is invalid.
         ;; This makes sure there are no invalid addresses left in the AST.
         *ast-addresses-valid-p*
         ))
  :rule-classes nil) ; don't bother to generate rewrite rules from this theorem
