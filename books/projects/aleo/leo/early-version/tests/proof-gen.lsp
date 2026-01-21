; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

;; Note:
;; To ld this file, in order for the relative pathnames to work,
;; you need to be in the directory of the current file
;; (i.e., in "leo-acl2/tests/") before starting ACL2.

(include-book "../testing/test-json2ast")
(include-book "../leo/canonicalization")
(include-book "../leo/type-inference")

(include-book "std/util/defconsts" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Temporarily put this file in program mode, due to json2ast.lisp being
;; in program mode.  EM 2021-08-29
(acl2::program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Make this book dependent on the json files parsed below.
; (depends-on "minimal/canon-self/outputs/initial_ast.json")
; (depends-on "minimal/canon-self/outputs/canonicalization_ast.json")
; (depends-on "minimal/canon-self/outputs/canonicalization_ast.json")
; (depends-on "minimal/compound-assignments/outputs/initial_ast.json")
; (depends-on "minimal/compound-assignments/outputs/canonicalization_ast.json")
; (depends-on "minimal/nested-arrays/outputs/initial_ast.json")
; (depends-on "minimal/nested-arrays/outputs/canonicalization_ast.json")
; (depends-on "minimal/fill-function-output-type/outputs/initial_ast.json")
; (depends-on "minimal/fill-function-output-type/outputs/canonicalization_ast.json")

; How can we regenerate those files?
; After updating leo:
;   cd minimal/canon-self ; leo clean ; leo run --enable-all-ast-snapshots
;   cd ../compound-assignments ; leo clean ; leo run --enable-all-ast-snapshots
;   cd ../nested-arrays ; leo clean ; leo run --enable-all-ast-snapshots
;   cd ../fill-function-output-type ; leo clean ; leo run --enable-all-ast-snapshots
; The preceding also creates
;   outputs/canon-self.json  <- this is the R1CS.  We check it in.  It can be
;                               a future test.
;   outputs/canon-self.{lpk,lvk,out,proof,sum}  <- right now we have these in .gitignore,
;                                                  but keep them in mind for possible future tests
; If anything we check in changed, it will show up in
;   cd ..
;   git status .

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some initial examples of proof generation.

; Although these examples are supposed to cover canonicalization,
; we add type inference checks as well just to get those started.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; see minimal/canon-self/src/main.leo

; Named constant for the initial AST.
(defconsts (& *initial-canon-self* state)
  (jsonfile-to-formal "minimal/canon-self/outputs/initial_ast.json" state))

; Named constant for the canonicalized AST.
(defconsts (& *canonicalized-canon-self* state)
  (jsonfile-to-formal "minimal/canon-self/outputs/canonicalization_ast.json" state))

; Named constant for the type inferenced AST.
(defconsts (& *type-inferenced-canon-self* state)
  (jsonfile-to-formal "minimal/canon-self/outputs/type_inferenced_ast.json" state))

; Theorem of correct canonicalization.
(defthm correctly-canonicalized--canon-self
  (file-canop *initial-canon-self*
              *canonicalized-canon-self*))

; Theorem of correct type inference
(defthm correctly-type-inferenced--canon-self
  (file-typeinfp *canonicalized-canon-self*
                 *type-inferenced-canon-self*))
;; For debugging:
;; If this fails, it might be that the following does not return NIL:
;; (file-typecheck *type-inferenced-canon-self*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; see minimal/compound-assignments/src/main.leo

; Named constant for the initial AST.
(defconsts (& *initial-compound-assignments* state)
  (jsonfile-to-formal "minimal/compound-assignments/outputs/initial_ast.json" state))

; Named constant for the canonicalized AST.
(defconsts (& *canonicalized-compound-assignments* state)
  (jsonfile-to-formal "minimal/compound-assignments/outputs/canonicalization_ast.json" state))

; Named constant for the type inferenced AST.
(defconsts (& *type-inferenced-compound-assignments* state)
  (jsonfile-to-formal "minimal/compound-assignments/outputs/type_inferenced_ast.json" state))

; Theorem of correct canonicalization.
(defthm correctly-canonicalized--compound-assignments
  (file-canop *initial-compound-assignments*
              *canonicalized-compound-assignments*))

; Theorem of correct type inference
(defthm correctly-type-inferenced--compound-assignments
  (file-typeinfp *canonicalized-compound-assignments*
                 *type-inferenced-compound-assignments*))
;; (file-typecheck *type-inferenced-coupound-assignments*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; see minimal/nested-arrays/src/main.leo

; Named constant for the initial AST.
(defconsts (& *initial-nested-arrays* state)
  (jsonfile-to-formal "minimal/nested-arrays/outputs/initial_ast.json" state))

; Named constant for the canonicalized AST.
(defconsts (& *canonicalized-nested-arrays* state)
  (jsonfile-to-formal "minimal/nested-arrays/outputs/canonicalization_ast.json" state))

; Named constant for the type inferenced AST.
(defconsts (& *type-inferenced-nested-arrays* state)
  (jsonfile-to-formal "minimal/nested-arrays/outputs/type_inferenced_ast.json" state))

; Theorem of correct canonicalization.
(defthm correctly-canonicalized--nested-arrays
  (file-canop *initial-nested-arrays*
              *canonicalized-nested-arrays*))

; Theorem of correct type inference
(defthm correctly-type-inferenced--nested-arrays
  (file-typeinfp *canonicalized-nested-arrays*
                 *type-inferenced-nested-arrays*))
;; (file-typecheck *type-inferenced-nested-arrays*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; see minimal/fill-function-output-type/src/main.leo

; Named constant for the initial AST.
(defconsts (& *initial-function-output-type* state)
  (jsonfile-to-formal "minimal/fill-function-output-type/outputs/initial_ast.json" state))

; Named constant for the canonicalized AST.
(defconsts (& *canonicalized-function-output-type* state)
  (jsonfile-to-formal "minimal/fill-function-output-type/outputs/canonicalization_ast.json" state))

; Named constant for the type inferenced AST.
(defconsts (& *type-inferenced-function-output-type* state)
  (jsonfile-to-formal "minimal/fill-function-output-type/outputs/type_inferenced_ast.json" state))

; Theorem of correct canonicalization.
(defthm correctly-canonicalized--function-output-types
  (file-canop *initial-function-output-type*
              *canonicalized-function-output-type*))

; Theorem of correct type inference
; This does not work yet.  See Leo issue #1253.
;(defthm correctly-type-inferenced--function-output-type
;  (file-typeinfp *canonicalized-function-output-type*
;                 *type-inferenced-function-output-type*))
;; (file-typecheck *type-inferenced-function-output-type*)
