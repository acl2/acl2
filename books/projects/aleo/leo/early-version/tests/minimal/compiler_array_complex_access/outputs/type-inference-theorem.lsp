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

; Most of the work to make this work is done, it just needs to be enabled for
; the current location:
;(include-book "test-json2ast" :dir :aleo-acl2)
;(include-book "leo/type-inference" :dir :aleo-acl2)

(include-book "../../../../testing/test-json2ast")
(include-book "../../../../leo/type-inference")
(include-book "std/util/defconsts" :dir :system)

; Make this book dependent on the json files parsed below.
; (depends-on "canonicalization_ast.json")
; (depends-on "type_inferenced_ast.json")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Put ASTs in constants.

; Named constant for the canonicalized AST.
(defconsts (& *canonicalized-leo-ast* state)
  (jsonfile-to-formal "canonicalization_ast.json" state))

; Named constant for the type inferenced AST.
(defconsts (& *type-inferenced-leo-ast* state)
  (jsonfile-to-formal "type_inferenced_ast.json" state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Theorem of correct type inference

(defthmd type-inferenced-theorem
  (file-typeinfp *canonicalized-leo-ast*
                 *type-inferenced-leo-ast*))
