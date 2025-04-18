(include-book "top")     ;; load the embedding's ACL2s book
:q                       ;; quit into raw lisp
(load "api.lsp")  ;; Load the backend module, which contains the API
(in-package :acl2s-python-types)       ;; "acl2s-python-types" is the name of the API package

(defvar *enum-random-state*)  ;; create variable to hold random state
(setf *enum-random-state* (make-cl-seed 1)) ;; Set seed

;; Generate 100 examples of floats
(generate-examples "float" 100 *enum-random-state*)

;; Register a union between integers, floats, and strings called intfloatstr
(register-union "intfloatstr" '("int" "float" "str"))

;; Generate 100 examples of intfloatstr
(generate-examples "intfloatstr" 100 *enum-random-state*)
