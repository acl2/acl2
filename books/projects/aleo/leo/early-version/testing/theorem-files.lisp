; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Theorem Generator: make-theorem-file

;; Current theorem file templates are in
;;   bin/theorem-template-parsing.tl
;; XXXout of dateXXX  bin/theorem-template-canonicalization.tl
;; XXXout of dateXXX  bin/theorem-template-type-inference.tl

;; See also
;;   batch-theorems.lisp

;; After doing
;;   cd leo
;;   cargo build --release
;;   cd compiler/parser
;;   cargo install --path . --example parser
;;   cd /path/to/source-files
;;   sha256sum source.leo
;; Record the sha256 hash.
;;   parser source.leo
;; That should cause /path/to/source-files/source.json to be created.
;;   parser source.json
;; Record this sha256 hash, too.
;;
;; Then, in ACL2 do:
;;   (make-theorem-file "/path/to/leo-acl2/testing/bin/theorem-template-parsing.tl"
;;     "/path/to/source-files/parsing-theorem.lisp"
;;     ;; Note, the following amap car strings must be in *tgc-stage-arguments*
;;     '(("leo-source-file" . "/path/to/source-files/source.leo")
;;       ("leo-source-file-hash" . "2acb148f279a15690749103f044672ceb84895f3f23e3e250711dfd06c61cb19")
;;       ("initial-json-file" . "/path/to/source-files/source.json")
;;       ("initial-json-file-hash" . "1cd25c6f38c61e4d103d00dd5974bb1be3a5b3769307c30cf6ac2620cfe465f3"))
;;     state)

#||
To make those instructions concrete (as of 2022-05-19)
(you might be able to just replace "batman" by your homedir):

  cd /home/batman/leo/tests/compiler/function
  sha256sum return.leo
  parser return.leo
  sha256sum return.json

cd to your leo-acl2 directory and start ACL2:

LEO !>
  (include-book
     "working")  ; These are on separate lines so as not to confuse book dependency analyzer.
                 ; Later, we will want a smaller set of books than "working"
                 ; because we would like to certify-book without any trust tags.
  (make-theorem-file
   "/home/batman/leo-acl2/testing/bin/theorem-template-parsing.tl"
   "/home/batman/leo/tests/compiler/function/return-parsing-theorem.lisp"
   '(("leo-source-file" . "/home/batman/leo/tests/compiler/function/return.leo")
     ("leo-source-file-hash" . "2acb148f279a15690749103f044672ceb84895f3f23e3e250711dfd06c61cb19")
     ("initial-json-file" . "/home/batman/leo/tests/compiler/function/return.json")
     ("initial-json-file-hash" . "1cd25c6f38c61e4d103d00dd5974bb1be3a5b3769307c30cf6ac2620cfe465f3"))
   state)
  (certify-book "/home/batman/leo/tests/compiler/function/return-parsing-theorem" ? t :ttags :all)

; Note,
; We should quantify which ttags we need.
; I think we can make the certification environment be ttag-free, as it was previoulsy
; with tgc for canonicalization and type-checking

||#


;; XXXout of dateXXX:
;; Example.
;; After doing:
;;   cd leo
;;   cargo run -p leo-test-framework --bin tgc -- -f compiler_tuples_destructured
;; You can call something like this to check canonicalization:
;;   (make-theorem-file "/path/to/leo-acl2/testing/bin/theorem-template-canonicalization.tl"
;;     "/path/to/leo/tmp/tgc/compiler_tuples_destructured.leo_574/canonicalization-theorem.lisp"
;;     ;; Note, the following amap car strings must be in *tgc-stage-arguments*
;;     '(("initial-json-file" . "/path/to/leo/tmp/tgc/compiler_tuples_destructured.leo_574/initial_ast.json")
;;       ("canonicalization-json-file" . "/path/to/leo/tmp/tgc/compiler_tuples_destructured.leo_574/canonicalization_ast.json")
;;       ("initial-json-file-hash" . "ea7f6cc8c9fe0deda02c3fde1f33dd71c33b6938c832af0f220fb681f56f9354")
;;       ("canonicalization-json-file-hash" . "ea7f6cc8c9fe0deda02c3fde1f33dd71c33b6938c832af0f220fb681f56f9354"))
;;       ;; Note, if no canonicalization was needed, the hashes can be the same.
;;     state)
;; or something like this to check type inference:
;;   (make-theorem-file "/path/to/leo-acl2/testing/bin/theorem-template-type-inference.tl"
;;     "/path/to/leo/tmp/tgc/compiler_tuples_destructured.leo_574/type-inference-theorem.lisp"
;;     '(("canonicalization-json-file" . "/path/to/leo/tmp/tgc/compiler_tuples_destructured.leo_574/canonicalization_ast.json")
;;       ("type-inferenced-json-file" . "/path/to/leo/tmp/tgc/compiler_tuples_destructured.leo_574/type_inferenced_ast.json")
;;       ("canonicalization-json-file-hash" . "ea7f6cc8c9fe0deda02c3fde1f33dd71c33b6938c832af0f220fb681f56f9354")
;;       ("type-inferenced-json-file-hash" . "72d9dedc48ac69de544b2f35b1f0e675f4053f562fc708b30eebcfdc6ac59dc9"))
;;     state)

;; Note on relative vs absolute pathnames:
;; Any relative input file names will be relative to the PWD when ACL2 was started.
;; So if you cd to /path/to/leo/tmp/tgc/compiler_tuples_destructured.leo_574
;; and then start ACL2, the previous call could be
;;   (make-theorem-file "/path/to/leo-acl2/testing/bin/theorem-template-type-inference.tl"
;;     "type-inference-theorem.lisp"
;;     '(("canonicalization-json-file" . "canonicalization_ast.json")
;;       ("type-inferenced-json-file" . "type_inferenced_ast.json")
;;       ("canonicalization-json-file-hash" . "ea7f6cc8c9fe0deda02c3fde1f33dd71c33b6938c832af0f220fb681f56f9354")
;;       ("type-inferenced-json-file-hash" . "72d9dedc48ac69de544b2f35b1f0e675f4053f562fc708b30eebcfdc6ac59dc9"))
;;     state)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "std/util/bstar" :dir :system)
(include-book "std/io/read-file-lines" :dir :system)
(include-book "std/strings/strsubst" :dir :system)
(include-book "kestrel/file-io-light/write-strings-to-file" :dir :system)

;; This include-book is for the benefit of certifying the generated theorem files,
;; which use defconsts.
(include-book "std/util/defconsts" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-state-ok t)

;; t-binds is an alist from template var string to template value string.
;; In the template, a template var is enclosed with "${}".
(defun make-string-substitutions (string-list t-binds)
  (b* (((when (endp t-binds))
        string-list)
       (strings-with-subst
        (str::strsubst-list (concatenate 'string "${" (car (first t-binds)) "}") (cdr (first t-binds)) string-list)))
    (make-string-substitutions strings-with-subst (cdr t-binds))))


;; tgc requires that the theorem file be an absolute path.
;; See defmacro tgc in batch-theorems.lisp for discussion.
;; This function itself doesn't really care; if a file name argument is relative
;; it will be relative to $PWD (the current directory when ACL2 was started).
;; For each pair (TEMPLATE-VAR . TEMPLATE-VAL) in t-binds, makes the substitutions
;; in theorem-template-file and writes the result out to theorem-file-to-make.
(defun make-theorem-file (theorem-template-file
                          theorem-file-to-make
                          t-binds
                          state)
  (b* (((mv strings0 state)
        (acl2::read-file-lines theorem-template-file state))
       (result-strings (make-string-substitutions strings0 t-binds)))
    (acl2::write-strings-to-file result-strings theorem-file-to-make 'top-level state)))
