; Kestrel Books
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book includes all definitions, theorems, tools, etc. in the Kestrel
;; Books.  Its main use is to check for conflicts within the Kestrel books and
;; with other libraries.

(include-book "acl2pl/top")
(include-book "algorithm-theories/top")
(include-book "apt/top")
(include-book "axe/top")
(include-book "arithmetic-light/top")
(include-book "built-ins/top")
(include-book "bv/top")
(in-theory (disable <-of-*-of-constant-and-constant <-of-constant-and-*-of-constant)) ; avoid theory-invariant errors in books that include this book
(include-book "auto-termination/top") ; omits some books (see file for why)
(include-book "bitcoin/top")
(include-book "c/top")
(merge-io-pairs
 dm::primep
 (include-book "crypto/top"))
(include-book "csv/parse-csv-file")
(include-book "error-checking/top")
(include-book "evaluators/top")
(include-book "event-macros/top")
(include-book "hdwallet/top")
;; (include-book "helpers/top") ;; TODO: Uncomment when stable
(include-book "ethereum/top")
(include-book "file-io-light/top")
(include-book "floats/top")
(include-book "fty/top")
(include-book "hints/top")
(include-book "isar/top")
(include-book "java/top")
;; (include-book "jvm/top")  ;; TODO: Uncomment when stable
(include-book "json/top")
(include-book "htclient/top")
(include-book "lists-light/top")
(include-book "number-theory/top")
(include-book "prime-fields/top")
(include-book "risc-v/top")
(include-book "simpl-imp/top")
(include-book "soft/top")
(include-book "solidity/top")
(include-book "strings-light/top")
(include-book "treeset/top")
;; (include-book "typed-lists-light/top") ; TODO: Name clash on perm
(include-book "syntheto/top")
(include-book "unicode-light/top")
(include-book "utilities/top")
(include-book "world-light/top")
(include-book "x86/top")
(include-book "yul/top")
(include-book "zcash/top")
