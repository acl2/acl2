; Kestrel Books
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book includes all definitions, theorems, tools, etc. in the Kestrel
;; Books.  Its main use is to check for conflicts within the Kestrel books and
;; with other libraries.

(include-book "abnf/top")
;; (include-book "abnf/examples") ; they have XDOC topics for the manual
(include-book "acl2pl/top")
(include-book "algorithm-theories/top")
(include-book "apt/top")
(include-book "axe/top")
(include-book "arithmetic-light/top")
(include-book "bv/top")
(in-theory (disable collect-constants-<-/ collect-constants-<-/-two)) ; avoid theory-invariant errors in books that include this book
(include-book "auto-termination/top") ; omits some books (see file for why)
(include-book "bitcoin/top")
;; (include-book "built-in-theorems-doc")
(include-book "c/top")
(merge-io-pairs
 rtl::primep
 (include-book "crypto/top"))
(include-book "error-checking/top")
(include-book "event-macros/top")
(include-book "hdwallet/top")
(include-book "ethereum/top")
(include-book "file-io-light/top")
(include-book "fty/top")
(include-book "isar/top")
(include-book "java/top")
(include-book "json/top")
;(include-book "lists-light/top") ; TODO: Name clash on take-opener
(include-book "number-theory/top")
(include-book "prime-fields/top")
(include-book "simpl-imp/top")
(include-book "soft/top")
(include-book "solidity/top")
(include-book "std/top")
(include-book "strings-light/top")
;; (include-book "typed-lists-light/top") ; TODO: Name clash on perm
(include-book "unicode-light/top")
(include-book "utilities/top")
(include-book "x86/top")
(include-book "zcash/top")
