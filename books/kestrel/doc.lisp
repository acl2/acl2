; Documentation for the Kestrel Books
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book gathers all xdoc topics that we want to contribute to the manual.

(include-book "abnf/top")
(include-book "abnf/examples") ; they have XDOC topics for the manual
(include-book "acl2pl/top")
(include-book "apt/doc")
(include-book "axe/doc")
(include-book "arithmetic-light/doc")
(include-book "bv/doc")
(include-book "auto-termination/top") ; omits some books (see file for why)
(include-book "bitcoin/top")
(include-book "built-in-theorems-doc")
(include-book "c/top")
(merge-io-pairs
 rtl::primep
 (include-book "crypto/top"))
(include-book "error-checking/top")
(include-book "event-macros/top")
(include-book "hdwallet/top")
(include-book "ethereum/top")
(include-book "file-io-light/doc")
(include-book "fty/top")
(include-book "isar/top")
(include-book "java/top")
(include-book "json/top")
(include-book "lists-light/doc")
(include-book "number-theory/top")
(include-book "prime-fields/doc")
(include-book "simpl-imp/top")
(include-book "soft/top")
(include-book "solidity/top")
(include-book "std/top")
(include-book "strings-light/doc")
(include-book "typed-lists-light/doc")
(include-book "utilities/top")
(include-book "zcash/top")

; (depends-on "images/kestrel-logo.png")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc kestrel-books

  :parents (software-verification)

  :short "A collection of ACL2 books contributed mainly by Kestrel Institute."

  :long

  (xdoc::topstring

   (xdoc::img :src "res/kestrel-images/kestrel-logo.png")

   (xdoc::p
    "The <b>Kestrel Books</b> are a collection of ACL2 books
     contributed mainly by "
    (xdoc::a :href "http://www.kestrel.edu" "Kestrel Institute")
    ". The Kestrel Books are freely available under a liberal license.
     Specific copyright, author, and license information
     is provided in the individual files and subdirectories.")

   (xdoc::p
    "As they become more stable,
     parts of the Kestrel Books may be moved
     to other locations in the "
    (xdoc::seetopic "community-books" "Community Books")
    ". For example, "
    (xdoc::seetopic "std" "STD")
    " and "
    (xdoc::seetopic "x86isa" "X86ISA")
    " include some Kestrel contributions.")

   (xdoc::p
    "Many of the Kestrel Books build upon,
     and are meant to extend and be compatible with,
     the ACL2 system code
     and various existing libraries such as "
    (xdoc::seetopic "std" "STD") ", "
    (xdoc::seetopic "fty" "FTY") ", "
    (xdoc::seetopic "seq" "Seq") ", and others.")))

(xdoc::add-resource-directory "kestrel-images" "images")

(xdoc::add-resource-directory "kestrel-design-notes" "design-notes")
