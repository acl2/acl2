; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "system/top" :dir :system)

(include-book "acceptable-rewrite-rule-p")
(include-book "add-suffix-lst")
(include-book "add-suffix-to-fn-lst")
(include-book "add-suffix-to-fn-or-const")
(include-book "add-suffix-to-fn-or-const-lst")
(include-book "arglistp")
(include-book "constant-queries")
(include-book "enhanced-utilities")
(include-book "event-landmark-names")
(include-book "event-name-queries")
(include-book "fresh-logical-name-with-dollars-suffix")
(include-book "function-queries")
(include-book "genvar-dollar")
(include-book "getprops")
(include-book "included-books")
(include-book "install-not-normalized-dollar")
(include-book "install-not-normalized-event")
(include-book "invariant-risk")
(include-book "irrelevant-formals")
(include-book "known-packages")
(include-book "known-packages-plus")
(include-book "macro-queries")
(include-book "maybe-pseudo-event-formp")
(include-book "non-parallel-book")
(include-book "partition-rest-and-keyword-args")
(include-book "plist-worldp-with-formals")
(include-book "pseudo-command-landmark-listp")
(include-book "pseudo-event-form-fix")
(include-book "pseudo-event-form-listp")
(include-book "pseudo-event-formp")
(include-book "pseudo-event-landmark-listp")
(include-book "pseudo-tests-and-call-listp")
(include-book "pseudo-tests-and-callp")
(include-book "rune-disabledp")
(include-book "rune-enabledp")
(include-book "table-alist-plus")
(include-book "term-function-recognizers")
(include-book "term-queries")
(include-book "term-transformations")
(include-book "theorem-queries")
(include-book "unquote-term")
(include-book "w")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system
  :parents (std)
  :short
  (xdoc::topstring
   "A library that complements the "
   (xdoc::seetopic "system-utilities" "built-in system utilities")
   " with theorems and with non-built-in system utilities.")
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a start towards a comprehensive library.
     Some candidate utilities are under @(see community-book)
     @('kestrel/std').")))
