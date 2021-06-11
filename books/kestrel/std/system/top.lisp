; Standard System Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "add-suffix-to-fn-or-const")
(include-book "arglistp")
(include-book "enhanced-utilities")
(include-book "event-landmark-names")
(include-book "event-name-queries")
(include-book "fresh-logical-name-with-dollars-suffix")
(include-book "function-queries")
(include-book "getprops")
(include-book "included-books")
(include-book "install-not-normalized-dollar")
(include-book "install-not-normalized-event")
(include-book "known-packages")
(include-book "known-packages-plus")
(include-book "macro-queries")
(include-book "maybe-pseudo-event-formp")
(include-book "plist-worldp-with-formals")
(include-book "pseudo-command-landmark-listp")
(include-book "pseudo-event-form-listp")
(include-book "pseudo-event-formp")
(include-book "pseudo-event-landmark-listp")
(include-book "pseudo-tests-and-callp")
(include-book "pseudo-tests-and-call-listp")
(include-book "rune-disabledp")
(include-book "rune-enabledp")
(include-book "table-alist-plus")
(include-book "term-function-recognizers")
(include-book "term-queries")
(include-book "term-transformations")
(include-book "theorem-queries")
(include-book "unquote-term")
(include-book "w")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system-extensions
  :parents (std-extensions std/system)
  :short
  (xdoc::topstring "Extensions of "
                   (xdoc::seetopic "std/system" "Std/system")
                   " in the "
                   (xdoc::seetopic "acl2::kestrel-books" "Kestrel Books")
                   ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "These extensions could be moved under @('[books]/std/system')
     at some point.")))
