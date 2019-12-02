; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "conjoin")
(include-book "event-name-queries")
(include-book "function-queries")
(include-book "included-books")
(include-book "known-packages")
(include-book "known-packages-plus")
(include-book "logic-friendly")
(include-book "macro-queries")
(include-book "rune-disabledp")
(include-book "rune-enabledp")
(include-book "table-alist-plus")
(include-book "term-function-recognizers")
(include-book "term-queries")
(include-book "term-transformations")
(include-book "theorem-queries")
(include-book "unquote-term")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system
  :parents (std-extensions std)
  :short
  (xdoc::topstring
   "A library that complements the "
   (xdoc::seetopic "system-utilities" "built-in system utilities")
   " with theorems and with non-built-in system utilities.")
  :long
  (xdoc::topstring
   (xdoc::p
    "These could be moved under @('[books]/std') at some point.")))
