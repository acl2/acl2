; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "bin-digit-char-listp")
(include-book "char-kinds")
(include-book "dec-digit-char-listp")
(include-book "decimal-fty")
(include-book "explode-implode-equalities")
(include-book "hex-digit-char-listp")
(include-book "oct-digit-char-listp")
(include-book "strtok-bang")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/strings-extensions
  :parents (acl2::std-extensions std/strings)
  :short
  (xdoc::topstring "Extensions of "
                   (xdoc::seetopic "std/strings" "Std/strings")
                   " in the "
                   (xdoc::seetopic "acl2::kestrel-books" "Kestrel Books")
                   ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "These extensions could be moved under @('std/strings')
     at some point.")))
