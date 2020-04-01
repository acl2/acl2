; Standard Strings Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "char-kinds")
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
    "These extensions could be moved under @('[books]/std/strings')
     at some point.")))
