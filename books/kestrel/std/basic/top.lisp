; Std/basic - Basic definitions
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-package-name-lst")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/basic-extensions
  :parents (std-extensions std/basic)
  :short
  (xdoc::topstring "Extensions of "
                   (xdoc::seeurl "std/basic" "Std/basic")
                   " in the "
                   (xdoc::seeurl "kestrel-books" "Kestrel Books")
                   ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "These extension could be moved under @('[books]/std/basic')
     at some point.")))
