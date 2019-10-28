; ACL2 Standard Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "basic/top")
(include-book "strings/top")
(include-book "system/top")
(include-book "util/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std-extensions
  :parents (kestrel-books std)
  :short
  (xdoc::topstring "Extensions of "
                   (xdoc::seetopic "std" "Std")
                   " library in the "
                   (xdoc::seetopic "kestrel-books" "Kestrel Books")
                   ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "These extensions could be moved under @('[books]/std') at some point.")
   (xdoc::p
    "Some material under @('[books]/kestrel/utilities')
     consists of Std extensions,
     and thus should be moved here under @('[books]/kestrel/std')
     (and then possibly under @('[books]/std')).")))
