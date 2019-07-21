; ACL2 Standard Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std-extensions
  :parents (kestrel-books std)
  :short
  (xdoc::topstring "Extensions of "
                   (xdoc::seeurl "std" "Std")
                   " library in the "
                   (xdoc::seeurl "kestrel-books" "Kestrel Books")
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
