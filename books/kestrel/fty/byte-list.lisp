; FTY -- Fixtype of True Lists of (Unsigned 8-bit) Bytes
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defbytelist" :dir :system)

(include-book "byte")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbytelist byte-list
  :elt-type byte
  :pred byte-listp
  :parents (fty::fty-extensions fty::specific-types byte)
  :short
  (xdoc::topstring
   "A "
   (xdoc::seetopic "fty::fty" "fixtype")
   " of true lists of "
   (xdoc::seetopic "bytep" "(unsigned 8-bit) bytes")
   ".")
  :long
  (xdoc::topstring-p
   "We use @(tsee fty::defbytelist) to generate this fixtype,
    along with the recognizer, fixer, and equivalence."))
