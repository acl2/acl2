; FTY -- Fixtype of True Lists of (Unsigned 4-bit) Nibbles
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defbytelist" :dir :system)

(include-book "nibble")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbytelist nibble-list
  :elt-type nibble
  :pred nibble-listp
  :parents (fty::fty-extensions fty::specific-types nibble)
  :short
  (xdoc::topstring
   "A "
   (xdoc::seetopic "fty::fty" "fixtype")
   " of true lists of "
   (xdoc::seetopic "nibblep" "(unsigned 4-bit) nibbles")
   ".")
  :long
  (xdoc::topstring-p
   "We use @(tsee fty::defbytelist) to generate this fixtype,
    along with the recognizer, fixer, and equivalence."))
