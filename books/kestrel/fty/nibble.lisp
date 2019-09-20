; FTY -- Fixtype of (Unsigned 4-bit) Nibbles
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defbyte" :dir :system)

; to use the NIBBLEP recognizer in Std:
(include-book "std/basic/nibblep" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte nibble
  :size 4
  :pred nibblep
  :parents (fty::fty-extensions fty::specific-types nibblep)
  :short
  (xdoc::topstring
   "A "
   (xdoc::seetopic "fty::fty" "fixtype")
   " of "
   (xdoc::seetopic "nibblep" "(unsigned 4-bit) nibbles")
   ".")
  :long
  (xdoc::topstring-p
   "We use @(tsee fty::defbyte) to generate this fixtype,
    along with the recognizer, fixer, and equivalence.
    The recognizer is identical to @(tsee nibblep)."))
