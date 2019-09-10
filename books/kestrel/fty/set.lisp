; FTY -- Fixtype of Osets
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set
  :parents (fty::fty-extensions fty::specific-types std/osets)
  :short
  (xdoc::topstring "A "
                   (xdoc::seetopic "fty::fty" "fixtype")
                   " of "
                   (xdoc::seetopic "std/osets" "osets")
                   ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "The fixing function used here is @(tsee sfix).")
   (xdoc::p
    "The name @('sequiv') of the equivalence relation introduced here
     is ``structurally similar'' to
     the name @('sfix') of the fixing function."))

  (fty::deffixtype set
    :pred setp
    :fix sfix
    :equiv sequiv
    :define t
    :forward t))
