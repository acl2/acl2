; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OBAG")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/obags/core" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bag
  :parents (fty::fty-extensions fty::specific-types obags)
  :short
  (xdoc::topstring
   "A "
   (xdoc::seetopic "fty::fty" "fixtype")
   " of "
   (xdoc::seetopic "obag::obags" "obags")
   ".")
  :long
  (xdoc::topstring-p
   "This is similar to the fixtype @(tsee set::set) of osets.")

  (fty::deffixtype bag
    :pred bagp
    :fix bfix
    :equiv bequiv
    :define t
    :forward t))
