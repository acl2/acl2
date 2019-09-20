; FTY -- Fixtype of Omaps
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/utilities/omaps/core" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection map
  :parents (fty::fty-extensions fty::specific-types omaps)
  :short
  (xdoc::topstring
   "A "
   (xdoc::seetopic "fty::fty" "fixtype")
   " of "
   (xdoc::seetopic "omap::omaps" "omaps")
   ".")
  :long
  (xdoc::topstring-p
   "This is similar to the fixtype @(tsee set::set) of osets.")

  (fty::deffixtype map
    :pred mapp
    :fix mfix
    :equiv mequiv
    :define t
    :forward t))
