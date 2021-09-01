; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/eqv" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection character-list
  :parents (fty::fty-extensions fty::specific-types maybe-stringp)
  :short "Fixtype of lists of characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The recognizer is @(tsee character-listp)
     and the fixer is @(tsee str::character-list-fix)."))
  (fty::deffixtype character-list
    :pred character-listp
    :fix str::character-list-fix
    :equiv character-list-equiv
    :define t
    :forward t))
