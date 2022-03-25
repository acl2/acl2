; FTY Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/std/system/pseudo-event-form-fix" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pseudo-event-form
  :parents (fty::fty-extensions fty::specific-types pseudo-event-formp)
  :short "Fixtype of pseudo event forms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The recognizer is @(tsee pseudo-event-formp)
     and the fixer is @(tsee pseudo-event-form-fix)."))
  (fty::deffixtype pseudo-event-form
    :pred pseudo-event-formp
    :fix pseudo-event-form-fix
    :equiv pseudo-event-form-equiv
    :define t
    :forward t))
