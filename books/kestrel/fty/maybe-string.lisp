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
(include-book "kestrel/std/basic/maybe-string-fix" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection maybe-string
  :parents (fty::fty-extensions fty::specific-types maybe-stringp)
  :short "Fixtype of optional strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "The recognizer is @(tsee maybe-stringp)
     and the fixer is @(tsee maybe-string-fix)."))
  (fty::deffixtype maybe-string
    :pred maybe-stringp
    :fix maybe-string-fix
    :equiv maybe-string-equiv
    :define t
    :forward t))
