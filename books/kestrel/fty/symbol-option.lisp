; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum symbol-option
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of optional symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since @('nil') is a symbol,
     @(tsee fty::defoption) cannot represent the absence of a symbol;
     so this is an explicit sum type."))
  (:some ((val symbol)))
  (:none ())
  :pred symbol-optionp)
