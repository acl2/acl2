; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defomap" :dir :system)
(include-book "kestrel/fty/character-set" :dir :system)
(include-book "std/omaps/identity" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap character-any-map
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of omaps from characters to anything."
  :key-type character
  :val-type any
  :pred character-any-mapp
  :fix character-any-mfix
  :equiv character-any-mequiv

  ///

  (defrule character-any-mapp-of-identity-when-character-setp
    (implies (character-setp keys)
             (character-any-mapp (omap::identity keys)))
    :induct t
    :enable omap::identity))
