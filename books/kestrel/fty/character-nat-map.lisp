; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "any-nat-map")
(include-book "character-any-map")

(include-book "kestrel/fty/defomap" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap character-nat-map
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of omaps from characters to natural numbers."
  :key-type character
  :val-type nat
  :pred character-nat-mapp
  :fix character-nat-mfix
  :equiv character-nat-mequiv

  ///

  (defruled any-nat-mapp-when-character-nat-mapp
    (implies (character-nat-mapp map)
             (any-nat-mapp map))
    :induct (character-nat-mapp map)
    :enable (character-nat-mapp any-nat-mapp))

  (defruled character-any-mapp-when-character-nat-mapp
    (implies (character-nat-mapp map)
             (character-any-mapp map))
    :induct (character-nat-mapp map)
    :enable (character-nat-mapp character-any-mapp)))
