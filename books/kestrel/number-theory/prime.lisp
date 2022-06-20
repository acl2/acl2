; Number Theory Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RTL")

(include-book "prime-fix")

(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection prime
  :short "Fixtype of prime numbers."
  :parents (acl2::number-theory)
  (fty::deffixtype prime
    :pred primep
    :fix prime-fix
    :equiv prime-equiv
    :define t
    :forward t))
