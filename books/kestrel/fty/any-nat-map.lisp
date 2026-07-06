; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "nat-set")

(include-book "kestrel/fty/defomap" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap any-nat-map
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of omaps from anything to natural numbers."
  :key-type any
  :val-type nat
  :pred any-nat-mapp
  :fix any-nat-mfix
  :equiv any-nat-mequiv

  ///

  (defruled nat-setp-of-values-when-any-nat-mapp
    (implies (any-nat-mapp map)
             (nat-setp (omap::values map)))
    :induct t
    :enable omap::values))
