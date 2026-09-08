; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "string-set")

(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-string-map
  :parents (fty::specific-types)
  :short "Fixtype of omaps from strings to strings."
  :key-type string
  :val-type string
  :pred string-string-mapp

  ///

  (defrule string-string-mapp-of-from-lists
    (implies (and (equal (len keys) (len vals))
                  (string-listp keys)
                  (string-listp vals))
             (string-string-mapp (omap::from-lists keys vals)))
    :induct t
    :enable (omap::from-lists string-listp))

  (defruled string-setp-of-values-when-string-string-mapp
    (implies (string-string-mapp map)
             (string-setp (omap::values map)))
    :enable omap::values))
