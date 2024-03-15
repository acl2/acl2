; FTY Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset pos-set
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of finite sets of positive integers."
  :elt-type pos
  :elementp-of-nil nil
  :pred pos-setp
  :fix pos-sfix
  :equiv pos-sequiv
  ///

  (defrule posp-of-head-when-pos-setp-type-prescription
    (implies (and (pos-setp x)
                  (not (set::emptyp x)))
             (posp (set::head x)))
    :rule-classes :type-prescription))
