; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset nat-set
  :parents (natp)
  :short "Fixtype of finite sets of natural numbers."
  :elt-type nat
  :elementp-of-nil nil
  :pred nat-setp
  :fix nat-sfix
  :equiv nat-sequiv
  ///

  (defrule natp-of-head-when-nat-setp-type-prescription
    (implies (and (nat-setp x)
                  (not (set::empty x)))
             (natp (set::head x)))
    :rule-classes :type-prescription))
