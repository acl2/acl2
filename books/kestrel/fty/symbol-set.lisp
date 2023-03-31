; FTY Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defset" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset symbol-set
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of finite sets of symbols."
  :elt-type symbol
  :elementp-of-nil t
  :pred symbol-setp
  :fix symbol-sfix
  :equiv symbol-sequiv
  ///

  (defrule symbolp-of-head-when-symbol-setp-type-prescription
    (implies (and (symbol-setp x)
                  (not (set::empty x)))
             (symbolp (set::head x)))
    :rule-classes :type-prescription))
