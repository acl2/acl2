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

(fty::defset string-set
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of finite sets of strings."
  :elt-type string
  :elementp-of-nil nil
  :pred string-setp
  :fix string-sfix
  :equiv string-sequiv
  ///

  (defrule stringp-of-head-when-string-setp-type-prescription
    (implies (and (string-setp x)
                  (not (set::emptyp x)))
             (stringp (set::head x)))
    :rule-classes :type-prescription)

  (defruled string-listp-when-string-setp
    (implies (string-setp x)
             (string-listp x))
    :enable string-setp))
