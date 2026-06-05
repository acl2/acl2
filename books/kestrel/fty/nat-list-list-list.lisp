; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "nat-list-list")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist nat-list-list-list
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of lists of lists of lists of natural numbers."
  :elt-type nat-list-list
  :true-listp t
  :elementp-of-nil t
  :pred nat-list-list-listp

  ///

  (defrule nat-list-list-listp-of-repeat
    (equal (nat-list-list-listp (repeat n x))
           (or (zp n) (nat-list-listp x)))
    :induct t
    :enable repeat)

  (defruled true-list-listp-when-nat-list-list-listp
    (implies (nat-list-list-listp x)
             (true-list-listp x))
    :induct t))
