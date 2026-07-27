; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/set-list" :dir :system)
(include-book "kestrel/fty/symbol-set" :dir :system)

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist symbol-set-list
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of lists of sets of symbols."
  :elt-type symbol-set
  :true-listp t
  :elementp-of-nil t
  :pred symbol-set-listp

  ///

  (defruled true-listp-when-symbol-set-listp
    (implies (symbol-set-listp x)
             (true-listp x)))

  (defruled set-listp-when-symbol-set-listp
    (implies (symbol-set-listp x)
             (set::set-listp x))
    :induct t
    :enable (symbol-set-listp set::set-listp))

  (defrule symbol-setp-of-set-list-union
    (implies (symbol-set-listp x)
             (symbol-setp (set::set-list-union x)))
    :induct t
    :enable set::set-list-union))
