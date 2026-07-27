; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/symbol-set-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist symbol-set-list-list
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of lists of lists of sets of symbols."
  :elt-type symbol-set-list
  :true-listp t
  :elementp-of-nil t
  :pred symbol-set-list-listp

  ///

  (defruled true-listp-when-symbol-set-list-listp
    (implies (symbol-set-list-listp x)
             (true-listp x))))
