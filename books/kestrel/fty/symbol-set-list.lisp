; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

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
             (true-listp x))))
