; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "kestrel/fty/set" :dir :system)

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist set-list
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of lists of sets."
  :elt-type set
  :true-listp t
  :elementp-of-nil t
  :pred set-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::define set-list-union ((sets set-listp))
  :returns (union-set setp)
  :parents (set-list)
  :short "Union of all the sets in a list of sets."
  (cond ((endp sets) nil)
        (t (union (sfix (car sets))
                  (set-list-union (cdr sets)))))
  :verify-guards :after-returns)
