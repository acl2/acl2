; List Utilities
;
; Copyright (C) 2024 Kestrel Institute (https://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist all-len-equal-p (x l)
  :parents (list-utilities)
  :short "Check if all the elements of a list of lists have a given length."
  :guard (and (true-list-listp x) (natp l))
  (equal (len x) (nfix l))
  :true-listp nil
  :elementp-of-nil :unknown)
