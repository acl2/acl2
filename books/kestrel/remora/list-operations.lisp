; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/utilities/true-list-listp-theorems" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ list-operations
  :parents (library-extensions)
  :short "Operations on lists."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define append-all ((lists true-list-listp))
  :returns (list true-listp)
  :short "Append all the lists in a list, in that order."
  (cond ((endp lists) nil)
        (t (append (mbe :logic (true-list-fix (car lists))
                        :exec (car lists))
                   (append-all (cdr lists)))))
  :hooks nil)
