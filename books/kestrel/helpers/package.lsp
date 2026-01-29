; The HELP package
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defpkg "HELP" (append '(b*
                         when ; the b* binder
                         *t*
                         *nil*
                         rule
                         defrule defruled defrulel defruledl
                         ;; functions used in the implementation:
                         pseudo-term-list-listp
                         string-list-listp
                         make-event-quiet
                         wrap-all
                         widen-margins
                         unwiden-margins)
                       *acl2-exports*))
