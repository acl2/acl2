; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/prime-fields/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "PFCS" (append (set-difference-eq *std-pkg-symbols*
                                          '(eval
                                            proof-tree))
                       '(define-sk
                         defund-sk
                         defxdoc+
                         int
                         nat
                         nat-resultp
                         nat-list-resultp
                         pseudo-event-formp
                         pseudo-event-form-listp
                         symbol-fix
                         symbol-list
                         symbol-setp
                         table-alist+
                         true-list
                         dm::primep
                         fty::ok
                         fty::reserr
                         fty::reserrp
                         pfield::add
                         pfield::fep
                         pfield::fe-listp
                         pfield::inv
                         pfield::mul)))
