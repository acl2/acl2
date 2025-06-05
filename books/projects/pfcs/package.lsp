; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/prime-fields/portcullis" :dir :system)
(include-book "kestrel/apt/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "PFCS" (append (set-difference-eq *std-pkg-symbols*
                                          '(eval
                                            proof-tree))
                       '(boolean-resultp
                         character-list-resultp
                         character-resultp
                         define-sk
                         defmacro+
                         defund-sk
                         defxdoc+
                         int
                         integer-resultp
                         maybe-string-fix
                         maybe-string-resultp
                         maybe-stringp
                         nat
                         nat-list
                         nat-list-fix
                         nat-list-resultp
                         nat-option
                         nat-optionp
                         nat-option-fix
                         nat-option-list
                         nat-option-listp
                         nat-option-resultp
                         nat-option-list-resultp
                         nat-resultp
                         nats=>string
                         pseudo-event-formp
                         pseudo-event-form-listp
                         string-setp
                         string=>nats
                         symbol-fix
                         symbol-list
                         symbol-setp
                         table-alist+
                         true-list
                         unsigned-byte-listp
                         dm::primep
                         fty::info
                         fty::ok
                         fty::okf
                         fty::reserr
                         fty::reserrf
                         fty::reserrf-push
                         fty::reserrp
                         fty::reserr-option
                         fty::reserr-optionp
                         fty::stack
                         pfield::add
                         pfield::fep
                         pfield::fe-listp
                         pfield::fe-list-listp
                         pfield::inv
                         pfield::mul
                         str::str-fix
                         str::string-list
                         str::string-list-fix
                         string-list-resultp
                         string-resultp
                         std::defret-mutual
                         )))
