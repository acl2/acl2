; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "REMORA" (append
                  (set-difference-eq *std-pkg-symbols*
                                     '(atom
                                       atom-listp
                                       check-type
                                       function
                                       functionp
                                       import
                                       prog
                                       sort
                                       termp
                                       type
                                       typep
                                       value
                                       values))
                  '(all-equalp
                    bool
                    boolean-resultp
                    booleanp-when-result-not-error
                    change-string-string-map-quadruple
                    chars=>nats
                    cons-listp
                    defmacro+
                    defund-sk
                    defxdoc+
                    enable*
                    explode
                    impossible
                    int
                    integer-resultp
                    integer-list-resultp
                    lifix
                    lnfix
                    make-string-string-map-pair
                    make-string-string-map-quadruple
                    nat
                    nat-resultp
                    nat-list
                    nat-list-fix
                    nat-list-resultp
                    nat-list-listp
                    nat-list-list-resultp
                    nat-list-list-listp
                    nats=>string
                    pos-fix
                    prefixp
                    str-fix
                    string=>nats
                    string-setp
                    string-sfix
                    string-string-mapp
                    string-string-map-fix
                    string-string-map-pair
                    string-string-map-pair-resultp
                    string-string-map-quadruple
                    string-string-map-quadruple-resultp
                    unsigned-byte-listp
                    ustring?
                    ustring=>utf8
                    utf8=>ustring
                    fty::ok
                    fty::okf
                    fty::patbind-ok
                    fty::patbind-okf
                    fty::reserr
                    fty::reserrf
                    fty::reserrf-push
                    fty::reserrp
                    std::define-sk
                    std::defret-mutual
                    std::defval
                    str::dec-digit-char-list
                    str::hex-digit-char-list
                    str::oct-digit-char-list
                    str::dec-digit-char-list-resultp
                    str::hex-digit-char-list-resultp
                    str::oct-digit-char-list-resultp
                    str::string-list
                    str::string-list-fix)))
