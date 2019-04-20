; Ethereum -- Package
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "kestrel/crypto/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ETHEREUM" (append *std-pkg-symbols*
                           '(assert-equal
                             bebytes=>nat
                             byte
                             byte-fix
                             byte-list
                             byte-list-equiv
                             byte-list-fix
                             byte-list20
                             byte-list20p
                             byte-list32
                             byte-list32p
                             byte-list64
                             byte-list64p
                             byte-listp
                             bytep
                             defmax-nat
                             defxdoc+
                             lnfix
                             nat
                             nat=>bebytes*
                             nibble
                             nibble-fix
                             nibble-list
                             nibble-list-fix
                             nibble-listp
                             nibblep
                             prefixp
                             string=>nats
                             trim-bendian*
                             unsigned-byte-fix
                             unsigned-byte-list-fix
                             std::define-sk
                             crypto::keccak-256)))
