; Ethereum Library -- Package
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ETHEREUM" (append (set-difference-eq *std-pkg-symbols*
                                              '(byte))
                           '(assert-equal
                             bendian=>nat
                             defmax-nat
                             defxdoc+
                             lnfix
                             nat=>bendian
                             nat
                             nat=>bendian*
                             prefixp
                             string=>nats
                             trim-bendian*
                             unsigned-byte-fix
                             unsigned-byte-list-fix
                             std::define-sk)))
