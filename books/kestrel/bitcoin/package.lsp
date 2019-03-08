; Bitcoin -- Package
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "BITCOIN" (append (set-difference-eq *std-pkg-symbols*
                                             '(byte))
                          '(bendian=>nat
                            dab-digit-fix
                            dab-digit-list-fix
                            dab-digit-listp
                            dab-digitp
                            define-sk
                            defthm-dab-return-types
                            defxdoc+
                            explode
                            implode
                            index-of
                            nat
                            nat-equiv
                            nat=>bendian
                            nat=>bendian*
                            prefixp
                            string=>nats
                            trim-bendian*
                            ubyte32
                            ubyte32-fix
                            ubyte32-list
                            ubyte32-list-fix
                            ubyte32-listp
                            ubyte32p
                            ubyte8-fix
                            ubyte8-list-equiv
                            ubyte8-list-fix
                            ubyte8-listp
                            ubyte8p)))
