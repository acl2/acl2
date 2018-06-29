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

(defpkg "ETHEREUM" (append *std-pkg-symbols*
                           '(bendian=>nat
                             lnfix
                             nat=>bendian
                             nat=>bendian*
                             nat
                             ubyte4
                             ubyte4-fix
                             ubyte4-list
                             ubyte4-list-fix
                             ubyte4-listp
                             ubyte4p
                             ubyte8
                             ubyte8-fix
                             ubyte8-list
                             ubyte8-list-fix
                             ubyte8-listp
                             ubyte8p
                             set::map-empty
                             set::map-head
                             set::map-put-assoc
                             set::map-tail
                             set::mapp
                             std::define-sk)))
