; Cryptographic Library
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

(defpkg "CRYPTO" (append *std-pkg-symbols*
                         '(all-unsigned-byte-p
                           bebytes=>bits
                           bit-listp
                           bool-fix
                           byte-list-equiv
                           byte-list-fix
                           byte-list20p
                           byte-list32p
                           byte-list64p
                           byte-listp
                           defxdoc+
                           maybe-posp
                           nat-equiv
                           nat=>bebytes
                           pos-fix)))
