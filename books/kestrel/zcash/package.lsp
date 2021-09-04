; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "kestrel/crypto/ecurve/portcullis" :dir :system)
(include-book "kestrel/crypto/r1cs/portcullis" :dir :system)
(include-book "kestrel/isar/portcullis" :dir :system)
(include-book "kestrel/prime-fields/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ZCASH" (append (set-difference-eq *std-pkg-symbols*
                                           '())
                        '(bitp
                          bytep
                          bit-listp
                          byte-listp
                          define-sk
                          defxdoc+
                          nat-setp
                          isar::defisar
                          pfield::fep
                          pfield::add
                          pfield::neg
                          pfield::sub
                          pfield::mul
                          pfield::inv
                          pfield::div
                          r1cs::fe-listp)))
