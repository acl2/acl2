; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/prime-fields/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ECURVE"
  (append '(;; added symbols
            assert!
            b*
            byte-listp
            define
            defrule
            defsection
            defxdoc
            defxdoc+
            i*
            i+
            i-
            nat=>bebytes
            repeat
            pfield::fep
            pfield::mul
            pfield::add
            pfield::div
            pfield::sub
            pfield::inv
            pfield::neg
            pfield::pow
            str::strval16s
            ///
            )
          (set-difference-eq
           *acl2-exports*
           '(;; removed symbols
             ))))
