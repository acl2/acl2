; Primes Library: Package
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/prime-fields/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)

(defpkg "PRIMES"
  (append '(assert!
            b*
            define
            defret
            defrule
            defruled
            defsection
            defxdoc
            defxdoc+
            patbind-unless
            patbind-when
            repeat
            pfield::fep
            pfield::mul
            pfield::add
            pfield::div
            pfield::sub
            pfield::inv
            pfield::neg
            pfield::pow
            ///
            )
          *acl2-exports*))
