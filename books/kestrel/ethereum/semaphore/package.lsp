; Ethereum Semaphore Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/crypto/r1cs/portcullis" :dir :system)
(include-book "kestrel/ethereum/portcullis" :dir :system)
(include-book "kestrel/number-theory/portcullis" :dir :system)
(include-book "kestrel/prime-fields/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ZKSEMAPHORE" ; 'zk' stands for zero-knowledge
  (append '(///
            assert!
            b*
            bit-listp
            booland
            define
            define-sk
            defmacro+
            defret
            defrule
            defruled
            defruledl
            defrulel
            defsection
            defxdoc+
            repeat
            rule
            unless
            when
            pfield::add
            pfield::mul
            pfield::neg
            pfield::inv
            pfield::div
            pfield::fep
            rtl::primep
            acl2::getbit
            acl2::slice
            acl2::bvchop
            acl2::bvcat
            acl2::bvplus
            acl2::bvxor
            acl2::bitxor
            acl2::bitnot
            acl2::keywords-to-acl2-package ; appears in proof examples
            ecurve::make-twisted-edwards-curve
            ecurve::pfield-squarep
            ecurve::twisted-edwards-curvep
            ecurve::twisted-edwards-curve-completep
            ecurve::twisted-edwards-curve-primep
            primes::*bn-254-group-prime*
            ) ; added symbols
          (set-difference-eq
           *acl2-exports*
           '() ; removed symbols
           )))
