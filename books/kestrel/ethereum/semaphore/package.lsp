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
            b*
            booland
            define
            define-sk
            defrule
            defruled
            defxdoc+
            rule
            unless
            when
            pfield::add
            pfield::mul
            pfield::neg
            pfield::fep
            rtl::primep
            acl2::keywords-to-acl2-package ; appears in proof examples
            primes::*bn-254-group-prime*
            r1cs::lift-r1cs
            ) ; added symbols
          (set-difference-eq
           *acl2-exports*
           '() ; removed symbols
           )))
