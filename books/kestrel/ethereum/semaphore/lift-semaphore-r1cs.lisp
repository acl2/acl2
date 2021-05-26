; A Semaphore-specific version of lift-r1cs
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "kestrel/crypto/r1cs/tools/lift-r1cs" :dir :system)

;; A thin wrapper around lift-r1cs-new that sets the prime for semaphore.
;; If the VARS are keywords (which is common), they get converted to the ZKSEMAPHORE package."
(defmacro lift-semaphore-r1cs (name-of-defconst vars constraints &rest args)
  `(r1cs::lift-r1cs-new ,name-of-defconst
                        ,vars
                        ,constraints
                        ;; This is baby-jubjub-prime:
                        21888242871839275222246405745257275088548364400416034343698204186575808495617
                        :package "ZKSEMAPHORE"
                        ,@args))
