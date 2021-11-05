; A Zcash-specific version of lift-r1cs
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "kestrel/axe/r1cs/lift-r1cs" :dir :system)

;; A thin wrapper around lift-r1cs that sets the prime for Zcash.
;; If the VARS are keywords (which is common), they get converted to the ZCASH package."
(defmacro lift-zcash-r1cs (name-of-defconst vars constraints &rest args)
  `(r1cs::lift-r1cs ,name-of-defconst
                        ,vars
                        ,constraints
                        ;; This is (zcash::jubjub-q):
                        52435875175126190479447740508185965837690552500527637822603658699938581184513
                        :package "ZCASH"
                        ,@args))
