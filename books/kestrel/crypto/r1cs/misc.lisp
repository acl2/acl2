; Support for proofs about R1CSes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; Proof support for R1CS proofs -- TODO: Move this material to libraries

(include-book "portcullis")
(include-book "proof-support") ;reduce
(include-book "kestrel/crypto/r1cs/fe-listp" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/prime-fields/bv-rules" :dir :system)
;(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(include-book "kestrel/typed-lists-light/bit-listp" :dir :system) ;drop?
(include-book "kestrel/arithmetic-light/lg" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
