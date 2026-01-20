; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "std/osets/top" :dir :system)

(include-book "time-set")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This tests file has the .lsp extension so that it isn't included in
;; regression builds. It is used to test performance and therefore takes
;; significant time to certify.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Previous tests:
;; - fnv-1a is slower than jenkins-hash
;; - using the hash order for the bst order is slower (than using it for the
;;   heap order)
;; - using cons-with-hint saves memory on delete, with negligible computation
;;   increase

;; The hash seems to be the bottleneck (and that is why insert is slower than
;; everything else). This seems to suggest we'd benefit from storing the hash
;; values in the tree nodes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Operations on random sets/osets

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ~0.05 seconds
(make-event (random-set-time-ins 10000 100000 state))

;; ~1.93 seconds
(make-event (random-oset-time-ins 10000 100000 state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ~0.40 seconds
(make-event (random-set-time-inserts 10000 100000 state))

;; ~6.8 seconds
(make-event (random-oset-time-inserts 10000 100000 state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ~0.07 seconds
(make-event (random-set-time-deletes 10000 100000 state))

;; ~25.11 seconds
(make-event (random-oset-time-deletes 10000 100000 state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Operations on sets/osets of consecutive nats

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ~0.02 seconds
(make-event (consecutive-nat-set-time-ins 10000 100000 state))

;; ~1.92 seconds
(make-event (consecutive-nat-oset-time-ins 10000 100000 state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ~0.07 seconds
(make-event (consecutive-nat-set-time-inserts 10000 100000 state))

;; ~12.04 seconds
(make-event (consecutive-nat-oset-time-inserts 10000 100000 state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ~0.02 seconds
(make-event (consecutive-nat-set-time-deletes 10000 100000 state))

;; ~16.52 seconds
(make-event (consecutive-nat-oset-time-deletes 10000 100000 state))
