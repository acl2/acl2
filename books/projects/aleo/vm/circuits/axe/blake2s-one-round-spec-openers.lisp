; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

(include-book "support-blake2s")
(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "blake2s1round")

;;;
;;; unroll the spec (just to see what's there)
;;;

(acl2::defopeners blake::bytes-to-blocks)
(acl2::defopeners blake::bytes-to-words)
(acl2::defopeners blake::words-to-bytes)
(acl2::defopeners blake::f-loop-1)
(acl2::defopeners blake::f-loop-2)
(acl2::defopeners blake::loop1)

(acl2::def-constant-opener acl2::bvshr)
(acl2::def-constant-opener acl2::slice)
(acl2::def-constant-opener acl2::logtail$inline)

(defthm blake::bytes-to-blocks-base-2
  (implies (equal 0 (len blake::bytes))
           (equal (blake::bytes-to-blocks blake::bytes)
                  'nil)))
