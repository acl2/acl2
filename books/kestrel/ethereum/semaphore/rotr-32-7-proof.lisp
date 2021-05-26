; A proof of an R1CS for rightrotate
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "json-to-r1cs/load-circom-json")
(include-book "lift-semaphore-r1cs")
(include-book "verify-semaphore-r1cs")
(include-book "baby-jubjub-prime")
(include-book "kestrel/crypto/r1cs/tools/axe-prover-r1cs" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)

;; Load the R1CS:
;; (depends-on "json/rotr-32-7.json")
(local (acl2::load-circom-json "json/rotr-32-7.json" *baby-jubjub-prime*))

;;;
;;; Unroll the R1CS
;;;

(local
 (lift-semaphore-r1cs *rotr-32-7-r1cs-lifted*
                      (acl2::rotr-32-7-vars)
                      (acl2::rotr-32-7-constraints)))

;;;
;;; The spec
;;;

;; TOOD: Maybe have this take all the individual I/O vars?
(defun rotr-32-7-spec (in out)
  (equal out (acl2::rightrotate 32 7 in)))

;; TODO: Can we do the unrolling as part of this, instead of separately above?
(verify-semaphore-r1cs
 *rotr-32-7-r1cs-lifted*
 (rotr-32-7-spec (acl2::packbv '32 '1
                               (list |main.in[31]| |main.in[30]|
                                     |main.in[29]| |main.in[28]|
                                     |main.in[27]| |main.in[26]|
                                     |main.in[25]| |main.in[24]|
                                     |main.in[23]| |main.in[22]|
                                     |main.in[21]| |main.in[20]|
                                     |main.in[19]| |main.in[18]|
                                     |main.in[17]| |main.in[16]|
                                     |main.in[15]| |main.in[14]|
                                     |main.in[13]| |main.in[12]|
                                     |main.in[11]| |main.in[10]|
                                     |main.in[9]| |main.in[8]|
                                     |main.in[7]| |main.in[6]|
                                     |main.in[5]| |main.in[4]|
                                     |main.in[3]| |main.in[2]|
                                     |main.in[1]| |main.in[0]|))
                 (acl2::packbv '32 '1 (list |main.out[31]| |main.out[30]|
                                            |main.out[29]|
                                            |main.out[28]|
                                            |main.out[27]|
                                            |main.out[26]|
                                            |main.out[25]|
                                            |main.out[24]|
                                            |main.out[23]|
                                            |main.out[22]|
                                            |main.out[21]|
                                            |main.out[20]|
                                            |main.out[19]|
                                            |main.out[18]|
                                            |main.out[17]|
                                            |main.out[16]|
                                            |main.out[15]|
                                            |main.out[14]|
                                            |main.out[13]|
                                            |main.out[12]|
                                            |main.out[11]|
                                            |main.out[10]|
                                            |main.out[9]| |main.out[8]|
                                            |main.out[7]| |main.out[6]|
                                            |main.out[5]| |main.out[4]|
                                            |main.out[3]| |main.out[2]|
                                            |main.out[1]| |main.out[0]|)))
 :rule-lists '(((acl2::lookup-rules)
                (acl2::core-rules-bv)
                (acl2::boolean-rules)
                (acl2::unsigned-byte-p-rules)
                implies
                rotr-32-7-spec
                car-cons
                acl2::equal-same
                acl2::packbv-opener
                acl2::rightrotate
                acl2::cdr-cons
                =
                acl2::slice-of-bvcat-gen
                ;;pfield::mod-when-fep
                ;;pfield::fep-of-ifix
                ;;pfield::ifix-when-fep
                acl2::bvcat-equal-rewrite
                acl2::bvchop-of-bvcat-cases
                acl2::leftrotate32
                acl2::leftrotate
                acl2::getbit-0-of-getbit
                acl2::booleanp-of-equal
                acl2::booleanp-of-booland
                ;;acl2::bool-fix$inline  caused problems? possibly because it expands to an if that becomes a booland?
                acl2::bool-fix-when-booleanp
                acl2::if-of-nil-becomes-booland
                acl2::if-of-t-arg3)))
