; Tests of the RFC 6979 Deterministic ECDSA formalization.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECDSA")

(include-book "deterministic-ecdsa-secp256k1")

;; Variant definitions that return k.  Useful for testing.

;; In case r or s is unacceptable, keeps trying with this function.
(defun ecdsa-sign-deterministic-next-exposing-k
    (mh privkey prev-K prev-V prev-max-iters)
  ;; :returns (mv error? x-index y-even? r s k)
  (declare (xargs :measure (nfix prev-max-iters)))
  (if (zp prev-max-iters)
      (mv t 0 nil 0 0 0)
    (mv-let (small-k large-K V max-iters)
      (generate-next-k-in-range prev-K prev-V prev-max-iters)
      (mv-let (error? x-index y-even? r s) (ecdsa-sign-given-k mh privkey small-k)
        (if (or error?
                (not (= x-index 0)))
            (ecdsa-sign-deterministic-next-exposing-k
             mh privkey large-K V (- max-iters 1))
          (mv nil x-index y-even? r s small-k))))))

;; NOTE: Currently this takes m:list-of-bits, privkey:nat
;; We might want to change privkey to be a list of 32 bytes.
(defun ecdsa-sign-deterministic-prehashed-exposing-k-aux (mh privkey)
  ;; :returns (mv error? x-index y-even? r s k)
  (mv-let (small-k large-K V max-iters) (generate-first-k-in-range mh privkey)
    (mv-let (error? x-index y-even? r s) (ecdsa-sign-given-k mh privkey small-k)
      (if (or error?
              (not (= x-index 0)))
          (ecdsa-sign-deterministic-next-exposing-k
           mh privkey large-K V (- max-iters 1))
        (mv nil x-index y-even? r s small-k)))))

(defun ecdsa-sign-deterministic-prehashed-exposing-k (mh privkey small-s?)
  ;; :returns (mv error? x-index y-even? r s k)
  (b* (((mv error? x-index y-even? r s k)
        (ecdsa-sign-deterministic-prehashed-exposing-k-aux mh privkey)))
    (if small-s?
        (b* (((mv x-index y-even? r s)
              (ecdsa-ensure-s-below-q/2 x-index y-even? r s)))
          (mv error? x-index y-even? r s k))
      (mv error? x-index y-even? r s k))))

;;; This is the most standard instantiation of RFC 6979, using sha-256 for both
;;; the message hash and the hmac.  However, this is not used by Ethereum.
;;; m is a list of bits; privkey is a nat
(defun ecdsa-sign-deterministic-sha-256-exposing-k (m privkey small-s?)
  ;; :returns (mv error? x-index y-even? r s k)
  (ecdsa-sign-deterministic-prehashed-exposing-k
   (bytes-to-bits (sha2::sha-256 m))
   privkey
   small-s?))
