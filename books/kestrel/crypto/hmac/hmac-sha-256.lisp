; Formal specification of HMAC-SHA-256
;
; Copyright (C) 2018-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HMAC")

;; A formal specification of HMAC specialized to use the SHA-256 hash function.
;; See https://tools.ietf.org/html/rfc2104.  Sections mentioned in this file
;; refer to that RFC.

;; See also tests in hmac-sha-256-tests-simple.lisp.

(include-book "../sha-2/sha-256")
(include-book "../../bv-lists/bvxor-list")
(local (include-book "../../lists-light/append"))
(local (include-book "../../typed-lists-light/all-integerp-of-repeat"))

(defconst *sha-256-block-size* 64) ;; 512 bits = 64 bytes

;; (defconst *sha-256-output-size* 32) ;; 256 bits = 32 bytes

;; Apply HMAC-SHA-256 to key K (a list of bytes) and data TEXT (a list of
;; bits).  See RFC 2104 for guidance on the length of k.  Returns a list of 32
;; bytes.  This function formalizes Section 2.
(defund hmac-sha-256 (k text)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 k)
                              (true-listp k)
                              (<= (len k) sha2::*sha-256-max-message-bytes*) ;so we can hash it
                              (all-unsigned-byte-p 1 text)
                              (true-listp text)
                              ;; so that we can hash the result of step3 below:
                              (< (len text)
                                 (- sha2::*sha-256-max-message-bits*
                                    ;; number of bits in step2:
                                    (* 8 *sha-256-block-size*))))))
  (let* ((b *sha-256-block-size*)
         ;; (l *sha-256-output-size*)
         ;; Hash keys that are too long. See the first paragraph of Section 2:
         (k (if (< b (len k))
                (sha2::sha-256-bytes k)
              k))
         (step1 (append k (repeat (- b (len k)) 0)))
         (ipad (repeat b #x36))
         (opad (repeat b #x5c))
         (step2 (bvxor-list 8 step1 ipad))
         (step3 (append (bytes-to-bits step2) text)) ; a list of bits
         (step4 (sha2::sha-256 step3))
         (step5 (bvxor-list 8 step1 opad))
         (step6 (append step5 step4))
         (step7 (sha2::sha-256 (bytes-to-bits step6))))
    step7))

(defthm all-unsigned-byte-p-of-hmac-sha-256
  (all-unsigned-byte-p 8 (hmac-sha-256 k text))
  :hints (("Goal" :in-theory (enable hmac-sha-256))))

(defthm all-integerp-of-hmac-sha-256
  (all-integerp (hmac-sha-256 k text))
  :hints (("Goal" :in-theory (enable hmac-sha-256))))

(defthm len-of-hmac-sha-256
  (equal (len (hmac-sha-256 k text))
         32)
  :hints (("Goal" :in-theory (enable hmac-sha-256))))

(defthm true-listp-of-hmac-sha-256
  (true-listp (hmac-sha-256 k text))
  :rule-classes :type-prescription)
