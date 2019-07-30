; KDF Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "KDF")

(include-book "../../utilities/strings/strings-codes")
(include-book "../hmac/hmac-sha-512")
(include-book "../../bv-lists/unpackbv")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; for compatibility between the string library and the bit vector library:

(local
 (defthm all-unsigned-byte-p-8-of-chars=>nats
   (acl2::all-unsigned-byte-p 8 (acl2::chars=>nats chars))
   :hints (("Goal" :in-theory (enable acl2::chars=>nats)))))

(local
 (defthm all-unsigned-byte-p-8-of-string=>nats
   (acl2::all-unsigned-byte-p 8 (acl2::string=>nats string))
   :hints (("Goal" :in-theory (enable acl2::string=>nats)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; PBKDF2 (Password-Based Key Derivation Function 2)
;;; is a key derivation function that uses
;;; repeated stretching and hashing to make it
;;; computationally expensive to do a brute force attack.

;;; For the spec, see
;;; https://tools.ietf.org/html/rfc8018
;;; (which supersedes https://tools.ietf.org/html/rfc2898,
;;; but for PBKDF2 they are identical).

;;; The following Wikipedia page provides a good illustration:
;;; https://en.wikipedia.org/wiki/PBKDF2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; From the RFC 8018 spec (with a few notes inline):

#||

5.2.  PBKDF2

   PBKDF2 applies a pseudorandom function (see Appendix B.1 for an
   example) to derive keys.  The length of the derived key is
   essentially unbounded.  (However, the maximum effective search space
   for the derived key may be limited by the structure of the underlying
   pseudorandom function.  See Appendix B.1 for further discussion.)
   PBKDF2 is recommended for new applications.

   PBKDF2 (P, S, c, dkLen)

   Options:        PRF        underlying pseudorandom function (hLen
                              denotes the length in octets of the
                              pseudorandom function output)

NOTE: for this file, we use HMAC-SHA-512 for the PRF.

   Input:          P          password, an octet string
                   S          salt, an octet string
                   c          iteration count, a positive integer
                   dkLen      intended length in octets of the derived
                              key, a positive integer, at most
                              (2^32 - 1) * hLen

NOTE: the Notation section of the spec defines:
   dkLen   length in octets of derived key, a positive integer
   hLen    length in octets of pseudorandom function output, a positive
           integer

The PRF HMAC-SHA-512 outputs 512 bits, or 64 octets, so hLen = 64.
The RFC also calls this sequence of hLen octets a "block".
In this file, we define the constant *hLen*.
We leave dkLen as a parameter.

||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *hLen* 64)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; function F

;;; From 5.2 step 3:
;;;   where the function F is defined as the exclusive-or sum of the
;;;   first c iterates of the underlying pseudorandom function PRF
;;;   applied to the password P and the concatenation of the salt S
;;;   and the block index i:
;;;
;;;       F (P, S, c, i) = U_1 \xor U_2 \xor ... \xor U_c
;;;
;;;   where
;;;       U_1 = PRF (P, S || INT (i)) ,
;;;       U_2 = PRF (P, U_1) ,
;;;       ...
;;;       U_c = PRF (P, U_{c-1}) .
;;;
;;;   Here, INT (i) is a four-octet encoding of the integer i, most
;;;   significant octet first.

;;; Let K(x) := PRF(P,x).  The function F-aux calculates
;;; K(prev-U) xor K(K(prev-U)) xor ... xor K^count(prev-U) xor 0...0,
;;; where the operands of the xor's are calculated left to right,
;;; and where the final 0...0 has no effect.
;;; The parameter count is a counter that controls the recursion.
;;; The length constraint on the password P derives from HMAC-SHA-512.
(defun F-aux (P prev-U count)
  (declare (xargs :guard (and (acl2::all-unsigned-byte-p 8 P)
                              (true-listp P)
                              (< (len P) (expt 2 125))
                              (acl2::all-unsigned-byte-p 8 prev-U)
                              (true-listp prev-U)
                              (equal (len prev-U) *hlen*)
                              (natp count))
                  :verify-guards nil)) ; done below
  (if (zp count)
      (repeat *hlen* 0)
    (let ((U (hmac::hmac-sha-512 P (acl2::bytes-to-bits prev-U))))
      (acl2::bvxor-list 8 U (F-aux P U (- count 1))))))

(defthm all-unsigned-byte-p-8-of-F-aux
  (acl2::all-unsigned-byte-p 8 (F-aux P prev-U count)))

(defthm all-integerp-of-F-aux
  (acl2::all-integerp (F-aux P prev-U count)))

(defthm true-listp-of-F-aux
  (true-listp (F-aux P prev-U count))
  :rule-classes :type-prescription)

(defthm len-of-F-aux
  (equal (len (F-aux P prev-U count))
         64)
  :rule-classes (:rewrite :linear))

(verify-guards F-aux)

(in-theory (disable F-aux))

;;; The function F calls F-aux with U_1 (as defined in the RFC)
;;; and with a count of c - 1, which calculates (see above)
;;; K(U_1) xor K(K(U_1)) xor ... xor K^(c-1)(U_1),
;;; which F xor's with U_1 obtaining
;;; U_1 xor K(U_1) xor K(K(U_1)) xor ... xor K^(c-1)(U_1),
;;; which according to the definitions of U_2, ..., U_c in the RFC is
;;; U_1 xor U_2 xor ... xor U_c.
;;; As a special case, if c = 1, F just returns U_1 without calling F-aux.
;;; The length constraint on the password P derives from HMAC-SHA-512.
;;; The length constraint on the salt S also derives from HMAC-SHA-512:
;;; in bits, the second argument of HMAC-SHA-512 must be below
;;; 2^128 - 8*128, where 128 is the SHA-512 block size (see HMAC for details),
;;; which in bytes turns into 2^125 - 128, which must be further reduced by 4
;;; because F passes S || INT(i) as second argument of HMAC-SHA-512,
;;; and INT(i) consists of 4 bytes.
;;; The integer i must be representable in 4 bytes.
(defun F (P S c i)
  (declare (xargs :guard (and (acl2::all-unsigned-byte-p 8 P)
                              (true-listp P)
                              (< (len P) (expt 2 125))
                              (acl2::all-unsigned-byte-p 8 S)
                              (true-listp S)
                              (< (len S) (- (expt 2 125) 132))
                              (posp c)
                              (natp i)
                              (< i (expt 2 32)))))
  (let ((U_1 (hmac::hmac-sha-512 P (acl2::bytes-to-bits
                                    (append S (acl2::unpackbv 4 8 i))))))
    (if (< 1 c)
        (acl2::bvxor-list 8 U_1 (F-aux P U_1 (- c 1)))
      U_1)))

(defthm all-unsigned-byte-p-8-of-F
  (acl2::all-unsigned-byte-p 8 (F P S c i)))

(defthm all-integerp-of-F
  (acl2::all-integerp (F P S c i)))

(defthm true-listp-of-F
  (true-listp (F P S c i))
  :rule-classes :type-prescription)

(defthm len-of-F
  (equal (len (F P S c i))
         64)
  :rule-classes (:rewrite :linear))

(in-theory (disable F))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Calculates the concatenation T_block_index || ... || T_l.
;;; The length restrictions on P and S are explained in F above.
;;; The restriction on the number of blocks l is motivated by
;;; the condition dkLen <= (2^32 - 1) * hLen
;;; whose satisfaction is checked in Step 1 of Section 5.2 of the RFC:
;;; that condition implies dkLen/hLen <= 2^32 - 1 since hLen is not 0,
;;; and therefore l = CEIL(dkLen/hLen) <= 2^32 - 1.
;;; Indeed, that condition serves to ensure that INT(i) fits in four octets
;;; (see F).
(defun appended-Ts (P S c block-index l)
  (declare (xargs :guard (and (acl2::all-unsigned-byte-p 8 P)
                              (true-listp P)
                              (< (len P) (expt 2 125))
                              (acl2::all-unsigned-byte-p 8 S)
                              (true-listp S)
                              (< (len S) (- (expt 2 125) 132))
                              (posp c)
                              (natp block-index)
                              (posp l)
                              (< l (expt 2 32)))
                  :measure (nfix (+ 1 (- l block-index)))))
  (if (not (mbt (and (natp block-index) (posp l))))
      nil
    (if (< l block-index)
        nil
      (append (F P S c block-index)
              (appended-Ts P S c (+ block-index 1) l)))))

(defthm all-unsigned-byte-p-8-of-appended-Ts
  (acl2::all-unsigned-byte-p 8 (appended-Ts P S c block_index l)))

(defthm true-listp-of-appended-Ts
  (true-listp (appended-Ts P S c block_index l))
  :rule-classes :type-prescription)

(defthm len-of-appended-Ts
  (equal (len (appended-Ts P S c block_index l))
         (if (and (natp block_index)
                  (posp l))
             (* 64 (nfix (- (1+ l) block_index)))
           0)))

(in-theory (disable appended-Ts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; pbkdf2-hmac-sha-512

;;; Top-level function.
;;; The length restrictions on password and salt are explained in F above.
;;; The restriction on dkLen is stated in Step 1 of Section 5.2 of the RFC.
(defun pbkdf2-hmac-sha-512 (P S c dkLen)
  (declare (xargs :guard (and (acl2::all-unsigned-byte-p 8 P)
                              (true-listp P)
                              (< (len P) (expt 2 125))
                              (acl2::all-unsigned-byte-p 8 S)
                              (true-listp S)
                              (< (len S) (- (expt 2 125) 132))
                              (posp c) ; iteration count
                              (posp dkLen)
                              (<= dkLen (* (- (expt 2 32) 1) *hlen*)))))

;;; 1.  If dkLen > (2^32 - 1) * hLen, output "derived key too long"
;;;     and stop.

  ;; This condition never occurs because of the guard of this function.
  ;; Presumably the RFC does not mean that PBKDF2 should actually return
  ;; the string "derived key too long"; it is just a way to emphasize that
  ;; PBKDF2 is not defined under that condition.

;;; 2.  Let l be the number of hLen-octet blocks in the derived key,
;;;     rounding up, and let r be the number of octets in the last
;;;     block:
;;;
;;;         l = CEIL (dkLen / hLen)
;;;         r = dkLen - (l - 1) * hLen

  (let* ((l (ceiling dkLen *hLen*))
         (r (- dkLen (* (- l 1) *hLen*))))
    ;; Note: it does not appear that we need r.
    ;; It seems to be used mainly for showing how many octets
    ;; of the last block are extracted to fill out DK.
    (declare (ignore r))

;;; 3.  For each block of the derived key apply the function F defined
;;;     below to the password P, the salt S, the iteration count c,
;;;     and the block index to compute the block:
;;;
;;;     T_1 = F (P, S, c, 1) ,
;;;     T_2 = F (P, S, c, 2) ,
;;;     ...
;;;     T_l = F (P, S, c, l) ,
;;;
;;;     where the function F ...
;;;
;;; NOTE: spec for function F moved to definition of F above.

    (let ((appended-Ts (appended-Ts P S c 1 l)))

;;; 4.  Concatenate the blocks and extract the first dkLen octets to
;;;     produce a derived key DK:
;;;
;;;         DK = T_1 || T_2 ||  ...  || T_l<0..r-1>
;;;
;;; 5.  Output the derived key DK.
      (take dkLen appended-Ts))

;;; Note: The construction of the function F follows a "belt-and-
;;; suspenders" approach.  The iterates U_i are computed recursively to
;;; remove a degree of parallelism from an opponent; they are exclusive-
;;; ored together to reduce concerns about the recursion degenerating
;;; into a small set of values.

    ))

(defthm all-unsigned-byte-p-8-of-pbkdf2-hmac-sha-512
  (acl2::all-unsigned-byte-p 8 (pbkdf2-hmac-sha-512 P S c dkLen)))

(defthm true-listp-of-pbkdf2-hmac-sha-512
  (true-listp (pbkdf2-hmac-sha-512 P S c dkLen))
  :rule-classes :type-prescription)

(defthm len-of-pbkdf2-hmac-sha-512
  (equal (len (pbkdf2-hmac-sha-512 P S c dkLen))
         (nfix dkLen)))

(in-theory (disable pbkdf2-hmac-sha-512))

;;; Variant top-level function that takes strings as password and salt.
;;; (ACL2 strings are isomorphic to octet strings.)
(defun pbkdf2-hmac-sha-512-from-strings (P-string S-string c dkLen)
  (declare (xargs :guard (and (stringp P-string)
                              (< (length P-string) (expt 2 125))
                              (stringp S-string)
                              (< (length S-string) (- (expt 2 125) 132))
                              (posp c)
                              (posp dkLen)
                              (<= dkLen (* (- (expt 2 32) 1) *hlen*)))))
  (pbkdf2-hmac-sha-512 (acl2::string=>nats P-string)
                       (acl2::string=>nats S-string)
                       c
                       dkLen))

(defthm all-unsigned-byte-p-8-of-pbkdf2-hmac-sha-512-from-strings
  (acl2::all-unsigned-byte-p
   8 (pbkdf2-hmac-sha-512-from-strings P-string S-string c dkLen)))

(defthm true-listp-of-pbkdf2-hmac-sha-512-from-strings
  (true-listp (pbkdf2-hmac-sha-512-from-strings P-string S-string c dkLen))
  :rule-classes :type-prescription)

(defthm len-of-pbkdf2-hmac-sha-512-from-strings
  (equal (len (pbkdf2-hmac-sha-512-from-strings P-string S-string c dkLen))
         (nfix dkLen)))

(in-theory (disable pbkdf2-hmac-sha-512-from-strings))
