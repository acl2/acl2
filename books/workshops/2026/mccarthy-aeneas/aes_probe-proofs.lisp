; Equivalence proofs for the extracted AES probe (aes_probe.lisp) against the
; Kestrel AES specification (books/kestrel/crypto/aes/aes-spec.lisp).
;
; The point mirrors the TEA development: don't trust the extraction chain --
; PROVE the extracted Rust operations equal an independently-audited ACL2 spec.
; Here we target AES's finite-field core, GF(2^8): the extracted `xtime`
; (multiply-by-x) and `gmul` (general multiply) are shown equal to Kestrel's
; AES::xtime and AES::gf256mult.  We also characterize the S-box lookup `sub`,
; whose `(byte as usize)` index cast is the feature this milestone added.

(in-package "ACL2")

(include-book "aes_probe")
(include-book "kestrel/crypto/aes/aes-spec" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

;; ====================================================================
;; FIPS-197 concrete test vectors (execution): the extracted GF ops
;; reproduce the worked examples from the AES standard, section 4.
;; ====================================================================

;; FIPS-197 sec 4.1: xtime(0x57) = 0xae, and the chain up to xtime(0x8e)=0x07.
(assert-event (equal (aes-probe-xtime #x57) (ok #xae)))
(assert-event (equal (aes-probe-xtime #xae) (ok #x47)))
(assert-event (equal (aes-probe-xtime #x47) (ok #x8e)))
(assert-event (equal (aes-probe-xtime #x8e) (ok #x07)))

;; FIPS-197 sec 4.2: 0x57 . 0x13 = 0xfe  (fuel 9 covers the 8 bit-iterations).
(assert-event (equal (aes-probe-gmul 9 #x57 #x13) (ok #xfe)))
(assert-event (equal (aes-probe-gmul 9 #x57 #x83) (ok #xc1)))
;; identity and zero
(assert-event (equal (aes-probe-gmul 9 #x01 #xab) (ok #xab)))
(assert-event (equal (aes-probe-gmul 9 #x00 #xab) (ok #x00)))

;; Cross-check the extracted gmul against the Kestrel spec on the same inputs.
(assert-event (equal (result-ok->val (aes-probe-gmul 9 #x57 #x13))
                     (aes::gf256mult #x57 #x13)))
(assert-event (equal (result-ok->val (aes-probe-xtime #x57))
                     (aes::xtime #x57)))

;; ====================================================================
;; S-box lookup `sub`: the (x & 3) as usize index cast is transparent, and
;; the lookup never panics for any integer input (index is always in range).
;; ====================================================================

(defthm logand-3-bound
  (<= (logand x 3) 3)
  :rule-classes :linear)

(defthm natp-logand-3
  (natp (logand x 3))
  :rule-classes :type-prescription)

;; The cast + bounds-check disappear: sub is exactly an S-box lookup.
(defthm sub-is-sbox-lookup
  (equal (aes-probe-sub x)
         (ok (nth (logand x 3) *aes-probe-sbox*)))
  :hints (("Goal" :in-theory (enable aes-probe-sub))))

;; ... and it never fails, whatever the input byte.
(defthm sub-never-panics
  (equal (result-kind (aes-probe-sub x)) :ok)
  :hints (("Goal" :in-theory (enable aes-probe-sub))))

;; ====================================================================
;; GF(2^8) EQUIVALENCE (the capstone): the extracted finite-field ops are
;; proven equal to the Kestrel AES spec for EVERY input -- not just the
;; FIPS vectors above.  xtime is a byte->byte function (256 inputs) and
;; gmul a (byte,byte)->byte function (65536 inputs), so each is verified
;; exhaustively over its finite domain by ground execution, then bridged
;; to the universally-quantified statement by structural induction.  This
;; is a complete total-correctness result over the field, the same thing a
;; bit-blaster establishes -- here via the evaluator.
;; ====================================================================

;; ---- xtime == AES::xtime, for all bytes ----------------------------

(local
 (defun xtime-ok-below (n)
   (if (zp n)
       t
     (and (equal (aes-probe-xtime (1- n)) (ok (aes::xtime (1- n))))
          (xtime-ok-below (1- n))))))

(local
 (defthm xtime-ok-below-implies
   (implies (and (xtime-ok-below n) (natp n) (natp x) (< x n))
            (equal (aes-probe-xtime x) (ok (aes::xtime x))))
   :hints (("Goal" :induct (xtime-ok-below n)
                   :in-theory (disable aes-probe-xtime aes::xtime)))))

(local (defthm xtime-ok-below-256 (xtime-ok-below 256)))

(defthm xtime-equals-kestrel-spec
  (implies (unsigned-byte-p 8 x)
           (equal (aes-probe-xtime x) (ok (aes::xtime x))))
  :hints (("Goal" :use ((:instance xtime-ok-below-implies (n 256)))
                  :in-theory (e/d (unsigned-byte-p)
                                  (xtime-ok-below aes-probe-xtime aes::xtime)))))

;; ---- gmul == AES::gf256mult, for all pairs of bytes ----------------

(local
 (defun gmul-ok-row (a n)
   (if (zp n)
       t
     (and (equal (aes-probe-gmul 9 a (1- n)) (ok (aes::gf256mult a (1- n))))
          (gmul-ok-row a (1- n))))))

(local
 (defthm gmul-ok-row-implies
   (implies (and (gmul-ok-row a n) (natp n) (natp b) (< b n))
            (equal (aes-probe-gmul 9 a b) (ok (aes::gf256mult a b))))
   :hints (("Goal" :induct (gmul-ok-row a n)
                   :in-theory (disable aes-probe-gmul aes::gf256mult)))))

(local
 (defun gmul-ok-below (m)
   (if (zp m)
       t
     (and (gmul-ok-row (1- m) 256)
          (gmul-ok-below (1- m))))))

(local
 (defthm gmul-ok-below-implies-row
   (implies (and (gmul-ok-below m) (natp m) (natp a) (< a m))
            (gmul-ok-row a 256))
   :hints (("Goal" :induct (gmul-ok-below m)
                   :in-theory (disable gmul-ok-row)))))

(local (defthm gmul-ok-below-256 (gmul-ok-below 256)))

;; The general GF(2^8) multiply extracted from Rust computes exactly the
;; Kestrel spec's product, on every pair of bytes.  (Fuel 9 covers the 8
;; bit-iterations of the Russian-peasant loop.)
(defthm gmul-equals-kestrel-spec
  (implies (and (unsigned-byte-p 8 a) (unsigned-byte-p 8 b))
           (equal (aes-probe-gmul 9 a b) (ok (aes::gf256mult a b))))
  :hints (("Goal"
           :use ((:instance gmul-ok-below-implies-row (m 256))
                 (:instance gmul-ok-row-implies (n 256)))
           :in-theory (e/d (unsigned-byte-p)
                           (gmul-ok-row gmul-ok-below
                            aes-probe-gmul aes::gf256mult)))))
