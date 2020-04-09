; Elliptic Curve Digital Signature Algorithm (ECDSA) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECDSA")

(include-book "kestrel/crypto/ecurve/secp256k1" :dir :system)
(include-book "kestrel/crypto/hmac/hmac-sha-256" :dir :system)
(include-book "kestrel/crypto/keccak/keccak" :dir :system)
(include-book "kestrel/bv-lists/all-integerp-of-repeat" :dir :system)
(include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes" :dir :system)

(local (include-book "std/lists/top" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (enable acl2::unsigned-byte-listp-rewrite)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Deterministic Elliptic Curve Digital Signature Algorithm
;; from RFC 6979
;; specialized for curve secp256k1.
;;
;; For section references see
;;   https://tools.ietf.org/html/rfc6979
;;
;; For more information on ECDSA before RFC 6979:
;;   Standards for Efficient Cryptography
;;   SEC 1: Elliptic Curve Cryptography (Version 2.0)
;;   Certicom Research, May 2009
;;   http://www.secg.org/sec1-v2.pdf

;; We plan to generalize this specification to cover arbitrary curves, not just
;; secp256k1, and/or to rename the current functions to reflect their
;; specificity to secp256k1.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; API summary
;;
;;   (ecdsa-sign-deterministic-sha-256 m privkey small-s?)
;;   (ecdsa-sign-deterministic-keccak-256 m privkey small-s?)
;;   (ecdsa-sign-deterministic-prehashed mh privkey small-s?)
;; These all return (mv error? x-index y-even? r s)
;;
;; For testing:
;;
;;   (ecdsa-sign-given-k mh privkey k)
;;
;; Where:
;;   m: message before hashing (list of bits)
;;   mh: hashed message (list of bits)
;;   privkey: private key (nat)
;;   small-s?: flag saying whether s should be below q/2
;;   k: ephemeral private key (nat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Top xdoc topic for this file.

(defxdoc deterministic-ecdsa-secp256k1
  :parents (elliptic-curve-digital-signature-algorithm)
  :short "A formal specification of Deterministic ECDSA using secp256k1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library contains executable formal specifications
     of functions implementing the Deterministic Elliptic Curve Digital
     Signature Algorithm (ECDSA), using secp256k1 as the elliptic curve.
     This algorithm is described in "
    (xdoc::a :href "https://tools.ietf.org/html/rfc6979"
             "IETF RFC 6979") ".")
   (xdoc::p "For more information on ECDSA before RFC 6979, see "
            (xdoc::a :href "http://www.secg.org/sec1-v2.pdf"
                     "Standards for Efficient Cryptography 1 (SEC 1)"))))

;; Order the subtopics according to the order in which they were defined.
(xdoc::order-subtopics deterministic-ecdsa-secp256k1
  nil
  t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.1.  Key Parameters

;; "ECDSA uses the following key parameters:
;;
;;   E    an elliptic curve, defined over a given finite field
;;
;;   q    a sufficiently large prime number (at least 160 bits) that is a
;;        divisor of the curve order
;;
;;   G    a point of E, of order q"

;; Note: The curve order is a prime, so q is the curve order.

;; Note: secp256k1 uses "n" as the elliptic curve order, rather than "q".
;; Here's what we use for the above parameters:
;;   q (RFC 6979) -> (secp256k1-order) (our specification of secp256k1)
;;   G (RFC 6979) -> (secp256k1-generator) (our specification of secp256k1)

;; For convenience for following the RFC 6979 spec
;; we define *q* as a synonym for (secp256k1-order)

(defconst *q* (ecurve::secp256k1-order))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.3.  Integer Conversions

;; "Let qlen be the binary length of q.  qlen is the smallest integer
;;  such that q is less than 2^qlen.  This is the size of the binary
;;  representation of q without a sign bit (note that q, being a big
;;  prime, is odd, thus avoiding any ambiguity about the length of any
;;  integer equal to a power of 2)."

(defconst *qlen* (integer-length *q*))

;; Note: For secp256k1, it is the case that *qlen* is 256,
;; which is a multiple of 8.
;; However, the spec below is written to be more general,
;; following RFC 6979, so it should also work for a different curve
;; when we generalize our specification.

(assert! (and (< *q* (expt 2 *qlen*))
              (<= (expt 2 (- *qlen* 1)) *q*)))

;; "rlen is equal to qlen, rounded up to the next multiple of
;;  8 (if qlen is already a multiple of 8, then rlen equals qlen;
;;  otherwise, rlen is slightly larger, up to qlen+7).  Note that rlen is
;;  unrelated to the value r, the first half of a generated signature."

;; Note: Since *qlen* is 256, *rlen* equals *qlen*.
;; However, the spec below is written to be more general,
;; following RFC 6979, so it should also work for a different curve.

(defconst *rlen* (* 8 (ceiling *qlen* 8)))

;; "if qlen is already a multiple of 8, then rlen equals qlen"

(assert!
  (implies (equal (mod *qlen* 8) 0)
           (equal *rlen* *qlen*)))

;; "otherwise, rlen is slightly larger, up to qlen+7"

(assert!
  (implies (and (not (equal (mod *qlen* 8) 0)))
           (and (< *qlen* *rlen*)  ; slightly larger
                (< *rlen* (+ *qlen* 8)))))  ; up to qlen+7

;; "blen is the length (in bits) of an input sequence of bits and may
;;  vary between calls.  blen may be smaller than, equal to, or larger
;;  than qlen.'

(defun blen (bitstring) ; we leave this enabled since it's an abbreviation
  (declare (xargs :guard (and (true-listp bitstring)
                              (acl2::all-unsigned-byte-p 1 bitstring))))
  (len bitstring))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.3.1.  Bits and Octets

;; This section basically just says that an octet is 8 bits and
;; the bits are ordered from most to least significant bit.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.3.2.  Bit String to Integer

;; "1.  The sequence is first truncated or expanded to length qlen:
;;       *  if qlen < blen, then the qlen leftmost bits are kept, and
;;          subsequent bits are discarded;
;;  ...
;;  The bits2int transform can also be described in the following way:
;;  the input bit sequence (of length blen) is transformed into an
;;  integer using the big-endian convention.  Then, if blen is greater
;;  than qlen, the resulting integer is divided by two to the power
;;  blen-qlen."

;; Note: The result can be unintuitive when there are leading zeros.
;; Example: if qlen is 8 and blen is 9,
;; and the bit sequence is (0 0 0 0 0 0 0 0 1),
;; then truncating yields (0 0 0 0 0 0 0 0) which converts to 0.

(defund bits2int (bitstring)
  (declare (xargs :guard (and (true-listp bitstring)
                              (acl2::all-unsigned-byte-p 1 bitstring))))
  (let* ((blen* (blen bitstring))
         (adjusted-bitstring
          (if (< *qlen* blen*)
              (take *qlen* bitstring)
            (append (repeat (- *qlen* blen*) 0) bitstring))))
    (acl2::packbv *qlen* 1 adjusted-bitstring)))

(defthm natp-of-bits2int
  (natp (bits2int bitstring))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable bits2int))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.3.3.  Integer to Octet String

;;  "An integer value x less than q (and, in particular, a value that has
;;   been taken modulo q) can be converted into a sequence of rlen bits,
;;   where rlen = 8*ceil(qlen/8).  This is the sequence of bits obtained
;;   by big-endian encoding.  In other words, the sequence bits x_i (for i
;;   ranging from 0 to rlen-1) are such that:
;;
;;      x = x_0*2^(rlen-1) + x_1*2^(rlen-2) + ... + x_(rlen-1)
;;
;;   We call this transform int2octets.  Since rlen is a multiple of 8
;;   (the smallest multiple of 8 that is not smaller than qlen), then the
;;   resulting sequence of bits is also a sequence of octets, hence the
;;   name."

;; Note: They define an octet string as a bit string that
;; has a length that is a multiple of 8, but
;; we represent octet strings here as a list of bytes.
;; It is easy enough to convert back to bits with acl2::bytes-to-bits.

(defund int2octets (x)
  (declare (xargs :guard (and (natp x)
                              (< x *q*))))
  (acl2::unpackbv (/ *rlen* 8) 8 x))

(defthm all-integerp-of-int2octets
  (acl2::all-integerp (int2octets x))
  :hints (("Goal" :in-theory (enable int2octets))))

(defthm all-unsigned-byte-p-8-of-int2octets
  (acl2::all-unsigned-byte-p 8 (int2octets bitstring))
  :hints (("Goal" :in-theory (enable int2octets))))

(defthm len-of-int2octets
  (equal (len (int2octets x))
         (/ *rlen* 8))
  :hints (("Goal" :in-theory (enable int2octets))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.3.4.  Bit String to Octet String

(defund bits2octets (bitstring)
  (declare (xargs :guard (and (true-listp bitstring)
                              (acl2::all-unsigned-byte-p 1 bitstring))))
  ;; "1.  The input sequence b is converted into an integer value z1
  ;; through the bits2int transform:"
  (let ((z1 (bits2int bitstring)))
    ;; "2.  z1 is reduced modulo q, yielding z2 (an integer between 0 and
    ;; q-1, inclusive):"
    (let ((z2 (mod z1 *q*)))
      ;; "3.  z2 is transformed into a sequence of octets (a sequence of rlen
      ;; bits) by applying int2octets."
      (int2octets z2))))

;; The RFC mentions the following optimization, which we could perhaps
;; incorporate in the above function at some point (e.g. via MBE):
;;
;; "Note that since z1 is less than 2^qlen, that modular reduction
;; can be implemented with a simple conditional subtraction:
;; z2 = z1-q if that value is non-negative; otherwise, z2 = z1."

(defthm all-integerp-of-bits2octets
  (acl2::all-integerp (bits2octets bitstring))
  :hints (("Goal" :in-theory (enable bits2octets))))

(defthm all-unsigned-byte-p-8-of-bits2octets
  (acl2::all-unsigned-byte-p 8 (bits2octets bitstring))
  :hints (("Goal" :in-theory (enable bits2octets))))

(defthm len-of-bits2octets
  (equal (len (bits2octets bitstring))
         (/ *rlen* 8))
  :hints (("Goal" :in-theory (enable bits2octets))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.3.5.  Usage

;; "int2octets is the reverse of bits2int only when qlen is a multiple of
;;   8 and bit sequences already have length qlen"

;; We may add theorems asserting this property in the future.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 2.4. Signature Generation

;; "Signature generation uses a cryptographic hash function H and an
;;   input message m."

;; RFC 6979 does not specify a particular hash function H,
;; i.e. the RFC is parameterized over H.
;; Our specification provides an API function to sign an already hashed message,
;; so that the user of our specification can invoke any hash function
;; before invoking our API function.
;; As an added convenience, though, our API also provides signature functions
;; that apply SHA-256 and Keccak-256 before producing the signature;
;; we may add more such convenience functions in the future.

;; Signature generation also uses
;; a random or pseudorandom value k in [1, q - 1],
;; where q is the elliptic curve order above.

;;   "Most of the remainder of this document will revolve around the process
;;    used to generate k."

;; We go beyond RFC 6979 by producing, besides the signature proper (r, s),
;; also some additional information for recovering the public key.
;; This is explained in SEC 1 Section 4.1.6.
;; To recover the public key associated to the private key used for signing,
;; it suffices to recover the ephemeral public key kG, denoted as R in SEC 1.
;; Given a value of r, there are at most 2(h+1) possible values of R,
;; where here h is the cofactor of the curve (using the notation of SEC 1):
;; these possible values of R result from the two nested loops
;; in SEC 1 Section 4.1.6 (Steps 1 and 1.6).
;; The outer loop tries h+1 successive values of Rx (the x coordinate of R),
;; namely r, r+n, r+2n, ..., r+hn, where here n is the order of the curve.
;; For each such Rx, the inner loop tries the two possible values of Ry
;; that are each other's negation (the curve is symmetric w.r.t. the x axis).
;; This means that the exact value of R can be identified by two values:
;; - the j such that Rx = r + jn;
;; - a bit, or boolean, indicating whether Ry is odd or even
;;   (in the prime field, negation changes the parity of a value).
;; Thus, our signing operations return these two additional values.
;; In the case of secp256k1 (which currently this file is specialized to),
;; the cofactor h is 1 and therefore there are at most two possible Rx values.
;; However, we write our code more generically, extensible to other curves,
;; by returning j = (floor Rx n).

;; ecdsa-sign-given-k(mh privkey k)
;; Args:
;;   mh is the hashed input message as a list of bits
;;   privkey is the private key
;;   k is the random or pseudorandom "ephemeral private key", which must be
;;     in the range [1 .. q - 1] (inclusive)
;; Returns:
;;   (mv error? x-index y-even? r s)
;; where:
;;   error? is T if the operation fails, NIL if it succeeds
;;          (if T, then the other results have irrelevant values)
;;   (r, s) is the signature
;;   x-index is the information to recover Rx (see explanation above)
;;   y-even? is the information to recover Ry (see explanation above)
;;
;; Note: This does not repeat any computations for improper results of r or s.
;; (Also note: we test this function independently of the overall signing
;; function, i.e. in a separate test run.)

(defund ecdsa-sign-given-k (mh privkey k)
  (declare (xargs :guard (and (true-listp mh)
                              (acl2::all-unsigned-byte-p 1 mh)
                              (posp privkey)
                              (< privkey *q*)
                              (posp k)
                              (< k *q*))
                  :guard-hints (("Goal"
                                 :use
                                 ((:instance ecurve::natp-of-car-of-secp256k1*
                                   (s k)
                                   (point (ecurve::secp256k1-generator)))
                                  (:instance ecurve::natp-of-cdr-of-secp256k1*
                                   (s k)
                                   (point (ecurve::secp256k1-generator))))
                                 :in-theory
                                 (e/d (pfield::fep)
                                      (ecurve::natp-of-car-of-secp256k1*
                                       ecurve::natp-of-cdr-of-secp256k1*))))))

;; "1. H(m) is transformed into an integer modulo q using the bits2int
;;     transform and an extra modular reduction:
;;
;;        h = bits2int(H(m)) mod q
;;
;;     As was noted in the description of bits2octets, the extra modular
;;     reduction is no more than a conditional subtraction.

;; Note: We raised the call of the hash function up to the API level,
;; so that alternate hash functions can be used. mh is the message hash.

  (b* ((h (mod (bits2int mh) *q*))

;; "2.  A random value modulo q, dubbed k, is generated.  ..."
;; Note: k is generated in section 3, below.  After that we define
;; the deterministic ECDSA sign operation, which first generates the k
;; and then calls this function, ecdsa-sign-given-k.

;; "3. A value r (modulo q) is computed from k and the key parameters:
;;    ...
;;    *  For ECDSA: the point kG is computed; its X coordinate (a
;;       member of the field over which E is defined) is converted to
;;       an integer, which is reduced modulo q, yielding r.
;;
;;    If r turns out to be zero, a new k should be selected and r
;;    computed again (this is an utterly improbable occurrence).

       (new-point (secp256k1* k (secp256k1-generator)))
       (rx (car new-point))
       (ry (cdr new-point))
       (r (mod rx *q*))
       ((when (= r 0)) (mv t 0 nil 0 0))
       (x-index (floor rx *q*))
       (y-even? (evenp ry))

;; 4.  The value s (modulo q) is computed:
;;
;;        s = (h+x*r)/k mod q
;;
;; Note: An official erratum (https://www.rfc-editor.org/errata/rfc6979)
;; adds these two lines:
;;     If s turns out to be zero, a new k should be selected and r
;;     and s computed again (a similarly improbable occurrence).
;; End of erratum.
;;
;;     The pair (r, s) is the signature.  How a signature is to be
;;     encoded is not covered by the DSA and ECDSA standards themselves;
;;     a common way is to use a DER-encoded ASN.1 structure (a SEQUENCE
;;     of two INTEGERs, for r and s, in that order).

;; Note: "x" is defined in section 2.2 as the private key,
;; (the public key is U = xG, where G is the EC generator point).

       (s (mod (* (pfield::inv k *q*) ; 1/k
                  (mod (+ h (* privkey r)) *q*)) ; h+xr
               *q*))
       ((when (= s 0)) (mv t 0 nil 0 0)))

    (mv nil x-index y-even? r s)))

(defthm booleanp-of-mv-nth-0-of-ecdsa-sign-given-k
  (booleanp (mv-nth 0 (ecdsa-sign-given-k mh privkey k)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-given-k))))

(encapsulate ()
  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm natp-of-mv-nth-1-of-ecdsa-sign-given-k
    (natp (mv-nth 1 (ecdsa-sign-given-k mh privkey k)))
    :rule-classes :type-prescription
    :hints (("Goal"
             :use (:instance ecurve::natp-of-car-of-secp256k1*
                   (s k) (point (ecurve::secp256k1-generator)))
             :in-theory (enable ecdsa-sign-given-k)))))

(defthm booleanp-of-mv-nth-2-of-ecdsa-sign-given-k
  (booleanp (mv-nth 2 (ecdsa-sign-given-k mh privkey k)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-given-k))))

(defthm posp-of-mv-nth-3-of-ecdsa-sign-given-k
  (implies (not (mv-nth 0 (ecdsa-sign-given-k mh privkey k)))
           (posp (mv-nth 3 (ecdsa-sign-given-k mh privkey k))))
  :rule-classes :type-prescription
  :hints (("Goal"
           :use (:instance ecurve::natp-of-car-of-secp256k1*
                 (s k) (point (ecurve::secp256k1-generator)))
           :in-theory (enable ecdsa-sign-given-k))))

(defthm <-*q*-of-mv-nth-3-of-ecdsa-sign-given-k
  (< (mv-nth 3 (ecdsa-sign-given-k mh privkey k))
     *q*)
  :rule-classes :linear
  :hints (("Goal"
           :use (:instance ecurve::natp-of-car-of-secp256k1*
                 (s k) (point (ecurve::secp256k1-generator)))
           :in-theory (enable ecdsa-sign-given-k))))

(defthm posp-of-mv-nth-4-of-ecdsa-sign-given-k
  (implies (and (not (mv-nth 0 (ecdsa-sign-given-k mh privkey k)))
                (posp privkey)
                (posp k))
           (posp (mv-nth 4 (ecdsa-sign-given-k mh privkey k))))
  :rule-classes :type-prescription
  :hints (("Goal"
           :use (:instance ecurve::natp-of-car-of-secp256k1*
                 (s k) (point (ecurve::secp256k1-generator)))
           :in-theory (enable ecdsa-sign-given-k))))

(defthm <-*q*-of-mv-nth-4-of-ecdsa-sign-given-k
  (implies (and (posp privkey)
                (posp k))
           (< (mv-nth 4 (ecdsa-sign-given-k mh privkey k))
              *q*))
  :rule-classes :linear
  :hints (("Goal"
           :use (:instance ecurve::natp-of-car-of-secp256k1*
                 (s k) (point (ecurve::secp256k1-generator)))
           :in-theory (enable ecdsa-sign-given-k))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SEC 1 Section 4.1.3 points out that if (r, s) is a valid signature,
;; then (r, -s mod q) is an equivalent signature,
;; where we use q for the order of the curve, as in RFC 6979.
;; Thus, if desired, it is always possible to produce a signature with s < q/2;
;; note that q/2 = i + 1/2 for some integer, because q is odd.
;; Suppose that s >= q/2, which is equivalent to s > q/2 since q/2 = i + 1/2:
;; then q - s < q - q/2 = q/2.
;; In this case, the maximum value of s is (floor q 2), or (ash q -1),
;; captured by the constant *q/2* below.
;; We introduce a function that ensures that a signature has an s
;; that does not exceed this maximum.
;; This function operates not only on the signature (r, s) proper,
;; but also on the public key recovery information:
;; examination of SEC 1 Section 4.1.6 Step 1.6.1 shows that
;; if s is negated, then R must be negated
;; in order for the calculated Q (the recovered public key) to remain the same:
;; this means that we need to flip the parity information for Ry,
;; while leaving the information for Rx unchanged.

(defconst *q/2* (ash *q* -1))

(defund ecdsa-ensure-s-below-q/2 (x-index y-even? r s)
  (declare (xargs :guard (and (natp x-index)
                              (booleanp y-even?)
                              (posp r)
                              (< r *q*)
                              (posp s)
                              (< s *q*))))
  (if (<= s *q/2*)
      (mv x-index y-even? r s) ; no change
    (mv x-index (not y-even?) r (- *q* s))))

(defthm mv-nth-0-of-ecdsa-ensure-s-below-q/2
  (equal (mv-nth 0 (ecdsa-ensure-s-below-q/2 x-index y-even? r s))
         x-index)
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable ecdsa-ensure-s-below-q/2))))

(defthm booleanp-of-mv-nth-1-of-ecdsa-ensure-s-below-q/2
  (implies (booleanp y-even?)
           (booleanp (mv-nth 1 (ecdsa-ensure-s-below-q/2 x-index y-even? r s))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-ensure-s-below-q/2))))

(defthm mv-nth-2-of-ecdsa-ensure-s-below-q/2
  (equal (mv-nth 2 (ecdsa-ensure-s-below-q/2 x-index y-even? r s))
         r)
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable ecdsa-ensure-s-below-q/2))))

(defthm posp-of-mv-nth-3-of-ecdsa-ensure-s-below-q/2
  (implies (and (posp s)
                (< s *q*))
           (posp (mv-nth 3 (ecdsa-ensure-s-below-q/2 x-index y-even? r s))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-ensure-s-below-q/2))))

(defthm <-*q*-of-mv-nth-3-of-ecdsa-ensure-s-below-q/2
  (implies (< s *q*)
           (< (mv-nth 3 (ecdsa-ensure-s-below-q/2 x-index y-even? r s)) *q*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-ensure-s-below-q/2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 3.  Deterministic DSA and ECDSA
;;
;; Note: Just ECDSA in this file.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 3.1.1.  HMAC

;;  "HMAC [RFC 2104] is a construction of a Message Authentication Code
;;   using a hash function and a secret key.  Here, we use HMAC with the
;;   same hash function H as the one used to process the input message
;;   prior to signature generation or verification.
;;
;;   We denote the process of applying HMAC with key K over data V by:
;;
;;      HMAC_K(V)
;;
;;   which returns a sequence of bits of length hlen (the output length of
;;   the underlying hash function H)."

;; Note: For now our spec for this is the function
;;   hmac-sha-256(key,data)
;; where
;;   KEY is a list of bytes (unsigned 8-bit bytes) and
;;   DATA is a list of bits.
;; In the future we may generalize this file to allow other HMACs.

;; Despite our choice of HMAC-SHA-256 as the HMAC function here,
;; we allow other choices for H, as discussed previously in this file.
;; RFC 6979 says that hlen is the number of output bits of H,
;; which in the RFC is also the number of output bits of HMAC:
;; in the RFC 6979, hlen is used in the computation of k using HMAC,
;; so here we define hlen based on our choice of HMAC-SHA-256,
;; not based on possibly other hash functions that we allow here as H.
;; For SHA-256, hlen is 256.

(defconst *hlen* 256)

(assert! (natp (/ *hlen* 8)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 3.2. Generation of k


;; - - - - - - - -
;; Discussion of the termination conditions
;;
;; There are a number of places where RFC 6979 states
;; that if the generated k doesn't have a "proper value"
;; (i.e., it is outside a given range), or
;; if the signature computed from the k is invalid (e.g. r is 0),
;; then Step 3.2(h) is repeated until the resulting values are acceptable.
;;
;; Specifying this loop as a terminating ACL2 function is problematic,
;; because the whole point of HMAC is to produce randomly-looking values,
;; making it difficult to analyze the sequence of k values
;; produced by the procedure described in the RFC.
;; Although it seems like the successive k values have a
;; flat distribution, if there is a cycle of improper k values
;; then the presumption that the procedure terminates
;; could be false.
;;
;; (When k is generated randomly, i.e. non-deterministically,
;; then termination can be proved only probabilistically.)
;;
;; It is also thought that the number of repetitions of Step 3.2(h)
;; is unlikely to be more than 3.  (Probabilistic arguments
;; of how unlikely it is that R repetitions could also be made,
;; perhaps treating HMAC as a random source.)
;;
;; Given the current thinking, and to avoid complicating this
;; specification, we introduce counters that
;; allow up to a certain number of computations of k, and
;; if exceeded, an error is returned. The termination proofs
;; need not iterate to the maximum limit, so a large limit
;; will not be a problem.
;;
;; Since all existing users of RFC 6979 that we know of
;; blithely repeat 3.2(h) until the k is proper, and since
;; we don't know of any inputs that cause infinite looping
;; of this step, we are fairly confident that executing
;; this spec will terminate quickly without error.
;; Note also that executing a loop forever is practically indistinguishable
;; from executing a loop an extremely large number of times,
;; say such that it would take 1M years, or just 1K years --
;; the software will be interrupted before the loop actually terminates.


;; - - - - - - - -
;; Structure of the functional spec
;;
;; If the first k generated is improper, the next k generated
;; must make use of the internal state from the first computation.
;; This state consists of K and V, where K is uppercase,
;; i.e. it is distinct from the lowercase k:
;; K is a sequence of bytes, while k is a natural number.
;; Therefore, we make each computation return the internal K and V.
;;
;; The first computation of k takes the message hash mh and the
;; private key ("x" in RFC 6979), but does not require an
;; input of a previous K or V.
;; It must do setup work: 3.2 steps (a) through (g).
;; Then it does step (h) except for (h)(3), the "otherwise" section.
;;
;; A successive computation of k does not take the message hash mh
;; and private key, but only looks at the previous K and V.
;; It must do setup work: (h)(3), the "otherwise" section.
;; Then it does step (h) except for (h)(3), the "otherwise" section.
;;
;; This suggests splitting the computation of k into building blocks:
;;   first-k-setup, next-k-setup, and generate-k.
;; These will be used by:
;;   generate-first-k: calls first-k-setup, generate-k
;; and
;;   generate-next-k: calls next-k-setup, generate-k
;;
;; Those functions are in turn used by functions that check if
;; the k is in the correct range, and if not, generate another one.
;;   generate-first-k-in-range: calls
;;     generate-first-k, generate-next-k-in-range
;;   generate-next-k-in-range: calls
;;     generate-next-k, generate-next-k-in-range (recursively)
;;
;; Finally, we must continue to generate k values if the signature
;; is unacceptable.  So the API function ecdsa-sign-deterministic-prehashed
;; first calls:
;;   generate-first-k-in-range and ecdsa-sign-given-k,
;; and then if the signature is unacceptable, it calls:
;;   ecdsa-sign-deterministic-next
;; which calls generate-next-k-in-range and ecdsa-sign-given-k,
;;   and if the signature is still unacceptable, it
;;   calls itself recursively.
;;
;; The recursive functions
;;   generate-next-k-in-range
;;   ecdsa-sign-deterministic-next
;; and their callers keep track of the number of k values generated,
;; and give up with an error value if 2^256 iterations happen without
;; an acceptable signature; this would take an impossibly long time.
;;
;; Keep in mind the distinction between uppercase K and lowercase k.
;; Even though ACL2 is case-insensitive, we will use uppercase variable names
;; for K (as well as for V), and lowercase variable names for k.
;; When the two variables appear together, or for greater clarity,
;; we will use the longer names 'small-k' and 'large-K'.

;; - - - - - - - -
;; first-k-setup
;;
;; Runs 3.2 (a) through (g).
;; Returns (mv large-K V), i.e. the internal state of computation

(defund first-k-setup (mh privkey)
  (declare (xargs :guard (and (true-listp mh)
                              (acl2::all-unsigned-byte-p 1 mh)
                              (posp privkey)
                              (< privkey *q*))))

;; 3.2. Generation of k
;;
;;   Given the input message m, the following process is applied:
;;
;;   a.  Process m through the hash function H, yielding:
;;
;;          h1 = H(m)
;;
;;       (h1 is a sequence of hlen bits).

;; Note: This step is raised to the interface functions,
;; so that alternate hash functions can be used.
;; Now we just bind h1 to the parameter mh.

   (let ((h1 mh))

;;   b.  Set:
;;
;;          V = 0x01 0x01 0x01 ... 0x01
;;
;;       such that the length of V, in bits, is equal to 8*ceil(hlen/8).
;;       For instance, on an octet-based system, if H is SHA-256, then V
;;       is set to a sequence of 32 octets of value 1.  Note that in this
;;       step and all subsequent steps, we use the same H function as the
;;       one used in step 'a' to process the input message; this choice
;;       will be discussed in more detail in Section 3.6.
;;
;;   c.  Set:
;;
;;          K = 0x00 0x00 0x00 ... 0x00
;;
;;       such that the length of K, in bits, is equal to 8*ceil(hlen/8).

    (let ((V1 (repeat (/ *hlen* 8) 1))
          (K0 (repeat (/ *hlen* 8) 0)))

;;   d.  Set:
;;
;;          K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1))
;;
;;       where '||' denotes concatenation.  In other words, we compute
;;       HMAC with key K, over the concatenation of the following, in
;;       order: the current value of V, a sequence of eight bits of value
;;       0, the encoding of the (EC)DSA private key x, and the hashed
;;       message (possibly truncated and extended as specified by the
;;       bits2octets transform).  The HMAC result is the new value of K.
;;       Note that the private key x is in the [1, q-1] range, hence a
;;       proper input for int2octets, yielding rlen bits of output, i.e.,
;;       an integral number of octets (rlen is a multiple of 8).

      (let ((K1 (hmac::hmac-sha-256
                 K0
                 (append (bytes-to-bits V1)
                         (repeat 8 0)
                         (bytes-to-bits (int2octets privkey))
                         (bytes-to-bits (bits2octets h1))))))

;;   e.  Set:
;;
;;          V = HMAC_K(V)

        (let ((V2 (hmac::hmac-sha-256 K1 (bytes-to-bits V1))))

;;   f.  Set:
;;
;;          K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1))
;;
;;       Note that the "internal octet" is 0x01 this time.

          (let ((K2 (hmac::hmac-sha-256
                     K1
                     (append (bytes-to-bits V2)
                             '(0 0 0 0 0 0 0 1)
                             (bytes-to-bits (int2octets privkey))
                             (bytes-to-bits (bits2octets h1))))))

;;   g.  Set:
;;
;;          V = HMAC_K(V)

            (let ((V3 (hmac::hmac-sha-256 k2 (bytes-to-bits V2))))

              ;; Return the current K and V
              (mv K2 V3)
              )))))))

(defthm true-listp-of-mv-nth-0-of-first-k-setup
  (true-listp (mv-nth 0 (first-k-setup mh privkey)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable first-k-setup))))

(defthm all-unsigned-byte-p-8-of-mv-nth-0-of-first-k-setup
  (acl2::all-unsigned-byte-p 8 (mv-nth 0 (first-k-setup mh privkey)))
  :hints (("Goal" :in-theory (enable first-k-setup))))

(defthm len-of-mv-nth-0-of-first-k-setup
  (equal (len (mv-nth 0 (first-k-setup mh privkey)))
         32)
  :hints (("Goal" :in-theory (enable first-k-setup))))

(defthm true-listp-of-mv-nth-1-of-first-k-setup
  (true-listp (mv-nth 1 (first-k-setup mh privkey)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable first-k-setup))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-first-k-setup
  (acl2::all-unsigned-byte-p 8 (mv-nth 1 (first-k-setup mh privkey)))
  :hints (("Goal" :in-theory (enable first-k-setup))))

(defthm len-of-mv-nth-1-of-first-k-setup
  (equal (len (mv-nth 1 (first-k-setup mh privkey)))
         32)
  :hints (("Goal" :in-theory (enable first-k-setup))))

;; - - - - - - - -
;; mac-and-pad-T
;;
;; Runs step 3.2(h)(2)
;; Returns (mv Tbits V)
;; Note that K is only used by this function, not updated:
;; thus, only V is returned -- besides the bits of T.

(defund mac-and-pad-T (K V Tbits)
  (declare (xargs :guard (and (true-listp K)
                              (acl2::unsigned-byte-listp 8 K)
                              (= (len K) 32)
                              (true-listp V)
                              (acl2::unsigned-byte-listp 8 V)
                              (= (len V) 32)
                              (true-listp Tbits)
                              (acl2::unsigned-byte-listp 1 Tbits))))
  (declare (xargs :measure (nfix (- *qlen* (len Tbits)))))
  (if (<= *qlen* (len Tbits))
      (mv Tbits V)
    (let* ((V1 (hmac::hmac-sha-256 k (bytes-to-bits V)))
           (Tbits1 (append Tbits (bytes-to-bits V1))))
      (mac-and-pad-T K V1 Tbits1))))

;;       2.  While tlen < qlen, do the following:
;;
;;              V = HMAC_K(V)
;;
;;              T = T || V

(defthm true-listp-of-mv-nth-0-of-mac-and-pad-T
  (implies (true-listp Tbits)
           (true-listp (mv-nth 0 (mac-and-pad-T K V Tbits))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable mac-and-pad-T))))

(defthm all-unsigned-byte-p-1-of-mv-nth-0-of-mac-and-pad-T
  (implies (acl2::all-unsigned-byte-p 1 Tbits)
           (acl2::all-unsigned-byte-p 1 (mv-nth 0 (mac-and-pad-T K V Tbits))))
  :hints (("Goal" :in-theory (enable mac-and-pad-T))))

(defthm true-listp-of-mv-nth-1-of-mac-and-pad-T
  (implies (true-listp V)
           (true-listp (mv-nth 1 (mac-and-pad-T K V Tbits))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable mac-and-pad-T))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-mac-and-pad-T
  (implies (acl2::all-unsigned-byte-p 8 V)
           (acl2::all-unsigned-byte-p 8 (mv-nth 1 (mac-and-pad-T K V Tbits))))
  :hints (("Goal" :in-theory (enable mac-and-pad-T))))

(defthm len-of-mv-nth-1-of-mac-and-pad-T
  (implies (equal (len V) 32)
           (equal (len (mv-nth  1 (mac-and-pad-T K V Tbits)))
                  32))
  :hints (("Goal" :in-theory (enable mac-and-pad-T))))

;; - - - - - - - -
;; next-k-setup
;;
;; Runs step 3.2(h)(3)(after "otherwise")
;; Returns (mv large-K V), i.e. the internal state of computation

(defund next-k-setup (prev-K prev-V)
  (declare (xargs :guard (and (true-listp prev-K)
                              (acl2::unsigned-byte-listp 8 prev-K)
                              (= (len prev-K) 32)
                              (true-listp prev-V)
                              (acl2::unsigned-byte-listp 8 prev-V)
                              (= (len prev-V) 32))))

;;           Otherwise, compute:
;;
;;              K = HMAC_K(V || 0x00)
;;
;;              V = HMAC_K(V)

  (let ((next-K (hmac::hmac-sha-256 prev-K
                                    (append (bytes-to-bits prev-V)
                                            (repeat 8 0)))))
    (let ((next-V (hmac::hmac-sha-256 next-K (bytes-to-bits prev-V))))
      (mv next-K next-V))))

(defthm true-listp-of-mv-nth-0-of-next-k-setup
  (true-listp (mv-nth 0 (next-k-setup prev-K prev-V)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable next-k-setup))))

(defthm all-unsigned-byte-p-8-of-mv-nth-0-of-next-k-setup
  (acl2::all-unsigned-byte-p 8 (mv-nth 0 (next-k-setup prev-K prev-V)))
  :hints (("Goal" :in-theory (enable next-k-setup))))

(defthm len-of-mv-nth-0-of-next-k-setup
  (equal (len (mv-nth 0 (next-k-setup prev-K prev-V)))
         32)
  :hints (("Goal" :in-theory (enable next-k-setup))))

(defthm true-listp-of-mv-nth-1-of-next-k-setup
  (true-listp (mv-nth 1 (next-k-setup prev-K prev-V)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable next-k-setup))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-next-k-setup
  (acl2::all-unsigned-byte-p 8 (mv-nth 1 (next-k-setup prev-K prev-V)))
  :hints (("Goal" :in-theory (enable next-k-setup))))

(defthm len-of-mv-nth-1-of-next-k-setup
  (equal (len (mv-nth 1 (next-k-setup prev-K prev-V)))
         32)
  :hints (("Goal" :in-theory (enable next-k-setup))))


;; - - - - - - - -
;; generate-k
;;
;; Runs 3.2(h), except for: step 3.2(h)(3)(after "otherwise")
;; Returns (mv small-k large-K V),
;;         where small-k is the candidate ephemeral private key,
;;         while large-K and V are the internal state of computation

(defund generate-k (K-from-setup V-from-setup)
  (declare (xargs :guard (and (true-listp K-from-setup)
                              (acl2::unsigned-byte-listp 8 K-from-setup)
                              (= (len K-from-setup) 32)
                              (true-listp V-from-setup)
                              (acl2::unsigned-byte-listp 8 V-from-setup)
                              (= (len V-from-setup) 32))))

;;  h.  Apply the following algorithm until a proper value is found for
;;       k:

;;       1.  Set T to the empty sequence.  The length of T (in bits) is
;;           denoted tlen; thus, at that point, tlen = 0.

  (let ((Tbits0 '()))

;;       2.  While tlen < qlen, do the following:
;;
;;              V = HMAC_K(V)
;;
;;              T = T || V

    ;; Note, step 2 is factored out to a recursive function mac-and-pad-T
    (mv-let (Tbits1 V1) (mac-and-pad-T K-from-setup V-from-setup Tbits0)

;;       3.  Compute:
;;
;;              k = bits2int(T)

      (mv (bits2int Tbits1) K-from-setup V1))))

;; Note: generate-k returns k, along with K and V.
;;  The logic about whether k is proper (in the right range)
;;  or whether it results in a signature that is proper,
;;  is outside of this function.
;;  Also, the "otherwise" computation at the end of step 3
;;  is done in next-k-setup().]
;;
;;           If that value of k is within the [1,q-1] range, and is
;;           suitable for DSA or ECDSA (i.e., it results in an r value
;;           that is not 0; see Section 3.4), then the generation of k is
;;           finished.  The obtained value of k is used in DSA or ECDSA.
;;           Otherwise, compute:
;; [...elided]
;;   Please note that when k is generated from T, the result of bits2int
;;   is compared to q, not reduced modulo q.

(defthm natp-of-mv-nth-0-of-generate-k
  (natp (mv-nth 0 (generate-k K-from-setup V-from-setup)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-k))))

(defthm true-listp-of-mv-nth-1-of-generate-k
  (implies (true-listp K-from-setup)
           (true-listp (mv-nth 1 (generate-k K-from-setup V-from-setup))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-k))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-generate-k
  (implies (acl2::all-unsigned-byte-p 8 K-from-setup)
           (acl2::all-unsigned-byte-p
            8 (mv-nth 1 (generate-k K-from-setup V-from-setup))))
  :hints (("Goal" :in-theory (enable generate-k))))

(defthm len-of-mv-nth-1-of-generate-k
  (implies (equal (len K-from-setup)
                  32)
           (equal (len (mv-nth 1 (generate-k K-from-setup V-from-setup)))
                  32))
  :hints (("Goal" :in-theory (enable generate-k))))

(defthm true-listp-of-mv-nth-2-of-generate-k
  (implies (true-listp V-from-setup)
           (true-listp (mv-nth 2 (generate-k K-from-setup V-from-setup))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-k))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-generate-k
  (implies (acl2::all-unsigned-byte-p 8 V-from-setup)
           (acl2::all-unsigned-byte-p
            8 (mv-nth 2 (generate-k K-from-setup V-from-setup))))
  :hints (("Goal" :in-theory (enable generate-k))))

(defthm len-of-mv-nth-2-of-generate-k
  (implies (equal (len V-from-setup)
                  32)
           (equal (len (mv-nth 2 (generate-k K-from-setup V-from-setup)))
                  32))
  :hints (("Goal" :in-theory (enable generate-k))))


;; - - - - - - - -
;; generate-first-k (m privkey)
;;
;; Returns (mv small-k large-K V),
;;         where small-k is the candidate ephemeral private key,
;;         while large-K and V are the internal state of computation
;; The large-K and V must be used in a subsequent call to generate-next-k
;; if the small-k is not "proper" (i.e., not within the correct range
;; or not leading to a valid signature).

(defund generate-first-k (mh privkey)
  (declare (xargs :guard (and (true-listp mh)
                              (acl2::all-unsigned-byte-p 1 mh)
                              (posp privkey)
                              (< privkey *q*))))
  (mv-let (k-from-setup V-from-setup) (first-k-setup mh privkey)
    (generate-k k-from-setup V-from-setup)))

(defthm natp-of-mv-nth-0-of-generate-first-k
  (natp (mv-nth 0 (generate-first-k mh privkey)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-first-k))))

(defthm true-listp-of-mv-nth-1-of-generate-first-k
  (true-listp (mv-nth 1 (generate-first-k K-from-setup V-from-setup)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-first-k))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-generate-first-k
  (acl2::all-unsigned-byte-p
   8 (mv-nth 1 (generate-first-k K-from-setup V-from-setup)))
  :hints (("Goal" :in-theory (enable generate-first-k))))

(defthm len-of-mv-nth-1-of-generate-first-k
  (equal (len (mv-nth 1 (generate-first-k K-from-setup V-from-setup)))
         32)
  :hints (("Goal" :in-theory (enable generate-first-k))))

(defthm true-listp-of-mv-nth-2-of-generate-first-k
  (true-listp (mv-nth 2 (generate-first-k K-from-setup V-from-setup)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-first-k))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-generate-first-k
  (acl2::all-unsigned-byte-p
   8 (mv-nth 2 (generate-first-k K-from-setup V-from-setup)))
  :hints (("Goal" :in-theory (enable generate-first-k))))

(defthm len-of-mv-nth-2-of-generate-first-k
  (equal (len (mv-nth 2 (generate-first-k K-from-setup V-from-setup)))
         32)
  :hints (("Goal" :in-theory (enable generate-first-k))))


;; - - - - - - - -
;; generate-next-k (prev-k prev-V)
;;
;; Returns (mv small-k large-K V),
;;         where small-k is the candidate ephemeral private key,
;;         while large-K and V are the internal state of computation

(defund generate-next-k (prev-K prev-V)
  (declare (xargs :guard (and (true-listp prev-K)
                              (acl2::unsigned-byte-listp 8 prev-K)
                              (= (len prev-K) 32)
                              (true-listp prev-V)
                              (acl2::unsigned-byte-listp 8 prev-V)
                              (= (len prev-V) 32))))
  (mv-let (k-from-setup V-from-setup) (next-k-setup prev-k prev-V)
    (generate-k k-from-setup V-from-setup)))

(defthm natp-of-mv-nth-0-of-generate-next-k
  (natp (mv-nth 0 (generate-next-k prev-K prev-V)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-next-k))))

(defthm true-listp-of-mv-nth-1-of-generate-next-k
  (true-listp (mv-nth 1 (generate-next-k prev-K prev-V)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-next-k))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-generate-next-k
  (acl2::all-unsigned-byte-p 8 (mv-nth 1 (generate-next-k prev-K prev-V)))
  :hints (("Goal" :in-theory (enable generate-next-k))))

(defthm len-of-mv-nth-1-of-generate-next-k
  (equal (len (mv-nth 1 (generate-next-k prev-K prev-V)))
         32)
  :hints (("Goal" :in-theory (enable generate-next-k))))

(defthm true-listp-of-mv-nth-2-of-generate-next-k
  (true-listp (mv-nth 2 (generate-next-k prev-K prev-V)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-next-k))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-generate-next-k
  (acl2::all-unsigned-byte-p 8 (mv-nth 2 (generate-next-k prev-K prev-V)))
  :hints (("Goal" :in-theory (enable generate-next-k))))

(defthm len-of-mv-nth-2-of-generate-next-k
  (equal (len (mv-nth 2 (generate-next-k prev-K prev-V)))
         32)
  :hints (("Goal" :in-theory (enable generate-next-k))))


;; - - - - - - - -
;; Functions that repeat the k generation
;; until the k is in range.

;; The returned k might still not be "proper" if
;; the signature computed from it is not proper.

;; Make this ridiculously large to make it clear
;; that proofs are not iterating all values,
;; and to ensure that in practice the calculation will never terminate
;; due to exhausting this limit (it would take an unreasonable number of years).

(defconst *max-ecdsa-sign-k-attempts* (expt 2 256))

;; Returns (mv small-k large-K V remaining-iters),
;;         where small-k is the candidate ephemeral private key,
;;         large-K and V are the internal state of computation,
;;         and remaining-iters is the remaining number of iterations
;; If remaining-iters reaches zero, which cannot happen in practice,
;; then returns all zeros.

(defund generate-next-k-in-range (prev-K prev-V max-iters)
  (declare (xargs :guard (and (true-listp prev-K)
                              (acl2::unsigned-byte-listp 8 prev-K)
                              (= (len prev-K) 32)
                              (true-listp prev-V)
                              (acl2::unsigned-byte-listp 8 prev-V)
                              (= (len prev-V) 32)
                              (natp max-iters))
                  :measure (nfix max-iters)))
  (if (zp max-iters)
      (mv 0 (repeat 32 0) (repeat 32 0) 0)
    (mv-let (small-k large-K V) (generate-next-k prev-K prev-V)
      (if (and (< 0 small-k) (< small-k *q*))
          (mv small-k large-K V (- max-iters 1))
        (generate-next-k-in-range large-K V (- max-iters 1))))))

(defthm natp-of-mv-nth-0-of-generate-next-k-in-range
  (natp (mv-nth 0 (generate-next-k-in-range prev-K prev-V max-iters)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm mv-nth-0-of-generate-next-k-in-range-bound
  (< (mv-nth 0 (generate-next-k-in-range prev-K prev-V max-iters))
     *q*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm true-listp-of-mv-nth-1-of-generate-next-k-in-range
  (true-listp (mv-nth 1 (generate-next-k-in-range prev-K prev-V max-iters)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-generate-next-k-in-range
  (acl2::all-unsigned-byte-p
   8 (mv-nth 1 (generate-next-k-in-range prev-K prev-V max-iters)))
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm len-of-mv-nth-1-of-generate-next-k-in-range
  (equal (len (mv-nth 1 (generate-next-k-in-range prev-K prev-V max-iters)))
         32)
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm true-listp-of-mv-nth-2-of-generate-next-k-in-range
  (true-listp (mv-nth 2 (generate-next-k-in-range prev-K prev-V max-iters)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-generate-next-k-in-range
  (acl2::all-unsigned-byte-p
   8 (mv-nth 2 (generate-next-k-in-range prev-K prev-V max-iters)))
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm len-of-mv-nth-2-of-generate-next-k-in-range
  (equal (len (mv-nth 2 (generate-next-k-in-range prev-K prev-V max-iters)))
         32)
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm natp-of-mv-nth-3-of-generate-next-k-in-range
  (natp (mv-nth 3 (generate-next-k-in-range prev-K prev-V max-iters)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

(defthm mv-nth-2-of-generate-next-k-in-range-bound
  (implies (natp max-iters)
           (<= (mv-nth 3 (generate-next-k-in-range prev-k prev-V max-iters))
               max-iters))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable generate-next-k-in-range))))

;; Returns (mv small-k large-K V remaining-iters),
;;         where small-k is the candidate ephemeral private key,
;;         large-K and V are the internal state of computation,
;;         and remaining-iters is the remaining number of iterations
;; If remaining-iters reaches zero, which cannot happen in practice,
;; then returns all zeros.

(defund generate-first-k-in-range (mh privkey)
  (declare (xargs :guard (and (true-listp mh)
                              (acl2::all-unsigned-byte-p 1 mh)
                              (posp privkey)
                              (< privkey *q*))))
  (mv-let (small-k large-K V) (generate-first-k mh privkey)
    (if (and (< 0 small-k) (< small-k *q*))
        (mv small-k large-K V (- *max-ecdsa-sign-k-attempts* 1))
      (generate-next-k-in-range large-K V (- *max-ecdsa-sign-k-attempts* 1)))))

(defthm natp-of-mv-nth-0-of-generate-first-k-in-range
  (natp (mv-nth 0 (generate-first-k-in-range mh privkey)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))

(defthm mv-nth-0-of-generate-first-k-in-range-bound
  (< (mv-nth 0 (generate-first-k-in-range mh prikey))
     *q*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))

(defthm true-listp-of-mv-nth-1-of-generate-first-k-in-range
  (true-listp (mv-nth 1 (generate-first-k-in-range mh privkey)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-generate-first-k-in-range
  (acl2::all-unsigned-byte-p
   8 (mv-nth 1 (generate-first-k-in-range mh privkey)))
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))

(defthm len-of-mv-nth-1-of-generate-first-k-in-range
  (equal (len (mv-nth 1 (generate-first-k-in-range mh privkey)))
         32)
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))

(defthm true-listp-of-mv-nth-2-of-generate-first-k-in-range
  (true-listp (mv-nth 2 (generate-first-k-in-range mh privkey)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-generate-first-k-in-range
  (acl2::all-unsigned-byte-p
   8 (mv-nth 2 (generate-first-k-in-range mh privkey)))
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))

(defthm len-of-mv-nth-2-of-generate-first-k-in-range
  (equal (len (mv-nth 2 (generate-first-k-in-range mh privkey)))
         32)
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))

(defthm natp-of-mv-nth-3-of-generate-first-k-in-range
  (natp (mv-nth 3 (generate-first-k-in-range mh privkey)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable generate-first-k-in-range))))


;; --------------------------------
;; Back to Section 2.4, signing a message.

;; The main interface is
;;   ecdsa-sign-deterministic-prehashed (mh privkey)
;; where
;;   mh is the hashed input message as a list of bits
;;   privkey is the private key as a natural number

;; As explained earlier in this file,
;; our specification of ECDSA signatures
;; also returns public key recovery information,
;; which consists of the Rx index and the Ry parity.
;; If one were to always generate signatures with Rx = r
;; (or, equivalently, with Rx < q),
;; then the Rx index would always be 0 and could be avoided,
;; reducing the public key recovery information to just the parity of Ry.
;; Note that, for secp256k1, the condition that Rx is in [q .. p-1]
;; is very unlikely to happen -- about 1/(2^128) chance.

;; To support this reduced information (i.e. just the parity Ry)
;; along with the full information (i.e. the index of Rx and the parity of Ry),
;; we parameterize the functions below over a flag small-x?
;; that says whether Rx should be "small", i.e. below q, i.e. equal to r.
;; If the small-x? flag is T, we keep generating ephemeral keys k
;; until the resulting signature has x-index = 0.
;; If the small-x? flag is NIL, we stop as soon as
;; an otherwise valid signature has been generated.

;; In case the signature is unacceptable, keeps trying with this function.
;;
;; Returns (mv error? x-index y-even? r s)

(defund ecdsa-sign-deterministic-next
  (mh privkey small-x? prev-K prev-V prev-max-iters)
  (declare (xargs :guard (and (true-listp mh)
                              (acl2::all-unsigned-byte-p 1 mh)
                              (posp privkey)
                              (< privkey *q*)
                              (booleanp small-x?)
                              (true-listp prev-K)
                              (acl2::unsigned-byte-listp 8 prev-K)
                              (= (len prev-K) 32)
                              (true-listp prev-V)
                              (acl2::unsigned-byte-listp 8 prev-V)
                              (= (len prev-V) 32)
                              (natp prev-max-iters))
                  :measure (nfix prev-max-iters)))
  (if (zp prev-max-iters)
      (mv t 0 nil 0 0) ; error
    (mv-let (small-k large-K V max-iters)
      (generate-next-k-in-range prev-k prev-V prev-max-iters)
      (if (= small-k 0) ; this means that no k could be found
          (mv t 0 nil 0 0) ; error
        (mv-let (error? x-index y-even? r s)
          (ecdsa-sign-given-k mh privkey small-k)
          (if (or error?
                  (and small-x?
                       (not (= x-index 0))))
              (if (zp max-iters)
                  (mv t 0 nil 0 0) ; error
                (ecdsa-sign-deterministic-next
                 mh privkey small-x? large-K V (- max-iters 1)))
            (mv nil x-index y-even? r s)))))))

(defthm booleanp-of-mv-nth-0-of-ecdsa-sign-deterministic-next
  (booleanp (mv-nth 0 (ecdsa-sign-deterministic-next
                       mh privkey small-x? prev-K prev-V prev-max-iters)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-next))))

(defthm natp-of-mv-nth-1-of-ecdsa-sign-deterministic-next
  (natp (mv-nth 1 (ecdsa-sign-deterministic-next
                   mh privkey small-x? prev-K prev-V prev-max-iters)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-next))))

(defthm booleanp-of-mv-nth-2-of-ecdsa-sign-deterministic-next
  (booleanp (mv-nth 2 (ecdsa-sign-deterministic-next
                       mh privkey small-x? prev-K prev-V prev-max-iters)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-next))))

(defthm posp-of-mv-nth-3-of-ecdsa-sign-deterministic-next
  (implies (not (mv-nth 0 (ecdsa-sign-deterministic-next
                           mh privkey small-x? prev-K prev-V prev-max-iters)))
           (posp (mv-nth 3 (ecdsa-sign-deterministic-next
                            mh privkey small-x? prev-K prev-V prev-max-iters))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-next))))

(defthm <-*q*-of-mv-nth-3-of-ecdsa-sign-deterministic-next
  (< (mv-nth 3 (ecdsa-sign-deterministic-next
                mh privkey small-x? prev-K prev-V prev-max-iters))
     *q*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-next))))

(defthm posp-of-mv-nth-4-of-ecdsa-sign-deterministic-next
  (implies (and (not (mv-nth 0 (ecdsa-sign-deterministic-next
                                mh privkey small-x?
                                prev-K prev-V prev-max-iters)))
                (posp privkey))
           (posp (mv-nth 4 (ecdsa-sign-deterministic-next
                            mh privkey small-x? prev-K prev-V prev-max-iters))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-next))))

(defthm <-*q*-of-mv-nth-4-of-ecdsa-sign-deterministic-next
  (implies (posp privkey)
           (< (mv-nth 4 (ecdsa-sign-deterministic-next
                         mh privkey small-x? prev-K prev-V prev-max-iters))
              *q*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-next))))

;; This produces the signature, without constraints on s.
;;
;; Returns (mv error? x-index y-even? r s)

(defund ecdsa-sign-deterministic-prehashed-aux (mh privkey small-x?)
  (declare (xargs :guard (and (true-listp mh)
                              (acl2::all-unsigned-byte-p 1 mh)
                              (posp privkey)
                              (< privkey *q*)
                              (booleanp small-x?))))
  (mv-let (small-k large-K V max-iters)
    (generate-first-k-in-range mh privkey)
    (if (= small-k 0) ; this means that no k could be found
        (mv t 0 nil 0 0) ; error
      (mv-let (error? x-index y-even? r s)
        (ecdsa-sign-given-k mh privkey small-k)
        (if (or error?
                (and small-x?
                     (not (= x-index 0))))
            (if (zp max-iters)
                (mv t 0 nil 0 0) ; error
              (ecdsa-sign-deterministic-next
               mh privkey small-x? large-K V (- max-iters 1)))
          (mv nil x-index y-even? r s))))))

(defthm booleanp-of-mv-nth-0-of-ecdsa-sign-deterministic-prehashed-aux
  (booleanp (mv-nth 0 (ecdsa-sign-deterministic-prehashed-aux
                       mh privkey small-x?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed-aux))))

(defthm natp-of-mv-nth-1-of-ecdsa-sign-deterministic-prehashed-aux
  (natp (mv-nth 1 (ecdsa-sign-deterministic-prehashed-aux
                   mh privkey small-x?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed-aux))))

(defthm booleanp-of-mv-nth-2-of-ecdsa-sign-deterministic-prehashed-aux
  (booleanp (mv-nth 2 (ecdsa-sign-deterministic-prehashed-aux
                       mh privkey small-x?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed-aux))))

(defthm posp-of-mv-nth-3-of-ecdsa-sign-deterministic-prehashed-aux
  (implies (not (mv-nth 0 (ecdsa-sign-deterministic-prehashed-aux
                           mh privkey small-x?)))
           (posp (mv-nth 3 (ecdsa-sign-deterministic-prehashed-aux
                            mh privkey small-x?))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed-aux))))

(defthm <-*q*-of-mv-nth-3-of-ecdsa-sign-deterministic-prehashed-aux
  (< (mv-nth 3 (ecdsa-sign-deterministic-prehashed-aux mh privkey small-x?))
     *q*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed-aux))))

(defthm posp-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed-aux
  (implies (and (not (mv-nth 0 (ecdsa-sign-deterministic-prehashed-aux
                                mh privkey small-x?)))
                (posp privkey))
           (posp (mv-nth 4 (ecdsa-sign-deterministic-prehashed-aux
                            mh privkey small-x?))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed-aux))))

(defthm <-*q*-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed-aux
  (implies (posp privkey)
           (< (mv-nth 4 (ecdsa-sign-deterministic-prehashed-aux
                         mh privkey small-x?))
              *q*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed-aux))))

;; This is our main API function.
;; The small-s? flag determines whether the s component of the signature
;; should be kept below q/2; see the discussion about ecdsa-ensure-s-below-q/2,
;; earlier in this file.
;;
;; Returns (mv error? x-index y-even? r s)

(defsection ecdsa-sign-deterministic-prehashed
  :parents (deterministic-ecdsa-secp256k1)
  :short "Sign a prehashed message using <see topic=\"SHA2____SHA-2\">SHA-256</see>."
  :long
  (xdoc::topstring
   (xdoc::p "The call")
   (xdoc::blockquote (xdoc::@call "ecdsa-sign-deterministic-prehashed"))
   (xdoc::p "signs the already-hashed message @('mh')
             using <see topic=\"SHA2____SHA-2\">SHA-256</see> when
             applying <see topic=\"HMAC____HMAC\">HMAC</see>.")
   (xdoc::p "Arguments:")
   (xdoc::ol
    (xdoc::li
     "@('mh') -- the already-hashed message to be signed, a list of bits.")
    (xdoc::li
     "@('privkey') -- the signer's private key, which is a positive integer
      less than the elliptic curve order.")
    (xdoc::li
     "@('small-x?') -- a boolean flag that, when true, restricts the
      ephemeral public key x coordinate
      to be to be less than the elliptic curve order.")
    (xdoc::li
     "@('small-s?') -- a boolean flag that, when true, restricts the returned
      @('s') value to be less than @($q/2$), where @($q$) is the elliptic
      curve order."))
    (xdoc::p
     "Return values (using <see topic=\"ACL2____MV\">mv</see>):")
    (xdoc::ol
     (xdoc::li
      "@('error?') -- a flag indicating any sort of error was detected.
       Please report errors, but do not send a private key that is in use.")
     (xdoc::li
      "@('x-index') -- an index from 0 to the curve cofactor @('h'),
       which can be used to recover the x coordinate of the ephemeral public
       key from @('r').  If the argument @('small-x?') is true, @('x-index') will be 0.")
     (xdoc::li
      "@('y-even?') -- a flag indicating whether the y coordinate of the
       ephemeral public key was even or odd.  This, along with @('r') and
       @('x-index'), can be used to recover the y coordinate of the ephemeral
       public key.")
     (xdoc::li
      "@('r') -- the x coordinate of the ephemeral public key, modulo the
       elliptic curve group order, considered the first part of the signature.")
     (xdoc::li
      "@('s') -- the second part of the signature.")))
  (defund ecdsa-sign-deterministic-prehashed (mh privkey small-x? small-s?)
    (declare (xargs :guard (and (true-listp mh)
                                (acl2::all-unsigned-byte-p 1 mh)
                                (posp privkey)
                                (< privkey *q*)
                                (booleanp small-x?))))
    (b* (((mv error? x-index y-even? r s)
          (ecdsa-sign-deterministic-prehashed-aux mh privkey small-x?))
         ((when error?) (mv error? 0 nil 0 0)))
      (if small-s?
          (b* (((mv x-index y-even? r s)
                (ecdsa-ensure-s-below-q/2 x-index y-even? r s)))
            (mv nil x-index y-even? r s))
        (mv nil x-index y-even? r s))))
)

(defthm booleanp-of-mv-nth-0-of-ecdsa-sign-deterministic-prehashed
  (booleanp (mv-nth 0 (ecdsa-sign-deterministic-prehashed
                       mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed))))

(defthm natp-of-mv-nth-1-of-ecdsa-sign-deterministic-prehashed
  (natp (mv-nth 1 (ecdsa-sign-deterministic-prehashed
                   mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed))))

(defthm booleanp-of-mv-nth-2-of-ecdsa-sign-deterministic-prehashed
  (booleanp (mv-nth 2 (ecdsa-sign-deterministic-prehashed
                       mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed))))

(defthm posp-of-mv-nth-3-of-ecdsa-sign-deterministic-prehashed
  (implies (not (mv-nth 0 (ecdsa-sign-deterministic-prehashed
                           mh privkey small-x? small-s?)))
           (posp (mv-nth 3 (ecdsa-sign-deterministic-prehashed
                            mh privkey small-x? small-s?))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed))))

(defthm <-*q*-of-mv-nth-3-of-ecdsa-sign-deterministic-prehashed
  (< (mv-nth 3 (ecdsa-sign-deterministic-prehashed
                mh privkey small-x? small-s?))
     *q*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed))))

(defthm posp-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed
  (implies (and (not (mv-nth 0 (ecdsa-sign-deterministic-prehashed
                                mh privkey small-x? small-s?)))
                (posp privkey))
           (posp (mv-nth 4 (ecdsa-sign-deterministic-prehashed
                            mh privkey small-x? small-s?))))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :use ((:instance posp-of-mv-nth-3-of-ecdsa-ensure-s-below-q/2
           (r (mv-nth 3 (ecdsa-sign-deterministic-prehashed-aux
                         mh privkey small-x?)))
           (s (mv-nth 4 (ecdsa-sign-deterministic-prehashed-aux
                         mh privkey small-x?))))
          posp-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed-aux
          <-*q*-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed-aux)
    :in-theory
    (e/d (ecdsa-sign-deterministic-prehashed)
         (posp-of-mv-nth-3-of-ecdsa-ensure-s-below-q/2
          posp-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed-aux
          <-*q*-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed-aux)))))

(defthm <-*q*-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed
  (implies (posp privkey)
           (< (mv-nth 4 (ecdsa-sign-deterministic-prehashed
                         mh privkey small-x? small-s?))
              *q*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-prehashed))))

;; This is the most standard instantiation of RFC 6979,
;; using SHA-256 for both the message hash and the HMAC.
;;
;; Returns (mv error? x-index y-even? r s)

(defsection ecdsa-sign-deterministic-sha-256
  :parents (deterministic-ecdsa-secp256k1)
  :short "Sign a message using <see topic=\"SHA2____SHA-2\">SHA-256</see>."
  :long
  (xdoc::topstring
   (xdoc::p "The call")
   (xdoc::blockquote (xdoc::@call "ecdsa-sign-deterministic-sha-256"))
   (xdoc::p "signs the message @('m')
             using <see topic=\"SHA2____SHA-2\">SHA-256</see> both for hashing
             the input message and when
             applying <see topic=\"HMAC____HMAC\">HMAC</see>.")
   (xdoc::p "Arguments:")
   (xdoc::ol
    (xdoc::li
     "@('m') -- the message to be signed, a list of bits.  Note,
      to convert a list of bytes to a list of bits prior to calling this,
      each byte should be converted to a big-endian list of bits
      which are then appended.  (This is different from when KECCAK-256 is
      used to hash the message).")
    (xdoc::li
     "@('privkey') -- the signer's private key, which is a positive integer
      less than the elliptic curve order.")
    (xdoc::li
     "@('small-x?') -- a boolean flag that, when true, restricts the
      ephemeral public key x coordinate
      to be to be less than the elliptic curve order.")
    (xdoc::li
     "@('small-s?') -- a boolean flag that, when true, restricts the returned
      @('s') value to be less than @($q/2$), where @($q$) is the elliptic
      curve order."))
    (xdoc::p
     "Return values (using <see topic=\"ACL2____MV\">mv</see>):")
    (xdoc::ol
     (xdoc::li
      "@('error?') -- a flag indicating any sort of error was detected.
       Please report errors, but do not send a private key that is in use.")
     (xdoc::li
      "@('x-index') -- an index from 0 to the curve cofactor @('h'),
       which can be used to recover the x coordinate of the ephemeral public
       key from @('r').  If the argument @('small-x?') is true, @('x-index') will be 0.")
     (xdoc::li
      "@('y-even?') -- a flag indicating whether the y coordinate of the
       ephemeral public key was even or odd.  This, along with @('r') and
       @('x-index'), can be used to recover the y coordinate of the ephemeral
       public key.")
     (xdoc::li
      "@('r') -- the x coordinate of the ephemeral public key, modulo the
       elliptic curve group order, considered the first part of the signature.")
     (xdoc::li
      "@('s') -- the second part of the signature.")))
  (defund ecdsa-sign-deterministic-sha-256 (m privkey small-x? small-s?)
    (declare (xargs :guard (and (true-listp m)
                                (acl2::all-unsigned-byte-p 1 m)
                                (< (len m) (expt 2 64))
                                (posp privkey)
                                (< privkey *q*)
                                (booleanp small-x?))))
    (ecdsa-sign-deterministic-prehashed
     (bytes-to-bits (sha2::sha-256 m))
     privkey
     small-x?
     small-s?))
)

(defthm booleanp-of-mv-nth-0-of-ecdsa-sign-deterministic-sha-256
  (booleanp (mv-nth 0 (ecdsa-sign-deterministic-sha-256
                       mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-sha-256))))

(defthm natp-of-mv-nth-1-of-ecdsa-sign-deterministic-sha-256
  (natp (mv-nth 1 (ecdsa-sign-deterministic-sha-256
                   mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-sha-256))))

(defthm booleanp-of-mv-nth-2-of-ecdsa-sign-deterministic-sha-256
  (booleanp (mv-nth 2 (ecdsa-sign-deterministic-sha-256
                       mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-sha-256))))

(defthm posp-of-mv-nth-3-of-ecdsa-sign-deterministic-sha-256
  (implies (not (mv-nth 0 (ecdsa-sign-deterministic-sha-256
                           mh privkey small-x? small-s?)))
           (posp (mv-nth 3 (ecdsa-sign-deterministic-sha-256
                            mh privkey small-x? small-s?))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-sha-256))))

(defthm <-*q*-of-mv-nth-3-of-ecdsa-sign-deterministic-sha-256
  (< (mv-nth 3 (ecdsa-sign-deterministic-sha-256
                mh privkey small-x? small-s?))
     *q*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-sha-256))))

(defthm posp-of-mv-nth-4-of-ecdsa-sign-deterministic-sha-256
  (implies (and (not (mv-nth 0 (ecdsa-sign-deterministic-sha-256
                                mh privkey small-x? small-s?)))
                (posp privkey))
           (posp (mv-nth 4 (ecdsa-sign-deterministic-sha-256
                            mh privkey small-x? small-s?))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-sha-256))))

(defthm <-*q*-of-mv-nth-4-of-ecdsa-sign-deterministic-sha-256
  (implies (posp privkey)
           (< (mv-nth 4 (ecdsa-sign-deterministic-sha-256
                         mh privkey small-x? small-s?))
              *q*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-sha-256))))

;; Keccak-256 is used to hash the message m,
;; but internally SHA-256 is used for the HMAC.
;;
;; Returns (mv error? x-index y-even? r s)

(defsection ecdsa-sign-deterministic-keccak-256
  :parents (deterministic-ecdsa-secp256k1)
  :short "Sign a message using <see topic=\"KECCAK____KECCAK\">KECCAK-256</see>/<see topic=\"SHA2____SHA-2\">SHA-256</see>."
  :long
  (xdoc::topstring
   (xdoc::p "The call")
   (xdoc::blockquote (xdoc::@call "ecdsa-sign-deterministic-keccak-256"))
   (xdoc::p "signs the message @('m')
             using <see topic=\"KECCAK____KECCAK\">KECCAK-256</see> for hashing the input message,
             but using <see topic=\"SHA2____SHA-2\">SHA-256</see> when
             applying <see topic=\"HMAC____HMAC\">HMAC</see>.")
   (xdoc::p "Arguments:")
   (xdoc::ol
    (xdoc::li
     "@('m') -- the message to be signed, a list of bits.  Note,
      to convert a list of bytes to a list of bits prior to calling this,
      each byte should be converted to a little-endian list of bits
      which are then appended.  (This is different from when SHA-256 is
      used to hash the message).")
    (xdoc::li
     "@('privkey') -- the signer's private key, which is a positive integer
      less than the elliptic curve order.")
    (xdoc::li
     "@('small-x?') -- a boolean flag that, when true, restricts the
      ephemeral public key x coordinate
      to be to be less than the elliptic curve order.")
    (xdoc::li
     "@('small-s?') -- a boolean flag that, when true, restricts the returned
      @('s') value to be less than @($q/2$), where @($q$) is the elliptic
      curve order."))
    (xdoc::p
     "Return values (using <see topic=\"ACL2____MV\">mv</see>):")
    (xdoc::ol
     (xdoc::li
      "@('error?') -- a flag indicating any sort of error was detected.
       Please report errors, but do not send a private key that is in use.")
     (xdoc::li
      "@('x-index') -- an index from 0 to the curve cofactor @('h'),
       which can be used to recover the x coordinate of the ephemeral public
       key from @('r').  If the argument @('small-x?') is true, @('x-index') will be 0.")
     (xdoc::li
      "@('y-even?') -- a flag indicating whether the y coordinate of the
       ephemeral public key was even or odd.  This, along with @('r') and
       @('x-index'), can be used to recover the y coordinate of the ephemeral
       public key.")
     (xdoc::li
      "@('r') -- the x coordinate of the ephemeral public key, modulo the
       elliptic curve group order, considered the first part of the signature.")
     (xdoc::li
      "@('s') -- the second part of the signature.")))
  (defund ecdsa-sign-deterministic-keccak-256 (m privkey small-x? small-s?)
    (declare (xargs :guard (and (true-listp m)
                                (acl2::all-unsigned-byte-p 1 m)
                                (posp privkey)
                                (< privkey *q*)
                                (booleanp small-x?))))
    (ecdsa-sign-deterministic-prehashed
     (keccak::keccak-256 m)
     privkey
     small-x?
     small-s?))
)

(defthm booleanp-of-mv-nth-0-of-ecdsa-sign-deterministic-keccak-256
  (booleanp (mv-nth 0 (ecdsa-sign-deterministic-keccak-256
                       mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-keccak-256))))

(defthm natp-of-mv-nth-1-of-ecdsa-sign-deterministic-keccak-256
  (natp (mv-nth 1 (ecdsa-sign-deterministic-keccak-256
                   mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-keccak-256))))

(defthm booleanp-of-mv-nth-2-of-ecdsa-sign-deterministic-keccak-256
  (booleanp (mv-nth 2 (ecdsa-sign-deterministic-keccak-256
                       mh privkey small-x? small-s?)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-keccak-256))))

(defthm posp-of-mv-nth-3-of-ecdsa-sign-deterministic-keccak-256
  (implies (not (mv-nth 0 (ecdsa-sign-deterministic-keccak-256
                           mh privkey small-x? small-s?)))
           (posp (mv-nth 3 (ecdsa-sign-deterministic-keccak-256
                            mh privkey small-x? small-s?))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-keccak-256))))

(defthm <-*q*-of-mv-nth-3-of-ecdsa-sign-deterministic-keccak-256
  (< (mv-nth 3 (ecdsa-sign-deterministic-keccak-256
                mh privkey small-x? small-s?))
     *q*)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-keccak-256))))

(defthm posp-of-mv-nth-4-of-ecdsa-sign-deterministic-keccak-256
  (implies (and (not (mv-nth 0 (ecdsa-sign-deterministic-keccak-256
                                mh privkey small-x? small-s?)))
                (posp privkey))
           (posp (mv-nth 4 (ecdsa-sign-deterministic-keccak-256
                            mh privkey small-x? small-s?))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-keccak-256))))

(defthm <-*q*-of-mv-nth-4-of-ecdsa-sign-deterministic-keccak-256
  (implies (posp privkey)
           (< (mv-nth 4 (ecdsa-sign-deterministic-keccak-256
                         mh privkey small-x? small-s?))
              *q*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ecdsa-sign-deterministic-keccak-256))))
