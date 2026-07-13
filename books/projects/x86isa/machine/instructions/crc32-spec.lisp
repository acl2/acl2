; X86ISA Library
;
; Copyright (C) 2026 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "structures" :dir :utils)

(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))

;; These two rules from the Kestrel book just above
;; rewrite comparisons of INTEGER-LENGTH into
;; comparisons with powers of 2,
;; which interferes with the direct reasoning about INTEGER-LENGTH in this file:
(local (in-theory (disable acl2::<-of-integer-length-arg1
                           acl2::<-of-integer-length-arg2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions
;; (candidate for eventual integration into a library
;; such as [books]/centaur/bitops/).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; XORing two integers of the same length cancels their leading bits.
(defrulel integer-length-of-logxor-same-length
  (implies (and (posp x)
                (natp y)
                (equal (integer-length y) (integer-length x)))
           (< (integer-length (logxor x y))
              (integer-length x)))
  :rule-classes :linear
  :enable (bitops::ihsext-inductions
           bitops::ihsext-recursive-redefs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; XORing two integers of different lengths preserves the longer length.
(defrulel integer-length-of-logxor-different-lengths
  (implies (and (natp x)
                (natp y)
                (not (equal (integer-length x) (integer-length y))))
           (equal (integer-length (logxor x y))
                  (max (integer-length x) (integer-length y))))
  :enable (bitops::ihsext-inductions
           bitops::ihsext-recursive-redefs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Shifting distributes over XOR.
(defrulel ash-of-logxor
  (equal (ash (logxor x y) n)
         (logxor (ash x n) (ash y n)))
  :hints ((bitops::logbitp-reasoning)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Concatenation is a XOR when the low part fits.
(defrulel logapp-as-logxor
  (implies (unsigned-byte-p n b)
           (equal (logapp n b a)
                  (logxor b (ash a n))))
  :enable (bitops::ihsext-inductions
           bitops::ihsext-recursive-redefs
           bitops::ihsext-bounds-thms)
  :disable (unsigned-byte-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ crc-spec
  :parents (instruction-semantic-functions)
  :short "Specification of CRC (cyclic redundancy check) calculations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A CRC treats bit strings as polynomials over the finite field GF(2),
     i.e. with coefficients 0 and 1 added and multiplied modulo 2:
     bit @($i$) of a value is the coefficient of @($x^i$).
     The CRC of a message (i.e. bit string, as a polynomial) @($M(x)$)
     with respect to a generator polynomial @($P(x)$) of degree @($W$)
     is the remainder of @($M(x) \\cdot x^W$) divided by @($P(x)$).
     See "
    (xdoc::ahref
     "https://doi.org/10.1109/JRPROC.1961.287814"
     "``Cyclic Codes for Error Detection'' by Peterson and Brown")
    ".")
   (xdoc::p
    "The function @(tsee crc) below is a general CRC update function,
     parameterized by the generator polynomial;
     it subsumes the calculation of the CRC of a whole message
     as well as the incremental update of a CRC with new data.
     The function @(tsee crc32) is the update calculated by
     the CRC32 instruction
     (Intel manual, June 2026, Vol. 2A, CRC32&mdash;Accumulate CRC32 Value),
     which instantiates @(tsee crc) with
     the CRC-32C (Castagnoli) polynomial @('11EDC6F41H')
     and processes data in bit-reflected form."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bit-reflect ((n natp) (x natp))
  :returns (reflected natp)
  :short "Reverse the low @('n') bits of @('x')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Bit @('i') of the @('n')-bit result is bit @('n-1-i') of @('x'):
     the least significant bit of the result is bit @('n-1') of @('x'),
     and the higher bits of the result are, recursively,
     the reflection of the low @('n-1') bits of @('x').
     This is the operation that the Intel manual calls @('BIT_REFLECT')
     (e.g. in the operation section of CRC32, Vol. 2A)."))
  (cond ((zp n) 0)
        (t (logcons (logbit (1- n) x)
                    (bit-reflect (1- n) x))))
  :type-prescription (natp (bit-reflect n x))

  ///

  (defret unsigned-byte-p-of-bit-reflect
    (implies (natp n)
             (unsigned-byte-p n reflected))
    :hints (("Goal"
             :induct t
             :in-theory (enable* bitops::ihsext-bounds-thms))))

  (defret logbitp-of-bit-reflect
    (implies (natp n)
             (equal (logbitp i reflected)
                    (and (< (nfix i) n)
                         (logbitp (- n (1+ (nfix i))) x))))
    :hints (("Goal" :induct (acl2::dec-dec-induct n i))))

  (defrule bit-reflect-of-bit-reflect
    (implies (natp n)
             (equal (bit-reflect n (bit-reflect n x))
                    (loghead n x)))
    :hints ((bitops::logbitp-reasoning))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define gf2-mod ((x natp) (y posp))
  :returns (r natp)
  :short "Remainder of the division of @('x') by @('y'),
          as polynomials over GF(2)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is polynomial long division:
     while the dividend has degree at least that of the divisor,
     subtract (i.e. XOR) the divisor,
     shifted left to align its leading coefficient with the dividend's;
     the dividend's degree strictly decreases at each step.
     This is the operation that the Intel manual calls @('MOD2')
     (e.g. in the operation section of CRC32, Vol. 2A)."))
  (b* (((unless (mbt (and (natp x) (posp y)))) 0)
       (deg-x (1- (integer-length x)))
       (deg-y (1- (integer-length y)))
       ((when (< deg-x deg-y)) x))
    (gf2-mod (logxor x (ash y (- deg-x deg-y))) y))
  :type-prescription (natp (gf2-mod x y))

  ///

  (defret unsigned-byte-p-of-gf2-mod
    (implies (and (natp x) (posp y))
             (unsigned-byte-p (1- (integer-length y))
                              r))
    :hints
    (("Goal"
      :induct t
      :in-theory (enable acl2::unsigned-byte-p-of-integer-length-gen))))

  ;; Induction scheme for the next theorem:
  ;; recurse like GF2-MOD on X while X is longer than (ASH Y K),
  ;; and case-split on the comparison when it is not.
  (local (defun gf2-mod-of-logxor-of-ash-induct (x y k)
           (b* (((unless (and (natp x) (posp y) (natp k))) 0)
                (deg-x (1- (integer-length x)))
                (deg-y (1- (integer-length y)))
                ((when (< deg-x (+ deg-y k))) 0)
                ((when (equal deg-x (+ deg-y k))) 0))
             (gf2-mod-of-logxor-of-ash-induct
              (logxor x (ash y (- deg-x deg-y))) y k))))

  ;; XORing into the dividend a shifted copy of the modulus
  ;; does not change the remainder.
  (defrule gf2-mod-of-logxor-of-ash-of-modulus
    (implies (and (natp x) (posp y) (natp k))
             (equal (gf2-mod (logxor x (ash y k)) y)
                    (gf2-mod x y)))
    :induct (gf2-mod-of-logxor-of-ash-induct x y k)
    :expand ((gf2-mod (logxor x (ash y k)) y)
             (gf2-mod x y)))

  ;; Variant of the previous theorem
  ;; that matches the shifted modulus inside a nested XOR.
  (defrulel gf2-mod-of-logxor-of-logxor-of-ash-of-modulus
    (implies (and (natp z) (natp w) (posp y) (natp k))
             (equal (gf2-mod (logxor z (logxor w (ash y k))) y)
                    (gf2-mod (logxor z w) y)))
    :use ((:instance gf2-mod-of-logxor-of-ash-of-modulus
                     (x (logxor z w)))))

  ;; A summand of the dividend may be reduced modulo the modulus
  ;; before being shifted and XORed.
  (defrule gf2-mod-of-logxor-of-ash-of-gf2-mod
    (implies (and (natp x) (natp z) (posp y) (natp k))
             (equal (gf2-mod (logxor z (ash (gf2-mod x y) k)) y)
                    (gf2-mod (logxor z (ash x k)) y)))
    ;; :induct t would induct on the structure of Z instead:
    :induct (gf2-mod x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crc ((poly posp) (crc natp) (data natp) (data-width natp))
  :returns (new-crc natp)
  :short "General CRC update:
          absorb @('data-width') bits of new data into the CRC @('crc'),
          with respect to the generator polynomial @('poly')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Viewing all the values as polynomials over GF(2)
     (see @(tsee crc-spec)), this calculates")
   (xdoc::@[]
    "(\\mathit{data} \\cdot x^W \\oplus
      \\mathit{crc} \\cdot x^{\\mathit{datawidth}})
     \\mod \\mathit{poly}")
   (xdoc::p
    "where @($W$) is the degree of @($\\mathit{poly}$)
     and @($\\oplus$) is addition of polynomials over GF(2), i.e. XOR.")
   (xdoc::p
    "This subsumes the CRC of a whole message,
     obtained by passing the whole message as @('data')
     (most significant bit first, i.e. @('data-width') may exceed @($W$))
     and 0 as @('crc'):
     the result is @($M(x) \\cdot x^W \\bmod P(x)$),
     the textbook CRC definition.
     Absorbing a message piecewise, via repeated calls of this function,
     yields the same result as absorbing it in one call:
     this is the theorem @('crc-of-crc').")
   (xdoc::p
    "Common CRC conventions
     (initial CRC values such as @('FFFFFFFFh'),
     final XOR masks,
     and bit reflection as in @(tsee crc32))
     are layered on top of this function.")
   (xdoc::p
    "The @('crc-of-crc') theorem provides a justification for this definition:
     it says that Absorbing two pieces of data in succession
     is the same as absorbing their concatenation;
     that is, it realizes an incremental calculation.")
   (xdoc::p
    "In the theorem, @('(logapp width2 data2 data1)') is
     the concatenation of @('data1') followed by the @('width2')-bit @('data2'):
     since @('data1') is absorbed first,
     it occupies the more significant positions.")
   (xdoc::p
    "By induction, absorbing a message in pieces of arbitrary widths,
     starting with CRC 0,
     yields the CRC of the whole message,
     i.e. the textbook CRC definition mentioned in @(see crc-spec):
     this justifies viewing this function,
     which the CRC32 instruction applies to
     8, 16, 32, or 64 bits of data at a time (see @(tsee crc32)),
     as an incremental calculation of whole-message CRCs.")
   (xdoc::p
    "The proof rests on the @(tsee gf2-mod) congruence theorem
     @('gf2-mod-of-logxor-of-ash-of-gf2-mod'),
     which lets the inner remainder be dropped,
     after which both sides reduce to
     the remainder of the same polynomial."))
  (gf2-mod (logxor (ash data (1- (integer-length poly)))
                   (ash crc data-width))
           poly)
  :type-prescription (natp (crc poly crc data data-width))

  ///

  (defret unsigned-byte-p-of-crc
    (implies (and (posp poly)
                  (natp crc)
                  (natp data))
             (unsigned-byte-p (1- (integer-length poly))
                              new-crc)))

  (defrule crc-of-crc
    (implies (and (posp poly)
                  (natp crc)
                  (natp data1)
                  (natp width1)
                  (unsigned-byte-p width2 data2))
             (equal (crc poly (crc poly crc data1 width1) data2 width2)
                    (crc poly crc (logapp width2 data2 data1)
                         (+ width1 width2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *crc32-polynomial*
  :short "Generator polynomial for CRC32."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the CRC-32C (Castagnoli) polynomial")
   (xdoc::codeblock
    "x^32 + x^28 + x^27 + x^26 + x^25 + x^23 + x^22 + x^20 + x^19 +"
    "x^18 + x^14 + x^13 + x^11 + x^10 + x^9 + x^8 + x^6 + 1")
   (xdoc::p
    "called 11EDC6F41H in the Intel manual (Vol. 2A, CRC32)."))
  #x11EDC6F41

  ///

  ;; The CRC-32C polynomial has degree 32.
  (assert-event (equal (integer-length *crc32-polynomial*) 33))

  ;; Reflecting the low 32 bits of the CRC-32C polynomial yields
  ;; the well-known 'reversed' form of the polynomial
  ;; used by software implementations of CRC-32C.
  (assert-event (equal (bit-reflect 32 #x1EDC6F41) #x82F63B78)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define crc32 ((crc (unsigned-byte-p 32 crc))
               (data natp)
               (data-width natp))
  :returns (new-crc (unsigned-byte-p 32 new-crc))
  :short "The CRC update calculated by the CRC32 instruction:
          absorb the @('data-width')-bit value @('data')
          into the 32-bit CRC @('crc')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The CRC32 instruction uses
     the CRC-32C polynomial @('11EDC6F41H') (see @(tsee *crc32-polynomial*))
     and processes both the data and the CRC in bit-reflected form.
     For example, for an 8-bit @('data'), the operation section of CRC32
     (Intel manual, June 2026, Vol. 2A) prescribes:")
   (xdoc::codeblock
    "TEMP1[7:0] := BIT_REFLECT8(SRC[7:0])"
    "TEMP2[31:0] := BIT_REFLECT32(DEST[31:0])"
    "TEMP3[39:0] := TEMP1[7:0] << 32"
    "TEMP4[39:0] := TEMP2[31:0] << 8"
    "TEMP5[39:0] := TEMP3[39:0] XOR TEMP4[39:0]"
    "TEMP6[31:0] := TEMP5[39:0] MOD2 11EDC6F41H"
    "DEST[31:0] := BIT_REFLECT(TEMP6[31:0])")
   (xdoc::p
    "Here @('SRC') is @('data'), @('DEST') is @('crc'),
     @('BIT_REFLECT') is @(tsee bit-reflect),
     and the shifting, XORing, and @('MOD2') of
     @('TEMP3'), @('TEMP4'), @('TEMP5'), and @('TEMP6')
     are @(tsee crc) (whose @(tsee gf2-mod) is @('MOD2')).
     The cases of 16-bit, 32-bit, and 64-bit @('data') are analogous,
     with 8 replaced by the data width.")
   (xdoc::p
    "Note that the initial value and final XOR mask used by
     common CRC-32C protocols (e.g. @('FFFFFFFFh') in iSCSI)
     are not part of the instruction:
     software applies them around the instruction."))
  (bit-reflect 32
               (crc *crc32-polynomial*
                    (bit-reflect 32 crc)
                    (bit-reflect data-width data)
                    data-width))

  ///

  ;; This variant of the return type theorem is useful
  ;; when the result is stored in a wider (e.g. 64-bit) location:
  (defret unsigned-byte-p-of-crc32
    (implies (and (integerp n) (<= 32 n))
             (unsigned-byte-p n new-crc))
    :hints (("Goal"
             :use return-type-of-crc32
             :in-theory (disable crc32
                                 return-type-of-crc32
                                 unsigned-byte-p)))))
