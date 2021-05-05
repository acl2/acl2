; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "blake2-hash")
(include-book "constants")
(include-book "jubjub")
(include-book "randomness-beacon")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two somewhat specific theorems, but more general than Pedersen hash.

(defrulel len-of-nthcdr-multiple-of-3
  (implies (and (integerp (* 1/3 (len x)))
                (consp x))
           (integerp (* 1/3 (len (nthcdr 3 x)))))
  :prep-books ((include-book "std/lists/nthcdr" :dir :system)))

(defrulel bit-listp-of-take-3
  (implies (and (bit-listp segment)
                (integerp (/ (len segment) 3))
                (consp segment))
           (bit-listp (take 3 segment)))
  :prep-books ((include-book "arithmetic-3/top" :dir :system)
               (include-book "std/lists/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pedersen-hash
  :parents (zcash)
  :short "A formalization of Zcash's Pedersen hash."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described in [ZPS:5.4.1.7],
     which refers to several other parts of [ZPS].
     We may split this file and XDOC topic into multiple ones
     that correspond to different parts of [ZPS],
     but for now we put here everything needed to define Pedersen hash."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hash-extract ((point jubjub-pointp))
  :returns (bits bit-listp)
  :short "The function @($\\mathsf{Extract}_{\\mathbb{J}^{(r)}}$)
          [ZPS:5.4.8.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "[ZPS] defines this is defined on @($\\mathbb{J}^{(r)}$),
     not all of @($\\mathbb{J}$),
     but for now we define on all of @($\\mathbb{J}$)
     because we do not have an ACL2 definition of @($\\mathbb{J}^{(r)}$) yet,
     and in fact the function is well-defined on all of @($\\mathbb{J}$)."))
  (i2lebsp *l-merkle-sapling* (jubjub-point->u point))
  :guard-hints (("Goal" :in-theory (enable jubjub-q)))
  ///
  (defret len-of-hash-extract
    (equal (len bits) *l-merkle-sapling*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define group-hash ((d byte-listp) (m byte-listp))
  :guard (and (= (len d) 8)
              (< (len m) (- blake::*blake2s-max-data-byte-length* 128)))
  :returns (point? maybe-jubjub-pointp)
  :short "The function
          @($\\mathsf{GroupHash_\\mathsf{URS}^{\\mathbb{J}^{(r)*}}}$)
          [ZPS:5.4.8.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "[ZPS] allows the argument @($M$) to have any length,
     but there is a (large) limit (see guard of @(tsee blake2s-256)).
     The limit here must be dimished by 64,
     which is the length of @($\\mathsf{URS}$)."))
  (b* ((hash (blake2s-256 d (append *urs* m)))
       (point (jubjub-abst (leos2bsp hash)))
       ((unless (jubjub-pointp point)) nil)
       (qoint (jubjub-mul (jubjub-h) point))
       ((when (equal qoint (ecurve::twisted-edwards-zero))) nil))
    qoint)
  :guard-hints (("Goal" :do-not-induct t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-group-hash ((d byte-listp) (m byte-listp))
  :guard (and (= (len d) 8)
              (< (len m) (- blake::*blake2s-max-data-byte-length* 129)))
  :returns (point? maybe-jubjub-pointp)
  :short "The function @($\\mathsf{FindGroupHash^{\\mathbb{J}^{(r)*}}}$)
          [ZPS:5.4.8.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since we need to append a byte to the message input,
     we need to diminish its maximum size by one in the guard."))
  (find-group-hash-loop 0 d m)

  :prepwork
  ((define find-group-hash-loop ((i natp) (d byte-listp) (m byte-listp))
     :guard (and (= (len d) 8)
                 (< (len m) (- blake::*blake2s-max-data-byte-length* 129)))
     :returns (point? maybe-jubjub-pointp)
     :parents nil
     (if (mbt (natp i))
         (if (< i 256)
             (b* ((point? (group-hash d (append m (list i)))))
               (or point?
                   (find-group-hash-loop (1+ i) d m)))
           nil)
       (acl2::impossible))
     :guard-hints (("Goal" :in-theory (enable bytep)))
     :measure (nfix (- 256 i)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-pad ((m bit-listp))
  :guard (consp m)
  :returns (m1 bit-listp :hyp (bit-listp m))
  :short "Pedersen hash padding [ZPS:5.4.1.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The message is padded with zero bits on the right
     to make its length a multiple of 3."))
  (case (mod (len m) 3)
    (0 m)
    (1 (append m (list 0 0)))
    (2 (append m (list 0))))
  ///

  (local (include-book "arithmetic-3/top" :dir :system))

  (defruledl lemma1
    (implies (and (integerp i)
                  (equal (mod i 3) 0))
             (equal (* 3 (ceiling i 3))
                    i)))

  (defruledl lemma2
    (implies (and (integerp i)
                  (equal (mod i 3) 1))
             (equal (* 3 (ceiling i 3))
                    (+ i 2))))

  (defruledl lemma3
    (implies (and (integerp i)
                  (equal (mod i 3) 2))
             (equal (* 3 (ceiling i 3))
                    (+ i 1))))

  (defret len-of-pedersen-pad
    (equal (len m1)
           (* 3 (ceiling (len m) 3)))
    :hints (("Goal" :use ((:instance lemma1 (i (len m)))
                          (:instance lemma2 (i (len m)))
                          (:instance lemma3 (i (len m)))))))

  (defret multiple-of-3-len-of-pedersen-hash
    (integerp (/ (len m1) 3))
    :hints (("Goal" :use len-of-pedersen-pad))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-enc ((3bits bit-listp))
  :guard (= (len 3bits) 3)
  :returns (enc integerp
                :rule-classes (:type-prescription :rewrite)
                :hyp (bit-listp 3bits))
  :short "The function @($\\mathsf{enc}$) in [ZPS:5.4.1.7]."
  (b* ((s0 (first 3bits))
       (s1 (second 3bits))
       (s2 (third 3bits)))
    (* (- 1 (* 2 s2))
       (+ 1 s0 (* 2 s1))))
  ///

  (defret pedersen-enc-lower-bound
    (>= enc -4)
    :hyp (bit-listp 3bits)
    :rule-classes :linear)

  (defret pedersen-enc-upper-bound
    (<= enc 4)
    :hyp (bit-listp 3bits)
    :rule-classes :linear)

  (defret pedersen-enc-not-zero
    (not (equal enc 0))
    :hyp (bit-listp 3bits)
    :rule-classes :type-prescription)

  (defrule pedersen-enc-injectivity
    (implies (and (bit-listp x)
                  (bit-listp y)
                  (equal (len x) 3)
                  (equal (len y) 3))
             (equal (equal (pedersen-enc x)
                           (pedersen-enc y))
                    (equal x y)))
    :use ((:instance pedersen-enc-injectivity-on-lists-of-3
           (x0 (first x))
           (x1 (second x))
           (x2 (third x))
           (y0 (first y))
           (y1 (second y))
           (y2 (third y)))
          (:instance rephrase-list-of-3 (l x))
          (:instance rephrase-list-of-3 (l y)))
    :prep-lemmas
    ((defruled pedersen-enc-injectivity-on-lists-of-3
       (implies (and (bitp x0)
                     (bitp x1)
                     (bitp x2)
                     (bitp y0)
                     (bitp y1)
                     (bitp y2))
                (equal (equal (pedersen-enc (list x0 x1 x2))
                              (pedersen-enc (list y0 y1 y2)))
                       (and (equal x0 y0)
                            (equal x1 y1)
                            (equal x2 y2)))))
     (defrule rephrase-list-of-3
       (implies (and (true-listp l)
                     (= (len l) 3))
                (equal l (list (first l) (second l) (third l))))
       :rule-classes nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *pedersen-c*
  :short "The constant @($c$) in [ZPS:5.4.1.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take the value from [ZPS].
     Eventually we should confirm that it satisfies
     the property described in [ZPS]."))
  63)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-segment-scalar ((segment bit-listp))
  :guard (integerp (/ (len segment) 3))
  :returns (i integerp :hyp (bit-listp segment))
  :short "The function @($\\langle\\cdot\\rangle$) in [ZPS:5.4.1.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the scalar that is used in the Jubjub multiplication,
     i.e. @($\\langle M_i \\rangle$) for the segment @($M_i$)."))
  (pedersen-segment-scalar-loop 1 segment)

  :prepwork

  ((local (include-book "arithmetic-3/top" :dir :system))

   (define pedersen-segment-scalar-loop ((j posp) (segment bit-listp))
     :guard (integerp (/ (len segment) 3))
     :returns (i integerp :hyp (and (posp j) (bit-listp segment)))
     :parents nil
     (if (consp segment)
         (+ (* (pedersen-enc (take 3 segment))
               (expt 2 (* 4 (1- j))))
            (pedersen-segment-scalar-loop (1+ j) (nthcdr 3 segment)))
       0)
     :measure (len segment)
     :prepwork ((local (include-book "std/lists/nthcdr" :dir :system)))

     :verify-guards nil ; done below

     ///

     (defrulel verify-guards-lemma
       (implies (and (integerp (/ (len x) 3))
                     (consp x))
                (>= (len x) 3))
       :cases ((equal (len x) 1)
               (equal (len x) 2))
       :rule-classes :linear
       :prep-books ((include-book "std/lists/len" :dir :system)))

     (verify-guards pedersen-segment-scalar-loop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-segment-scalar-bound ((segment bit-listp))
  :guard (integerp (/ (len segment) 3))
  :returns (bound natp)
  :short "Bound on the value of @(tsee pedersen-segment-scalar)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Theorem 5.4.1 in [ZPS:5.4.1.7] defines @$(\\Delta$) as
     a bound on the value of the encoding function @($\\langle\\cdot\\rangle$):
     the value of the function is between @($-\\Delta$) and @($\\Delta$).
     In [ZPS], @($\\Delta$) is a constant because @($\\langle\\cdot\\rangle$)
     is defined over segments of maximum size @($3c$).
     However, our @(tsee pedersen-segment-scalar) is more generally defined
     over segments of any length that is a multiple of 3.
     Accordingly, we define a function that expresses @($\\Delta$)
     in terms of (the length of) the segment.
     Since @(tsee pedersen-segment-scalar) is defined in terms of
     an auxiliary recursive function that is defined even more generally
     over not only a segment of length multiple of 3
     but also the index @($j$) of the chunk of 3 bits,
     we also introduce a function that expresses
     the bound on the recursive function.")
   (xdoc::p
    "Based on the summation that defines @($\\Delta$) in [ZPS],
     we define the bound for the recursive function
     by recursively adding @($4\\cdot2^{4\\cdot(j-1)}$)
     while @($j$) is incremented until there is no 3-bit chunk left.
     The bound for @(tsee pedersen-segment-scalar) is obtained from that
     by setting @($j$) to 1.")
   (xdoc::p
    "To prove that these are actual bounds,
     we start with a proof by induction for the recursive function and bound.
     We need a lemma about the length of @('(nthcdr 3 x)') being a multiple of 3
     when the length of @('x') is:
     this serves to relieve the hypothesis of the induction hypothesis.
     We also need a lemma saying that @('(take 3 segment)') is a list of bits
     under the hypothesis of the theorem:
     this is needed for the base case,
     to relieve the hypothesis of the bound rules of @(tsee pedersen-enc).
     We also need a few arithmetic lemmas
     to nudge the proof in the right direction.
     With linear bound rules for the recursive function in hand,
     the bound proofs for @(tsee pedersen-segment-scalar) are automatic."))
  (pedersen-segment-scalar-loop-bound 1 segment)

  :prepwork
  ((define pedersen-segment-scalar-loop-bound ((j posp) (segment bit-listp))
     :guard (integerp (/ (len segment) 3))
     :returns (bound natp :hyp (posp j))
     :parents nil
     (if (consp segment)
         (+ (* 4 (expt 2 (* 4 (1- j))))
            (pedersen-segment-scalar-loop-bound (1+ j) (nthcdr 3 segment)))
       0)
     :measure (len segment)
     :prepwork ((local (include-book "std/lists/nthcdr" :dir :system))
                (local (include-book "arithmetic-3/top" :dir :system)))))

  ///

  (defruledl arith-lemma1
    (implies (<= x y)
             (<= (* x (expt 2 a))
                 (* y (expt 2 a))))
    :prep-books ((include-book "arithmetic/top" :dir :system)))

  (defruledl arith-lemma2
    (implies (and (<= a b)
                  (<= x y))
             (<= (+ a x)
                 (+ y b))))

  (defruledl arith-lemma3
    (equal (- (* 4 x))
           (* -4 x)))

  (defrule pedersen-segment-scalar-loop-upper-bound
    (implies (and (posp j)
                  (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (<= (pedersen-segment-scalar-loop j segment)
                 (pedersen-segment-scalar-loop-bound j segment)))
    :rule-classes :linear
    :enable (pedersen-segment-scalar-loop
             pedersen-segment-scalar-loop-bound
             arith-lemma1 arith-lemma2))

  (defrule pedersen-segment-scalar-loop-lower-bound
    (implies (and (posp j)
                  (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (<= (- (pedersen-segment-scalar-loop-bound j segment))
                 (pedersen-segment-scalar-loop j segment)))
    :rule-classes :linear
    :enable (pedersen-segment-scalar-loop
             pedersen-segment-scalar-loop-bound
             arith-lemma1 arith-lemma2 arith-lemma3))

  (defrule pedersen-segment-scalar-upper-bound
    (implies (and (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (<= (pedersen-segment-scalar segment)
                 (pedersen-segment-scalar-bound segment)))
    :rule-classes :linear
    :enable (pedersen-segment-scalar pedersen-segment-scalar-bound))

  (defrule pedersen-segment-scalar-lower-bound
    (implies (and (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (<= (- (pedersen-segment-scalar-bound segment))
                 (pedersen-segment-scalar segment)))
    :rule-classes :linear
    :enable (pedersen-segment-scalar pedersen-segment-scalar-bound)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pedersen-segment-scalar-not-zero-proof
  :short "Proof that @(tsee pedersen-segment-scalar) is not 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by first proving that
     the loop function is outside the interval
     between @($-2^{4\\cdot(j-1)}$) to @($2^{4\\cdot(j-1)}$)
     both exclusive.
     Setting @($j=1$), we have that @(tsee pedersen-segment-scalar)
     is outside the interval from -1 to 1 exclusive, i.e. it is not 0.
     To prove the lemma about the loop function,
     to avoid dealing with a disjunction of inequalities,
     we introduce a predicate for being outside the interval
     and we prove some theorems about it.
     Some of these theorems are currently somewhat specific;
     perhaps there is a way to improve the form of the proof."))

  (local
   (define outsidep (x b)
     (or (<= x (- b))
         (<= b x))
     :verify-guards nil))

  (defruledl outsidep-lemma1
    (implies (posp c)
             (equal (outsidep (* c x) c)
                    (outsidep x 1)))
    :enable outsidep
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defruledl outsidep-lemma2
    (implies (and (posp c)
                  (outsidep x (* c b))
                  (integerp y)
                  (< (- c) y)
                  (< y c))
             (outsidep (+ x (* y b)) b))
    :enable outsidep
    :prep-books ((include-book "arithmetic-5/top" :dir :system)
                 (set-default-hints '((acl2::nonlinearp-default-hint
                                       stable-under-simplificationp
                                       hist
                                       pspv)))))

  (defruledl outsidep-lemma3
    (implies (and (posp j)
                  (outsidep x (expt 2 (* 4 j)))
                  (integerp y)
                  (< -16 y)
                  (< y 16))
             (outsidep (+ x (* y (expt 2 (+ -4 (* 4 j)))))
                       (expt 2 (+ -4 (* 4 j)))))
    :use (:instance outsidep-lemma2 (c 16) (b (expt 2 (+ -4 (* 4 j)))))
    :prep-books ((include-book "arithmetic/top" :dir :system)))

  (defruledl posp-of-bound
    (implies (posp j)
             (posp (expt 2 (+ -4 (* 4 j)))))
    :rule-classes :type-prescription
    :prep-books ((include-book "arithmetic-3/top" :dir :system)))

  (defruledl outsidep-of-pedersen-segment-scalar-loop
    (implies (and (posp j)
                  (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (outsidep (pedersen-segment-scalar-loop j segment)
                       (expt 2 (+ -4 (* 4 j)))))
    :enable (pedersen-segment-scalar-loop
             outsidep-lemma1
             outsidep-lemma3
             posp-of-bound))

  (defrule pedersen-segment-scalar-not-zero
    (implies (and (bit-listp segment)
                  (integerp (/ (len segment) 3))
                  (consp segment))
             (not (equal (pedersen-segment-scalar segment) 0)))
    :rule-classes :type-prescription
    :enable pedersen-segment-scalar
    :use (:instance outsidep-of-pedersen-segment-scalar-loop (j 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-segment-point ((d byte-listp) (i posp))
  :guard (= (len d) 8)
  :returns (point? maybe-jubjub-pointp)
  :short "The function @($\\mathcal{I}$) in [ZPS:5.4.1.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns a Jubjub point from (the index of) a segment.
     However, @(tsee find-group-hash) may return @('nil'),
     so we need to allow that case here.
     [ZPS] does not explicitly handles that case,
     perhaps because it is not going to happen with overwhelming probability.")
   (xdoc::p
    "We need to turn the index @($i$), diminished by one,
     into a byte sequence consisting of 32 bits, i.e. 4 bytes.
     There seems to be a bit of ambiguity on how to do that.
     The meaning of this kind of diagrams (i.e. boxes)
     is explained in the last two paragraphs [ZPS:5.2].
     First, take @($i - 1$), and turn it into a 32-bit unsigned integer;
     [ZPS] does not explicitly say that, but the diagram shows 32 bits
     (presumably it is envisioned that this integer will never exceed 32 bits).
     The first paragraph of [ZPS:5.2] says that, unless otherwise specified,
     integers are encoded in little endian bytes of fixed length;
     but here we need bits, so perhaps we should pick little endian bits.
     Once we have bits, the last two paragraphs of [ZPS:5.2] apply:
     we convert to bytes, with each byte in big endian.
     This seems a bit involved; we should confirm and/or test this."))
  (b* ((i1 (1- i))
       (i1-32bit (mod i1 (expt 2 32)))
       (bits (acl2::nat=>lebits 32 i1-32bit))
       (m (acl2::bits=>bebytes bits)))
    (find-group-hash d m))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-segment-addend ((d byte-listp) (segment bit-listp) (i posp))
  :guard (and (= (len d) 8)
              (integerp (/ (len segment) 3)))
  :returns (point? maybe-jubjub-pointp)
  :short "The addend point in the definition of
          @($\\mathsf{PedersenHashPoint}$) [ZPS:5.4.1.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @($[\\langle{M_i}\\rangle]\\mathcal{I}_i^D$)."))
  (b* ((ipoint (pedersen-segment-point d i))
       ((unless (jubjub-pointp ipoint)) nil)
       (scalar (pedersen-segment-scalar segment)))
    (jubjub-mul scalar ipoint)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen-point ((d byte-listp) (m bit-listp))
  :guard (and (= (len d) 8) (consp m))
  :returns (point? maybe-jubjub-pointp)
  :short "The function @($\\mathsf{PedersenHashToPoint}$) [ZPS:5.4.1.7]."
  (b* ((m1 (pedersen-pad m)))
    (pedersen-point-loop 1 d m1))

  :prepwork
  ((define pedersen-point-loop ((i posp) (d byte-listp) (m1 bit-listp))
     :guard (and (= (len d) 8)
                 (integerp (/ (len m1) 3)))
     :returns (point? maybe-jubjub-pointp)
     :parents nil
     (b* (((when (<= (len m1) (* 3 *pedersen-c*)))
           (pedersen-segment-addend d m1 i))
          (point1 (pedersen-segment-addend d (take (* 3 *pedersen-c*) m1) i))
          ((unless (jubjub-pointp point1)) nil)
          (point2 (pedersen-point-loop (1+ i) d (nthcdr (* 3 *pedersen-c*) m1)))
          ((unless (jubjub-pointp point2)) nil))
       (jubjub-add point1 point2))
     :measure (len m1)
     :prepwork ((local (include-book "std/lists/nthcdr" :dir :system))))
   (local (include-book "arithmetic/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pedersen ((d byte-listp) (m bit-listp))
  :guard (and (= (len d) 8) (consp m))
  :returns (hash bit-listp)
  :short "The function @($\\mathsf{PedersenHash}$) [ZPS:5.4.1.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if, instead of a point, an error is returned.
     This is distinguishes from a valid hash, which is not empty."))
  (b* ((point (pedersen-point d m))
       ((unless (jubjub-pointp point)) nil))
    (hash-extract point)))
