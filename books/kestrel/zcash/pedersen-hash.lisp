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

(include-book "kestrel/crypto/ecurve/jubjub" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "kestrel/utilities/bytes-as-digits" :dir :system)
(include-book "kestrel/utilities/bits-and-bytes-as-digits" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

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

(defval *l-merkle-sapling*
  :short "The constant @($\\ell_\\mathsf{MerkleSapling}$) [ZPS:5.3]."
  255)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define i2lebsp ((l natp) (x (integer-range-p 0 (expt 2 l) x)))
  :returns (bits bit-listp)
  :short "The function @($\\mathsf{I2LEBSP}$) [ZPS:5.2]."
  (acl2::nat=>lebits l x)
  ///
  (defret len-of-i2lebsp
    (equal (len bits) (nfix l))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lebs2ip ((s bit-listp))
  :returns (x natp :rule-classes :type-prescription)
  :short "The function @('$\\mathsf{LEBS2IP}$') [ZPS:5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('$\\ell$') argument can be determined from the @($S$) argument:
     it is the length of @($S$).
     Thus, in our formalization we just have one argument."))
  (acl2::lebits=>nat s)
  ///
  (local (include-book "arithmetic-3/top" :dir :system))
  (defret lebs2ip-upper-bound
    (< x (expt 2 (len s)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define leos2ip ((s byte-listp))
  :returns (x natp :rule-classes :type-prescription)
  :short "The function @('$\\mathsf{LEOS2IP}$') [ZPS:5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('$\\ell$') argument can be determined from the @($S$) argument:
     it is the length of @($S$) times 8.
     Thus, in our formalization we just have one argument."))
  (acl2::lebytes=>nat s)
  ///
  (local (include-book "arithmetic-3/top" :dir :system))
  (defret leos2ip-upper-bound
    (< x (expt 2 (* 8 (len s))))
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance acl2::lebytes=>nat-upper-bound
                   (acl2::digits s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define leos2bsp ((bytes byte-listp))
  :returns (bits bit-listp)
  :short "The function @($\\mathsf{LEOS2BSP}$) [ZPS:5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @($\\ell$) argumnent can be determined from the other argument:
     it is the length of the other argument times 8.
     Thus, in our formalization we just have one argument."))
  (acl2::lebytes=>bits bytes)
  ///
  (defret len-of-leos2bsp
    (equal (len bits)
           (* 8 (len bytes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize elements of @($\\mathbb{J}$) [ZPS:5.4.8.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the points on the Jubjub curve.")
   (xdoc::p
    "These are all finite points."))
  (and (ecurve::pointp x)
       (ecurve::point-on-twisted-edwards-p x (jubjub-curve)))
  ///
  (defruled point-finite-when-jubjub-pointp
    (implies (jubjub-pointp x)
             (equal (ecurve::point-kind x) :finite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-point->u ((point jubjub-pointp))
  :returns (u natp :rule-classes :type-prescription)
  :short "The function @($\\mathcal{U}$) [ZPS:5.4.8.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "[ZPS] defines this function on any finite point (in fact, on any pair),
     but it is only used on Jubjub points.")
   (xdoc::p
    "This is always below the Jubjub field prime."))
  (ecurve::point-finite->x point)
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp)))
  ///
  (defret jubjub-point->u-upper-bound
    (< u (jubjub-q))
    :hyp (jubjub-pointp point)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable jubjub-pointp
                                       ecurve::point-on-twisted-edwards-p
                                       jubjub-curve)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-point->v ((point jubjub-pointp))
  :returns (v natp :rule-classes :type-prescription)
  :short "The function @($\\mathcal{V}$) [ZPS:5.4.8.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "[ZPS] defines this function on any finite point (in fact, on any pair),
     but it is only used on Jubjub points.")
   (xdoc::p
    "This is always below the Jubjub field prime."))
  (ecurve::point-finite->y point)
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp)))
  ///
  (defret jubjub-point->v-upper-bound
    (< v (jubjub-q))
    :hyp (jubjub-pointp point)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable jubjub-pointp
                                       ecurve::point-on-twisted-edwards-p
                                       jubjub-curve)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-extract ((point jubjub-pointp))
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
  ///
  (defret len-of-jubjub-extract
    (equal (len bits) *l-merkle-sapling*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *urs*
  :short "The constant @($\\mathsf{URS}$) [ZPS:5.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is copied and pasted from [ZPS], and visually compared with it.
     Nonetheless, eventually it would be good to replicate, in ACL2,
     its calculation, which is described in [ZPS:5.9]."))
  (acl2::string=>nats
   "096b36a5804bfacef1691e173c366a47ff5ba84a44f26ddd7e8d9f79d5b42df0")
  ///
  (assert-event (byte-listp *urs*))
  (assert-event (equal (len *urs*) 64)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *jubjub-l*
  :short "The constant @($\\ell_\\mathbb{J}$) [ZPS:5.4.8.3]."
  256)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-jubjub-pointp (x)
  :returns (yes/no booleanp)
  :short "Recognize Jubjub points and @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are optional Jubjub points.
     Useful, for instance, as results of functions that may return
     either Jubjub points or an error value."))
  (or (jubjub-pointp x)
      (eq x nil))
  ///
  (defrule maybe-jubjub-pointp-when-jubjub-pointp
    (implies (jubjub-pointp x)
             (maybe-jubjub-pointp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-abst ((bits bit-listp))
  :guard (= (len bits) *jubjub-l*)
  :returns (point? maybe-jubjub-pointp
                   :hints (("Goal"
                            :in-theory (enable returns-lemma
                                               ecurve::pfield-squarep))))
  :short "The function @($\\mathsf{abst}_\\mathbb{J}$) [ZPS:5.4.8.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The definition in [ZPS] takes a square root @($u$) at some point,
     which may or may not exist; if it does, it is not exactly specified.
     So we use @(tsee ecurve::pfield-squarep) and @('pfield-square->root').
     It should be the case that the definition
     does not depend on the exact square root chosen;
     we should prove that eventually.")
   (xdoc::p
    "Note that, when @($u = 0$) and @($\\tilde{u} = 1$)
     (which happens, for instance, when the input bit sequence is
     @('(1 0 ... 0 1)'), i.e. 254 zeros surrounded by ones),
     the prescribed result is @($(q_\\mathbb{J}, 1)$) in [ZPS].
     However, we need to reduce that modulo @($q_\\mathbb{J}$),
     in order for it to be a field element in our model.
     For simplicity, we do the reduction in all cases,
     which always coerces an integer to the corresponding field element;
     we do that via the field negation operation, to ease proofs.")
   (xdoc::p
    "To prove that this returns an optional Jubjub point,
     we locally prove a key lemma, @('returns-lemma').
     It says that, when the square of @($u$) is
     the argument of the square root as used in the definition,
     @($(u,v)$) is on the curve:
     this is easily proved by simple algebraic manipulations,
     which turn the equality of the square into the curve equation."))
  (b* ((q (jubjub-q))
       (a (jubjub-a))
       (d (jubjub-d))
       (v* (butlast bits 1))
       (u~ (car (last bits)))
       (v (lebs2ip v*))
       ((when (>= v q)) nil)
       (a-d.v^2 (sub a (mul d (mul v v q) q) q))
       ((when (equal a-d.v^2 0)) nil)
       (u^2 (div (sub 1 (mul v v q) q)
                 a-d.v^2
                 q))
       ((unless (ecurve::pfield-squarep u^2 q)) nil)
       (u (ecurve::pfield-square->root u^2 q)))
    (if (= (mod u 2) u~)
        (ecurve::point-finite u v)
      (ecurve::point-finite (neg u q) v)))

  :prepwork

  ((local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

   ;; When the following are enabled (particularly a and d),
   ;; prime field rules fire that combine their values in undesired ways.
   ;; So we disable them completely, but prove their needed properties.
   ;; Perhaps these should be moved to a more central place,
   ;; and these nullary functions should be always kept disabled.

   (defrulel fep-of-jubjub-a
     (fep (jubjub-a) (jubjub-q)))

   (defrulel fep-of-jubjub-d
     (fep (jubjub-d) (jubjub-q)))

   (defrulel jubjub-a-d-different
     (not (equal (jubjub-a) (jubjub-d))))

   (defrulel jubjub-a-not-zero
     (not (equal (jubjub-a) 0)))

   (defrulel jubjub-d-not-zero
     (not (equal (jubjub-d) 0)))

   (defrulel primep-of-jubjub-q
     (rtl::primep (jubjub-q)))

   (defrulel jubjub-q-not-two
     (not (equal (jubjub-q) 2)))

   (local (in-theory (disable (:e jubjub-a)
                              (:e jubjub-d)
                              (:e jubjub-q)
                              jubjub-q)))

   ;; This is they lemma for the :returns theorem.

   (defruledl returns-lemma
     (b* ((q (jubjub-q))
          (a (jubjub-a))
          (d (jubjub-d)))
       (implies (and (fep u q)
                     (fep v q)
                     (not (equal (sub a (mul d (mul v v q) q) q) 0))
                     (equal (mul u u q)
                            (div (sub 1 (mul v v q) q)
                                 (sub a (mul d (mul v v q) q) q)
                                 q)))
                (jubjub-pointp (ecurve::point-finite u v))))
     :use (step1 step2)

     :prep-lemmas

     ((defrule step1
        (b* ((q (jubjub-q))
             (a (jubjub-a))
             (d (jubjub-d)))
          (implies (and (fep u q)
                        (fep v q)
                        (not (equal (sub a (mul d (mul v v q) q) q) 0))
                        (equal (mul u u q)
                               (div (sub 1 (mul v v q) q)
                                    (sub a (mul d (mul v v q) q) q)
                                    q)))
                   (equal (mul (mul u u q)
                               (sub a (mul d (mul v v q) q) q)
                               q)
                          (sub 1 (mul v v q) q))))
        :enable div
        :disable ((:rewrite pfield::mul-of-add-arg1)
                  (:rewrite pfield::mul-of-add-arg2)
                  (:rewrite pfield::mul-associative)))

      (defrule step2
        (b* ((q (jubjub-q))
             (a (jubjub-a))
             (d (jubjub-d)))
          (implies (and (fep u q)
                        (fep v q)
                        (equal (mul (mul u u q)
                                    (sub a (mul d (mul v v q) q) q)
                                    q)
                               (sub 1 (mul v v q) q)))
                   (jubjub-pointp (ecurve::point-finite u v))))
        :enable (jubjub-pointp
                 ecurve::point-on-twisted-edwards-p
                 jubjub-curve)
        :prep-books
        ((include-book "kestrel/prime-fields/bind-free-rules" :dir :system))))))

  :verify-guards nil ; done below

  ///

  (local (include-book "std/lists/len" :dir :system))
  (local (include-book "std/lists/last" :dir :system))
  (local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))

  (defrulel verify-guards-lemma
    (implies (bitp x)
             (acl2-numberp x)))

  (verify-guards jubjub-abst
    :hints (("Goal" :in-theory (e/d (ecurve::pfield-squarep)
                                    (bitp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-h ()
  :returns (h natp)
  :short "The constant @($h_\\mathbb{J}$) [ZPS:5.4.8.3]."
  8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-mul ((scalar integerp) (point jubjub-pointp))
  :returns (point1 jubjub-pointp
                   :hyp (jubjub-pointp point)
                   :hints (("Goal" :in-theory (enable jubjub-pointp))))
  :short "Scalar multiplication [ZPS:4.1.8], on Jubjub."
  (ecurve::twisted-edwards-mul scalar point (jubjub-curve))
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jubjub-add ((point1 jubjub-pointp) (point2 jubjub-pointp))
  :returns (point jubjub-pointp
                  :hyp (and (jubjub-pointp point1) (jubjub-pointp point2))
                  :hints (("Goal" :in-theory (enable jubjub-pointp))))
  :short "Group addition [ZPS:4.1.8], on Jubjub."
  (ecurve::twisted-edwards-add point1 point2 (jubjub-curve))
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define group-hash ((d byte-listp) (m byte-listp))
  :guard (and (= (len d) 8)
              (< (len m) (- blake::*blake2s-max-data-byte-length* 128)))
  :returns (point? maybe-jubjub-pointp)
  :short "The function
          @($\\mathsf{GroupHash_\\mathsf{URS}^{\\mathbb{J}^(r)*}}$)
          [ZPS:5.4.8.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "[ZPS] allows the argument @($M$) to have any length,
     but there is a (large) limit (see guard of @(tsee blake2s-256)).
     The limit here must be dimished by 64,
     which is the length of @($\\mathsf{URS)$)."))
  (b* ((hash (blake2s-256 d (append *urs* m)))
       (point (jubjub-abst (leos2bsp hash)))
       ((unless (jubjub-pointp point)) nil)
       (qoint (jubjub-mul (jubjub-h) point))
       ((when (equal qoint (ecurve::twisted-edwards-neutral))) nil))
    qoint)
  :guard-hints (("Goal" :do-not-induct t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-group-hash ((d byte-listp) (m byte-listp))
  :guard (and (= (len d) 8)
              (< (len m) (- blake::*blake2s-max-data-byte-length* 129)))
  :returns (point? maybe-jubjub-pointp)
  :short "The function @($\\mathsf{FindGroupHash^{\\mathbb{J}^(r)*}}$)
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

(defval *uncommitted-sapling*
  :short "The constant @($\\mathsf{Uncommitted}^\\mathsf{Sapling}$) [ZPS:5.3]."
  (i2lebsp *l-merkle-sapling* 1))

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
  :returns (i integerp :hyp (bit-listp 3bits))
  :short "The function @($\\mathsf{enc}$) in [ZPS:5.4.1.7]."
  (b* ((s0 (first 3bits))
       (s1 (second 3bits))
       (s2 (third 3bits)))
    (* (- 1 (* 2 s2))
       (+ 1 s0 (* 2 s1)))))

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
  :short "The function @($\\langle\\bullet\\rangle$) in [ZPS:5.4.1.7]."
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
    "We need to turn the index @($i$) into four bytes (i.e. 32 bits),
     presumably in big endian and truncating any higher bytes."))
  (b* ((i1 (1- i))
       (i1-32bit (mod i1 (expt 2 32)))
       (m (acl2::nat=>bebytes 4 i1-32bit)))
    (find-group-hash d m))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))
  :guard-hints (("Goal" :in-theory (disable blake::bvplus-intro))))

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
    "This is @($[\\langle{M_i\\rangle]\\mathcal{I}_i^D$)."))
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
    (jubjub-extract point)))
