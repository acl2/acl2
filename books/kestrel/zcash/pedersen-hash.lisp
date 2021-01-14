; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "kestrel/crypto/ecurve/jubjub" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "kestrel/utilities/bytes-as-digits" :dir :system)
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
     it is the length of @(S$) times 8.
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
       (ecurve::point-on-twisted-edwards-p x (ecurve::jubjub-curve)))
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
    (< u (ecurve::jubjub-q))
    :hyp (jubjub-pointp point)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable jubjub-pointp
                                       ecurve::point-on-twisted-edwards-p
                                       ecurve::jubjub-curve)))))

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
    (< v (ecurve::jubjub-q))
    :hyp (jubjub-pointp point)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable jubjub-pointp
                                       ecurve::point-on-twisted-edwards-p
                                       ecurve::jubjub-curve)))))

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
