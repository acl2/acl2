; Std/basic - Basic definitions
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; arith-equivs.lisp -- congruence reasoning about integers/naturals/bits


;; Note: To use this book at full strength, do:
;; (local (in-theory (enable* arith-equiv-forwarding)))

(in-package "ACL2")
(include-book "arith-equiv-defs")
(include-book "std/lists/mfc-utils" :dir :system)


(defthm posp-redefinition
  (equal (posp x) (not (zp x))))

(defthm ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x) x)))

(defthm nfix-when-natp
  (implies (natp x)
           (equal (nfix x) x)))

(defthm bfix-when-bitp
  (implies (bitp x)
           (equal (bfix x) x)))



(defthm ifix-when-not-integerp
  (implies (not (integerp x))
           (equal (ifix x) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm nfix-when-not-natp
  (implies (not (natp x))
           (equal (nfix x) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm bfix-when-not-bitp
  (implies (not (bitp x))
           (equal (bfix x) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

;; Canonicalizing in this way seems sort of bad because we lost the
;; compound recognizer stuff about zp/zip

;; (defthm zip-to-int-equiv
;;   (equal (zip x) (int-equiv x 0)))

;; (defthm zp-to-nat-equiv
;;   (equal (zp x) (nat-equiv x 0)))

;; (defthm zbp-to-bit-equiv
;;   (equal (zbp x) (bit-equiv x 0)))

;; This seems like a better alternative...

(defthm int-equiv-zero
  (equal (int-equiv x 0) (zip x)))

(defthm nat-equiv-zero
  (equal (nat-equiv x 0) (zp x)))

;; And there are similar rules we can use to normalize things into ZP, ZIP, etc.

(defthm nfix-gt-0
  (equal (< 0 (nfix x))
         (not (zp x))))

(defthm ifix-equal-to-0
  (equal (equal (ifix x) 0)
         (zip x)))

(defthm nfix-equal-to-zero
  (equal (equal (nfix x) 0)
         (zp x)))



(defthm ifix-equal-to-nonzero-const
  (implies (and (syntaxp (quotep n))
                (not (zip n)))
           (equal (equal (ifix x) n)
                  (equal x n))))

(defthm nfix-equal-to-nonzero-const
  (implies (and (syntaxp (quotep n))
                (not (zp n)))
           (equal (equal (nfix x) n)
                  (equal x n))))


; When we started using the more sophisticated equal-by-logbitp hammer, we
; found that we were running into (equal (nfix x) n) terms, where n was greater
; than zero.  In these cases we really want to learn that X is a natural.  It's
; easy to imagine these rules getting expensive, so we might want to consider
; backchain limits.

(defthm ifix-equal-to-nonzero
  (implies (not (zip n))
           (equal (equal (ifix x) n)
                  (equal x n))))

(defthm nfix-equal-to-nonzero
  (implies (not (zp n))
           (equal (equal (nfix x) n)
                  (equal x n))))


(defthm bfix-gt-0
  (equal (< 0 (bfix x))
         (equal x 1)))

(defthm bfix-equal-0
  (equal (equal 0 (bfix x))
         (not (bit->bool x)))
  :hints(("Goal" :in-theory (enable bit->bool))))

(defthm bfix-equal-1
  (equal (equal 1 (bfix x))
         (bit->bool x))
  :hints(("Goal" :in-theory (enable bit->bool))))

(defthm bfix-when-not-1
  (implies (not (equal x 1))
           (equal (bfix x) 0)))


(local (in-theory (enable negp)))

(defthm negp-when-integerp
  (implies (integerp x)
           (equal (negp x)
                  (< x 0)))
  :hints(("Goal" :in-theory (enable negp)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthm negp-when-less-than-0
  (implies (< x 0)
           (equal (negp x)
                  (integerp x)))
  :hints(("Goal" :in-theory (enable negp)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthm natp-when-integerp
  (implies (integerp x)
           (equal (natp x)
                  (<= 0 x)))
  :hints(("Goal" :in-theory (enable negp)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthm natp-when-gte-0
  (implies (<= 0 x)
           (equal (natp x)
                  (integerp x)))
  :hints(("Goal" :in-theory (enable negp)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))


(defthm zp-when-integerp
  (implies (integerp x)
           (equal (zp x)
                  (<= x 0)))
  :hints(("Goal" :in-theory (enable negp)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))

(defthm zp-when-gt-0
  (implies (< 0 x)
           (equal (zp x)
                  (not (integerp x))))
  :hints(("Goal" :in-theory (enable negp)))
  :rule-classes ((:rewrite :backchain-limit-lst (1))))


(defthm negp-fc-1
  (implies (negp x)
           (integerp x))
  :rule-classes :forward-chaining)

(defthm negp-fc-2
  (implies (negp x)
           (< x 0))
  :rule-classes :forward-chaining)


(defthm ifix-negative-to-negp
  (equal (< (ifix x) 0)
         (negp x)))

(defthm ifix-positive-to-non-zp
  (equal (< 0 (ifix x))
         (not (zp x))))

(defthm nfix-positive-to-non-zp
  (equal (< 0 (nfix x))
         (not (zp x))))

(defthm bfix-positive-to-equal-1
  (equal (< 0 (bfix x))
         (equal 1 x)))



(defthm zip-forward-to-int-equiv-0
  (implies (zip x)
           (int-equiv x 0))
  :rule-classes :forward-chaining)

(defthm zp-forward-to-nat-equiv-0
  (implies (zp x)
           (nat-equiv x 0))
  :rule-classes :forward-chaining)

(defthm zbp-forward-to-bit-equiv-0
  (implies (zbp x)
           (bit-equiv x 0))
  :rule-classes :forward-chaining)

(defthm not-negp-implies-ifix-nonnegative
  (implies (not (negp x))
           (<= 0 (ifix x)))
  :rule-classes :forward-chaining)

(defthm zp-implies-ifix-nonpositive
  (implies (zp x)
           (<= (ifix x) 0))
  :rule-classes :forward-chaining)


(def-ruleset! arith-equiv-minimal-forwarding
  '(zip-forward-to-int-equiv-0
    zp-forward-to-nat-equiv-0
    zbp-forward-to-bit-equiv-0
    not-negp-implies-ifix-nonnegative
    zp-implies-ifix-nonpositive))


(defthm negative-forward-to-nat-equiv-0
  (implies (< n 0)
           (nat-equiv n 0))
  :rule-classes :forward-chaining)

(defthm nonpositive-forward-to-nat-equiv-0
  (implies (<= n 0)
           (nat-equiv n 0))
  :rule-classes :forward-chaining)

(defthm not-integerp-forward-to-int-equiv-0
  (implies (not (integerp x))
           (int-equiv x 0))
  :rule-classes :forward-chaining)

(defthm not-natp-forward-to-int-equiv-0
  (implies (not (natp x))
           (nat-equiv x 0))
  :rule-classes :forward-chaining)

(defthm not-bitp-forward-to-int-equiv-0
  (implies (not (bitp x))
           (bit-equiv x 0))
  :rule-classes :forward-chaining)

(defthm equal-ifix-foward-to-int-equiv
  (implies (and (equal (ifix x) y)
                (syntaxp (not (and (consp y)
                                   (eq (car y) 'ifix)))))
           (int-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-ifix-foward-to-int-equiv-both
  (implies (equal (ifix x) (ifix y))
           (int-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-nfix-foward-to-nat-equiv
  (implies (and (equal (nfix x) y)
                (syntaxp (not (and (consp y)
                                   (eq (car y) 'nfix)))))
           (nat-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-nfix-foward-to-nat-equiv-both
  (implies (equal (nfix x) (nfix y))
           (nat-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-bfix-foward-to-bit-equiv
  (implies (and (equal (bfix x) y)
                (syntaxp (not (and (consp y)
                                   (eq (car y) 'bfix)))))
           (bit-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-bfix-foward-to-bit-equiv-both
  (implies (equal (bfix x) (bfix y))
           (bit-equiv x y))
  :rule-classes :forward-chaining)

(defthm equal-bit->bool-foward-to-bit-equiv
  (implies (and (equal (bit->bool x) y)
                (syntaxp (not (and (consp y)
                                   (eq (car y) 'bit->bool)))))
           (bit-equiv x (bool->bit y)))
  :hints(("Goal" :in-theory (enable bit->bool)))
  :rule-classes :forward-chaining)

(defthm equal-bit->bool-foward-to-bit-equiv-both
  (implies (equal (bit->bool x) (bit->bool y))
           (bit-equiv x y))
  :hints(("Goal" :in-theory (enable bit->bool)))
  :rule-classes :forward-chaining)

(defthm not-equal-1-forward-to-bit-equiv
  (implies (not (equal x 1))
           (bit-equiv x 0))
  :rule-classes :forward-chaining)

(defthm not-bit->bool-forward-to-bit-equiv-0
  (implies (not (bit->bool x))
           (bit-equiv x 0))
  :hints(("Goal" :in-theory (enable bit->bool)))
  :rule-classes :forward-chaining)

(defthm bit->bool-forward-to-equal-1
  (implies (bit->bool x)
           (equal x 1))
  :hints(("Goal" :in-theory (enable bit->bool)))
  :rule-classes :forward-chaining)


; When we started using the more sophisticated equal-by-logbitp hammer, we
; found that we were running into hyps like (< 7 (nfix n)) and failing to
; realize that N was a natural.
;
; We can get close to what we want with just some forward-chaining rules:

; Note: disabling these for now, and removing them from the ruleset below.
; Consider:

;; (defstub foo (x y) t)

;; (defaxiom foo-axiom
;;   (implies (and (equal x (< (nfix a) (nfix b)))
;;                 (syntaxp (prog2$ (cw "x: ~x0~%" x)
;;                                  t))
;;                 x)
;;            (equal (foo a b) t)))

;; (thm (implies (< (nfix a) (nfix b))
;;               (foo a b)))

; This fails when inequality-with-nfix-foward-to-natp-1 is enabled, because
; we forward-chain from the (< (nfix a) (nfix b)) hyp to (natp b), which then
; causes (< (nfix a) (nfix b)) to rewrite to (< (nfix a) b) and not get relieved.

(defthmd inequality-with-nfix-forward-to-natp-1
  (implies (and (< a (nfix n))
                (<= 0 a))
           (natp n))
  :rule-classes :forward-chaining)

(defthmd inequality-with-nfix-forward-to-natp-2
  (implies (and (<= a (nfix n))
                (< 0 a))
           (natp n))
  :rule-classes :forward-chaining)

; But something insidious can happen here.  For instance:
;
#||

(defstub foo (x) t)

(defthm crock (implies (< 3 (nfix n)) (foo n))
  :hints(("Goal" :in-theory (disable nfix))))

(defthm crock2 (implies (<= 3 (nfix n)) (foo n))
    :hints(("Goal" :in-theory (disable nfix))))

||#
;
; Here, the forward-chaining rules don't appear to get us anything, because
; when we rewrite the particular hyp (< 3 (nfix n)), we don't assume that
; particular hyp, and nothing else in the clause shows us that (natp n).
;
; What we really want to do in this special case is to go ahead and replace the
; inequality in the clause with (and (natp n) (< 3 n)).  If we had this as a
; general rewrite rule it would introduce case-splits, but as a special rule
; that only applies to top-level literals we won't introduce case-splits.

(defthm inequality-with-nfix-hyp-1
  ;; Rewrite top-level (< 3 (nfix n)) into (and (natp n) (< 3 n)).
  ;; We originally did this only for quoteps, but I think since we're only
  ;; rewriting top-level hyps it should be cheap, and found cases where we
  ;; seem to want to do this to non-constants, too.
  (implies (and (syntaxp (rewriting-negative-literal-fn `(< ,a (nfix ,n)) mfc state))
                (<= 0 a))
           (equal (< a (nfix n))
                  (and (natp n)
                       (< a n)))))

(defthm inequality-with-nfix-hyp-2
  ;; Rewrite top-level (<= 3 (nfix n)) into (and (natp n) (<= 3 n))
  (implies (and (syntaxp (rewriting-positive-literal-fn `(< (nfix ,n) ,a) mfc state))
                (< 0 a))
           (equal (< (nfix n) a)
                  (not (and (natp n)
                            (<= a n)))))
  :hints(("Goal" :in-theory (enable nfix))))


(def-ruleset! arith-equiv-forwarding
  '(negative-forward-to-nat-equiv-0
    nonpositive-forward-to-nat-equiv-0
    not-integerp-forward-to-int-equiv-0
    not-natp-forward-to-int-equiv-0
    not-bitp-forward-to-int-equiv-0
    equal-ifix-foward-to-int-equiv
    equal-ifix-foward-to-int-equiv-both
    equal-nfix-foward-to-nat-equiv
    equal-nfix-foward-to-nat-equiv-both
    equal-bfix-foward-to-bit-equiv
    equal-bfix-foward-to-bit-equiv-both
    equal-bit->bool-foward-to-bit-equiv
    equal-bit->bool-foward-to-bit-equiv-both
    not-equal-1-forward-to-bit-equiv
    ; inequality-with-nfix-forward-to-natp-1
    ; inequality-with-nfix-forward-to-natp-2
    ))



;; (defthm ifix-when-zip
;;   (implies (zip x)
;;            (equal (ifix x) 0)))

;; (defthm nfix-when-zp
;;   (implies (zp x)
;;            (equal (nfix x) 0)))

;; (defthm bfix-when-zbp
;;   (implies (zbp x)
;;            (equal (bfix x) 0)))


;; (defthm int-equiv-to-equal-ifix
;;   (implies (integerp a)
;;            (equal (int-equiv a b)
;;                   (equal a (ifix b))))
;;   :rule-classes ((:rewrite)
;;                  (:rewrite :corollary
;;                   (implies (integerp a)
;;                            (equal (int-equiv b a)
;;                                   (equal a (ifix b)))))))

;; (defthm nat-equiv-to-equal-nfix
;;   (implies (natp a)
;;            (equal (nat-equiv a b)
;;                   (equal a (nfix b))))
;;   :rule-classes ((:rewrite)
;;                  (:rewrite :corollary
;;                   (implies (natp a)
;;                            (equal (nat-equiv b a)
;;                                   (equal a (nfix b)))))))

;; (defthm bit-equiv-to-equal-bfix
;;   (implies (bitp a)
;;            (equal (bit-equiv a b)
;;                   (equal a (bfix b))))
;;   :rule-classes ((:rewrite)
;;                  (:rewrite :corollary
;;                   (implies (bitp a)
;;                            (equal (bit-equiv b a)
;;                                   (equal a (bfix b)))))))

(defthmd equal-of-ifixes
  (equal (equal (ifix a) (ifix b))
         (int-equiv a b)))

(defthmd equal-of-nfixes
  (equal (equal (nfix a) (nfix b))
         (nat-equiv a b)))

(defthmd equal-of-bfixes
  (equal (equal (bfix a) (bfix b))
         (bit-equiv a b)))

(defthmd equal-of-bit->bools
  (equal (equal (bit->bool a) (bit->bool b))
         (bit-equiv a b))
  :hints(("Goal" :in-theory (enable bit->bool))))

;; (in-theory (disable int-equiv nat-equiv bit-equiv))

;; (theory-invariant (incompatible
;;                    (:rewrite equal-of-ifixes)
;;                    (:definition int-equiv)))

;; (theory-invariant (incompatible
;;                    (:rewrite equal-of-nfixes)
;;                    (:definition nat-equiv)))

;; (theory-invariant (incompatible
;;                    (:rewrite equal-of-bfixes)
;;                    (:definition bit-equiv)))



(in-theory (disable natp nfix bitp bfix ifix))


(defcong nat-equiv equal (nth n x) 1)
(defcong nat-equiv equal (update-nth n v x) 1)
(defcong nat-equiv equal (nthcdr n x) 1)
(defcong nat-equiv equal (take n x) 1)
(defcong nat-equiv equal (resize-list lst n default) 2)

(defcong nat-equiv equal (logbitp n x) 1
  :hints(("Goal" :in-theory (enable logbitp))))
(defcong int-equiv equal (logbitp n x) 2
  :hints(("Goal" :in-theory (enable logbitp))))

(defcong nat-equiv equal (logbit n x) 1
  :hints(("Goal" :in-theory (enable logbit))))
(defcong int-equiv equal (logbit n x) 2
  :hints(("Goal" :in-theory (enable logbit))))

(defcong int-equiv equal (logcar x) 1
  :hints(("Goal" :in-theory (enable logcar))))
(defcong int-equiv equal (logcdr x) 1
  :hints(("Goal" :in-theory (enable logcdr))))
(defcong bit-equiv equal (logcons b x) 1
  :hints(("Goal" :in-theory (enable logcons))))
(defcong int-equiv equal (logcons b x) 2
  :hints(("Goal" :in-theory (enable logcons))))

(defcong bit-equiv equal (b-not x) 1)
(defcong bit-equiv equal (b-and x y) 1)
(defcong bit-equiv equal (b-and x y) 2)
(defcong bit-equiv equal (b-ior x y) 1)
(defcong bit-equiv equal (b-ior x y) 2)
(defcong bit-equiv equal (b-xor x y) 1)
(defcong bit-equiv equal (b-xor x y) 2)
(defcong bit-equiv equal (b-eqv x y) 1)
(defcong bit-equiv equal (b-eqv x y) 2)
(defcong bit-equiv equal (b-nand x y) 1)
(defcong bit-equiv equal (b-nand x y) 2)
(defcong bit-equiv equal (b-nor x y) 1)
(defcong bit-equiv equal (b-nor x y) 2)
(defcong bit-equiv equal (b-andc1 x y) 1)
(defcong bit-equiv equal (b-andc1 x y) 2)
(defcong bit-equiv equal (b-andc2 x y) 1)
(defcong bit-equiv equal (b-andc2 x y) 2)
(defcong bit-equiv equal (b-orc1 x y) 1)
(defcong bit-equiv equal (b-orc1 x y) 2)
(defcong bit-equiv equal (b-orc2 x y) 1)
(defcong bit-equiv equal (b-orc2 x y) 2)
(defcong bit-equiv equal (b-ite test then else) 1)
(defcong bit-equiv equal (b-ite test then else) 2)
(defcong bit-equiv equal (b-ite test then else) 3)


(defcong int-equiv equal (lognot x) 1)

(defcong int-equiv equal (logand x y) 1
  :hints (("goal" :in-theory (enable ifix))))
(defcong int-equiv equal (logand x y) 2
  :hints (("goal" :in-theory (enable ifix))))

(defcong int-equiv equal (logior x y) 1
  :hints (("goal" :in-theory (enable ifix))))
(defcong int-equiv equal (logior x y) 2
  :hints (("goal" :in-theory (enable ifix))))

(defcong int-equiv equal (logxor x y) 1
  :hints (("goal" :in-theory (enable ifix))))
(defcong int-equiv equal (logxor x y) 2
  :hints (("goal" :in-theory (enable ifix))))

(defcong int-equiv equal (logite test then else) 1
  :hints (("goal" :in-theory (e/d (ifix logite) ((force))))))
(defcong int-equiv equal (logite test then else) 2
  :hints (("goal" :in-theory (e/d (ifix logite) ((force))))))
(defcong int-equiv equal (logite test then else) 3
  :hints (("goal" :in-theory (e/d (ifix logite) ((force))))))


(defcong nat-equiv equal (loghead n x) 1)
(defcong int-equiv equal (loghead n x) 2)

(defcong nat-equiv equal (logtail n x) 1)
(defcong int-equiv equal (logtail n x) 2)

(defcong int-equiv equal (expt b i) 2
  :hints(("Goal" :in-theory (enable ifix))))

(defcong int-equiv equal (ash i c) 1
  :hints(("Goal" :in-theory (e/d (ifix) (floor)))))
(defcong int-equiv equal (ash i c) 2
  :hints(("Goal" :in-theory (e/d (ifix) (floor)))))

(defcong int-equiv equal (integer-length x) 1
  :hints(("Goal" :in-theory (enable ifix))))

(defcong nat-equiv equal (logapp size i j) 1)
(defcong int-equiv equal (logapp size i j) 2)
(defcong int-equiv equal (logapp size i j) 3)

(defcong nat-equiv equal (logext n x) 1
  :hints(("Goal" :in-theory (e/d (nfix) (floor oddp expt)))))

(defcong int-equiv equal (logext n x) 2
  :hints(("Goal" :in-theory (e/d (ifix) (logbitp logapp expt)))))

(defcong nat-equiv equal (logmask n) 1)


(encapsulate
  ()

  (local (in-theory (enable bool->bit bit->bool)))

  ;; (bit->bool x) would just be the same as (equal x 1).  So we just use this
  ;; as our bit->bool.

  (defthm equal-1-of-bool->bit
    (iff (equal 1 (bool->bit x))
         x))

  (defthm equal-0-of-bool->bit
    (equal (equal 0 (bool->bit x))
           (not x)))

  (defthm bit->bool-of-bool->bit
    (equal (bit->bool (bool->bit x))
           (not (not x))))

  (defthm bool->bit-of-equal-1
    (equal (bool->bit (equal 1 x))
           (bfix x)))

  (defthm bool->bit-of-bit->bool
    (equal (bool->bit (bit->bool x))
           (bfix x)))

  (defthm bool->bit-of-not
    (equal (bool->bit (not x))
           (b-not (bool->bit x)))
    :hints(("Goal" :in-theory (enable b-not))))

  (defcong iff equal (bool->bit x) 1)

  ;; [Jared] 2016-04-08 BOZO.  I think we shouldn't need this rule because we
  ;; have a bitp type-prescription for bool->bit and, given
  ;; bitp-compound-recognizer, shouldn't we know that it's a bit?  But having
  ;; this as a rewrite seems to be necessary for a proof in
  ;; gl/always-equal-prep.lisp.  So, for now, I'll leave this in place, even
  ;; though I think we shouldn't need this???

  ;; [Matt K. mod 5/2016 (type-set bit for {1}):] It appears that the theorem
  ;; in centaur/gl/always-equal-prep.lisp whose proof was failing is
  ;; always-equal-ss-under-hyp-correct.  I've fixed it simply by enabling
  ;; (:type-prescription acl2::bool->bit$inline).

; (defthm bitp-of-bool->bit
;   (bitp (bool->bit x)))

  ;; (defthm bool->bit-bound
  ;;   (< (bool->bit x) 2)
  ;;   :rule-classes :linear)

  (defthm bfix-when-bit->bool
    (implies (bit->bool x)
             (equal (bfix x) 1))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm bfix-when-not-bit->bool
    (implies (not (bit->bool x))
             (equal (bfix x) 0))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))


(defsection bitops-in-terms-of-bit->bool
  (local (in-theory (enable bit->bool b-not b-and b-ior b-xor)))

  ;; These rules can be enabled to allow case-splitting on some
  ;; bit->bool occurrences.
  (defthmd bfix-in-terms-of-bit->bool
    (equal (bfix x)
           (if (bit->bool x) 1 0))
    :hints(("Goal" :in-theory (enable bfix))))


  (defthmd b-not-in-terms-of-bit->bool
    (equal (b-not x)
           (if (bit->bool x) 0 1))
    :hints(("Goal" :in-theory (enable bfix))))

  (defthmd b-and-in-terms-of-bit->bool
    (equal (b-and x y)
           (if (bit->bool x) (bfix y) 0))
    :hints(("Goal" :in-theory (enable bfix))))

  (defthmd b-ior-in-terms-of-bit->bool
    (equal (b-ior x y)
           (if (bit->bool x) 1 (bfix y)))
    :hints(("Goal" :in-theory (enable bfix))))

  (defthmd b-xor-in-terms-of-bit->bool
    (equal (b-xor x y)
           (if (bit->bool x)
               (b-not y)
             (bfix y)))
    :hints(("Goal" :in-theory (enable bfix)))))



(in-theory (disable* arith-equiv-forwarding))

