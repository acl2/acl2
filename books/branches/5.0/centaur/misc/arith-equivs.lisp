; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Jared Davis <jared@centtech.com>, Sol Swords <sswords@centtech.com>

; arith-equivs.lisp -- congruence reasoning about integers/naturals/bits


;; Note: To use this book at full strength, do:
;; (local (in-theory (enable* arith-equiv-forwarding)))

(in-package "ACL2")
(include-book "ihs/logops-definitions" :dir :system)
(include-book "tools/rulesets" :dir :system)

(defthm bitp-compound-recognizer
  ;; Questionable given the bitp-forward rule.  But I think we may still want
  ;; this.
  (implies (bitp x)
           (natp x))
  :rule-classes :compound-recognizer)

;; (defthm bitp-when-under-2
;;   ;; questionable to bring arithmetic into it
;;   (implies (< x 2)
;;            (equal (bitp x)
;;                   (natp x))))

;; (defthm bitp-when-over-1
;;   (implies (< 1 x)
;;            (not (bitp x))))

(defun int-equiv (a b)
  (declare (xargs :guard t))
  (equal (ifix a) (ifix b)))

(defun nat-equiv (a b)
  (declare (xargs :guard t))
  (equal (nfix a) (nfix b)))

(defun bit-equiv (x y)
  (declare (xargs :guard t))
  (equal (bfix x) (bfix y)))

(local (in-theory (enable int-equiv nat-equiv bit-equiv)))

(defequiv int-equiv)
(defequiv nat-equiv)
(defequiv bit-equiv)

(defrefinement int-equiv nat-equiv)
(defrefinement nat-equiv bit-equiv)
;; (defrefinement int-equiv bit-equiv) ;; already known

(defcong int-equiv equal (ifix a) 1)
(defcong nat-equiv equal (nfix a) 1)
(defcong bit-equiv equal (bfix a) 1)

(defthm ifix-under-int-equiv
  (int-equiv (ifix a) a))

(defthm nfix-under-nat-equiv
  (nat-equiv (nfix a) a))

(defthm bfix-under-bit-equiv
  (bit-equiv (bfix a) a))

(defcong int-equiv equal (zip a) 1)
(defcong nat-equiv equal (zp a)  1)
(defcong bit-equiv equal (zbp a) 1)

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


(defthm bfix-gt-0
  (equal (< 0 (bfix x))
         (equal x 1)))

(defthm bfix-equal-0
  (equal (equal 0 (bfix x))
         (not (equal x 1))))

(defthm bfix-equal-1
  (equal (equal 1 (bfix x))
         (equal x 1)))

(defthm bfix-when-not-1
  (implies (not (equal x 1))
           (equal (bfix x) 0)))



(defund negp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (< x 0)))

(local (in-theory (enable negp)))

(defthm negp-compound-recognizer
  (equal (negp x)
         (and (integerp x)
              (< x 0)))
  :rule-classes :compound-recognizer)

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

(defthm zp-forward-to-int-equiv-0
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
    zp-forward-to-int-equiv-0
    zbp-forward-to-bit-equiv-0
    not-negp-implies-ifix-nonnegative
    zp-implies-ifix-nonpositive))


(defthm negative-forward-to-nat-equiv-0
  (implies (< n 0)
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

(defthm not-equal-1-forward-to-bit-equiv
  (implies (not (equal x 1))
           (bit-equiv x 0))
  :rule-classes :forward-chaining)



(def-ruleset! arith-equiv-forwarding
  '(negative-forward-to-nat-equiv-0
    not-integerp-forward-to-int-equiv-0
    not-natp-forward-to-int-equiv-0
    not-bitp-forward-to-int-equiv-0
    equal-ifix-foward-to-int-equiv
    equal-ifix-foward-to-int-equiv-both
    equal-nfix-foward-to-nat-equiv
    equal-nfix-foward-to-nat-equiv-both
    equal-bfix-foward-to-bit-equiv
    equal-bfix-foward-to-bit-equiv-both
    not-equal-1-forward-to-bit-equiv))



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

;; (defthm equal-of-ifixes
;;   (equal (equal (ifix a) (ifix b))
;;          (int-equiv a b)))

;; (defthm equal-of-nfixes
;;   (equal (equal (nfix a) (nfix b))
;;          (nat-equiv a b)))

;; (defthm equal-of-bfixes
;;   (equal (equal (bfix a) (bfix b))
;;          (bit-equiv a b)))

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

  (defund bool->bit (x)
    (declare (xargs :guard t))
    (if x 1 0))

  (local (in-theory (enable bool->bit)))

  ;; (bit->bool x) would just be the same as (equal x 1).  So we just use this
  ;; as our bit->bool.

  (defthm equal-1-of-bool->bit
    (iff (equal 1 (bool->bit x))
         x))

  (defthm bool->bit-of-equal-1
    (equal (bool->bit (equal 1 x))
           (bfix x)))

  (defthm bool->bit-of-not
    (equal (bool->bit (not x))
           (b-not (bool->bit x)))
    :hints(("Goal" :in-theory (enable b-not))))

  (defcong iff equal (bool->bit x) 1)

  (defthm bitp-of-bool->bit
    (bitp (bool->bit x)))

  (defthm bool->bit-bound
    (< (bool->bit x) 2)
    :rule-classes :linear)

  (defthm bool->bit-equal-0
    (equal (equal (bool->bit x) 0)
           (not x))))




(in-theory (disable* arith-equiv-forwarding))

