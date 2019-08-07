; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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


; ihsext-basics.lisp
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "BITOPS")

;; BOZO Some of the rules from logops-lemmas that are made redundant by rules
;; here are left still enabled.  Perhaps accumulated-persistence will find the
;; important ones.

(include-book "std/basic/arith-equivs" :dir :system)

(local (in-theory (enable* arith-equiv-forwarding)))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

(defsection bitops/ihsext-basics
  :parents (bitops)
  :short "A key book in the bitops library.  This is intended to be a (still
lightweight) replacement for books such as @('ihs/logops-lemmas.lisp')."

  :long "<p>BOZO this needs a lot of documentation.  For now you're best
off looking at the source code.</p>")


;; [Jared] this was causing errors, I think due to the doc-string stripping code
;; not working when :doc nil is given.  Switching it to use std/util/defredundant
;; instead.
;; (include-book "tools/defredundant" :dir :system)
;; (defredundant-events

(encapsulate
  ()
  (local (include-book "std/util/defredundant" :dir :system))
  (make-event
   (b* ((imports #!ACL2 '(

; There are too many rules with forced hyps in logops-lemmas.  We'll locally
; include it and redundantly define many of the useful theorems.

                   constant-syntaxp
                   ash-0
                   cancel-equal-lognot
                   commutativity-of-logand
                   simplify-logand
                   commutativity-of-logior
                   simplify-logior
                   commutativity-of-logxor
                   simplify-logxor
                   simplify-logite
                   simplify-bit-functions
                   unsigned-byte-p-base-case
                   unsigned-byte-p-0
                   unsigned-byte-p-plus
                   difference-unsigned-byte-p
                   ;; signed-byte-p-base-cases
                   ;; backchain-signed-byte-p-to-unsigned-byte-p
                   loghead-identity
                   ;; loghead-0-i remove hyp
                   ;; loghead-size-0 remove hyp
                   ;; loghead-leq remove force
                   bitp-loghead-1
                   logtail-identity
                   ;; logtail-logtail remove hyps
                   ;; logtail-0-i remove hyp
                   ;; logtail-size-0 remove hyp
                   ;; logtail-leq remove hyp
                   ;; logtail-unsigned-byte-p remove hyp
                   ;; logtail-loghead remove hyp
                   ;; associativity-of-logapp remove hyp

                   logext-identity

                   ;; we'll prove a stronger rewrite rule and disable this
                   ;; rw, but it's a good elim
                   logcar-logcdr-elim

                   ;; these are weird but won't hurt much
                   logcar-2*i
                   logcar-i+2*j
                   logcdr-2*i
                   logcdr-i+2*j

                   ;; logbitp-0-minus-1 remove hyps
                   ;; logbit-0-minus-1 remove hyps

                   signed-byte-p-logops))
        (events (std::defredundant-fn imports nil state)))
     (acl2::value events))))

;; [Jared] these rules seem pretty expensive; especially if
;; signed-byte-p/unsigned-byte-p happen to be enabled.
(local (in-theory (disable acl2::logtail-identity
                           acl2::loghead-identity
                           acl2::logext-identity)))

(defconst *ihs-extensions-disables*
  '(floor mod expt ash evenp oddp
          logbitp logbit logior logand lognot logxor logite
          logcons logcar logcdr loghead logtail
          integer-length
          logmaskp logext logapp logrev
          b-eqv b-nand b-nor b-andc1 b-andc2 b-orc1 b-orc2
          b-not b-and b-ior b-xor b-ite bfix bitp
          logcount))


(make-event
 (prog2$ (cw "Bitops Note: disabling ~&0.~%~%"
             *ihs-extensions-disables*)
         '(value-triple :invisible))
 :check-expansion t)

(in-theory (set-difference-theories (current-theory :here)
                                    *ihs-extensions-disables*))

(def-ruleset! ihsext-basic-thms nil)
(def-ruleset! ihsext-advanced-thms nil)
(def-ruleset! ihsext-bad-type-thms nil)
(def-ruleset! ihsext-redefs nil)
(def-ruleset! ihsext-recursive-redefs nil)
(def-ruleset! ihsext-inductions nil)
(def-ruleset! ihsext-bounds-thms nil)
(def-ruleset! ihsext-arithmetic nil)


(defsection bit-ops

  (local (in-theory (enable b-eqv b-nand b-nor b-andc1 b-andc2 b-orc1 b-orc2
                            bfix b-not b-and b-ior b-xor bitp
                            bit->bool)))

  ;; expand this to other bitops or canonicalize to these four?
  ;; b-eqv b-nand b-nor b-andc1 b-andc2 b-orc1 b-orc2

  (defthm b-eqv-remove
    (equal (b-eqv a b)
           (b-not (b-xor a b))))

  (defthm b-nand-remove
    (equal (b-nand a b)
           (b-not (b-and a b))))

  (defthm b-nor-remove
    (equal (b-nor a b)
           (b-not (b-ior a b))))

  (defthm b-andc1-remove
    (equal (b-andc1 x y)
           (b-and (b-not x) y)))

  (defthm b-andc2-remove
    (equal (b-andc2 x y)
           (b-and x (b-not y))))

  (defthm b-orc1-remove
    (equal (b-orc1 x y)
           (b-ior (b-not x) y)))

  (defthm b-orc2-remove
    (equal (b-orc2 x y)
           (b-ior x (b-not y))))

  (defthm b-not-bound
    (<= (b-not x) 1)
    :rule-classes :linear)

  (defthm b-ior-bound
    (<= (b-ior x y) 1)
    :rule-classes :linear)

  (defthm b-and-bound
    (<= (b-and x y) 1)
    :rule-classes :linear)

  (defthm b-xor-bound
    (<= (b-xor x y) 1)
    :rule-classes :linear)

  ;; (defthm bxor-norm
  ;;   (implies
  ;;    (syntaxp (and
  ;;              (not (equal x ''0))
  ;;              (not (equal x ''1))
  ;;              (or
  ;;               (equal y ''0)
  ;;               (equal y ''1))))
  ;;    (equal
  ;;     (b-xor x y)
  ;;     (b-xor y x)))
  ;;   :hints (("goal" :in-theory (enable xor)))
  ;;   )

  (defthm commutativity-of-b-xor
    (equal (b-xor x y)
           (b-xor y x)))

  (defthm bxor-to-bnot
    (equal (b-xor 1 x)
           (b-not x)))

  (defthm bxor-to-id
    (equal (b-xor 0 x)
           (bfix x)))

  (defthm bfix-bound
    (<= (bfix x) 1)
    :rule-classes :linear)

  ;; (defthm bitp-by-natp-bound
  ;;   (implies (and (natp x)
  ;;                 (<= x 1))
  ;;            (bitp x)))

  ;; simplify-bit-functions does a bunch of simplifications on these
  ;; bit-functions-type has bitp rewrite and natp type prescrips

  (defthm b-not-b-not
    (equal (b-not (b-not x))
           (bfix x)))

  (defthm b-not-equal-0
    (equal (equal 0 (b-not x))
           (equal x 1)))

  (defthm b-not-equal-1
    (equal (equal 1 (b-not x))
           (not (equal x 1))))

  (defthm bit->bool-of-b-not
    (equal (bit->bool (b-not x))
           (not (bit->bool x))))

  ;; Some fancy rules, originally from centaur/sv/svex/bits.  These look like
  ;; they case-split ensure that we only apply these rules when no actual case
  ;; split would be caused.  For instance, in the first rule here, we
  ;; strengthen:
  ;;
  ;;  (implies (and ...
  ;;                (equal (b-and x y) 1)
  ;;                ...)
  ;;           concl)
  ;;
  ;; Into a new goal:
  ;;
  ;;  (implies (and ...
  ;;                (equal x 1)
  ;;                (equal y 1)
  ;;                ...)
  ;;           concl)
  ;;
  ;; But note that this just a single replacement goal, not two new goals. The
  ;; other rules are similar.

  (defthm b-and-equal-1-in-hyp
    (implies (syntaxp (or (acl2::rewriting-negative-literal-fn `(equal (acl2::b-and$inline ,x ,y) '1) mfc state)
                          (acl2::rewriting-negative-literal-fn `(equal '1 (acl2::b-and$inline ,x ,y)) mfc state)))
             (equal (equal (b-and x y) 1)
                    (and (equal x 1) (equal y 1)))))

  (defthm b-and-equal-0-in-concl
    (implies (syntaxp (or (acl2::rewriting-positive-literal-fn `(equal (acl2::b-and$inline ,x ,y) '0) mfc state)
                          (acl2::rewriting-positive-literal-fn `(equal '0 (acl2::b-and$inline ,x ,y)) mfc state)))
             (equal (equal (b-and x y) 0)
                    (or (not (equal x 1)) (not (equal y 1))))))

  (defthm b-ior-equal-1-in-concl
    (implies (syntaxp (or (acl2::rewriting-positive-literal-fn `(equal (acl2::b-ior$inline ,x ,y) '1) mfc state)
                          (acl2::rewriting-positive-literal-fn `(equal '1 (acl2::b-ior$inline ,x ,y)) mfc state)))
             (equal (equal (b-ior x y) 1)
                    (or (equal x 1) (equal y 1)))))

  (defthm b-ior-equal-0-in-concl
    (implies (syntaxp (or (acl2::rewriting-negative-literal-fn `(equal (acl2::b-ior$inline ,x ,y) '0) mfc state)
                          (acl2::rewriting-negative-literal-fn `(equal '0 (acl2::b-ior$inline ,x ,y)) mfc state)))
             (equal (equal (b-ior x y) 0)
                    (and (not (equal x 1)) (not (equal y 1))))))

  )



(defsection logcons-car-cdr

  (local (in-theory (enable logcar logcons logcdr)))

  (defthm logcar-bound
    (<= (logcar x) 1)
    :hints (("goal" :use ((:instance acl2::logcar-type (i x)))))
    :rule-classes :linear)

  ;; hopefully we don't need this:
  ;; (defthm logcons-when-zip
  ;;   (implies (zip x)
  ;;            (equal (logcons b x)
  ;;                   (bfix b))))

  (defthm logcons-b-0
    (equal (logcons b 0)
           (bfix b)))

  ;; (defthm logcons-of-ifix
  ;;   (equal (logcons b (ifix x))
  ;;          (logcons b x)))

  ;; (defthm logcons-when-not-bit
  ;;   (implies (not (bitp b))
  ;;            (equal (logcons b x)
  ;;                   (logcons 0 x))))

  ;; (defthm logcons-of-bfix
  ;;   (equal (logcons (bfix b) x)
  ;;          (logcons b x)))

  ;; (defthm logcar-when-zip
  ;;   (implies (zip i)
  ;;            (equal (logcar i) 0)))

  ;; (defthm logcar-of-ifix
  ;;   (equal (logcar (ifix x))
  ;;          (logcar x)))

  ;; (defthm logcdr-when-zip
  ;;   (implies (zip i)
  ;;            (equal (logcdr i) 0)))

  ;; (defthm logcdr-of-ifix
  ;;   (equal (logcdr (ifix x))
  ;;          (logcdr x)))

  ;; (add-to-ruleset ihsext-bad-type-thms
  ;;                 '(logcons-when-zip
  ;;                   logcons-when-not-bit
  ;;                   logcar-when-zip
  ;;                   logcdr-when-zip))

  ;; These are a special case since we don't produce definition rules
  ;; for logcar/logcdr/logcons
  (add-to-ruleset ihsext-basic-thms
                  '(logcons-b-0))
  ;;                 '(logcons-when-zip
  ;;                   logcons-when-not-bit
  ;;                   logcar-when-zip
  ;;                   logcdr-when-zip
  ;;                   logcons-of-ifix
  ;;                   logcons-of-bfix
  ;;                   logcar-of-ifix
  ;;                   logcar-of-ifix))

  ;; (local (in-theory (enable* ihsext-bad-type-thms)))
  (local (in-theory (disable logcar logcdr logcons)))

  (defthm logcar-of-bit
    (implies (bitp b)
             (equal (logcar b) b))
    :hints(("Goal" :in-theory (enable bitp))))

  (defthm logcdr-of-bit
    (implies (bitp b)
             (equal (logcdr b) 0))
    :hints(("Goal" :in-theory (enable bitp))))

  (defthm logcar-of-logcons
    (equal (logcar (logcons b x))
           (bfix b))
    :hints(("Goal" :cases ((integerp x)))
           (and stable-under-simplificationp
                '(:cases ((bitp b))))))

  (defthm logcdr-of-logcons
    (equal (logcdr (logcons b x))
           (ifix x))
    :hints (("goal" :cases ((bitp b)))
            (and stable-under-simplificationp
                 '(:cases ((integerp x))))))

  ;; ;; like the above but with integerp hyps
  ;; (in-theory (disable logcar-logcons
  ;;                     logcdr-logcons))

  (defthm logcons-destruct
    (equal (logcons (logcar x) (logcdr x))
           (ifix x)))

  ;; from ihs, like the above but with integerp hyp.  Leaving it enabled as an
  ;; elim rule.
  (in-theory (disable (:rewrite logcar-logcdr-elim)))

  (defthmd equal-logcons-strong
    (equal (equal (logcons a b) i)
           (and (integerp i)
                (equal (logcar i) (bfix a))
                (equal (logcdr i) (ifix b))))
    :hints (("goal" :cases ((bitp a)))
            (and stable-under-simplificationp
                 '(:cases ((integerp b))))))

  (local (in-theory (enable equal-logcons-strong)))

  (defthm equal-logcons-weak
    (equal (equal (logcons a b) (logcons c d))
           (and (equal (bfix a) (bfix c))
                (equal (ifix b) (ifix d)))))

  (defthm logcons-equal-constant
    (implies (syntaxp (quotep i))
             (equal (equal (logcons a b) i)
                    (and (integerp i)
                         (equal (logcar i) (bfix a))
                         (equal (logcdr i) (ifix b))))))

  (add-to-ruleset ihsext-basic-thms
                  '(logcar-of-logcons
                    logcdr-of-logcons
                    logcons-destruct
                    equal-logcons-weak
                    logcons-equal-constant))

  (add-to-ruleset ihsext-advanced-thms '(equal-logcons-strong))

  (defthmd logcons-<-0-linear
    (implies (and (integerp i) (< i 0))
             (< (logcons b i) 0))
    :rule-classes :linear)

  (defthmd logcons->=-0-linear
    (implies (or (not (integerp i))
                 (<= 0 i))
             (<= 0 (logcons b i)))
    :rule-classes :linear)

  (defthmd logcons->=-x-when-nonnegative
    (implies (<= 0 (ifix x))
             (<= (ifix x) (logcons b x)))
    :hints (("goal" :in-theory (enable logcons)))
    :rule-classes :linear)

  (defthmd logcons-<=-x-when-negative
    (implies (< (ifix x) 0)
             (<= (logcons b x) (ifix x)))
    :hints (("goal" :in-theory (enable logcons)))
    :rule-classes :linear)

  (defthmd logcons->-x-when-positive
    (implies (< 0 (ifix x))
             (< (ifix x) (logcons b x)))
    :hints(("Goal" :in-theory (enable logcons)))
    :rule-classes :linear)

  (defthmd logcons-<-x-when-below-minus1
    (implies (< (ifix x) -1)
             (< (logcons b x) (ifix x)))
    :hints(("Goal" :in-theory (enable logcons)))
    :rule-classes :linear)

  (defthmd logcdr-<-0-linear
    (implies (and (integerp i) (< i 0))
             (< (logcdr i) 0))
    :rule-classes :linear)

  (defthmd logcdr->=-0-linear
    (implies (or (not (integerp i))
                 (<= 0 i))
             (<= 0 (logcdr i)))
    :rule-classes :linear)

  (defthmd logcdr-<=-x-when-nonnegative
    (implies (<= 0 (ifix x))
             (<= (logcdr x) (ifix x)))
    :hints(("Goal" :in-theory (enable logcdr)))
    :rule-classes :linear)

  (defthmd logcdr-<-x-when-positive
    (implies (< 0 (ifix x))
             (< (logcdr x) (ifix x)))
    :hints(("Goal" :in-theory (enable logcdr)))
    :rule-classes :linear)

  (defthmd logcdr->=-x-when-nonpositive
    (implies (<= (ifix x) 0)
             (<= (ifix x) (logcdr x)))
    :hints(("Goal" :in-theory (enable logcdr ifix)))
    :rule-classes :linear)

  (defthmd logcdr->-x-when-below-minus1
    (implies (< (ifix x) -1)
             (< (ifix x) (logcdr x)))
    :hints(("Goal" :in-theory (enable logcdr ifix)))
    :rule-classes :linear)

  ;; from logops-definitions
  (add-to-ruleset ihsext-bounds-thms '(logcons-<-0-linear
                                       logcons->=-0-linear
                                       logcdr-<-0-linear
                                       logcdr->=-0-linear
                                       logcons->=-x-when-nonnegative
                                       logcons-<=-x-when-negative
                                       logcons->-x-when-positive
                                       logcons-<-x-when-below-minus1
                                       logcdr-<=-x-when-nonnegative
                                       logcdr-<-x-when-positive
                                       logcdr->=-x-when-nonpositive
                                       logcdr->-x-when-below-minus1))

  (defthmd logcons-<-n-strong
    (implies (integerp j)
             (equal (< (logcons b i) j)
                    (or (< (ifix i) (logcdr j))
                        (and (= (ifix i) (logcdr j))
                             (< (bfix b) (logcar j))))))
    :hints(("Goal" :in-theory (enable logcons))))

  (defthmd logcons->-n-strong
    (implies (integerp j)
             (equal (> (logcons b i) j)
                    (or (> (ifix i) (logcdr j))
                        (and (= (ifix i) (logcdr j))
                             (> (bfix b) (logcar j))))))
    :hints(("Goal" :in-theory (enable logcons))))

  (add-to-ruleset ihsext-advanced-thms '(acl2::logcons-<-0
                                         acl2::logcdr-<-0
                                         logcons-<-n-strong
                                         logcons->-n-strong))

  (defthm logcons-<-constant
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (< (logcons b i) j)
                    (or (< (ifix i) (logcdr j))
                        (and (= (ifix i) (logcdr j))
                             (< (bfix b) (logcar j))))))
    :hints(("Goal" :in-theory (enable logcons-<-n-strong))))

  (defthm logcons->-constant
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (> (logcons b i) j)
                    (or (> (ifix i) (logcdr j))
                        (and (= (ifix i) (logcdr j))
                             (> (bfix b) (logcar j))))))
    :hints(("Goal" :in-theory (enable logcons->-n-strong))))

  (defthm logcons-<-logcons
    (equal (< (logcons a i) (logcons b j))
           (or (< (ifix i) (ifix j))
               (and (= (ifix i) (ifix j))
                    (< (bfix a) (bfix b)))))
    :hints(("Goal" :in-theory (enable logcons-<-n-strong))))

  (add-to-ruleset ihsext-basic-thms '(logcons-<-constant
                                      logcons->-constant
                                      logcons-<-logcons))

  (defthm logcdr-<=-logcdr
    (implies (<= (ifix a) (ifix b))
             (<= (logcdr a) (logcdr b)))
    :rule-classes (:rewrite :linear))

  (add-to-ruleset ihsext-bounds-thms '(logcdr-<=-logcdr))

  (defthm logcdr-<-const
    (implies (and (syntaxp (quotep c))
                  (integerp c))
             (equal (< (logcdr x) c)
                    (< (ifix x) (logcons 0 c))))
    :hints(("Goal" :in-theory (enable logcons->-n-strong))))

  (defthm logcdr->-const
    (implies (and (syntaxp (quotep c))
                  (integerp c))
             (equal (> (logcdr x) c)
                    (> (ifix x) (logcons 1 c))))
    :hints(("Goal" :in-theory (enable logcons->-n-strong))))

  (add-to-ruleset ihsext-basic-thms '(logcdr-<-const logcdr->-const))

  (defthm logcdr-natp
    (implies (natp x)
             (natp (logcdr x)))
    :rule-classes :type-prescription)

  (defthm logcons-natp
    (implies (natp x)
             (natp (logcons b x)))
    :rule-classes :type-prescription)

  (defthm logcons-posp-1
    (implies (posp x)
             (posp (logcons b x)))
    :rule-classes :type-prescription)

  (defthm logcons-posp-2
    (implies (and (natp x)
                  (bit->bool b))
             (posp (logcons b x)))
    :rule-classes :type-prescription)

  (defthm logcons-negp
    (implies (negp x)
             (negp (logcons b x)))
    :hints(("Goal" :in-theory (enable negp)))
    :rule-classes :type-prescription)

  (defthm logcar-minus-a
    (equal (logcar (- a))
           (logcar a))
    :hints(("Goal" :in-theory (enable logcar ifix)))))




(defsection logbitp**

  (local (in-theory (enable acl2::logbitp*)))

  ;; (defthmd logbitp-when-not-natp
  ;;   (implies (not (natp i))
  ;;            (equal (logbitp i j)
  ;;                   (logbitp 0 j))))

  ;; (defthm logbitp-of-nfix
  ;;   (equal (logbitp (nfix i) j)
  ;;          (logbitp i j)))

  ;; (local (defthmd logbitp-when-not-integer
  ;;          (implies (not (integerp j))
  ;;                   (equal (logbitp i j)
  ;;                          (logbitp i 0)))))

  ;; (defthm logbitp-of-ifix
  ;;   (equal (logbitp i (ifix j))
  ;;          (logbitp i j)))

  ;; (defthmd logbitp-when-zip
  ;;   (implies (zip j)
  ;;            (equal (logbitp i j)
  ;;                   nil))
  ;;   :hints(("Goal" :in-theory (enable logbitp-when-not-integer
  ;;                                     floor zip))))

  (defthm logbitp-n-0
    (equal (logbitp n 0) nil)
    :hints (("goal" :cases ((natp n)))))

  (defthm logbitp-n-minus1
    (equal (logbitp n -1) t)
    :hints (("goal" :cases ((natp n)))))

  ;; (add-to-ruleset ihsext-bad-type-thms
  ;;                 '(logbitp-when-not-natp
  ;;                   logbitp-when-zip))

  (add-to-ruleset ihsext-basic-thms
                  '(logbitp-n-0
                    logbitp-n-minus1))

  ;; (local (in-theory (enable logbitp-when-zip
  ;;                           logbitp-when-not-natp
  ;;                           logcar-when-zip
  ;;                           logcdr-when-zip)))

  (local (in-theory (disable logbitp acl2::logbitp*)))

  (defthmd logbitp**
    ;; This is a better replacement for logbitp* that doesn't have unnecessary
    ;; type restrictions.
    (equal (logbitp pos i)
           (cond ((zp pos)
                  (bit->bool (logcar i)))
                 (t
                  (logbitp (1- pos) (logcdr i)))))
    :hints(("Goal" :use ((:instance acl2::logbitp*
                          (pos (nfix pos)) (i (ifix i))))))
    :rule-classes ((:definition :clique (logbitp)
                    :controller-alist ((logbitp t t)))))

  (add-to-ruleset ihsext-redefs '(logbitp**))
  (add-to-ruleset ihsext-recursive-redefs '(logbitp**))

  ;; (theory-invariant (not (active-runep '(:definition acl2::logbitp*)))
  ;;                   :key |Use LOGBITP** instead of LOGBITP*|)

  (defun logbitp-ind (pos i)
    (if (zp pos)
        (bit->bool (logcar i))
      (logbitp-ind (1- pos) (logcdr i))))

  (defthmd logbitp-induct
    t
    :rule-classes ((:induction
                    :pattern (logbitp pos i)
                    :scheme (logbitp-ind pos i))))

  (add-to-ruleset ihsext-inductions '(logbitp-induct))

  (local (in-theory (enable* ihsext-recursive-redefs)))

  (defthm logbitp-of-logcons
    (equal (logbitp pos (logcons b i))
           (if (zp pos)
               (bit->bool b)
             (logbitp (1- pos) i)))
    :hints (("goal" :expand ((logbitp pos (logcons b i))))))

  ;; we could write logbitp-of-logcdr, but it would loop with logbitp**.

  (defthm logbitp-0-of-bit
    (implies (bitp b)
             (equal (logbitp 0 b)
                    (bit->bool b))))

  (defthm logbitp-nonzero-of-bit
    (implies (and (bitp b)
                  (not (zp n)))
             (equal (logbitp n b) nil))))

(defsection logbit

  (defthm logbit-to-logbitp
    (equal (logbit n i)
           (bool->bit (logbitp n i)))
    :hints(("Goal" :in-theory (enable logbit bool->bit)))))


(defsection loghead**

  ;; (local (defthm loghead-when-not-integerp
  ;;          (implies (not (integerp i))
  ;;                   (equal (loghead size i)
  ;;                          (loghead size 0)))
  ;;          :hints(("Goal" :in-theory (enable loghead)))))

  ;; (local (defthm loghead-when-not-natp
  ;;          (implies (not (natp size))
  ;;                   (equal (loghead size i)
  ;;                          (loghead 0 i)))
  ;;          :hints(("Goal" :in-theory (enable loghead)))))

  ;; (defthm loghead-of-nfix
  ;;   (equal (loghead (nfix size) i)
  ;;          (loghead size i)))

  ;; (defthm loghead-of-ifix
  ;;   (equal (loghead size (ifix i))
  ;;          (loghead size i)))

  ;; (add-to-ruleset ihsext-basic-thms '(loghead-of-nfix loghead-of-ifix))

  (defthmd loghead**
    (equal (loghead size i)
           (if (zp size)
               0
             (logcons (logcar i)
                      (loghead (1- size) (logcdr i)))))
    :hints (("goal" :use ((:instance acl2::loghead*
                           (size (nfix size))
                           (i (ifix i))))))
    :rule-classes ((:definition
                    :clique (acl2::loghead$inline)
                    :controller-alist ((acl2::loghead$inline t nil)))))

  (add-to-ruleset ihsext-recursive-redefs '(loghead**))
  (add-to-ruleset ihsext-redefs '(loghead**))

  (local (in-theory (enable loghead**)))

  ;; (defthmd loghead-when-zp
  ;;   (implies (zp size)
  ;;            (equal (loghead size i) 0)))

  ;; (defthmd loghead-when-zip
  ;;   (implies (zip i)
  ;;            (equal (loghead size i) 0)))

  ;; (add-to-ruleset ihsext-bad-type-thms '(loghead-when-zp
  ;;                                        loghead-when-zip))

  (defthm loghead-of-0-i
    (equal (loghead 0 i) 0))

  (defthm loghead-of-n-0
    (equal (loghead n 0) 0))

  (defthmd loghead-induct
    t
    :rule-classes ((:induction
                    :pattern (loghead size i)
                    :scheme (logbitp-ind size i))))

  (add-to-ruleset ihsext-inductions '(loghead-induct))


  (defthm logcar-of-loghead
    (implies (not (zp size))
             (equal (logcar (loghead size i))
                    (logcar i)))
    :hints(("Goal" :in-theory (disable (force)))))

  (add-to-ruleset ihsext-basic-thms logcar-of-loghead)

  (defthmd logcdr-of-loghead
    (implies (not (zp size))
             (equal (logcdr (loghead size i))
                    (loghead (1- size) (logcdr i))))
    :hints (("goal" :expand ((loghead size i)))))

  (add-to-ruleset ihsext-basic-thms logcdr-of-loghead)

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (local (in-theory (disable acl2::logbitp-loghead)))

  (defthm logbitp-of-loghead-in-bounds
    (implies (< (nfix pos) (nfix size))
             (equal (logbitp pos (loghead size i))
                    (logbitp pos i))))

  (defthm logbitp-of-loghead-out-of-bounds
    (implies (<= (nfix size) (nfix pos))
             (equal (logbitp pos (loghead size i))
                    nil))
    :hints(("Goal"
            :induct (and (logbitp pos i)
                         (logbitp size i))
            :expand ((:free (x) (logbitp pos x))))))

  (add-to-ruleset ihsext-basic-thms '(logbitp-of-loghead-in-bounds
                                      logbitp-of-loghead-out-of-bounds))

  (defthmd logbitp-of-loghead-split
    (equal (logbitp pos (loghead size i))
           (and (< (nfix pos) (nfix size))
                (logbitp pos i))))

  (add-to-ruleset ihsext-advanced-thms logbitp-of-loghead-split)

  ;; replaces LOGHEAD-LEQ, which forces integerp/natp hyps
  (defthmd loghead-<=-i
    (implies (<= 0 (ifix i))
             (<= (loghead size i) (ifix i)))
    :rule-classes ((:linear :trigger-terms ((loghead size i)))))

  (add-to-ruleset ihsext-bounds-thms loghead-<=-i)

  ;; collectively replace loghead-loghead
  (defthm loghead-of-loghead-1
    (implies (<= (nfix m) (nfix n))
             (equal (loghead m (loghead n x))
                    (loghead m x)))
    :hints (("goal" :in-theory (e/d* (ihsext-recursive-redefs
                                      ihsext-inductions)
                                     (loghead-identity
                                      acl2::loghead-upper-bound
                                      logcdr-<-const))
             :induct (loghead n b)
             :expand ((:free (b) (loghead n b))
                      (:free (a b) (loghead m (logcons a b)))
                      (:free (a b) (lognot (logcons a b)))))))

  (defthm loghead-of-loghead-2
    (implies (<= (nfix n) (nfix m))
             (equal (loghead m (loghead n x))
                    (loghead n x)))
    :hints (("goal" :in-theory (e/d* (ihsext-recursive-redefs
                                      ihsext-inductions)
                                     (loghead-identity
                                      acl2::loghead-upper-bound
                                      logcdr-<-const))
             :induct (loghead n b)
             :expand ((:free (b) (loghead n b))
                      (:free (a b) (loghead m (logcons a b)))
                      (:free (a b) (lognot (logcons a b)))))))

  (add-to-ruleset ihsext-basic-thms '(loghead-of-loghead-1
                                      loghead-of-loghead-2))

  (defthmd loghead-of-loghead-split
    (equal (loghead m (loghead n x))
           (if (<= (nfix n) (nfix m))
               (loghead n x)
             (loghead m x))))

  (add-to-ruleset ihsext-advanced-thms loghead-of-loghead-split)

  ;; Anna (not sure whether this file is a good place to put these theorems)

  ;; [Jared] these seem slightly special purpose, maybe ihs-extensions.lisp would
  ;; be a better home, but this is probably fine too.

  (defthm loghead-of-+-of-loghead-same
    (equal (loghead n (+ (loghead n x) (loghead n y)))
           (loghead n (+ (ifix x) (ifix y))))
    :hints (("goal" :in-theory (enable loghead))))

  (defthm loghead-of-*-of-loghead-same
    (equal (loghead n (* (loghead n x) (loghead n y)))
           (loghead n (* (ifix x) (ifix y))))
    :hints (("goal"
             :in-theory (e/d (loghead
                              acl2::imod
                              acl2::expt2
                              ifix
                              nfix)
                             ;; dumb speed hacking
                             ((:e tau-system)
                              ACL2::EXPT-TYPE-PRESCRIPTION-INTEGERP
                              ACL2::EXPT-TYPE-PRESCRIPTION-POSITIVE
                              ACL2::EXPT-TYPE-PRESCRIPTION-NONZERO
                              ACL2::EXPT-TYPE-PRESCRIPTION-RATIONALP
                              ACL2::EXPT-WITH-VIOLATED-GUARDS
                              acl2::rationalp-mod
                              acl2::mod-type
                              acl2::nfix-when-natp
                              acl2::nfix-when-not-natp
                              default-*-1
                              default-*-2
                              default-<-1
                              default-<-2
                              default-unary-minus
                              acl2::numerator-when-integerp
                              acl2::negative-forward-to-nat-equiv-0
                              ACL2::NOT-INTEGERP-FORWARD-TO-INT-EQUIV-0
                              (:t expt)
                              ACL2::|x < y  =>  0 < -x+y|))))))

(defsection logtail**

  ;; (local (defthm logtail-when-not-integerp
  ;;          (implies (not (integerp i))
  ;;                   (equal (logtail pos i)
  ;;                          (logtail pos 0)))
  ;;          :hints(("Goal" :in-theory (enable logtail)))))

  ;; (local (defthm logtail-when-not-natp
  ;;          (implies (not (natp pos))
  ;;                   (equal (logtail pos i)
  ;;                          (logtail 0 i)))
  ;;          :hints(("Goal" :in-theory (enable logtail)))))

  ;; (defthm logtail-of-nfix
  ;;   (equal (logtail (nfix size) i)
  ;;          (logtail size i)))

  ;; (defthm logtail-of-ifix
  ;;   (equal (logtail size (ifix i))
  ;;          (logtail size i)))

  ;; (add-to-ruleset ihsext-basic-thms '(logtail-of-nfix logtail-of-ifix))

  (defthmd logtail**
    (equal (logtail pos i)
           (if (zp pos)
               (ifix i)
             (logtail (1- pos) (logcdr i))))
    :hints (("goal" :use ((:instance acl2::logtail*
                           (pos (nfix pos))
                           (i (ifix i))))))
    :rule-classes ((:definition
                    :clique (acl2::logtail$inline)
                    :controller-alist ((acl2::logtail$inline t nil)))))

  (add-to-ruleset ihsext-recursive-redefs '(logtail**))
  (add-to-ruleset ihsext-redefs '(logtail**))

  (local (in-theory (e/d* (logtail**) (logtail))))

  ;; (defthmd logtail-when-zp
  ;;   (implies (zp pos)
  ;;            (equal (logtail pos i)
  ;;                   (ifix i))))

  ;; (defthmd logtail-when-zip
  ;;   (implies (zip i)
  ;;            (equal (logtail pos i) 0)))

  ;; (add-to-ruleset ihsext-bad-type-thms '(logtail-when-zp
  ;;                                        logtail-when-zip))


  (defthmd logtail-induct
    t
    :rule-classes ((:induction
                    :pattern (logtail pos i)
                    :scheme (logbitp-ind pos i))))

  (add-to-ruleset ihsext-inductions '(logtail-induct))


  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))


  (defthm logtail-of-0-i
    (equal (logtail 0 i)
           (ifix i)))

  (defthm logtail-of-n-0
    (equal (logtail n 0) 0))

  (defthm logtail-of-n-minus1
    (equal (logtail n -1) -1))

  (add-to-ruleset ihsext-basic-thms '(logtail-of-0-i
                                      logtail-of-n-0
                                      logtail-of-n-minus1))


  (defthm logcdr-of-logtail
    (equal (logcdr (logtail pos i))
           (logtail (1+ (nfix pos)) i))
    :hints (("goal" :expand ((logtail pos i)))))

  (add-to-ruleset ihsext-basic-thms logcdr-of-logtail)

  (defthm logcar-of-logtail
    (equal (logcar (logtail pos i))
           (logbit pos i))
    :hints (("goal" :expand ((logtail pos i)))))

  (add-to-ruleset ihsext-basic-thms logcar-of-logtail)

  (local (in-theory (disable logbitp-logtail)))

  (defthm logbitp-of-logtail
    (equal (logbitp pos (logtail pos2 i))
           (logbitp (+ (nfix pos) (nfix pos2))
                    i)))

  (add-to-ruleset ihsext-basic-thms logbitp-of-logtail)

  (defthm logtail-of-loghead
    (equal (logtail n (loghead m x))
           (loghead (- (nfix m) (nfix n))
                    (logtail n x)))
    :hints (("goal" :induct (and (loghead m x)
                                 (logtail n x))
             :in-theory (disable (force)
                                 loghead-identity
                                 logtail-identity
                                 acl2::logtail-equal-0))))

  (defthm logtail-of-logtail
    (equal (logtail n (logtail m x))
           (logtail (+ (nfix n) (nfix m)) x))

    :hints (("goal" :induct (and (logtail m x)
                                 (logtail n x))
             :in-theory (disable (force)
                                 logtail-identity
                                 acl2::logtail-equal-0))))

  (defthm loghead-1-of-logtail
    ;; Maybe too special-purpose?
    (equal (loghead 1 (logtail n x))
           (logbit n x))
    :hints(("Goal"
            :in-theory (enable logtail** loghead** logbitp**)
            :induct (logtail n x))))

  (defthm logtail-natp
    (implies (natp x)
             (natp (logtail n x)))
    :hints(("Goal" :in-theory (disable (force))))
    :rule-classes :type-prescription))


(defsection integer-length**

  ;; (defthmd integer-length-when-zip
  ;;   (implies (zip i)
  ;;            (equal (integer-length i)
  ;;                   0)))

  ;; (add-to-ruleset ihsext-bad-type-thms '(integer-length-when-zip))

  ;; (defthm integer-length-of-ifix
  ;;   (equal (integer-length (ifix i))
  ;;          (integer-length i)))

  ;; (add-to-ruleset ihsext-basic-thms integer-length-of-ifix)



  ;; Integer-length* is already defined this same way in logops-lemmas;
  ;; we rename it for consistency.
  (defthmd integer-length**
   (equal (integer-length i)
          (cond ((zip i) 0)
                ((equal i -1) 0)
                (t (1+ (integer-length (logcdr i))))))
   :hints (("goal" :by acl2::integer-length*))
   :rule-classes
   ((:definition :clique (integer-length)
     :controller-alist ((integer-length t)))))



  (add-to-ruleset ihsext-redefs '(integer-length**))
  (add-to-ruleset ihsext-recursive-redefs '(integer-length**))

  (local (in-theory (enable integer-length**)))

  (defun integer-length-ind (i)
    (declare (Xargs :measure (integer-length i)))
    (cond ((zip i) 0)
          ((= i -1) 0)
          (t (+ 1 (integer-length-ind (logcdr i))))))

  (defthmd integer-length-induct
    t
    :rule-classes ((:induction
                    :pattern (integer-length i)
                    :scheme (integer-length-ind i))))

  (add-to-ruleset ihsext-inductions '(integer-length-induct))


  (defthm integer-length-of-logtail
    (equal (integer-length (logtail n x))
           (nfix (- (integer-length x) (nfix n))))
    :hints(("Goal" :in-theory (e/d* (logtail**
                                     integer-length**
                                     ihsext-inductions)
                                    ((force))))))

  (defthm integer-length-of-loghead-bound
    (<= (integer-length (loghead n i)) (nfix n))
    :hints(("Goal" :in-theory (e/d* (loghead**
                                     integer-length**
                                     ihsext-inductions)
                                    ((force)))))
    :rule-classes :linear))


(defsection lognot**

  ;; (defthmd lognot-when-zip
  ;;   (implies (zip x)
  ;;            (equal (lognot x) -1)))

  ;; (add-to-ruleset ihsext-bad-type-thms '(lognot-when-zip))

  ;; (local (in-theory (enable* ihsext-bad-type-thms)))

  ;; (defthm lognot-of-ifix
  ;;   (equal (lognot (ifix x))
  ;;          (lognot x)))

  ;; (add-to-ruleset ihsext-basic-thms lognot-of-ifix)
  (defthm lognot-of-lognot
    (equal (lognot (lognot x))
           (ifix x)))


  (defthmd lognot**
    ;; Better than lognot* since there are no hyps.
    ;; Need to case-split manually.
    (equal (lognot i)
           (logcons (b-not (logcar i))
                    (lognot (logcdr i))))
    :hints(("Goal"
            :use ((:instance acl2::lognot*
                   (i (ifix i))))))
    :rule-classes ((:definition :clique (lognot)
                    :controller-alist ((lognot t)))))

  (add-to-ruleset ihsext-redefs '(lognot**))

  (defthm lognot-of-logcons
    (equal (lognot (logcons a b))
           (logcons (b-not a) (lognot b)))
    :hints(("Goal" :in-theory (enable lognot**))))

  (defthmd lognot$
    (equal (lognot i)
           (cond ((zip i) -1)
                 ((= i -1) 0)
                 (t (logcons (b-not (logcar i))
                             (lognot (logcdr i))))))
    :hints (("goal" :use ((:instance acl2::lognot*
                           (i (ifix i))))
             :in-theory (disable lognot acl2::lognot*)))
    :rule-classes ((:definition
                    :clique (lognot)
                    :controller-alist ((lognot t)))))

  (add-to-ruleset ihsext-recursive-redefs '(lognot$))

  ;; (theory-invariant (not (active-runep '(:definition lognot*)))
  ;;                   :key |Use LOGNOT** or LOGNOT$ instead of LOGNOT*|)

  (defthmd lognot-induct
    t
    :rule-classes ((:induction
                    :pattern (lognot i)
                    :scheme (integer-length-ind i))))

  (add-to-ruleset ihsext-inductions '(lognot-induct))

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm lognot-natp
    (implies (negp x)
             (natp (lognot x)))
    :rule-classes :type-prescription)

  (defthm lognot-negp
    (implies (natp x)
             (negp (lognot x)))
    :rule-classes :type-prescription)


  (defthm logcar-of-lognot
    (equal (logcar (lognot x))
           (b-not (logcar x))))

  (defthm logcdr-of-lognot
    (equal (logcdr (lognot x))
           (lognot (logcdr x))))

  (defthm logbitp-of-lognot
    (equal (logbitp a (lognot x))
           (not (logbitp a x)))
    :hints (("goal" :induct (logbitp a x)
             :in-theory (enable b-not))))

  ;; this is pretty weak, but loghead of lognot and lognot of loghead don't
  ;; correspond in the upper bits
  (defthm loghead-cancel-in-lognot
    (implies (<= (nfix n) (nfix m))
             (equal (loghead n (lognot (loghead m x)))
                    (loghead n (lognot x))))
    :hints (("goal" :induct (and (loghead n x)
                                 (loghead m x))
             :in-theory (disable loghead-identity))))

  (defthm logtail-of-lognot
    (equal (logtail n (lognot x))
           (lognot (logtail n x)))
    :hints (("goal" :in-theory (disable logtail-identity
                                        acl2::logtail-equal-0))))


  (add-to-ruleset ihsext-basic-thms '(logcar-of-lognot
                                      logcdr-of-lognot
                                      logbitp-of-lognot
                                      loghead-cancel-in-lognot
                                      logtail-of-lognot))

  (defthm lognot-<-0
    (equal (< (lognot x) 0)
           (not (< (ifix x) 0))))

  (add-to-ruleset ihsext-bounds-thms '(lognot-<-0))

  (defthm lognot-<-const
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (< (lognot i) j)
                    (> (ifix i) (lognot j))))
    :hints(("Goal" :in-theory (enable lognot)
            :use ((:instance acl2::<-on-others
                   (x (lognot i)) (y j))
                  (:instance acl2::<-on-others
                   (x (lognot k)) (y (ifix i)))))))

  (defthm lognot->-const
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (> (lognot i) j)
                    (< (ifix i) (lognot j))))
    :hints(("Goal" :in-theory (enable lognot)
            :use ((:instance acl2::<-on-others
                   (y (lognot i)) (x j))
                  (:instance acl2::<-on-others
                   (y (lognot j)) (x (ifix i)))))))

  (defthm lognot-equal-const
    (implies (and (syntaxp (quotep j))
                  (integerp j))
             (equal (equal (lognot i) j)
                    (equal (ifix i) (lognot j))))
    :hints(("Goal" :in-theory (enable lognot))))

  (defthm integer-length-of-lognot
    (equal (integer-length (lognot x))
           (integer-length x))
    :hints(("Goal" :in-theory (enable* ihsext-inductions
                                       ihsext-recursive-redefs))))

  (add-to-ruleset ihsext-basic-thms '(lognot-<-const
                                      lognot->-const
                                      lognot-equal-const
                                      integer-length-of-lognot)))



(defun logcdr-3-ind (a b c)
  (declare (xargs :measure (+ (integer-length a)
                              (integer-length b)
                              (integer-length c))
                  :hints(("Goal" :in-theory (enable integer-length**)))))
  (if (and (or (zip a) (= a -1))
           (or (zip b) (= b -1))
           (or (zip c) (= c -1)))
      (list a b c)
    (logcdr-3-ind (logcdr a) (logcdr b) (logcdr c))))


(defsection logand**

  (local (in-theory (enable logand)))

  ;; (defthmd logand-when-zip
  ;;   (implies (or (zip i) (zip j))
  ;;            (equal (logand i j) 0)))

  ;; (add-to-ruleset ihsext-bad-type-thms '(logand-when-zip))

  ;; (defthm logand-of-ifix-1
  ;;   (equal (logand (ifix a) b)
  ;;          (logand a b)))

  ;; (defthm logand-of-ifix-2
  ;;   (equal (logand b (ifix a))
  ;;          (logand b a)))

  ;; (add-to-ruleset ihsext-basic-thms '(logand-of-ifix-1 logand-of-ifix-2))

  (local (in-theory (enable* ihsext-bad-type-thms)))
  (local (in-theory (disable logand)))

  (defthmd logand**
    ;; Better than logand* since there are no hyps; but must case-split manually.
    (equal (logand i j)
           (logcons (b-and (logcar i) (logcar j))
                    (logand (logcdr i) (logcdr j))))
    :hints(("Goal" :use ((:instance acl2::logand*
                          (i (ifix i)) (j (ifix j))))))
    :rule-classes
    ((:definition :clique (binary-logand)
      :controller-alist ((binary-logand t t)))))

  (add-to-ruleset ihsext-redefs '(logand**))

  (defthm logand-of-logcons-left
    (equal (logand (logcons a b) c)
           (logcons (b-and a (logcar c))
                    (logand b (logcdr c))))
    :hints(("Goal" :in-theory (enable logand**))))

  (defthm logand-of-logcons-right
    (equal (logand c (logcons a b))
           (logcons (b-and a (logcar c))
                    (logand (logcdr c) b)))
    :hints(("Goal" :in-theory (enable logand**))))

  (defthmd logand$
    ;; Bozo maybe we should have a version that only terminates based on one
    ;; input or the other? maybe better case-splitting/induction schemes
    (equal (logand i j)
           (cond ((or (zip i) (zip j)) 0)
                 ((= i -1) j)
                 ((= j -1) i)
                 (t (logcons (b-and (logcar i) (logcar j))
                             (logand (logcdr i) (logcdr j))))))
    :hints (("goal" :in-theory (disable logcons logcar logcdr
                                        acl2::logand* logand (force))
             :use ((:instance acl2::logand*
                    (i (ifix i)) (j (ifix j))))))
    :rule-classes ((:definition
                    :clique (binary-logand)
                    :controller-alist ((binary-logand t t)))))

  (add-to-ruleset ihsext-recursive-redefs '(logand$))

  ;; (theory-invariant (not (active-runep '(:definition logand*)))
  ;;                   :key |Use LOGAND** or LOGAND$ instead of LOGAND*|)

  (local (in-theory (enable integer-length**)))

  (defun logand-ind (i j)
    (declare (xargs :measure (integer-length i)))
    (cond ((or (zip i) (zip j)) 0)
          ((= i -1) j)
          ((= j -1) i)
          (t (logcons (b-and (logcar i) (logcar j))
                      (logand-ind (logcdr i) (logcdr j))))))

  (defthmd logand-induct
    t
    :rule-classes ((:induction
                    :pattern (logand i j)
                    :scheme (logand-ind i j))))

  (add-to-ruleset ihsext-inductions '(logand-induct))

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm logcar-of-logand
    (equal (logcar (logand x y))
           (b-and (logcar x) (logcar y)))
    :hints (("Goal" :expand (logand x y))))


  (defthm logcdr-of-logand
    (equal (logcdr (logand x y))
           (logand (logcdr x) (logcdr y))))

  (defthm logbitp-of-logand
    (equal (logbitp a (logand x y))
           (bit->bool (b-and (logbit a x)
                             (logbit a y))))
    :hints(("Goal" :induct (and (logbitp a x)
                                (logbitp a y))
            :in-theory (enable bool->bit b-and))))

  (defthm loghead-of-logand
    (equal (loghead a (logand x y))
           (logand (loghead a x)
                   (loghead a y)))
    :hints(("Goal" :in-theory (disable loghead-identity))))

  (defthm logtail-of-logand
    (equal (logtail a (logand x y))
           (logand (logtail a x)
                   (logtail a y)))
    :hints(("Goal" :in-theory (disable logtail-identity
                                       acl2::logtail-equal-0))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-logand
                                      logcdr-of-logand
                                      logbitp-of-logand
                                      loghead-of-logand))

  (defthm logand-<-0-linear
    (implies (and (< (ifix x) 0)
                  (< (ifix y) 0))
             (< (logand x y) 0))
    :rule-classes :linear)

  (defthm logand->=-0-linear-1
    (implies (<= 0 (ifix x))
             (<= 0 (logand x y)))
    :rule-classes :linear)

  (defthm logand->=-0-linear-2
    (implies (<= 0 (ifix y))
             (<= 0 (logand x y)))
    :rule-classes :linear)

  (add-to-ruleset ihsext-bounds-thms '(logand-<-0-linear
                                       logand->=-0-linear-1
                                       logand->=-0-linear-2))

  (defthmd logand-<-0
    (equal (< (logand x y) 0)
           (and (< (ifix x) 0)
                (< (ifix y) 0))))

  (add-to-ruleset ihsext-advanced-thms '(logand-<-0))

  (defthm upper-bound-of-logand
    (implies (>= i 0)
             (<= (logand i j) i))
    :hints(("Goal" :use ((:instance logand-upper-bound))))
    :rule-classes ((:linear :corollary (implies (>= i 0) (<= (logand i j) i)))
                   (:linear :corollary (implies (>= i 0) (<= (logand j i) i)))))

  (add-to-ruleset ihsext-bounds-thms '(upper-bound-of-logand))


  (defthm logand-x-lognot-x
    (equal (logand x (lognot x)) 0)
    :rule-classes (:rewrite
                   (:rewrite :corollary
                    (equal (logand (lognot x) x) 0))))

  (defthm unsigned-byte-p-of-logand-1
    (implies (unsigned-byte-p n x)
             (unsigned-byte-p n (logand x y)))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm unsigned-byte-p-of-logand-2
    (implies (unsigned-byte-p n y)
             (unsigned-byte-p n (logand x y)))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm logand-natp-type-1
    (implies (or (not (integerp x))
                 (<= 0 x))
             (natp (logand x y)))
    :rule-classes :type-prescription)

  (defthm logand-natp-type-2
    (implies (or (not (integerp y))
                 (<= 0 y))
             (natp (logand x y)))
    :rule-classes :type-prescription)

  (defthm associativity-of-logand
    (equal (logand (logand a b) c)
           (logand a b c))
    :hints (("goal" :induct (logcdr-3-ind a b c)
             :in-theory (e/d (logand**)
                             (acl2::zip-open
                              logand$)))))

  (defthm commutativity-2-of-logand
    (equal (logand a b c)
           (logand b a c))
    :hints (("goal" :induct (logcdr-3-ind a b c)
             :in-theory (e/d (logand**)
                             (acl2::zip-open
                              logand$)))))

  (defthm logand-fold-consts
    (implies (syntaxp (and (quotep a) (quotep b)))
             (equal (logand a b c)
                    (logand (logand a b) c))))

  (defthm logand-of-self
    (equal (logand x x)
           (ifix x)))

  (defthm logand-of-logand-self-1
    (equal (logand x (logand x y))
           (logand x y)))

  (defthm logand-of-logand-self-2
    (equal (logand x (logand y x))
           (logand x y))))



(defsection logior**

  (local (in-theory (enable* logior
                             ihsext-recursive-redefs
                             ihsext-inductions
                             ihsext-advanced-thms)))

  ;; (defthm logior-of-ifix-1
  ;;   (equal (logior (ifix a) b)
  ;;          (logior a b)))

  ;; (defthm logior-of-ifix-2
  ;;   (equal (logior b (ifix a))
  ;;          (logior b a)))

  ;; (add-to-ruleset ihsext-basic-thms '(logior-of-ifix-1 logior-of-ifix-2))



  (defthmd logior**
    ;; Better than logand* since there are no hyps.
    (equal (logior i j)
           (logcons (b-ior (logcar i) (logcar j))
                    (logior (logcdr i) (logcdr j))))
    :rule-classes
    ((:definition :clique (binary-logior)
      :controller-alist ((binary-logior t t)))))

  (add-to-ruleset ihsext-redefs '(logior**))

  (defthm logior-of-logcons-left
    (equal (logior (logcons a b) c)
           (logcons (b-ior a (logcar c))
                    (logior b (logcdr c))))
    :hints(("Goal" :in-theory (enable logior**
                                      b-not b-and b-ior))))

  (defthm logior-of-logcons-right
    (equal (logior c (logcons a b))
           (logcons (b-ior a (logcar c))
                    (logior (logcdr c) b)))
    :hints(("Goal" :in-theory (enable logior**
                                      b-not b-and b-ior))))

  (defthmd logior$
    ;; Bozo maybe we should have a version that only terminates based on one
    ;; input or the other? maybe better case-splitting/induction schemes
    (equal (logior i j)
           (cond ((zip i) (ifix j))
                 ((zip j) i)
                 ((or (= j -1) (= i -1)) -1)
                 (t (logcons (b-ior (logcar i) (logcar j))
                             (logior (logcdr i) (logcdr j))))))
    :rule-classes
    ((:definition :clique (binary-logior)
      :controller-alist ((binary-logior t t)))))

  (add-to-ruleset ihsext-recursive-redefs '(logior$))

  ;; (theory-invariant (not (active-runep '(:definition logior*)))
  ;;                   :key |Use LOGIOR** or LOGIOR$ instead of LOGIOR*|)

  ;; LOGAND-IND is the same induction scheme.
  (defthmd logior-induct
    t
    :rule-classes ((:induction
                    :pattern (logior i j)
                    :scheme (logand-ind i j))))

  (add-to-ruleset ihsext-inductions '(logior-induct))

  (local (in-theory (enable* ihsext-bad-type-thms
                             logior-induct
                             logior$)))
  (local (in-theory (disable logior)))

  (defthm logcar-of-logior
    (equal (logcar (logior x y))
           (b-ior (logcar x) (logcar y)))
    :hints (("goal" :expand (logior x y))))


  (defthm logcdr-of-logior
    (equal (logcdr (logior x y))
           (logior (logcdr x) (logcdr y))))

  (defthm logbitp-of-logior
    (equal (logbitp a (logior x y))
           (bit->bool (b-ior (logbit a x)
                             (logbit a y))))
    :hints(("Goal" :induct (and (logbitp a x)
                                (logbitp a y))
            :in-theory (enable bool->bit b-ior))))

  (defthm loghead-of-logior
    (equal (loghead a (logior x y))
           (logior (loghead a x)
                   (loghead a y)))
    :hints(("Goal" :in-theory (disable loghead-identity))))

  (defthm logtail-of-logior
    (equal (logtail a (logior x y))
           (logior (logtail a x)
                   (logtail a y)))
    :hints(("Goal" :in-theory (disable logtail-identity
                                       acl2::logtail-equal-0))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-logior
                                      logcdr-of-logior
                                      logbitp-of-logior
                                      loghead-of-logior
                                      logtail-of-logior))

  (defthm logior-<-0-linear-1
    (implies (< (ifix x) 0)
             (< (logior x y) 0))
    :rule-classes :linear)

  (defthm logior-<-0-linear-2
    (implies (< (ifix y) 0)
             (< (logior x y) 0))
    :rule-classes :linear)

  (defthm logior->=-0-linear
    (implies (and (<= 0 (ifix x))
                  (<= 0 (ifix y)))
             (<= 0 (logior x y)))
    :rule-classes :linear)

  (add-to-ruleset ihsext-bounds-thms '(logior-<-0-linear-1
                                       logior-<-0-linear-2
                                       logior->=-0-linear))

  (defthmd logior-<-0
    (equal (< (logior x y) 0)
           (or (< (ifix x) 0)
               (< (ifix y) 0))))

  (add-to-ruleset ihsext-advanced-thms '(logior-<-0))

  (local (in-theory (disable acl2::logior-=-0)))

  (defthm logior-equal-0-forward
    (implies (equal (logior i j) 0)
             (and (zip i) (zip j)))
    :rule-classes :forward-chaining)

  (defthm logior-nonzero-1
    (implies (not (zip i))
             (not (equal (logior i j) 0))))

  (defthm logior-nonzero-2
    (implies (not (zip j))
             (not (equal (logior i j) 0))))

  (add-to-ruleset ihsext-basic-thms '(logior-equal-0-forward
                                      logior-nonzero-1
                                      logior-nonzero-2))

  (defthm logior-equal-0
    (equal (equal (logior i j) 0)
           (and (equal (ifix i) 0)
                (equal (ifix j) 0))))

  (add-to-ruleset ihsext-advanced-thms '(logior-equal-0))

  (defthm logior-x-lognot-x
    (equal (logior x (lognot x)) -1)
    :rule-classes (:rewrite
                   (:rewrite :corollary
                    (equal (logior (lognot x) x) -1))))

  (defthm unsigned-byte-p-of-logior
    (implies (and (unsigned-byte-p n i)
                  (unsigned-byte-p n j))
             (unsigned-byte-p n (logior i j))))

  (defthm logior-natp-type
    (implies (and (or (not (integerp a))
                      (<= 0 a))
                  (or (not (integerp b))
                      (<= 0 b)))
             (natp (logior a b)))
    :rule-classes :type-prescription)


  (defthm associativity-of-logior
    (equal (logior (logior a b) c)
           (logior a b c))
    :hints (("goal" :induct (logcdr-3-ind a b c)
             :in-theory (e/d (logior**)
                             (acl2::zip-open
                              logior$)))))

  (defthm commutativity-2-of-logior
    (equal (logior a b c)
           (logior b a c))
    :hints (("goal" :induct (logcdr-3-ind a b c)
             :in-theory (e/d (logior**)
                             (acl2::zip-open
                              logior$)))))

  (defthm logior-fold-consts
    (implies (syntaxp (and (quotep a) (quotep b)))
             (equal (logior a b c)
                    (logior (logior a b) c))))

  (defthm logior-of-self
    (equal (logior x x)
           (ifix x)))

  (defthm logior-of-logior-self
    (equal (logior x (logior x y))
           (logior x y)))

  (defthm logior-of-logior-self-2
    (equal (logior x (logior y x))
           (logior x y)))

  (defthm logior-of-logand-self
    (equal (logior b (logand a b))
           (ifix b)))

  (defthm logand-of-logior-self
    (equal (logand b (logior a b))
           (ifix b))))


(defsection logxor**

  (local (in-theory (enable* logxor logeqv logorc1
                             ihsext-inductions
                             ihsext-advanced-thms)))


  (defthmd logxor**
    ;; Better than logxor* since there are no hyps.
    ;; Needs manual case-splitting.
    (equal (logxor i j)
           (logcons (b-xor (logcar i) (logcar j))
                    (logxor (logcdr i) (logcdr j))))
    :rule-classes
    ((:definition :clique (binary-logxor)
                  :controller-alist ((binary-logxor t t)))))

  (add-to-ruleset ihsext-redefs '(logxor**))

  (defthm logxor-of-logcons-left
    (equal (logxor (logcons a b) c)
           (logcons (b-xor a (logcar c))
                    (logxor b (logcdr c))))
    :hints(("Goal" :in-theory (enable logxor**
                                      b-not b-and b-xor))))

  (defthm logxor-of-logcons-right
    (equal (logxor c (logcons a b))
           (logcons (b-xor a (logcar c))
                    (logxor b (logcdr c))))
    :hints(("Goal" :in-theory (enable logxor**
                                      b-not b-and b-xor))))

  (local (in-theory (enable* ihsext-recursive-redefs)))
  (local (in-theory (disable bfix zbp)))

  (defthmd logxor$
    ;; Better than logxor* since there are no hyps.

    ;; Bozo maybe we should have a version that only terminates based on one
    ;; input or the other? maybe better case-splitting/induction schemes
    (equal (logxor i j)
           (cond ((zip i) (ifix j))
                 ((zip j) (ifix i))
                 ((= i -1) (lognot j))
                 ((= j -1) (lognot i))
                 (t (logcons (b-xor (logcar i) (logcar j))
                             (logxor (logcdr i) (logcdr j))))))
    :rule-classes
    ((:definition :clique (binary-logxor)
                  :controller-alist ((binary-logxor t t)))))

  ;; (defthm logxor-of-ifix-1
  ;;   (equal (logxor (ifix a) b)
  ;;          (logxor a b)))

  ;; (defthm logxor-of-ifix-2
  ;;   (equal (logxor b (ifix a))
  ;;          (logxor b a)))

  ;; (add-to-ruleset ihsext-basic-thms '(logxor-of-ifix-1 logxor-of-ifix-2))


  (add-to-ruleset ihsext-recursive-redefs '(logxor$))

  ;; (theory-invariant (not (active-runep '(:definition logxor*)))
  ;;                   :key |Use LOGXOR** or LOGXOR$ instead of LOGXOR*|)

  (defthm logxor-induct
    t
    :rule-classes ((:induction
                    :pattern (logxor i j)
                    :scheme (logand-ind i j))))

  (add-to-ruleset ihsext-inductions '(logxor-induct))

  (local (in-theory (enable* ihsext-bad-type-thms
                             logxor-induct
                             logxor$)))
  (local (in-theory (disable logxor)))

  (defthm logcar-of-logxor
    (equal (logcar (logxor x y))
           (b-xor (logcar x) (logcar y)))
    :hints (("goal" :expand (logxor x y))))


  (defthm logcdr-of-logxor
    (equal (logcdr (logxor x y))
           (logxor (logcdr x) (logcdr y))))

  (defthm logbitp-of-logxor
    (equal (logbitp a (logxor x y))
           (bit->bool (b-xor (logbit a x)
                             (logbit a y))))
    :hints (("goal" :induct (and (logbitp a x)
                                 (logbitp a y))
             :in-theory (enable b-xor))))

  (defthm loghead-of-logxor
    (equal (loghead a (logxor x y))
           (logxor (loghead a x)
                   (loghead a y)))
    :hints (("goal" :induct (and (loghead a x)
                                 (loghead a y))
             :in-theory (disable loghead-identity))))

  (defthm logtail-of-logxor
    (equal (logtail a (logxor x y))
           (logxor (logtail a x)
                   (logtail a y)))
    :hints (("goal" :induct (and (logtail a x)
                                 (logtail a y))
             :in-theory (disable logtail-identity
                                 acl2::logtail-equal-0))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-logxor
                                      logcdr-of-logxor
                                      logbitp-of-logxor
                                      loghead-of-logxor
                                      logtail-of-logxor))

  ;; (defthmd logxor-commutes
  ;;   (equal (logxor a b)
  ;;          (logxor b a)))

  ;; (add-to-ruleset ihsext-advanced-thms '(logxor-commutes))

  (defthm logxor-<-0-linear-1
    (implies (and (< (ifix x) 0)
                  (<= 0 (ifix y)))
             (< (logxor x y) 0))
    :rule-classes :linear)

  (defthm logxor-<-0-linear-2
    (implies (and (< (ifix y) 0)
                  (<= 0 (ifix x)))
             (< (logxor x y) 0))
    :rule-classes :linear)

  (defthm logxor->=-0-linear-1
    (implies (and (< (ifix x) 0)
                  (< (ifix y) 0))
             (<= 0 (logxor x y)))
    :rule-classes :linear)

  (defthm logxor->=-0-linear-2
    (implies (and (<= 0 (ifix x))
                  (<= 0 (ifix y)))
             (<= 0 (logxor x y)))
    :rule-classes :linear)

  (add-to-ruleset ihsext-bounds-thms '(logxor-<-0-linear-1
                                       logxor-<-0-linear-2
                                       logxor->=-0-linear-1
                                       logxor->=-0-linear-2))


  (defthmd logxor-<-0
    (equal (< (logxor x y) 0)
           (xor (< (ifix x) 0)
                (< (ifix y) 0))))

  (add-to-ruleset ihsext-bounds-thms '(logxor-<-0))

  (defthm logxor-of-self
    (equal (logxor x x)
           0)
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm logxor-equal-0
    (equal (equal (logxor x y) 0)
           (equal (ifix x) (ifix y)))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm logxor-equal-minus1
    (equal (equal (logxor x y) -1)
           (equal (ifix x) (lognot y))))

  (add-to-ruleset ihsext-basic-thms '(logxor-equal-0
                                      logxor-equal-minus1))

  (defthm logxor-natp-type-1
    (implies (and (or (not (integerp x))
                      (<= 0 x))
                  (or (not (integerp y))
                      (<= 0 y)))
             (natp (logxor x y)))
    :rule-classes :type-prescription)

  (defthm logxor-natp-type-2
    (implies (and (integerp x)
                  (< x 0)
                  (integerp y)
                  (< y 0))
             (natp (logxor x y)))
    :rule-classes :type-prescription)

  (defthm associativity-of-logxor
    (equal (logxor (logxor a b) c)
           (logxor a b c))
    :hints (("goal" :induct (logcdr-3-ind a b c)
             :in-theory (e/d (logxor** b-xor)
                             (acl2::zip-open logxor$)))))

  (defthm commutativity-2-of-logxor
    (equal (logxor a b c)
           (logxor b a c))
    :hints (("goal" :induct (logcdr-3-ind a b c)
             :in-theory (e/d (logxor** b-xor)
                             (acl2::zip-open logxor$)))))

  (defthm logxor-fold-consts
    (implies (syntaxp (and (quotep a) (quotep b)))
             (equal (logxor a b c)
                    (logxor (logxor a b) c)))))



(defsection ash**

  ;; This is the same as the existing ash*, renamed for consistency.
  (defthmd ash**
    (equal (ash i count)
           (cond ((zip count) (ifix i))
                 ((< count 0) (ash (logcdr i)    (1+ count)))
                 (t           (logcons 0 (ash i (1- count))))))
    :hints (("goal" :by acl2::ash*))
    :rule-classes
    ((:definition :clique (ash)
      :controller-alist ((ash nil t)))))


  (add-to-ruleset ihsext-redefs ash**)
  (add-to-ruleset ihsext-recursive-redefs ash**)

  (defun ash**-ind (i count)
    (declare (xargs :measure (abs (ifix count))))
    (cond ((zip count) (ifix i))
          ((< count 0)
           (ash**-ind (logcdr i) (1+ count)))
          (t (logcons 0 (ash**-ind i (1- count))))))


  (defthmd ash**-induct
    t
    :rule-classes ((:induction
                    :pattern (ash i count)
                    :scheme (ash**-ind i count))))

  (add-to-ruleset ihsext-inductions '(ash**-induct))

  (local (in-theory (enable* ash**
                             ihsext-recursive-redefs
                             ihsext-inductions
                             ihsext-advanced-thms)))


  ;; (defthm ash-of-ifix-1
  ;;   (equal (ash (ifix a) b)
  ;;          (ash a b)))

  ;; (defthm ash-of-ifix-2
  ;;   (equal (ash b (ifix a))
  ;;          (ash b a)))

  ;; (add-to-ruleset ihsext-basic-thms '(ash-of-ifix-1 ash-of-ifix-2))


  (local (defthm ash-of-logcons-0
           (implies (<= 0 (ifix count))
                    (equal (ash (logcons 0 i) count)
                           (logcons 0 (ash i count))))
           :hints (("goal" :expand ((ash i count))))))

  ;; (local (defthm logcdr-of-ash
  ;;          (implies (<= (ifix count) 0)
  ;;                   (equal (logcdr (ash i count))
  ;;                          (ash (logcdr i) count)))
  ;;          :hints (("goal" :expand ((ash i count))))))

  ;; (defthmd ash$$
  ;;   (equal (ash i count)
  ;;          (cond ((zip count) (ifix i))
  ;;                ((< count 0) (logcdr    (ash i (1+ count))))
  ;;                (t           (logcons 0 (ash i (1- count))))))
  ;;   :hints (("goal" :expand ((ash i count))))
  ;;   :rule-classes
  ;;   ((:definition :clique (ash)
  ;;     :controller-alist ((ash nil t)))))

  ;; (defthmd ash**
  ;;   (equal (ash i count)
  ;;          (cond ((zip count) (ifix i))
  ;;                ((< count 0) (ash (logcdr i)    (1+ count)))
  ;;                (t           (ash (logcons 0 i) (1- count)))))
  ;;   :rule-classes
  ;;   ((:definition :clique (ash)
  ;;     :controller-alist ((ash nil t)))))

  ;; (add-to-ruleset ihsext-recursive-redefs '(ash**))
  ;; (add-to-ruleset ihsext-redefs '(ash**))

  ;; (defun ash-ind (i count)
  ;;   (declare (xargs :measure (abs (ifix count))))
  ;;   (cond ((zip count) (ifix i))
  ;;         ((< count 0)
  ;;          (ash-ind (logcdr i) (1+ count)))
  ;;         (t (logcons 0 (ash-ind i (1- count))))))

  ;; (defthmd ash-induct
  ;;   t
  ;;   :rule-classes ((:induction
  ;;                   :pattern (ash i count)
  ;;                   :scheme (ash-ind i count))))



  ;; (defun ash$$-ind (i count)
  ;;   (cond ((zip count) (ifix i))
  ;;         ((< count 0) (logcdr    (ash$$-ind i (1+ count))))
  ;;         (t           (logcons 0 (ash$$-ind i (1- count))))))

  ;; (defthmd ash$$-induct
  ;;   t
  ;;   :rule-classes ((:induction
  ;;                   :pattern (ash i count)
  ;;                   :scheme (ash$$-ind i count))))

  ;; (defun ash**-ind (i count)
  ;;   (cond ((zip count) (ifix i))
  ;;         ((< count 0) (ash**-ind (logcdr i)    (1+ count)))
  ;;         (t           (ash**-ind (logcons 0 i) (1- count)))))


  ;; (in-theory (disable ash))

  (local (in-theory (enable* ihsext-inductions
                             ihsext-recursive-redefs)))

  (defthm ash-of-0-c
    (equal (ash 0 count) 0))

  (defthm ash-of-n-0
    (equal (ash n 0) (ifix n)))


  ;; (defthmd ash-when-zip-i
  ;;   (implies (zip i)
  ;;            (equal (ash i count) 0)))

  (add-to-ruleset ihsext-basic-thms '(ash-of-0-c
                                      ash-of-n-0))

  ;; (defthmd ash-when-zip-count
  ;;   (implies (zip count)
  ;;            (equal (ash i count)
  ;;                   (ifix i))))

  ;; (add-to-ruleset ihsext-bad-type-thms '(ash-when-zip-count))

  (defthm logcar-of-left-shift
    (implies (< 0 (ifix count))
             (equal (logcar (ash i count)) 0)))

  (defthm right-shift-to-logtail
    (implies (<= (ifix count) 0)
             (equal (ash i count)
                    (logtail (- count) i))))


  (add-to-ruleset ihsext-basic-thms '(logcar-of-left-shift
                                      right-shift-to-logtail))

  (local (in-theory (enable logcar-of-left-shift)))

  (defthmd logcdr-of-ash
    (equal (logcdr (ash i count))
           (ash i (1- (ifix count)))))

  (defthm logcdr-of-left-shift
    ;; this hyp isn't necessary, but this rule could loop with the def of ash otherwise
    (implies (< 0 (ifix count))
             (equal (logcdr (ash i count))
                    (ash i (1- (ifix count)))))
    :hints(("Goal" :in-theory (enable logcdr-of-ash))))

  (defun logbitp-of-ash-ind (pos i count)
    (declare (xargs :measure (abs (ifix count))))
    (cond ((or (zp pos)
               (zip count))
           (if (zip count)
               (list pos i)
             (list i pos)))
          ((< count 0)
           (logbitp-of-ash-ind pos (logcdr i) (1+ count)))
          (t (logbitp-of-ash-ind (1- pos) i (1- count)))))

  (defthmd logbitp-of-ash-split
    (equal (logbitp pos (ash i count))
           (and (<= (ifix count) (nfix pos))
                (logbitp (- (nfix pos) (ifix count)) i)))
    :hints (("goal" :induct (logbitp-of-ash-ind pos i count)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((<= (ifix count) 0))))))

  (add-to-ruleset ihsext-advanced-thms logbitp-of-ash-split)


  (defthm logbitp-of-ash-in-range
    (implies (<= (ifix count) (nfix pos))
             (equal (logbitp pos (ash i count))
                    (logbitp (- (nfix pos) (ifix count)) i)))
    :hints(("Goal" :in-theory (enable logbitp-of-ash-split))))

  (defthm logbitp-of-ash-out-of-range
    (implies (< (nfix pos) (ifix count))
             (equal (logbitp pos (ash i count))
                    nil))
    :hints(("Goal" :in-theory (enable logbitp-of-ash-split))))

  (add-to-ruleset ihsext-basic-thms '(logcdr-of-left-shift
                                      logbitp-of-ash-in-range
                                      logbitp-of-ash-out-of-range))


  (defthm ash-<-0
    (equal (< (ash i count) 0)
           (< (ifix i) 0))
    :hints (("goal" :induct t
             :in-theory (disable (force)))
            (and stable-under-simplificationp
                 '(:cases ((integerp i))))))

  (defthmd ash-<-0-linear
    (implies (and (integerp i)
                  (< i 0))
             (< (ash i count) 0))
    :rule-classes :linear)

  (defthmd ash->-0-linear
    (implies (and (integerp i)
                  (> i 0)
                  (<= 0 count))
             (> (ash i count) 0))
    :rule-classes :linear)

  (defthmd ash->=-0-linear
    (implies (or (not (integerp i))
                 (<= 0 i))
             (<= 0 (ash i count)))
    :rule-classes :linear)

  (add-to-ruleset ihsext-bounds-thms '(ash-<-0
                                       ash-<-0-linear
                                       ash->-0-linear
                                       ash->=-0-linear))


  (encapsulate nil
    (local
     (progn
       (defthm ash-of-ash-1
         (implies (and (<= 0 (ifix sh1))
                       (<= 0 (ifix sh2)))
                  (equal (ash (ash x sh1) sh2)
                         (ash x (+ (ifix sh1) (ifix sh2)))))
         :hints (("goal" :induct (ash x sh1)
                  :in-theory (e/d (logcdr-of-ash)
                                  ((force))))))

       (defthm ash-of-ash-2
         (implies (and (<= (ifix sh1) 0)
                       (<= (ifix sh2) 0))
                  (equal (ash (ash x sh1) sh2)
                         (ash x (+ (ifix sh1) (ifix sh2)))))
         :hints (("goal" :induct (ash x sh1))
                 (and stable-under-simplificationp
                      '(:cases ((= 0 (ifix sh2)))))))

       (defthm ash-of-ash-3
         (implies (<= 0 (ifix sh1))
                  (equal (ash (ash x sh1) (+ (- (ifix sh1)) (ifix sh)))
                         (ash x sh)))
         :hints (("goal" :induct (ash x sh1))
                 (and stable-under-simplificationp
                      '(:cases ((< 0 (+ (- (ifix sh1)) (ifix sh)))
                                (< (+ (- (ifix sh1)) (ifix sh)) 0))))))))

    (defthm ash-of-ash
      (implies (or (<= 0 (ifix sh1))
                   (<= (ifix sh2) 0))
               (equal (ash (ash x sh1) sh2)
                      (ash x (+ (ifix sh1) (ifix sh2)))))
      :hints ('(:cases ((< 0 (ifix sh1))
                        (= 0 (ifix sh1))
                        (> 0 (ifix sh1))))
              '(:cases ((< (ifix sh2) 0)
                        (= (ifix sh2) 0)
                        (> (ifix sh2) 0)))
              (and stable-under-simplificationp
                   '(:use ((:instance ash-of-ash-3
                            (sh (+ sh1 sh2)))))))))

  (defthm logtail-of-ash
    (equal (logtail sh2 (ash x sh1))
           (ash x (+ (ifix sh1) (- (nfix sh2)))))
    :hints (("goal" :use ((:instance ash-of-ash
                           (sh2 (- (nfix sh2)))))
             :in-theory (disable ash-of-ash)
             :do-not-induct t)))

  (add-to-ruleset ihsext-basic-thms ash-of-ash)

  (defthm ash-natp-type
    (implies (or (not (integerp x))
                 (<= 0 x))
             (natp (ash x y)))
    :rule-classes :type-prescription)

  (defthm loghead-of-ash-same
    (implies (natp n)
             (equal (loghead n (ash x n))
                    0))
    :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                     ihsext-recursive-redefs)))))

  (local (defun ind (n m x)
           (cond ((zip m) (list n x))
                 ((< m 0) (ind (1+ n) (1+ m) x))
                 (t (ind (1- n) (1- m) x)))))

  (defthmd loghead-of-ash
    (equal (loghead n (ash x m))
           (ash (loghead (nfix (- (nfix n) (ifix m))) x) m))
    :hints(("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                    ihsext-inductions
                                    nfix ifix zip
                                    ash**)
                                   (bitp
                                    loghead-identity
                                    logcdr-of-ash))
            :induct (ind n m x)
            :do-not-induct t)))

  (add-to-ruleset ihsext-advanced-thms loghead-of-ash)

  (defthm integer-length-of-ash
    (implies (not (zip n))
             (equal (integer-length (ash n m))
                    (nfix (+ (ifix m) (integer-length n)))))
    :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                       ihsext-inductions nfix ifix)))))

(defsection expt

  (defthmd expt-2-is-ash
    (implies (natp n)
             (equal (expt 2 n)
                    (ash 1 n)))
    :hints(("Goal" :in-theory (enable ash floor))))

  (defthmd ash-1-removal
    (equal (ash 1 n)
           (if (integerp n)
               (if (<= 0 n)
                   (expt 2 n)
                 0)
             1))
    :hints(("Goal" :in-theory (e/d (expt-2-is-ash ash**)
                                   (right-shift-to-logtail)))))


  (defthm expt-of-ifix
    (equal (expt r (ifix i))
           (expt r i))
    :hints(("Goal" :in-theory (enable expt))))

  (add-to-ruleset ihsext-arithmetic '(expt-2-is-ash))
  (add-to-ruleset ihsext-basic-thms expt-of-ifix)

  (defthmd ash-is-expt-*-x
    (implies (natp n)
             (equal (ash x n)
                    (* (ifix x) (expt 2 n))))
    :hints (("goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs)
             :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable expt logcons))))))




(defsection unsigned-byte-p**

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (local (in-theory (enable expt-2-is-ash)))


  (defthm unsigned-byte-p-of-n-0
    (equal (unsigned-byte-p n 0)
           (natp n)))

  (defthm unsigned-byte-p-of-0-x
    (equal (unsigned-byte-p 0 x)
           (equal x 0)))

  (defthmd unsigned-byte-p**
    (equal (unsigned-byte-p bits x)
           (and (integerp x)
                (natp bits)
                (if (zp bits)
                    (equal x 0)
                  (unsigned-byte-p (1- bits)
                                   (logcdr x)))))
    :rule-classes ((:definition
                    :clique (unsigned-byte-p)
                    :controller-alist ((unsigned-byte-p t t)))))

  (local (in-theory (enable unsigned-byte-p**)))
  (local (in-theory (disable unsigned-byte-p)))

  (add-to-ruleset ihsext-recursive-redefs '(unsigned-byte-p**))


  (defun unsigned-byte-p-ind (bits x)
    (and (integerp x)
         (natp bits)
         (if (zp bits)
             (equal x 0)
           (unsigned-byte-p-ind (1- bits) (logcdr x)))))

  (defthm unsigned-byte-p-induct
    t
    :rule-classes ((:induction
                    :pattern (unsigned-byte-p bits x)
                    :scheme (unsigned-byte-p-ind bits x))))

  (defthm unsigned-byte-p-incr
    (implies (and (unsigned-byte-p a x)
                  (natp b)
                  (<= a b))
             (unsigned-byte-p b x)))

  (defthmd unsigned-byte-p-logcons
    (implies (and (unsigned-byte-p (1- b) x)
                  (natp b))
             (unsigned-byte-p b (logcons bit x)))
    :hints (("goal" :expand ((unsigned-byte-p b (logcons bit x))))))

  (defthmd unsigned-byte-p-logcons-free
    (implies (and (unsigned-byte-p a x)
                  (natp b)
                  (<= a (1- b)))
             (unsigned-byte-p b (logcons bit x)))
    :hints (("goal" :expand ((unsigned-byte-p b (logcons bit x))))))

  (defthmd unsigned-byte-p-logcdr
    (implies (and (unsigned-byte-p a x)
                  (natp b)
                  (<= a (1+ b)))
             (unsigned-byte-p b (logcdr x))))

  (add-to-ruleset ihsext-bounds-thms '(unsigned-byte-p-incr
                                       unsigned-byte-p-logcons
                                       unsigned-byte-p-logcons-free
                                       unsigned-byte-p-logcdr))

  (local (in-theory (disable unsigned-byte-p-logand
                             unsigned-byte-p-logior
                             acl2::logior-=-0)))

  (defthmd unsigned-byte-p-logand-fix
    (implies (or (unsigned-byte-p b x)
                 (unsigned-byte-p b y))
             (unsigned-byte-p b (logand x y))))

  (defun unsigned-byte-p-logior-ind (b x y)
    (cond ((zp b) (list x y))
          (t (unsigned-byte-p-logior-ind
              (1- b) (logcdr x) (logcdr y)))))

  (defthmd unsigned-byte-p-logior-fix
    (equal (unsigned-byte-p b (logior x y))
           (and (unsigned-byte-p b (ifix x))
                (unsigned-byte-p b (ifix y))))
    :hints (("goal" :induct (unsigned-byte-p-logior-ind b x y))))

  (add-to-ruleset ihsext-basic-thms '(unsigned-byte-p-logand-fix
                                      unsigned-byte-p-logior-fix))

  (defthm unsigned-byte-p-of-loghead
    (implies (and (integerp size1)
                  (<= (nfix size) size1))
             (unsigned-byte-p size1 (loghead size i))))

  (defthm unsigned-byte-p-of-logtail
    (implies (natp size1)
             (equal (unsigned-byte-p size1 (logtail size i))
                    (unsigned-byte-p (+ size1 (nfix size)) (ifix i))))
    :hints (("goal" :induct (and (logtail size i)
                                 (logtail size1 i)))))

  (encapsulate
    nil
    (local (defun ind (n m x)
             (cond ((zip m) (list n x))
                   ((< m 0) (ind (1+ n) (1+ m) x))
                   (t (ind (1- n) (1- m) x)))))

    (local (defthm help1
             (implies (unsigned-byte-p n x)
                      (natp n))))


    (local (defthm unsigned-byte-p-of-ash-worse
             ;; "worse" because of the natp hyp, which we'll eliminate in a moment
             (implies (and (unsigned-byte-p (- n (ifix m)) x)
                           (natp n))
                      (unsigned-byte-p n (ash x m)))
             :hints(("Goal" :in-theory (e/d* (acl2::ihsext-recursive-redefs
                                              acl2::ihsext-inductions
                                              nfix ifix zip)
                                             (unsigned-byte-p))
                     :induct (ind n m x)
                     :do-not-induct t)
                    (and stable-under-simplificationp
                         '(:expand ((ash x m)))))
             :otf-flg t))

    (defthm unsigned-byte-p-of-ash
      (implies (unsigned-byte-p (- n (ifix m)) x)
               (equal (unsigned-byte-p n (ash x m))
                      (natp n)))
      :hints(("Goal"
              :in-theory (disable unsigned-byte-p)
              :cases ((natp n))))))

  (encapsulate
    ()
    (local (defun my-induct (n x y)
             (if (zp n)
                 (list n x y)
               (my-induct (- n 1) (logcdr x) (logcdr y)))))

    (defthm unsigned-byte-p-of-logxor
      (implies (and (unsigned-byte-p n i)
                    (unsigned-byte-p n j))
               (unsigned-byte-p n (logxor i j)))
      :hints(("Goal"
              :induct (my-induct n i j)
              :in-theory (enable acl2::logxor**
                                 acl2::unsigned-byte-p**)))))

  (defthmd unsigned-byte-p-implies-natp-width
    (implies (unsigned-byte-p n x)
             (natp n))
    :hints(("Goal" :in-theory (enable unsigned-byte-p)))
    :rule-classes :forward-chaining))

(defsection logite**

  (local (in-theory (enable logite)))

  ;; (defthmd logite-when-zip
  ;;   (implies (or (zip i) (zip j))
  ;;            (equal (logite i j) 0)))

  ;; (add-to-ruleset ihsext-bad-type-thms '(logite-when-zip))

  ;; (defthm logite-of-ifix-1
  ;;   (equal (logite (ifix a) b)
  ;;          (logite a b)))

  ;; (defthm logite-of-ifix-2
  ;;   (equal (logite b (ifix a))
  ;;          (logite b a)))

  ;; (add-to-ruleset ihsext-basic-thms '(logite-of-ifix-1 logite-of-ifix-2))

  (local (in-theory (enable* ihsext-bad-type-thms)))
  (local (in-theory (disable logite)))

  (defthmd logite**
    ;; Better than logite* since there are no hyps; but must case-split manually.
    (equal (logite test then else)
           (logcons (b-ite (logcar test) (logcar then) (logcar else))
                    (logite (logcdr test) (logcdr then) (logcdr else))))
    :hints(("Goal" :in-theory (enable logite logand** logior**)))
    :rule-classes
    ((:definition :clique (logite)
      :controller-alist ((logite t t t)))))

  (add-to-ruleset ihsext-redefs '(logite**))

  (defthm logite-of-logcons-test
    (equal (logite (logcons a b) then else)
           (logcons (b-ite a (logcar then) (logcar else))
                    (logite b (logcdr then) (logcdr else))))
    :hints(("Goal" :expand (logite (logcons a b) then else))))

  (defthm logite-of-logcons-then
    (equal (logite test (logcons a b) else)
           (logcons (b-ite (logcar test) a (logcar else))
                    (logite (logcdr test) b (logcdr else))))
    :hints(("Goal" :in-theory (enable logite**))))

  (defthm logite-of-logcons-else
    (equal (logite test then (logcons a b))
           (logcons (b-ite (logcar test) (logcar then) a)
                    (logite (logcdr test) (logcdr then) b)))
    :hints(("Goal" :in-theory (enable logite**))))


  (defthmd logite$
    ;; Bozo maybe we should have a version that only terminates based on one
    ;; input or the other? maybe better case-splitting/induction schemes
    (equal (logite test then else)
           (cond ((zip test) (ifix else))
                 ((eql test -1) (ifix then))
                 (t (logcons (b-ite (logcar test) (logcar then) (logcar else))
                             (logite (logcdr test) (logcdr then) (logcdr else))))))
    :hints (("goal" :in-theory (enable logite logand$ logior$)))
    :rule-classes ((:definition
                    :clique (logite)
                    :controller-alist ((logite t nil nil)))))

  (add-to-ruleset ihsext-recursive-redefs '(logite$))

  ;; (theory-invariant (not (active-runep '(:definition logite*)))
  ;;                   :key |Use LOGITE** or LOGITE$ instead of LOGITE*|)

  (local (in-theory (enable integer-length**)))

  (defun logite-ind (test then else)
    (declare (xargs :measure (integer-length test)))
    (cond ((zip test) (ifix else))
          ((eql test -1) (ifix then))
          (t (logite-ind (logcdr test) (logcdr then) (logcdr else)))))

  (defthmd logite-induct
    t
    :rule-classes ((:induction
                    :pattern (logite test then else)
                    :scheme (logite-ind test then else))))

  (add-to-ruleset ihsext-inductions '(logite-induct))

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm logcar-of-logite
    (equal (logcar (logite test then else))
           (b-ite (logcar test) (logcar then) (logcar else)))
    :hints (("Goal" :expand (logite test then else))))


  (defthm logcdr-of-logite
    (equal (logcdr (logite test then else))
           (logite (logcdr test) (logcdr then) (logcdr else)))
    :hints(("Goal" :use logite**
            :in-theory (disable logite$))))

  (defthm logbitp-of-logite
    (equal (logbitp a (logite test then else))
           (bit->bool (b-ite (logbit a test)
                            (logbit a then)
                            (logbit a else))))
    :hints(("Goal" :induct (and (logbitp a test)
                                (logbitp a then)
                                (logbitp a else))
            :in-theory (enable bool->bit))))

  (defthm loghead-of-logite
    (equal (loghead a (logite test then else))
           (logite (loghead a test)
                  (loghead a then)
                  (loghead a else)))
    :hints(("Goal" :in-theory (disable loghead-identity))))

  (defthm logtail-of-logite
    (equal (logtail a (logite test then else))
           (logite (logtail a test)
                  (logtail a then)
                  (logtail a else)))
    :hints(("Goal" :in-theory (disable logtail-identity
                                       acl2::logtail-equal-0))))

  (add-to-ruleset ihsext-basic-thms '(logcar-of-logite
                                      logcdr-of-logite
                                      logbitp-of-logite
                                      loghead-of-logite))

  (defthm unsigned-byte-p-of-logite
    (implies (and (unsigned-byte-p n then)
                  (unsigned-byte-p n else))
             (unsigned-byte-p n (logite test then else)))
    :hints(("Goal" :in-theory (disable (force) unsigned-byte-p)))))




(defsection logsquash**

  ;; Squashes to 0 the lowest N bits of I.
  (defund-inline logsquash (n i)
    (declare (xargs :guard (and (natp n)
                                (integerp i))))
    (logand i (ash -1 (nfix n))))

  (defthmd logsquash**
    (equal (logsquash size i)
           (if (zp size)
               (ifix i)
             (logcons 0
                      (logsquash (1- size) (logcdr i)))))
    :hints(("Goal" :in-theory (enable logsquash)))
    :rule-classes ((:definition
                    :clique (logsquash$inline)
                    :controller-alist ((logsquash$inline t nil)))))

  (add-to-ruleset ihsext-recursive-redefs '(logsquash**))
  (add-to-ruleset ihsext-redefs '(logsquash**))

  (local (in-theory (enable logsquash**)))

  ;; (defthmd logsquash-when-zp
  ;;   (implies (zp size)
  ;;            (equal (logsquash size i) 0)))

  ;; (defthmd logsquash-when-zip
  ;;   (implies (zip i)
  ;;            (equal (logsquash size i) 0)))

  ;; (add-to-ruleset ihsext-bad-type-thms '(logsquash-when-zp
  ;;                                        logsquash-when-zip))

  (defthm logsquash-of-0-i
    (equal (logsquash 0 i) (ifix i)))

  (defthmd logsquash-induct
    t
    :rule-classes ((:induction
                    :pattern (logsquash size i)
                    :scheme (logbitp-ind size i))))

  (add-to-ruleset ihsext-inductions '(logsquash-induct))

  (defthm logsquash-of-n-0
    (equal (logsquash n 0) 0)
    :hints(("Goal" :in-theory (enable logsquash-induct))))


  (defthm logcar-of-logsquash
    (implies (not (zp size))
             (equal (logcar (logsquash size i))
                    0))
    :hints(("Goal" :expand ((logsquash size i)))))

  (add-to-ruleset ihsext-basic-thms logcar-of-logsquash)

  (defthmd logcdr-of-logsquash
    (implies (not (zp size))
             (equal (logcdr (logsquash size i))
                    (logsquash (1- size) (logcdr i))))
    :hints (("goal" :expand ((logsquash size i)))))

  (add-to-ruleset ihsext-basic-thms logcdr-of-logsquash)

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm logbitp-of-logsquash-in-bounds
    (implies (<= (nfix size) (nfix pos))
             (equal (logbitp pos (logsquash size i))
                    (logbitp pos i))))

  (defthm logbitp-of-logsquash-out-of-bounds
    (implies (< (nfix pos) (nfix size))
             (equal (logbitp pos (logsquash size i))
                    nil))
    :hints(("Goal"
            :induct (and (logbitp pos i)
                         (logbitp size i))
            :expand ((:free (x) (logbitp pos x))))))

  (add-to-ruleset ihsext-basic-thms '(logbitp-of-logsquash-in-bounds
                                      logbitp-of-logsquash-out-of-bounds))

  (defthmd logbitp-of-logsquash-split
    (equal (logbitp pos (logsquash size i))
           (and (<= (nfix size) (nfix pos))
                (logbitp pos i))))

  (add-to-ruleset ihsext-advanced-thms logbitp-of-logsquash-split)

  (defthmd logsquash-<=-i
    (implies (<= 0 (ifix i))
             (<= (logsquash size i) (ifix i)))
    :rule-classes ((:linear :trigger-terms ((logsquash size i)))))

  (add-to-ruleset ihsext-bounds-thms logsquash-<=-i)

  (defthm logsquash-of-logsquash-1
    (implies (<= (nfix m) (nfix n))
             (equal (logsquash m (logsquash n x))
                    (logsquash n x)))
    :hints (("goal" :in-theory (e/d* (ihsext-recursive-redefs
                                      ihsext-inductions)
                                     (logcdr-<-const
                                      acl2::mod-x-y-=-x+y-for-rationals))
             :induct (and (logsquash m x)
                          (logsquash n x))
             :expand ((:free (b) (logsquash n b))
                      (:free (a b) (logsquash m (logcons a b)))
                      (:free (a b) (lognot (logcons a b)))))))

  (defthm logsquash-of-logsquash-2
    (implies (<= (nfix m) (nfix n))
             (equal (logsquash m (logsquash n x))
                    (logsquash n x)))
    :hints (("goal" :in-theory (e/d* (ihsext-recursive-redefs
                                      ihsext-inductions)
                                     (logcdr-<-const
                                      acl2::MOD-X-Y-=-X+Y-for-rationals))
             :induct (and (logsquash m x)
                          (logsquash n x))
             :expand ((:free (b) (logsquash n b))
                      (:free (a b) (logsquash m (logcons a b)))
                      (:free (a b) (lognot (logcons a b)))))))

  (add-to-ruleset ihsext-basic-thms '(logsquash-of-logsquash-1
                                      logsquash-of-logsquash-2))


  (defcong nat-equiv equal (logsquash n i) 1)
  (defcong int-equiv equal (logsquash n i) 2
    :hints(("Goal" :in-theory (disable int-equiv))))

  (defthm loghead-of-logsquash-commute
    (equal (loghead m (logsquash n i))
           (logsquash n (loghead m i))))

  (defthm logsquash-of-loghead-zero
    (implies (<= (nfix n) (nfix m))
             (equal (logsquash m (loghead n i)) 0))
    :hints (("goal" :induct (and (loghead m i)
                                 (loghead n i)))))

  (defthm logsquash-idempotent
    (equal (logsquash n (logsquash n i))
           (logsquash n i)))

  (add-to-ruleset ihsext-basic-thms '(loghead-of-logsquash-commute
                                      logsquash-of-loghead-zero
                                      logsquash-idempotent))

  (defthmd logsquash-of-logsquash-split
    (equal (logsquash n (logsquash m i))
           (logsquash (max (nfix n) (nfix m)) i)))

  (add-to-ruleset ihsext-advanced-thms logsquash-of-logsquash-split)

  (defthm logtail-of-logsquash
    (equal (logtail n (logsquash m x))
           (logsquash (- (nfix m) (nfix n))
                      (logtail n x)))
    :hints (("goal" :induct (and (logsquash m x)
                                 (logtail n x)))))

  (add-to-ruleset ihsext-basic-thms logtail-of-logsquash)

  (defthm logsquash-cancel-in-lognot
    (implies (<= (nfix m) (nfix n))
             (equal (logsquash n (lognot (logsquash m x)))
                    (logsquash n (lognot x))))
    :hints (("goal" :induct (and (loghead n x)
                                 (loghead m x)))))

  (add-to-ruleset ihsext-basic-thms logsquash-cancel-in-lognot)

  (defthm logsquash-of-logand
    (equal (logsquash a (logand x y))
           (logand (logsquash a x)
                   (logsquash a y))))

  (add-to-ruleset ihsext-basic-thms logsquash-of-logand)

  (defthm logsquash-of-logior
    (equal (logsquash a (logior x y))
           (logior (logsquash a x)
                   (logsquash a y))))

  (add-to-ruleset ihsext-basic-thms logsquash-of-logior)

  (defthm logsquash-of-logxor
    (equal (logsquash a (logxor x y))
           (logxor (logsquash a x)
                   (logsquash a y))))

  (add-to-ruleset ihsext-basic-thms logsquash-of-logxor)

  (defthm logsquash-of-ash-same
    (implies (natp n)
             (equal (logsquash n (ash x n))
                    (ash x n)))
    :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                     ihsext-recursive-redefs)))))

  (local (defun ind (n m x)
           (cond ((zip m) (list n x))
                 ((< m 0) (ind (1+ n) (1+ m) x))
                 (t (ind (1- n) (1- m) x)))))

  (defthmd logsquash-of-ash
    (equal (logsquash n (ash x m))
           (ash (logsquash (nfix (- (nfix n) (ifix m))) x) m))
    :hints(("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                    ihsext-inductions
                                    nfix ifix zip
                                    ash**)
                                   (bitp
                                     logcdr-of-ash))
            :induct (ind n m x)
            :do-not-induct t)))

  (add-to-ruleset ihsext-advanced-thms logsquash-of-ash)

  (defthm logsquash-<-0
    (equal (< (logsquash n x) 0)
           (< (ifix x) 0)))

  (defthm logsquash-cancel
    (implies (unsigned-byte-p n x)
             (equal (logsquash n x) 0))
    :hints(("Goal" :in-theory (disable unsigned-byte-p))))

  (defthm unsigned-byte-p-of-logsquash
    (implies (and (unsigned-byte-p size1 i)
                  (<= (nfix size) (nfix size1)))
             (unsigned-byte-p size1 (logsquash size i)))
    :hints(("Goal" :in-theory (disable unsigned-byte-p))))

  (defthm logsquash-of-ash-greater
    (implies (<= (nfix n) (ifix i))
             (equal (logsquash n (ash x i))
                    (ash x i)))
    :hints (("goal" :induct (and (logsquash n b)
                                 (logsquash i b))))))


(defsection signed-byte-p**

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions
                             ihsext-bounds-thms
                             ihsext-advanced-thms
                             ihsext-arithmetic
                             )))

  (defthmd minus-to-lognot
    (implies (integerp x)
             (equal (- x)
                    (+ 1 (lognot x))))
    :hints(("Goal" :in-theory (enable lognot)))
    :rule-classes ((:rewrite :backchain-limit-lst (0))))

  (defthmd elim-plus-one
    (implies (and (integerp x)
                  (integerp y))
             (equal (< x (+ 1 y))
                    (<= x y)))
    :rule-classes ((:rewrite :backchain-limit-lst (0 0))))

  (add-to-ruleset ihsext-advanced-thms '(elim-plus-one))

  (local (in-theory (enable minus-to-lognot elim-plus-one)))

  (local (defthm ash-zero-fwd
           (implies (and (equal (ash x bits) 0)
                         (not (zip x)))
                    (< bits 0))
           :rule-classes :forward-chaining))


  (defthmd signed-byte-p**
    (equal (signed-byte-p bits x)
           (and (integerp x)
                (posp bits)
                (cond ((= bits 1) (or (= x 0) (= x -1)))
                      (t (signed-byte-p (1- bits) (logcdr x))))))
    :rule-classes ((:definition
                    :clique (signed-byte-p)
                    :controller-alist ((signed-byte-p t t)))))

  (local (in-theory (enable signed-byte-p**)))
  (local (in-theory (disable signed-byte-p)))

  (add-to-ruleset ihsext-recursive-redefs '(signed-byte-p**))

  (defun signed-byte-p-ind (bits x)
    (and (integerp x)
         (posp bits)
         (cond ((= bits 1) (or (= x 0) (= x -1)))
               (t (signed-byte-p-ind (1- bits) (logcdr x))))))

  (defthm signed-byte-p-induct
    t
    :rule-classes ((:induction
                    :pattern (signed-byte-p bits x)
                    :scheme (signed-byte-p-ind bits x))))

  (defthm signed-byte-p-incr
    (implies (and (signed-byte-p a x)
                  (natp b)
                  (<= a b))
             (signed-byte-p b x)))

  (defthmd signed-byte-p-logcons
    (implies (and (signed-byte-p a x)
                  (natp b)
                  (<= a (1- b)))
             (signed-byte-p b (logcons bit x)))
    :hints (("goal" :expand ((signed-byte-p b (logcons bit x))))))

  (defthmd signed-byte-p-logcdr
    (implies (and (signed-byte-p a x)
                  (posp b)
                  (<= a (1+ b)))
             (signed-byte-p b (logcdr x))))

  (add-to-ruleset ihsext-bounds-thms '(signed-byte-p-incr
                                       signed-byte-p-logcons
                                       signed-byte-p-logcdr))

  ;; from logops-lemmas
  (add-to-ruleset ihsext-bounds-thms '(signed-byte-p-logops))

  (defthm signed-byte-p-0-x
    (not (signed-byte-p 0 n)))

  (defthm signed-byte-p-n-0
    (equal (signed-byte-p n 0)
           (< 0 (nfix n))))

  (defthm signed-byte-p-n-minus1
    (equal (signed-byte-p n -1)
           (< 0 (nfix n))))

  (local (defun signed-byte-p-of-logtail-ind (size1 size i)
           (if (zp size)
               (list size1 i)
             (signed-byte-p-of-logtail-ind (1+ size1) (1- size) i))))

  (defthm signed-byte-p-of-logtail
    (equal (signed-byte-p size (logtail shift i))
           (and (posp size)
                (signed-byte-p (+ size (nfix shift)) (ifix i))))
    :hints (("goal" :induct (signed-byte-p-of-logtail-ind size shift i))))

  (defthm signed-byte-p-of-logcdr
    (equal (signed-byte-p width (logcdr x))
           (and (posp width)
                (signed-byte-p (+ 1 width) (ifix x)))))


  (local (in-theory (disable minus-to-lognot)))

  (local (defun signed-byte-of-ash-ind (shift n)
           (declare (xargs :measure (abs (ifix shift))))
           (if (zip shift)
               n
             (if (< 0 shift)
                 (signed-byte-of-ash-ind (1- shift) (1- n))
               (signed-byte-of-ash-ind (1+ shift) (1+ n))))))

  (defthm signed-byte-p-of-ash-split
    (equal (signed-byte-p n (ash x shift))
           (and (posp n)
                (or (zip x)
                    (signed-byte-p (- n (ifix shift)) x))))
    :hints(("Goal" :in-theory (enable signed-byte-p** ash**)
            :induct (signed-byte-of-ash-ind shift n)))))





(defsection logapp**
  (local (include-book "ihs/logops-lemmas" :dir :system))
  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions
                             ihsext-bounds-thms
                             ihsext-advanced-thms
                             ihsext-arithmetic
                             acl2::logapp*
                             )))

  ;; (defthm logapp-of-nfix
  ;;   (equal (logapp (nfix size) i j)
  ;;          (logapp size i j))
  ;;   :hints(("Goal" :in-theory (enable logapp))))

  ;; (defthm logapp-of-ifix-1
  ;;   (equal (logapp size (ifix i) j)
  ;;          (logapp size i j))
  ;;   :hints(("Goal" :in-theory (enable logapp))))

  ;; (defthm logapp-of-ifix-2
  ;;   (equal (logapp size j (ifix i))
  ;;          (logapp size j i))
  ;;   :hints(("Goal" :in-theory (enable logapp))))

  ;; (add-to-ruleset ihsext-basic-thms '(logapp-of-nfix logapp-of-ifix-1 logapp-of-ifix-2))


  ;; just to instantiate below
  (local (defthm logapp-fixes
           (equal (logapp size i j)
                  (logapp (nfix size) (ifix i) (ifix j)))
           :rule-classes nil))

  (defthmd logapp**
    (equal (logapp size i j)
           (if (zp size)
               (ifix j)
             (logcons (logcar i)
                      (logapp (1- size) (logcdr i) j))))
    :hints (("goal" :use (logapp-fixes
                          (:instance logapp-fixes
                                     (size (1- size)) (i (logcdr i))))
             :in-theory (disable logapp (force)

; Matt K. mod 5/2016 (type-set bit for {1}): the addition of a type-set bit for
; the set {1} sent the proof in a different direction with this rewrite rule.
; Monitoring this rule shows that (EQUAL (BINARY-+ '-1 SIZE) '0) rewrites to
; (EQUAL SIZE '1), so with the new type-set bit for {1}, it isn't surprising
; that the proof goes in a different direction than before.

                                 acl2::equal-constant-+
                                 acl2::int-equiv-implies-equal-logapp-2
                                 acl2::int-equiv-implies-equal-logapp-3
                                 acl2::nat-equiv-implies-equal-logapp-1)))
    :rule-classes ((:definition
                    :clique (logapp)
                    :controller-alist ((logapp t nil nil)))))

  (add-to-ruleset ihsext-recursive-redefs '(logapp**))
  (add-to-ruleset ihsext-redefs '(logapp**))

  (local (in-theory (e/d (logapp**) (acl2::logapp* logapp))))

  (defthmd logapp-induct
    t
    :rule-classes ((:induction
                    :pattern (logapp size i j)
                    :scheme (logbitp-ind size i))))

  (add-to-ruleset ihsext-inductions '(logapp-induct))

  (defthm logapp-of-size-0
    (equal (logapp 0 i j) (ifix j)))

  (defthm logapp-of-i-0
    (equal (logapp size 0 j)
           (ash j (nfix size)))
    :hints(("Goal" :in-theory (e/d (ash** logapp-induct))
            :induct (logapp size 0 j))))

  (defthm logapp-of-j-0
    (equal (logapp size i 0)
           (loghead size i))
    :hints(("Goal" :in-theory (e/d (loghead** logapp-induct))
            :induct (logapp size i 0))))

  (add-to-ruleset ihsext-bad-type-thms '(logapp-of-size-0
                                         logapp-of-i-0
                                         logapp-of-j-0))

  (local (in-theory (disable logapp)))

  (defthmd logcar-of-logapp-split
    (equal (logcar (logapp size i j))
           (if (zp size) (logcar j) (logcar i)))
    :hints (("goal" :expand ((logapp size i j)))))

  (add-to-ruleset ihsext-advanced-thms '(logcar-of-logapp-split))

  (defthm logcar-of-logapp-nonzero
    (implies (not (zp size))
             (equal (logcar (logapp size i j))
                    (logcar i)))
    :hints(("Goal" :in-theory (enable logcar-of-logapp-split))))

  (defthmd logcdr-of-logapp-split
    (equal (logcdr (logapp size i j))
           (if (zp size)
               (logcdr j)
             (logapp (1- size) (logcdr i) j)))
    :hints (("goal" :expand ((logapp size i j)))))

  (add-to-ruleset ihsext-advanced-thms logcdr-of-logapp-split)

  (defthm logcdr-of-logapp-nonzero
    (implies (not (zp size))
             (equal (logcdr (logapp size i j))
                    (logapp (1- size) (logcdr i) j)))
    :hints(("Goal" :in-theory (enable logcdr-of-logapp-split))))

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (local (in-theory (disable acl2::logbitp-logapp)))

  (defthmd logbitp-of-logapp-split
    (equal (logbitp pos (logapp size i j))
           (if (< (nfix pos) (nfix size))
               (logbitp pos i)
             (logbitp (- (nfix pos) (nfix size)) j)))
    :hints (("goal" :in-theory (enable* ihsext-inductions)
             :induct (and (logapp size i j)
                          (logbitp pos i)))))

  (add-to-ruleset ihsext-advanced-thms logbitp-of-logapp-split)

  (defthm logbitp-of-logapp-first
    (implies (< (nfix pos) (nfix size))
             (equal (logbitp pos (logapp size i j))
                    (logbitp pos i)))
    :hints(("Goal" :in-theory (enable logbitp-of-logapp-split))))

  (defthm logbitp-of-logapp-second
    (implies (>= (nfix pos) (nfix size))
             (equal (logbitp pos (logapp size i j))
                    (logbitp (- (nfix pos) (nfix size)) j)))
    :hints(("Goal" :in-theory (enable logbitp-of-logapp-split))))

  (defthmd loghead-of-logapp-split
    (equal (loghead n (logapp size i j))
           (if (<= (nfix n) (nfix size))
               (loghead n i)
             (logapp size i (loghead (- (nfix n) (nfix size)) j))))
    :hints (("goal" :in-theory (e/d* (ihsext-inductions)
                                     (loghead-identity
                                      (force)))
             :induct (and (logapp size i j)
                          (loghead n i)))))

  (add-to-ruleset ihsext-advanced-thms loghead-of-logapp-split)

  (defthm loghead-of-logapp-1
    (implies (<= (nfix n) (nfix size))
             (equal (loghead n (logapp size i j))
                    (loghead n i)))
    :hints(("Goal" :in-theory (enable loghead-of-logapp-split))))

  (defthm loghead-of-logapp-2
    (implies (> (nfix n) (nfix size))
             (equal (loghead n (logapp size i j))
                    (logapp size i (loghead (- (nfix n) (nfix size)) j))))
    :hints(("Goal" :in-theory (enable loghead-of-logapp-split))))

  (defthmd logtail-of-logapp-split
    (equal (logtail n (logapp size i j))
           (if (< (nfix n) (nfix size))
               (logapp (- (nfix size) (nfix n))
                       (logtail n i) j)
             (logtail (- (nfix n) (nfix size)) j)))
    :hints (("goal" :in-theory (e/d* (ihsext-inductions)
                                     (logtail-identity
                                      acl2::logtail-equal-0
                                      (force)))
             :induct (and (logapp size i j)
                          (loghead n i)))))

  (add-to-ruleset ihsext-advanced-thms logtail-of-logapp-split)

  (defthm logtail-of-logapp-1
    (implies (< (nfix n) (nfix size))
             (equal (logtail n (logapp size i j))
                    (logapp (- (nfix size) (nfix n))
                            (logtail n i) j)))
    :hints(("Goal" :in-theory (enable logtail-of-logapp-split))))

  (defthm logtail-of-logapp-2
    (implies (>= (nfix n) (nfix size))
             (equal (logtail n (logapp size i j))
                    (logtail (- (nfix n) (nfix size)) j)))
    :hints(("Goal" :in-theory (enable logtail-of-logapp-split))))

  (local (defun ind (size1 size i j)
           (if (zp size)
               (list size1 size i j)
             (ind (1- size1) (1- size) (logcdr i) j))))

  (defthm unsigned-byte-p-of-logapp
    (implies (and (integerp size1)
                  (<= (nfix size) size1)
                  (unsigned-byte-p (- size1 (nfix size)) j))
             (unsigned-byte-p size1 (logapp size i j)))
    :hints (("goal" :induct (ind size1 size i j)
             :in-theory (disable unsigned-byte-p
                                 minus-to-lognot))))

  (defthm signed-byte-p-of-logapp
    (implies (and (integerp size1)
                  (<= (nfix size) size1)
                  (signed-byte-p (- size1 (nfix size)) j))
             (signed-byte-p size1 (logapp size i j)))
    :hints (("goal" :induct (ind size1 size i j)
             :in-theory (disable signed-byte-p
                                 minus-to-lognot))))

  (defthm integer-length-of-logapp-when-j
    (implies (<= 1 (integer-length j))
             (equal (integer-length (logapp size i j))
                    (+ (nfix size) (integer-length j))))
    :hints (("goal" :induct (logapp size i j)
             :in-theory (disable (force)))))

  (defthm logapp-sign
    (equal (< (logapp size i j) 0)
           (< (ifix j) 0))
    :hints (("goal" :induct (logapp size i j)
             :in-theory (disable (force)))))

  (local (defun logapp-of-loghead-ind (n m x)
           (if (zp n)
               (list m x)
             (logapp-of-loghead-ind (1- n) (1- m) (logcdr x)))))

  (defthm logapp-of-loghead
    (implies (<= (nfix n) (nfix m))
             (equal (logapp n (loghead m x) y)
                    (logapp n x y)))
    :hints (("goal" :induct (logapp-of-loghead-ind n m x))))

  (defthm logapp-of-logtail
    (equal (logapp n x (logtail n x))
           (ifix x)))

  (local (defun logapp-right-ind (w1 w2 a)
            (if (or (zp w1) (zp w2))
                a
              (logapp-right-ind (1- w1) (1- w2) (logcdr a)))))

   (defthmd logapp-right-assoc
     (equal (logapp w1 (logapp w2 a b) c)
            (let ((w1 (nfix w1)) (w2 (nfix w2)))
              (logapp (min w1 w2)
                      a (if (<= w1 w2) c (logapp (- w1 w2) b c)))))
     :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                      ihsext-recursive-redefs))
             :induct (logapp-right-ind w1 w2 a))))

  (add-to-ruleset ihsext-basic-thms '(unsigned-byte-p-of-logapp
                                      signed-byte-p-of-logapp
                                      logapp-sign
                                      logapp-of-loghead
                                      logapp-of-logtail))

  ;; (defthm logapp-zeros
  ;;   (equal (logapp i 0 0) 0))

  (defthm logapp-minus1s
    (equal (logapp i -1 -1) -1)))



(defsection mod

  (defthm mod-self
    (equal (mod a a) 0)
    :hints(("Goal"
            :in-theory (enable mod floor)
            :cases ((acl2-numberp a)))))

  (defthmd mod-to-loghead
    (implies (and (integerp i)
                  ;; n is expected to be a natural, but it could really be
                  ;; anything except for a negative integer, since ash and
                  ;; loghead treat only those differently
                  (not (and (integerp n)
                            (< n 0))))
             (equal (mod i (ash 1 n))
                    (loghead n i)))
    :hints(("Goal" :in-theory (enable* ihsext-bad-type-thms
                                       loghead expt-2-is-ash)
            :cases ((integerp n)))))

  (add-to-ruleset ihsext-arithmetic '(mod-to-loghead)))



(defsection floor

  (defthm floor-0
    ;; Names chosen for compatibility with an arithmetic-3 rule of the same name
    (and (equal (floor x 0) 0)
         (equal (floor 0 y) 0))
    :hints(("Goal" :in-theory (enable floor))))

  (defthmd floor-to-logtail
    (implies (and (integerp i)
                  ;; n is expected to be a natural, but it could really be
                  ;; anything except for a negative integer, since ash and
                  ;; logtail treat only those differently
                  (not (and (integerp n)
                            (< n 0))))
             (equal (floor i (ash 1 n))
                    (logtail n i)))
    :hints(("Goal" :in-theory (enable* ihsext-bad-type-thms
                                       logtail expt-2-is-ash)
            :cases ((integerp n)))))

  (add-to-ruleset ihsext-arithmetic '(floor-to-logtail)))



(defsection logext**

  (local (in-theory (enable* ihsext-bad-type-thms
                             logext)))

  ;; (defthm logext-when-not-posp
  ;;   (implies (not (posp size))
  ;;            (equal (logext size i)
  ;;                   (if (= (logcar i) 1) -1 0)))
  ;;   :hints(("Goal" :in-theory (enable* logext))))

  ;; (defthm logext-when-zip
  ;;   (implies (zip i)
  ;;            (equal (logext size i)
  ;;                   0))
  ;;   :hints(("Goal" :in-theory (e/d (logext) (logapp-0)))))

  ;; (defthm logext-of-nfix
  ;;   (equal (logext (nfix size) i)
  ;;          (logext size i)))

  ;; (defthm logext-of-ifix
  ;;   (equal (logext size (ifix i))
  ;;          (logext size i)))

  ;; (add-to-ruleset ihsext-basic-thms '(logext-of-nfix logext-of-ifix))

  (defthm logext-of-0-i-when-logcar-1
    (implies (bit->bool (logcar i))
             (equal (logext 0 i) -1))
    :hints(("Goal" :in-theory (enable logapp**))))

  (defthm logext-of-0-i-when-logcar-0
    (implies (not (bit->bool (logcar i)))
             (equal (logext 0 i) 0)))

  (defthm logext-of-1-i-when-logcar-1
    (implies (bit->bool (logcar i))
             (equal (logext 1 i) -1)))

  (defthm logext-of-1-i-when-logcar-0
    (implies (not (bit->bool (logcar i)))
             (equal (logext 1 i) 0)))

  (defthm logext-of-sz-0
    (equal (logext size 0) 0))

  (defthm logext-of-sz-minus1
    (equal (logext size -1) -1))

  (defthmd logext**
    (equal (logext size i)
           (cond ((or (zp size)
                      (= size 1))
                  (if (bit->bool (logcar i)) -1 0))
                 (t (logcons (logcar i)
                             (logext (1- size) (logcdr i))))))
    :hints(("Goal" :in-theory (disable logext)
            :use ((:instance acl2::logext*
                   (size (if (posp size) size 1))
                   (i (ifix i))))))
    :rule-classes ((:definition
                    :clique (logext)
                    :controller-alist ((logext t nil)))))

  (add-to-ruleset ihsext-recursive-redefs logext**)
  (add-to-ruleset ihsext-redefs logext**)

  (defun logext-ind (size i)
    (declare (xargs :measure (nfix size)))
    (cond ((or (zp size)
               (= size 1))
           (if (bit->bool (logcar i)) -1 0))
          (t (logcons (logcar i)
                      (logext-ind (1- size) (logcdr i))))))

  (defthmd logext-induct
    t
    :rule-classes ((:induction
                    :pattern (logext pos i)
                    :scheme (logext-ind pos i))))

  (add-to-ruleset ihsext-inductions logext-induct)

  ;; (in-theory (disable logext-when-not-posp
  ;;                     logext-when-zip))

  ;; (add-to-ruleset ihsext-bad-type-thms
  ;;                 '(logext-when-not-posp
  ;;                   logext-when-zip))

  (local (in-theory (e/d* (ihsext-recursive-redefs
                           ihsext-inductions)
                          (logext
                           signed-byte-p
                           acl2::logext-identity
                           signed-byte-p**))))

  (defthm logbitp-of-logext
    (equal (logbitp pos (logext size i))
           (if (< (nfix pos) (nfix size))
               (logbitp pos i)
             (logbitp (1- size) i))))

  (defthm signed-byte-p-of-logext
    (implies (and (integerp size1)
                  (>= size1 (if (posp size) size 1)))
             (signed-byte-p size1 (logext size i))))

  (add-to-ruleset ihsext-basic-thms signed-byte-p-of-logext)

  (local
   (defun my-induct (m n x)
     (cond ((zp m) (list m n x))
           ((equal n 1) t)
           (t (my-induct (1- m) (1- n) (logcdr x))))))

  (defthm cancel-logext-under-loghead
    (implies (<= (nfix m) (nfix n))
             (equal (loghead m (logext n x))
                    (loghead m x)))
    :hints(("Goal"
            :induct (my-induct m n x)
            :in-theory (e/d (loghead** logext**)
                            (acl2::logextu-as-loghead
                             acl2::loghead-identity))
            :do-not '(eliminate-destructors generalize fertilize)
            :do-not-induct t)))

  (defthm cancel-loghead-under-logext
    (implies (posp sz)
             (equal (logext sz (loghead sz x))
                    (logext sz x)))
    :hints (("goal" :in-theory (enable* ihsext-inductions
                                        ihsext-recursive-redefs
                                        posp))))

  (add-to-ruleset ihsext-arithmetic cancel-logext-under-loghead)
  (add-to-ruleset ihsext-arithmetic cancel-loghead-under-logext)

  (defthm logext-of-logand
    (equal (logext n (logand x1 x2))
           (logand (logext n x1)
                   (logext n x2)))
    :hints (("goal" :in-theory (e/d* (ihsext-inductions
                                      ihsext-recursive-redefs)
                                     (acl2::logext-identity ;; Dumb speed hint
                                      acl2::logext-bounds
                                      acl2::logext-type
                                      logand$)))))

  (defthm logext-of-logior
    (equal (logext n (logior x1 x2))
           (logior (logext n x1)
                   (logext n x2)))
    :hints (("goal" :in-theory (e/d* (ihsext-inductions
                                      ihsext-recursive-redefs)
                                     (acl2::logext-identity ;; Dumb speed hint
                                      acl2::logext-bounds
                                      acl2::logext-type
                                      logior$))))))


(defsection bitmaskp

  (local (in-theory (enable bitmaskp)))

  (defcong int-equiv equal (bitmaskp i) 1)

  (defthmd bitmaskp**
    (equal (bitmaskp i)
           (cond ((zip i) t)
                 ((= i -1) nil)
                 (t (and (bit->bool (logcar i))
                         (bitmaskp (logcdr i))))))
    :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                     acl2::logmaskp*
                                     ihsext-recursive-redefs)
                                    ((force)))))
    :rule-classes ((:definition :clique (acl2::bitmaskp$inline)
                    :controller-alist ((acl2::bitmaskp$inline t)))))

  (local (in-theory (disable bitmaskp)))

  (defthmd bitmaskp-induct
    t
    :rule-classes ((:induction
                    :pattern (bitmaskp i)
                    :scheme (integer-length-ind i))))

  (add-to-ruleset ihsext-redefs bitmaskp**)
  (add-to-ruleset ihsext-recursive-redefs bitmaskp**)
  (add-to-ruleset ihsext-inductions bitmaskp-induct)

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm bitmaskp-of-construct-mask
    (implies (natp n)
             (bitmaskp (+ -1 (ash 1 n))))
    :hints (("goal" :induct t
             :in-theory (enable logcons)
             :expand ((:free (a b) (bitmaskp (+ -1 (logcons a b))))))))

  (encapsulate nil
    (local (defthm mult-both-sides
             (implies (and (rationalp x)
                           (rationalp y)
                           (rationalp z)
                           (not (equal 0 z)))
                      (equal (equal (* x z) (* y z))
                             (equal x y)))
             :rule-classes nil))
    ;; wtf
    (local (defthm 2-n-is-not-1
             (implies (integerp n)
                      (equal (equal (* 2 n) 1)
                             nil))
             :hints (("goal" :use ((:instance mult-both-sides
                                    (z 1/2) (x (* 2 n)) (y 1)))))))

    (defthm integer-length-of-construct-mask
      (equal (integer-length (+ -1 (ash 1 width)))
             (nfix width))
      :hints (("goal" :induct t
               :in-theory (enable logcons)))))

  (defthm logand-with-bitmask
    (implies (bitmaskp mask)
             (equal (logand mask i)
                    (loghead (integer-length mask) i)))
    :hints (("goal"
             :in-theory (enable* ihsext-inductions
                                 ihsext-recursive-redefs)
             :induct (logand mask i))))

  (defthmd logmaskp-lognot
    ;; bozo why not bitmaskp?
    (equal (logmaskp (lognot mask))
           (equal mask (ash -1 (integer-length mask))))
    :hints (("goal" :induct (integer-length mask)
             :in-theory (e/d* (logtail** logand** acl2::logmaskp*
                                         integer-length**
                                         lognot**
                                         logapp** ash**
                                         ihsext-inductions)
                              (logmaskp logapp))
             :do-not-induct t)))

  (defthm logand-with-negated-bitmask
    (implies (bitmaskp (lognot mask))
             (equal (logand mask i)
                    (logsquash (integer-length mask) i)))
    :hints (("goal"
             :in-theory (enable* ihsext-inductions
                                 ihsext-recursive-redefs)
             :induct (logand mask i))))

  (defthm logbitp-when-bitmaskp
    (implies (bitmaskp x)
             (equal (logbitp n x)
                    (< (nfix n) (integer-length x))))
    :hints (("goal" :in-theory (enable* logbitp** integer-length** bitmaskp**
                                        ihsext-inductions)
             :induct (logbitp n x))
            (and stable-under-simplificationp
                 '(:cases ((logbitp (+ -1 n) (logcdr x)))))))

  (defthmd loghead-of-negative-one
    (equal (loghead n -1)
           (1- (ash 1 (nfix n))))
    :hints (("goal" :induct (loghead n a)
             :do-not-induct t
             :in-theory (e/d* (logcons ihsext-inductions nfix)
                              (loghead-identity))
             :expand ((:free (a) (loghead n a))
                      (ash 1 n))))))

(defsection logmask**

  (local (in-theory (enable logmask)))

  (defthmd logmask**
    (equal (logmask n)
           (if (zp n)
               0
             (logcons 1 (logmask (1- n)))))
    :hints(("Goal" :in-theory (e/d* (ihsext-inductions
                                     logmask
                                     logcons
                                     expt-2-is-ash
                                     ihsext-recursive-redefs)
                                    ((force)))))
    :rule-classes ((:definition :clique (acl2::logmask$inline)
                    :controller-alist ((acl2::logmask$inline t)))))

  (local (in-theory (disable logmask)))

  (defun count-down (n)
    (if (zp n)
        n
      (count-down (1- n))))

  (defthmd logmask-induct
    t
    :rule-classes ((:induction
                    :pattern (logmask i)
                    :scheme (count-down i))))

  (add-to-ruleset ihsext-redefs logmask**)
  (add-to-ruleset ihsext-recursive-redefs logmask**)
  (add-to-ruleset ihsext-inductions logmask-induct)

  (local (in-theory (enable* ihsext-recursive-redefs
                             ihsext-inductions)))

  (defthm bitmaskp-of-logmask
    (bitmaskp (logmask n))
    :hints (("goal" :in-theory (enable logmask expt-2-is-ash))))

  (defthm integer-length-of-logmask
    (equal (integer-length (logmask width))
           (nfix width))
    :hints (("goal" :in-theory (enable logmask expt-2-is-ash))))

  (defthm unsigned-byte-p-of-logmask
    (implies (posp width)
             (unsigned-byte-p width (logmask width)))
    :hints(("Goal" :in-theory (e/d (unsigned-byte-p**)
                                   (unsigned-byte-p))
            :induct (logmask width))))

  (local (defthmd signed-byte-p-of-logmask-lemma
           (signed-byte-p (+ 1 (nfix width)) (logmask width))
           :hints(("Goal" :in-theory (e/d* (signed-byte-p** logmask**
                                                            ihsext-inductions)
                                           (signed-byte-p logmask))
                   :induct (logmask width)))))

  (defthm signed-byte-p-monotonicity
    (implies (and (signed-byte-p a x)
                  (<= a b)
                  (integerp b))
             (signed-byte-p b x))
    :hints(("Goal" :in-theory (enable signed-byte-p**))))

  (defthm signed-byte-p-of-logmask
    (implies (and (posp width2)
                  (<= (+ 1 (nfix width)) width2))
             (signed-byte-p width2 (logmask width)))
    :hints(("Goal" :use signed-byte-p-of-logmask-lemma
            :in-theory (disable signed-byte-p logmask))))

  (defthmd ash-minus-1-is-logmask
    (implies (natp n)
             (equal (+ -1 (ash 1 n))
                    (logmask n)))
    :hints (("goal" :in-theory (enable expt-2-is-ash logmask)))))




(defsection logcount**

  (local (defthm nonnegative-integer-quotient-is-logcdr
           (implies (natp x)
                    (equal (nonnegative-integer-quotient x 2)
                           (logcdr x)))))

  (local (defthm evenp-is-logcar-equal-0
           (implies (integerp x)
                    (equal (evenp x)
                           (equal (logcar x) 0)))
           :hints(("Goal" :in-theory (enable oddp)
                   :use ((:instance logbitp
                          (i 0) (j x)))))))

  (defthmd logcount**
    (equal (logcount x)
           (cond ((zip x) 0)
                 ((= x -1) 0)
                 (t (+ (if (< 0 x)
                           (logcar x)
                         (b-not (logcar x)))
                       (logcount (logcdr x))))))
    :hints(("Goal" :in-theory (enable logcount)))
    :rule-classes ((:definition
                    :clique (logcount)
                    :controller-alist ((logcount t)))))

  (add-to-ruleset ihsext-redefs logcount**)
  (add-to-ruleset ihsext-recursive-redefs logcount**)

  (defthmd logcount-induct
    t
    :rule-classes ((:induction
                    :pattern (logcount x)
                    :scheme (integer-length-ind x))))

  (add-to-ruleset ihsext-inductions logcount-induct))


(defsection logrev**

  (local (in-theory (enable* arith-equiv-forwarding)))
  (local (in-theory (enable logrev1 logrev)))

  (in-theory (disable (:t logrev))) ;; Too weak (integerp)

  (defthm logrev-type
    ;; Redundant with ihs/basic-definitions.lisp
    (b* ((nat (acl2::logrev$inline size i)))
      (natp nat))
    :rule-classes :type-prescription)

  (local (defthm natp-of-logrev1
           (implies (natp j)
                    (natp (logrev1 size i j)))))

  (local (defthm logtail-1-of-logcons
           ;; BOZO unlocalize?
           (equal (logtail 1 (logcons a b))
                  (ifix b))
           :hints(("Goal" :in-theory (enable logtail**)))))

  (local (defthmd logcons-alt
           (equal (logcons b i)
                  (logior (bfix b) (ash i 1)))
           :hints(("Goal" :in-theory (enable ash**)))))

  (local (defthm ash-of-logior
           (implies (natp size)
                    (equal (ash (logior a b) size)
                           (logior (ash a size)
                                   (ash b size))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-redefs)))))

  (local (defthm ash-of-logcons-0
           (implies (natp size)
                    (equal (ASH (LOGCONS 0 J) (+ -1 SIZE))
                           (ash j size)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-redefs
                                              logcons-alt)))))

  (local (defthm ash-of-logcons-1
           (implies (natp size)
                    (equal (ASH (LOGCONS 1 J) (+ -1 SIZE))
                           (logior (ash 1 (+ -1 size))
                                   (ash j size))))
           :hints(("Goal"
                   :in-theory (enable* ihsext-inductions
                                       ihsext-redefs
                                       logcons-alt)))))

  (encapsulate
    ()
    ;; This is similar to how REV differs from REVERSE.  Using a non
    ;; tail-recursive version seems really convenient for reasoning.
    (local (defun my-logrev (size i)
             (declare (xargs :measure (nfix size)))
             (if (zp size)
                 0
               (let ((size (- size 1)))
                 (logior (my-logrev size (logcdr i))
                         (ash (logcar i) size))))))

    (local (defthm logrev1-removal
             (equal (logrev1 size i j)
                    (logior (my-logrev size i)
                            (ash j (nfix size))))
             :hints(("Goal" :induct (logrev1 size i j)))))

    (local (defthm logrev-removal
             (equal (logrev size i)
                    (my-logrev size i))))

    (defthmd logrev**
      (equal (logrev size i)
             (if (zp size)
                 0
               (let ((size (- size 1)))
                 (logior (logrev size (logcdr i))
                         (ash (logcar i) size)))))
      :rule-classes ((:definition
                      :clique (acl2::logrev$inline)
                      :controller-alist ((acl2::logrev$inline t nil))))))

  (add-to-ruleset ihsext-recursive-redefs '(logrev**))
  (add-to-ruleset ihsext-redefs '(logrev**))

  (defthmd logrev-induct
    t
    :rule-classes ((:induction
                    :pattern (acl2::logrev$inline size i)
                    :scheme (logbitp-ind size i))))

  (add-to-ruleset ihsext-inductions '(logrev-induct))

  (local (in-theory (e/d (logrev**)
                         (logrev))))

  (defcong nat-equiv equal (logrev size i) 1
    :hints(("Goal" :in-theory (enable* logrev-induct))))

  (defcong int-equiv equal (logrev size i) 2
    :hints(("Goal" :in-theory (enable* logrev-induct))))

  (defthm logrev-when-zp
    (implies (zp size)
             (equal (logrev size i)
                    0)))

  (defthm logrev-when-zip
    (implies (zip i)
             (equal (logrev size i)
                    0))
    :hints(("Goal" :in-theory (enable* logrev-induct))))

  (defsection logrev-upper-bound

    (local (in-theory (enable expt-2-is-ash)))

    (local (defthm l2
             (implies (and (< a (ash 1 size))
                           (< b (ash 1 size))
                           (integerp a)
                           (integerp b)
                           (natp size))
                      (< (logior a b) (ash 1 size)))
             :rule-classes ((:rewrite) (:linear))
             :hints(("Goal"
                     :in-theory (disable right-shift-to-logtail
                                         unsigned-byte-p-of-logior
                                         unsigned-byte-p-logior)
                     :use ((:instance unsigned-byte-p-of-logior
                                      (n size)
                                      (i a)
                                      (j b)))))))

    (local (defthm l3
             ;; BOZO good rule to unlocalize?
             (equal (equal (ash 1 k) 0)
                    (negp k))
             :hints(("Goal" :in-theory (enable* ihsext-inductions
                                                ihsext-recursive-redefs)))))

    (local (defthm l4
             (implies (natp size)
                      (< (ash 1 (+ -1 size))
                         (ash 1 size)))
             :rule-classes ((:rewrite) (:linear))
             :hints(("Goal" :in-theory (enable* ihsext-inductions
                                                ihsext-recursive-redefs
                                                logcons)))))

    (local (defthm l6
             (implies (and (< (logrev (+ -1 size) k)
                              (ash 1 (+ -1 size)))
                           (not (zp size)))
                      (< (logior (ash 1 (+ -1 size))
                                 (logrev (+ -1 size) k))
                         (ash 1 size)))
             :hints(("goal"
                     :use ((:instance l2
                                      (a (ash 1 (+ -1 size)))
                                      (b (logrev (+ -1 size) k))
                                      (size size)))))))

    (defthm logrev-upper-bound
      (< (logrev size i)
         (expt 2 (nfix size)))
      :rule-classes ((:linear)
                     ;; BOZO this is gross, what's the right way to do this?
                     (:linear :corollary
                              (implies (natp size)
                                       (< (logrev size i)
                                          (ash 1 size))))
                     (:linear :corollary
                              (implies (natp size)
                                       (< (logrev size i)
                                          (expt 2 size))))
                     (:rewrite :corollary
                               (implies (natp size)
                                        (< (logrev size i)
                                           (ash 1 size))))
                     (:rewrite :corollary
                               (implies (natp size)
                                        (< (logrev size i)
                                           (expt 2 size)))))
      :hints(("Goal" :in-theory (enable* ihsext-inductions
                                         ihsext-recursive-redefs
                                         logcons-alt)))))

  (defthm unsigned-byte-p-of-logrev
    (equal (unsigned-byte-p size (logrev size n))
           (natp size)))

  (defthm logrev-of-loghead-same
    (equal (logrev size (loghead size i))
           (logrev size i))
    :hints(("Goal" :in-theory (enable* ihsext-inductions
                                       ihsext-recursive-redefs))))

  (defthm loghead-of-logrev-same
    (equal (loghead size (logrev size i))
           (logrev size i))
    :hints(("Goal"
            :in-theory (enable acl2::loghead-identity)
            :cases ((natp size)))))

  (defsection logbitp-of-logrev-split
    (local (defun my-ind (n size x)
             (if (or (zp n)
                     (zp size))
                 (list n size x)
               (my-ind (- n 1) (- size 1) (logcdr x)))))

    (local (defthm l0
             (implies (and (unsigned-byte-p size x)
                           (<= size (nfix n)))
                      (not (logbitp n x)))
             :hints(("Goal"
                     :induct (my-ind n size x)
                     :in-theory (enable* ihsext-recursive-redefs
                                         logcons-alt)))))

    (local (defthm l1
             (implies (unsigned-byte-p size x)
                      (not (logbitp size x)))
             :hints(("Goal"
                     :in-theory (disable l0)
                     :use ((:instance l0 (n size)))))))

    (local (defthm case-too-big
             (implies (>= (nfix n) (nfix size))
                      (equal (logbitp n (logrev size i))
                             nil))
             :hints(("Goal"
                     :in-theory (disable l0)
                     :use ((:instance l0
                                      (size (nfix size))
                                      (x (logrev size i))
                                      (n (nfix n))))))))

    (local (defthm case-in-bounds
             (implies (and (natp n)
                           (natp size)
                           (< n size))
                      (equal (logbitp n (logrev size i))
                             (logbitp (- size (+ 1 n)) i)))
             :hints(("Goal"
                     :induct (logrev size i)
                     :in-theory (enable* ihsext-inductions
                                         ihsext-recursive-redefs)))))

    (local (defthm better-in-bounds
             (implies (and (natp n)
                           (natp size))
                      (equal (logbitp n (logrev size i))
                             (and (< n size)
                                  (logbitp (- size (+ 1 n)) i))))))

    (defthmd logbitp-of-logrev-split
      (equal (logbitp n (logrev size i))
             (and (< (nfix n) (nfix size))
                  (logbitp (- (nfix size) (+ 1 (nfix n))) i)))
      :hints(("Goal"
              :in-theory (disable case-too-big
                                  case-in-bounds
                                  better-in-bounds)
              :use ((:instance better-in-bounds
                               (n (nfix n))
                               (size (nfix size)))))))))

(defsection plus

  (defthm +-of-logcons-with-cin
    (implies (bitp cin)
             (equal (+ cin
                       (logcons b1 r1)
                       (logcons b2 r2))
                    (logcons (b-xor cin (b-xor b1 b2))
                             (+ (b-ior (b-and cin b1)
                                       (b-ior (b-and cin b2)
                                              (b-and b1 b2)))
                                (ifix r1)
                                (ifix r2)))))
    :hints(("Goal" :in-theory (enable logcons b-ior b-and b-xor b-not bitp))))

  (defthm +-of-logcons
    (equal (+ (logcons b1 r1)
              (logcons b2 r2))
           (logcons (b-xor b1 b2)
                    (+ (b-and b1 b2)
                       (ifix r1)
                       (ifix r2))))
    :hints(("Goal" :use ((:instance +-of-logcons-with-cin
                          (cin 0))))))

  (defthm logcar-of-+
    (implies (and (integerp a)
                  (integerp b))
             (equal (logcar (+ a b))
                    (logxor (logcar a) (logcar b)))))

  (defthm logcdr-of-+
    (implies (and (integerp a)
                  (integerp b))
             (equal (logcdr (+ a b))
                    (+ (logcdr a) (logcdr b)
                       (b-and (logcar a) (logcar b)))))))



