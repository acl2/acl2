
; FGL - A Symbolic Simulation Framework for ACL2
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/floor-mod" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable unsigned-byte-p)))

(define scratch-nontagidx-p (x)
  (not (equal 0 (loghead 4 (nfix x))))
  ///
  (defthm scratch-nontagidx-p-implies
    (implies (and (scratch-nontagidx-p x)
                  (natp x))
             (not (equal (loghead 4 x) 0))))

  (defthm scratch-nontagidx-implies-linear
    (implies (scratch-nontagidx-p x)
             (<= 1 (loghead 4 x)))
    :hints(("Goal" :in-theory (enable nfix)))
    :rule-classes :linear)
  
  (defthm scratch-nontagidx-p-when-loghead
    (implies (not (equal (loghead 4 (nfix x)) 0))
             (scratch-nontagidx-p x)))

  (defthm scratch-nontagidx-p-implies-natp
    (implies (scratch-nontagidx-p x)
             (posp x))
    :rule-classes :compound-recognizer))

(define scratch-nontagidx-fix ((x scratch-nontagidx-p))
  :inline t
  :returns (new-x scratch-nontagidx-p :rule-classes (:rewrite
                                                     (:type-prescription
                                                      :typed-term new-x)))
  :prepwork ((local (in-theory (enable scratch-nontagidx-p))))
  :guard-hints (("goal" :in-theory (enable nfix)))
  (mbe :logic (let ((x (nfix x)))
                (if (equal 0 (loghead 4 x))
                    (logior 1 x)
                  x))
       :exec x)
  ///
  (defthm scratch-nontagidx-fix-when-scratch-nontagidx-p
    (implies (scratch-nontagidx-p x)
             (equal (scratch-nontagidx-fix x) x))
    :hints(("Goal" :in-theory (enable nfix))))

  (fty::deffixtype scratch-nontagidx :pred scratch-nontagidx-p :fix scratch-nontagidx-fix
    :equiv scratch-nontagidx-equiv :define t)

  (local (defthm unsigned-byte-p-of-1
           (implies (posp n)
                    (unsigned-byte-p n 1))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

  (local (defthm unsigned-byte-p-implies-natp-n
           (implies (unsigned-byte-p n x)
                    (natp n))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))
           :rule-classes :forward-chaining))

  (defthm unsigned-byte-p-of-scratch-nontagidx-fix
    (implies (and (unsigned-byte-p n x)
                  (not (equal n 0)))
             (unsigned-byte-p n (scratch-nontagidx-fix x)))))

(local
 (defthm loghead-of-plus-small-const
   (implies (and (syntaxp (and (quotep c) (quotep n)))
                 (natp c) (integerp x)
                 (< c (ash 1 (nfix n))))
            (equal (loghead n (+ c x))
                   (let ((sum (+ c (loghead n x))))
                     (if (< sum (ash 1 (nfix n)))
                         sum
                       (+ (- (ash 1 (nfix n))) sum)))))
   :hints(("Goal" :in-theory (e/d (loghead bitops::ash-is-expt-*-x)
                                  (acl2::simplify-mod-+-mod))
           :use ((:instance acl2::mod-+
                  (x c) (y x) (z (expt 2 (nfix n))))))
          (and stable-under-simplificationp
               '(:expand ((:with acl2::mod-redef
                           (MOD (+ C (MOD X (EXPT 2 (NFIX N))))
                                (EXPT 2 (NFIX N))))))))
   :otf-flg t))

(local (defthm expt-2-type-positive-int
         (implies (natp n)
                  (posp (expt 2 n)))
         :rule-classes :type-prescription))

(local
 (defthm loghead-of-minus-small-const
   (implies (and (syntaxp (and (quotep c) (quotep n)))
                 (acl2::negp c) (integerp x)
                 (< (- c) (ash 1 (nfix n))))
            (equal (loghead n (+ c x))
                   (let ((sum (+ c (loghead n x))))
                     (if (<= 0 sum)
                         sum
                       (+ (ash 1 (nfix n)) sum)))))
   :hints(("Goal" :in-theory (e/d (loghead bitops::ash-is-expt-*-x)
                                  (acl2::simplify-mod-+-mod
                                   acl2::cancel-mod-+-basic
                                   acl2::mod-=-0
                                   acl2::expt-type-prescription-integerp
                                   acl2::expt-type-prescription-positive
                                   acl2::expt-type-prescription-nonzero
                                   not))
           :use ((:instance acl2::mod-+
                  (x c) (y x) (z (expt 2 (nfix n)))))))
   :otf-flg t))






;; (defthm scratch-nontagidx-p-of-plus-1
;;   (implies (and (equal (loghead 4 n) 0)
;;                 (natp n))
;;            (scratch-nontagidx-p (+ 1 n)))
;;   :hints(("Goal" :in-theory (enable scratch-nontagidx-p))))
;;           ;; :expand ((loghead 4 (+ 1 n))
;;           ;;          (loghead 4 n)))))

;; (defthm scratch-nontagidx-p-of-plus-2
;;   (implies (and (equal (loghead 4 (+ 1 n)) 0)
;;                 (natp n))
;;            (scratch-nontagidx-p (+ 2 n)))
;;   :hints (("goal" :use ((:instance scratch-nontagidx-p-of-plus-1 (n (+ 1 n)))))))


(local (defthm loghead-bound-by-ash
         (implies (natp n)
                  (< (loghead n x) (ash 1 n)))
         :hints (("goal" :in-theory (enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))
         :rule-classes :linear))

(local (defthmd logapp-loghead-logtail
         (equal (logapp n (loghead n x) (logtail n x))
                (ifix x))))

(local (defthm loghead-plus-ash-times-logtail
         (implies (natp n)
                  (equal (+ (loghead n x) (* (ash 1 n) (logtail n x)))
                         (ifix x)))
         :hints (("goal" :use logapp-loghead-logtail
                  :in-theory (enable logapp bitops::ash-is-expt-*-x)))))


(local (defthm logior-loghead-ash-logtail
         (implies (natp n)
                  (equal (logior (loghead n x) (ash (logtail n x) n))
                         (ifix x)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs
                                            bitops::equal-logcons-strong
                                            acl2::arith-equiv-forwarding)))))

(local (defthmd compare-with-*-n
         (implies (and (integerp a) (integerp b) (integerp c) (integerp d) (integerp n)
                       (< 0 a) (< 0 c)
                       (<= a n) (<= c n))
                  (equal (< (+ a (* n b)) (+ c (* n d)))
                         (cond ((< b d) t)
                               ((< d b) nil)
                               (t (< a c)))))
         :hints ((and stable-under-simplificationp
                      '(:nonlinearp t)))))

  
(local (defthmd compare-split-loghead-logtail
         (implies (and (integerp a) (integerp b) (natp n))
                  (equal (< a b)
                         (cond ((< (logtail n a) (logtail n b)) t)
                               ((< (logtail n b) (logtail n a)) nil)
                               (t (< (loghead n a) (loghead n b))))))
         :hints (("goal" :use ((:instance compare-with-*-n
                                (a (+ 1 (loghead n a))) (b (logtail n a)) (n (ash 1 n))
                                (c (+ 1 (loghead n b))) (d (logtail n b))))
                  :in-theory (disable compare-with-*-n)))))

(local (defthm ash-of-+
         (implies (and (natp n) (integerp x) (integerp y))
                  (equal (ash (+ x y) n)
                         (+ (ash x n) (ash y n))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions bitops::ihsext-recursive-redefs)))))



(local (defthm disjoint-with-ash-by-unsigned-byte-p
         (implies (unsigned-byte-p n x);; (and (<= 0 (ifix x))
                  ;; (< (ifix x) (ash 1 n)))
                  (equal (logand x (ash y n)) 0))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm disjoint-with-ash-by-less
         (implies (and (<= 0 (ifix x))
                       (< (ifix x) (ash 1 n)))
                  (equal (logand x (ash y n)) 0))
         :hints (("goal" :use ((:instance disjoint-with-ash-by-unsigned-byte-p))
                  :cases ((natp n))
                  :in-theory (e/d* (unsigned-byte-p
                                    bitops::logtail**
                                    bitops::ash-is-expt-*-x)
                                   (disjoint-with-ash-by-unsigned-byte-p)))
                 (and stable-under-simplificationp
                      '(:in-theory (enable* ifix acl2::arith-equiv-forwarding))))))

(local (defthmd logior-of-disjoint
         (implies (equal (logand x y) 0)
                  (equal (logior x y) (+ (ifix x) (ifix y))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))


(local (defthm loghead-plus-ash-free
         (implies (and (natp n)
                       (equal y (loghead n x)))
                  (equal (+ y (ash (logtail n x) n))
                         (ifix x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))



  

(local (defthm collect-consts
         (implies (syntaxp (and (quotep c) (quotep d)))
                  (equal (equal (+ c x) (+ d y))
                         (equal (fix x) (+ (+ (- c) d) y))))))

(local (defthm logtail-zero-by-bound
         (implies (and (<= 0 (ifix x))
                       (< (ifix x) (ash 1 (nfix n))))
                  (equal (logtail n x) 0))
         :hints(("Goal" 
                 :in-theory (enable logtail
                                    bitops::ash-is-expt-*-x)))
         :otf-flg t))

(local (defthm loghead-identity-by-bound
         (implies (and (<= 0 (ifix x))
                       (< (ifix x) (ash 1 (nfix n))))
                  (equal (loghead n x) (ifix x)))
         :hints(("Goal" 
                 :in-theory (enable loghead
                                    bitops::ash-is-expt-*-x)))
         :otf-flg t))



(define scratch-nontagidx-to-index ((x scratch-nontagidx-p))
  :returns (index natp :rule-classes :type-prescription)
  :inline t
  :hooks (:fix)
  (b* ((x (scratch-nontagidx-fix x)))
    (+ (* 15 (ash x -4))
       (logand #xf x)
       -1))
  ///

  ;; (local (defthm upper-bound-loghead-4
  ;;          (< (loghead 4 x) 16)
  ;;          :hints(("Goal" :in-theory (enable loghead)))
  ;;          :rule-classes :linear))

  

  (defthm scratch-nontagidx-to-index-monotonic
    (iff (< (scratch-nontagidx-to-index x) (scratch-nontagidx-to-index y))
         (< (scratch-nontagidx-fix x) (scratch-nontagidx-fix y)))
    :hints (("goal" :use ((:instance compare-split-loghead-logtail
                           (a (scratch-nontagidx-fix x))
                           (b (scratch-nontagidx-fix y))
                           (n 4))))))

  (defthm scratch-nontagidx-to-index-equal
    (equal (equal (scratch-nontagidx-to-index x) (scratch-nontagidx-to-index y))
           (equal (scratch-nontagidx-fix x) (scratch-nontagidx-fix y)))
    :hints (("goal" :use ((:instance scratch-nontagidx-to-index-monotonic)
                          (:instance scratch-nontagidx-to-index-monotonic (x y) (y x)))
             :in-theory (disable scratch-nontagidx-to-index-monotonic
                                 scratch-nontagidx-to-index)))))



(define index-to-scratch-nontagidx ((x natp))
  :hooks (:fix)
  :returns (nontagidx scratch-nontagidx-p
                      :hints(("Goal" :in-theory (enable scratch-nontagidx-p))
                             (and stable-under-simplificationp
                                  '(:in-theory (enable loghead))))
                      :rule-classes (:rewrite
                                     (:type-prescription :typed-term nontagidx)))
  :inline t
  (b* ((x (lnfix x)))
    (logior (ash (floor x 15) 4)
            (+ (mod x 15) 1)))
  ///
  

  (defthm scratch-nontagidx-to-index-of-index-to-scratch-nontagidx
    (equal (scratch-nontagidx-to-index (index-to-scratch-nontagidx x))
           (nfix x))
    :hints (("goal" :in-theory (e/d (scratch-nontagidx-to-index)
                                    (index-to-scratch-nontagidx)))
            (and stable-under-simplificationp
                 '(:in-theory (enable )))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable bitops::logand-with-negated-bitmask)))
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable loghead logtail bitops::ash-is-expt-*-x)))
            ))

  (defthm index-to-scratch-nontagidx-of-scratch-nontagidx-to-index
    (equal (index-to-scratch-nontagidx (scratch-nontagidx-to-index x))
           (scratch-nontagidx-fix x))
    :hints (("goal" :use ((:instance scratch-nontagidx-to-index-equal
                           (x (index-to-scratch-nontagidx (scratch-nontagidx-to-index x)))
                           (y (scratch-nontagidx-fix x))))
             :in-theory (disable index-to-scratch-nontagidx
                                 scratch-nontagidx-to-index-equal))))

  (defthm index-to-scratch-nontagidx-monotonic
    (iff (< (index-to-scratch-nontagidx x) (index-to-scratch-nontagidx y))
         (< (nfix x) (nfix y)))
    :hints (("goal" :use ((:instance scratch-nontagidx-to-index-monotonic
                           (x (index-to-scratch-nontagidx x))
                           (y (index-to-scratch-nontagidx y))))
             :in-theory (disable scratch-nontagidx-to-index-monotonic
                                 index-to-scratch-nontagidx))))

  (defthm index-to-scratch-nontagidx-equal
    (equal (equal (index-to-scratch-nontagidx x) (index-to-scratch-nontagidx y))
           (equal (nfix x) (nfix y)))
    :hints (("goal" :use ((:instance scratch-nontagidx-to-index-equal
                           (x (index-to-scratch-nontagidx x))
                           (y (index-to-scratch-nontagidx y))))
             :in-theory (disable scratch-nontagidx-to-index-equal
                                 index-to-scratch-nontagidx))))

  (defthm index-to-scratch-nontagidx-of-scratch-nontagidx-to-index-plus-const
    (implies (posp n)
             (< (scratch-nontagidx-fix x)
                (index-to-scratch-nontagidx (+ n (scratch-nontagidx-to-index x)))))
    :hints(("Goal" :in-theory (disable index-to-scratch-nontagidx
                                       index-to-scratch-nontagidx-monotonic)
            :use ((:instance index-to-scratch-nontagidx-monotonic
                   (x (scratch-nontagidx-to-index x))
                   (y (+ n (scratch-nontagidx-to-index x)))))))
    :rule-classes :linear)

  (defthm index-to-scratch-nontagidx-of-scratch-nontagidx-to-index-minus-const
    (implies (and (acl2::negp n)
                  (< 0 (scratch-nontagidx-to-index x)))
             (< (index-to-scratch-nontagidx (+ n (scratch-nontagidx-to-index x)))
                (scratch-nontagidx-fix x)))
    :hints(("Goal" :in-theory (disable index-to-scratch-nontagidx
                                       index-to-scratch-nontagidx-monotonic)
            :use ((:instance index-to-scratch-nontagidx-monotonic
                   (x (+ n (scratch-nontagidx-to-index x)))
                   (y (scratch-nontagidx-to-index x))))))
    :rule-classes :linear)

  (local (in-theory (disable index-to-scratch-nontagidx)))

  (defthm scratch-nontagidx-to-index-<-const
    (implies (and (syntaxp (quotep c))
                  (natp c))
             (iff (< c (scratch-nontagidx-to-index x))
                  (< (index-to-scratch-nontagidx c) (scratch-nontagidx-fix x))))
    :hints (("goal" :use ((:instance scratch-nontagidx-to-index-monotonic
                           (x (index-to-scratch-nontagidx c))
                           (y x)))
             :in-theory (disable scratch-nontagidx-to-index-monotonic))))

  (defthm scratch-nontagidx-to-index->-const
    (implies (and (syntaxp (quotep c))
                  (natp c))
             (iff (> c (scratch-nontagidx-to-index x))
                  (> (index-to-scratch-nontagidx c) (scratch-nontagidx-fix x))))
    :hints (("goal" :use ((:instance scratch-nontagidx-to-index-monotonic
                           (y (index-to-scratch-nontagidx c))
                           (x x)))
             :in-theory (disable scratch-nontagidx-to-index-monotonic))))

  (defthm index-to-scratch-nontagidx-<-const
    (implies (and (syntaxp (quotep c))
                  (scratch-nontagidx-p c))
             (iff (< c (index-to-scratch-nontagidx x))
                  (< (scratch-nontagidx-to-index c) (nfix x))))
    :hints (("goal" :use ((:instance index-to-scratch-nontagidx-monotonic
                           (x (scratch-nontagidx-to-index c))
                           (y x)))
             :in-theory (disable index-to-scratch-nontagidx-monotonic))))

  (defthm index-to-scratch-nontagidx->-const
    (implies (and (syntaxp (quotep c))
                  (scratch-nontagidx-p c))
             (iff (> c (index-to-scratch-nontagidx x))
                  (> (scratch-nontagidx-to-index c) (nfix x))))
    :hints (("goal" :use ((:instance index-to-scratch-nontagidx-monotonic
                           (y (scratch-nontagidx-to-index c))
                           (x x)))
             :in-theory (disable index-to-scratch-nontagidx-monotonic)))))




(define scratch-decr-nontagidx ((x scratch-nontagidx-p))
  :hooks (:fix)
  :guard (not (eql x 1))

  :returns (prev-x scratch-nontagidx-p
                   :rule-classes (:rewrite
                                  (:type-prescription :typed-term prev-x)))
  (b* ((x (scratch-nontagidx-fix x))
       (mod (logand #xf x)))
    (if (eql mod 1)
        (mbe :logic (if (eql x 1) 1 (- x 2))
             :exec (- x 2))
      (- x 1)))
  ///
  (defret scratch-decr-nontagidx-less-strict
    (implies (not (equal (scratch-nontagidx-fix x) 1))
             (< prev-x (scratch-nontagidx-fix x)))
    :rule-classes ((:linear :trigger-terms (prev-x))))

  (defret scratch-decr-nontagidx-less-nonstrict
    (<= prev-x (scratch-nontagidx-fix x))
    :rule-classes ((:linear :trigger-terms (prev-x))))

  (defret unsigned-byte-p-of-<fn>
    (implies (unsigned-byte-p n (scratch-nontagidx-fix x))
             (unsigned-byte-p n prev-x))
    :hints (("goal" :in-theory (e/d (unsigned-byte-p)
                                    (<fn>)))))


  (local (defthm logtail-lower-bound-when-loghead-not-1
           (implies (and (equal (loghead n x) 1)
                         (not (equal x 1))
                         (natp x)
                         (natp n))
                    (<= 1 (logtail n x)))
           :hints (("goal" :use ((:instance logapp-loghead-logtail))))
           :rule-classes :linear))

  (defthm scratch-decr-nontagidx-in-terms-of-conversions
    (equal (scratch-decr-nontagidx x)
           (index-to-scratch-nontagidx
            (+ -1 (scratch-nontagidx-to-index x))))
    :hints(("Goal" :in-theory (enable scratch-nontagidx-to-index
                                      index-to-scratch-nontagidx
                                      logior-of-disjoint))))

  (defthm scratch-decr-nontagidx-gte-when-was-greater
    (implies (and (< x (scratch-nontagidx-fix y))
                  (scratch-nontagidx-p x))
             (<= x (scratch-decr-nontagidx y)))
    :hints (("goal" :in-theory (disable scratch-decr-nontagidx
                                        index-to-scratch-nontagidx-monotonic
                                        scratch-nontagidx-to-index-monotonic)
             :use ((:instance index-to-scratch-nontagidx-monotonic
                    (y (+ -1 (scratch-nontagidx-to-index y)))
                    (x (scratch-nontagidx-to-index x)))
                   (:instance scratch-nontagidx-to-index-monotonic
                    (x x) (y y)))))
    :rule-classes (:rewrite :linear)))

(define scratch-incr-nontagidx ((x scratch-nontagidx-p))
  :hooks (:fix)
  :returns (next-x scratch-nontagidx-p
                   ;; :hints(("Goal" :in-theory (e/d (loghead)
                   ;;                                (acl2::mod-=-0))))
                   :rule-classes (:rewrite
                                  (:type-prescription :typed-term next-x)))
  (b* ((x (scratch-nontagidx-fix x))
       (mod (logand #xf x)))
    (if (eql mod #xf)
        (+ x 2)
      (+ x 1)))
  ///
  (defret scratch-incr-nontagidx-greater-strict
    (< (scratch-nontagidx-fix x) next-x)
    :rule-classes (:rewrite (:linear :trigger-terms (next-x))))

  (defthm scratch-incr-nontagidx-in-terms-of-conversions
    (equal (scratch-incr-nontagidx x)
           (index-to-scratch-nontagidx
            (+ 1 (scratch-nontagidx-to-index x))))
    :hints(("Goal" :in-theory (e/d (scratch-nontagidx-to-index
                                    index-to-scratch-nontagidx
                                    logior-of-disjoint)
                                   (ash-of-+)))
           (and stable-under-simplificationp
                '(:in-theory (enable ash-of-+)))))
  
  (defthm scratch-decr-nontagidx-of-scratch-incr-nontagidx
    (equal (scratch-decr-nontagidx (scratch-incr-nontagidx x))
           (scratch-nontagidx-fix x))
    :hints(("Goal" :in-theory (disable scratch-incr-nontagidx)))))

(local (defthm floor-nonneg
         (implies (and (natp x) (natp y))
                  (natp (floor x y)))
         :hints(("Goal" :in-theory (enable floor)))
         :rule-classes :type-prescription))

;; (local (include-book "std/util/termhints" :dir :system))


(define scratch-nontagidx-offset ((x scratch-nontagidx-p)
                                  (offset integerp))
  :returns (new-x scratch-nontagidx-p
                  :hints(("Goal" :in-theory (disable ash-of-+)))
                  :rule-classes (:rewrite (:type-prescription :typed-term new-x)))
  :guard (<= (- offset) (scratch-nontagidx-to-index x))
  :guard-hints (("goal" :in-theory (enable scratch-nontagidx-to-index))
                (and stable-under-simplificationp
                     '(:use ((:instance loghead-plus-ash-times-logtail
                              (n 4) (x x))
                             (:instance acl2::floor-mod-elim
                              (x offset) (y 15)))
                       :in-theory (disable loghead-plus-ash-times-logtail
                                           acl2::floor-mod-elim))))
  (b* ((x (scratch-nontagidx-fix x))
       (offset (lifix offset))
       (x-upper (ash x -4))
       (x-lower (logand #xf x))
       (offs-upper (floor offset 15))
       (offs-lower (mod offset 15))
       (lower-sum (+ x-lower offs-lower))
       (overflow (< 15 lower-sum))
       (upper (+ offs-upper x-upper (if overflow 1 0)))
       ((unless (mbt (<= 0 upper)))
        ;;(acl2::hintcontext :bad 1)
        1))
    ;; (acl2::hintcontext :good
    (logior (ash upper 4)
            (+ lower-sum (if overflow -15 0))))
  ///
  (set-ignore-ok t)

  (local (defthm mod-cancel-lemma
           (implies (and (real/rationalp a)
                         (real/rationalp b)
                         (real/rationalp c)
                         (integerp d)
                         (real/rationalp y)
                         (not (equal y 0)))
                    (equal (mod (+ a b c (* y d)) y)
                           (mod (+ a b c) y)))
           :hints (("goal" :use ((:instance acl2::cancel-mod-+-basic
                                  (i d) (x (* y d)) (y (+ a b c)) (z y)))
                    :in-theory (disable acl2::cancel-mod-+-basic)))))

  (local (defthm floor-cancel-lemma
           (implies (and (real/rationalp a)
                         (real/rationalp b)
                         (real/rationalp c)
                         (integerp d)
                         (real/rationalp y)
                         (not (equal y 0)))
                    (equal (floor (+ a b c (* y d)) y)
                           (+ d (floor (+ a b c) y))))
           :hints (("goal" :use ((:instance acl2::cancel-floor-+-basic
                                  (i d) (x (* y d)) (y (+ a b c)) (z y)))
                    :in-theory (disable acl2::cancel-floor-+-basic)))))

  (local (defthmd mod-15-plus-ash-floor-4
           (implies (integerp x)
                    (equal (+ (mod x 15) (ash (floor x 15) 4))
                           (+ x (floor x 15))))
           :hints (("goal" :use ((:instance acl2::floor-mod-elim (y 15)))
                    :in-theory (e/d (bitops::ash-is-expt-*-x)
                                    (acl2::floor-mod-elim))))))

  (local (in-theory (disable ;; acl2::floor-bounded-by-/
                             acl2::zip-open
                             acl2::ash-0
                             acl2::nfix-positive-to-non-zp)))

  (defthm scratch-nontagidx-offset-in-terms-of-conversions
    (equal (scratch-nontagidx-offset x offset)
           (index-to-scratch-nontagidx
            (+ (ifix offset) (scratch-nontagidx-to-index x))))
    :hints(("Goal" :in-theory (e/d (logior-of-disjoint
                                    index-to-scratch-nontagidx
                                    scratch-nontagidx-to-index)
                                   (ash-of-+)))
           (and stable-under-simplificationp
                `(:computed-hint-replacement
                     ((and stable-under-simplificationp
                           '(:in-theory (e/d (mod-15-plus-ash-floor-4)
                                             (acl2::floor-mod-elim)))))
                     :use ((:instance acl2::floor-mod-elim
                            (x (ifix offset))
                            (y 15)))
                     :in-theory (disable acl2::floor-mod-elim)))
           ;; (acl2::function-termhint
           ;;  scratch-nontagidx-offset
           ;;  (:bad `(:use ((:instance acl2::mark-clause-is-true (x :bad))
           ;;                (:instance acl2::floor-mod-elim
           ;;                 (x (ifix offset))
           ;;                 (y 15)))
           ;;          :in-theory (e/d (nfix) (acl2::floor-mod-elim))))
           ;;  (:good `(:computed-hint-replacement
           ;;           ((and stable-under-simplificationp
           ;;                 '(:in-theory (e/d (mod-15-plus-ash-floor-4)
           ;;                                   (acl2::floor-mod-elim)))))
           ;;           :use ((:instance acl2::mark-clause-is-true (x :good))
           ;;                 (:instance acl2::floor-mod-elim
           ;;                  (x (ifix offset))
           ;;                  (y 15)))
           ;;           :in-theory (disable acl2::floor-mod-elim))))
           )
    :otf-flg t))
