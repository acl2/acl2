; Copyright (C) Intel Corporation
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
;;; Original Author(s): Sol Swords <sol.swords@intel.com>

(in-package "IFP")
(include-book "fp-common")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/floor" :dir :system))
(local (include-book "centaur/bitops/integer-length" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p
                           signed-byte-p
                           logmask
                           (tau-system)))))

(local (std::add-default-post-define-hook :fix))

(local
 (defthm floor-natp
   (implies (and (natp x) (natp y))
            (natp (floor x y)))
   :hints (("Goal" :in-theory (enable floor)))
   :rule-classes :type-prescription))

(local
 (defsection floor-lemmas
   (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
   ;; (local (include-book "centaur/bitops/floor-mod" :Dir :System))

   (defthmd floor-bounded-by-/
     (implies (and (rationalp x) (rationalp y) (<= 0 x) (< 0 y))
              (<= (floor x y) (/ x y)))
     :rule-classes ((:linear :trigger-terms ((floor x y)
                                             (/ x y)))))

   (defthmd floor-upper-bound
     (implies (and (rationalp x) (rationalp y) (<= 0 x) (< 0 y))
              (< (+ -1 (/ x y)) (floor x y)))
     :rule-classes ((:linear :trigger-terms ((floor x y)
                                             (/ x y)))))
   ))

(define fp-divide-arith-num/div ((x fp-arith-triple-p)
                                 (y fp-arith-triple-p)
                                 &key
                                 ((size fp-size-p) 'size))
  :guard (not (equal (fp-arith-triple->man y) 0))
  :returns (mv (num natp :rule-classes :type-prescription)
               (div natp :rule-classes :type-prescription))
  :prepwork ((local (defthm fp-arith-leftshift-when-zp
                      (implies (zp n)
                               (equal (fp-arith-leftshift x n)
                                      (fp-arith-triple-fix x)))
                      :hints (("Goal" :in-theory (enable fp-arith-leftshift))))))
  (b* (((fp-arith-triple x))
       ((fp-arith-triple y))
       ((fp-size size))

       ;; We need the quotient to be at least size.frac-size+2 bits long.  From
       ;; 'integer-length-of-floor' in centaur/bitops/floor.lisp we have
       ;; (integer-length (floor a b)) >= (- (integer-length a) (integer-length b)).
       ;; So we need to left-shift x make its integer-length fracsize+2+ysize.
       (leftshift (- (+ 2 size.frac-size (integer-length y.man))
                     (integer-length x.man)))
       ((fp-arith-triple x-shift)
        ;; If leftshift were somehow negative, it would just mean x is big
        ;; enough already and doesn't need to be left-shifted more.  But
        ;; fp-arith-leftshift won't shift right anyway so we'll just use that
        ;; unconditionally (at least logically).
        (mbe :logic (fp-arith-leftshift x leftshift)
             :exec
             (if (< leftshift 0)
                 x ;; x is big enough, no need to leftshift
               (fp-arith-leftshift x leftshift)))))
    (mv x-shift.man y.man))
  ///
  (defret <fn>-div-nonzero
    (implies (not (equal (fp-arith-triple->man y) 0))
             (> div 0))
    :rule-classes :linear))

(define fp-divide-arith-man/sticky ((x fp-arith-triple-p)
                                    (y fp-arith-triple-p)
                                    &key
                                    ((size fp-size-p) 'size))
  :guard (not (equal (fp-arith-triple->man y) 0))
  :returns (mv (man natp :rule-classes :type-prescription)
               (stickyp booleanp))

  (b* (((mv num div) (fp-divide-arith-num/div x y))
       (new-man (floor num div))
       (stickyp (not (eql 0 (mod num div)))))
    (mv new-man stickyp)))

(define fp-divide-arith ((x fp-arith-triple-p)
                         (y fp-arith-triple-p)
                         &key
                         ((size fp-size-p) 'size) ;; really just need the frac size
                         ((override-man acl2::maybe-posp) 'nil)
                         ((override-stickyp booleanp) 'nil)) ;; only used if override-man
  :returns (mv (ans fp-arith-triple-p)
               (stickyp booleanp))
  :guard (not (equal (fp-arith-triple->man y) 0))

  :prepwork ((local (defthm fp-arith-leftshift-when-zp
                      (implies (zp n)
                               (equal (fp-arith-leftshift x n)
                                      (fp-arith-triple-fix x)))
                      :hints (("Goal" :in-theory (enable fp-arith-leftshift)))))
             (local (in-theory (enable fp-divide-arith-man/sticky)))
             (local (in-theory (enable fp-divide-arith-num/div)))
             (local (in-theory (disable not))))
  (b* (((fp-arith-triple x))
       ((fp-arith-triple y))
       ((fp-size size))

       ;; We need the quotient to be at least size.frac-size+2 bits long.  From
       ;; 'integer-length-of-floor' in centaur/bitops/floor.lisp we have
       ;; (integer-length (floor a b)) >= (- (integer-length a) (integer-length b)).
       ;; So we need to left-shift x make its integer-length fracsize+2+ysize.
       (leftshift (- (+ 2 size.frac-size (integer-length y.man))
                     (integer-length x.man)))
       ((fp-arith-triple x-shift)
        ;; If leftshift were somehow negative, it would just mean x is big
        ;; enough already and doesn't need to be left-shifted more.  But
        ;; fp-arith-leftshift won't shift right anyway so we'll just use that
        ;; unconditionally (at least logically).
        (mbe :logic (fp-arith-leftshift x leftshift)
             :exec
             (if (< leftshift 0)
                 x ;; x is big enough, no need to leftshift
               (fp-arith-leftshift x leftshift))))

       ((mv new-man stickyp)
        (if override-man
            (mv (lposfix override-man)
                (mbe :logic (acl2::bool-fix override-stickyp)
                     :exec override-stickyp))
          (mbe :logic (fp-divide-arith-man/sticky x y)
               :exec (mv (floor x-shift.man y.man)
                         (not (eql 0 (mod x-shift.man y.man)))))))
       (new-exp (- x-shift.exp y.exp))
       (new-sign (b-xor x-shift.sign y.sign)))

    (mv (make-fp-arith-triple :man new-man
                              :exp new-exp
                              :sign new-sign)
        stickyp))
  ///
  (local (defthm fp-arith-triple->man-of-fp-arith-leftshift
           (equal (fp-arith-triple->man (fp-arith-leftshift x n))
                  (ash (fp-arith-triple->man x) (nfix n)))
           :hints (("Goal" :in-theory (enable fp-arith-leftshift)))))

  (defret integer-length-of-<fn>
    (implies (and (not (equal 0 (fp-arith-triple->man x)))
                  (not (equal 0 (fp-arith-triple->man y)))
                  (not override-man))
             (<= (+ 2 (fp-size->frac-size size))
                 (integer-length (fp-arith-triple->man ans))))
    :hints (("Goal" :in-theory (enable bitops::integer-length-of-floor nfix)
             :do-not-induct t
             :use ((:instance bitops::integer-length-monotonic
                              (j (fp-arith-triple->man y))
                              (i (ash (fp-arith-triple->man x)
                                      (nfix
                                       (+ 2 (fp-size->frac-size size)
                                          (- (integer-length (fp-arith-triple->man x)))
                                          (integer-length (fp-arith-triple->man y))))))))))
    :otf-flg t)

  (local (defthm floor-when-mod-equal-0
           (implies (and (equal 0 (mod x y))
                         (not (equal 0 (fix y))))
                    (equal (floor x y) (/ x y)))
           :hints (("Goal" :in-theory (enable mod)))))

  (local (defthm fp-arith-triple->exp-of-fp-arith-leftshift
           (equal (fp-arith-triple->exp (fp-arith-leftshift x n))
                  (- (fp-arith-triple->exp x) (nfix n)))
           :hints (("Goal" :in-theory (enable fp-arith-leftshift)))))

  (defret <fn>-correct-when-exact
    (implies (and (not stickyp)
                  (not override-man)
                  ;; (not (equal 0 (fp-arith-triple->man x)))
                  (not (equal 0 (fp-arith-triple->man y))))
             (equal (fp-arith-triple->rational ans)
                    (/ (fp-arith-triple->rational x)
                       (fp-arith-triple->rational y))))
    :hints (("Goal" :in-theory (enable fp-arith-triple->rational
                                       b-xor
                                       nfix
                                       bitops::ash-is-expt-*-x))))

  (local (in-theory (enable floor-bounded-by-/
                            floor-upper-bound)))

  (local (defthm something-times-floor-upper-bound
           (implies (and (rationalp x) (rationalp y) (<= 0 x) (< 0 y)
                         (rationalp a) (<= 0 a))
                    (<= (* a (floor x y)) (* x (/ y) a)))
           ;; :hints (("Goal" :use floor-bounded-by-/
           ;;          :in-theory (disable floor-bounded-by-/)))
           :rule-classes ((:linear :trigger-terms ((* a (floor x y))
                                                   (* x (/ y) a))))))

  (local (defthm something-times-floor-lower-bound
           (implies (and (rationalp x) (rationalp y) (<= 0 x) (< 0 y)
                         (rationalp a) (< 0 a))
                    (< (* x (/ y) a) (+ a (* a (floor x y)))))
           :hints (("Goal" :use floor-upper-bound
                    :in-theory (disable floor-upper-bound))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))
           :rule-classes ((:linear :trigger-terms ((* a (floor x y))
                                                   (* x (/ y) a))))))

  (local (in-theory (disable something-times-floor-lower-bound
                             something-times-floor-upper-bound)))

  (local (defthm two-things-times-floor-upper-bound
           (implies (and (rationalp x) (rationalp y) (<= 0 x) (< 0 y)
                         (rationalp a) (rationalp b)
                         (<= 0 (* a b)))
                    (<= (* a b (floor x y))
                        (* x (/ y) a b)))
           :hints (("Goal" :use ((:instance something-times-floor-upper-bound
                                            (a (* a b))))
                    :in-theory (disable something-times-floor-upper-bound)))
           :rule-classes ((:linear :trigger-terms ((* a b (floor x y)))))))

  (local (defthm two-things-times-floor-lower-bound
           (implies (and (rationalp x) (rationalp y) (<= 0 x) (< 0 y)
                         (rationalp a) (rationalp b)
                         (< 0 (* a b)))
                    (< (+ (- (* a b))
                          (* x (/ y) a b))
                       (* a b (floor x y))))
           :hints (("Goal" :use ((:instance something-times-floor-lower-bound
                                            (a (* a b))))
                    :in-theory (disable something-times-floor-lower-bound)))
           :rule-classes ((:linear :trigger-terms ((* a b (floor x y))
                                                   (* x (/ y) a b)
                                                   )))))

  (local (defthm five-things-times-floor-upper-bound
           (implies (and (rationalp x) (rationalp y) (<= 0 x) (< 0 y)
                         (rationalp a) (rationalp b) (rationalp c) (rationalp d) (rationalp e)
                         (<= 0 (* a b c d e)))
                    (<= (* a b c d e (floor x y))
                        (* x (/ y) a b c d e)))
           :hints (("Goal" :use ((:instance something-times-floor-upper-bound
                                            (a (* a b c d e))))
                    :in-theory (disable something-times-floor-upper-bound)))
           :rule-classes ((:linear :trigger-terms ((* a b c d e (floor x y)))))))

  (local (defthm five-things-times-floor-lower-bound
           (implies (and (rationalp x) (rationalp y) (<= 0 x) (< 0 y)
                         (rationalp a) (rationalp b) (rationalp c) (rationalp d) (rationalp e)
                         (< 0 (* a b c d e)))
                    (< (+ (- (* a b c d e))
                          (* x (/ y) a b c d e))
                       (* a b c d e (floor x y))))
           :hints (("Goal" :use ((:instance something-times-floor-lower-bound
                                            (a (* a b c d e))))
                    :in-theory (disable something-times-floor-lower-bound)))
           :rule-classes ((:linear :trigger-terms ((* a b c d e (floor x y)))))))

  (defret <fn>-correct-general
    (b* ((exact (/ (fp-arith-triple->rational x)
                   (fp-arith-triple->rational y))))
      (implies (and (not (equal 0 (fp-arith-triple->man x)))
                    (not (equal 0 (fp-arith-triple->man y)))
                    (not override-man))
               (and (implies (<= 0 exact)
                             (and (<= (fp-arith-triple->rational ans) exact)
                                  (< exact (fp-arith-triple->rational
                                            (fp-arith-triple-incr ans)))))
                    (implies (< exact 0)
                             (and (>= (fp-arith-triple->rational ans) exact)
                                  (> exact (fp-arith-triple->rational
                                            (fp-arith-triple-incr ans))))))))
    :hints (("Goal" :in-theory (enable fp-arith-triple->rational
                                       fp-arith-triple-incr
                                       b-xor
                                       nfix
                                       bitops::ash-is-expt-*-x))))

  (defret <fn>-mantissa-nonzero
    (implies (and (not (equal 0 (fp-arith-triple->man x)))
                  (not (equal 0 (fp-arith-triple->man y)))
                  (acl2::maybe-posp override-man))
             (< 0 (fp-arith-triple->man ans)))
    :hints (("Goal"
             :use ((:instance integer-length-of-<fn>))
             :in-theory (disable integer-length-of-<fn> <fn>))
            (and stable-under-simplificationp
                 '(:expand ((fp-divide-arith x y
                                             :override-man override-man
                                             :override-stickyp override-stickyp)))))
    :rule-classes :linear)

  (local (defthm posp-by-integer-length
           (implies (and (< 0 (integer-length x))
                         (natp x))
                    (posp x))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))))

  (defret <fn>-override-correct
    :pre-bind (((mv override-man override-stickyp)
                (fp-divide-arith-man/sticky x y)))
    (implies (and (not (equal 0 (fp-arith-triple->man x)))
                  (not (equal 0 (fp-arith-triple->man y))))
             (b* (((mv spec-ans spec-stickyp)
                   (fp-divide-arith x y :override-man nil :override-stickyp nil)))
               (and (equal ans spec-ans)
                    (equal stickyp spec-stickyp))))
    :hints (("Goal" :use ((:instance integer-length-of-<fn>
                                     (override-man nil) (override-stickyp nil)))
             :in-theory '(<fn>
                          fp-arith-triple->man-of-fp-arith-triple
                          posp-by-integer-length
                          acl2::pos-fix-when-posp
                          lposfix
                          acl2::nfix-when-natp
                          natp-of-fp-divide-arith-man/sticky.man
                          acl2::natp-compound-recognizer
                          acl2::posp-compound-recognizer
                          posp-of-fp-size->frac-size
                          (:t integer-length)
                          acl2::bool-fix-when-booleanp
                          booleanp-of-fp-divide-arith-man/sticky.stickyp))))

  (local (in-theory (enable acl2::maybe-posp-fix))))
