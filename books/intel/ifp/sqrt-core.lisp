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
(include-book "centaur/bitops/int-sqrt" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/floor" :dir :system))
(local (include-book "centaur/bitops/integer-length" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/misc/collect-like-terms" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p
                           signed-byte-p
                           logmask
                           (tau-system)))))

(local (std::add-default-post-define-hook :fix))



(local (defthm logbitp-integer-length-minus-1
         (implies (and (integerp x)
                       (not (equal 0 x))
                       (not (equal -1 x)))
                  (equal (logbitp (+ -1 (integer-length x)) x)
                         (< 0 x)))
         :hints (("Goal"
                  :induct (integer-length x)
                  :in-theory (e/d* (bitops::ihsext-inductions))
                  :expand ((integer-length x)
                           (:free (i) (logbitp i x)))))))

(local
 (defthm ash-by-minus-integer-length-plus-offset
   (implies (and (posp x)
                 (posp offset))
            (not (equal 0 (ash x (+ offset (- (integer-length x)))))))
   :hints (("Goal"
            :use ((:instance bitops::logbitp-of-ash-in-range
                             (count (+ offset (- (integer-length x))))
                             (pos (+ -1 offset))
                             (i x)))
            :in-theory (disable bitops::logbitp-of-ash-in-range)))))

(local
 (defthm ash-nonneg-nonzero
   (implies (and (posp x)
                 (natp offset))
            (not (equal 0 (ash x offset))))
   :hints (("Goal"
            :use ((:instance bitops::logbitp-of-ash-in-range
                             (count offset)
                             (pos (+ -1 offset (integer-length x)))
                             (i x)))
            :in-theory (disable bitops::logbitp-of-ash-in-range)))))


(define fp-sqrt-arith-input-man ((x fp-arith-triple-p)
                                 &key
                                 ((size fp-size-p) 'size))
  :guard (not (equal (fp-arith-triple->man x) 0))
  :returns (mant natp :rule-classes :type-prescription)
  :prepwork ((local (defthm fp-arith-leftshift-when-zp
                      (implies (zp n)
                               (equal (fp-arith-leftshift x n)
                                      (fp-arith-triple-fix x)))
                      :hints (("Goal" :in-theory (enable fp-arith-leftshift))))))
  (b* (((fp-arith-triple x))
       ((fp-size size))

       ;; x.value = x.man * 2^(x.exp)
       ;; sqrt(x.value) =  sqrt(x.man) * 2^(x.exp / 2)
       ;;          if x.exp is even:
       ;;               =  sqrt(x.man) * 2^(x.exp >> 1)
       ;;          if x.exp is odd:
       ;;               =  sqrt(2*x.man) * 2^(x.exp >> 1).

       ;; Call the quantity inside the sqrt (in both cases) the base-mant.
       ;; We need to get a square root approximation for the base-mant of size.frac-size+2 bits (one for the round bit).
       ;; This is the int-sqrt of some power of 2 times the base-mant.
       ;; n bit values range from 2^(n-1) to (2^n)-1.
       ;; Because (2^(n-1))^2 = 2^(2n-2) and ((2^n)-1)^2 < 2^2n,
       ;; the bit width of the int-sqrt of a 2n-1 or 2n-bit value is n -- also, integer-length-of-int-sqrt says
       ;; len(int-sqrt(x)) = (len(x)+1)>>1. So we need to shift base-mant to be size 2n-1, i.e.
       ;; 2*fracsize + 3, or 2n, i.e. 2*fracsize+4.
       ;; The other criterion is that we want to end up with an even exponent.
       ;; This means we shift by 2*fracsize + 3 - len(x.man), plus one if lsb(x.exp)==lsb(len(x.man)).

       ;; Doing the sum for the shift amount in this order because when x.man
       ;; is constrained to be normal, the subtraction will be constant, which
       ;; is probably better for symbolic simulation.
       (man-len (integer-length x.man))
       (leftshift (+ (- (+ 3 (* 2 size.frac-size)) man-len)
                     (b-eqv (logcar x.exp) (logcar man-len))))
       ;; If somehow this is less than 0, it means the mantissa is so long that
       ;; it doesn't need to be shifted.  But we still want an even exponent,
       ;; so just shift by (logcar x.exp).
       (leftshift (if (<= 0 leftshift) leftshift (logcar x.exp))))
    (ash x.man leftshift))
  ///
  (defret <fn>-mant-nonzero
    (implies (not (equal (fp-arith-triple->man x) 0))
             (> mant 0))
    :hints (("Goal" :use ((:instance ash-by-minus-integer-length-plus-offset
                                     (x (fp-arith-triple->man x))
                                     (offset (+ 3 (b-eqv (logcar (fp-arith-triple->exp x))
                                                         (logcar (integer-length (fp-arith-triple->man x))))
                                                (* 2 (fp-size->frac-size size))))))))
    :rule-classes :linear))


(define fp-sqrt-arith-man/sticky ((x fp-arith-triple-p)
                                  &key
                                  ((size fp-size-p) 'size))
  :guard (not (equal (fp-arith-triple->man x) 0))
  :returns (mv (man natp :rule-classes :type-prescription)
               (stickyp booleanp))

  (b* ((in-mant (fp-sqrt-arith-input-man x))
       ((mv sqrt rem) (bitops::int-sqrt/rem in-mant))
       (stickyp (not (eql 0 rem))))
    (mv sqrt stickyp)))


(define fp-sqrt-arith ((x fp-arith-triple-p)
                       &key
                       ((size fp-size-p) 'size) ;; really just need the frac size
                       ((override-man acl2::maybe-posp) 'nil)
                       ((override-stickyp booleanp) 'nil)) ;; only used if override-man
  :returns (mv (ans fp-arith-triple-p)
               (stickyp booleanp))
  :guard (not (equal (fp-arith-triple->man x) 0))
  :prepwork ((local (defthm fp-arith-leftshift-when-zp
                      (implies (zp n)
                               (equal (fp-arith-leftshift x n)
                                      (fp-arith-triple-fix x)))
                      :hints (("Goal" :in-theory (enable fp-arith-leftshift)))))
             (local (in-theory (enable fp-sqrt-arith-man/sticky)))
             (local (in-theory (enable fp-sqrt-arith-input-man)))
             (local (in-theory (disable not)))
             (local (defthm fp-arith-triple->man-of-fp-arith-leftshift
                      (equal (fp-arith-triple->man (fp-arith-leftshift x n))
                             (ash (fp-arith-triple->man x) (nfix n)))
                      :hints (("Goal" :in-theory (enable fp-arith-leftshift))))))
  (b* (((fp-arith-triple x))
       ((fp-size size))


       ;; See the comment above in fp-sqrt-arith-input-man.
       (man-len (integer-length x.man))
       (leftshift (+ (- (+ 3 (* 2 size.frac-size)) man-len)
                     (b-eqv (logcar x.exp) (logcar man-len))))
       (leftshift (if (<= 0 leftshift) leftshift (logcar x.exp)))
       ((fp-arith-triple x-shift)
        ;; If leftshift were somehow negative, it would just mean x is big
        ;; enough already and doesn't need to be left-shifted more.  But
        ;; fp-arith-leftshift won't shift right anyway so we'll just use that
        ;; unconditionally (at least logically).
        (fp-arith-leftshift x leftshift))

       ((mv new-man stickyp)
        (if override-man
            (mv (lposfix override-man)
                (mbe :logic (acl2::bool-fix override-stickyp)
                     :exec override-stickyp))
          (mbe :logic (fp-sqrt-arith-man/sticky x)
               :exec (b* (((mv sqrt rem)
                           (bitops::int-sqrt/rem x-shift.man)))
                       (mv sqrt (not (eql 0 rem)))))))
       ;; Shifted exponent
       (new-exp (ash x-shift.exp -1))
       (new-sign 0))

    (mv (make-fp-arith-triple :man new-man
                              :exp new-exp
                              :sign new-sign)
        stickyp))
  ///

  (local (defthmd logcdr-arith
           (equal (logcdr x) (* 1/2 (- (ifix x) (logcar x))))
           :hints (("Goal"
                    :use ((:instance acl2::logcar-logcdr-elim
                                     (i (ifix x))))
                    :in-theory (e/d (logcons)
                                    (bitops::logcons-destruct))))))

  (local (defthm logxor-of-bits
           (implies (and (bitp a) (bitp b))
                    (equal (logxor a b)
                           (b-xor a b)))))

  (local (defthmd b-not-is-sub
           (equal (b-not a)
                  (- 1 (bfix a)))
           :hints (("Goal" :in-theory (enable b-not)))))

  (defret integer-length-of-<fn>
    (implies (and (not (equal 0 (fp-arith-triple->man x)))
                  (not override-man))
             (<= (+ 2 (fp-size->frac-size size))
                 (integer-length (fp-arith-triple->man ans))))
    :hints (("Goal"
             :in-theory (enable nfix)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((equal 1 (logcar (integer-length (fp-arith-triple->man x)))))
                          :in-theory (enable logcdr-arith b-not-is-sub))))
    :otf-flg t)

  (local (defthm fp-arith-triple->exp-of-fp-arith-leftshift
           (equal (fp-arith-triple->exp (fp-arith-leftshift x n))
                  (- (fp-arith-triple->exp x) (nfix n)))
           :hints (("Goal" :in-theory (enable fp-arith-leftshift)))))


  (local (defthm int-sqrt-dumb-elim
           (implies (equal x (* (bitops::int-sqrt x) (bitops::int-sqrt x)))
                    (equal (* (bitops::int-sqrt x) (bitops::int-sqrt x) zz)
                           (* x zz)))))

  (local (defthm b-xor-a-a-b
           (equal (b-xor a (b-xor a b))
                  (bfix b))
           :hints (("Goal" :in-theory (enable b-xor)))))

  (local (defthm b-xor-a-b-a
           (equal (b-xor a (b-xor b a))
                  (bfix b))
           :hints (("Goal" :in-theory (enable b-xor)))))

  (local (defthm b-and-a-b-xor-a-b
           (equal (b-and a (b-xor a b))
                  (b-and a (b-not b)))
           :hints (("Goal" :in-theory (enable b-and b-xor)))))

  (local (defthm b-and-a-b-xor-b-a
           (equal (b-and a (b-xor b a))
                  (b-and a (b-not b)))
           :hints (("Goal" :in-theory (enable b-and b-xor)))))

  (local (defthmd collect-exponents
           (implies (and (integerp i) (integerp j) (acl2-numberp r)
                         (not (equal 0 r)))
                    (and (equal (* (expt r i) (expt r j))
                                (expt r (+ i j)))
                         (equal (* (expt r i) (expt r j) c)
                                (* (expt r (+ i j)) c))))))

  (local (defthm logcdr-minus-bit
           (implies (bitp b)
                    (equal (logcdr (- b)) (- b)))
           :hints (("Goal" :in-theory (enable bitp)))))

  (local (defthm logcdr-minus-2x
           (implies (integerp x)
                    (equal (logcdr (- (* 2 x)))
                           (- x)))
           :hints (("Goal" :use ((:instance acl2::logcdr-2*i
                                            (i (- x))))
                    :in-theory (e/d ()
                                    (acl2::logcdr-2*i))))))

  (local (defthm logcar-plus-2-logcdr
           (equal (+ (logcar x) (* 2 (logcdr x)) y)
                  (+ (ifix x) y))
           :hints (("Goal" :use ((:instance bitops::logcons-destruct (x x)))
                    :in-theory (e/d (logcons) (bitops::logcons-destruct))))))

  (local (defthm 2-logcar-plus-2-logcdr
           (equal (+ (* 2 (logcar x)) (* 2 (logcdr x)))
                  (+ (logcar x) (ifix x)))
           :hints (("Goal" :use ((:instance bitops::logcons-destruct (x x)))
                    :in-theory (e/d (logcons) (bitops::logcons-destruct))))))

  (local (in-theory (disable acl2::exponents-add
                             acl2::expt-minus)))

  (local (defthm expt-2-times-2
           (implies (integerp exp)
                    (and (equal (* 2 (expt 2 (+ -1 exp)))
                                (expt 2 exp))
                         (equal (* 2 (expt 2 (+ -1 exp)) c)
                                (* (expt 2 exp) c))
                         (equal (* 2 b (expt 2 (+ -1 exp)))
                                (* b (expt 2 exp)))
                         (equal (* 2 b (expt 2 (+ -1 exp)) c)
                                (* b (expt 2 exp) c))))
           :hints (("Goal" :cases ((< exp 0))
                    :do-not-induct t)
                   (and stable-under-simplificationp
                        (if (member-equal '(< exp '0) clause)
                            '(:expand ((expt 2 exp)))
                          '(:expand ((expt 2 (+ -1 exp)))
                                    :in-theory (disable bitops::|(* 1/2 (expt 2 n))|)))))
           :otf-flg t))

  (local (defthmd b-and-is-mult
           (equal (b-and a b)
                  (* (bfix a) (bfix b)))
           :hints (("Goal" :in-theory (enable b-and)))))

  (local (defthm b-xor-of-b-not
           (and (equal (b-xor (b-not a) b)
                       (b-not (b-xor a b)))
                (equal (b-xor a (b-not b))
                       (b-not (b-xor a b))))
           :hints (("Goal" :in-theory (enable b-not)))))

  (local (defthmd b-xor-is-add
           (equal (b-xor a b)
                  (- (+ (bfix a) (bfix b))
                     (* 2 (b-and a b))))
           :hints (("Goal" :in-theory (enable b-xor b-and)))))

  (local (defthm logcdr-*-2-arith
           (equal (* 2 (logcdr x))
                  (- (ifix x) (logcar x)))
           :hints (("Goal" :in-theory (enable logcdr-arith)))))


  (defret <fn>-correct-when-exact
    (implies (and (not stickyp)
                  (not override-man)
                  (not (equal 0 (fp-arith-triple->man x)))
                  (equal (fp-arith-triple->sign x) 0))
             (equal (* (fp-arith-triple->rational ans)
                       (fp-arith-triple->rational ans))
                    (fp-arith-triple->rational x)))
    :hints (("Goal"
             :in-theory (enable fp-arith-triple->rational
                                nfix
                                bitops::ash-is-expt-*-x
                                collect-exponents
                                acl2::collect-like-terms
                                ;; b-and-is-mult
                                ;; b-not-is-sub
                                b-and b-not b-xor
                                logcdr-*-2-arith
                                )
             :expand ((:free (x) (logtail 1 x)))))
    :otf-flg t)

  (local (defthmd expt-expand
           (implies (and (acl2-numberp n)
                         (not (equal n 0)))
                    (equal (expt n x)
                           (* n (expt n (1- (ifix x))))))
           :hints (("Goal" :in-theory (enable expt)
                    :expand ((expt n x)
                             (expt n -1))
                    :do-not-induct t))
           :rule-classes ((:definition :install-body nil
                                       :controller-alist ((expt nil t))))))

  (local (defthm int-sqrt-times-expt-2-lemma
           (implies (and (natp x)
                         (integerp y))
                    (and (<= (* (bitops::int-sqrt (* 2 x))
                                (bitops::int-sqrt (* 2 x))
                                (expt 2 (+ -1 y)))
                             (* x (expt 2 y)))
                         (< (* x (expt 2 y))
                            (+ (expt 2 (+ -1 y))
                               (* (expt 2 y)
                                  (bitops::int-sqrt (* 2 x)))
                               (* (bitops::int-sqrt (* 2 x))
                                  (bitops::int-sqrt (* 2 x))
                                  (expt 2 (+ -1 y)))))))
           :hints (("Goal" :expand ((:with expt-expand (expt 2 y)))
                    :use ((:instance bitops::int-sqrt-bounds
                                     (x (* 2 x))))
                    :in-theory (disable bitops::int-sqrt-bounds
                                        expt-2-times-2))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm int-sqrt-times-expt-2-lemma-2
           (implies (and (natp x)
                         (integerp w)
                         (natp y)
                         (integerp z)
                         (equal w (+ z y)))
                    (and (<= (* (expt 2 z)
                                (bitops::int-sqrt (* x (expt 2 y)))
                                (bitops::int-sqrt (* x (expt 2 y))))
                             (* x (expt 2 w)))
                         (< (* x (expt 2 w))
                            (+ (expt 2 z)
                               (* 2 (expt 2 z)
                                  (bitops::int-sqrt (* x (expt 2 y))))
                               (* (expt 2 z)
                                  (bitops::int-sqrt (* x (expt 2 y)))
                                  (bitops::int-sqrt (* x (expt 2 y))))))))
           :hints (("Goal" :in-theory (enable acl2::exponents-add)
                    :use ((:instance bitops::int-sqrt-bounds
                                     (x (* x (expt 2 y))))))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))))



  (local (defthm int-sqrt-times-expt-2-lemma-3
           (implies (and (natp x)
                         (< 0 y))
                    (and (<= (* (bitops::int-sqrt x)
                                (bitops::int-sqrt x)
                                y)
                             (* x y))
                         (< (* x y)
                            (+ y
                               (* 2
                                  (bitops::int-sqrt x)
                                  y)
                               (* (bitops::int-sqrt x)
                                  (bitops::int-sqrt x)
                                  y)))))
           :hints (("Goal"
                    :use ((:instance bitops::int-sqrt-bounds
                                     (x x)))
                    :in-theory (disable bitops::int-sqrt-bounds
                                        expt-2-times-2))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (defret <fn>-correct-general
    (implies (and (not (equal 0 (fp-arith-triple->man x)))
                  (equal (fp-arith-triple->sign x) 0)
                  (not override-man))
             (b* ((sqrt-sq-value (* (fp-arith-triple->rational ans)
                                    (fp-arith-triple->rational ans)))
                  (sqrt+1-sq-value (* (fp-arith-triple->rational
                                       (fp-arith-triple-incr ans))
                                      (fp-arith-triple->rational
                                       (fp-arith-triple-incr ans))))
                  (x-value (fp-arith-triple->rational x)))
               (and (<= sqrt-sq-value x-value)
                    (< x-value sqrt+1-sq-value))))
    :hints (("Goal"
             :in-theory (enable fp-arith-triple->rational
                                fp-arith-triple-incr
                                nfix
                                bitops::ash-is-expt-*-x
                                collect-exponents
                                acl2::collect-like-terms
                                ;; b-and-is-mult
                                ;; b-not-is-sub
                                b-and b-not b-xor
                                logcdr-*-2-arith
                                )
             :expand ((:free (x) (logtail 1 x))))))

  (defret <fn>-mantissa-nonzero
    (implies (and (not (equal 0 (fp-arith-triple->man x)))
                  (acl2::maybe-posp override-man))
             (< 0 (fp-arith-triple->man ans)))
    :rule-classes :linear)

  (local (defthm posp-by-integer-length
           (implies (and (< 0 (integer-length x))
                         (natp x))
                    (posp x))
           :hints (("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))))

  (defret <fn>-override-correct
    :pre-bind (((mv override-man override-stickyp)
                (fp-sqrt-arith-man/sticky x)))
    (implies (and (not (equal 0 (fp-arith-triple->man x))))
             (b* (((mv spec-ans spec-stickyp)
                   (fp-sqrt-arith x :override-man nil :override-stickyp nil)))
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
                          natp-of-fp-sqrt-arith-man/sticky.man
                          acl2::natp-compound-recognizer
                          acl2::posp-compound-recognizer
                          posp-of-fp-size->frac-size
                          (:t integer-length)
                          acl2::bool-fix-when-booleanp
                          booleanp-of-fp-sqrt-arith-man/sticky.stickyp))))

  (local (in-theory (enable acl2::maybe-posp-fix))))
