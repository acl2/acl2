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

(in-package "IFP")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/bitstruct" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)
(include-book "std/strings/hexify" :dir :system)
(include-book "centaur/bitops/limited-shifts" :dir :system)
(include-book "centaur/fgl/def-fgl-rewrite" :dir :System)
(include-book "centaur/fgl/arith-base" :dir :System)
;; (include-book "centaur/bitops/range-is-0" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable unsigned-byte-p
                           logmask
                           (tau-system))))

(defxdoc fp-common
  :short "Common FP functions, data types, and macros."
  )

(local
 (xdoc::set-default-parents fp-common))

(local (std::add-default-post-define-hook :fix))

(defmacro cw-verbose (&rest rst)
  `(if verbosep ;; Captured free var.
       (cw ,@rst)
     nil))

(fty::defbitstruct
  fp-flags
  ((ie bitp)
   (de bitp)
   (ze bitp)
   (oe bitp)
   (ue bitp)
   (pe bitp))
  :msb-first nil)

(fty::defbitstruct fp-rc 2)

(defthm fp-flags-p-of-logior
  (implies (and (fp-flags-p x)
                (fp-flags-p y))
           (fp-flags-p (logior x y)))
  :hints (("Goal"
           :in-theory (e/d (fp-flags-p) ()))))

(define unmasked-fp-exception-p
  ((masks fp-flags-p)
   (flags fp-flags-p))
  :short "Check if there is any unmasked exceptions"
  :hooks nil
  :returns (bool booleanp :rule-classes :type-prescription)
  (not (eql 0 (logand (lognot (fp-flags-fix masks))
                      (loghead 6 flags)))))

(std::defenum rounding-mode-p
  (:rne :rmi :ri :rtz))

(define rc->rounding-mode ((rc fp-rc-p))
  :returns (mode rounding-mode-p
                 :hints (("goal" :in-theory (e/d (fp-rc-fix) ()))))
  :short "Convert rc (2-bit integer) to rounding-mode (keywords describing the equivalent
  rounding operation)"
  (case (fp-rc-fix rc)
    (0 :rne)
    (1 :rmi)
    (2 :ri)
    (3 :rtz)))

(define rounding-mode->rc ((mode rounding-mode-p))
  :returns (rc fp-rc-p)
  :short "Convert rounding-mode (keywords describing a
  rounding operation) to rc (2-bit integer)"
  (case (rounding-mode-fix mode)
    (:rne 0)
    (:rmi 1)
    (:ri  2)
    (:rtz 3))

  :prepwork
  ((local
    (defthm rounding-mode-fix-possibilities
      (implies (and (not (equal (rounding-mode-fix mode) :rne))
                    (not (equal (rounding-mode-fix mode) :rmi))
                    (not (equal (rounding-mode-fix mode) :ri)))
               (equal (rounding-mode-fix mode) :rtz))
      :hints (("goal" :in-theory (e/d (rounding-mode-fix) ()))))))

  ///
  (local (in-theory (e/d (rc->rounding-mode) ())))

  (defthm rc->rounding-mode-of-rounding-mode->rc
    (equal (rc->rounding-mode (rounding-mode->rc mode))
           (rounding-mode-fix mode)))

  (defthm rounding-mode->rc-of-rc->rounding-mode
    (equal (rounding-mode->rc (rc->rounding-mode rc))
           (fp-rc-fix rc))
    :hints (("goal" :in-theory (e/d (fp-rc-fix) ())))))

(defsection fp-expsize
  :set-as-default-parent t
  :short "Fp-expsize data dype"
  (define fp-expsize-p (x)
    :short "Recognizer for @(see fp-expsize)"
    (and (integerp x)
         (<= 2 x))
    ///
    (defthm fp-expsize-p-compound-recognizer
      (equal (fp-expsize-p x)
             (and (integerp x)
                  (<= 2 x)))
      :rule-classes :compound-recognizer))

  (define fp-expsize-fix ((x fp-expsize-p))
    :returns (new-x fp-expsize-p)
    :parents (fp-expsize)
    :short "Fixing function for @(see fp-expsize) data type"
    (mbe :logic (if (fp-expsize-p x) x 2)
         :exec x)
    ///
    (defret <fn>-when-fp-expsize-p
      (implies (fp-expsize-p x)
               (equal new-x x))))

  (local
   (xdoc::set-default-parents fp-common))

  (fty::deffixtype fp-expsize
    :pred fp-expsize-p
    :fix fp-expsize-fix
    :equiv fp-expsize-equiv
    :define t
    ))

(fty::defflexsum fp-size
  (:fp-size
   :fields ((exp-size :type fp-expsize
                      :rule-classes :type-prescription
                      :acc-body (car x))
            (explicit-jbit :type booleanp
                           :rule-classes :type-prescription
                           :acc-body (consp (cdr x)))
            (frac-size :type posp
                       :rule-classes :type-prescription
                       :acc-body (if (consp (cdr x)) (cddr x) (cdr x))))
   :ctor-body (cons exp-size (if explicit-jbit (cons 1 frac-size) frac-size))
   :type-name fp-size
   :shape (and (consp x)
               (or (atom (cdr x)) (eql 1 (cadr x))))
   :remake-name remake-fp-size
   :remake-body (cons-with-hint exp-size
                                (if explicit-jbit
                                    (cons-with-hint 1 frac-size (cdr x))
                                  frac-size)
                                x)
   :extra-binder-names (width exp-bias emax emin))
  :case nil
  :kind nil)


(define maybe-fp-size-p (x)
  :returns (res)
  (or (not x)
      (fp-size-p x))
  ///
  (defret <fn>-implies-fp-size-p
    (implies (and res x)
             (fp-size-p x))
    :rule-classes :forward-chaining))

;; (fty::defprod fp-size
;;               ((frac-size posp)
;;                (exp-size posp))
;;               :extra-binder-names (width)
;;               :layout :fulltree)

(define fp-size->width (&optional ((size fp-size-p) 'size))
  :returns (width posp :rule-classes :type-prescription)
  :short "Extract bit-width from a given @(see fp-size)"
  (b* (((fp-size size)))
    (+ 1 size.exp-size (bool->bit size.explicit-jbit) size.frac-size)))

(defmacro fp-size-width (&rest args) `(fp-size->width . ,args))
(add-macro-alias fp-size-width fp-size->width-fn)

(local
 (defthm ash-non-zero-lemma
   (implies (natp n)
            (not (equal (ash 1 n) 0)))
   :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
                                     bitops::ihsext-recursive-redefs)
                                    ())))))

(local (defthm ash-1-gt-1
         (implies (<= 1 (ifix n))
                  (< 1 (ash 1 n)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))
         :rule-classes :linear))

(define fp-size->exp-bias (&optional ((size fp-size-p) 'size))
  :returns (exp-bias posp :rule-classes :type-prescription)
  :short "Extract exponent bias from a given @(see fp-size)"
  (b* (((fp-size size)))
    (1- (ash 1 (1- size.exp-size)))))

(defmacro fp-size-exp-bias (&rest args) `(fp-size->exp-bias . ,args))
(add-macro-alias fp-size-exp-bias fp-size->exp-bias-fn)

(define fp-size->emax (&optional ((size fp-size-p) 'size))
  :returns (emax posp :rule-classes :type-prescription)
  :short "Calculate the maximum effective/real value of exponent for a given @(see fp-size)"
  (b* (((fp-size size)))
    size.exp-bias))
(defmacro fp-size-emax (&rest args) `(fp-size->emax . ,args))
(add-macro-alias fp-size-emax fp-size->emax-fn)

(define fp-size->emin (&optional ((size fp-size-p) 'size))
  :short "Calculate the minimum effective/real value of exponent for a given @(see fp-size)"
  :returns (emin)
  (b* (((fp-size size)))
    (- (- size.exp-bias 1)))
  ///
  (defret <fn>-type
    (and (integerp emin)
         (<= emin 0))
    :rule-classes :type-prescription))
(defmacro fp-size-emin (&rest args) `(fp-size->emin . ,args))
(add-macro-alias fp-size-emin fp-size->emin-fn)

(defconst *fp-size-e4m3*  (make-fp-size :frac-size 3 :exp-size 4)) ;;this format fdoes nto follow IEEE (we need ot do a bit more about it!!!!)
(defconst *fp-size-bf8*   (make-fp-size :frac-size 2 :exp-size 5)) ;;E5M2
(defconst *fp-size-bf16*  (make-fp-size :frac-size 7 :exp-size 8))
(defconst *fp-size-hp*    (make-fp-size :frac-size 10 :exp-size 5)) ;;fp16
(defconst *fp-size-sp*    (make-fp-size :frac-size 23 :exp-size 8)) ;;fp32
(defconst *fp-size-tf32*   (make-fp-size :frac-size 10 :exp-size 8)) ;;tf32 same mantissa as fp16 and the same exp as fp32
(defconst *fp-size-dp*    (make-fp-size :frac-size 52 :exp-size 11))
(defconst *fp-size-ep*    (make-fp-size :frac-size 63 :exp-size 15 :explicit-jbit t))

;; ----------------------------------------------------------------------

(defsection fp-value
  :short "Data type for Floating point values"
  :set-as-default-parent t

  (define fp-value-p (x &key ((size fp-size-p) 'size))
    :short "Recognizer for @(see fp-value) data type"
    (unsigned-byte-p (fp-size-width) x)
    ///
    (defthm fp-value-p-implies-natp
      (implies (fp-value-p x)
               (natp x))
      :rule-classes :forward-chaining))

  ;; (local (defthm unsigned-byte-p-of-logcons
  ;;          (implies (unsigned-byte-p n a)
  ;;                   (unsigned-byte-p (+ 1 n) (logcons b a)))
  ;;          :hints(("Goal" :in-theory (enable unsigned-byte-p logcons)))))

  (define fp-value ((frac integerp)
                    (exp integerp)
                    (sign bitp)
                    &key
                    ((jbit maybe-bitp) 'nil)
                    ((size fp-size-p) 'size))
    :returns (val fp-value-p
                  :hints(("Goal" :in-theory (enable fp-value-p fp-size-width
                                                    bitops::unsigned-byte-p-logcons))))
    (b* (((fp-size size))
         (exp-sign (logapp size.exp-size exp
                           (lbfix sign))))
      (logapp size.frac-size frac
              (if size.explicit-jbit
                  (logcons (or (maybe-bit-fix jbit)
                               (bool->bit (not (eql (loghead size.exp-size exp) 0))))
                           exp-sign)
                exp-sign))))

  (define make-fp-value (&key
                         (sign bitp)
                         (exp  integerp)
                         (frac integerp)
                         ((jbit maybe-bitp) 'nil)
                         ((size fp-size-p) 'size))
    :returns (val fp-value-p)
    :enabled t
    (fp-value frac exp sign :jbit jbit))

  (define fp-value-fix ((x fp-value-p)
                        &key
                        ((size fp-size-p) 'size))
    :prepwork ((local (in-theory (enable fp-value-p))))
    :returns (new-x fp-value-p)
    (mbe :logic (loghead (fp-size-width) x)
         :exec x)
    ///
    (defret <fn>-when-fp-value-p
      (implies (fp-value-p x)
               (equal (fp-value-fix x) x))))

  (define fp-value->frac ((x fp-value-p) &key ((size fp-size-p) 'size))
    :returns (frac natp :rule-classes :type-prescription)
    (loghead (fp-size->frac-size size) x)
    ///
    (defthm fp-value->frac-of-fp-value
      (equal (fp-value->frac (fp-value frac exp sign :jbit jbit))
             (loghead (fp-size->frac-size size) frac))
      :hints(("Goal" :in-theory (enable fp-value))))

    (defthm fp-value->frac-of-fp-value-fix
      (equal (fp-value->frac (fp-value-fix x))
             (fp-value->frac x))
      :hints(("Goal" :in-theory (enable fp-value-fix fp-size-width))))

    (defret width-of-<fn>
      (unsigned-byte-p (fp-size->frac-size size) frac)))

  (define fp-value->exp ((x fp-value-p) &key ((size fp-size-p) 'size))
    :returns (exp natp :rule-classes :type-prescription)
    (part-select x :width (fp-size->exp-size size)
                 :low (+ (bool->bit (fp-size->explicit-jbit size))
                         (fp-size->frac-size size)))
    ///
    (defthm fp-value->exp-of-fp-value
      (equal (fp-value->exp (fp-value frac exp sign :jbit jbit))
             (loghead (fp-size->exp-size size) exp))
      :hints(("Goal" :in-theory (enable fp-value bitops::logtail**))))

    (defthm fp-value->exp-of-fp-value-fix
      (equal (fp-value->exp (fp-value-fix x))
             (fp-value->exp x))
      :hints(("Goal" :in-theory (enable fp-value-fix fp-size-width))))

    (defret width-of-<fn>
      (unsigned-byte-p (fp-size->exp-size size) exp)))

  (define fp-value->sign ((x fp-value-p) &key ((size fp-size-p) 'size))
    :returns (sign bitp :rule-classes :type-prescription)
    (part-select x :width 1 :low (1- (fp-size->width size)))
    ///
    (defthm fp-value->sign-of-fp-value
      (equal (fp-value->sign (fp-value frac exp sign :jbit jbit))
             (bfix sign))
      :hints(("Goal" :in-theory (enable fp-value fp-size->width))))

    (defthm fp-value->sign-of-fp-value-fix
      (equal (fp-value->sign (fp-value-fix x))
             (fp-value->sign x))
      :hints(("Goal" :in-theory (enable fp-value-fix fp-size-width)))))

  (define fp-value->jbit ((x fp-value-p) &key ((size fp-size-p) 'size))
    :returns (jbit bitp :rule-classes :type-prescription)
    (if (fp-size->explicit-jbit size)
        (logbit (fp-size->frac-size size) x)
      (bool->bit (not (eql 0 (fp-value->exp x)))))
    ///
    (defthm fp-value->jbit-of-fp-value
      (equal (fp-value->jbit (fp-value frac exp sign :jbit jbit))
             (if (and (fp-size->explicit-jbit size) jbit)
                 (bfix jbit)
               (bool->bit (not (eql (loghead (fp-size->exp-size size) exp) 0)))))
      :hints(("Goal" :in-theory (enable fp-value fp-value->exp))))

    (defthm fp-value->jbit-of-fp-value-fix
      (equal (fp-value->jbit (fp-value-fix x))
             (fp-value->jbit x))
      :hints((and stable-under-simplificationp
                  '(:in-theory (enable fp-value-fix fp-size-width))))))

  (define fp-value->man ((x fp-value-p) &key ((size fp-size-p) 'size))
    :returns (man natp :rule-classes :type-prescription)
    (logapp (fp-size->frac-size size)
            (fp-value->frac x)
            (fp-value->jbit x))
    ///
    (defthm fp-value->man-of-fp-value
      (equal (fp-value->man (fp-value frac exp sign :jbit jbit))
             (b* (((fp-size size)))
               (logapp size.frac-size
                       frac
                       (if (and size.explicit-jbit jbit)
                           (bfix jbit)
                         (bool->bit (not (equal (loghead size.exp-size exp) 0)))))))
      :hints(("Goal" :in-theory (enable ))))

    (defthm fp-value->man-of-fp-value-fix
      (equal (fp-value->man (fp-value-fix x))
             (fp-value->man x)))

    (defret width-of-<fn>
      (unsigned-byte-p (+ 1 (fp-size->frac-size size)) man)))

  (make-event
   (std::da-make-binder-gen 'fp-value
                            '((frac . fp-value->frac)
                              (exp . fp-value->exp)
                              (sign . fp-value->sign)
                              (type . fp-value->type)
                              (man  . fp-value->man)
                              (jbit . fp-value->jbit))))

  (std::defenum fp-type-p
    (:zero :denorm :normal :inf :qnan :snan :pseudo-denorm :invalid))

  (fty::deflist fp-types :elt-type fp-type-p :true-listp t)

  (define fp-value->type ((x fp-value-p) &key ((size fp-size-p) 'size))
    :parents (fp-value)
    :short "Gets the encoding type of a @(see fp-value)."
    :long "<p>The possible types are as follows.  The first five types occur in
all sizes (with and without explicit jbit), and in explicit-jbit sizes assume
that the jbit is 1 exactly when the exponent is nonzero.  The last two only
occur in explicit-jbit sizes.</p>

<ul>
<li>@(':zero') when exp = 0 and frac = 0</li>
<li>@(':denorm') when exp = 0 and frac != 0</li>
<li>@(':inf') when exp = max, frac = 0</li>
<li>@(':qnan') when exp=max, frac != 0 and upper bit of frac is 1</li>
<li>@(':snan') when exp=max, frac != 0 and upper bit of frac is 0</li>
<li>@(':pseudo-denorm') when exp = 0 and jbit = 1 (explicit jbit only)</li>
<li>@(':invalid') when exp != 0 and jbit = 0 (explicit jbit only).</li>
</ul>"
    :returns (type fp-type-p)
    (b* (((fp-size size))
         ((fp-value x)))
      (cond ((eql 0 x.exp)
             (cond ((eql 1 x.jbit) :pseudo-denorm)
                   ((eql 0 x.frac) :zero)
                   (t :denorm)))
            ((eql x.jbit 0) :invalid)
            ((eql x.exp (logmask size.exp-size))
             (cond ((eql 0 x.frac) :inf)
                   ((logbitp (1- size.frac-size) x.frac) :qnan)
                   (t :snan)))
            (t :normal)))
    ///
    (defret <fn>-possibilities
      (or (equal type :zero)
          (equal type :denorm)
          (equal type :normal)
          (equal type :inf)
          (equal type :qnan)
          (equal type :snan)
          (equal type :pseudo-denorm)
          (equal type :invalid))
      :rule-classes ((:forward-chaining :trigger-terms (type))))

    (defthm fp-value->type-of-fp-value-fix
      (equal (fp-value->type (fp-value-fix x))
             (fp-value->type x))))

  (define fp-nan-p ((x fp-value-p)
                    &key
                    ((size fp-size-p) 'size))
    :enabled t
    (b* (((fp-value x)))
      (or (eql x.type :snan)
          (eql x.type :qnan))))

  (define fp-nonzero-finite-p ((x fp-value-p)
                               &key
                               ((size fp-size-p) 'size))
    (b* (((fp-value x)))
      (or (eql x.type :normal)
          (eql x.type :denorm))))

  (define fp-value-debug ((x fp-value-p)
                          &key
                          ((size fp-size-p) 'size))
    (b* (((fp-value x)))
      (list (cons :value (str::hexify x))
            (cons :type x.type)
            (cons :sign x.sign)
            (cons :exp  (str::hexify x.exp))
            (cons :jbit (str::hexify x.jbit))
            (cons :frac (str::hexify x.frac))
            (cons :man (str::hexify x.man)))))

  (defthm fp-value-p-when-unsigned-byte-p
    (implies (unsigned-byte-p (fp-size->width size) x)
             (fp-value-p x))
    :hints(("Goal" :in-theory (enable fp-value-p))))


  ;; (local (defthm logapp-logtail-logbitp-lemma
  ;;          (implies (natp sz1)
  ;;                   (equal (logapp sz1 x (bool->bit (logbitp sz1 x)))
  ;;                          (loghead (+ sz1 1) x)))
  ;;          :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
  ;;                                            bitops::ihsext-recursive-redefs))))))

  (local (defthm logapp-logtail-logbitp
           (implies (and (natp sz1) (natp sz2)
                         (equal sz3 (+ sz1 sz2)))
                    (equal (logapp sz1 (logtail sz2 x) (bool->bit (logbitp sz3 x)))
                           (loghead (+ sz1 1) (logtail sz2 x))))
           :hints (("goal" :use ((:instance bitops::logapp-of-logtail
                                  (n sz1)
                                  (x (loghead (+ sz1 1) (logtail sz2 x)))))
                    :in-theory (disable bitops::logapp-of-logtail)))))

  (local (defthm logapp-logtail-logbitp-2
           (implies (and (natp sz1) (natp sz2)
                         (equal y (loghead sz1 (logtail sz2 x))))
                    (equal (logapp sz1 y (bool->bit (logbitp (+ sz1 sz2) x)))
                           (loghead (+ sz1 1) (logtail sz2 x))))
           :hints (("goal" :use ((:instance bitops::logapp-of-logtail
                                  (n sz1)
                                  (x (loghead (+ sz1 1) (logtail sz2 x)))))
                    :in-theory (disable bitops::logapp-of-logtail)))))

  (local (defthm logcons-logbitp-loghead-logtail
           (implies (and (natp sz1) (natp sz2)
                         (equal c (bool->bit (logbitp sz1 x))))
                    (equal (logcons c
                                    (loghead sz2 (logtail (+ 1 sz1) x)))
                           (loghead (+ 1 sz2) (logtail sz1 x))))
           :hints (("goal" :use ((:instance bitops::logapp-of-logtail
                                  (n 1)
                                  (x (loghead (+ sz2 1) (logtail sz1 x)))))
                    :expand ((loghead (+ 1 sz2) (logtail sz1 x)))
                    :in-theory (disable bitops::logapp-of-logtail)))))

  (local (defthm logapp-of-loghead-logtail
           (implies (and (natp sz1) (natp sz2))
                    (equal (logapp sz1 x (loghead sz2 (logtail sz1 x)))
                           (loghead (+ sz1 sz2) x)))
           :hints (("goal" :use ((:instance bitops::logapp-of-logtail
                                  (n sz1)
                                  (x (loghead (+ sz2 sz1) x))))
                    :expand ((loghead (+ 1 sz2) (logtail sz1 x)))
                    :in-theory (disable bitops::logapp-of-logtail)))))

  (defthm fp-value-of-fp-value-fields-with-jbit
    (equal (fp-value (fp-value->frac x)
                     (fp-value->exp x)
                     (fp-value->sign x)
                     :jbit (fp-value->jbit x))
           (fp-value-fix x))
    :hints(("Goal" :in-theory (enable fp-value
                                      fp-value->frac
                                      fp-value->exp
                                      fp-value->sign
                                      fp-value->jbit
                                      fp-value-fix
                                      fp-size->width))))

  (defthm fp-value-of-fp-value-fields-without-jbit
    (implies (and (not (equal (fp-value->type x) :invalid))
                  (not (equal (fp-value->type x) :pseudo-denorm)))
             (equal (fp-value (fp-value->frac x)
                              (fp-value->exp x)
                              (fp-value->sign x))
                    (fp-value-fix x)))
    :hints(("Goal" :in-theory (e/d (fp-value
                                      fp-value->frac
                                      fp-value->exp
                                      fp-value->sign
                                      fp-value->jbit
                                      fp-value-fix
                                      fp-size->width
                                      fp-value->type)
                                   (bitops::logapp-of-i-0)))))

  

  (defthm fp-value-p-implies-unsigned-byte-p
    (and (implies (fp-value-p x :size *fp-size-sp*)
                  (unsigned-byte-p 32 x))
         (implies (fp-value-p x :size *fp-size-dp*)
                  (unsigned-byte-p 64 x))
         (implies (fp-value-p x :size *fp-size-hp*)
                  (unsigned-byte-p 16 x))
         (implies (fp-value-p x :size *fp-size-bf16*)
                  (unsigned-byte-p 16 x)))
    :hints (("Goal"
             :in-theory (e/d (fp-value-p) ())))))

(define fp-value-zero ((sign bitp)
                       &key
                       ((size fp-size-p) 'size))
  :short "Create an @(see fp-value) with :zero type"
  :returns (zero fp-value-p)
  (fp-value 0 0 sign :jbit 0)
  ///
  (local (in-theory (e/d (fp-value->type) ())))
  (defret fp-value->type-of-<fn>
    (equal (fp-value->type zero) :zero)))

(local
 (defthm non-zero-logmask-with-posp-input
   (implies (posp x)
            (equal (equal (logmask x) 0) nil))
   :hints (("goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                     bitops::ihsext-inductions)
                                    ())))))

(define fp-value-inf ((sign bitp)
                      &key
                      ((size fp-size-p) 'size))
  :short "Create an @(see fp-value) with :inf type"
  :returns (inf fp-value-p)
  (b* (((fp-size size)))
    (fp-value 0 (logmask size.exp-size) sign :jbit 1))
  ///
  (local (in-theory (e/d (fp-value->type) ())))

  (defret fp-value->type-of-<fn>
    (equal (fp-value->type inf) :inf)))

(local
 (defthm non-zero-logapp-lemma
   (implies (and (posp x) (posp z))
            (equal (equal (logapp (1- x) y z) 0) nil))
   :hints (("goal" :in-theory (e/d* (logapp
                                     bitops::ihsext-recursive-redefs
                                     bitops::ihsext-inductions)
                                    ())))))

(define fp-value-qnan ((sign bitp)
                       (frac natp)
                       &key
                       ((size fp-size-p) 'size))
  :short "Create an @(see fp-value) with :qnan type"
  :hooks ((:fix :args ((sign bitp) (frac integerp) (size fp-size-p))))
  :returns (qnan fp-value-p)
  (b* (((fp-size size))
       (frac-size-1 (1- size.frac-size)))
    (fp-value (logapp frac-size-1 (loghead frac-size-1 frac) 1)
              (logmask size.exp-size)
              sign
              :jbit 1))
  ///
  (local (in-theory (e/d (fp-value->type) ())))

  (defret fp-value->type-of-<fn>
    (equal (fp-value->type qnan) :qnan)))

(define fp-value-snan ((sign bitp)
                       (frac posp)
                       &key
                       ((size fp-size-p) 'size))
  :short "Create an @(see fp-value) with :snan type"
  :guard (not (eql (loghead (1- (fp-size->frac-size size)) frac) 0))
  :hooks ((:fix :args ((sign bitp) (frac integerp) (size fp-size-p))))
  :returns (snan fp-value-p)
  (b* (((fp-size size))
       (frac-size-1 (1- size.frac-size)))
    (fp-value (loghead frac-size-1 frac)
              (logmask size.exp-size)
              sign
              :jbit 1))
  ///
  (local (in-theory (e/d (fp-value->type) ())))

  (defret fp-value->type-of-<fn>
    (implies (not (eql (loghead (1- (fp-size->frac-size size)) frac) 0))
             (equal (fp-value->type snan) :snan))))

(define fp-value-quiet ((x fp-value-p)
                        &key
                        ((size fp-size-p) 'size))
  :short "Force QNAN/SNAN @(see fp-value) into a QNAN"
  :guard (or (eql (fp-value->type x) :qnan)
             (eql (fp-value->type x) :snan))
  :returns (qnan fp-value-p)
  (b* (((fp-size size))
       ((fp-value x)))
    (fp-value-qnan x.sign x.frac))
  ///
  (defret fp-value->type-of-<fn>
    (equal (fp-value->type qnan) :qnan)))

(define fp-value-indef (&key
                        ((size fp-size-p) 'size))
  :returns (indef fp-value-p)
  (b* (((fp-size size)))
    (fp-value-qnan 1 (ash 1 (1- size.frac-size))))
  ///
  (defret fp-value->type-of-<fn>
    (equal (fp-value->type indef) :qnan))

  (defretd sp-<fn>-value
    (equal (fp-value-indef :size *fp-size-sp*)
           #xFFC00000)))

(define fp-value-norm-max ((sign bitp)
                           &key
                           ((size fp-size-p) 'size))
  :short "Create the largest :normal @(see fp-value)"
  :guard-hints (("goal" :in-theory (e/d (make-fp-value) ())))
  :returns (n_max fp-value-p)
  (b* (((fp-size size)))
    (make-fp-value :sign sign
                   :exp (1- (logmask size.exp-size))
                   :frac (logmask size.frac-size)
                   :jbit (bool->bit size.explicit-jbit)))
  ///

  (local
   (defthm loghead-n-of-logmask-n-1-!=-0
     (implies (and (integerp n) (< 1 n))
              (not (equal (loghead n (+ -1 (logmask n))) 0)))
     :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
                                       bitops::ihsext-recursive-redefs)
                                      ())))))

  (local
   (defthm loghead-n-of-1-logmask-n-!=-logmask-n
     (implies (and (integerp n) (< 0 n))
              (not (equal (loghead n (+ -1 (logmask n)))
                          (logmask n))))
     :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
                                       bitops::ihsext-recursive-redefs)
                                      ())))))

  (defret <fn>-is-normal
    (b* (((fp-value n_max))
         ((fp-size size)))
      (implies (< 1 size.exp-size) ;; posp not enough; see loghead-n-of-logmask-n-1-!=-0.
               (eql n_max.type :normal)))
    :hints (("goal" :in-theory (e/d (make-fp-value fp-value->type) ())))))

(define fp-value-norm-min ((sign bitp)
                           &key
                           ((size fp-size-p) 'size))
  :short "Create the smallest :normal @(see fp-value)"
  :returns (n_min fp-value-p)
  (b* (((fp-size size)))
    (make-fp-value :sign sign :exp 1 :frac 0 :jbit (bool->bit size.explicit-jbit)))
  ///

  (local
   (defthm loghead-n-1-!=0
     (implies (and (integerp n) (< 0 n))
              (not (equal (loghead n 1) 0)))
     :hints (("goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                       bitops::ihsext-inductions)
                                      ())))))

  (local
   (defthm loghead-n-1-!=-logmask-n
     (implies (and (integerp n) (< 1 n))
              (not (equal (loghead n 1)
                          (logmask n))))
     :hints (("goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                       bitops::ihsext-inductions
                                       logmask)
                                      ())))))

  (defret <fn>-is-normal
    (b* (((fp-value n_min))
         ((fp-size size)))
      (implies (< 1 size.exp-size) ;; Posp not enough. See loghead-n-1-!=-logmask-n.
               (eql n_min.type :normal)))
    :hints (("goal" :in-theory (e/d (make-fp-value fp-value->type) ())))))

;; ----------------------------------------------------------------------

(define fp-sign-value ((sign bitp))
  :short "Returns -1 when sign is 1, returns 1 otherwise."
  :returns (val (and (integerp val) (not (equal val 0)))
                :hints(("Goal" :in-theory (enable bfix)))
                :rule-classes :type-prescription)
  (- 1 (* 2 (lbfix sign))))

(define fp-value-apply-daz ((x fp-value-p) (daz bitp)
                            &key ((size fp-size-p) 'size))
  :short "Apply the DAZ (denormals-are-zero) flag to a given @(see fp-value)"
  :long "<p>The result will be :zero fp-value with the same sign as @('x') when
          @('x') is a :denorm fp-value and @('daz') is 1.
          Otherwise, @('x') of type fp-value will be returned.</p>"
  :returns (new-x fp-value-p)
  (if (or (eql (lbfix daz) 0)
          (not (eq (fp-value->type x) :denorm)))
      (fp-value-fix x)
    (fp-value 0 0 (fp-value->sign x)))
  ///
  (defret unsigned-byte-p-of-<fn>.new-x
    (implies (>= (nfix n) (fp-size-width))
             (unsigned-byte-p n new-x))
    :hints (("Goal" :in-theory (e/d (fp-value-p) (fp-value-p-of-<fn>))
             :use fp-value-p-of-<fn>)))

  (defret fp-value->exp-of-<fn>.new-x
    (equal (fp-value->exp new-x)
           (if (and (equal 1 daz)
                    (equal (fp-value->type x) :denorm))
               0
             (fp-value->exp x))))

  (defret fp-value->sign-of-<fn>.new-x
    (equal (fp-value->sign new-x)
           (fp-value->sign x)))

  (defret fp-value->type-of-<fn>.new-x
    (equal (fp-value->type (fp-value-apply-daz x daz))
           (if (and (not (equal (bfix daz) 0))
                    (equal (fp-value->type x) :denorm))
               :zero
               (fp-value->type x)))
    :hints
    (("Goal"
      :cases
      ((and (not (equal (bfix daz) 0))
            (equal (fp-value->type x) :denorm)))
      :expand
      (fp-value->type (fp-value 0 0 (fp-value->sign x)
                                :jbit nil)))))

  (defret fp-value->man-of-<fn>.new-x
    (equal (fp-value->man new-x)
           (if (and (equal 1 daz)
                    (equal (fp-value->type x) :denorm))
               0
             (fp-value->man x))))

  (in-theory (disable fp-value->exp-of-fp-value-apply-daz.new-x
                      fp-value->sign-of-fp-value-apply-daz.new-x
                      fp-value->type-of-fp-value-apply-daz.new-x
                      fp-value->man-of-fp-value-apply-daz.new-x)))

(define fp-value->rational ((x fp-value-p)
                            &key ((size fp-size-p) 'size))
  :short "Returns the rational number equivalent of a given @(see fp-value)"
  :guard (member (fp-value->type x) '(:zero :denorm :normal :pseudo-denorm))
  :returns (ans rationalp :rule-classes :type-prescription)
  (b* (((fp-size size))
       (lsb-exp-bias (+ size.frac-size size.exp-bias))
       ((fp-value x)))
    (* (fp-sign-value x.sign)
       x.man
       (expt 2 (- (max x.exp 1) lsb-exp-bias)))))

(defthm fp-value-p-of-0
  (fp-value-p 0)
  :hints(("Goal" :in-theory (enable fp-value-p))))

(define fp-sign ((x integerp))
  :short "Given an integer, returns 1 when the input is negative, 0 otherwise."
  (if (minusp (lifix x)) 1 0))

(define rational->fp-value ((x rationalp)
                            &key ((size fp-size-p) 'size))
  :short "Convert a rational number into an @(see fp-value).
   Return OK only if value is exact. No rounding etc."
  :returns (mv okp (ans fp-value-p))
  (b* ((den (denominator x))
       (den-exp (1- (integer-length den)))
       (power-of-2p (equal den (ash 1 den-exp)))
       ((unless power-of-2p)
        ;; denominator is not a power of 2 so
        ;; this can't be represented exactly
        (mv nil 0))
       (num (numerator x))
       ((when (eql 0 num))
        (mv t (fp-value 0 0 0)))
       (abs-num (abs num))
       (sign (fp-sign num))
       (num-size (integer-length abs-num))
       ((fp-size size))
       (norm-shift (- (+ 1 size.frac-size) num-size))
       (man (ash abs-num norm-shift))
       (lost-bits (if (< norm-shift 0)
                      (loghead (- norm-shift) abs-num)
                    0))
       ((unless (eql lost-bits 0))
        ;; lost some bits when normalizing so this can't be represented exactly
        (mv nil 0))
       (unbiased-exp (+ size.frac-size
                        (- norm-shift)
                        (- den-exp)))
       (biased-exp (+ unbiased-exp size.exp-bias))
       ((unless (< biased-exp (1- (ash 1 size.exp-size))))
        ;; too big to be represented exactly
        (mv nil 0))
       ((when (< 0 biased-exp))
        ;; normal range
        (mv t (fp-value (loghead size.frac-size man)
                        biased-exp
                        sign)))
       ((unless (< (- size.frac-size) biased-exp))
        ;; too small to be represented exactly
        (mv nil 0))
       (denorm-shift (+ -1 biased-exp))
       (lost-bits (loghead (- denorm-shift) man))
       ((unless (eql lost-bits 0))
        ;; lost some bits when denormalizing so not exact
        (mv nil 0))
       (denorm-man (ash man denorm-shift)))
    (mv t (fp-value denorm-man 0 sign)))
  ///
  (local (defthmd loghead-of-non-integer
           (implies (not (integerp x))
                    (equal (loghead n x) 0))
           :hints (("goal" :use ((:instance
                                  ACL2::INT-EQUIV-IMPLIES-EQUAL-LOGHEAD-2
                                  (x x) (x-equiv 0) (n n)))
                    :in-theory (disable ACL2::INT-EQUIV-IMPLIES-EQUAL-LOGHEAD-2)))))

  (local (defthm loghead-identity-by-bounds
           (implies (and (< (ifix x) (ash 1 (nfix sz)))
                         (<= 0 (ifix x)))
                    (equal (loghead sz x) (ifix x)))
           :hints(("Goal" :in-theory (e/d (unsigned-byte-p
                                           loghead-of-non-integer
                                           bitops::ash-is-expt-*-x)
                                          (bitops::loghead-identity))
                   :use ((:instance bitops::loghead-identity
                                    (size (nfix sz)) (i x)))
                   :cases ((integerp x))))))

  (local (defthm equal-by-logtail-loghead
           (implies (and (equal (logtail n x) (logtail n y))
                         (equal (loghead n x) (loghead n y)))
                    (equal (ifix x) (ifix y)))
           :hints (("goal" :induct (equal (logtail n x) (logtail n y))
                    :in-theory (enable* bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs)))
           :rule-classes nil))

  (local (defthm logtail-of-one-less-than-integer-length
           (implies (posp x)
                    (equal (logtail (+ -1 (integer-length x)) x) 1))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm logapp-1-normalize
           (implies (and (natp x)
                         (natp size)
                         (equal (integer-length x) (+ 1 size)))
                    (equal (logapp size x 1) x))
           :hints (("goal" :use ((:instance equal-by-logtail-loghead
                                            (n size)
                                            (x (logapp size x 1))
                                            (y x))
                                 (:instance
                                  logtail-of-one-less-than-integer-length))
                    :in-theory (disable
                                logtail-of-one-less-than-integer-length)))))

  (local (defthm 2*logcdr-when-logcar-0
           (implies (equal 0 (logcar x))
                    (equal (* 2 (logcdr x))
                           (ifix x)))
           :hints (("goal" :use ((:instance bitops::logcons-destruct
                                            (x x)))
                    :in-theory (e/d (logcons)
                                    (bitops::logcons-destruct
                                     acl2::logcar-logcdr-elim))))))

  (local (defthm 2*logcdr-when-logcar-0-left
           (implies (equal 0 (logcar x))
                    (equal (* 2 (logcdr x) y)
                           (* (ifix x) y)))
           :hints (("goal" :use 2*logcdr-when-logcar-0
                    :in-theory (disable 2*logcdr-when-logcar-0)))))

  (local (defthmd ash-when-loghead-equal-0
           (implies (or (equal (loghead (- (ifix sh)) x) 0)
                        (<= 0 (ifix sh)))
                    (equal (ash x sh)
                           (* (expt 2 sh) (ifix x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)
                   :induct t)
                  (and stable-under-simplificationp
                       (cond ((member-equal '(< sh '0) clause)
                              '(:in-theory (enable logcons)
                                           :expand ((expt 2 sh))))
                             (t '(:expand ((expt 2 (+ 1 sh))))))))))

  ;; (local (defthmd integerp-when-loghead-equal-0
  ;;          (implies (equal (loghead (- (ifix sh)) x) 0)
  ;;                   (integerp (* (expt 2 sh) (ifix x))))
  ;;          :hints (("goal" :use ash-when-loghead-equal-0))))

  (local (defthmd integerp-when-loghead-equal-0
           (implies (and (equal (loghead (- (ifix sh)) x) 0)
                         (integerp x))
                    (integerp (* x (expt 2 sh))))
           :hints (("goal" :use ash-when-loghead-equal-0))))

  (local (defthmd integerp-when-loghead-equal-0-neg
           (implies (and (equal (loghead (- (ifix sh)) (- x)) 0)
                         (integerp x))
                    (integerp (- (* x (expt 2 sh)))))
           :hints (("goal" :use ((:instance ash-when-loghead-equal-0 (x (- x))))))))

  (local (defthmd expt-2-distrib
           (implies (and (integerp x) (integerp y))
                    (equal (expt 2 (+ x y))
                           (* (expt 2 x) (expt 2 y))))
           :hints(("Goal" :in-theory (enable expt)))))

  (local (defthm integer-length-when-posp
           (implies (posp x)
                    (posp (integer-length x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))
           :rule-classes :type-prescription))

  ;; (local (defthm posp-integer-length-denom
  ;;          (posp (integer-length (denominator x)))
  ;;          :hints (("goal" :use ((:instance rational-implies1 (x x)))))
  ;;          :rule-classes :type-prescription))

  ;; (local (defthm x-times-expt-2-integer-length-denom
  ;;          (implies (and (rationalp x)
  ;;                        (equal (denominator x)
  ;;                               (ash 1 (+ -1 (integer-length (denominator x))))))
  ;;                   (equal (* x (expt 2 (integer-length (denominator x))))
  ;;                          (* 2 (numerator x))))
  ;;          :hints (("goal" :in-theory (e/d (bitops::ash-is-expt-*-x)
  ;;                                          (rational-implies2
  ;;                                           ACL2::*-R-DENOMINATOR-R))
  ;;                   :use ((:instance rational-implies2 (x x)))
  ;;                   :expand ((expt 2 (integer-length (denominator x))))))))

  ;; (local (defthm numerator/expt-2-integer-length-denom
  ;;          (implies (and (rationalp x)
  ;;                        (equal (denominator x)
  ;;                               (ash 1 (+ -1 (integer-length (denominator x))))))
  ;;                   (equal (* (numerator x) (/ (expt 2 (integer-length (denominator x)))))
  ;;                          (* 1/2 x)))
  ;;          :hints (("goal" :in-theory (e/d (bitops::ash-is-expt-*-x)
  ;;                                          (rational-implies2
  ;;                                           ACL2::*-R-DENOMINATOR-R))
  ;;                   :use ((:instance rational-implies2 (x x)))
  ;;                   :expand ((expt 2 (integer-length (denominator x))))))))

  (local (defthm numerator/expt-2-integer-length-denom
           (implies (and (rationalp x)
                         (equal (denominator x)
                                (* 1/2 (expt 2 (integer-length (denominator x))))))
                    (equal (* (numerator x) (/ (expt 2 (integer-length (denominator x)))))
                           (* 1/2 x)))
           :hints (("goal" :in-theory (e/d (bitops::ash-is-expt-*-x)
                                           (rational-implies2
                                            ACL2::*-R-DENOMINATOR-R))
                    :use ((:instance rational-implies2 (x x)))
                    :expand ((expt 2 (integer-length (denominator x))))))))

  (local (defthm unsigned-byte-p-by-integer-length
           (implies (and (natp x)
                         (natp n)
                         (<= (integer-length x) n))
                    (unsigned-byte-p n x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (in-theory (disable bitops::ash-of-ash
                             right-shift-to-logtail)))

  ;; (local (defthm integerp-minus
  ;;          (implies (integerp x)
  ;;                   (integerp (- x)))))

  (local (defthm natp-abs
           (implies (integerp x)
                    (natp (abs x)))
           :rule-classes :type-prescription))

  (local (defthm posp-abs
           (implies (not (zip x))
                    (posp (abs x)))
           :hints(("Goal" :in-theory (enable zip abs)))
           :rule-classes :type-prescription))

  (local (defthm abs-*-fp-sign-value
           (implies (integerp x)
                    (equal (* (abs x) (fp-sign-value (fp-sign x))) (fix x)))
           :hints(("Goal" :in-theory (enable abs fp-sign-value fp-sign)))))

  (local (defthm abs-*-fp-sign-value-2
           (implies (integerp x)
                    (equal (* (abs x) (fp-sign-value (fp-sign x)) y) (* (fix x) y)))
           :hints(("Goal" :in-theory (enable abs fp-sign-value fp-sign)))))

  (local (defthm max-when-gte
           (implies (and (<= y x)
                         (rationalp x) (rationalp y))
                    (equal (max x y) x))
           :hints(("Goal" :in-theory (enable max)))))

  (local (in-theory (disable acl2::unsigned-byte-p-plus
                             not
                             acl2::natp-posp--1
                             acl2::natp-when-integerp
                             loghead-identity-by-bounds
                             acl2::loghead-identity
                             acl2::x*y>1-positive
                             acl2::equal-*-/-1
                             abs max)))

  (defret fp-value->rational-of-<fn>
    (implies okp
             (equal (fp-value->rational ans) (rfix x)))
    :hints(("Goal" :in-theory (enable fp-value->rational
                                      loghead-identity-by-bounds
                                      acl2::loghead-identity))
           (and stable-under-simplificationp
                '(:in-theory (enable ash-when-loghead-equal-0
                                     integerp-when-loghead-equal-0
                                     integerp-when-loghead-equal-0-neg)))
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable bitops::ash-is-expt-*-x)))
           (and stable-under-simplificationp
                '(:in-theory (enable expt-2-distrib)))
           )
    ;; :otf-flg t
    )

  ;; even worse :)
  ;; (defthm rational->fp-value-of-fp-value->rational
  ;;   (implies (member-equal (fp-value->type x) '(:normal :denorm :zero))
  ;;            (equal (rational->fp-value (fp-value->rational x))
  ;;                   (mv t (loghead (fp-size-width size) x))))
  ;;   :hints(("Goal" :in-theory (enable fp-value->rational
  ;;                                     fp-size-width))))
  )

(define rational->fp-value! ((x rationalp)
                             &key ((size fp-size-p) 'size))
  :parents (rational->fp-value)
  :short "Calls @(see rational->fp-value) but drops the @('okp') indicator from returned values."
  :enabled t
  (b* (((mv ?ok ans) (rational->fp-value x)))
    ans))

(defsection fp-arith-triple
  :set-as-default-parent t
  :autodoc nil

  (fty::defprod
    fp-arith-triple
    :parents (fp-common)
    :short "Our internal 'working' representation of an FP value:
 @('exp') is the exponent of the least-significant bit of the mantissa
 @('man') (includes J-bit)."

    :long "<p>We use @('fp-arith-triple') for all kinds of intermediate FP
values (with the @('exp') adjusted as described above).  See document 'Floating
Point Reference Sheet for Intel(R) Architecture' (available at
https://software.intel.com/en-us/articles/floating-point-reference-sheet-for-intel-architecture)
for details.</p>

 <ol>

  <li>@('IPR') (Infinitely Precise Result) or, alternatively,
  @('URPR') (Unnormalized Infintely Precise Result)</li>

  <li>@('RPR') (Reduced Precision Result)</li>

  <li>@('WPR') (Working Precision Result)</li>

  <li>@('DRPR') (Denormalized Reduced Precision Result)</li>

 </ol>

 <p>We obtain the @('arith-triple') corresponding to a FP
 operand (@(tsee fp-value)) using the function @(tsee
 fp-value-to-arith-triple). As the calculation proceeds from the
 @('IPR/URPR') through to @('WPR') (or @('DRPR'), if needed), the
 final @('arith-triple') is expected to have the same sign and
 mantissa as the final result, but the exponent still reflects that of
 the LSB of the mantissa. We fix this exponent using the function
 @(tsee fp-arith-triple-to-value), which returns an appropriate @(tsee
 fp-value). Note that @(see fp-arith-triple-to-value) only affects the
 exponent---it is NOT a general-purpose function that can convert an
 @('IPR') (say) to an appropriate @('fp-value').</p>"

    ((sign bitp)
     (exp integerp)
     (man natp)))

  (define fp-arith-triple->rational ((x fp-arith-triple-p))
    :short "Return rational number equivalent of a given @(see fp-arith-triple)"
    :returns (val rationalp :rule-classes :type-prescription)
    (b* (((fp-arith-triple x)))
      (* (fp-sign-value x.sign) x.man (expt 2 x.exp)))
    ///
    (defretd <fn>-equal-0
      (iff (equal 0 val)
           (equal (fp-arith-triple->man x) 0))))

  (define fp-value-to-arith-triple ((x fp-value-p)
                                    &key ((size fp-size-p) 'size))
    :short "Convert an @(tsee fp-value) to an @(tsee fp-arith-triple)"
    :guard (member-equal (fp-value->type x) '(:normal :denorm :pseudo-denorm :zero))
    :returns (arith-triple fp-arith-triple-p)
    (b* (((fp-size size))
         ((fp-value x))
         ((when (eql x.type :zero))
          (make-fp-arith-triple :sign x.sign :exp 0 :man 0))
         (lsb-exp-bias (+ size.frac-size size.exp-bias))
         (exp (- (max x.exp 1) lsb-exp-bias)))
      (make-fp-arith-triple :sign x.sign
                            :exp exp
                            :man x.man))
    :prepwork
    ((local
      (defthm non-zero-logapp-when-non-zero-high-bits
        (implies (posp high)
                 (equal (equal (logapp n low high)
                               0)
                        nil))
        :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
                                          bitops::ihsext-recursive-redefs)
                                         ())))))
     (local
      (defthm loghead-frac-size-of-frac-identity
        (equal (loghead (fp-size->frac-size size)
                        (fp-value->frac x))
               (fp-value->frac x))
        :hints (("goal" :in-theory (e/d (fp-value->frac)
                                        ())))))

     (local
      (defthm zero-man-implies-not-normal-or-denorm
        (implies (equal (fp-value->man x) 0)
                 (and (not (equal (fp-value->type x) :normal))
                      (not (equal (fp-value->type x) :denorm))))
        :hints (("goal" :in-theory (e/d (fp-value->type
                                         fp-value->man)
                                        ())))))

     (local
      (defthm zero-type-implies-zero-man
        (implies (equal (fp-value->type x) :zero)
                 (equal (fp-value->man x) 0))
        :hints (("goal" :in-theory (e/d (fp-value->type
                                         fp-value->man)
                                        ()))))))
    ///

    (defret <fn>.sign-unchanged
      (b* (((fp-value x))
           ((fp-arith-triple arith-triple)))
        (equal arith-triple.sign x.sign)))

    (defret <fn>.man-unchanged
      (b* (((fp-value x))
           ((fp-arith-triple arith-triple)))
        (equal arith-triple.man x.man)))

    (defret <fn>.exp-for-zero-inputs
      (b* (((fp-size size))
           ((fp-value x))
           ((fp-arith-triple arith-triple)))
        (implies (eql x.type :zero)
                 (equal arith-triple.exp 0))))

    (local
     (defthm unsigned-byte-p-of-fp-value->exp
       (b* (((fp-size size))
            ((fp-value x)))
         (unsigned-byte-p size.exp-size x.exp))
       :hints (("goal" :in-theory (e/d (fp-value->exp) ())))))

    (local (include-book "centaur/bitops/ash-bounds" :dir :system))
    ;; (local (include-book "arithmetic-3/top" :dir :system))

    (local
     (defthm ash-helper-lemma-1
       (implies (and (integerp n)
                     (< 1 n))
                (= (+ (ash 1 (+ -1 n)) (ash 1 (+ -1 n)))
                   (ash 1 n)))
       :hints (("goal"
                :use ((:instance bitops::expt-2-is-ash (n n))
                      (:instance bitops::expt-2-is-ash (n (1- n))))
                :expand ((expt 2 n))))
       :rule-classes (:rewrite :linear)))

    (local (defthmd ash-of-n-greater-than-1
             (implies (< 1 (nfix n))
                      (< 2 (ash 1 n)))
             :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                                bitops::ihsext-recursive-redefs)))))

    (local
     (defthm ash-helper-lemma-2
       (implies (natp n)
                (equal (equal (ash 1 n) 2)
                       (equal n 1)))
       :hints(("Goal" :use ash-of-n-greater-than-1
               :cases ((equal n 0)
                       (equal n 1))))))

    (defret lower-bound-of-<fn>.exp
      (b* (((fp-size size))
           ((fp-arith-triple arith-triple))
           (lsb-emin (+ size.emin (- size.frac-size))))
        (<= lsb-emin arith-triple.exp))
      :hints (("goal" :in-theory (e/d (fp-value-to-arith-triple
                                       fp-size->emin
                                       fp-size->exp-bias)
                                      ())))
      :rule-classes :linear)

    (defret upper-bound-of-<fn>.exp-non-zero
      (b* (((fp-size size))
           ((fp-value x))
           ((fp-arith-triple arith-triple))
           (lsb-emax (+ size.emax (- size.frac-size))))
        (implies (and (< 1 size.exp-size)
                      (< x.exp (logmask size.exp-size))
                      (not (eql x.type :zero)))
                 (<= arith-triple.exp lsb-emax)))
      :hints (("goal"
               :use ((:instance unsigned-byte-p-of-fp-value->exp))
               :in-theory (e/d (fp-value-to-arith-triple
                                fp-size->emax
                                fp-size->exp-bias
                                bitops::expt-2-is-ash
                                logmask
                                unsigned-byte-p)
                               (unsigned-byte-p-of-fp-value->exp))))
      :rule-classes :linear)

    (defret <fn>-preserves-rational-value
      (b* (((fp-value x)))
        (implies (member-equal x.type '(:normal :denorm :pseudo-denorm :zero))
                 (equal (fp-arith-triple->rational arith-triple)
                        (fp-value->rational x))))
      :hints(("Goal" :in-theory (enable fp-value->rational fp-value->type
                                        fp-arith-triple->rational))))

    (defret fp-arith-triple->exp-of-<fn>
      (equal (fp-arith-triple->exp arith-triple)
             (if (equal (fp-value->type x) :zero)
                 0
               (- (max (fp-value->exp x) 1)
                  (+ (fp-size->exp-bias)
                     (fp-size->frac-size size))))))

    (in-theory (disable fp-arith-triple->exp-of-fp-value-to-arith-triple)))

  (define fp-arith-triple-to-value ((x fp-arith-triple-p)
                                    &key
                                    ((size fp-size-p) 'size))
    :short "Convert an @('fp-arith-triple') (a @('WPR') or @('DRPR')) to
  @('fp-value') only by adjusting the exponent"
    :returns (value fp-value-p)
    :guard (b* (((fp-arith-triple x))
                ((fp-size size))
                (lsb-emin (+ size.emin (- size.frac-size)))
                (lsb-emax (+ size.emax (- size.frac-size))))
             (and
              (<= lsb-emin x.exp)
              (<= x.exp lsb-emax)
              (<= (integer-length x.man) (1+ size.frac-size))))
    (b* (((fp-size size))
         ((fp-arith-triple x))
         ((when (eql x.man 0)) ;; Zero
          (make-fp-value :sign x.sign :exp 0 :frac 0))
         (lsb-exp-bias (+ size.frac-size size.exp-bias))
         (lsb-emin (+ size.emin (- size.frac-size)))
         (exp (if (and (eql x.exp lsb-emin)
                       (not (logbitp size.frac-size x.man)))
                  ;; Denormal
                  0
                ;; Normal
                (+ x.exp lsb-exp-bias))))
      (make-fp-value :sign x.sign
                     :exp exp
                     :frac (loghead size.frac-size x.man)
                     :jbit (logbit size.frac-size x.man)))

    ///

    (local (in-theory (e/d (fp-value-to-arith-triple
                            fp-value->type)
                           ())))

    (local
     (defthm logbitp-frac-size-of-fp-value->man
       (b* (((fp-size size)))
         (equal (logbitp size.frac-size (fp-value->man x))
                (equal (fp-value->jbit x) 1)))
       :hints (("goal" :in-theory (e/d (fp-value->man) ())))))

    (local
     (defthm loghead-exp-size-of-fp-value->exp
       (b* (((fp-size size)))
         (equal (loghead size.exp-size (fp-value->exp x))
                (fp-value->exp x)))
       :hints (("goal" :in-theory (e/d (fp-value->exp) ())))))

    (local
     (defthm loghead-frac-size-of-fp-value->frac
       (b* (((fp-size size)))
         (equal (loghead size.frac-size (fp-value->frac x))
                (fp-value->frac x)))
       :hints (("goal" :in-theory (e/d (fp-value->frac)
                                       ())))))

    (local
     (defthm loghead-frac-size-of-fp-value->man
       (b* (((fp-size size)))
         (equal (loghead size.frac-size (fp-value->man x))
                (fp-value->frac x)))
       :hints (("goal" :in-theory (e/d (fp-value->frac
                                        fp-value->man)
                                       ())))))

    (local
     (defthm logapp-equal-0
       (iff (equal (logapp w x y) 0)
            (and (equal (loghead w x) 0)
                 (zip y)))
       :hints(("Goal" :in-theory
               (enable* bitops::ihsext-inductions
                        bitops::ihsext-recursive-redefs)))))

    (defthm normal-man-is-non-zero
      (b* (((fp-value x)))
        (implies (eql x.type :normal)
                 (not (equal x.man 0))))
      :hints (("goal" :in-theory (e/d (fp-value->type
                                       fp-value->man)
                                      ()))))

    (defthm denorm-man-is-non-zero
      (b* (((fp-value x)))
        (implies (eql x.type :denorm)
                 (not (equal x.man 0))))
      :hints (("goal" :in-theory (e/d (fp-value->type
                                       fp-value->man
                                       fp-value->frac)
                                      ()))))

    (defthm pseudo-denorm-man-is-non-zero
      (b* (((fp-value x)))
        (implies (eql x.type :pseudo-denorm)
                 (not (equal x.man 0))))
      :hints (("goal" :in-theory (e/d (fp-value->type
                                       fp-value->man
                                       fp-value->frac)
                                      ()))))

    (defthm integer-length-of-normal-man
      (b* (((fp-size size))
           ((fp-value x)))
        (implies (or (eql x.type :normal)
                     (eql x.type :pseudo-denorm))
                 (equal (integer-length x.man) (1+ size.frac-size))))
      :hints (("goal" :in-theory (e/d (fp-value->type
                                       fp-value->man)
                                      ()))))

    (local (include-book "centaur/bitops/integer-length" :dir :system))

    (defthm integer-length-of-denorm-man-bounds
      (b* (((fp-size size))
           ((fp-value x)))
        (implies (eql x.type :denorm)
                 (and
                  (< 0 (integer-length x.man))
                  (< (integer-length x.man) (1+ size.frac-size)))))
      :hints (("goal" :in-theory (e/d (fp-value->type
                                       fp-value->man
                                       fp-value->frac)
                                      ())))
      :rule-classes :linear)

    (local
     (defthm loghead-n-1
       (implies (posp n)
                (equal (loghead n 1) 1))
       :hints (("goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                         bitops::ihsext-inductions)
                                        ())))))

    (local (defthm sum-negs-equal-0-implies-equal
             (implies (and (equal (+ (- a) (- b) c) 0)
                           (acl2-numberp a)
                           (acl2-numberp b)
                           (acl2-numberp c))
                      (equal (+ a b) c))))

    ;; (local (include-book "arithmetic-5/top" :dir :system))

    (local
     (defthm fp-value->man-non-zero-lemma
       (implies (and (equal (fp-value->jbit value) 0)
                     (not (equal 0 (fp-value->frac value))))
                (not (equal (fp-value->man value) 0)))
       :hints (("goal" :in-theory (e/d (fp-value->man fp-value->frac)
                                       ())))))

    (local (defthm unsigned-byte-p-of-1
             (implies (posp n)
                      (unsigned-byte-p n 1))
             :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

    (local (defthm unsigned-byte-p-of-max
             (implies (and (unsigned-byte-p n x)
                           (unsigned-byte-p n y))
                      (unsigned-byte-p n (max x y)))
             :hints(("Goal" :in-theory (enable max unsigned-byte-p)))))

    (defthmd fp-value-to-arith-triple-and-back
      ;; Sanity check
      (b* (((fp-size size))
           ((fp-value value))
           (arith-triple (fp-value-to-arith-triple value))
           ((fp-value value1) (fp-arith-triple-to-value arith-triple)))
        (implies (and (or (eql value.type :zero)
                          (eql value.type :normal)
                          (eql value.type :denorm)))
                 (and
                  (equal value1.sign value.sign)
                  (equal value1.exp value.exp)
                  (equal value1.frac value.frac))))
      :hints (("goal" :in-theory (e/d (fp-size->emin
                                       fp-size->emax)
                                      (max)))
              (and stable-under-simplificationp
                   '(:in-theory (enable max)))))

    ;; (defret <fn>-preserves-rational-value
    ;;   (implies (and (unsigned-byte-p (+ 1 (fp-size->frac-size size)) (fp-arith-triple->man x))
    ;;                 (or (equal (integer-length (fp-arith-triple->man x)) (+ 1 (fp-size->frac-size size)))
    ;;                     (equal (fp-arith-triple->exp x) (- (fp-size->emin size) (fp-size->frac-size size))))
    ;;                 (<= (fp-arith-triple->exp x) (- (fp-size->emax size) (fp-size->frac-size size)))
    ;;                 (<= (- (fp-size->emin size) (fp-size->frac-size size)) (fp-arith-triple->exp x)))
    ;;            (equal (fp-value->rational value)
    ;;                   (fp-arith-triple->rational x)))
    ;;   :hints(("Goal" :in-theory (enable fp-value->rational
    ;;                                     fp-arith-triple->rational))))
    )

  (define fp-arith-leftshift ((x fp-arith-triple-p)
                              (n natp))
    :short "Shift @('x') left"
    :returns (new-x fp-arith-triple-p)
    (b* (((fp-arith-triple x))
         (n (lnfix n)))
      (change-fp-arith-triple x
                              ;; TODO: use bitops::limshift-loghead-of-ash
                              :man (ash x.man n)
                              :exp (- x.exp n)))

    ///

    (defret <fn>.sign-unchanged
      (b* (((fp-arith-triple x))
           ((fp-arith-triple new-x)))
        (equal new-x.sign x.sign)))

    (defret integer-length-of-<fn>.man
      (b* (((fp-arith-triple new-x))
           ((fp-arith-triple x)))
        (implies (and (natp n) (posp x.man))
                 (equal (integer-length new-x.man)
                        (+ n (integer-length x.man))))))

    (defret <fn>-preserves-rational-value
      (equal (fp-arith-triple->rational new-x)
             (fp-arith-triple->rational x))
      :hints(("Goal" :in-theory (enable fp-arith-triple->rational
                                        bitops::ash-is-expt-*-x)))))

  (define fp-arith-rightshift ((x fp-arith-triple-p)
                               (n natp))
    :short "Shift @('x') right"
    :long "<p>IMPORTANT: We discard bits in this function--make sure
  they are captured elsewhere, if needed.</p>"
    :returns (new-x fp-arith-triple-p)
    (b* (((fp-arith-triple x)))
      (change-fp-arith-triple x
                              ;; TODO: use bitops::limshift-loghead-of-ash
                              :man (logtail n x.man) ;;(ash x.man (- n))
                              :exp (+ x.exp (lnfix n))))
    ///

    (defret <fn>.sign-unchanged
      (b* (((fp-arith-triple x))
           ((fp-arith-triple new-x)))
        (equal new-x.sign x.sign)))

    (defret integer-length-of-<fn>.man
      (b* (((fp-arith-triple new-x))
           ((fp-arith-triple x)))
        (implies (natp n)
                 (equal (integer-length new-x.man)
                        (nfix (- (integer-length x.man) n))))))

    (local (include-book "centaur/bitops/integer-length" :dir :system))

    (defretd unsigned-byte-p-of-<fn>.man
      (b* (((fp-arith-triple new-x))
           ((fp-arith-triple x)))
        (implies (natp n)
                 (unsigned-byte-p (nfix (- (integer-length x.man) n)) new-x.man)))
      :hints (("goal" :in-theory (e/d (unsigned-byte-p nfix) ()))))

    (local (defthmd logcar-equals-x-minus-logcdr
             (equal (logcar x)
                    (- (ifix x)
                       (* 2 (logcdr x))))
             :hints(("Goal" :use ((:instance bitops::logcons-destruct (x x)))
                     :in-theory (e/d (logcons)
                                     (acl2::logcar-logcdr-elim
                                      bitops::logcons-destruct))))))

    (local (defthmd loghead-equals-x-minus-logtail
             (equal (loghead n x)
                    (- (ifix x)
                       (* (expt 2 (nfix n)) (logtail n x))))
             :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                                bitops::ihsext-recursive-redefs
                                                bitops::expt-2-is-ash)
                     :induct (loghead n x))
                    (and stable-under-simplificationp
                         '(:in-theory (enable logcons)))
                    (and stable-under-simplificationp
                         '(:in-theory (enable logcar-equals-x-minus-logcdr))))))

    (defretd rational-value-of-<fn>
      (implies (natp n)
               (equal (fp-arith-triple->rational new-x)
                      (- (fp-arith-triple->rational x)
                         (fp-arith-triple->rational
                          (change-fp-arith-triple x :man (loghead n (fp-arith-triple->man x)))))))
      :hints(("Goal" :in-theory (enable fp-arith-triple->rational))
             (and stable-under-simplificationp
                  '(:in-theory (enable loghead-equals-x-minus-logtail))))))

  (define fp-arith-triple-incr ((x fp-arith-triple-p))
    :returns (inc fp-arith-triple-p)
    (change-fp-arith-triple x :man (+ 1 (fp-arith-triple->man x)))
    ///
    (local (defthm right-distrib
             (equal (* (+ a b) c)
                    (+ (* a c) (* b c)))))
    (defretd <fn>-rational-value
      (equal (fp-arith-triple->rational inc)
             (+ (fp-arith-triple->rational x)
                (* (fp-sign-value (fp-arith-triple->sign x))
                   (expt 2 (fp-arith-triple->exp x)))))
      :hints(("Goal" :in-theory (enable fp-arith-triple->rational
                                        fp-sign-value))))))

;;--------------------------------------------------------------------------------

(define round-up ((sign bitp)
                  (l booleanp "LSB")
                  (r booleanp "Round")
                  (s booleanp "Sticky")
                  (rc fp-rc-p))
  :short "Make a round-up decision"
  :prepwork
  ((local (in-theory (e/d (rc->rounding-mode) ()))))
  :returns (bool booleanp :rule-classes :type-prescription)
  (b* ((l (acl2::bool-fix l))
       (r (acl2::bool-fix r))
       (s (acl2::bool-fix s)))
    (case (rc->rounding-mode rc)
      (:rne (and r (or l s)))
      (:rmi (if (eql sign 1)
                (or r s)
              nil))
      (:ri (if (eql sign 1)
               nil
             (or r s)))
      (t nil))))

(define normalize-arith-triple ((x fp-arith-triple-p)
                                &key
                                ((size fp-size-p) 'size)
                                ((sticky-in booleanp) 'nil)
                                (verbosep 'verbosep))
  :short "Normalize an @('IPR/URPR arith-triple') to get an
  @('RPR arith-triple')"
  :long "<p>Shift the mantissa until the leading 1 is in the J-bit
  position.</p>"
  :returns (mv (new-x fp-arith-triple-p)
               (roundp booleanp :rule-classes :type-prescription)
               (stickyp booleanp :rule-classes :type-prescription))

  (b* (((fp-arith-triple x))
       ((when (eql x.man 0))
        ;; fix exponent to 0
        (mv (change-fp-arith-triple x :exp 0)
            nil
            (mbe :logic (acl2::bool-fix sticky-in) :exec sticky-in) ))
       ((fp-size size))
       (man-len (integer-length x.man))
       (shiftCnt (- man-len (+ 1 size.frac-size)))
       (- (cw-verbose "~% shiftCnt: ~x0 ~%" shiftCnt)))
    (cond ((< 0 shiftCnt)
           (mv (fp-arith-rightshift x shiftCnt)
               (logbitp (1- shiftCnt) x.man)
               (if sticky-in t (not (eql (loghead (1- shiftCnt) x.man) 0)))))
          ((< shiftCnt 0)
           (mv (fp-arith-leftshift x (- shiftCnt))
               nil
               (mbe :logic (acl2::bool-fix sticky-in) :exec sticky-in)))
          (t
           (mv (fp-arith-triple-fix x)
               nil
               (mbe :logic (acl2::bool-fix sticky-in) :exec sticky-in)))))
  ///

  (defret <fn>.sign-unchanged
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x)))
      (equal new-x.sign x.sign)))

  (defret <fn>.exp-value
    (b* (((fp-size size))
         ((fp-arith-triple x))
         ((fp-arith-triple new-x))
         (man-len (integer-length x.man))
         (shiftCnt (- man-len (+ 1 size.frac-size))))
      (equal new-x.exp
             (if (eql x.man 0)
                 0
               (+ x.exp shiftCnt))))
    :hints (("goal" :in-theory (e/d (fp-arith-leftshift
                                     fp-arith-rightshift)
                                    ()))))

  (defret integer-length-of-<fn>.man
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((fp-size size)))
      (implies (posp x.man)
               (equal (integer-length new-x.man) (+ 1 size.frac-size)))))


  
  (local (defthm integer-length-of-left-shift-when-posp
           (implies (and (posp x) (natp n))
                    (equal (integer-length (ash x n))
                           (+ n (integer-length x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm left-shift-equal-0
           (implies (natp n)
                    (equal (Equal (ash x n) 0)
                           (equal (ifix x) 0)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm loghead-of-zp-width
           (implies (zp n)
                    (equal (loghead n x) 0))))

  (defthm normalize-arith-triple-of-left-shift
    (implies (not (equal 0 (fp-arith-triple->man x)))
             (equal (normalize-arith-triple (fp-arith-leftshift x shift) :verbosep verbosep)
                    (normalize-arith-triple x :verbosep verbosep)))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift
                                      fp-arith-rightshift
                                      bitops::loghead-of-ash))))

  ;; (local (Defthmd loghead-of-logtail
  ;;          (equal (loghead n (logtail m x))
  ;;                 (logtail m (loghead (+ (nfix n) (nfix m)) x)))))

  (local (defthm loghead-of-logtail-equal-0
           (implies (equal 0 (loghead shift x))
                    (equal (equal 0 (loghead head (logtail shift x)))
                           (equal 0 (loghead (+ (nfix head) (nfix shift)) x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm loghead-of-logtail-equal-0-2
           (implies (equal 0 (loghead (+ (nfix head) (nfix shift)) x))
                    (equal (equal 0 (loghead head (logtail shift x)))
                           t))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthmd loghead-equal-0-of-less
           (implies (and (equal (loghead n x) 0)
                         (<= (nfix m) (nfix n)))
                    (equal (equal (loghead m x) 0) t))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm logtail-nonzero-by-integer-length
           (implies (< (nfix shift) (integer-length x))
                    (not (equal 0 (logtail shift x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))
  
  
  (defret man-equal-0-of-<fn>
    (b* (((fp-arith-triple x))
         ((fp-arith-triple new-x)))
      (iff (equal new-x.man 0)
           (equal x.man 0)))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift
                                      fp-arith-rightshift))))

  

  (defret rational-equal-0-of-<fn>
    (iff (equal 0 (fp-arith-triple->rational new-x))
         (equal 0 (fp-arith-triple->rational x)))
    :hints (("goal"
             :in-theory (e/d (fp-arith-triple->rational-equal-0)
                             (<fn>)))))
  
  (defthm normalize-arith-triple-of-right-shift
    (b* (((fp-size size))
         ((fp-arith-triple x))
         ((mv impl-norm impl-round impl-sticky)
          (normalize-arith-triple (fp-arith-rightshift x shift) :verbosep verbosep))
         ((mv spec-norm spec-round spec-sticky)
          (normalize-arith-triple x :verbosep verbosep)))
      (implies (<= (+ 2 size.frac-size) (- (integer-length x.man) (nfix shift)))
               (and (equal impl-norm spec-norm)
                    (equal impl-round spec-round)
                    (implies (equal 0 (loghead shift x.man))
                             (equal impl-sticky spec-sticky)))))
    :hints(("Goal" :in-theory (enable fp-arith-rightshift
                                      bitops::loghead-of-ash))))

  (defthm normalize-arith-triple-of-right-shift-sticky
    (b* (((fp-size size))
         ((fp-arith-triple x))
         ((mv ?impl-norm ?impl-round impl-sticky)
          (normalize-arith-triple (fp-arith-rightshift x shift) :verbosep verbosep))
         ((mv ?spec-norm ?spec-round spec-sticky)
          (normalize-arith-triple x :verbosep verbosep)))
      (implies (<= (+ 2 size.frac-size) (- (integer-length x.man) (nfix shift)))
               (equal (or impl-sticky (not (equal 0 (loghead shift x.man))))
                      spec-sticky)))
    :hints(("Goal" :in-theory (enable fp-arith-rightshift
                                      bitops::loghead-of-ash))
           (and stable-under-simplificationp
                '(:in-theory (enable loghead-equal-0-of-less))))
    :rule-classes nil) ;; not a good rewrite rule

  (defthm normalize-arith-triple-norm-verbosep
    (implies (syntaxp (not (equal verbosep ''nil)))
             (equal (normalize-arith-triple x :verbosep verbosep)
                    (normalize-arith-triple x :verbosep nil))))

  (defretd mantissa-of-<fn>-norm
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((mv (fp-arith-triple new-x-norm) roundp-norm stickyp-norm)
          (normalize-arith-triple (make-fp-arith-triple :man x.man :sign 0 :Exp 0) :sticky-in sticky-in)))
      (implies (and (syntaxp (not (case-match x
                                    (('fp-arith-triple ''0 ''0 &) t)
                                    (('quote ('(sign . 0) '(exp . 0) &)) t)))))
               (and (equal new-x.man new-x-norm.man)
                    (equal roundp roundp-norm)
                    (equal stickyp stickyp-norm))))
    :hints(("Goal" :in-theory (enable fp-arith-rightshift
                                      fp-arith-leftshift))))

  (defretd exponent-of-<fn>-norm
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((mv (fp-arith-triple new-x-norm) ?roundp-norm ?stickyp-norm)
          (normalize-arith-triple (make-fp-arith-triple :man x.man :sign 0 :Exp 0) :sticky-in sticky-in)))
      (implies (and (syntaxp (not (case-match x
                                    (('fp-arith-triple ''0 ''0 &) t)
                                    (('quote ('(sign . 0) '(exp . 0) &)) t)))))
               (equal new-x.exp
                      (if (eql 0 x.man)
                          0
                        (+ x.exp new-x-norm.exp)))))
    :hints(("Goal" :in-theory (enable fp-arith-rightshift
                                      fp-arith-leftshift)))))


;; Optimizations for symbolic simulation of normalize-arith-triple

(define fp-arith-leftshift-opt ((final-man-width natp
                                                 "Must be an upper bound for @('n + length(x.man)').
                                                  Should be constant for best symbolic simulation performance.")
                                (x fp-arith-triple-p)
                                (n natp))
  :guard (<= (+ n (integer-length (fp-arith-triple->man x))) final-man-width)
  :returns (new-x fp-arith-triple-p)
  :short "Another version for leftshift that is optimized for
  symbolic simulation"
  (b* ((n (lnfix n))
       (final-man-width (lnfix final-man-width))
       ((fp-arith-triple x)))
    (change-fp-arith-triple
     x
     :man (bitops::limshift-loghead-of-ash final-man-width x.man n)
     :exp (- x.exp n)))

  ///

  (local
   (defthm loghead-of-integer-length-+-ash-simple
     (implies (and (<= (integer-length x) m) (natp m) (natp n) (natp x))
              (equal (loghead (+ m n) (ash x n))
                     (ash x n)))
     :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
                                       bitops::ihsext-recursive-redefs)
                                      ())))))

  (local
   (defthm loghead-of-integer-length-+-ash
     (implies (and (<= (+ n (integer-length x)) m)
                   (natp m)
                   (natp n)
                   (natp x))
              (equal (loghead m (ash x n))
                     (ash x n)))
     :hints (("goal"
              :use ((:instance loghead-of-integer-length-+-ash-simple
                               (x x)
                               (m (+ m (- n)))
                               (n n)))
              :in-theory (e/d* ()
                               (loghead-of-integer-length-+-ash-simple))))))

  (local (in-theory (e/d (fp-arith-leftshift) ())))

  (defretd <fn>-is-fp-arith-leftshift
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((fp-arith-triple new-x1) (fp-arith-leftshift x n)))
      (implies (<= (+ (nfix n) (integer-length x.man)) (nfix final-man-width))
               (equal new-x new-x1)))
    :hints (("goal" :in-theory (e/d ()
                                    (loghead-of-integer-length-+-ash))
             :use ((:Instance loghead-of-integer-length-+-ash
                              (m (nfix final-man-width))
                              (x (fp-arith-triple->man x))
                    (n (nfix n))))))))


(define fp-arith-rightshift-opt ((final-man-width natp
                                                    "Must be an upper bound for @('length(x.man) - n').
                                                  Should be constant for best symbolic simulation performance.")
                                 (x fp-arith-triple-p)
                                 (n natp))
  :guard (<= (- (integer-length (fp-arith-triple->man x)) n) final-man-width)
  :returns (new-x fp-arith-triple-p)
  :short "Another version for rightshift that is optimized for symbolic
simulation.  This just does a loghead of the final mantissa to truncate off
upper bits that may otherwise be always zero without being syntactically zero."
  (b* ((n (lnfix n))
       ((fp-arith-triple x)))
    (change-fp-arith-triple
     x
     :man (loghead final-man-width (logtail n x.man))
     :exp (+ x.exp n)))

  ///

  (local (defthm unsigned-byte-p-by-integer-length
           (implies (and (natp n)
                         (natp x)
                         (<= (integer-length x) n))
                    (unsigned-byte-p n x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))


  (local (defthm integer-length-equal-0
           (implies (natp x)
                    (equal (Equal (integer-length x) 0)
                           (equal x 0)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (defretd <fn>-is-fp-arith-rightshift
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((fp-arith-triple new-x1) (fp-arith-rightshift x n)))
      (implies (<= (- (integer-length x.man) (nfix n))
                   (nfix final-man-width))
               (equal new-x new-x1)))
    :hints (("goal" :in-theory (e/d (fp-arith-rightshift))
             :cases ((< (nfix final-man-width) (nfix n))))
            (and stable-under-simplificationp
                 '(:cases ((natp final-man-width)))))))

(defsection normalize-arith-triple-fgl
  (local (defthm fp-arith-rightshift-when-zp
           (implies (zp n)
                    (equal (fp-arith-rightshift x n)
                           (fp-arith-triple-fix x)))
           :hints(("Goal" :in-theory (enable fp-arith-rightshift)))))

  (fgl::def-fgl-rewrite normalize-arith-triple-fgl
    (equal (normalize-arith-triple x :sticky-in sticky-in)
           (b* (((fp-arith-triple x))
                ((fp-size size))
                ((when (eql x.man 0))
                 (mv (change-fp-arith-triple x :exp 0)
                     nil (and sticky-in t)))
                (man-len (integer-length x.man))
                (shiftCnt (fgl::binary-minus man-len (+ 1 size.frac-size)))
                (round-idx (fgl::binary-minus man-len (+ 2 size.frac-size)))
                (- (cw-verbose "~% shiftCnt: ~x0 ~%" shiftCnt))
                (new-x (if (<= 0 shiftcnt)
                           (fp-arith-rightshift-opt (+ 1 size.frac-size) x shiftCnt)
                         (fp-arith-leftshift-opt (+ 1 size.frac-size) x (- shiftCnt))))
                ((mv roundp stickyp)
                 (if (<= 0 round-idx)
                     (mv (logbitp round-idx x.man)
                         (not (eql (loghead round-idx x.man) 0)))
                   (mv nil nil))))
             (mv new-x roundp (or (and sticky-in t) stickyp))))
    :hints(("Goal" :in-theory (enable normalize-arith-triple
                                      fp-arith-leftshift-opt-is-fp-arith-leftshift
                                      fp-arith-rightshift-opt-is-fp-arith-rightshift
                                      fgl::binary-minus))))

  (fgl::disable-definition normalize-arith-triple-fn))


(define round-arith-triple ((x fp-arith-triple-p "Normalized arith-triple; see @(tsee normalize-arith-triple)")
                            (roundp booleanp)
                            (stickyp booleanp)
                            (rc fp-rc-p)
                            &key
                            ((size fp-size-p) 'size)
                            (verbosep 'verbosep))
  :short "Round an @('RPR arith-triple') to get a @('WPR arith-triple')"
  :returns (mv (new-x fp-arith-triple-p :hyp (fp-arith-triple-p x))
               (round-up booleanp :rule-classes :type-prescription)
               (exp-bumped booleanp :rule-classes :type-prescription))

  :guard (b* (((fp-size size))
              ((fp-arith-triple x)))
           (implies (not (equal x.man 0))
                    (equal (integer-length x.man) (+ 1 size.frac-size))))

  (b* (((fp-size size))
       ((fp-arith-triple x))
       ((when (eql x.man 0))
        ;; rounding up from 0 doesn't make any sense
        (mv (change-fp-arith-triple x :exp 0) nil nil))
       (round-up? (round-up x.sign (logbitp 0 x.man) roundp stickyp rc))
       (- (cw-verbose "~% Round-up? ~x0 ~%" round-up?))
       ((unless round-up?) (mv (fp-arith-triple-fix x) nil nil))
       (x-rnd (change-fp-arith-triple x :man (+ 1 x.man)))
       ((mv x-norm ?norm-roundp ?norm-stickyp) (normalize-arith-triple x-rnd)))
    (mv x-norm t (not (eql x.exp (fp-arith-triple->exp x-norm)))))

  ///
  (defretd <fn>-normalize-verbosep
    (implies (syntaxp (not (equal verbosep ''nil)))
             (equal <call>
                    (let ((verbosep nil)) <call>))))

  (defret mant-equal-0-of-<fn>
    (iff (equal 0 (fp-arith-triple->man new-x))
         (equal 0 (fp-arith-triple->man x))))

  (defret rational-equal-0-of-<fn>
    (iff (equal 0 (fp-arith-triple->rational new-x))
         (equal 0 (fp-arith-triple->rational x)))
    :hints (("goal"
             :in-theory (e/d (fp-arith-triple->rational-equal-0)
                             (<fn>)))))
  
  (local
   (defthm integer-length-+-1-lemma
     (implies (and (not (equal (integer-length (+ 1 x))
                               (integer-length x)))
                   (natp x))
              (equal (integer-length (+ 1 x))
                     (+ 1 (integer-length x))))
     :hints (("goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                       bitops::ihsext-inductions)
                                      ())))))

  (defret <fn>.sign-unchanged
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x)))
      (equal new-x.sign x.sign)))

  (defret <fn>.exp-value-unchanged-when-not-round-up
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         (round-up? (round-up x.sign (logbitp 0 x.man) roundp stickyp rc)))
      (implies (and (not round-up?)
                    (not (eql 0 x.man)))
               (equal new-x.exp x.exp))))

  (defret <fn>.exp-value-when-round-up-no-normalization-needed
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((fp-size size))
         (round-up? (round-up x.sign (logbitp 0 x.man) roundp stickyp rc)))
      (implies (and round-up?
                    (equal (integer-length x.man) (integer-length (+ 1 x.man)))
                    (equal (integer-length x.man) (+ 1 size.frac-size)))
               (equal new-x.exp x.exp)))
    :hints (("goal" :in-theory (e/d (normalize-arith-triple) ()))))

  (defret <fn>.exp-value-when-round-up-normalization-needed
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((fp-size size))
         (round-up? (round-up x.sign (logbitp 0 x.man) roundp stickyp rc)))
      (implies (and round-up?
                    (< (integer-length x.man) (integer-length (+ 1 x.man)))
                    (equal (integer-length x.man) (+ 1 size.frac-size)))
               (equal new-x.exp (+ 1 x.exp))))
    :hints (("goal" :in-theory (e/d (normalize-arith-triple
                                     fp-arith-rightshift)
                                    ()))))

  (defretd <fn>.exp-possibilities
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((fp-size size)))
      (implies (equal (integer-length x.man) (+ 1 size.frac-size))
               (or (equal new-x.exp x.exp)
                   (equal new-x.exp (+ 1 x.exp)))))
    :hints (("goal"
             :use ((:instance <fn>.exp-value-unchanged-when-not-round-up)
                   (:instance <fn>.exp-value-when-round-up-normalization-needed)
                   (:instance <fn>.exp-value-when-round-up-no-normalization-needed))
             :in-theory (e/d ()
                             (<fn>.exp-value-unchanged-when-not-round-up
                              <fn>.exp-value-when-round-up-normalization-needed
                              <fn>.exp-value-when-round-up-no-normalization-needed)))))

  (defret integer-length-of-<fn>.man
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((fp-size size)))
      (implies (equal (integer-length x.man) (+ 1 size.frac-size))
               (equal (integer-length new-x.man) (+ 1 size.frac-size)))))

  (defretd mantissa-of-<fn>-norm-round-nearest
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((mv (fp-arith-triple new-x-norm) round-up-norm exp-bumped-norm)
          (round-arith-triple (make-fp-arith-triple :man x.man :sign 0 :Exp 0) roundp stickyp rc)))
      (implies (and (syntaxp (not (case-match x
                                    (('fp-arith-triple ''0 ''0 &) t)
                                    (('quote ('(sign . 0) '(exp . 0) &)) t))))
                    (equal rc (rounding-mode->rc :rne)))
               (and (equal new-x.man new-x-norm.man)
                    (equal round-up round-up-norm)
                    (equal exp-bumped exp-bumped-norm))))
    :hints(("Goal" :in-theory (enable round-up
                                      mantissa-of-normalize-arith-triple-norm))))

  (defretd exponent-of-<fn>-norm-round-nearest
    (b* (((fp-arith-triple new-x))
         ((fp-arith-triple x))
         ((mv (fp-arith-triple new-x-norm) ?round-up-norm ?exp-bumped-norm)
          (round-arith-triple (make-fp-arith-triple :man x.man :sign 0 :Exp 0) roundp stickyp rc)))
      (implies (and (syntaxp (not (case-match x
                                    (('fp-arith-triple ''0 ''0 &) t)
                                    (('quote ('(sign . 0) '(exp . 0) &)) t))))
                    (equal rc (rounding-mode->rc :rne)))
               (equal new-x.exp
                      (if (equal x.man 0)
                          0
                        (+ x.exp new-x-norm.exp)))))
    :hints(("Goal" :in-theory (enable round-up)))
    :otf-flg t))

(defbitstruct fp-postproc-bits
  ((norm-lsb booleanp    "LSB from the RPR (normalized, unrounded result)")
   (norm-roundp booleanp "Round bit from RPR")
   (norm-stickyp booleanp "Sticky bit from RPR")
   (norm-round-up booleanp "Rounding decision from RPR")
   (norm-exp-bumped booleanp "RPR was rounded up to next exponent")
   (denorm-lsb    booleanp "LSB after denormalizing, before rounding, if applicable")
   (denorm-roundp booleanp "Round bit after denormalizing")
   (denorm-stickyp booleanp "Sticky bit after denormalizing")
   (denorm-round-up booleanp "Rounding decision after denormalizing")
   (denorm-to-normal booleanp "Rounded up to least normal after denormalizing")
   (underflow booleanp "Underflowed, including flushed or rounded to zero or rounded up to normal")
   (underflow-extreme booleanp "result was below x87 undervalue exponent range")
   (overflow-round-up booleanp "Round decision for overflow (up to inf or down to max norm)")
   (overflow booleanp "Overflowed -- RPR exponent was too high")
   (overflow-extreme booleanp "result was past x87 overvalue exponent range")

   ;; This is intended to provide info not given by the combination of final flags and result.
   ;; But this underflow flag is complicated enough to recreate that we'll store it anyway.
   ;; It should be UF OR final result is denorm OR denorm-to-normal.
   ;; UF covers rounded inexactly to 0 and flushed to 0 cases, denorm-to-normal
   ;; obv covers rounded up to normal, otherwise result remains denormal.
   ))

(define denormalize-and-round-arith-triple ((x fp-arith-triple-p
                                               "@('RPR') (from @(tsee normalize-arith-triple)), NOT @('WPR')")
                                            (rc fp-rc-p)
                                            (sticky-in booleanp)
                                            &key
                                            ((size fp-size-p) 'size)
                                            (verbosep 'verbosep))
  :short "Denormalize and round a tiny @('RPR arith-triple') to get a
  @('DRPR arith-triple')"

  :guard (b* (((fp-size size))
              ((fp-arith-triple x))
              (lsb-emin (+ size.emin (- size.frac-size))))
           (and (equal (integer-length x.man) (1+ size.frac-size))
                (< x.exp lsb-emin)))

  :returns (mv (new-x fp-arith-triple-p :hyp (fp-arith-triple-p x))
               (bits fp-postproc-bits-p))

  (b* (((fp-size size))
       ((fp-arith-triple x))
       (lsb-emin (+ size.emin (- size.frac-size)))
       (denormalize-amt (- lsb-emin x.exp))
       (- (cw-verbose "~% [~x0] denormalize-amt: ~x1 ~%" __function__ denormalize-amt))
       ((fp-arith-triple x-dnrm) (fp-arith-rightshift x denormalize-amt))
       (- (cw-verbose "~% [~x0] denormalized arith-triple: ~x1 ~%" __function__ x-dnrm))

       (lsb (logbitp 0 x-dnrm.man))
       (roundp-index (1- denormalize-amt))
       (- (cw-verbose "~% [~x0] roundp-index: ~x1 ~%" __function__ roundp-index))
       (roundp (logbitp roundp-index x.man))
       ;; (- (cw-verbose "~% [~x0] roundp: ~x1 ~%" __function__ roundp))
       ;; (sticky-bits (loghead (1- denormalize-amt) x.man))
       ;; (- (cw-verbose "~% [~x0] sticky-bits: ~x1 ~%" __function__ sticky-bits))

       ;; Optimization -- needed for fscale, where sometimes the exp is -huge
       ;; and therefore denormalize-amt is huge, i.e. 2^17 bits wide.
       ;; By the guard, the length of x.man is 1+size.frac-size.
       ;; So instead of comparing (loghead (1- denormalize-amt) x.man) to 0
       ;; we can instead use
       ;; (limshift-loghead-of-logapp (1+ size.frac-size) (1- denormalize-amt) x.man 0)
       ;; = (loghead (1+ size.frac-size) (logapp (1- denormalize-amt) x.man 0))
       ;; = (loghead (1+ size.frac-size) (loghead (1- denormalize-amt) x.man))
       ;; = (loghead (1- denormalize-amt) x.man) by loghead-identity.

       (stickyp (or (acl2::bool-fix sticky-in)
                    (not (equal 0 (bitops::limshift-loghead-of-logapp
                                   (1+ size.frac-size)
                                   (1- denormalize-amt)
                                   x.man 0)))))
       (- (cw-verbose "~% [~x0] stickyp: ~x1 ~%" __function__ stickyp))
       (round-up? (round-up x.sign lsb roundp stickyp rc))
       (- (cw-verbose "~% [~x0] Round-up? ~x1 ~%" __function__ round-up?))
       (x-rnd
        ;; x-rnd can be either a denormal number or the smallest
        ;; possible normal number.
        (if round-up?
            (change-fp-arith-triple x-dnrm :man (+ 1 x-dnrm.man))
          x-dnrm))
       (- (cw-verbose "~% [~x0] DRPR: ~x1 ~%" __function__ x-rnd)))
    (mv x-rnd
        (make-fp-postproc-bits
         :denorm-lsb (logbitp 0 x-dnrm.man)
         :denorm-roundp roundp
         :denorm-stickyp stickyp
         :denorm-round-up round-up?
         :denorm-to-normal (eql (fp-arith-triple->man x-rnd)
                                (ash 1 size.frac-size)))))

  ///

  (defret <fn>.sign-unchanged
    (b* (((fp-arith-triple x))
         ((fp-arith-triple new-x)))
      (equal new-x.sign x.sign)))

  (defret <fn>.exp-is-lsb-emin
    (b* (((fp-size size))
         ((fp-arith-triple x))
         ((fp-arith-triple new-x))
         (lsb-emin (+ size.emin (- size.frac-size))))
      (implies (<= x.exp lsb-emin)
               (equal new-x.exp lsb-emin)))
    :hints (("goal" :in-theory (e/d (fp-arith-rightshift) ()))))

  (local
   (defthm logtail-by->=-integer-length==0
     (implies (and (<= (integer-length x) n)
                   (natp n)
                   (natp x))
              (equal (logtail n x) 0))
     :hints (("goal" :in-theory (e/d* (bitops::ihsext-inductions
                                       bitops::ihsext-recursive-redefs)
                                      ())))))

  (local
   (defthm mantissa-is-zero-when-denormalize-amt->-1+frac-size
     (b* (((fp-size size))
          ((fp-arith-triple x))
          (lsb-emin (+ size.emin (- size.frac-size)))
          (denormalize-amt (- lsb-emin x.exp))
          ((fp-arith-triple x-dnrm) (fp-arith-rightshift x denormalize-amt)))
       (implies (and (<= (1+ size.frac-size) denormalize-amt)
                     (equal (integer-length x.man) (1+ size.frac-size)))
                (equal x-dnrm.man 0)))
     :hints (("goal" :in-theory (e/d (fp-arith-rightshift) ())))))

  (defret integer-length-of-<fn>.man-when-large-denormalize-amt
    (b* (((fp-size size))
         ((fp-arith-triple new-x))
         ((fp-arith-triple x))
         (lsb-emin (+ size.emin (- size.frac-size)))
         (denormalize-amt (- lsb-emin x.exp)))
      (implies (and (<= (1+ size.frac-size) denormalize-amt)
                    (equal (integer-length x.man) (1+ size.frac-size)))
               (< (integer-length new-x.man)
                  (integer-length x.man))))
    :hints (("goal"
             :use ((:instance mantissa-is-zero-when-denormalize-amt->-1+frac-size))
             :in-theory (e/d () (mantissa-is-zero-when-denormalize-amt->-1+frac-size))))
    :rule-classes :linear)

  (local
   (defthm fp-arith-rightshift-man-integer-length-upper-bound
     (implies (and (posp n) (posp (integer-length (fp-arith-triple->man x))))
              (< (integer-length (fp-arith-triple->man (fp-arith-rightshift x n)))
                 (integer-length (fp-arith-triple->man x))))
     :hints (("goal" :in-theory (e/d (fp-arith-rightshift nfix) ())))
     :rule-classes :linear))

  (local (include-book "centaur/bitops/integer-length" :dir :system))

  (local
   (defthm integer-length-1+-bounds
     (implies (natp x)
              (and
               (<= (integer-length x) (integer-length (1+ x)))
               (<= (integer-length (1+ x)) (1+ (integer-length x)))))
     :hints (("goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                       bitops::ihsext-inductions)
                                      ())))
     :rule-classes :linear))

  (local
   (defthm integer-length-1+-rightshift-upper-bound
     (implies (and (posp n) (posp (integer-length (fp-arith-triple->man x))))
              (<= (integer-length (+ 1 (fp-arith-triple->man (fp-arith-rightshift x n))))
                  (integer-length (fp-arith-triple->man x))))
     :hints (("goal" :in-theory (e/d ()
                                     (fp-arith-rightshift-man-integer-length-upper-bound
                                      integer-length-of-fp-arith-rightshift.man))
              :use ((:instance fp-arith-rightshift-man-integer-length-upper-bound))))
     :rule-classes :linear))

  (defret integer-length-of-<fn>.man-when-denormalize-amt-<-1+frac-size
    (b* (((fp-size size))
         ((fp-arith-triple new-x))
         ((fp-arith-triple x))
         (lsb-emin (+ size.emin (- size.frac-size))))
      (implies (and
                (< x.exp lsb-emin)
                (equal (integer-length x.man) (1+ size.frac-size)))
               (<= (integer-length new-x.man)
                   (integer-length x.man))))
    :rule-classes :linear)

  ;; TODO: Prove that iff (integer-length new-x.man) ==
  ;; (integer-length x.man), then new-x is the arith-triple version of
  ;; the smallest possible normal number.

  (defret natp-bits-of-<fn>
    (natp bits)
    :rule-classes :type-prescription))



;; BOZO We should get rid of either fp-arith-triple-left-normalize or left-normalize-arith-triple
(Define fp-arith-triple-left-normalize ((x fp-arith-triple-p)
                                        (width natp))
  :guard (unsigned-byte-p width (fp-arith-triple->man x))
  :prepwork ((local (defthm unsigned-byte-p-in-terms-of-integer-length
                      (equal (unsigned-byte-p n x)
                             (And (natp n)
                                  (natp x)
                                  (<= (integer-length x) n)))
                      :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                                         bitops::ihsext-recursive-redefs))))))
  :returns (new-x fp-arith-triple-p)
  (b* (((fp-arith-triple x))
       (shift (lnfix (- (lnfix width) (integer-length x.man))))
       (new-man
        (bitops::limshift-loghead-of-ash width x.man shift))
       (new-exp (- x.exp shift)))
    (make-fp-arith-triple :sign x.sign
                               :man new-man
                               :exp new-exp))
  ///
  (defret <fn>-correct
    (implies (unsigned-byte-p width (fp-arith-triple->man x))
             (equal (fp-arith-triple->rational new-x)
                    (fp-arith-triple->rational x)))
    :hints(("Goal" :in-theory (enable fp-arith-triple->rational)
            :cases ((equal 0 (fp-arith-triple->man x))))
           (and stable-under-simplificationp
                '(:in-theory (enable bitops::ash-is-expt-*-x)))))

  (defret <fn>-normalized
    (implies (and (unsigned-byte-p width (fp-arith-triple->man x))
                  (not (equal (fp-arith-triple->man x) 0)))
             (equal (integer-length (fp-arith-triple->man new-x))
                    width)))

  (defret <fn>-sign
    (equal (fp-arith-triple->sign new-x)
           (fp-arith-triple->sign x))))



;; BOZO We should get rid of either fp-arith-triple-left-normalize or left-normalize-arith-triple
(define left-normalize-arith-triple ((x fp-arith-triple-p)
                                     (frac-size posp))
  :returns (new-x fp-arith-triple-p)
  (b* (((fp-arith-triple x))
       ((when (eql x.man 0))
        (change-fp-arith-triple x :exp 0))
       (man-len (integer-length x.man))
       (shiftcnt (- (+ 1 (pos-fix frac-size)) man-len)))
    (fp-arith-leftshift x (nfix shiftcnt)))
  ///
  (defthmd normalize-arith-triple-is-left-normalize
    (b* (((mv norm & &) (normalize-arith-triple x))
         ((fp-arith-triple x))
         ((fp-size size)))
      (implies (<= (integer-length x.man) (+ 1 size.frac-size))
               (equal norm (left-normalize-arith-triple x size.frac-size))))
    :hints(("Goal" :in-theory (enable normalize-arith-triple))
           (and stable-under-simplificationp
                '(:in-theory (enable fp-arith-leftshift)))))

  (defret fp-arith-triple->rational-of-<fn>
    (equal (fp-arith-triple->rational new-x)
           (fp-arith-triple->rational x))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable fp-arith-triple->rational)))))

  (defret man-when-0
    (b* (((fp-arith-triple x))
         ((fp-arith-triple new-x)))
      (implies (equal x.man 0)
               (equal new-x.man 0)))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift
                                      bitops::ash-is-expt-*-x))))

  (defret man-equals-0
    (b* (((fp-arith-triple x))
         ((fp-arith-triple new-x)))
      (iff (equal new-x.man 0)
           (equal x.man 0)))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift
                                      bitops::ash-is-expt-*-x))))

  (local (defthm integer-length-bounded-by-width
           (implies (unsigned-byte-p n x)
                    (<= (integer-length x) n))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))
           :rule-classes :linear))
  
  (defret man-length-of-<fn>
    (b* (((fp-arith-triple x))
         ((fp-arith-triple new-x)))
      (implies (and (not (equal x.man 0))
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) x.man))
               (equal (integer-length new-x.man) (+ 1 (pos-fix frac-size)))))
    :hints(("Goal" :in-theory (enable fp-arith-leftshift))))

  (local (defthmd unsigned-byte-p-of-integer-length
           (implies (natp x)
                    (unsigned-byte-p (integer-length x) x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (defret unsigned-byte-p-of-<fn>
    (b* (((fp-arith-triple x))
         ((fp-arith-triple new-x)))
      (implies (and (integerp size)
                    (<= (+ 1 (pos-fix frac-size)) size)
                    (unsigned-byte-p (+ 1 (pos-fix frac-size)) x.man))
               (unsigned-byte-p size new-x.man)))
    :hints (("goal" :use ((:instance unsigned-byte-p-of-integer-length
                           (x (fp-arith-triple->man new-x))))))
    :hints-sub-returnnames t))
