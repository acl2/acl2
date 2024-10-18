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
;================================================================================================
; Original Author(s): Shilpi Goel <shilpi.goel@intel.com>

(in-package "IFP")
(include-book "fp-common")

;; (include-book "centaur/bitops/limited-shifts" :dir :system)

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable unsigned-byte-p
                           logmask
                           (tau-system))))

(local (std::add-default-post-define-hook :fix))
;; ----------------------------------------------------------------------


;; ----------------------------------------------------------------------

(fty::defbitstruct trap-handling-config
  :parents (fp-common)
  :short "Config for trap-handling-core.  Includes typical control
fields such as masks and RC, but also configuration bits such as disabling
denormalization or over/undervalue exponent results."
  ((masks fp-flags :subfields (ie de ze oe ue pe)
          "Exception masks")
   (rc fp-rc "Rounding control")
   (ftz bitp "Flush to zero")
   (unmasked-rescale
    bitp
    "return a normalized value with over/undervalue exponent on unmasked over/underflow.")))


(define fp-arith-triple-overflow-rescale ((x fp-arith-triple-p)
                                          &key
                                          ((size fp-size-p) 'size))
  :short "Convert a normalized @('fp-arith-triple') (a @('WPR') or @('DRPR'))
with an above-range exponent to @('fp-value') with converted overvalue
exponent."
  :long "<p>The overvalue exponent is biased by -3*2^13 and if the resulting
exponent still can't be represented, an infinity is produced instead.</p>"
  :returns (mv (value fp-value-p)
               (re-overflowed booleanp))
  :guard (b* (((fp-arith-triple x))
              ((fp-size size))
              (lsb-emax (+ size.emax (- size.frac-size))))
           (and
            (< lsb-emax x.exp)
            (eql (integer-length x.man) (1+ size.frac-size))))
  (b* (((fp-size size))
       ((fp-arith-triple x))
       (lsb-exp-bias (+ size.frac-size size.exp-bias))
       (overflow-scale-bias (* -3 (ash 1 (- size.exp-size 2))))
       (exp1 (+ x.exp lsb-exp-bias overflow-scale-bias))
       ((when (<= (logmask size.exp-size) exp1))
        (mv (fp-value-inf x.sign) t)))
    (mv (make-fp-value :sign x.sign
                       :exp exp1
                       :frac (loghead size.frac-size x.man)
                       :jbit (logbit size.frac-size x.man))
        nil))

  ///
  (defret value-natp-of-<fn>
    (natp value)
    :rule-classes :type-prescription))

(define result-overflow? ((x fp-arith-triple-p)
                          (result-inexactp booleanp)
                          (config trap-handling-config-p)
                          &key
                          ((size fp-size-p) 'size))
  :returns (mv (overflowp booleanp :rule-classes :type-prescription)
               (value fp-value-p)
               (flags fp-flags-p)
               (bits fp-postproc-bits-p))
  :guard (b* (((fp-arith-triple x))
              ((fp-size size)))
           (eql (integer-length x.man) (1+ size.frac-size)))

  (b* (((fp-size size))
       ((fp-arith-triple x))
       ((trap-handling-config config))
       ((fp-flags masks) config.masks)
       (lsb-emax (+ size.emax (- size.frac-size)))

       ((unless (< lsb-emax x.exp))
        ;; No overflow.
        (mv nil 0 (make-fp-flags) 0))

       ((unless (and (eql masks.oe 0) (eql config.unmasked-rescale 1)))
        ;; Masked overflow
        (b* ((pe (or (eql masks.oe 1) result-inexactp))
             (flags (make-fp-flags :oe 1 :pe (bool->bit pe)))
             (round-up
              (case (rc->rounding-mode config.rc)
                (:rne t)
                (:rmi (eql x.sign 1))
                (:ri  (eql x.sign 0))
                (t ;; rtz
                 nil))))
          (mv t
              (if round-up
                  (fp-value-inf x.sign)
                (fp-value-norm-max x.sign))
              flags
              (make-fp-postproc-bits :overflow t :overflow-round-up round-up))))

       ((mv value ?too-bigp)
        (fp-arith-triple-overflow-rescale x))
       (pe (or result-inexactp too-bigp))
       (flags (make-fp-flags :oe 1 :pe (bool->bit pe)))
       (bits (make-fp-postproc-bits :overflow t :overflow-round-up too-bigp
                                    :overflow-extreme too-bigp)))
    (mv t
        value
        flags
        bits))
  ///
  (defret type-of-<fn>.value
    (natp value)
    :rule-classes :type-prescription)

  (defret type-of-<fn>.flags
    (natp flags)
    :rule-classes :type-prescription)

  (defretd <fn>-overflowp-spec
    (equal overflowp
           (< (- (fp-size->emax) (fp-size->frac-size size))
              (fp-arith-triple->exp x))))

  (defret type-of-<fn>.bits
    (natp bits)
    :rule-classes :type-prescription))


(define result-normal? ((x fp-arith-triple-p)
                        (result-inexactp booleanp)
                        &key
                        ((size fp-size-p) 'size))

  :guard (b* (((fp-size size))
              ((fp-arith-triple x)))
           (and (equal (integer-length x.man) (1+ size.frac-size))
                ;; not overflow
                (<= x.exp (- size.emax size.frac-size))))

  :returns (mv (normalp booleanp :rule-classes :type-prescription)
               (value fp-value-p)
               (flags fp-flags-p))

  (b* (((fp-size size))
       ((fp-arith-triple x))
       (lsb-emax (+ size.emax (- size.frac-size)))
       (lsb-emin (+ size.emin (- size.frac-size)))

       (normalp
        (and (mbt (<= x.exp lsb-emax))
             (<= lsb-emin x.exp)))

       ((unless normalp)
        (mv nil 0 (make-fp-flags)))

       (flags (make-fp-flags :pe (bool->bit result-inexactp) :oe 0 :ue 0)))

      (mv t (fp-arith-triple-to-value x) flags))
  ///
  (defret type-of-<fn>.value
    (natp value)
    :rule-classes :type-prescription)

  (defret type-of-<fn>.flags
    (natp flags)
    :rule-classes :type-prescription)

  (defretd <fn>-normalp-spec
    (implies (<= (fp-arith-triple->exp x)
                 (- (fp-size->emax) (fp-size->frac-size size)))
             (equal normalp
                    (<= (- (fp-size->emin) (fp-size->frac-size size))
                        (fp-arith-triple->exp x))))))

(define fp-arith-triple-to-underflow-value ((x fp-arith-triple-p)
                                            &key
                                            ((size fp-size-p) 'size))
  :short "Convert a normalized @('fp-arith-triple') (a @('WPR') or @('DRPR'))
with a below-range exponent to @('fp-value') with converted undervalue
exponent."
  :returns (mv (value fp-value-p)
               (zeroedp booleanp))
  :guard (b* (((fp-arith-triple x))
              ((fp-size size))
              (lsb-emin (+ size.emin (- size.frac-size))))
           (and
            (< x.exp lsb-emin)
            (eql (integer-length x.man) (1+ size.frac-size))))
  (b* (((fp-size size))
       ((fp-arith-triple x))
       (lsb-exp-bias (+ size.frac-size size.exp-bias))
       (lsb-emin (+ size.emin (- size.frac-size)))
       (exp1 (+ x.exp lsb-exp-bias
                (ash 1 (1- size.exp-size))))
       ((when (<= exp1 0))
        (mv (fp-value-zero x.sign) t))
       (exp2 (if (eql x.exp (- lsb-emin 1))
                 (- exp1 (ash 1 (1- size.exp-size)))
               exp1)))
    (mv (make-fp-value :sign x.sign
                       :exp exp2
                       :frac (loghead size.frac-size x.man)
                       :jbit (logbit size.frac-size x.man))
        nil))
  
  ///
  (defret value-natp-of-<fn>
    (natp value)
    :rule-classes :type-prescription))


(define fp-arith-triple-underflow-rescale ((x fp-arith-triple-p)
                                          &key
                                          ((size fp-size-p) 'size))
  :short "Convert a normalized @('fp-arith-triple') (a @('WPR') or @('DRPR'))
with a below-range exponent to @('fp-value') with converted undervalue
exponent."
  :returns (mv (value fp-value-p)
               (re-underflowed booleanp))
  :guard (b* (((fp-arith-triple x))
              ((fp-size size))
              (lsb-emin (+ size.emin (- size.frac-size))))
           (and
            (< x.exp lsb-emin)
            (eql (integer-length x.man) (1+ size.frac-size))))
  (b* (((fp-size size))
       ((fp-arith-triple x))
       (lsb-exp-bias (+ size.frac-size size.exp-bias))
       (underflow-scale-bias (* 3 (ash 1 (- size.exp-size 2))))
       (exp1 (+ x.exp lsb-exp-bias
                underflow-scale-bias))
       ((when (<= exp1 0))
        (mv (fp-value-zero x.sign) t)))
    (mv (make-fp-value :sign x.sign
                       :exp exp1
                       :frac (loghead size.frac-size x.man)
                       :jbit (logbit size.frac-size x.man))
        nil))
  
  ///
  (defret value-natp-of-<fn>
    (natp value)
    :rule-classes :type-prescription))


(define result-underflow? ((x fp-arith-triple-p "@('RPR')")
                           (x-rounded fp-arith-triple-p "@('WPR')")
                           (result-inexactp booleanp "Based on @('RPR')")
                           (config trap-handling-config-p)
                           &key
                           ((size fp-size-p) 'size)
                           (verbosep 'verbosep))

  :guard (and (b* (((fp-size size))
                   ((fp-arith-triple x)))
                (and (equal (integer-length x.man) (1+ size.frac-size))
                     (< x.exp (- size.emin size.frac-size))))
              (b* (((fp-size size))
                   ((fp-arith-triple x) x-rounded))
                (and (equal (integer-length x.man) (1+ size.frac-size))
                     (< x.exp (- size.emin size.frac-size)))))

  :returns (mv (underflowp booleanp :rule-classes :type-prescription)
               (value fp-value-p)
               (flags fp-flags-p)
               (bits fp-postproc-bits-p))

  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable fp-size->emin
                                          fp-size->emax
                                          fp-size->exp-bias))))

  :prepwork
  ((local
    (defthm emin-<-emax
      ;; (implies (not (equal (fp-size->exp-bias) 0))
      (<= (fp-size->emin) (fp-size->emax))
      :hints (("goal" :in-theory (e/d (fp-size->emin
                                       fp-size->emax)
                                      ())))
      :rule-classes :linear))
   (local (defthm shift-one-gte-2
            (implies (<= 1 (ifix n))
                     (<= 2 (ash 1 n)))
            :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                               bitops::ihsext-recursive-redefs)))
            :rule-classes :linear)))


  (b* (((fp-size size))
       ((fp-arith-triple x))
       ((trap-handling-config config))
       (lsb-emin (+ size.emin (- size.frac-size)))

       ((unless (mbt (< x.exp lsb-emin)))
        ;; No underflow.
        (mv nil 0 (make-fp-flags) (make-fp-postproc-bits)))


       ;; If UE is unmasked, we're going to produce take a UE trap and produce
       ;; the following flags.  We could exit here (the FPCOE Reference Sheet
       ;; says to do that) but prefer to compute the result as if the exception
       ;; was masked.  We just need to make sure and use the right flags at the
       ;; end.
       (ue-trap (not (eql (fp-flags->ue config.masks) 1)))
       (ue-trap-flags (make-fp-flags :ue 1 :pe (bool->bit result-inexactp) :oe 0))
       (ue-trap-bits (!fp-postproc-bits->underflow t 0))

       ((when (eql config.ftz 1))
        (let ((flags (if ue-trap ue-trap-flags (make-fp-flags :ue 1 :pe 1 :oe 0))))
          (mv t (fp-value-zero x.sign) flags ue-trap-bits)))

       ((when (and ue-trap (eql config.unmasked-rescale 1)))
        ;; This is x87 behavior when unmasked -- rescale the exponent
        (b* (((mv underflow-val zeroedp)
              (fp-arith-triple-underflow-rescale x-rounded)))
          (mv t
              underflow-val
              ;; CHECK -- should PE be set when zeroed here?
              (make-fp-flags :ue 1 :pe (b-ior (bool->bit result-inexactp)
                                              (bool->bit zeroedp)))
              (!fp-postproc-bits->underflow-extreme zeroedp ue-trap-bits))))

             ;; Denormalize RPR:
       ((mv x-rnd (fp-postproc-bits denorm-bits))
        (denormalize-and-round-arith-triple x config.rc result-inexactp :verbosep verbosep))
       (x-rnd-inexactp (or denorm-bits.denorm-roundp denorm-bits.denorm-stickyp))
       (bits (logior ue-trap-bits denorm-bits))
       (flags (if ue-trap
                  ue-trap-flags
                (if x-rnd-inexactp
                    (make-fp-flags :ue 1 :pe 1)
                  (make-fp-flags)))))
    (mv t (fp-arith-triple-to-value x-rnd) flags bits))
  ///
  (defret type-of-<fn>.value
    (natp value)
    :rule-classes :type-prescription)

  (defret type-of-<fn>.flags
    (natp flags)
    :rule-classes :type-prescription)

  (defret type-of-<fn>.bits
    (natp bits)
    :rule-classes :type-prescription)

  (defretd <fn>-underflowp-spec
    (implies (< (fp-arith-triple->exp x)
                (- (fp-size->emin) (fp-size->frac-size size)))
    (equal underflowp t)))
           ;; (< (fp-arith-triple->exp x)
           ;;    (- (fp-size->emin) (fp-size->frac-size size)))
           )



(define trap-handling-core ((x fp-arith-triple-p "Normalized arith-triple (@('RPR')); see @(tsee normalize-arith-triple)")
                            (roundp booleanp "@('RPR.R')")
                            (stickyp booleanp "@('RPR.S')")
                            (config trap-handling-config-p)
                            &key
                            ((size fp-size-p) 'size)
                            (verbosep 'verbosep))

  ;; Only deals with the following post-compute exceptions: PE, OE, UE
  ;; When unmasked exception occurs, the caller of this function
  ;; should make sure that the destination is unmodified.
  :returns (mv (new-x fp-value-p)
               (flags fp-flags-p)
               (bits  fp-postproc-bits-p))
  :guard (b* (((fp-size size))
              ((fp-arith-triple x)))
           (equal (integer-length x.man) (1+ size.frac-size)))
  ;; :verify-guards nil
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable result-overflow?-overflowp-spec
                                          result-normal?-normalp-spec)))
                (and stable-under-simplificationp
                     '(:in-theory (enable round-arith-triple-exp-casesplit
                                          result-underflow?-underflowp-spec))))
  :prepwork ((local
              (defretd round-arith-triple-exp-casesplit
                (b* (((fp-arith-triple new-x))
                     ((fp-arith-triple x))
                     ((fp-size size)))
                  (implies (and (equal (integer-length x.man) (+ 1 size.frac-size))
                                (case-split (not (equal new-x.exp x.exp))))
                           (equal new-x.exp (+ 1 x.exp))))
              :hints (("goal" :use round-arith-triple.exp-possibilities))
              :fn round-arith-triple)))
  (b* (((fp-size size))
       ((fp-arith-triple x))
       ((fp-flags masks))

       ((mv (fp-arith-triple x-rounded) round-up exp-bumped)
        (round-arith-triple x roundp stickyp (trap-handling-config->rc config) :verbosep verbosep))

       (norm-bits (make-fp-postproc-bits
                   :norm-lsb (logbitp 0 x.man)
                   :norm-roundp roundp
                   :norm-stickyp stickyp
                   :norm-round-up round-up
                   :norm-exp-bumped exp-bumped))

       (result-inexactp (or roundp stickyp))

       ((mv overflowp result flags overflow-bits)
        (result-overflow? x-rounded result-inexactp config))
       ((when overflowp) (mv result flags
                             (logior norm-bits overflow-bits)))

       ((mv normalp result flags)
        (result-normal? x-rounded result-inexactp))
       ((when normalp) (mv result flags norm-bits))
       ((mv ?underflowp result flags uflow-bits)
        (result-underflow? x x-rounded result-inexactp config :verbosep verbosep))
       ((when (mbt underflowp))
        (mv result flags (logior norm-bits uflow-bits))))
    (prog2$
     (raise "Unreachable code!")
     (mv 0 0 0)))
  ///

  (defret type-of-<fn>.new-x
    (natp new-x)
    :rule-classes :type-prescription)

  (defret type-of-<fn>.flags
    (natp flags)
    :rule-classes :type-prescription)

  (defret type-of-<fn>.bits
    (natp flags)
    :rule-classes :type-prescription))


