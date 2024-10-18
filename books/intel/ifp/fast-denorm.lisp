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
(include-book "postproc")

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable unsigned-byte-p
                           logmask
                           (tau-system))))
(local (std::add-default-post-define-hook :fix))


;; Here we define an alternative function that provably has the same behavior
;; as normalize-arith-triple followed by trap-handling.  The difference is in
;; the denormalization case, the result mantissa is shifted only once to
;; denormalize, rather than once to normalize and then again to denormalize.

(define denormalize-and-round-arith-triple-unnormalized ((x fp-arith-triple-p)
                                                         (rc fp-rc-p)
                                                         (sticky-in booleanp)
                                                         &key
                                                         ((size fp-size-p) 'size))
  :returns (mv (new-x fp-arith-triple-p)
               (bits fp-postproc-bits-p))
  :guard (b* (((fp-arith-triple x))
              ((fp-size size))
              (norm-exp (+ x.exp (- (integer-length x.man) (+ 1 size.frac-size))))
              (lsb-emin (+ size.emin (- size.frac-size))))
           (<= norm-exp lsb-emin))
  ;; :guard-debug t
  (b* (((fp-size size))
       ((fp-arith-triple x))
       (lsb-emin (+ size.emin (- size.frac-size)))
       ;; (mant-len (integer-length x.man))
       ;; (norm-shift (- mant-len (+ 1 size.frac-size))) ;; right shift amount
       ;; (norm-exp (+ x.exp norm-shift))
       ;; (denorm-shift (- lsb-emin norm-exp)) ;; right shift amount
       ;; (full-shift (+ norm-shift denorm-shift))
       ;; (full-shift (+ norm-shift (- lsb-emin norm-exp)))
       ;; (full-shift (+ norm-shift (+ lsb-emin (- x.exp) (- norm-shift))))
       (full-shift (+ lsb-emin (- x.exp)))
       (round-idx (+ (1- lsb-emin) (- x.exp)))
       ((fp-arith-triple x-denorm)
        (if (<= 0 full-shift)
            (fp-arith-rightshift-opt (+ 1 size.frac-size) x full-shift)
          (fp-arith-leftshift-opt (+ 1 size.frac-size) x (- full-shift))
          ))
       ((mv roundp stickyp)
        (if (<= 0 round-idx)
            (mv (logbitp round-idx x.man)
                (or sticky-in
                    (not (eql (loghead round-idx x.man) 0))))
          (mv nil sticky-in)))
       (lsb (logbitp 0 x-denorm.man))
       (round-up? (round-up x.sign lsb roundp stickyp rc))
       (x-rnd (change-fp-arith-triple x-denorm :man (+ (bool->bit round-up?) x-denorm.man))))
    (mv x-rnd
        (make-fp-postproc-bits
         :denorm-lsb lsb
         :denorm-roundp roundp
         :denorm-stickyp stickyp
         :denorm-round-up round-up?
         :denorm-to-normal (eql (fp-arith-triple->man x-rnd)
                                (ash 1 size.frac-size)))))
  ///
  (local (defthm exp-of-fp-rightshift
           (equal (fp-arith-triple->exp (fp-arith-rightshift x n))
                  (+ (fp-arith-triple->exp x) (nfix n)))
           :hints(("Goal" :in-theory (enable fp-arith-rightshift)))))

  (local (defthm exp-of-fp-leftshift
           (equal (fp-arith-triple->exp (fp-arith-leftshift x n))
                  (- (fp-arith-triple->exp x) (nfix n)))
           :hints(("Goal" :in-theory (enable fp-arith-leftshift)))))

  (local (defthm fp-arith-rightshift-of-leftshift
           (equal (fp-arith-rightshift
                   (fp-arith-leftshift x m) n)
                  (if (<= (nfix m) (nfix n))
                      (fp-arith-rightshift x (- (nfix n) (nfix m)))
                    (fp-arith-leftshift x (- (nfix m) (nfix n)))))
           :hints(("Goal" :in-theory (enable fp-arith-leftshift
                                             fp-arith-rightshift)))))


  (local (defthm equal-0-loghead-of-left-shift
           (implies (natp m)
                    (equal (equal 0 (loghead n (ash x m)))
                           (if (<= (nfix n) m)
                               t
                             (equal 0 (loghead (- (nfix n) m) x)))))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))))

  (local (defthm loghead-of-logtail-equal-0
           (implies (and (equal n (+ (nfix a) (nfix b)))
                         (equal (loghead n x) 0))
                    (equal (equal (loghead a (logtail b x)) 0)
                           t))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm loghead-of-less-equal-0
           (implies (and (equal (loghead n x) 0)
                         (< (nfix m) (nfix n)))
                    (equal (equal (loghead m x) 0)
                           t))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm loghead-of-logtail-not-equal-0
           (implies (and (equal n (+ (nfix a) (nfix b)))
                         (not (equal (loghead n x) 0))
                         (equal (loghead b x) 0))
                    (not (equal (loghead a (logtail b x)) 0)))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))))

  (local (defthmd loghead-0-when-loghead-minus-1-0
           (implies (and (posp n)
                         (equal (loghead (+ -1 n) x) 0)
                         (not (logbitp (+ -1 n) x)))
                    (equal (equal (loghead n x) 0)
                           t))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))
           :rule-classes ((:rewrite :backchain-limit-lst (nil 1 1)))))
  
  (local (defthm loghead-of-logtail-not-equal-0-logbitp
           (implies (and (equal n (+ (nfix a) (nfix b)))
                         (not (equal (loghead n x) 0))
                         (equal (loghead (+ -1 b) x) 0)
                         (not (logbitp (+ -1 b) x))
                         (posp b))
                    (not (equal (loghead a (logtail b x)) 0)))
           :hints(("Goal" :in-theory (e/d (loghead-0-when-loghead-minus-1-0)
                                          (loghead-of-logtail-not-equal-0))
                   :use loghead-of-logtail-not-equal-0))))

  (local (defthm left-shift-equal-0
           (implies (natp n)
                    (equal (equal 0 (ash x n))
                           (equal 0 (ifix x))))
           :hints (("goal" :in-theory (disable acl2::ifix-equal-to-0))
                   (bitops::logbitp-reasoning :prune-examples nil))))

  (local (defthm unsigned-byte-p-integer-length
           (implies (and (<= (integer-length x) n)
                         (natp x)
                         (natp n))
                    (unsigned-byte-p n x))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm equal-0-of-logtail-norm
           (implies (< (nfix n) (integer-length x))
                    (iff (equal 0 (logtail n x))
                         (equal 0 (ifix x))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))))

  (local (defthm logbitp-when-loghead-0
           (implies (and (equal (loghead n x) 0)
                         (< (nfix m) (nfix n)))
                    (not (logbitp m x)))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))))
           

  
  ;; (local (defthm <-when-<
  ;;          (implies (< x y)
  ;;                   (< x y))))

  ;; (local (defthm not-<-when-<
  ;;          (implies (not (< x y))
  ;;                   (not (< x y)))))
  
  (defret <fn>-correct
    (b* (((mv (fp-arith-triple x-norm) roundp-norm stickyp-norm) (normalize-arith-triple x :sticky-in sticky-in
                                                                                         :verbosep nil))
         ((fp-arith-triple x))
         ((fp-size size))
         ((mv new-x-spec bits-spec)
          (denormalize-and-round-arith-triple x-norm rc
                                              (or roundp-norm stickyp-norm)
                                              :verbosep nil)))
      (implies (and ;; (not (equal x.man 0))
                    ;; (booleanp sticky-in)
                    (< x-norm.exp (- size.emin size.frac-size)))
               (and (equal new-x new-x-spec)
                    (equal bits bits-spec))))
    :hints(("Goal" :in-theory (enable normalize-arith-triple
                                      denormalize-and-round-arith-triple
                                      bool->bit
                                      fgl::binary-minus
                                      fp-arith-leftshift-opt-is-fp-arith-leftshift
                                      fp-arith-rightshift-opt-is-fp-arith-rightshift))
           (and stable-under-simplificationp
                '(:in-theory (enable fp-arith-leftshift
                                     fp-arith-rightshift
                                     bitops::logbitp-of-ash-split
                                     bitops::loghead-of-loghead-split)))
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable <-when-< not-<-when-<)))
           ))

  (defret bits-type-of-<fn>
    (natp bits)
    :rule-classes :type-prescription))
         



(define result-underflow?-fast-denorm ((x-norm fp-arith-triple-p "@('RPR')")
                                       (x-rounded fp-arith-triple-p "@('WPR')")
                                       (x-orig fp-arith-triple-p)
                                       (result-inexactp booleanp "Based on @('RPR')")
                                       (orig-sticky-in booleanp)
                                       (config trap-handling-config-p)
                                       &key
                                       ((size fp-size-p) 'size))
  

  :guard (and (b* (((fp-size size))
                   ((fp-arith-triple x) x-norm)
                   (verbosep nil)
                   ((mv x-norm-spec roundp stickyp)
                    (normalize-arith-triple x-orig :sticky-in orig-sticky-in)))
                (and (equal (integer-length x.man) (1+ size.frac-size))
                     (< x.exp (- size.emin size.frac-size))
                     (equal x-norm x-norm-spec)
                     (equal result-inexactp (or roundp stickyp))))
              (b* (((fp-size size))
                   ((fp-arith-triple x) x-rounded))
                (and (equal (integer-length x.man) (1+ size.frac-size))
                     (< x.exp (- size.emin size.frac-size))))
              ;; (b* (((fp-size size))
              ;;      ((fp-arith-triple x) x-orig)
              ;;      (norm-exp (+ x.exp (- (integer-length x.man) (+ 1 size.frac-size))))
              ;;      (lsb-emin (+ size.emin (- size.frac-size))))
              ;;   (<= norm-exp lsb-emin))
              )

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
       ((fp-arith-triple x-norm))
       ((trap-handling-config config))
       (lsb-emin (+ size.emin (- size.frac-size)))

       ((unless (mbt (< x-norm.exp lsb-emin)))
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
          (mv t (fp-value-zero x-norm.sign) flags ue-trap-bits)))

       ((when (and ue-trap (eql config.unmasked-rescale 1)))
        ;; rescale the exponent
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
        (denormalize-and-round-arith-triple-unnormalized x-orig config.rc orig-sticky-in))
       (x-rnd-inexactp (or denorm-bits.denorm-roundp denorm-bits.denorm-stickyp))
       (bits (logior ue-trap-bits denorm-bits))
       (flags (if ue-trap
                  ue-trap-flags
                (if x-rnd-inexactp
                    (make-fp-flags :ue 1 :pe 1)
                  (make-fp-flags)))))
    (mv t (fp-arith-triple-to-value x-rnd) flags bits))
  ///


  
  (defret result-underflow?-fast-denorm-correct
    :pre-bind (((mv (fp-arith-triple x-norm) roundp-norm stickyp-norm) (normalize-arith-triple x-orig :sticky-in orig-sticky-in :verbosep nil)))
    (b* (((fp-arith-triple x-orig))
         ((fp-size size))
         ((mv underflowp-spec value-spec flags-spec bits-spec)
          (result-underflow? x-norm x-rounded (or roundp-norm stickyp-norm) config
                             :verbosep nil)))
      (implies (and ;; (not (equal x-orig.man 0))
                    (iff result-inexactp (or roundp-norm stickyp-norm))
                    (< x-norm.exp (- size.emin size.frac-size)))
               (and (equal underflowp underflowp-spec)
                    (equal value value-spec)
                    (equal flags flags-spec)
                    (equal bits bits-spec))))
    :hints(("Goal" :in-theory (enable result-underflow?))))

  (defret flags-type-of-<fn>
    (natp flags)
    :rule-classes :type-prescription)

  (defret bits-type-of-<fn>
    (natp bits)
    :rule-classes :type-prescription))



(define trap-handling-core-fast-denorm ((x-norm fp-arith-triple-p)
                                        (x-orig fp-arith-triple-p)
                                        (roundp booleanp)
                                        (stickyp booleanp)
                                        (orig-sticky-in booleanp)
                                        (config trap-handling-config-p)
                                        &key
                                        ((size fp-size-p) 'size))
  :returns (mv (new-x fp-value-p)
               (flags fp-flags-p)
               (bits  fp-postproc-bits-p))
  :guard (b* (((fp-size size))
              ((mv x-norm-spec roundp-spec stickyp-spec)
               (normalize-arith-triple x-orig :sticky-in orig-sticky-in :verbosep nil)))
           (and ;; (equal (integer-length x.man) (1+ size.frac-size))
            (not (equal (fp-arith-triple->man x-orig) 0))
            (equal x-norm x-norm-spec)
            (equal roundp roundp-spec)
            (equal stickyp stickyp-spec)))
  ;; :verify-guards nil
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (e/d (round-arith-triple-exp-casesplit)
                                       (NORMALIZE-ARITH-TRIPLE.EXP-VALUE))))
                (and stable-under-simplificationp
                     '(:in-theory (enable normalize-arith-triple.exp-value))))
  :prepwork ((local (defret result-underflow?-underflowp-iff
                      (iff underflowp
                           (< (fp-arith-triple->exp x)
                              (- (fp-size->emin) (fp-size->frac-size size))))
                      :fn result-underflow?
                      :hints(("Goal" :in-theory (enable result-underflow?)))))

             (local (defret result-normal?-normalp-iff
                      (iff normalp
                           (and (>= (fp-arith-triple->exp x)
                                    (- (fp-size->emin) (fp-size->frac-size size)))
                                (<= (fp-arith-triple->exp x)
                                    (- (fp-size->emax) (fp-size->frac-size size)))))
                      :fn result-normal?
                      :hints(("Goal" :in-theory (enable result-normal?)))))

             (local (defret result-overflow?-overflowp-iff
                      (iff overflowp
                           (> (fp-arith-triple->exp x)
                              (- (fp-size->emax) (fp-size->frac-size size))))
                      :fn result-overflow?
                      :hints(("Goal" :in-theory (enable result-overflow?)))))
             (local
              (defretd round-arith-triple-exp-casesplit
                (b* (((fp-arith-triple new-x))
                     ((fp-arith-triple x))
                     ((fp-size size)))
                  (implies (and (equal (integer-length x.man) (+ 1 size.frac-size))
                                (case-split (not (equal new-x.exp x.exp))))
                           (equal new-x.exp (+ 1 x.exp))))
                :hints (("goal" :use round-arith-triple.exp-possibilities))
                :fn round-arith-triple))
             (local (in-theory (disable round-arith-triple-exp-casesplit))))
  ;; EVerything is the same as trap-handling-core except the underflow case.
  (b* (((fp-size size))
       ((fp-arith-triple x-norm))
       ((fp-flags masks))

       ((mv (fp-arith-triple x-rounded) round-up exp-bumped)
        (round-arith-triple x-norm roundp stickyp (trap-handling-config->rc config) :verbosep nil))

       (norm-bits (make-fp-postproc-bits
                   :norm-lsb (logbitp 0 x-norm.man)
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
        (result-underflow?-fast-denorm x-norm x-rounded x-orig result-inexactp orig-sticky-in config))
       ((when (mbt underflowp))
        (mv result flags (logior norm-bits uflow-bits))))
    (prog2$
     (raise "Unreachable code!")
     (mv 0 0 0)))
  ///
  
  
  (defret <fn>-correct
    :pre-bind (((mv (fp-arith-triple x-norm) roundp stickyp) (normalize-arith-triple x-orig :sticky-in orig-sticky-in :verbosep nil)))
    (b* (((fp-arith-triple x-orig))
         ((fp-size size))
         ((mv value-spec flags-spec bits-spec)
          (trap-handling-core x-norm roundp stickyp config
                              :verbosep nil)))
      (implies (not (equal x-orig.man 0))
               (and (equal new-x value-spec)
                    (equal flags flags-spec)
                    (equal bits bits-spec))))
    :hints(("Goal" :in-theory (enable trap-handling-core
                                      round-arith-triple-exp-casesplit))))

  (defret flags-type-of-<fn>
    (natp flags)
    :rule-classes :type-prescription)

  (defret bits-type-of-<fn>
    (natp bits)
    :rule-classes :type-prescription))

