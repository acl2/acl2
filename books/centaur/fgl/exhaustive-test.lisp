; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2022 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "FGL")


(include-book "pathcond")
(include-book "interp-st-bfrs-ok")
(include-book "satlink-sat") ;; bozo move things around so we don't need this
(include-book "centaur/aignet/vecsim" :dir :system)
(include-book "centaur/aignet/copying" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

(defprod fgl-exhaustive-test-config
  :parents (fgl-solving)
  :short "FGL SAT config object that says to use exhaustive vectorized simulation to check satisfiability."
  ((ignore-pathcond booleanp :default nil)
   (ignore-constraint booleanp :default nil)
   (transform booleanp :default nil)
   (transform-config-override :default nil)
   (random-iters acl2::maybe-natp :default nil
                 "If set, random simulation will be used instead of exhaustive
simulation, and as a result, the SAT check will never return UNSAT. Therefore,
this is useful for testing but not for proof."))
  :tag :fgl-exhaustive-test-config)

(define fgl-exhaustive-test-transforms ((x fgl-exhaustive-test-config-p))
  (b* (((fgl-exhaustive-test-config x))
       ((unless x.transform) nil))
    (or x.transform-config-override
        (fgl-aignet-transforms-config))))

(local (in-theory (disable nth update-nth)))

#!aignet
(define int-to-bitarr ((idx natp)
                       (val integerp)
                       (bitarr))
  :guard (<= idx (bits-length bitarr))
  :measure (nfix (- (bits-length bitarr) (nfix idx)))
  :returns (new-bitarr)
  (b* (((when (mbe :logic (zp (- (bits-length bitarr) (nfix idx)))
                   :exec (eql (bits-length bitarr) idx)))
        (mbe :logic (non-exec (bit-list-fix bitarr))
             :exec bitarr))
       (bitarr (set-bit idx (logbit idx val) bitarr)))
    (int-to-bitarr (1+ (lnfix idx)) val bitarr))
  ///
  (defret nth-of-<fn>
    (bit-equiv (nth n new-bitarr)
               (if (and (<= (nfix idx) (nfix n))
                        (< (nfix n) (len bitarr)))
                   (logbit n val)
                 (nth n bitarr)))
    :hints(("Goal" :in-theory (enable* arith-equiv-forwarding))))
  
  ;; (local (defthm take-of-len-free-nfix
  ;;          (implies (Equal (nfix len) (len x))
  ;;                   (equal (take len x)
  ;;                          (acl2::list-fix x)))))

  (local (defthm my-nth-of-append
           (equal (nth n (append x y))
                  (if (< (nfix n) (len x))
                      (nth n x)
                    (nth (- (nfix n) (len x)) y)))))
  
  (defret <fn>-in-terms-of-int-to-bitlist
    (implies (<= (nfix idx) (len bitarr))
             (bits-equiv new-bitarr
                         (append (take idx (bit-list-fix bitarr))
                                 (int-to-bitlist (- (len bitarr) (nfix idx))
                                                 (logtail idx val)))))
    :hints(("Goal" :in-theory (e/d (bits-equiv
                                    bitops::logbitp-of-loghead-split) (<fn>))))))


(local (in-theory (disable w)))

#!aignet
(define aignet-cube-transform-and-exhaustive-test ((cube lit-listp)
                                                   xform-config
                                                   bitarr
                                                   aignet
                                                   state)
  :guard (aignet-lit-listp cube aignet)
  
  :returns (mv status new-bitarr new-state)
  (b* (((unless (<= (num-ins aignet) 37))
        (mv :failed bitarr state))
       ((acl2::local-stobjs aignet2)
        (mv status bitarr state aignet2))
       (aignet2 (aignet-copy-with-conjoined-output cube aignet aignet2))
       ((mv aignet2 state) (apply-comb-transforms! aignet2 xform-config state))
       ((acl2::hintcontext :sim))
       (ctrex-val (time$ (exhaustive-sim aignet2)))
       ((when ctrex-val)
        (b* ((bitarr (resize-bits (num-ins aignet) bitarr))
             (bitarr (int-to-bitarr 0 ctrex-val bitarr)))
          (mv :sat bitarr state aignet2))))
    (mv :unsat bitarr state aignet2))
  ///
  (set-ignore-ok t)
  
  (defret <fn>-unsat-implies
    (implies (and (equal 1 (aignet-eval-conjunction cube invals regvals aignet))
                  (aignet-lit-listp (lit-list-fix cube) aignet)
                  (equal (num-regs aignet) 0))
             (not (eq status :unsat)))
    :hints (; ("goal" :do-not-induct t)
            (acl2::function-termhint
             aignet-cube-transform-and-exhaustive-test
             (:sim
              `(:use ((:instance exhaustive-sim-correct
                       (aignet ,(acl2::hq aignet2))
                       (invals invals)
                       (regvals regvals))))))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


#!aignet
(define aignet-cube-transform-and-random-test ((cube lit-listp)
                                               xform-config
                                               (nsims natp)
                                               bitarr
                                               aignet
                                               state)
  :guard (aignet-lit-listp cube aignet)
  
  :returns (mv status new-bitarr new-state)
  (b* (((acl2::local-stobjs aignet2)
        (mv status bitarr state aignet2))
       (aignet2 (aignet-copy-with-conjoined-output cube aignet aignet2))
       ((mv aignet2 state) (apply-comb-transforms! aignet2 xform-config state))
       ((mv ctrexp bitarr state)
        (time$ (random-sim nsims bitarr aignet2 state)))
       ((when ctrexp)
        (mv :sat bitarr state aignet2)))
    (mv :failed bitarr state aignet2))
  ///
  (set-ignore-ok t)

  ;; Soundness guarantee is that it never returns :UNSAT. :)
  (defret <fn>-unsat-implies
    (not (eq status :unsat)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define interp-st-exhaustive-test-core ((config fgl-exhaustive-test-config-p)
                                          (bfr interp-st-bfr-p)
                                          (interp-st interp-st-bfrs-ok)
                                          state)
  :guard (bfr-mode-is :aignet (interp-st-bfr-mode))
  :returns (mv status
               new-interp-st
               new-state)
  :ignore-ok t
  :irrelevant-formals-ok t
  ;; :guard-debug t
  :guard-hints (("goal" :in-theory (e/d (interp-st-bfrs-ok) (not))))
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (mv :failed interp-st state))
       ((fgl-exhaustive-test-config config))
       (cube (interp-st-sat-check-cube
              ;; silly...
              (make-fgl-satlink-monolithic-sat-config
               :ignore-pathcond config.ignore-pathcond
               :ignore-constraint config.ignore-constraint)
              bfr interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (env$ (interp-st->ctrex-env interp-st)))
               (ans env$ state)
               (stobj-let ((aignet (logicman->aignet logicman)))
                          (ans env$ state)
                          (stobj-let ((bitarr (env$->bitarr env$)))
                                     (ans bitarr state)
                                     (b* ((transform-config (fgl-exhaustive-test-transforms config))
                                          ((acl2::hintcontext :check)))
                                       (if config.random-iters
                                           (aignet::aignet-cube-transform-and-random-test
                                            cube
                                            transform-config
                                            config.random-iters
                                            bitarr aignet state)
                                         (aignet::aignet-cube-transform-and-exhaustive-test
                                          cube
                                          transform-config
                                          bitarr aignet state)))
                                     (mv ans env$ state))
                          (mv ans env$ state))
               (mv ans interp-st state)))
  ///
  
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-p bfr))
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok))))

  ;; (defret interp-st-bfr-p-of-<fn>
  ;;   (implies (and (interp-st-bfrs-ok interp-st)
  ;;                 (interp-st-bfr-p bfr)
  ;;                 (equal logicman (interp-st->logicman interp-st)))
  ;;            (lbfr-p ans logicman)))

  (defret logicman-equiv-of-<fn>
    (logicman-equiv (interp-st->logicman new-interp-st)
                    (interp-st->logicman interp-st))
    :hints(("Goal" :in-theory (enable logicman-equiv))))

  (set-ignore-ok t)

  (defret <fn>-unsat-implies
    (implies (and (equal status :unsat)
                  (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-p bfr)
                  ;; (not (interp-st->errmsg new-interp-st))
                  (equal logicman (interp-st->logicman interp-st))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st)))
             (not (gobj-bfr-eval bfr env (interp-st->logicman interp-st))))
    :hints ((acl2::function-termhint
             interp-st-exhaustive-test-core
             (:check
              (b* ((invals (alist-to-bitarr (aignet::num-ins aignet)
                                            (fgl-env->bfr-vals env) nil)))
                `(:in-theory (e/d (gobj-bfr-eval bfr-eval)
                                  (aignet::aignet-cube-transform-and-exhaustive-test-unsat-implies))
                  :use ((:instance aignet::aignet-cube-transform-and-exhaustive-test-unsat-implies
                         (cube ,(acl2::hq cube))
                         (xform-config ,(acl2::hq transform-config))
                         (aignet ,(acl2::hq aignet))
                         (bitarr ,(acl2::hq bitarr))
                         (invals ,(acl2::hq invals))
                         (regvals nil))))))))
    )
                                
  
  ;; (defret status-of-<fn>
  ;;   (or (equal status :unsat)
  ;;       (equal status :sat)
  ;;       (equal status :failed))
  ;;   :rule-classes ((:forward-chaining :trigger-terms (status))))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
                  (not (equal (interp-st-field-fix key) :errmsg))
                  (not (equal (interp-st-field-fix key) :debug-info))
                  (not (equal (interp-st-field-fix key) :debug-stack))
                  (not (equal (interp-st-field-fix key) :ctrex-env)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  ;; (defret major-stack-ev-of-<fn>
  ;;   (implies (equal stack (interp-st->stack interp-st))
  ;;            (equal (major-stack-ev stack env (interp-st->logicman new-interp-st))
  ;;                   (major-stack-ev stack env (interp-st->logicman interp-st)))))

  (defret logicman->mode-of-<fn>
    (equal (logicman->mode (interp-st->logicman new-interp-st))
           (logicman->mode (interp-st->logicman interp-st))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars (interp-st->logicman new-interp-st))
           (bfr-nvars (interp-st->logicman interp-st))))

  
  (defret <fn>-return-values-correct
    (equal (list . <values>)
           <call>))

  (defret <fn>-preserves-errmsg
    (let ((errmsg (interp-st->errmsg interp-st)))
      (implies errmsg
               (equal (interp-st->errmsg new-interp-st) errmsg))))

  

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(make-event
 `(define interp-st-exhaustive-test (params
                                     (bfr interp-st-bfr-p)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
    :returns (mv status new-interp-st new-state)
    (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
          ;; Skip the SAT check when not in aignet mode, for now.
          (mv :failed interp-st state))
         ((when (interp-st->errmsg interp-st))
          (mv :failed interp-st state))
         ((unless (fgl-exhaustive-test-config-p params))
          (b* ((interp-st (fgl-interp-store-debug-info
                           "Malformed fgl-sat-check call: params was not resolved to a fgl-sat-config object"
                           nil interp-st)))
            (mv :failed interp-st state)))
         ((when (eq bfr nil))
          (mv :unsat interp-st state)))
      (interp-st-exhaustive-test-core params bfr interp-st state))
    ///
    . ,*interp-st-sat-check-thms*))
  
  

(define logicman-exhaustive-test-counterexample (logicman
                                                 env$)  ;; ctrex-env field
  :returns (mv err new-env$)
  (b* ((bfrstate (logicman->bfrstate)))
    (stobj-let ((aignet (logicman->aignet logicman)))
               (err env$)
               (stobj-let ((bitarr (env$->bitarr env$)))
                          (err bitarr)
                          (bfrstate-case
                            :aignet
                            (b* (((unless (<= (aignet::num-ins aignet) (bits-length bitarr)))
                                  (b* ((bitarr (resize-bits (aignet::num-fanins aignet) bitarr)))
                                    (mv "Error: expected longer bitarr" bitarr)))
                                 ((acl2::local-stobjs aignet::vals)
                                  (mv err bitarr aignet::vals))
                                 (aignet::vals (resize-bits (aignet::num-fanins aignet) aignet::vals))
                                 (aignet::vals (aignet::aignet-invals->vals bitarr aignet::vals aignet))
                                 (aignet::vals (aignet::aignet-eval aignet::vals aignet))
                                 ((mv bitarr aignet::vals) (swap-stobjs bitarr aignet::vals)))
                              (mv nil bitarr aignet::vals))
                            :bdd
                            (b* ((bitarr (resize-bits (bfrstate->bound bfrstate) bitarr)))
                              (mv "Error: expected bfr mode to be :aignet"
                                  bitarr))
                            :aig
                            (mv "Error: expected bfr mode to be :aignet"
                                bitarr))
                          (mv err env$))
               (mv err env$)))
  ///
  (defret bfr-env$-p-of-<fn>
    (bfr-env$-p new-env$ (logicman->bfrstate))
    :hints(("Goal" :in-theory (enable bfr-env$-p))))

  (defret aignet-vals-p-of-<fn>
    (implies (not err)
             (aignet::aignet-vals-p (env$->bitarr new-env$)
                                    (logicman->aignet logicman)))))


(define interp-st-exhaustive-test-counterexample (params
                                                  (interp-st interp-st-bfrs-ok)
                                                  state)
  :returns (mv err new-interp-st)
  (declare (ignore params state))
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (env$ (interp-st->ctrex-env interp-st)))
             (err env$)
             (logicman-exhaustive-test-counterexample logicman env$)
             (mv err interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :ctrex-env))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret bfr-env$-p-of-<fn>
    (implies (not err)
             (bfr-env$-p (interp-st->ctrex-env new-interp-st)
                         (logicman->bfrstate (interp-st->logicman interp-st)))))

  (defret aignet-vals-p-of-<fn>
    (implies (and (not err)
                  (bfr-mode-is :aignet (interp-st-bfr-mode)))
             (aignet::aignet-vals-p
              (env$->bitarr (interp-st->ctrex-env new-interp-st))
              (logicman->aignet (interp-st->logicman interp-st))))))

(defmacro fgl-use-exhaustive-test ()
  '(progn (defattach interp-st-sat-check interp-st-exhaustive-test)
          (defattach interp-st-sat-counterexample interp-st-exhaustive-test-counterexample)))

(fgl-use-exhaustive-test)
