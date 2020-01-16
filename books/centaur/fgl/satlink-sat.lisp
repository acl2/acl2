; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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


(include-book "pathcond")
(include-book "interp-st-bfrs-ok")
(include-book "sat-stub")
(include-book "centaur/aignet/cube-sat" :dir :system)
(local (std::add-default-post-define-hook :fix))
(local (include-book "std/lists/resize-list" :dir :system))

(defprod fgl-satlink-monolithic-sat-config
  ((ignore-pathcond booleanp :default nil)
   (ignore-constraint booleanp :default nil)
   (satlink-config-override :default nil)
   (transform booleanp :default nil)
   (transform-config-override :default nil))
  :tag :fgl-satlink-config)


(define interp-st-sat-check-cube ((config fgl-satlink-monolithic-sat-config-p)
                                  (bfr interp-st-bfr-p)
                                  (interp-st interp-st-bfrs-ok))
  :guard (bfr-mode-is :aignet (interp-st-bfr-mode))
  :returns (cube satlink::lit-listp)
  :ignore-ok t
  :irrelevant-formals-ok t
  ;; :guard-debug t
  :guard-hints (("goal" :in-theory (e/d (interp-st-bfrs-ok) (not))))
  (b* (((fgl-satlink-monolithic-sat-config config)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st)))
               (cube)
               (b* ((cube nil)
                    (cube
                     (if (or** config.ignore-pathcond
                               (not (pathcond-enabledp pathcond)))
                         cube
                       (pathcond-to-cube pathcond cube)))
                    (cube
                     (if (or** config.ignore-constraint
                               (not (pathcond-enabledp constraint-pathcond)))
                         cube
                       (pathcond-to-cube constraint-pathcond cube))))
                 (cons (bfr->aignet-lit bfr (logicman->bfrstate)) cube))
               cube))
  ///
  
  (local (defthm aignet-eval-conjunction-of-cons
           (equal (aignet::aignet-eval-conjunction (cons x y) invals regvals aignet)
                  (b-and (aignet::lit-eval x invals regvals aignet)
                         (aignet::aignet-eval-conjunction y invals regvals aignet)))
           :hints(("Goal" :in-theory (enable aignet::aignet-eval-conjunction)))))

  (local (defthm aignet-eval-conjunction-of-nil
           (equal (aignet::aignet-eval-conjunction nil invals regvals aignet)
                  1)
           :hints(("Goal" :in-theory (enable aignet::aignet-eval-conjunction)))))


  (defret aignet-eval-conjunction-of-<fn>
    (implies (and (equal logicman (interp-st->logicman interp-st))
                  (equal aignet (logicman->aignet logicman))
                  (lbfr-mode-is :aignet)
                  ;; (equal invals (alist-to-bitarr (aignet::num-ins aignet) env nil))
                  (logicman-pathcond-eval env
                                          (interp-st->pathcond interp-st)
                                          logicman)
                  (logicman-pathcond-eval env
                                          (interp-st->constraint interp-st)
                                          logicman))
               (equal (aignet::aignet-eval-conjunction
                       cube
                       (alist-to-bitarr (aignet::stype-count :pi aignet) env nil)
                       ;; invals
                       nil aignet)
                      (bool->bit (bfr-eval bfr env))))
    :hints(("Goal" :in-theory (enable bfr-eval))))

  ;; (local #!aignet
  ;;        (defthm aignet-lit-listp-of-append
  ;;          (implies (and (aignet-lit-listp x aignet)
  ;;                        (aignet-lit-listp y aignet))
  ;;                   (aignet-lit-listp (append x y) aignet))
  ;;          :hints(("Goal" :in-theory (enable aignet-lit-listp)))))

  (local #!aignet
         (defthm aignet-lit-listp-of-rev
           (implies (aignet-lit-listp x aignet)
                    (aignet-lit-listp (acl2::rev x) aignet))
           :hints(("Goal" :in-theory (enable aignet-lit-listp acl2::rev)))))
           

  (defret aignet-lit-listp-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (lbfr-mode-is :aignet (interp-st->logicman interp-st))
                  (interp-st-bfr-p bfr))
             (aignet::aignet-lit-listp cube (logicman->aignet (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable pathcond-to-cube
                                      interp-st-bfrs-ok
                                      logicman-pathcond-p)))))



(encapsulate
  (((fgl-satlink-config) => *
    :formals nil :guard t))
  (local (defun fgl-satlink-config ()
           (declare (xargs :guard t))
           satlink::*default-config*))
  (defthm fgl-satlink-config-constraint
    (satlink::config-p (fgl-satlink-config))))

(defun fgl-default-satlink-config ()
  (declare (xargs :guard t))
  (satlink::change-config satlink::*default-config*
                          :verbose nil))

(defattach fgl-satlink-config fgl-default-satlink-config)

(define fgl-satlink-config-wrapper ((x fgl-satlink-monolithic-sat-config-p))
  :returns (config satlink::config-p)
  (b* ((config-config (fgl-satlink-monolithic-sat-config->satlink-config-override x))
       ((when (and config-config (satlink::config-p config-config)))
        config-config))
    (fgl-satlink-config)))


(encapsulate
  (((fgl-aignet-transforms-config) => *
    :formals nil :guard t))
  (local (defun fgl-aignet-transforms-config ()
           (declare (xargs :guard t))
           nil)))

(defun fgl-default-aignet-transforms-config ()
  (declare (xargs :guard t))
  nil)

(defattach fgl-aignet-transforms-config fgl-default-aignet-transforms-config)

(define fgl-aignet-transforms-config-wrapper ((x fgl-satlink-monolithic-sat-config-p))
  (b* ((config-config (fgl-satlink-monolithic-sat-config->transform-config-override x)))
    (or config-config
        (fgl-aignet-transforms-config))))



(local (in-theory (disable w)))

(define interp-st-satlink-sat-check-core ((config fgl-satlink-monolithic-sat-config-p)
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
       (cube (interp-st-sat-check-cube config bfr interp-st))
       ((fgl-satlink-monolithic-sat-config config)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (env$ (interp-st->ctrex-env interp-st)))
               (ans env$ state)
               (stobj-let ((aignet (logicman->aignet logicman)))
                          (ans env$ state)
                          (stobj-let ((bitarr (env$->bitarr env$)))
                                     (ans bitarr state)
                                     (b* ((satlink-config (fgl-satlink-config-wrapper config))
                                          
                                          ((unless config.transform)
                                           (acl2::hintcontext
                                            :no-xform
                                            (b* (((mv status bitarr)
                                                  (aignet::aignet-sat-check-cube cube satlink-config aignet bitarr)))
                                              (mv status bitarr state))))
                                          (transform-config (fgl-aignet-transforms-config-wrapper config))
                                          ((acl2::hintcontext :xform)))
                                       (aignet::aignet-transform-sat-check-cube
                                        cube satlink-config transform-config aignet bitarr state))
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
             interp-st-satlink-sat-check-core
             (:no-xform
              (b* ((invals (alist-to-bitarr (aignet::num-ins aignet)
                                            (fgl-env->bfr-vals env) nil)))
                `(:in-theory (e/d (gobj-bfr-eval bfr-eval)
                                  (aignet::aignet-sat-check-cube-unsat))
                  :use ((:instance aignet::aignet-sat-check-cube-unsat
                         (cube ,(acl2::hq cube))
                         (config ,(acl2::hq satlink-config))
                         (aignet ,(acl2::hq aignet))
                         (bitarr ,(acl2::hq bitarr))
                         (invals ,(acl2::hq invals))
                         (regvals nil))))))
             (:xform
              (b* ((invals (alist-to-bitarr (aignet::num-ins aignet)
                                            (fgl-env->bfr-vals env) nil)))
                `(:in-theory (e/d (gobj-bfr-eval bfr-eval)
                                  (aignet::aignet-transform-sat-check-cube-unsat))
                  :use ((:instance aignet::aignet-transform-sat-check-cube-unsat
                         (cube ,(acl2::hq cube))
                         (sat-config ,(acl2::hq satlink-config))
                         (xform-config ,(acl2::hq transform-config))
                         (aignet ,(acl2::hq aignet))
                         (bitarr ,(acl2::hq bitarr))
                         (invals ,(acl2::hq invals))
                         (regvals nil)))))))))
                                
  
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
 `(define interp-st-satlink-sat-check-impl (params
                                            (bfr interp-st-bfr-p)
                                            (interp-st interp-st-bfrs-ok)
                                            state)
    :returns (mv status
                 new-interp-st
                 new-state)
    (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
          ;; Skip the SAT check when not in aignet mode, for now.
          (mv :failed interp-st state))
         ((when (interp-st->errmsg interp-st))
          (mv :failed interp-st state))
         ((unless (fgl-satlink-monolithic-sat-config-p params))
          (b* ((interp-st (fgl-interp-store-debug-info
                           "Malformed fgl-sat-check call: params was not resolved to a fgl-sat-config object"
                           nil interp-st)))
            (mv :failed interp-st state)))
         ((when (eq bfr nil))
          (mv :unsat interp-st state)))
      (interp-st-satlink-sat-check-core params bfr interp-st state))
    ///
    . ,*interp-st-sat-check-thms*))



(define logicman-satlink-counterexample (logicman
                                         env$)  ;; ctrex-env field
  :returns (mv err new-env$)
  (b* ((bfrstate (logicman->bfrstate)))
    (stobj-let ((aignet (logicman->aignet logicman)))
               (err env$)
               (stobj-let ((bitarr (env$->bitarr env$)))
                          (err bitarr)
                          (bfrstate-case
                            :aignet
                            (b* ((bitarr (resize-bits (aignet::num-fanins aignet) bitarr))
                                 (bitarr (aignet::aignet-eval bitarr aignet)))
                              (mv nil bitarr))
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


(define interp-st-satlink-counterexample (params
                                          (interp-st interp-st-bfrs-ok)
                                          state)
  :returns (mv err new-interp-st)
  (declare (ignore params state))
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (env$ (interp-st->ctrex-env interp-st)))
             (err env$)
             (logicman-satlink-counterexample logicman env$)
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


(make-event
 `(define fgl-satlink-default-toplevel-sat-check-config ()
    ',(make-fgl-satlink-monolithic-sat-config :ignore-pathcond nil)))

(defmacro fgl-use-satlink ()
  '(progn (defattach interp-st-sat-check interp-st-satlink-sat-check-impl)
          (defattach interp-st-sat-counterexample interp-st-satlink-counterexample)
          (defattach fgl-toplevel-sat-check-config fgl-satlink-default-toplevel-sat-check-config)))

(fgl-use-satlink)


