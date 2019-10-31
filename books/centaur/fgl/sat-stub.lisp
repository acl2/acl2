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
(local (std::add-default-post-define-hook :fix))
(local (include-book "std/lists/resize-list" :dir :system))

(local (in-theory (disable w)))

(defconst *interp-st-sat-check-thms-base*
  '((defret interp-st-bfrs-ok-of-<fn>
      (implies (and (interp-st-bfrs-ok interp-st)
                    (interp-st-bfr-p bfr))
               (interp-st-bfrs-ok new-interp-st)))

    ;; (defret interp-st-bfr-p-of-<fn>
    ;;   (implies (and (interp-st-bfrs-ok interp-st)
    ;;                 (interp-st-bfr-p bfr)
    ;;                 (equal logicman (interp-st->logicman interp-st)))
    ;;            (lbfr-p ans logicman)))


    (defret interp-st-get-of-<fn>
      (implies (and (not (equal (interp-st-field-fix key) :logicman))
                    (not (equal (interp-st-field-fix key) :errmsg))
                    (not (equal (interp-st-field-fix key) :debug-info))
                    (not (equal (interp-st-field-fix key) :debug-stack))
                    (not (equal (interp-st-field-fix key) :sat-ctrex))
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

    ;; (defret pathcond-eval-checkpoints-of-<fn>
    ;;   (implies (equal pathcond (interp-st->pathcond interp-st))
    ;;            (equal (logicman-pathcond-eval-checkpoints!
    ;;                    env
    ;;                    pathcond
    ;;                    (interp-st->logicman new-interp-st))
    ;;                   (logicman-pathcond-eval-checkpoints!
    ;;                    env
    ;;                    pathcond
    ;;                    (interp-st->logicman interp-st)))))

    ;;   (defret constraint-eval-of-<fn>
    ;;     (implies (equal constraint (interp-st->constraint interp-st))
    ;;              (equal (logicman-pathcond-eval
    ;;                      env
    ;;                      constraint
    ;;                      (interp-st->logicman new-interp-st))
    ;;                     (logicman-pathcond-eval
    ;;                      env
    ;;                      constraint
    ;;                      (interp-st->logicman interp-st)))))
    
    (defret <fn>-return-values-correct
      (equal (list . <values>)
             <call>))

    (defret <fn>-preserves-errmsg
      (let ((errmsg (interp-st->errmsg interp-st)))
        (implies errmsg
                 (equal (interp-st->errmsg new-interp-st) errmsg))))

    
    
    ;; (defret get-bvar->term-eval-of-<fn>
    ;;   (implies (equal bvar-db (interp-st->bvar-db interp-st))
    ;;            (iff (fgl-object-eval (get-bvar->term$a n bvar-db)
    ;;                                  env
    ;;                                  (interp-st->logicman new-interp-st))
    ;;                 (fgl-object-eval (get-bvar->term$a n bvar-db)
    ;;                                  env
    ;;                                  (interp-st->logicman interp-st)))))

    (defret interp-st->errmsg-equal-unreachable-of-<fn>
      (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
               (not (equal (interp-st->errmsg new-interp-st) :unreachable))))

    (defret logicman-equiv-of-<fn>
      (logicman-equiv (interp-st->logicman new-interp-st)
                      (interp-st->logicman interp-st))
      :hints(("Goal" :in-theory (enable logicman-equiv))))

    (defret w-state-of-<fn>
      (equal (w new-state) (w state)))))

(defconst *interp-st-sat-check-thms*
  (append *interp-st-sat-check-thms-base*
          '(;; (defret status-of-<fn>
            ;;   (or (equal status :unsat)
            ;;       (equal status :sat)
            ;;       (equal status :failed))
            ;;   :rule-classes ((:forward-chaining :trigger-terms (status))))

            (defret <fn>-unsat-implies
              (implies (and (equal status :unsat)
                            (interp-st-bfrs-ok interp-st)
                            (interp-st-bfr-p bfr)
                            (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                    (interp-st->pathcond interp-st)
                                                    (interp-st->logicman interp-st))
                            (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                    (interp-st->constraint interp-st)
                                                    (interp-st->logicman interp-st)))
                       (not (gobj-bfr-eval bfr env (interp-st->logicman interp-st))))))))


(make-event
 `(encapsulate
    (((interp-st-sat-check * * interp-st state)
      => (mv * interp-st state)
      :formals (params bfr interp-st state)
      :guard (and (interp-st-bfr-p bfr)
                  (interp-st-bfrs-ok interp-st))))
    (local
     (define interp-st-sat-check (params
                                  (bfr interp-st-bfr-p)
                                  (interp-st interp-st-bfrs-ok)
                                  state)
       :returns (mv status
                    new-interp-st new-state)
       :ignore-ok t
       :irrelevant-formals-ok t
       (mv :failed interp-st state)))

    (local (in-theory (enable interp-st-sat-check)))
    
    . ,*interp-st-sat-check-thms*))






;; (make-event
;;  `(encapsulate
;;     (((interp-st-monolithic-sat-check * * interp-st state)
;;       => (mv * interp-st)
;;       :formals (params bfr interp-st state)
;;       :guard (and (interp-st-bfr-p bfr)
;;                   (interp-st-bfrs-ok interp-st))))
;;     (local
;;      (define interp-st-monolithic-sat-check (params
;;                                              (bfr interp-st-bfr-p)
;;                                              (interp-st interp-st-bfrs-ok)
;;                                              state)
;;        :returns (mv ans
;;                     new-interp-st)
;;        :ignore-ok t
;;        :irrelevant-formals-ok t
;;        (mv bfr interp-st)))

;;     (local (in-theory (enable interp-st-monolithic-sat-check)))
;;     . 
;;     ,*interp-st-sat-check-thms*))




;; (make-event
;;  `(define fgl-sat-check-impl ((params fgl-object-p)
;;                                        (bfr interp-st-bfr-p)
;;                                        (interp-st interp-st-bfrs-ok)
;;                                        state)
;;     :returns (mv ans
;;                  new-interp-st
;;                  new-state)
;;     :ignore-ok t
;;     :irrelevant-formals-ok t
;;     (b* (((unless (fgl-object-case params :g-concrete))
;;           (fgl-interp-error
;;            :msg (fgl-msg "Malformed fgl-sat-check call: params was not resolved to a value"))))
;;       (interp-st-sat-check (g-concrete->val params) bfr interp-st state))
;;     ///
;;     ,@*interp-st-sat-check-thms-base*
;;     (defret eval-of-<fn>
;;       (implies (and (interp-st-bfrs-ok interp-st)
;;                     (interp-st-bfr-p bfr)
;;                     (not (interp-st->errmsg new-interp-st))
;;                     (equal logicman (interp-st->logicman interp-st))
;;                     (logicman-pathcond-eval (fgl-env->bfr-vals env)
;;                                             (interp-st->pathcond interp-st)
;;                                             (interp-st->logicman interp-st))
;;                     (logicman-pathcond-eval (fgl-env->bfr-vals env)
;;                                             (interp-st->constraint interp-st)
;;                                             (interp-st->logicman interp-st)))
;;                (equal (gobj-bfr-eval ans env logicman)
;;                       (gobj-bfr-eval bfr env (interp-st->logicman interp-st)))))))


;; (local (defthm aignet-lit->bfr-of-extension
;;          (implies (and (logicman-extension-p new old)
;;                        (aignet::aignet-litp x (logicman->aignet old))
;;                        (lbfr-mode-is :aignet old))
;;                   (equal (aignet-lit->bfr x (logicman->bfrstate new))
;;                          (aignet-lit->bfr x (logicman->bfrstate old))))
;;          :hints(("Goal" :in-theory (enable aignet-lit->bfr
;;                                            logicman->bfrstate
;;                                            logicman-extension-p)))))

;; (local (defthm bfr-not-of-logicman-extension
;;          (implies (and (logicman-extension-p new old)
;;                        (lbfr-p x old))
;;                   (equal (bfr-not x new)
;;                          (bfr-not x old)))
;;          :hints(("Goal" :in-theory (enable bfr-not)))))

;; (local (defthm bfr-not-of-interp-st-logicman-extension
;;          (implies (and (equal old-logicman (interp-st->logicman old))
;;                        (logicman-extension-p (interp-st->logicman new) old-logicman)
;;                        (lbfr-p x old-logicman))
;;                   (equal (bfr-not x (interp-st->logicman new))
;;                          (bfr-not x old-logicman)))))

;; (local (defthm bfr-not-logicman-equiv-congruence
;;          (implies (logicman-equiv new old)
;;                   (equal (bfr-not x new)
;;                          (bfr-not x old)))
;;          :hints(("Goal" :in-theory (e/d (bfr-not)
;;                                         (logicman->bfrstate-updater-independence))))
;;          :rule-classes :congruence))

;; (make-event
;;  `(define interp-st-validity-check (params
;;                                     (bfr interp-st-bfr-p)
;;                                     (interp-st interp-st-bfrs-ok)
;;                                     state)
;;     :returns (mv ans new-interp-st new-state)
;;     (b* ((not-bfr (stobj-let ((logicman (interp-st->logicman interp-st)))
;;                              (bfr)
;;                              (bfr-not bfr)
;;                              bfr))
;;          ((mv not-ans interp-st state)
;;           (interp-st-sat-check params not-bfr interp-st state)))
;;       (stobj-let ((logicman (interp-st->logicman interp-st)))
;;                  (bfr)
;;                  (bfr-not not-ans)
;;                  (mv bfr interp-st state)))
;;     ///
;;     (local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval)))

;;     . ,*interp-st-sat-check-thms*))


;; (make-event
;;  `(define interp-st-monolithic-validity-check (params
;;                                                (bfr interp-st-bfr-p)
;;                                                (interp-st interp-st-bfrs-ok)
;;                                                state)
;;     :returns (mv ans new-interp-st)
;;     (b* ((not-bfr (stobj-let ((logicman (interp-st->logicman interp-st)))
;;                              (bfr)
;;                              (bfr-not bfr)
;;                              bfr))
;;          ((mv not-ans interp-st)
;;           (interp-st-monolithic-sat-check params not-bfr interp-st state)))
;;       (stobj-let ((logicman (interp-st->logicman interp-st)))
;;                  (bfr)
;;                  (bfr-not not-ans)
;;                  (mv bfr interp-st)))
;;     ///
;;     (local (in-theory (disable gobj-bfr-eval-reduce-by-bfr-eval)))

;;     . ,*interp-st-sat-check-thms*))




;; Interp-st-get-counterexample: attachable function that just returns an env$,
;; which is the stobj we use in ctrex-utils to evaluate objects.


(define bfr-env$-p (env$ (bfrstate bfrstate-p))
  (bfrstate-case
    :bdd (stobj-let ((bitarr (env$->bitarr env$)))
                    (ok)
                    (<= (bfrstate->bound bfrstate) (bits-length bitarr))
                    ok)
    :aig t
    :aignet (stobj-let ((bitarr (env$->bitarr env$)))
                       (ok)
                       (< (bfrstate->bound bfrstate) (bits-length bitarr))
                       ok))
  ///
  (defthm bfr-env$-p-of-update-obj-alist
    (equal (bfr-env$-p (update-env$->obj-alist obj-alist env$) bfrstate)
           (bfr-env$-p env$ bfrstate))))

(encapsulate
  (((interp-st-sat-counterexample * interp-st state) => (mv * interp-st)
    :formals (params interp-st state)
    :guard (interp-st-bfrs-ok interp-st)))
  (local (defun interp-st-sat-counterexample (params interp-st state)
           (declare (Xargs :guard (interp-st-bfrs-ok interp-st)
                           :stobjs (interp-st state))
                    (ignore params state))
           (mv t interp-st)))

  (defthm interp-st-get-of-interp-st-sat-counterexample
    (implies (and (not (equal (interp-st-field-fix key) :ctrex-env))
                  (not (equal (interp-st-field-fix key) :sat-ctrex)))
             (equal (interp-st-get key (mv-nth 1 (interp-st-sat-counterexample params interp-st state)))
                    (interp-st-get key interp-st))))

  (defthm bfr-env$-p-of-interp-st-sat-counterexample
    (b* (((mv err new-interp-st) (interp-st-sat-counterexample params interp-st state)))
      (implies (not err)
               (bfr-env$-p (interp-st->ctrex-env new-interp-st)
                           (logicman->bfrstate (interp-st->logicman interp-st)))))
    :hints(("Goal" :in-theory (enable bfr-env$-p))))

  (defthm aignet-vals-p-of-interp-st-sat-counterexample
    (b* (((mv err new-interp-st) (interp-st-sat-counterexample params interp-st state)))
      (implies (and (not err)
                    (bfr-mode-is :aignet (interp-st-bfr-mode)))
               (aignet::aignet-vals-p
                (env$->bitarr (interp-st->ctrex-env new-interp-st))
                (logicman->aignet (interp-st->logicman interp-st)))))))

;; (encapsulate
;;   (((interp-st-monolithic-sat-counterexample interp-st state) => (mv * interp-st)
;;     :formals (interp-st state)
;;     :guard (interp-st-bfrs-ok interp-st)))
;;   (local (defun interp-st-monolithic-sat-counterexample (interp-st state)
;;            (declare (Xargs :guard (interp-st-bfrs-ok interp-st)
;;                            :stobjs (interp-st state))
;;                     (ignore state))
;;            (mv t interp-st)))

;;   (defthm interp-st-get-of-interp-st-monolithic-sat-counterexample
;;     (implies (and (not (equal (interp-st-field-fix key) :ctrex-env))
;;                   (not (equal (interp-st-field-fix key) :sat-ctrex)))
;;              (equal (interp-st-get key (mv-nth 1 (interp-st-monolithic-sat-counterexample interp-st state)))
;;                     (interp-st-get key interp-st))))

;;   (defthm bfr-env$-p-of-interp-st-monolithic-sat-counterexample
;;     (b* (((mv err new-interp-st) (interp-st-monolithic-sat-counterexample interp-st state)))
;;       (implies (not err)
;;                (bfr-env$-p (interp-st->ctrex-env new-interp-st)
;;                            (logicman->bfrstate (interp-st->logicman interp-st)))))
;;     :hints(("Goal" :in-theory (enable bfr-env$-p)))))
