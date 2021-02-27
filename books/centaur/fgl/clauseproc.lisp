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

(include-book "interp")
(include-book "ctrex-utils")
(include-book "casesplit")

(local (in-theory (disable pseudo-termp pseudo-term-listp)))
;; (include-book "primitives")

(define variable-g-bindings ((vars pseudo-var-list-p))
  :returns (bindings fgl-object-bindings-p)
  (if (atom vars)
      nil
    (cons (cons (pseudo-var-fix (car vars))
                (g-var (car vars)))
          (variable-g-bindings (cdr vars))))
  ///
  (defret fgl-object-bindings-bfrlist-of-<fn>
    (equal (fgl-object-bindings-bfrlist bindings) nil))

  (defret alist-keys-of-<fn>
    (equal (alist-keys bindings)
           (pseudo-var-list-fix vars))
    :hints(("Goal" :in-theory (enable alist-keys))))

  (defret lookup-in-<fn>
    (equal (hons-assoc-equal k bindings)
           (and (member k (pseudo-var-list-fix vars))
                (cons k (g-var k))))
    :hints(("Goal" :in-theory (enable pseudo-var-list-fix)))))


(defun def-cons-opener-fn (accessor wrld)
  (Declare (Xargs :mode :program))
  (b* ((fn (acl2::deref-macro-name accessor (acl2::macro-aliases wrld)))
       (formals (acl2::formals fn wrld))
       (body (body fn nil wrld))
       ((unless (eql (len formals) 1))
        (er hard? 'def-cons-opener-fn "Only works for single-argument functions")))
    `(defthm ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name accessor) "-OF-CONS")
               accessor)
       (equal (,accessor (cons a b))
              (let ((,(car formals) (cons a b)))
                ,body))
       :hints(("Goal" :in-theory (enable ,accessor))))))


(defmacro def-cons-opener (accessor)
  `(make-event
    (def-cons-opener-fn ',accessor (w state))))

(encapsulate nil
  (set-ignore-ok t)
  (def-cons-opener interp-st->logicman)
  (def-cons-opener interp-st->stack)
  (def-cons-opener interp-st->constraint-db)
  (def-cons-opener interp-st->constraint-db^)
  (def-cons-opener interp-st->bvar-db)
  (def-cons-opener interp-st->pathcond)
  (def-cons-opener interp-st->constraint)
  (def-cons-opener interp-st->cgraph)
  (def-cons-opener interp-st->cgraph^)
  (def-cons-opener logicman->bfrstate)
  (def-cons-opener logicman->aignet)
  (def-cons-opener logicman->mode)
  (def-cons-opener logicman->mode^)
  (def-cons-opener logicman->ipasir-length)
  (def-cons-opener logicman->sat-lits-length)
  (def-cons-opener logicman->aignet-refcounts)
  (def-cons-opener logicman->refcounts-index)
  (def-cons-opener logicman->refcounts-index^))


(local (defthm sat-lits-wfp-of-create-sat-lits
         (aignet::sat-lits-wfp (aignet::create-sat-lits) aignet)
         :hints(("Goal" :in-theory (enable aignet::sat-lits-wfp aignet::create-sat-lits)))))

;; (local (defthm cnf-for-aignet-of-create-sat-lits
;;          (aignet::cnf-for-aignet aignet nil (aignet::create-sat-lits))
;;          :hints(("Goal" :in-theory (enable aignet::cnf-for-aignet aignet::create-sat-lits
;;                                            aignet::aignet-agrees-with-cnf
;;                                            aignet::aignet-id-has-sat-var
;;                                            satlink::eval-formula)))))


(local (in-theory (disable w)))

(define initialize-interp-st ((config fgl-config-p)
                              (interp-st)
                              state)
  :returns (mv new-interp-st new-state)
  :prepwork ((local (defthm constraint-db-bfrlist-of-fast-alist-fork
                      (implies (and (not (member v (constraint-db-bfrlist x)))
                                    (not (member v (constraint-db-bfrlist y))))
                               (not (member v (constraint-db-bfrlist (fast-alist-fork x y))))))))
  :verify-guards nil
  (b* ((interp-st (interp-st-init interp-st))
       ((fgl-config config))
       (interp-st (update-interp-st->reclimit config.reclimit interp-st))
       (interp-st (update-interp-st->config config interp-st))
       (interp-st (update-interp-st-prof-enabledp config.prof-enabledp interp-st))
       (constraint-db (table-alist 'fgl::fgl-bool-constraints (w state)))
       (interp-st (if (and (constraint-db-p constraint-db)
                           (not (constraint-db-bfrlist constraint-db)))
                      (update-interp-st->constraint-db
                       (gbc-db-make-fast constraint-db) interp-st)
                    interp-st))
       (flags (interp-st->flags interp-st))
       (interp-st (update-interp-st->flags
                   (!interp-flags->make-ites
                    config.make-ites
                    (!interp-flags->trace-rewrites config.trace-rewrites flags))
                   interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (logicman)
               (update-logicman->mode (bfrmode :aignet) logicman)
               (mv interp-st state)))
  ///
  (local (defthm interp-st->stack-of-create-interp-st
           (equal (interp-st->stack (create-interp-st))
                  (create-stack))
           :hints(("Goal" :in-theory (enable* interp-st-defs)))))

  (local (defthm interp-st->constraint-of-create-interp-st
           (equal (interp-st->constraint (create-interp-st))
                  (create-pathcond))
           :hints(("Goal" :in-theory (enable* interp-st-defs)))))

  (local (defthm interp-st->pathcond-of-create-interp-st
           (equal (interp-st->pathcond (create-interp-st))
                  (create-pathcond))
           :hints(("Goal" :in-theory (enable* interp-st-defs)))))

  (local (defthm interp-st->bvar-db-of-create-interp-st
           (equal (interp-st->bvar-db (create-interp-st))
                  (create-bvar-db))
           :hints(("Goal" :in-theory (enable* interp-st-defs)))))

  (local (defthm interp-st->constraint-db-of-create-interp-st
           (equal (interp-st->constraint-db (create-interp-st))
                  nil)
           :hints(("Goal" :in-theory (enable* interp-st-defs)))))

  (local (defthm interp-st->equiv-contexts-of-create-interp-st
           (equal (interp-st->equiv-contexts (create-interp-st))
                  nil)
           :hints(("Goal" :in-theory (enable* interp-st-defs)))))

  (local (defthm interp-st->cgraph-of-create-interp-st
           (equal (interp-st->cgraph (create-interp-st))
                  nil)
           :hints(("Goal" :in-theory (enable* interp-st-defs)))))



  (local (in-theory (e/d (interp-st-init)
                         (create-interp-st))))
  ;; (defthm initialize-interp-st-norm
  ;;   (implies (syntaxp (not (equal interp-st ''nil)))
  ;;            (equal (initialize-interp-st config interp-st state)
  ;;                   (initialize-interp-st config nil state))))

  ;; (local
  ;;  (acl2::set-default-hints
  ;;   '('(:in-theory (e/d (interp-st-bfrs-ok
  ;;                               major-stack-bfrlist
  ;;                               stack$a-set-bindings
  ;;                               major-frame-bfrlist
  ;;                               bfr-nvars)))
  ;;     (and stable-under-simplificationp
  ;;          '(:in-theory (e/d (;; interp-st->logicman
  ;;                             ;; interp-st->stack
  ;;                             ;; interp-st->constraint-db
  ;;                             ;; interp-st->constraint-db^
  ;;                             ;; interp-st->bvar-db
  ;;                             ;; interp-st->pathcond
  ;;                             ;; interp-st->constraint
  ;;                             logicman-invar
  ;;                             ;; logicman->bfrstate
  ;;                             ;; logicman->aignet
  ;;                             ;; logicman->mode
  ;;                             ;; logicman->mode^
  ;;                             bvar-db-bfrlist
  ;;                             bvar-db-bfrlist-aux
  ;;                             logicman-pathcond-p
  ;;                             logicman-pathcond-eval
  ;;                             aignet::aignet-pathcond-eval
  ;;                             aignet::aignet-pathcond-p
  ;;                             aignet::nbalist-lookup
  ;;                             interp-st-bvar-db-ok
  ;;                             ipasir::ipasir-init$a)
  ;;                            (pathcond-fix-of-pathcond-fix-pathcond-normalize-const
  ;;                             LOGICMAN-PATHCOND-P-FN-OF-PATHCOND-FIX-PATHCOND-NORMALIZE-CONST
  ;;                             LOGICMAN-PATHCOND-EVAL-FN-OF-PATHCOND-FIX-PATHCOND-NORMALIZE-CONST
  ;;                             (pathcond-fix))))))))

  (local (in-theory (disable (pathcond-fix)
                             (update-logicman->mode))))

  (local (in-theory (enable  interp-st-bfrs-ok
                             logicman-pathcond-p
                             logicman-invar
                             aignet::bounded-pathcond-p
                             ipasir::ipasir-init$a
                             bvar-db-bfrlist
                             bvar-db-bfrlist-aux
                             bfr-nvars
                             aignet::aignet-idp
                             aignet::nbalist-lookup)))

  (defret interp-st-bfrs-ok-of-<fn>
    (interp-st-bfrs-ok new-interp-st)
    :hints (("goal" :do-not '(preprocess)
             :in-theory (enable logicman-ipasir-sat-lits-invar
                                logicman-ipasirs-assumption-free
                                bfr-listp-when-not-member-witness)
             :expand ((:free (var) (aignet::nbalist-boundp var nil))))))

  (defret pathcond-eval-of-<fn>
    (logicman-pathcond-eval env (interp-st->pathcond new-interp-st)
                            (interp-st->logicman new-interp-st))
    :hints (("goal" :do-not '(preprocess)
             :in-theory (enable logicman-pathcond-eval
                                aignet::aignet-pathcond-eval)
             :expand ((:free (var) (aignet::nbalist-boundp var nil))))))

  (defret constraint-eval-of-<fn>
    (logicman-pathcond-eval env (interp-st->constraint new-interp-st)
                            (interp-st->logicman new-interp-st))
    :hints (("goal" :do-not '(preprocess)
             :in-theory (enable logicman-pathcond-eval
                                aignet::aignet-pathcond-eval)
             :expand ((:free (var) (aignet::nbalist-boundp var nil))))))

  (defret equiv-contexts-of-<fn>
    (equal (interp-st->equiv-contexts new-interp-st) nil)
    :hints (("goal" :do-not '(preprocess)
             :in-theory (enable logicman-pathcond-eval
                                aignet::aignet-pathcond-eval))))

  (defret interp-st-bvar-db-ok-of-<fn>
    (interp-st-bvar-db-ok new-interp-st env)
    :hints(("Goal" :in-theory (enable interp-st-bvar-db-ok))))

  (defret stack$a-minor-bindings-of-<fn>
    (equal (stack$a-minor-bindings (interp-st->stack new-interp-st)) nil))

  (verify-guards initialize-interp-st)

  (defret w-of-<fn>
    (equal (w new-state) (w state))
    :hints(("Goal" :in-theory (enable w get-global)
            :expand ((read-acl2-oracle state)
                     (:free (val) (update-acl2-oracle val state)))))))

(local (defthm member-bfrlist-of-lookup-in-bvar-db
         (implies (and (not (consp (bvar-db-bfrlist bvar-db)))
                       (<= (base-bvar$a bvar-db) (nfix n))
                       (< (nfix n) (next-bvar$a bvar-db)))
                  (not (member v (fgl-object-bfrlist (get-bvar->term$a n bvar-db)))))))

(local (defthm atom-bfrlist-of-lookup-in-bvar-db
         (implies (and (not (consp (bvar-db-bfrlist bvar-db)))
                       (<= (base-bvar$a bvar-db) (nfix n))
                       (< (nfix n) (next-bvar$a bvar-db)))
                  (not (consp (fgl-object-bfrlist (get-bvar->term$a n bvar-db)))))
         :hints (("goal" :use ((:instance member-bfrlist-of-lookup-in-bvar-db
                                (v (car (fgl-object-bfrlist (get-bvar->term$a n bvar-db))))))
                  :in-theory (disable member-bfrlist-of-lookup-in-bvar-db
                                      bfrlist-of-get-bvar->term)))))




(define bvar-db-to-bfr-env-aux ((n natp) (env fgl-env-p) bvar-db logicman)
  :guard (and (<= n (next-bvar bvar-db))
              (<= (base-bvar bvar-db) n)
              (not (consp (bvar-db-bfrlist bvar-db))))
  :measure (nfix (- (next-bvar bvar-db) (nfix n)))
  (b* (((When (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (eql (next-bvar bvar-db) n)))
        env)
       (obj (get-bvar->term n bvar-db))
       (val (bool-fix (fgl-object-eval obj env logicman)))
       (env (change-fgl-env env :bfr-vals (bfr-set-var n val (fgl-env->bfr-vals env)))))
    (bvar-db-to-bfr-env-aux (+ 1 (lnfix n)) env bvar-db logicman))
  ///

  (defthm fgl-env->obj-alist-of-bvar-db-to-bfr-env-aux
    (equal (fgl-env->obj-alist (bvar-db-to-bfr-env-aux n env bvar-db logicman))
           (fgl-env->obj-alist env)))

  (defthm gobj-var-lookup-of-bfr-set-var
    (equal (gobj-var-lookup v (fgl-env (fgl-env->obj-alist env)
                                      bfr-vals))
           (gobj-var-lookup v env))
    :hints(("Goal" :in-theory (enable gobj-var-lookup))))

  (defthm gobj-var-lookup-of-bvar-db-to-bfr-env-aux
    (equal (gobj-var-lookup v (bvar-db-to-bfr-env-aux n env bvar-db logicman))
           (gobj-var-lookup v env)))

  (defthm bvar-db-to-bfr-env-aux-preserves-bfr-eval-when-bounded
    (implies (and (bfr-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (bfr-eval x (fgl-env->bfr-vals (bvar-db-to-bfr-env-aux n env bvar-db logicman)) logicman)
                    (bfr-eval x (fgl-env->bfr-vals env) logicman))))

  (defthm bvar-db-to-bfr-env-aux-preserves-bfrlist-eval-when-bounded
    (implies (and (bfrlist-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (bfr-list-eval x (fgl-env->bfr-vals (bvar-db-to-bfr-env-aux n env bvar-db logicman)) logicman)
                    (bfr-list-eval x (fgl-env->bfr-vals env) logicman)))
    :hints(("Goal" :in-theory (e/d (bfrlist-boundedp bfr-list-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defthm bvar-db-to-bfr-env-aux-preserves-gobj-bfr-eval-when-bounded
    (implies (and (bfr-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (gobj-bfr-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                    (gobj-bfr-eval x env logicman)))
    :hints(("Goal" :in-theory (e/d (gobj-bfr-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defthm bvar-db-to-bfr-env-aux-preserves-gobj-bfrlist-eval-when-bounded
    (implies (and (bfrlist-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (gobj-bfr-list-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                    (gobj-bfr-list-eval x env logicman)))
    :hints(("Goal" :in-theory (e/d (bfrlist-boundedp gobj-bfr-list-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defthm gobj-bfr-eval-of-set-var-when-bounded
    (implies (and (bfr-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (gobj-bfr-eval x (fgl-env (fgl-env->obj-alist env)
                                             (bfr-set-var n v (fgl-env->bfr-vals env))) logicman)
                    (gobj-bfr-eval x env logicman)))
    :hints(("Goal" :in-theory (e/d (gobj-bfr-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defthm gobj-bfrlist-eval-of-set-var-when-bounded
    (implies (and (bfrlist-boundedp x m logicman)
                  (<= (nfix m) (nfix n)))
             (equal (gobj-bfr-list-eval x (fgl-env (fgl-env->obj-alist env)
                                                  (bfr-set-var n v (fgl-env->bfr-vals env))) logicman)
                    (gobj-bfr-list-eval x env logicman)))
    :hints(("Goal" :in-theory (e/d (bfrlist-boundedp gobj-bfr-list-eval)
                                   (bvar-db-to-bfr-env-aux)))))

  (defret-mutual fgl-object-eval-of-bvar-db-to-bfr-env-aux-when-bounded
    (defret fgl-object-eval-of-bvar-db-to-bfr-env-aux-when-bounded
      (implies (and (bfrlist-boundedp (fgl-object-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-object-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                      (fgl-object-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-object-eval x env logicman))
                         (fgl-object-bfrlist x)))
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable if*
              ;;                           gobj-var-lookup
              ;;                           gobj-bfr-list-eval)))
              )
      :fn fgl-object-eval)

    (defret fgl-objectlist-eval-of-bvar-db-to-bfr-env-aux-when-bounded
      (implies (and (bfrlist-boundedp (fgl-objectlist-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-objectlist-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                      (fgl-objectlist-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-objectlist-eval x env logicman))
                         (fgl-objectlist-bfrlist x)))
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable if*
              ;;                           gobj-var-lookup
              ;;                           gobj-bfr-list-eval)))
              )
      :fn fgl-objectlist-eval)

    (defret fgl-object-alist-eval-of-bvar-db-to-bfr-env-aux-when-bounded
      (implies (and (bfrlist-boundedp (fgl-object-alist-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-object-alist-eval x (bvar-db-to-bfr-env-aux n env bvar-db logicman) logicman)
                      (fgl-object-alist-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-object-alist-eval x env logicman))
                         (fgl-object-alist-bfrlist x)))
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable if*
              ;;                           gobj-var-lookup
              ;;                           gobj-bfr-list-eval)))
              )
      :fn fgl-object-alist-eval)
    :mutual-recursion fgl-object-eval)

  (defret-mutual fgl-object-eval-of-bfr-set-var-when-bounded
    (defret fgl-object-eval-of-bfr-set-var-when-bounded
      (implies (and (bfrlist-boundedp (fgl-object-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-object-eval x (fgl-env (fgl-env->obj-alist env)
                                                 (bfr-set-var n v (fgl-env->bfr-vals env)))
                                       logicman)
                      (fgl-object-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-object-eval x env logicman))
                         (fgl-object-bfrlist x))))
      :fn fgl-object-eval)

    (defret fgl-objectlist-eval-of-bfr-set-var-when-bounded
      (implies (and (bfrlist-boundedp (fgl-objectlist-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-objectlist-eval x (fgl-env (fgl-env->obj-alist env)
                                                     (bfr-set-var n v (fgl-env->bfr-vals env)))
                                       logicman)
                      (fgl-objectlist-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-objectlist-eval x env logicman))
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-eval)

    (defret fgl-object-alist-eval-of-bfr-set-var-when-bounded
      (implies (and (bfrlist-boundedp (fgl-object-alist-bfrlist x) m logicman)
                    (<= (nfix m) (nfix n)))
               (equal (fgl-object-alist-eval x (fgl-env (fgl-env->obj-alist env)
                                                     (bfr-set-var n v (fgl-env->bfr-vals env)))
                                       logicman)
                      (fgl-object-alist-eval x env logicman)))
      :hints ('(:expand ((:free (env logicman) (fgl-object-alist-eval x env logicman))
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-eval)
    :mutual-recursion fgl-object-eval)


  (defthm bfr-lookup-preserved-by-of-bvar-db-to-bfr-env-aux
    (implies (< (nfix m) (nfix n))
             (equal (bfr-lookup m (fgl-env->bfr-vals
                                   (bvar-db-to-bfr-env-aux n env bvar-db logicman)))
                    (bfr-lookup m (fgl-env->bfr-vals env)))))

  ;; (defret fgl-object-eval-when-no-bvars-rw
  ;;   (implies (and (syntaxp (not (and (equal bfr-env ''nil)
  ;;                                    (equal logicman ''nil))))
  ;;                 (not (consp (fgl-object-bfrlist x))))
  ;;            (equal (fgl-object-eval x (fgl-env obj-alist bfr-env) logicman)
  ;;                   (fgl-object-eval x (fgl-env obj-alist nil) nil)))
  ;;   :hints (("Goal" :use ((:instance fgl-object-eval-when-no-bvars
  ;;                          (env (fgl-env obj-alist bfr-env))))
  ;;            :in-theory (disable fgl-object-eval-when-no-bvars)))
  ;;   :fn fgl-object-eval)



  (local (in-theory (enable bfr-varname-p)))

  (defthm bvar-db-to-bfr-env-aux-correct
    (implies (and (bvar-db-boundedp bvar-db logicman)
                  (<= (base-bvar$a bvar-db) (nfix n))
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (next-bvar$a bvar-db))
                  (equal (next-bvar$a bvar-db) (bfr-nvars logicman)))
             (iff (bfr-lookup m
                              (fgl-env->bfr-vals (bvar-db-to-bfr-env-aux n env bvar-db logicman))
                              logicman)
                  (fgl-object-eval (get-bvar->term$a m bvar-db)
                                   (bvar-db-to-bfr-env-aux n env bvar-db logicman)
                                   logicman)))
    :hints (("goal"
             :in-theory (enable* acl2::arith-equiv-forwarding)
             :induct (bvar-db-to-bfr-env-aux n env bvar-db logicman))
            (and stable-under-simplificationp
                 '(:use ((:instance bvar-db-boundedp-necc
                          (var (nfix m))))))))

  (defthm bfr-set-var-when-logicman-equiv
    (implies (logicman-equiv logicman1 logicman2)
             (equal (bfr-set-var n val env logicman1)
                    (bfr-set-var n val env logicman2)))
    :hints(("Goal" :in-theory (enable bfr-set-var)))
    :rule-classes :congruence)

  (defthm bvar-db-to-bfr-env-aux-logicman-equiv
    (implies (logicman-equiv logicman1 logicman2)
             (equal (bvar-db-to-bfr-env-aux n env bvar-db logicman1)
                    (bvar-db-to-bfr-env-aux n env bvar-db logicman2)))
    :rule-classes :congruence))

(define fix-env-for-bvar-db ((env fgl-env-p) bvar-db logicman)
  :guard (not (consp (bvar-db-bfrlist bvar-db)))
  (bvar-db-to-bfr-env-aux (base-bvar bvar-db) env bvar-db logicman)
  ///

  (local (in-theory (enable bfr-varname-p)))

  (defthm interp-st-bvar-db-ok-of-fix-env-for-bvar-db
    (b* ((bvar-db (interp-st->bvar-db interp-st))
         (logicman (interp-st->logicman interp-st)))
      (implies (interp-st-bfrs-ok interp-st)
               (interp-st-bvar-db-ok interp-st
                                     (fix-env-for-bvar-db env bvar-db logicman))))
    :hints(("Goal" :in-theory (enable interp-st-bvar-db-ok
                                      interp-st-bfrs-ok))))

  (defthm fgl-env->obj-alist-of-<fn>
    (equal (fgl-env->obj-alist (fix-env-for-bvar-db env bvar-db logicman))
           (fgl-env->obj-alist env)))

  (defthm fix-env-for-bvar-db-when-logicman-equiv
    (implies (logicman-equiv logicman1 logicman2)
             (equal (fix-env-for-bvar-db env bvar-db logicman1)
                    (fix-env-for-bvar-db env bvar-db logicman2)))
    :rule-classes :congruence))



(local (in-theory (enable bfr-listp-when-not-member-witness)))


(local
 (defthm major-stack-bfrlist-of-stack$a-set-bindings
   (implies (and (not (member v (major-stack-bfrlist stack)))
                 (not (member v (fgl-object-bindings-bfrlist bindings))))
            (not (member v (major-stack-bfrlist (stack$a-set-bindings bindings stack)))))
   :hints(("Goal" :in-theory (enable stack$a-set-bindings
                                     major-stack-bfrlist
                                     major-frame-bfrlist
                                     minor-frame-bfrlist
                                     minor-stack-bfrlist)
           :do-not-induct t))))

(local
 (defthm major-stack-bfrlist-of-stack$a-set-term
      (equal (major-stack-bfrlist (stack$a-set-term obj stack))
             (major-stack-bfrlist stack))
      :hints(("Goal" :in-theory (enable stack$a-set-term
                                        major-stack-bfrlist
                                        major-frame-bfrlist
                                        minor-frame-bfrlist)
              :expand ((minor-stack-bfrlist (major-frame->minor-stack (car stack))))
              :do-not-induct t))))

(local (defthm assoc-when-nonnil
         (implies v
                  (equal (assoc v a)
                         (hons-assoc-equal v a)))))

;; (define fgl-primitive-formula-checks-wrap (state)
;;   :enabled t
;;   (fgl-primitive-formula-checks-stub state))


(define my-get-rewrite-rule-table (state)
  (and (boundp-global 'fgl-rewrite-rule-table state)
       (@ fgl-rewrite-rule-table)))


(define save-interp-st-info-into-state (interp-st state)
  (b* ((user-scratch (interp-st->user-scratch interp-st))
       (state (if user-scratch
                  (prog2$ (cw "~%The FGL interpreter's user scratch data is ~
                               stored in state global:~%~x0~%"
                              '(@ :fgl-user-scratch))
                          (f-put-global ':fgl-user-scratch user-scratch state))
                state))
       (errmsg (interp-st->errmsg interp-st))
       (debug-obj (interp-st->debug-info interp-st))
       (state
        (if (or errmsg debug-obj)
            (progn$ (cw "~%The FGL interpreter's error message (if any), ~
                         debug object, and debug stack are stored in the ~
                         following state globals:~%~x0~%~x1~%~x2~%"
                        '(@ :fgl-interp-error-message)
                        '(@ :fgl-interp-error-debug-obj)
                        '(@ :fgl-interp-error-debug-stack))
                    (pprogn
                     (f-put-global ':fgl-interp-error-message errmsg state)
                     (f-put-global ':fgl-interp-error-debug-obj debug-obj state)
                     (f-put-global ':fgl-interp-error-debug-stack (interp-st->debug-stack interp-st) state)))
          state)))
    state))

(local (defthm bfr-listp-of-stack$a-bindings-when-stack
         (implies (bfr-listp (major-stack-bfrlist stack))
                  (bfr-listp (fgl-object-bindings-bfrlist (stack$a-bindings stack))))
         :hints(("Goal" :in-theory (enable stack$a-bindings
                                           major-frame-bfrlist)
                 :expand ((major-stack-bfrlist stack))))))

(define fgl-toplevel-sat-check-config-wrapper (override)
  (or override (fgl-toplevel-sat-check-config)))

(local (defthm iff?-forall-extensions-of-nil
         (equal (iff?-forall-extensions nil obj term eval-alist)
                (iff-forall-extensions obj term eval-alist))
         :hints(("Goal" :in-theory (enable iff?-forall-extensions)))))

(define fgl-clause-proc-core ((goal pseudo-termp)
                              (config fgl-config-p)
                              (interp-st)
                              state)
  :returns (mv err
               (new-interp-st)
               (new-state))
  (b* ((vars (term-vars goal))
       ((mv interp-st state) (initialize-interp-st config interp-st state))
       (interp-st (update-interp-st->user-scratch (hons-acons :goal-term goal
                                                              (interp-st->user-scratch interp-st))
                                                  interp-st))
       (interp-st (interp-st-set-bindings (variable-g-bindings vars) interp-st))
       (interp-st (interp-st-set-term goal interp-st))
       ((acl2::hintcontext-bind ((init-interp-st interp-st)
                                 (init-interp-state state))))
       ((mv ans-interp interp-st state)
        (time$ (fgl-interp-test goal interp-st state)
               :msg "FGL interpreter completed: ~st sec, ~sa bytes~%"))
       ((acl2::hintcontext-bind ((interp-interp-st interp-st)
                                 (interp-state state))))
       (- (and (interp-st-prof-enabledp interp-st)
               (interp-st-prof-print-report interp-st)))
       ((acl2::hintcontext-bind ((early-interp-st interp-st)
                                 (early-state state))))
       ((when (and (equal ans-interp t)
                   (not (interp-st->errmsg interp-st))))
        ;; Proved!
        (acl2::hintcontext :interp-early
                           (mv nil interp-st state)))
       ((when (fgl-config->skip-toplevel-sat-check config))
        (mv (msg "FGL interpreter result was not syntactically T and skipping toplevel SAT check.")
            interp-st state))
       (sat-config (fgl-toplevel-sat-check-config-wrapper
                    (fgl-config->sat-config config)))
       ((mv ans interp-st state)
        (interp-st-sat-check
         ;; BOZO -- use a user-provided config
         sat-config
         (interp-st-bfr-not ans-interp) interp-st state))
       ((acl2::hintcontext-bind ((sat-interp-st interp-st)
                                 (sat-state state))))

       ((when (and (eq ans :unsat)
                   (not (interp-st->errmsg interp-st))))
        ;; Proved!
        (acl2::hintcontext :interp-test
                           (mv nil interp-st state)))
       ((when (interp-st->errmsg interp-st))
        (mv (msg "Interpreter error: ~@0" (interp-st->errmsg interp-st)) interp-st state))
       ((unless (eq ans :sat))
        (mv (msg "Final SAT check failed!") interp-st state))
       ((mv sat-ctrex-err interp-st)
        (interp-st-sat-counterexample sat-config interp-st state))
       ((when sat-ctrex-err)
        (mv (msg "Error retrieving SAT counterexample: ~@0~%" sat-ctrex-err) interp-st state))
       ((mv ctrex-errmsg ctrex-bindings ?var-vals interp-st)
        (interp-st-counterex-bindings (interp-st-bindings interp-st) interp-st state))
       (- (and ctrex-errmsg
               (cw "Warnings/errors from deriving counterexample: ~@0~%" ctrex-errmsg)))
       ;; ((when ctrex-errmsg)
       ;;  (mv (msg "Error extending counterexample: ~@0~%" ctrex-errmsg) interp-st state))
       (- (cw "~%*** Counterexample assignment: ***~%~x0~%~%" ctrex-bindings))
       (- (cw "Running counterexample on top-level goal:~%"))
       ((mv err ans) (magitastic-ev goal ctrex-bindings 1000 state t t))
       (- (cond (err (cw "Error running goal on counterexample: ~@0~%" err))
                (ans (cw "False counterexample -- returned: ~x0.  See ~
                          warnings/errors from counterexample derivation ~
                          above.~%" ans))
                (t   (cw "Counterexample verified!~%"))))
       (interp-st (interp-st-check-bvar-db-ctrex-consistency interp-st state))
       (interp-st (update-interp-st->debug-info ctrex-bindings interp-st)))
    (mv "Counterexample." interp-st state))
  ///


  (set-ignore-ok t)


  (local (in-theory (e/d (acl2::subsetp-append1
                          lookup-in-fgl-object-bindings-eval)
                         ;; (FGL-OBJECT-EVAL-OF-ALIST-LOOKUP)
                         )))
  (local
   (cmr::defthm-term-vars-flag
     (defthm fgl-ev-of-object-bindings-eval-of-variable-g-bindings
       (implies (subsetp (term-vars x) (pseudo-var-list-fix vars))
                (equal (fgl-ev x (fgl-object-bindings-eval (variable-g-bindings vars) env logicman))
                       (fgl-ev x (fgl-env->obj-alist env))))
       :hints('(:expand ((term-vars x))
                :in-theory (enable fgl-ev-when-pseudo-term-call
                                   gobj-var-lookup
                                   subsetp-equal)))
       :flag cmr::term-vars)
     (defthm fgl-ev-list-of-object-bindings-eval-of-variable-g-bindings
       (implies (subsetp (termlist-vars x) (pseudo-var-list-fix vars))
                (equal (fgl-ev-list x (fgl-object-bindings-eval (variable-g-bindings vars) env logicman))
                       (fgl-ev-list x (fgl-env->obj-alist env))))
       :hints('(:expand ((termlist-vars x))))
       :flag cmr::termlist-vars)))

  (local
   (cmr::defthm-term-vars-flag
     (defthm fgl-ev-of-obj-alist-fix
       (equal (fgl-ev x (obj-alist-fix a))
              (fgl-ev x a))
       :hints('(:expand ((term-vars x))
                :in-theory (enable fgl-ev-when-pseudo-term-call)))
       :flag cmr::term-vars)
     (defthm fgl-ev-list-of-obj-alist-fix
       (equal (fgl-ev-list x (obj-alist-fix a))
              (fgl-ev-list x a))
       :hints('(:expand ((termlist-vars x))))
       :flag cmr::termlist-vars)))


  ;; (local (skip-proofs
  ;;         (defthm fgl-primitive-formula-checks-wrap-true
  ;;           (fgl-primitive-formula-checks-wrap state))))

  (local (defthm fgl-object-bindings-eval-rewrite-with-fgl-object-bindings-ev
           (implies (and (equal ev (double-rewrite (fgl-object-bindings-concretize x env)))
                         (syntaxp (and (not (equal ev x))
                                       (case-match ev
                                         (('fgl-object-bindings-concretize-fn xans & &)
                                          (not (equal xans x)))
                                         (& t))))
                         (equal eval (fgl-object-bindings-eval ev nil nil))
                         (syntaxp (case-match eval
                                    (('fgl-object-bindings-eval-fn ('fgl-object-bindings-concretize-fn xans & &) & &)
                                     (not (equal xans x)))
                                    (('fgl-object-bindings-eval-fn xans & &)
                                     (not (equal xans x)))
                                    (& t))))
                    (equal (fgl-object-bindings-eval x env) eval))))

  (local (defthm fgl-object-bindings-ev-of-stack$a-bindings
           (equal (fgl-object-bindings-concretize (stack$a-bindings stack) env)
                  (double-rewrite (stack$a-bindings (fgl-major-stack-concretize stack env))))
           :hints(("Goal" :in-theory (enable fgl-major-frame-concretize
                                             stack$a-bindings)
                   :expand ((fgl-major-stack-concretize stack env))
                   :do-not-induct t))))

  (local (defthm fgl-major-stack-concretize-identity
           (equal (fgl-major-stack-concretize (fgl-major-stack-concretize x env) env2 logicman2)
                  (fgl-major-stack-concretize x env))
           :hints(("Goal" :in-theory (enable fgl-major-stack-concretize)))))


  (local (in-theory (disable fgl-interp-test-bvar-db-ok-implies-previous-ok)))

  (defret fgl-clause-proc-core-correct
    (implies (and (fgl-ev-meta-extract-global-facts)
                  (fgl-formula-checks-stub state)
                  (not err))
             (fgl-ev goal a))
    :hints ((acl2::function-termhint
             fgl-clause-proc-core
             (:interp-test
              (b* ((NEW-LOGICMAN (INTERP-ST->LOGICMAN sat-INTERP-ST))
                   (LOGICMAN (INTERP-ST->LOGICMAN init-INTERP-ST))
                   (NEW-STACK (INTERP-ST->STACK sat-INTERP-ST))
                   (STACK (INTERP-ST->STACK init-INTERP-ST))
                   (new-bvar-db (interp-st->bvar-db sat-interp-st))
                   (env (fgl-env a nil))
                   (env (fix-env-for-bvar-db env new-bvar-db new-logicman))
                   (ans-eval (gobj-bfr-eval ans-interp env new-logicman))
                   (orig-alist (fgl-object-bindings-eval (stack$a-bindings stack) env logicman))
                   (MAJOR-ALIST
                    (FGL-OBJECT-BINDINGS-EVAL (STACK$A-BINDINGS NEW-STACK)
                                           ENV NEW-LOGICMAN))
                   (MINOR-ALIST
                    (FGL-OBJECT-BINDINGS-EVAL (STACK$A-MINOR-BINDINGS STACK)
                                           ENV LOGICMAN))
                   (?EVAL-ALIST (APPEND MINOR-ALIST MAJOR-ALIST)))
                `(:use ((:instance interp-st-sat-check-unsat-implies
                         (params ,(acl2::hq sat-config))
                         (bfr ,(acl2::hq (interp-st-bfr-not ans-interp interp-interp-st)))
                         (interp-st ,(acl2::hq interp-interp-st))
                         (state ,(acl2::hq interp-state))
                         (env ,(acl2::hq env)))
                        (:instance fgl-interp-test-correct
                         (x ,(acl2::hq goal))
                         (interp-st ,(acl2::hq init-interp-st))
                         (env ,(acl2::hq env))
                         (st state)
                         (state ,(acl2::hq init-interp-state)))
                        (:instance iff-forall-extensions-necc
                         (obj ,(acl2::hq ans-eval))
                         (term ,(acl2::hq goal))
                         (eval-alist ,(acl2::hq eval-alist))
                         (ext ,(acl2::hq eval-alist)))
                        (:instance fgl-ev-of-extension-when-term-vars-bound
                         (b ,(acl2::hq eval-alist))
                         (a ,(acl2::hq orig-alist))
                         (x ,(acl2::hq goal))))
                  :in-theory (disable interp-st-sat-check-unsat-implies
                                      fgl-interp-test-correct
                                      iff-forall-extensions-necc
                                      fgl-ev-of-extension-when-term-vars-bound))))

             (:interp-early
              (b* ((NEW-LOGICMAN (INTERP-ST->LOGICMAN early-INTERP-ST))
                   (LOGICMAN (INTERP-ST->LOGICMAN init-INTERP-ST))
                   (NEW-STACK (INTERP-ST->STACK early-INTERP-ST))
                   (STACK (INTERP-ST->STACK init-INTERP-ST))
                   (new-bvar-db (interp-st->bvar-db early-interp-st))
                   (env (fgl-env a nil))
                   (env (fix-env-for-bvar-db env new-bvar-db new-logicman))
                   (ans-eval (gobj-bfr-eval ans-interp env new-logicman))
                   (orig-alist (fgl-object-bindings-eval (stack$a-bindings stack) env logicman))
                   (MAJOR-ALIST
                    (FGL-OBJECT-BINDINGS-EVAL (STACK$A-BINDINGS NEW-STACK)
                                           ENV NEW-LOGICMAN))
                   (MINOR-ALIST
                    (FGL-OBJECT-BINDINGS-EVAL (STACK$A-MINOR-BINDINGS STACK)
                                           ENV LOGICMAN))
                   (?EVAL-ALIST (APPEND MINOR-ALIST MAJOR-ALIST)))
                `(:use ((:instance fgl-interp-test-correct
                         (x ,(acl2::hq goal))
                         (interp-st ,(acl2::hq init-interp-st))
                         (env ,(acl2::hq env))
                         (st state)
                         (state ,(acl2::hq init-interp-state)))
                        (:instance iff-forall-extensions-necc
                         (obj ,(acl2::hq ans-eval))
                         (term ,(acl2::hq goal))
                         (eval-alist ,(acl2::hq eval-alist))
                         (ext ,(acl2::hq eval-alist)))
                        (:instance fgl-ev-of-extension-when-term-vars-bound
                         (b ,(acl2::hq eval-alist))
                         (a ,(acl2::hq orig-alist))
                         (x ,(acl2::hq goal))))
                  :in-theory (disable fgl-interp-test-correct
                                      iff-forall-extensions-necc
                                      fgl-ev-of-extension-when-term-vars-bound))))))))



(define fgl-interp-cp ((clause pseudo-term-listp)
                      hint
                      interp-st
                      state)
  ;; :prepwork ((local (in-theory (disable acl2::member-equal-append))))
  :hooks nil
  :guard-debug t
  (b* (((unless (fgl-config-p hint))
        (mv "Bad hint object -- must satisfy fgl-config-p" nil interp-st state))
       ((unless (fgl-formula-checks-stub state))
        (mv "Failed formula checks! Some assumed definitions needed for primitives are not installed."
            nil interp-st state))
       (config hint)
       (disj (disjoin clause))

       ((mv err interp-st state)
        (fgl-clause-proc-core disj config interp-st state))

       (state (save-interp-st-info-into-state interp-st state)))
    (mv err nil interp-st state))
  ///
  (local (in-theory (disable pseudo-term-listp
                             equal-of-booleans-rewrite
                             not
                             (tau-system))))

  (defthm fgl-interp-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (fgl-ev-meta-extract-global-facts)
                  (fgl-ev (conjoin-clauses
                           (acl2::clauses-result (fgl-interp-cp clause hint interp-st state)))
                          a))
             (fgl-ev (disjoin clause) a))
    :rule-classes :clause-processor))
