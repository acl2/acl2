; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "svtv-stobj")
(include-book "clause-processors/meta-extract-user" :dir :System)
(include-book "clause-processors/pseudo-term-fty" :dir :System)
(include-book "centaur/meta/replace" :dir :System)
(include-book "centaur/meta/unify-strict" :dir :system)
(include-book "centaur/meta/lambda-measure" :dir :system)

;; Uses the contents of a svtv-stobj to prove that a pipeline expresses the
;; correct formula of the cycle.

#||

(include-book
 "svtv-stobj-defsvtv")

(local
 (defconst *my-design*
   (make-design
    :top "my-mod"
    :modalist (list
               (cons "my-mod"
                     (make-module
                      :wires (list (make-wire :name "in"
                                              :width 5
                                              :low-idx 0)
                                   (make-wire :name "out"
                                              :width 5
                                              :low-idx 0))
                      :assigns (list (cons
                                      (list (make-lhrange
                                             :w 5
                                             :atom
                                             (make-lhatom-var
                                              :name "out"
                                              :rsh 0)))
                                      (make-driver
                                       :value (svcall bitnot
                                                      (svcall zerox 5 "in")))))))))))

(defsvtv$-phasewise my-svtv
   :design *my-design*
   :phases
   ((:label the-phase
     :inputs (("in" in))
     :outputs (("out" out)))
    (:label the-next-phase
     :inputs (("in" in2))
     :outputs (("out" out2)))))

(def-pipeline-thm my-svtv)

;; (make-event
;;  `(defund my-cycle ()
;;     (declare (xargs :guard t))
;;     ',(svtv-data->cycle-fsm svtv-data)))

;; (make-event
;;  `(defund my-namemap ()
;;     (declare (xargs :guard t))
;;     ',(svtv-data->namemap svtv-data)))

;; (make-event
;;  `(defund my-pipeline-setup ()
;;     (declare (xargs :guard t))
;;     ',(svtv-data->pipeline-setup svtv-data)))

;; (local (in-theory (disable (my-cycle)
;;                            (my-namemap)
;;                            (my-pipeline-setup))))

;; (defthm my-svtv-pipeline-correct
;;   (b* ((fsm (my-cycle))
;;        (rename-fsm (make-svtv-fsm :base-fsm fsm
;;                                   :namemap (my-namemap)))
;;        (renamed-fsm (svtv-fsm->renamed-fsm rename-fsm))       
;;        ((pipeline-setup pipe) (my-pipeline-setup))
;;        (outvars (svtv-probealist-outvars pipe.probes))
;;        (run (base-fsm-run
;;              (svex-alistlist-eval
;;               (svtv-fsm-run-input-substs
;;                (take (len outvars) pipe.inputs)
;;                pipe.overrides
;;                rename-fsm)
;;               env)
;;              (svex-alist-eval pipe.initst env)
;;              renamed-fsm outvars)))
;;     (svex-envs-equivalent
;;      (svex-alist-eval (svtv->outexprs (my-svtv)) env)
;;      (svtv-probealist-extract pipe.probes run)))
;;   :hints (("goal" :clause-processor (svtv-pipeline-clause-proc
;;                                      clause
;;                                      '((my-cycle)
;;                                        (my-namemap)
;;                                        (my-pipeline-setup)
;;                                        (svtv->outexprs$inline (my-svtv))
;;                                        env)
;;                                      svtv-data state)
;;            :in-theory (enable svtv-pipeline-correct))))
       



||#


(define svtv-pipeline-correct ((cycle-fsm base-fsm-p)
                               (namemap svtv-name-lhs-map-p)
                               (pipeline-setup pipeline-setup-p)
                               (pipeline-result svex-alist-p)
                               (env svex-env-p))
  :verify-guards nil
  :enabled t
  (b* ((fsm cycle-fsm)
       (rename-fsm (make-svtv-fsm :base-fsm fsm
                                  :namemap namemap))
       (renamed-fsm (svtv-fsm->renamed-fsm rename-fsm))
       ((pipeline-setup pipe) pipeline-setup)
       (outvars (svtv-probealist-outvars pipe.probes))
       (run (base-fsm-run
             (svex-alistlist-eval
              (svtv-fsm-run-input-substs
               (take (len outvars) pipe.inputs)
               pipe.overrides
               rename-fsm)
              env)
             (svex-alist-eval pipe.initst env)
             renamed-fsm
             outvars)))
    (svex-envs-equivalent
     (svex-alist-eval pipeline-result env)
     (svtv-probealist-extract pipe.probes run)))
  ///
  (local (defthm take-of-svex-alistlist-eval
           (equal (take n (svex-alistlist-eval x env))
                  (svex-alistlist-eval (take n x) env))
           :hints(("Goal" :in-theory (e/d (svex-alistlist-eval take)
                                          (acl2::take-when-atom
                                           acl2::take-of-too-many))
                   :induct t
                   :expand ((svex-alist-eval nil env))))))

  (defthm svtv-pipeline-correct-when-svtv-data$ap
    (implies (and (svtv-datap svtv-data)
                  (svtv-data->pipeline-validp svtv-data))
             (svtv-pipeline-correct (svtv-data$c->cycle-fsm svtv-data)
                                    (svtv-data$c->namemap svtv-data)
                                    (svtv-data$c->pipeline-setup svtv-data)
                                    (svtv-data$c->pipeline svtv-data)
                                    env))
    :hints(("Goal" :in-theory (enable svtv-data$ap
                                      svtv-fsm-run-is-base-fsm-run)))))

(local (in-theory (disable svtv-pipeline-correct)))



(defevaluator svtvpipe-ev svtvpipe-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)

   ;; (svtv-data$c-pipeline-okp svtvdat results)
   ;; (svtv-data$c->cycle-fsm$inline svtvdat)
   ;; (svtv-data$c->pipeline-setup$inline svtvdat)
   ;; (svtv-data$c->namemap$inline svtvdat)
   (svtv-pipeline-correct cycle namemap setup pipeline env)
   )
  :namedp t)

(local (acl2::def-ev-pseudo-term-fty-support svtvpipe-ev svtvpipe-ev-lst))
(acl2::def-meta-extract svtvpipe-ev svtvpipe-ev-lst)

(local (in-theory (disable w)))

(local (acl2::def-functional-instance svtvpipe-ev-when-agree-on-term-vars
         cmr::base-ev-when-agree-on-term-vars
         ((cmr::base-ev svtvpipe-ev)
          (cmr::base-ev-list svtvpipe-ev-lst))))

(local (in-theory (disable svtvpipe-ev-when-agree-on-term-vars)))

(local (defthmd svtvpipe-ev-when-no-term-vars
         (implies (and (syntaxp (not (equal a ''nil)))
                       (not (cmr::term-vars x)))
                  (equal (svtvpipe-ev x a)
                         (svtvpipe-ev x nil)))
         :hints (("goal" :use ((:instance svtvpipe-ev-when-agree-on-term-vars
                                (a a)
                                (b nil)))
                  :in-theory (enable acl2::eval-alists-agree)))))

(define meta-extract-const-value ((term pseudo-termp) state)
  :returns (mv err val)
  (b* ((term (acl2::pseudo-term-fix term))
       ((unless (eq (cmr::term-vars term) nil))
        (mv "term has variables" nil))
       ((unless (logic-fnsp term (w state)))
        (mv "term has non-logic functions" nil)))
    (acl2::magic-ev term nil state t nil))

  ;; (acl2::pseudo-term-case term
  ;;   :const (mv nil term.val)
  ;;   :fncall (b* (((unless (eq term.args nil))
  ;;                 (mv "fncall has arguments" nil))
  ;;                ((mv ok formals body) (acl2::fn-get-def-w term.fn wrld))
  ;;                ((unless (and ok
  ;;                              (not formals)
  ;;                              (pseudo-termp body)
  ;;                              (acl2::pseudo-term-case body :const)))
  ;;                 (mv (msg "function ~x0 not recognized as a constant" term.fn) nil)))
  ;;             (mv nil (acl2::pseudo-term-const->val body)))
  ;;   :otherwise (mv (msg "bad form for constant term: ~x0" term) nil))
  ///
  (defret <fn>-correct
    (implies (and (not err)
                  (svtvpipe-ev-meta-extract-global-facts))
             (equal (svtvpipe-ev term a) val))
    :hints(("Goal" :in-theory (enable svtvpipe-ev-when-no-term-vars)))))

;; (local
;;  #!cmr
;;  (defthm term-unify-strict-reversible-hyp
;;    (implies (acl2::rewriting-negative-literal
;;              `(mv-nth '0 (term-unify-strict ,pat ,x ,alist)))
;;             (iff (mv-nth 0 (term-unify-strict pat x alist))
;;                  (equal (term-subst-strict pat (mv-nth 1 (term-unify-strict pat x alist)))
;;                         (pseudo-term-fix x))))))

;; (local (in-theory (disable cmr::term-unify-strict-reversible-iff)))




;; (define pipeline-okp-implicant-term ((wrld plist-worldp))
;;   :returns (mv err (impl-term pseudo-termp))
;;   ;; :verify-guards nil
;;   (b* ((form (acl2::meta-extract-formula-w 'svtv-data$c-pipeline-okp wrld))
;;        ((unless (pseudo-termp form))
;;         (mv "pipeline-okp formula was not pseudo-termp" nil))
;;        ;; Form is the conjunction of formulas for the defun-sk, namely
;;        ;;   definition of pipeline-okp
;;        ;;   pipeline-okp-necc theorem
;;        ;; The second is the one we want.
;;        ((mv ok alist)
;;         (cmr::term-unify-strict
;;          '(if pipe-ok-def (implies (svtv-data$c-pipeline-okp svtv-data$c results)
;;                                    impl-term)
;;             'nil)
;;          form
;;          '((svtv-data$c . svtv-data$c)
;;            (results . results))))
;;        ((unless ok)
;;         (mv "pipeline-okp formula had unexpected form" nil)))
;;     (mv nil (cdr (hons-assoc-equal 'impl-term alist))))
;;   ///
;;   (set-ignore-ok t)
;;   (local
;;    (make-event
;;     (let ((form
;;            `(progn
;;               (defthm expand-term-subst-strict
;;                 (implies (syntaxp (quotep x))
;;                          (equal (cmr::term-subst-strict x acl2::a)
;;                                 ,(acl2::body 'cmr::term-subst-strict nil (w state))))
;;                 :hints(("Goal" :in-theory (enable cmr::term-subst-strict))))
;;               (defthm expand-termlist-subst-strict
;;                 (implies (syntaxp (quotep x))
;;                          (equal (cmr::termlist-subst-strict x acl2::a)
;;                                 ,(acl2::body 'cmr::termlist-subst-strict nil (w state))))
;;                 :hints(("Goal" :in-theory (enable cmr::termlist-subst-strict)))))))
;;       (value form))))

;;   (local (defthmd equal-cons-strong
;;            (implies (syntaxp (not (or (quotep x)
;;                                       (and (quotep a) (quotep b)))))
;;                     (equal (Equal x (cons a b))
;;                            (and (consp x)
;;                                 (equal (car x) a)
;;                                 (equal (cdr x) b))))))

;;   (local (defthm assoc-is-hons-assoc-equal-when-key
;;            (implies k
;;                     (equal (assoc-equal k x)
;;                            (hons-assoc-equal k x)))))

;;   (defret <fn>-correct
;;     (implies (and (not err)
;;                   (svtvpipe-ev-meta-extract-global-facts)
;;                   (equal wrld (w state))
;;                   (svtv-data$c-pipeline-okp
;;                    (cdr (hons-assoc-equal 'svtv-data$c alist))
;;                    (cdr (hons-assoc-equal 'results alist))))
;;              (svtvpipe-ev impl-term alist))
;;     :hints(("Goal"
;;             :use ((:instance SVTVPIPE-EV-META-EXTRACT-FORMULA
;;                    (st state) (name 'svtv-data$c-pipeline-okp) (a alist)))
;;             :in-theory (e/d (cmr::equal-of-pseudo-term-fncall
;;                                equal-cons-strong)
;;                             (SVTVPIPE-EV-META-EXTRACT-FORMULA))
;;             :do-not-induct t))))

;; (acl2::def-functional-instance svtvpipe-ev-of-lazy-beta-reduce
;;   cmr::base-ev-of-lazy-beta-reduce
;;   ((cmr::base-ev svtvpipe-ev)
;;    (cmr::base-ev-list svtvpipe-ev-lst)))

(local (defthm pseudo-termp-nth-when-pseudo-term-listp
         (implies (pseudo-term-listp x)
                  (pseudo-termp (nth n x)))))

;; (define svtvpipe-ev-pseudo-term-mapping-correct-p ((map cmr::pseudo-term-mapping-p) (env alistp))
;;   (b* (((when (atom map)) t)
;;        ((unless (mbt (and (consp (car map))
;;                           (pseudo-termp (caar map)))))
;;         (svtvpipe-ev-pseudo-term-mapping-correct-p (cdr map) env)))
;;     (and (equal (svtvpipe-ev (caar map) env)
;;                 (svtvpipe-ev (cdar map) env))
;;          (svtvpipe-ev-pseudo-term-mapping-correct-p (cdr map) env))))

;; (acl2::def-functional-instance svtvpipe-ev-term-replace-correct
;;   cmr::term-replace-correct
;;   ((cmr::base-ev svtvpipe-ev)
;;    (cmr::base-ev-list svtvpipe-ev-lst)
;;    (cmr::base-ev-pseudo-term-mapping-correct-p
;;     svtvpipe-ev-pseudo-term-mapping-correct-p))
;;   :hints(("Goal" :in-theory (enable svtvpipe-ev-pseudo-term-mapping-correct-p))))


(define pipeline-okp-hint-subst ((hints pseudo-term-listp)
                                 svtv-data
                                 state)
  :returns (mv err (subst cmr::pseudo-term-mapping-p))
  :prepwork ((local (in-theory (disable nth))))
  (b* (((acl2::nths cycle-term namemap-term pipeline-setup-term pipeline-term) hints)
       ((mv cycle-term-err cycle-val)
        (meta-extract-const-value cycle-term state))
       ((when (or cycle-term-err
                  (not (equal cycle-val (svtv-data->cycle-fsm svtv-data)))))
        (mv "bad cycle value" nil))
       ((mv namemap-term-err namemap-val)
        (meta-extract-const-value namemap-term state))
       ((when (or namemap-term-err
                  (not (equal namemap-val (svtv-data->namemap svtv-data)))))
        (mv "bad namemap value" nil))
       ((mv pipeline-setup-term-err pipeline-setup-val)
        (meta-extract-const-value pipeline-setup-term state))
       ((when (or pipeline-setup-term-err
                  (not (equal pipeline-setup-val (svtv-data->pipeline-setup svtv-data)))))
        (mv "bad pipeline-setup value" nil))
       ((mv pipeline-term-err pipeline-val)
        (meta-extract-const-value pipeline-term state))
       ((when (or pipeline-term-err
                  (not (equal pipeline-val (svtv-data->pipeline svtv-data)))))
        (mv "bad pipeline value" nil)))
    (mv nil
        `(((svtv-data$c->cycle-fsm$inline svtv-data$c) . ,(acl2::pseudo-term-fix cycle-term))
          ((svtv-data$c->namemap$inline svtv-data$c) . ,(acl2::pseudo-term-fix namemap-term))
          ((svtv-data$c->pipeline-setup$inline svtv-data$c) . ,(acl2::pseudo-term-fix pipeline-setup-term))
          (results . ,(acl2::pseudo-term-fix pipeline-term)))))
  ///
  ;; (defret <fn>-correct
  ;;   (implies (and (not err)
  ;;                 (svtvpipe-ev-meta-extract-global-facts)
  ;;                 (equal (cdr (assoc-equal 'svtv-data$c env)) svtv-data)
  ;;                 (equal (cdr (assoc-equal 'results env)) (svtv-data->pipeline svtv-data)))
  ;;            (svtvpipe-ev-pseudo-term-mapping-correct-p subst env))
  ;;   :hints(("Goal" :in-theory (enable svtvpipe-ev-pseudo-term-mapping-correct-p))))
  )




(local (acl2::def-functional-instance svtvpipe-ev-when-agree-on-term-vars
         cmr::base-ev-when-agree-on-term-vars
         ((cmr::base-ev svtvpipe-ev)
          (cmr::base-ev-list svtvpipe-ev-lst))))

(local (in-theory (disable svtvpipe-ev-when-agree-on-term-vars)))

(local (defthm eval-alists-agree-of-cons-non-member
         (implies (not (member v lst))
                  (acl2::eval-alists-agree lst (cons (cons v val) a) a))
         :hints(("Goal" :in-theory (enable acl2::eval-alists-agree)))))

(defthm svtvpipe-ev-remove-unused-var
  (implies (not (member v (cmr::term-vars x)))
           (equal (svtvpipe-ev x (cons (cons v val) a))
                  (svtvpipe-ev x a)))
  :hints (("goal" :use ((:instance svtvpipe-ev-when-agree-on-term-vars
                         (b a) (a (cons (cons v val) a)))))))



(define svtv-pipeline-clause-proc (clause hints svtv-data state)
  ;; hints are: (cycle-term namemap-term pipeline-setup-term pipeline-term env-term)
  (b* (((unless (mbt (svtv-datap svtv-data)))
        (mv "impossible" nil))
       ((unless (svtv-data->pipeline-validp svtv-data))
        (mv "svtv-data pipeline not valid" nil))
       ((unless (and (pseudo-term-listp hints)
                     (eql (len hints) 5)))
        (mv "bad hints" nil))
       ((mv hints-err ?subst) (pipeline-okp-hint-subst hints svtv-data state))
       ((when hints-err)
        (mv hints-err nil))
       ((acl2::nths cycle-term namemap-term pipeline-setup-term pipeline-term env) hints)
       ;; ((mv impl-err impl-term) (pipeline-okp-implicant-term (w state)))
       ;; ((when impl-err)
       ;;  (mv impl-err nil))
       ;; (impl-term-beta (cmr::lazy-beta-reduce impl-term))
       ;; (impl-term-subst (cmr::term-replace impl-term-beta subst))
       ;; ((when (cmr::member-term-vars 'results impl-term-subst))
       ;;  (mv "programming error: result was in added term" nil))
       ;; ((when (cmr::member-term-vars 'svtv-data$c impl-term-subst))
       ;;  (mv "svtv-data$c was still free in term, check def of svtv-data$c-pipeline-okp" nil))
       )
    ;; (mv nil (list (cons `(not ,impl-term-subst) clause)))
    (mv nil (list (cons `(not (svtv-pipeline-correct ,cycle-term ,namemap-term ,pipeline-setup-term ,pipeline-term ,env)) clause))))
  ///
  (defthm svtv-pipeline-clause-proc-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (svtvpipe-ev-meta-extract-global-facts)
                  (svtvpipe-ev (acl2::conjoin-clauses
                                (acl2::clauses-result (svtv-pipeline-clause-proc
                                                       clause hints svtv-data state)))
                               ;; `((svtv-data$c . ,svtv-data)
                               ;;   (results . ,(svtv-data->pipeline svtv-data)))
                               a))
             (svtvpipe-ev (disjoin clause) a))
    :hints (("goal" :do-not-induct t 
             :in-theory (e/d (pipeline-okp-hint-subst)
                             (nth))
             ;; :use ((:instance svtvpipe-ev-term-replace-correct
             ;;        (x (CMR::LAZY-BETA-REDUCE (MV-NTH 1
             ;;                        (PIPELINE-OKP-IMPLICANT-TERM (W STATE)))))
             ;;        (map (MV-NTH 1
             ;;                     (PIPELINE-OKP-HINT-SUBST HINTS SVTV-DATA state)))
             ;;        (env
             ;;         `((svtv-data$c . ,svtv-data)
             ;;           (results . ,(svtv-data->pipeline svtv-data))
             ;;           . ,a))))
             ))

    :rule-classes :clause-processor))



(defun def-pipeline-thm-fn (svtv-name
                            cycle-name
                            define-cycle
                            stobj-name)
  (declare (xargs :mode :program))
  (b* ((define-cycle (or (not cycle-name) define-cycle))
       (cycle-name (or cycle-name
                       (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name svtv-name) "-CYCLE")
                        svtv-name)))
       (cycle-events (and define-cycle
                          `((make-event
                             `(define ,',cycle-name ()
                                :no-function t
                                :returns (fsm base-fsm-p)
                                ',(svtv-data->cycle-fsm ,stobj-name))))))
       (namemap-name (intern-in-package-of-symbol
                      (concatenate 'string (symbol-name svtv-name) "-NAMEMAP")
                      svtv-name))
       (pipeline-setup-name (intern-in-package-of-symbol
                             (concatenate 'string (symbol-name svtv-name) "-PIPELINE-SETUP")
                             svtv-name))
       (thmname (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name svtv-name) "-PIPELINE-CORRECT")
                 svtv-name)))
  `(progn ,@cycle-events
          (make-event
           `(define ,',namemap-name ()
              :no-function t
              :returns (namemap svtv-name-lhs-map-p)
              ',(svtv-data->namemap ,stobj-name)))
          (make-event
           `(define ,',pipeline-setup-name ()
              :no-function t
              :returns (setup pipeline-setup-p)
              ',(svtv-data->pipeline-setup ,stobj-name)))
          (in-theory (disable ,@(and define-cycle `((,cycle-name)))))
          (defthmd ,thmname
            (b* ((fsm (,cycle-name))
                 (rename-fsm (make-svtv-fsm :base-fsm fsm
                                            :namemap (,namemap-name)))
                 (renamed-fsm (svtv-fsm->renamed-fsm rename-fsm))
                 ((pipeline-setup pipe) (,pipeline-setup-name))
                 (outvars  (svtv-probealist-outvars pipe.probes))
                 (run (base-fsm-run
                       (svex-alistlist-eval
                        (svtv-fsm-run-input-substs
                         (take (len outvars) pipe.inputs)
                         pipe.overrides
                         rename-fsm)
                        env)
                       (svex-alist-eval pipe.initst env)
                       renamed-fsm
                       outvars)))
              (svex-envs-equivalent
               (svex-alist-eval (svtv->outexprs (,svtv-name)) env)
               (svtv-probealist-extract pipe.probes run)))
            :hints (("goal" :clause-processor (svtv-pipeline-clause-proc
                                               clause
                                               '((,cycle-name)
                                                 (,namemap-name)
                                                 (,pipeline-setup-name)
                                                 (svtv->outexprs$inline (,svtv-name))
                                                 env)
                                               ,stobj-name state)
                     :in-theory (enable svtv-pipeline-correct))))
          (add-to-ruleset! svtv-pipeline-thms ,thmname)
          (add-to-ruleset! svtv-pipeline-thm-constants '((:executable-counterpart ,namemap-name)
                                                         (:executable-counterpart ,pipeline-setup-name))))))

(defmacro def-pipeline-thm (svtv-name
                            &key
                            cycle-name
                            define-cycle
                            (stobj-name 'svtv-data))
  (def-pipeline-thm-fn svtv-name cycle-name define-cycle stobj-name))


(defxdoc def-pipeline-thm
  :parents (svex-stvs svtv-data)
  :short "Prove that an SVTV pipeline is an unrolling of the FSM that it's based on"
  :long "<p>When computing an SVTV pipeline using @(see defsvtv$) or @(see
defsvtv$-phasewise), a FSM is first created and the pipeline is then a
composition (unrolling) of FSM phases.  This is an invariant of the @(see
svtv-data) stobj; if the @('pipeline-valid') bit of the @('svtv-data') stobj is
set, then it is known that the @('pipeline') field is an unrolling of the
@('cycle-fsm') field, with unrolling parameters specified in the
@('pipeline-setup') field.</p>

<p>The @('def-pipeline-thm') event uses this invariant of the @('svtv-data')
stobj to prove that property, given an SVTV that was created using
@('defsvtv$').  This event requires that the @('svtv-data') stobj was not
changed since the creation of the @('defsvtv$'). It proves a theorem of the
following form:</p>

@({
   (b* ((fsm (svtv-cycle))
        (rename-fsm (make-svtv-fsm :base-fsm fsm
                                   :namemap (svtv-namemap)))
        (renamed-fsm (svtv-fsm->renamed-fsm rename-fsm))
        ((pipeline-setup pipe) (svtv-pipeline-setup))
        (outvars  (svtv-probealist-outvars pipe.probes))
        (run (base-fsm-run
              (svex-alistlist-eval
               (svtv-fsm-run-input-substs
                (take (len outvars) pipe.inputs)
                pipe.overrides
                rename-fsm)
               env)
              (svex-alist-eval pipe.initst env)
              renamed-fsm
              outvars)))
     (svex-envs-equivalent
      (svex-alist-eval (svtv->outexprs (svtv)) env)
      (svtv-probealist-extract pipe.probes run)))
 })

<p>Here @('(svtv)') is the SVTV created by @('defsvtv$'). The other constant
functions @('(svtv-cycle)'), @('(svtv-namemap)'), and
@('(svtv-pipeline-setup)') are introduced by the @('def-pipeline-thm')
event. (The cycle function doesn't need to be created if a previous
@('def-pipeline-thm') event already introduced it.)</p>

<p>The options for @('def-pipeline-thm') are as follows:</p>

@({
 (def-pipeline-thm svtv-name
                   ;; optional, in case cycle was introduced previously
                   :cycle-name cycle-name)
 })

")
