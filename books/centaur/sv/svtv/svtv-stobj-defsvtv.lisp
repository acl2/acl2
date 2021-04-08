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

(include-book "svtv-stobj-pipeline")
(include-book "svtv-stobj-defcycle")
(include-book "process")
(include-book "centaur/misc/hons-remove-dups" :dir :System)
(include-book "preprocess")

(local (defthm svar-p-when-stringp
         (implies (stringp x)
                  (svar-p x))
         :hints(("Goal" :in-theory (enable svar-p)))))



(define defsvtv-compute-user-namemap ((ins true-list-listp)
                                      (overrides true-list-listp)
                                      (outs true-list-listp))
  :prepwork ((local (defthm svarlist-p-when-string-listp
                      (implies (string-listp x)
                               (svarlist-p x))
                      :hints(("Goal" :in-theory (enable svarlist-p)))))
             (local (defthm svtv-namemap-p-of-pairlis
                      (implies (and (string-listp y)
                                    (svarlist-p x)
                                    (equal (len x) (len y)))
                               (svtv-namemap-p (pairlis$ x y)))
                      :hints(("Goal" :in-theory (enable svtv-namemap-p pairlis$)))))
             (local (defthm string-listp-of-remove-dups
                      (implies (string-listp x)
                               (string-listp (remove-duplicates-equal x)))
                      :hints(("Goal" :in-theory (enable remove-duplicates-equal))))))
  :returns (user-names svtv-namemap-p)
  (b* ((strings (acl2::hons-remove-dups
                 (ec-call
                  (str::string-list-fix (append (strip-cars (alist-fix ins))
                                                (strip-cars (alist-fix overrides))
                                                (strip-cars (alist-fix outs))))))))
    (pairlis$ strings strings)))


(define defsvtv-probes-for-phases ((phase natp) (phases true-listp) (signal svar-p))
  :returns (probes svtv-probealist-p)
  (b* (((when (atom phases)) nil)
       (ent (car phases))
       ((when (svtv-dontcare-p ent))
        (defsvtv-probes-for-phases (1+ (lnfix phase)) (cdr phases) signal))
       ((unless (svar-p ent))
        (raise "Bad output entry: ~x0~%" ent)
        (defsvtv-probes-for-phases (1+ (lnfix phase)) (cdr phases) signal)))
    (cons (cons ent (make-svtv-probe :signal signal :time phase))
          (defsvtv-probes-for-phases (1+ (lnfix phase)) (cdr phases) signal))))

(define defsvtv-compute-probes ((outs true-list-listp))
  :returns (probes svtv-probealist-p)
  (if (atom outs)
      nil
    (if (atom (car outs))
        (defsvtv-compute-probes (cdr outs))
      (append (defsvtv-probes-for-phases 0 (cdar outs) (str-fix (caar outs)))
              (defsvtv-compute-probes (cdr outs))))))


(define phase-compute-input-alist ((phase natp) (ins true-list-listp))
  :returns (alist svex-alist-p)
  (b* (((when (atom ins)) nil)
       ((unless (consp (car ins)))
        (phase-compute-input-alist phase (cdr ins)))
       (signal (str-fix (caar ins)))
       (ent (nth phase (cdar ins)))
       ((when (svtv-dontcare-p ent))
        (phase-compute-input-alist phase (cdr ins)))
       ((unless (svtv-baseentry-p ent))
        (if (svtv-entry-p ent)
            (raise "SVTV entries such as ~x0 are only allowed in overrides." ent)
          (raise "Bad SVTV entry: ~x0." ent))
        (phase-compute-input-alist phase (cdr ins)))
       (val (svtv-baseentry-svex ent)))
    (cons (cons signal val)
          (phase-compute-input-alist phase (cdr ins)))))

(define phase-compute-override-val-alist ((phase natp) (overrides true-list-listp))
  :returns (alist svex-alist-p)
  :prepwork ((local (in-theory (enable svtv-entry-p))))
  (b* (((when (atom overrides)) nil)
       ((unless (consp (car overrides)))
        (phase-compute-override-val-alist phase (cdr overrides)))
       (signal (str-fix (caar overrides)))
       (ent (nth phase (cdar overrides)))
       ((unless (svtv-entry-p ent))
        (raise "Bad SVTV entry: ~x0." ent)
        (phase-compute-override-val-alist phase (cdr overrides)))
       ((when (svtv-dontcare-p ent))
        (phase-compute-override-val-alist phase (cdr overrides)))
       (val (if (svtv-condoverride-p ent)
                (b* (((svtv-condoverride ent)))
                  (svtv-baseentry-svex ent.value))
              (svtv-baseentry-svex ent))))
    (cons (cons signal val)
          (phase-compute-override-val-alist phase (cdr overrides)))))


(define phase-compute-override-test-alist ((phase natp) (overrides true-list-listp))
  :returns (alist svex-alist-p)
  :prepwork ((local (in-theory (enable svtv-entry-p))))
  (b* (((when (atom overrides)) nil)
       ((unless (consp (car overrides)))
        (phase-compute-override-test-alist phase (cdr overrides)))
       (signal (str-fix (caar overrides)))
       (ent (nth phase (cdar overrides)))
       ((unless (svtv-entry-p ent))
        (raise "Bad SVTV entry: ~x0." ent)
        (phase-compute-override-val-alist phase (cdr overrides)))
       ((when (svtv-dontcare-p ent))
        (phase-compute-override-test-alist phase (cdr overrides)))
       (test (if (svtv-condoverride-p ent)
                (b* (((svtv-condoverride ent)))
                  (svtv-baseentry-svex ent.test))
               (svex-quote -1))))
    (cons (cons signal test)
          (phase-compute-override-test-alist phase (cdr overrides)))))
    
(define svtv-compute-input-phases ((phase natp) (nphases natp)
                                   (ins true-list-listp)
                                   (overrides true-list-listp))
  :guard (<= phase nphases)
  :measure (nfix (- (nfix nphases) (nfix phase)))
  :returns (inputs svex-alistlist-p)
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql phase nphases)))
        nil)
       (inputs (phase-compute-input-alist phase ins))
       (override-vals (phase-compute-override-val-alist phase overrides)))
    (cons (append inputs override-vals)
          (svtv-compute-input-phases (1+ (lnfix phase)) nphases ins overrides))))

(define svtv-compute-override-test-phases ((phase natp) (nphases natp)
                                   (overrides true-list-listp))
  :guard (<= phase nphases)
  :measure (nfix (- (nfix nphases) (nfix phase)))
  :returns (override-tests svex-alistlist-p)
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql phase nphases)))
        nil)
       (override-tests (phase-compute-override-test-alist phase overrides)))
    (cons override-tests
          (svtv-compute-override-test-phases (1+ (lnfix phase)) nphases overrides))))

(define svtv-lines-max-length ((x true-list-listp))
  :returns (max-len natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (if (consp (car x))
        (max (len (cdar x))
             (svtv-lines-max-length (cdr x)))
      (svtv-lines-max-length (cdr x)))))


(define defsvtv-compute-inputs ((ins true-list-listp)
                                (overrides true-list-listp))
  :returns (mv (nphases natp :rule-classes :type-prescription)
               (inputs svex-alistlist-p)
               (override-tests svex-alistlist-p))
  (b* ((nphases (max (svtv-lines-max-length ins) (svtv-lines-max-length overrides))))
    (mv nphases
        (svtv-compute-input-phases 0 nphases ins overrideS)
        (svtv-compute-override-test-phases 0 nphases overrides))))
       

(define svex-x-subst ((vars svarlist-p))
  :returns (subst svex-alist-p)
  (pairlis$ (svarlist-fix vars)
            (make-list (len vars) :initial-element (svex-x)))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys subst)
           (svarlist-fix vars))))

(define user-svtv-lines-to-svtv-lines ((lines true-list-listp)
                                       (namemap svtv-name-lhs-map-p))
  :returns (entries svtv-lines-p)
  (b* (((when (atom lines)) nil)
       ((unless (consp (car lines)))
        (user-svtv-lines-to-svtv-lines (cdr lines) namemap))
       ((cons name entrylist) (car lines))
       ((unless (svtv-entrylist-p entrylist))
        (raise "bad entrylist: ~x0~%" (car lines))
        (user-svtv-lines-to-svtv-lines (cdr lines) namemap)))
    (cons (make-svtv-line :lhs (cdr (hons-assoc-equal (str-fix name) namemap))
                          :entries entrylist)
          (user-svtv-lines-to-svtv-lines (cdr lines) namemap))))
              
      
(local (defthm true-list-listp-of-append
         (implies (and (true-list-listp x)
                       (true-list-listp y))
                  (true-list-listp (append x y)))))

(define svtv-lines-expand ((lines true-list-listp)
                           (nphases natp)
                           (namemap svtv-name-lhs-map-p))
  :returns (new-lines true-list-listp)
  (b* (((when (atom lines)) nil)
       ((unless (consp (car lines)))
        (svtv-lines-expand (cdr lines) nphases namemap))
       ((cons name entrylist) (car lines))
       ((unless (svtv-entrylist-p entrylist))
        (raise "bad entrylist: ~x0~%" (car lines))
        (svtv-lines-expand (cdr lines) nphases namemap))
       (lhs (cdr (hons-assoc-equal (str-fix name) namemap)))
       (width (lhs-width lhs))
       (ext-entrylist (svtv-extend-entrylist entrylist nphases 'acl2::_ 'acl2::_ width)))
    (cons (cons name ext-entrylist)
          (svtv-lines-expand (cdr lines) nphases namemap))))
    



(define svtv-compute-trivial-cycle ((pre-simplify booleanp) svtv-data
                                    (simp svex-simpconfig-p))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (not (svtv-data->cycle-fsm-validp svtv-data))
              (not (svtv-data->pipeline-validp svtv-data)))
  :returns (new-svtv-data)
  (b* ((cycle-phases (list (make-svtv-cyclephase :constants nil
                                                 :inputs-free t
                                                 :outputs-captured t)))
       (svtv-data (update-svtv-data->cycle-phases cycle-phases svtv-data))
       (svtv-data (svtv-data-compute-cycle-fsm svtv-data simp))

       (svtv-data (svtv-data-maybe-rewrite-cycle-fsm pre-simplify svtv-data :verbosep t)))
    svtv-data)
  ///
  
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :cycle-phases))
                  (not (equal key :cycle-fsm))
                  (not (equal key :cycle-fsm-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret cycle-fsm-validp-of-<fn>
    (svtv-data$c->cycle-fsm-validp new-svtv-data)))


(define defsvtv-compute-pipeline-setup ((outs+ true-list-listp)
                                            (ins true-list-listp)
                                            (overrides true-list-listp)
                                            (initial-state-vars)
                                            (statevars svarlist-p)
                                            (namemap svtv-name-lhs-map-p))
  :returns (setup pipeline-setup-p)
  (b* ((probes (defsvtv-compute-probes outs+))
       (nphases (svtv-lines-max-length outs+))
       (ins (svtv-lines-expand ins nphases namemap))
       (overrides (svtv-lines-expand overrides nphases namemap))
       ((mv ?in-nphases inputs override-tests) (defsvtv-compute-inputs ins overrides))
       (initst
        (make-fast-alist
         (if initial-state-vars
             (svex-identity-subst statevars)
           (svex-x-subst statevars)))))
    (make-pipeline-setup :probes probes
                         :inputs inputs
                         :overrides override-tests
                         :initst initst))
  ///
  (defret initst-keys-of-<fn>
    (equal (svex-alist-keys (pipeline-setup->initst setup))
           (svarlist-fix statevars) )))
  
(define defsvtv-compute-pipeline ((outs+ true-list-listp)
                                  (ins true-list-listp)
                                  (overrides true-list-listp)
                                  (simplify booleanp)
                                  (pipe-simp svex-simpconfig-p)
                                  (initial-state-vars)
                                  svtv-data)
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->cycle-fsm-validp svtv-data))
  (b* ((namemap (svtv-data->namemap svtv-data))
       (fsm (svtv-data->cycle-fsm svtv-data))
       (statevars (svex-alist-keys (base-fsm->nextstate fsm)))
       (setup (defsvtv-compute-pipeline-setup
                outs+ ins overrides initial-state-vars statevars namemap))
       (svtv-data (svtv-data-maybe-compute-pipeline setup svtv-data :simp pipe-simp))
       (svtv-data (svtv-data-maybe-rewrite-pipeline simplify svtv-data)))
    svtv-data))





(defprod defsvtv-args
  ((name symbolp)
   (inputs true-list-listp)
   (overrides true-list-listp)
   (outputs true-list-listp)
   (internals true-list-listp)
   (design design-p)
   (design-const symbolp)
   labels
   (simplify booleanp)
   (pre-simplify booleanp)
   (pipe-simp svex-simpconfig-p)
   (cycle-phases svtv-cyclephaselist-p)
   (cycle-phases-p)
   (cycle-simp svex-simpconfig-p)
   ;; state-machine
   (initial-state-vars booleanp)
   ;; keep-final-state
   ;; keep-all-states
   define-macros
   parents
   short
   long)
  :layout :list)


(define svtv-data-to-svtv ((x defsvtv-args-p)
                           svtv-data)
  :returns (svtv svtv-p)
  (b* ((namemap (svtv-data->namemap svtv-data))
       ((defsvtv-args x))
       (outs+ (append x.internals x.outputs))
       (nphases (svtv-lines-max-length outs+))
       (exp-ins (svtv-lines-expand x.inputs nphases namemap))
       (exp-overrides (svtv-lines-expand x.overrides nphases namemap))
       (expanded-ins (user-svtv-lines-to-svtv-lines exp-ins namemap))
       (expanded-overrides (user-svtv-lines-to-svtv-lines exp-overrides namemap))
       (expanded-outs (user-svtv-lines-to-svtv-lines outs+ namemap)))
    
    (make-svtv :name x.name
               :outexprs (svtv-data->pipeline svtv-data)
               :inmasks
               (append (fast-alist-free (fast-alist-clean (svtv-collect-masks
                                                           expanded-ins)))
                       (fast-alist-free (fast-alist-clean (svtv-collect-masks
                                                           expanded-overrides))))
               :outmasks 
               (fast-alist-free (fast-alist-clean (svtv-collect-masks
                                                   expanded-outs)))
               :orig-ins x.inputs
               :orig-overrides x.overrides
               :orig-outs x.outputs
               :orig-internals x.internals
               :expanded-ins expanded-ins
               :expanded-overrides expanded-overrides
               :nphases nphases)))



;; Does everything EXCEPT compute the pipeline.
(define defsvtv-stobj-pipeline-setup ((x defsvtv-args-p)
                                      ;; (keep-final-state)
                                      ;; (keep-all-states)
                                      svtv-data)
  :guard (modalist-addr-p (design->modalist (defsvtv-args->design x)))
  :guard-hints (("goal" :do-not-induct t))
  :returns (mv err
               (pipeline-setup (implies (not err) (pipeline-setup-p pipeline-setup)))
               (new-svtv-data))
  (b* (((defsvtv-args x))
       (phases (if x.cycle-phases-p
                   x.cycle-phases
                 (list (make-svtv-cyclephase :constants nil
                                             :inputs-free t
                                             :outputs-captured t))))
       (outs+ (append x.internals x.outputs))

       ((mv err svtv-data)
        (svtv-data-defcycle-core x.design phases svtv-data
                                 :rewrite-phases x.pre-simplify
                                 :rewrite-cycle x.pre-simplify
                                 :cycle-simp x.cycle-simp))
       
       ((when err)
        (mv err nil svtv-data))

       (user-names (defsvtv-compute-user-namemap x.inputs x.overrides outs+))
       ((mv err svtv-data) (svtv-data-maybe-compute-namemap user-names svtv-data))
       ((when err)
        (mv err nil svtv-data))

       (namemap (svtv-data->namemap svtv-data))
       (fsm (svtv-data->cycle-fsm svtv-data))
       (statevars (svex-alist-keys (base-fsm->nextstate fsm)))
       (pipeline-setup (defsvtv-compute-pipeline-setup
                         outs+ x.inputs x.overrides x.initial-state-vars statevars namemap)))
    (mv nil pipeline-setup svtv-data))
  ///
  (defret initst-keys-of-<fn>
    (implies (not err)
             (equal (svex-alist-keys (pipeline-setup->initst pipeline-setup))
                    (svex-alist-keys (base-fsm->nextstate
                                      (svtv-data->cycle-fsm new-svtv-data))))))

  (defret validp-of-<fn>
    (implies (not err)
             (and (b* (((defsvtv-args x)))
                    (and (equal (svtv-data$c->design new-svtv-data) x.design)
                         (equal (svtv-data$c->cycle-phases new-svtv-data)
                                (if x.cycle-phases-p
                                    x.cycle-phases
                                  (list (make-svtv-cyclephase :constants nil
                                                              :inputs-free t
                                                              :outputs-captured t))))))
                  (equal (svtv-data$c->flatten-validp new-svtv-data) t)
                  (equal (svtv-data$c->flatnorm-validp new-svtv-data) t)
                  (equal (svtv-data$c->phase-fsm-validp new-svtv-data) t)
                  (equal (svtv-data$c->cycle-fsm-validp new-svtv-data) t)))))



(define defsvtv-stobj-main ((x defsvtv-args-p)
                            ;; (keep-final-state)
                            ;; (keep-all-states)
                            svtv-data)
  :guard (modalist-addr-p (design->modalist (defsvtv-args->design x)))
  :guard-hints (("goal" :do-not-induct t))
  :returns (mv err
               (svtv (implies (not err) (svtv-p svtv)))
               (new-svtv-data))
  (b* (((mv err pipeline-setup svtv-data)
        (defsvtv-stobj-pipeline-setup x svtv-data))
       ((when err)
        (mv err nil svtv-data))
       ((defsvtv-args x))
       (svtv-data (svtv-data-maybe-compute-pipeline pipeline-setup svtv-data :simp x.pipe-simp))
       (svtv-data (svtv-data-maybe-rewrite-pipeline x.simplify svtv-data))
       (svtv (svtv-data-to-svtv x svtv-data)))
    (mv nil svtv svtv-data)))










(define defsvtv$-fn ((x defsvtv-args-p)
                     svtv-data
                     ;; irrelevant, just included for make-event signature requirement
                     state)
  :guard (modalist-addr-p (design->modalist (defsvtv-args->design x)))
  :irrelevant-formals-ok t
  :hooks nil
  ;; much of this copied from defstv
  (b* (((mv err svtv svtv-data)
        (defsvtv-stobj-main x svtv-data))
       ((when err)
        (raise "Failed to generate svtv: ~@0" err)
        (mv err nil state svtv-data))
       ((defsvtv-args x))
       (events (defsvtv-events svtv x.design-const x.labels x.define-macros x.parents x.short x.long)))
    (mv nil events state svtv-data)))



(define remove-keywords ((keys symbol-listp)
                         (args keyword-value-listp))
  :returns (new-args (implies (keyword-value-listp args)
                              (keyword-value-listp new-args)))
  (cond ((endp args) nil)
        ((member-eq (car args) keys)
         (remove-keywords keys (cddr args)))
        (t (cons-with-hint (car args)
                           (cons-with-hint (cadr args)
                                           (remove-keywords keys (cddr args))
                                           (cdr args))
                           args))))

(define process-defsvtv$-user-args (name args)
  ;; Returns the :stobj argument (defaults to SVTV-DATA) and the list of
  ;; arguments to be passed to make-defsvtv-args.
  :returns (mv stobj norm-args)
  :mode :program
  (b* (((unless (keyword-value-listp args))
        (raise "Arguments must be a keyword/value list.~%")
        (mv nil nil))
       ((unless (xor (assoc-keyword :design args)
                     (assoc-keyword :mod args)))
        (raise "Must provide either :design or :mod (interchangeable), but not both.~%")
        (mv nil nil))
       (design (cadr (or (assoc-keyword :design args)
                         (assoc-keyword :mod args))))
       (stobj-look (assoc-keyword :stobj args))
       (stobj (if stobj-look (cadr stobj-look) 'svtv-data))
       (cycle-phases-p (consp (assoc-keyword :cycle-phases args)))
       (norm-args (list* :name (list 'quote name)
                         :design design
                         :cycle-phases-p cycle-phases-p
                         (remove-keywords '(:mod :design :stobj) args))))
    (mv stobj norm-args)))



;; Documented in new-svtv-doc.lisp
(defmacro defsvtv$ (name &rest args)
  (b* (((mv stobj norm-args)
        (process-defsvtv$-user-args name args)))
    `(make-event (defsvtv$-fn (make-defsvtv-args . ,norm-args)
                   ,stobj state))))



(define process-defsvtv$-phasewise-user-args (name args)
  :mode :program
  :returns (mv stobj norm-args)
  (b* (((unless (keyword-value-listp args))
        (raise "Arguments must be a keyword/value list.~%")
        (mv nil nil))
       (phases-look (assoc-keyword :phases args))
       ((unless phases-look)
        (raise "Needs a :phases argument.~%")
        (mv nil nil))
       (rest-args (remove-keywords '(:phases) args))
       (phases (svtv*-parse-phases (cadr phases-look)))
       (main-args (defsvtv*-phases-to-defsvtv-args phases)))
    (process-defsvtv$-user-args name (append main-args rest-args))))




(defmacro defsvtv$-phasewise (name &rest args)
  (b* (((mv stobj norm-args)
        (process-defsvtv$-phasewise-user-args name args)))
    `(make-event (defsvtv$-fn (make-defsvtv-args . ,norm-args)
                   ,stobj state))))

;; Doc in new-svtv-doc.lisp


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
(local
 (defsvtv$-phasewise my-svtv
   :design *my-design*
   :phases
   ((:label the-phase
     :inputs (("in" in))
     :outputs (("out" out)))
    (:label the-next-phase
     :inputs (("in" in2))
     :outputs (("out" out2))))))
