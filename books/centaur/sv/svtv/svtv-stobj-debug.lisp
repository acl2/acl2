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

(include-book "svtv-stobj-defsvtv")
(include-book "debug")
(local (include-book "std/io/base" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))


;; (svtv-cycle-run-fsm-inputs ins phases) produces a set of inputs for the base
;; fsm given the cycle phases and inputs for the cycle fsm.

;; (svtv-fsm-run-input-envs
;;   (take (len (svtv-probealist-outvars probes)) ins)
;;   overrides fsm)
;; produces a set of inputs for the cycle fsm given inputs for the pipeline.



;; svtv-fsm-debug-init was the same as what is now svtv-design-flatten, so omitting
;; ;; BOZO This should be mostly unnecessary once we can access the moddb/aliases
;; ;; from svtv-data directly.  The main thing we're doing is replicating the
;; ;; moddb and aliases for use in the svtv-debug functions.
;; (define svtv-fsm-debug-init ((design design-p)
;;                              &key
;;                              (moddb 'moddb)
;;                              (aliases 'aliases)
;;                              ;; (debugdata 'debugdata)
;;                              )
;;   :guard (modalist-addr-p (design->modalist design))
;;   :returns (mv err
;;                new-moddb
;;                new-aliases
;;                ;; new-debugdata
;;                )
;;   :prepwork ((local (in-theory (enable modscope-local-bound modscope->modidx modscope-okp))))
;;   (b* (((mv err ?assigns ?fixups ?constraints moddb aliases)
;;         (svex-design-flatten design))
;;        ((when err)
;;         (raise "~@0~%" err)
;;         (mv err moddb aliases))
;;        (aliases (aliases-indexed->named aliases (make-modscope-top
;;                                                  :modidx (moddb-modname-get-index
;;                                                           (design->top design) moddb))
;;                                         moddb)))
;;     (mv nil moddb aliases))
;;   ///
;;   (defret moddb-okp-of-<fn>
;;     (implies (not err)
;;              (and (moddb-mods-ok new-moddb)
;;                   (moddb-basics-ok new-moddb))))

;;   (defret modname-of-<fn>
;;     (implies (not err)
;;              (moddb-modname-get-index (design->top design) new-moddb)))

;;   ;; (defret modidx-of-<fn>
;;   ;;   (implies (not err)
;;   ;;            (< (moddb-modname-get-index (design->top design) new-moddb)
;;   ;;               (nfix (nth *moddb->nmods1* new-moddb))))
;;   ;;   :rule-classes :linear)

;;   (defret totalwires-of-<fn>
;;     (implies (not err)
;;              (<= (moddb-mod-totalwires
;;                   (moddb-modname-get-index (design->top design) new-moddb) new-moddb)
;;                  (len new-aliases)))
;;     :rule-classes :linear))


(local (in-theory (disable hons-dups-p)))



(define fsm-debug-writephases ((phasenum natp)
                                    (inalists svex-envlist-p)
                                    (prev-state svex-env-p)
                                    (fsm base-fsm-p)
                                    aliases vcd-wiremap vcd-vals
                                    (p vl-printedlist-p))
  :guard-hints (("goal" :do-not-induct t))
  :guard (and (<= (aliass-length aliases) (vcdwires-length vcd-wiremap))
              (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
              (<= (aliass-length aliases) (4vecs-length vcd-vals))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm))))
              (equal (alist-keys prev-state)
                     (svex-alist-keys (base-fsm->nextstate fsm))))
  :returns (mv vcd-vals1
               (p1 vl-printedlist-p)
               (final-state svex-env-p))
  (b* (((when (atom inalists))
        (mv vcd-vals (vl::vl-printedlist-fix p) (svex-env-fix prev-state)))
       ((base-fsm fsm))
       (eval-alist (append (mbe :logic (svex-env-extract (svex-alist-keys fsm.nextstate) prev-state)
                                :exec prev-state)
                           (car inalists)))
       ((mv wirevals next-state)
        (with-fast-alist eval-alist
          (mv (svex-alist-eval fsm.values eval-alist)
              (svex-alist-eval fsm.nextstate eval-alist))))
       (all-wirevals (append (car inalists) wirevals))
       ((mv changes vcd-vals)
        (with-fast-alist all-wirevals
          ;; evaluate aliases and stick values in vcd-vals,
          ;; tracking changes if phase > 0
          (if (zp phasenum)
              (let* ((vcd-vals (svtv-debug-eval-aliases 0 aliases all-wirevals vcd-vals)))
                (mv nil vcd-vals))
          (svtv-debug-eval-aliases-track 0 aliases all-wirevals vcd-vals))))
       ;; print out changed vals (or all if phase = 0)
       (p (if (zp phasenum)
              (vcd-dump-first-snapshot vcd-vals vcd-wiremap p)
            (vcd-dump-delta (* 10 phasenum) changes vcd-vals vcd-wiremap p))))
    (fsm-debug-writephases (1+ (lnfix phasenum))
                                (cdr inalists)
                                next-state
                                fsm 
                                aliases vcd-wiremap vcd-vals p))
  ///
  (defret len-of-fsm-debug-writephases-vcd-vals
    (<= (len vcd-vals)
        (len vcd-vals1))
    :rule-classes :linear))


(define fsm-debug ((ins svex-envlist-p)
                   (initst svex-env-p)
                   (fsm base-fsm-p)
                   &key
                   ((top-mod modname-p) 'nil)
                   ((filename stringp) '"svtv-debug.vcd")
                   (moddb 'moddb)
                   (aliases 'aliases)
                   (vcd-wiremap 'vcd-wiremap)
                   (vcd-vals 'vcd-vals)
                   (state 'state))
  :guard (and (moddb-ok moddb)
              (b* ((modidx (moddb-modname-get-index top-mod moddb)))
                (and modidx
                     (< modidx (moddb->nmods moddb))
                     (<= (moddb-mod-totalwires modidx moddb)
                         (aliass-length aliases))))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm))))
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate fsm))))
  :guard-hints (("Goal" :do-not-induct t))
  (b* (((base-fsm fsm))
       (modidx (moddb-modname-get-index top-mod moddb))

       ;; Start VCD creation.  Make the wiremap and the scope structure (from
       ;; which we write out the module hierarchy portion of the VCD file.)
       (vcd-wiremap (resize-vcdwires (aliass-length aliases) vcd-wiremap))
       ((mv scope & vcd-wiremap) (vcd-moddb->scopes "top" modidx 0 0 moddb vcd-wiremap))

       ;; Start accumulating the contents of the VCD file into reverse
       ;; string/char accumulator p.  Print the header into p.
       ((mv date state) (oslib::date))
       (p (vcd-print-header date scope nil))

       ;; Set up the VCD values structure, an array of 4vecs -- these are
       ;; conveniently initialized to Xes
       (vcd-vals (resize-4vecs (vcdwires-length vcd-wiremap) vcd-vals))
       

       ((mv vcd-vals p &)
        (fsm-debug-writephases 0 ins initst fsm
                               aliases vcd-wiremap vcd-vals p))

       ((mv channel state)
        (open-output-channel (mbe :logic (acl2::str-fix filename) :exec filename)
                             :character state))

       ((unless channel)
        (raise "Couldn't write vcd file ~s0~%" filename)
        (mv vcd-wiremap vcd-vals state))

       (state (princ$ (vl::vl-printedlist->string p) channel state))
       (state (close-output-channel channel state)))
    (mv vcd-wiremap vcd-vals state)))


;; (local (defthm no-duplicatesp-when-equal
;;          (implies (and (equal (svex-alist-keys x) (alist-keys y))
;;                        (svex-alist-eval-equiv! x (svtv-fsm->nextstate z))
;;                        (no-duplicatesp-equal (svex-alist-keys (svtv-fsm->nextstate z))))
;;                   (no-duplicatesp-equal (alist-keys y)))))

(defsection no-duplicates-when-keys-equal-data-nextstate
  (local
   (defret no-duplicate-nextstates-when-equal-<fn>
     (implies (and (equal y
                          (svex-alist-keys (base-fsm->nextstate fsm)))
                   (not err))
              (no-duplicatesp-equal y))
     :fn svtv-design-to-fsm))
  
  (defthm no-duplicate-nextstates-of-base-nextstate
    (implies (and (svtv-data$ap svtv-data)
                  (svtv-data$c->phase-fsm-validp svtv-data))
             (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
    :hints(("Goal" :in-theory (e/d (svtv-data$ap))))))

(defthm modalist-addr-p-of-svtv-data-design
  (implies (svtv-data$ap svtv-data)
           (svarlist-addr-p (modalist-vars
                             (design->modalist (svtv-data$c->design svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap))))



(define svtv-data-debug-phase-fsm ((ins svex-envlist-p)
                                   (initst svex-env-p)
                                   &key
                                   ((filename stringp) '"svtv-debug.vcd")
                                   (svtv-data 'svtv-data)
                                   (moddb 'moddb)
                                   (aliases 'aliases)
                                   (vcd-wiremap 'vcd-wiremap)
                                   (vcd-vals 'vcd-vals)
                                   (skip-flatten 'nil)
                                   (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data))))
              (or (not skip-flatten)
                  (and (moddb-ok moddb)
                       (b* ((design (svtv-data->design svtv-data))
                            (top-mod (design->top design))
                            (modidx (moddb-modname-get-index top-mod moddb)))
                         (and modidx
                              (< modidx (moddb->nmods moddb))
                              (<= (moddb-mod-totalwires modidx moddb)
                                  (aliass-length aliases)))))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable svtv-data$ap)
  ;;                      :do-not-induct t)))
  (b* ((design (svtv-data->design svtv-data))
       ((mv err ?flatten moddb aliases)
        (if skip-flatten
            (mv nil nil moddb aliases)
          (svtv-design-flatten design)))
       ((when err)
        (mv err moddb aliases vcd-wiremap vcd-vals state))
       ((mv vcd-wiremap vcd-vals state)
        (fsm-debug ins initst (svtv-data->phase-fsm svtv-data)
                   :top-mod (design->top design)
                   :filename filename)))
    (mv nil moddb aliases vcd-wiremap vcd-vals state)))


(define svtv-data-debug-cycle-fsm ((ins svex-envlist-p)
                                   (initst svex-env-p)
                                   &key
                                   ((filename stringp) '"svtv-debug.vcd")
                                   (svtv-data 'svtv-data)
                                   (moddb 'moddb)
                                   (aliases 'aliases)
                                   (vcd-wiremap 'vcd-wiremap)
                                   (vcd-vals 'vcd-vals)
                                   (skip-flatten 'nil)
                                   (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data))))
              (or (not skip-flatten)
                  (and (moddb-ok moddb)
                       (b* ((design (svtv-data->design svtv-data))
                            (top-mod (design->top design))
                            (modidx (moddb-modname-get-index top-mod moddb)))
                         (and modidx
                              (< modidx (moddb->nmods moddb))
                              (<= (moddb-mod-totalwires modidx moddb)
                                  (aliass-length aliases)))))))
  (b* ((base-ins (svtv-cycle-run-fsm-inputs ins (svtv-data->cycle-phases svtv-data))))
    (svtv-data-debug-phase-fsm base-ins initst :filename filename :skip-flatten skip-flatten)))


(defthm svex-alist-keys-of-svtv-data->cycle-nextstate
  (implies (and (svtv-data$ap svtv-data)
                ;; (svtv-data$c->base-fsm-validp svtv-data)
                (svtv-data$c->cycle-fsm-validp svtv-data))
           (equal (svex-alist-keys (base-fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))
                  (svex-alist-keys (base-fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap))))

(defthm svex-alist-keys-of-svtv-data->pipeline-initst
  (implies (and (svtv-data$ap svtv-data)
                ;; (svtv-data$c->base-fsm-validp svtv-data)
                ;; (svtv-data$c->cycle-fsm-validp svtv-data)
                (svtv-data$c->pipeline-validp svtv-data))
           (equal (svex-alist-keys (pipeline-setup->initst (svtv-data$c->pipeline-setup svtv-data)))
                  (svex-alist-keys (base-fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap svtv-data$c-pipeline-okp))))


(define svtv-data-debug-pipeline-aux ((env svex-env-p)
                                      (setup pipeline-setup-p)
                                      &key
                                      ((filename stringp) '"svtv-debug.vcd")
                                      (svtv-data 'svtv-data)
                                      (moddb 'moddb)
                                      (aliases 'aliases)
                                      (vcd-wiremap 'vcd-wiremap)
                                      (vcd-vals 'vcd-vals)
                                      (skip-flatten 'nil)
                                      (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->cycle-fsm-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->cycle-fsm svtv-data))))
              (or (not skip-flatten)
                  (and (moddb-ok moddb)
                       (b* ((design (svtv-data->design svtv-data))
                            (top-mod (design->top design))
                            (modidx (moddb-modname-get-index top-mod moddb)))
                         (and modidx
                              (< modidx (moddb->nmods moddb))
                              (<= (moddb-mod-totalwires modidx moddb)
                                  (aliass-length aliases)))))))

  (b* (((acl2::with-fast env))
       ((pipeline-setup setup))
       (rename-ins (svex-alistlist-eval setup.inputs env))
       (rename-overrides (svex-alistlist-eval setup.overrides env))
       (initst (svex-alist-eval setup.initst env))
       (outvars (svtv-probealist-outvars setup.probes))
       (len (len outvars))
       (fsm (make-svtv-fsm :base-fsm (svtv-data->cycle-fsm svtv-data)
                           :namemap (svtv-data->namemap svtv-data)))
       (cycle-ins (svtv-fsm-run-input-envs
                   (take len rename-ins)
                   rename-overrides fsm)))
    (svtv-data-debug-cycle-fsm cycle-ins initst :filename filename :skip-flatten skip-flatten)))

(define svtv-data-debug-pipeline ((env svex-env-p)
                                  &key
                                  ((filename stringp) '"svtv-debug.vcd")
                                  (svtv-data 'svtv-data)
                                  (moddb 'moddb)
                                  (aliases 'aliases)
                                  (vcd-wiremap 'vcd-wiremap)
                                  (vcd-vals 'vcd-vals)
                                  (skip-flatten 'nil)
                                  (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->cycle-fsm-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst (svtv-data->pipeline-setup svtv-data)))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->cycle-fsm svtv-data))))
              (or (not skip-flatten)
                  (and (moddb-ok moddb)
                       (b* ((design (svtv-data->design svtv-data))
                            (top-mod (design->top design))
                            (modidx (moddb-modname-get-index top-mod moddb)))
                         (and modidx
                              (< modidx (moddb->nmods moddb))
                              (<= (moddb-mod-totalwires modidx moddb)
                                  (aliass-length aliases)))))))
  (svtv-data-debug-pipeline-aux
   env (svtv-data->pipeline-setup svtv-data)
   :filename filename :skip-flatten skip-flatten))


(defun find-make-defsvtv-args (x)
  (cond ((atom x) nil)
        ((or (eq (car x) 'sv::make-defsvtv-args)
             (eq (car x) 'sv::make-defsvtv-args!))
         x)
        ((eq (car x) 'quote) nil)
        (t (or (find-make-defsvtv-args (car x))
               (find-make-defsvtv-args (cdr x))))))
    

(defun translate-defsvtv-form-for-debug (defsvtv$-form wrld)
  (declare (xargs :mode :program))
  (b* (((mv err val) (acl2::macroexpand1-cmp defsvtv$-form
                                             'translate-defsvtv-form-for-debug
                                             wrld
                                             (default-state-vars nil)))
       ((when err) (mv err val))
       (make-defsvtv-args (find-make-defsvtv-args val))
       ((unless make-defsvtv-args)
        (translate-defsvtv-form-for-debug val wrld)))
    (mv nil make-defsvtv-args)))


(define lookup-keyword-with-default ((key symbolp)
                                     (default)
                                     (keyvals keyword-value-listp))
  :hooks nil
  (b* ((look (assoc-keyword key keyvals)))
    (if look (cadr look) default)))

(defun svtv-data-debug-defsvtv$-form (make-defsvtv-args-form
                                      args)
  (b* (((unless (keyword-value-listp args))
        (er hard? 'svtv-data-debug-defsvtv$ "Args should be a keyword-value list~%"))
       (env (cadr (assoc-keyword :env args)))
       (args (remove-keywords '(:env) args))
       (svtv-data (lookup-keyword-with-default :svtv-data 'svtv-data args))
       (moddb (lookup-keyword-with-default :moddb 'moddb args))
       (aliases (lookup-keyword-with-default :aliases 'aliases args))
       (vcd-wiremap (lookup-keyword-with-default :vcd-wiremap 'vcd-wiremap args))
       (vcd-vals (lookup-keyword-with-default :vcd-vals 'vcd-vals args)))
    `(b* ((x ,make-defsvtv-args-form)
          ((mv err pipeline-setup ,svtv-data)
           (defsvtv-stobj-pipeline-setup x ,svtv-data))
          ((when err)
           (mv err ,svtv-data ,moddb ,aliases ,vcd-wiremap ,vcd-vals state))
          ((mv err ,moddb ,aliases ,vcd-wiremap ,vcd-vals state)
           (svtv-data-debug-pipeline-aux ,env pipeline-setup . ,args)))
       (mv err ,svtv-data ,moddb ,aliases ,vcd-wiremap ,vcd-vals state))))

(defun svtv-data-debug-defsvtv$-fn (defsvtv$-form args)
  (declare (xargs :mode :program))
  ;; (b* ((std::__function__ 'svtv-data-debug-defsvtv$-fn)
  ;;      ((mv err make-defsvtv-args-form)
  ;;       (translate-defsvtv-form-for-debug defsvtv$-form wrld))
  ;;      ((when err)
  ;;       (raise "Malformed defsvtv$-form (second argument).")))
  `(b* (((mv err make-defsvtv-args-form)
         (translate-defsvtv-form-for-debug ',defsvtv$-form (w state)))
        ((when err)
         (er soft 'svtv-data-debug-defsvtv$
             "Error translating defsvtv$ form: ~@0~%" make-defsvtv-args-form))
        (form (svtv-data-debug-defsvtv$-form make-defsvtv-args-form ',args)))
     (trans-eval-default-warning form 'svtv-data-debug-defsvtv$ state t)))


;; (defun svtv-data-debug-defsvtv$-fn (defsvtv$-form
;;                                      env args
;;                                      filename
;;                                      svtv-data
;;                                      moddb
;;                                      aliases
;;                                      vcd-wiremap
;;                                      vcd-vals
;;                                      skip-flatten)
;;   (declare (xargs :mode :program))
;;   (b* ((std::__function__ 'svtv-data-debug-defsvtv$-fn)
;;        ((acl2::unless-casematch defsvtv$-form
;;                                 (defsvtv-name name . args))
;;         (raise "Malformed defsvtv$-form (second argument)."))
;;        ((unless (or (eq defsvtv-name 'defsvtv$)
;;                     (eq defsvtv-name 'defsvtv$-phasewise)))
;;         (raise "Malformed defsvtv$-form (must be a call of ~x0 or ~x1)."
;;                'defsvtv$ 'defsvtv$-phasewise))
;;        ((mv ?stobj defsvtv-args)
;;         (if (eq defsvtv-name 'defsvtv$)
;;             (process-defsvtv$-user-args name args)
;;           (process-defsvtv$-phasewise-user-args name args))))
;;     `(b* ((x (make-defsvtv-args . ,defsvtv-args))
;;           ((mv err pipeline-setup ,svtv-data)
;;            (defsvtv-stobj-pipeline-setup x ,svtv-data))
;;           ((when err)
;;            (mv err ,svtv-data ,moddb ,aliases ,vcd-wiremap ,vcd-vals state))
;;           ((mv err ,moddb ,aliases ,vcd-wiremap ,vcd-vals state)
;;            (svtv-data-debug-pipeline-aux ,env pipeline-setup
;;                                          :filename ,filename
;;                                          :svtv-data ,svtv-data
;;                                          :moddb ,moddb
;;                                          :aliases ,aliases
;;                                          :vcd-wiremap ,vcd-wiremap
;;                                          :vcd-vals ,vcd-vals
;;                                          :skip-flatten ,skip-flatten)))
;;        (mv err ,svtv-data ,moddb ,aliases ,vcd-wiremap ,vcd-vals state))))

(defmacro svtv-data-debug-defsvtv$ (defsvtv$-form
                                     &rest args
                                     ;; (env 'nil)
                                     ;; (filename '"svtv-debug.vcd")
                                     ;; (svtv-data 'svtv-data)
                                     ;; (moddb 'moddb)
                                     ;; (aliases 'aliases)
                                     ;; (vcd-wiremap 'vcd-wiremap)
                                     ;; (vcd-vals 'vcd-vals)
                                     ;; (skip-flatten 'nil)
                                     )
  (svtv-data-debug-defsvtv$-fn defsvtv$-form args
                               ;; env
                               ;; filename
                               ;; svtv-data
                               ;; moddb
                               ;; aliases
                               ;; vcd-wiremap
                               ;; vcd-vals
                               ;; skip-flatten
                               ))



(defprod svtv-evaldata
  ((nextstate svex-alist-p)
   (inputs svex-envlist-p)
   (initst svex-env-p))
  :layout :tree)

(local (defthm svex-env-p-of-nth
         (implies (svex-envlist-p x)
                  (svex-env-p (nth n x)))))

;; bozo move somewhere sensible
(defines svex-eval-svtv-phases
  (define svex-eval-svtv-phases ((x svex-p)
                                    (phase natp)
                                    (data svtv-evaldata-p))
    :measure (acl2::nat-list-measure (list phase (svex-count x) 1))
    :returns (val 4vec-p)
    :verify-guards nil
    (b* ((x (svex-fix x)))
      (svex-case x
        :quote x.val
        :var (b* (((svtv-evaldata data))
                  (look (svex-fastlookup x.name data.nextstate))
                  ((when look)
                   ;; state var
                   (if (zp phase)
                       (svex-env-lookup x.name data.initst)
                     (svex-eval-svtv-phases look (1- phase) data))))
               ;; input var
               (svex-env-lookup x.name (nth phase data.inputs)))
        :call (svex-eval-svtv-phases-call x phase data))))

  (define svex-eval-svtv-phases-call ((x svex-p)
                                      (phase natp)
                                      (data svtv-evaldata-p))
    :measure (acl2::nat-list-measure (list phase (svex-count x) 0))
    :returns (val 4vec-p)
    :guard (svex-case x :call)
    (b* (((unless (mbt (svex-case x :call))) (4vec-x))
         ((svex-call x)))
      (mbe :logic (b* ((args (svexlist-eval-svtv-phases x.args phase data)))
                    (svex-apply x.fn args))
           :exec
           (case x.fn
             ((? ?*)
              (b* (((unless (eql (len x.args) 3))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (3vec-fix (svex-eval-svtv-phases (first x.args) phase data)))
                   ((4vec test))
                   ((when (eql test.upper 0))
                    (svex-eval-svtv-phases (third x.args) phase data))
                   ((when (not (eql test.lower 0)))
                    (svex-eval-svtv-phases (second x.args) phase data))
                   (then (svex-eval-svtv-phases (second x.args) phase data))
                   (else (svex-eval-svtv-phases (third x.args) phase data)))
                (case x.fn
                  (? (4vec-? test then else))
                  (?* (4vec-?* test then else)))))
             (?!
              (b* (((unless (eql (len x.args) 3))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((4vec test))
                   (testvec (logand test.upper test.lower))
                   ((when (eql testvec 0))
                    (svex-eval-svtv-phases (third x.args) phase data)))
                (svex-eval-svtv-phases (second x.args) phase data)))
             (bit?
              (b* (((unless (eql (len x.args) 3))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((when (eql test 0))
                    (svex-eval-svtv-phases (third x.args) phase data))
                   ((when (eql test -1))
                    (svex-eval-svtv-phases (second x.args) phase data)))
                (4vec-bit? test
                           (svex-eval-svtv-phases (second x.args) phase data)
                           (svex-eval-svtv-phases (third x.args) phase data))))
             (bit?!
              (b* (((unless (eql (len x.args) 3))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((when (eql test -1))
                    (svex-eval-svtv-phases (second x.args) phase data))
                   ((4vec test))
                   ((when (eql (logand test.upper test.lower) 0))
                    (svex-eval-svtv-phases (third x.args) phase data)))
                (4vec-bit?! test
                            (svex-eval-svtv-phases (second x.args) phase data)
                            (svex-eval-svtv-phases (third x.args) phase data))))
             (bitand
              (b* (((unless (eql (len x.args) 2))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((when (eql test 0)) 0))
                (4vec-bitand test
                             (svex-eval-svtv-phases (second x.args) phase data))))
             (bitor
              (b* (((unless (eql (len x.args) 2))
                    (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))
                   (test (svex-eval-svtv-phases (first x.args) phase data))
                   ((when (eql test -1)) -1))
                (4vec-bitor test
                            (svex-eval-svtv-phases (second x.args) phase data))))
             (otherwise
              (svex-apply x.fn (svexlist-eval-svtv-phases x.args phase data)))))))

  (define svexlist-eval-svtv-phases ((x svexlist-p)
                                        (phase natp)
                                        (data svtv-evaldata-p))
    :measure (acl2::nat-list-measure (list phase (svexlist-count x) 1))
    :returns (vals 4veclist-p)
    (if (atom x)
        nil
      (cons (svex-eval-svtv-phases (car x) phase data)
            (svexlist-eval-svtv-phases (cdr x) phase data))))
  ///

  (local (defthm consp-of-svexlist-eval-svtv-phases
           (equal (consp (svexlist-eval-svtv-phases x phase data))
                  (consp x))
           :hints (("goal" :expand ((svexlist-eval-svtv-phases x phase data))))))

  ;; (local (defthm len-of-svexlist-eval-svtv-phases
  ;;          (equal (len (svexlist-eval-svtv-phases x phase data))
  ;;                 (len x))
  ;;          :hints(("Goal" :in-theory (enable len)))))
  (local (in-theory (disable (tau-system))))

    (local (defthm upper-lower-of-3vec-fix
           (implies (and (3vec-p x)
                         (not (equal (4vec->lower x) 0)))
                    (not (equal (4vec->upper x) 0)))
           :hints(("Goal" :in-theory (enable 3vec-p)))))

  (local (defthm 4vec-?-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-? test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-? 3vec-?)))))

  (local (defthm 4vec-bit?-cases
           (and (implies (equal test 0)
                         (equal (4vec-bit? test then else)
                                (4vec-fix else)))
                (implies (equal test -1)
                         (equal (4vec-bit? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit? 3vec-bit?)))))

  (local (defthm 4vec-bit?!-cases
           (and (implies (equal (logand (4vec->upper test)
                                        (4vec->lower test))
                                0)
                         (equal (4vec-bit?! test then else)
                                (4vec-fix else)))
                (implies (equal test -1)
                         (equal (4vec-bit?! test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit?!)))))

  (local (defthm 4vec-?*-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-?* test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-?* test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*)))))

  (local (defthm 4vec-bitand-case
           (implies (equal test 0)
                    (equal (4vec-bitand test x)
                           0))
           :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand)))))

  (local (defthm 4vec-bitor-case
           (implies (equal test -1)
                    (equal (4vec-bitor test x)
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-bitor 3vec-bitor)))))

  (verify-guards svex-eval-svtv-phases
    :hints((and stable-under-simplificationp
                '(:in-theory (e/d (svex-apply len 4veclist-nth-safe nth 4vec-?!)
                                  (svex-eval))
                  :expand ((svexlist-eval-svtv-phases (svex-call->args x) phase data)
                           (svexlist-eval-svtv-phases (cdr (svex-call->args x)) phase data)
                           (svexlist-eval-svtv-phases (cddr (svex-call->args x)) phase data))))))
  (memoize 'svex-eval-svtv-phases-call)

  (defthm-svex-eval-svtv-phases-flag
    (defthm svex-eval-svtv-phases-correct
      (equal (svex-eval-svtv-phases x phase data)
             (b* (((svtv-evaldata data)))
               (svex-eval-unroll-multienv x phase data.nextstate data.inputs data.initst)))
      :hints ('(:expand ((svex-eval-svtv-phases x phase data)
                         (:free (ins initst nextstate phase) (svex-eval-unroll-multienv x phase nextstate ins initst)))))
      :flag svex-eval-svtv-phases)
    (defthm svex-eval-svtv-phases-call-correct
      (implies (svex-case x :call)
               (equal (svex-eval-svtv-phases-call x phase data)
                      (b* (((svtv-evaldata data)))
                        (svex-eval-unroll-multienv x phase data.nextstate data.inputs data.initst))))
      :hints ('(:expand ((svex-eval-svtv-phases-call x phase data)
                         (:free (ins initst nextstate phase) (svex-eval-unroll-multienv x phase nextstate ins initst))))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-eval))))
      :flag svex-eval-svtv-phases-call)
    (defthm svexlist-eval-svtv-phases-correct
      (equal (svexlist-eval-svtv-phases x phase data)
             (b* (((svtv-evaldata data)))
               (svexlist-eval-unroll-multienv x phase data.nextstate data.inputs data.initst)))
      :hints ('(:expand ((svexlist-eval-svtv-phases x phase data)
                         (:free (nextstate ins initst) (svexlist-eval-unroll-multienv x phase nextstate ins initst)))))
      :flag svexlist-eval-svtv-phases))

  (deffixequiv-mutual svex-eval-svtv-phases))


(define svtv-probealist-eval ((x svtv-probealist-p)
                              (values svex-alist-p)
                              (data svtv-evaldata-p))
  :returns (result svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (consp (car x))))
        (svtv-probealist-eval (cdr x) values data))
       ((svtv-probe p) (cdar x))
       (svex (svex-fastlookup p.signal values))
       ((unless svex)
        (cw "No signal named: ~x0~%" p.signal)
        (svtv-probealist-eval (cdr x) values data)))
    (cons (cons (svar-fix (caar x))
                (svex-eval-svtv-phases svex p.time data))
          (svtv-probealist-eval (cdr x) values data))))


       
       
    





(define svtv-data-run-cycle-fsm ((ins svex-envlist-p)
                                 (initst svex-env-p)
                                 (probes svtv-probealist-p)
                                 &key
                                 (svtv-data 'svtv-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  :returns (result svex-env-p)
  (b* (((base-fsm fsm) (svtv-data->cycle-fsm svtv-data))
       ((with-fast fsm.values))
       (renamed-values (svtv-name-lhs-map-compose (svtv-data->namemap svtv-data) fsm.values))
       ((with-fast fsm.nextstate renamed-values initst))
       (evaldata (make-svtv-evaldata :nextstate fsm.nextstate
                                     :inputs (make-fast-alistlist ins)
                                     :initst initst))
       (res
        (svtv-probealist-eval probes renamed-values evaldata)))
    (clear-memoize-table 'svex-eval-svtv-phases-call)
    res))



(define svtv-data-run-pipeline-aux ((env svex-env-p)
                                    (setup pipeline-setup-p)
                                    &key
                                    (svtv-data 'svtv-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->cycle-fsm-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->cycle-fsm svtv-data)))))
  :returns (result svex-env-p)
  (b* (((acl2::with-fast env))
       ((pipeline-setup setup))
       (rename-ins (svex-alistlist-eval setup.inputs env))
       (rename-overrides (svex-alistlist-eval setup.overrides env))
       (initst (svex-alist-eval setup.initst env))
       (outvars (svtv-probealist-outvars setup.probes))
       (len (len outvars))
       (fsm (make-svtv-fsm :base-fsm (svtv-data->cycle-fsm svtv-data)
                           :namemap (svtv-data->namemap svtv-data)))
       (cycle-ins (svtv-fsm-run-input-envs
                   (take len rename-ins)
                   rename-overrides fsm)))
    (svtv-data-run-cycle-fsm cycle-ins initst setup.probes)))




(defun svtv-data-run-defsvtv$-form (make-defsvtv-args-form
                                    env
                                    svtv-data)
  `(b* ((x ,make-defsvtv-args-form)
        ((mv err pipeline-setup ,svtv-data)
         (defsvtv-stobj-pipeline-setup x ,svtv-data))
        ((when err)
         (mv err nil ,svtv-data))
        (env
         (svtv-data-run-pipeline-aux ,env pipeline-setup
                                     :svtv-data ,svtv-data)))
     (svtv-print-alist-readable env)
     (mv nil env ,svtv-data)))

(defun svtv-data-run-defsvtv$-fn (defsvtv$-form
                                   env
                                   ;; wrld
                                   svtv-data)
  (declare (xargs :mode :program))
  ;; (b* ((std::__function__ 'svtv-data-run-defsvtv$-fn)
  ;;      ((mv err make-defsvtv-args-form)
  ;;       (translate-defsvtv-form-for-debug defsvtv$-form wrld))
  ;;      ((when err)
  ;;       (raise "Malformed defsvtv$-form (second argument).")))
  `(b* (((mv err make-defsvtv-args-form)
         (translate-defsvtv-form-for-debug ',defsvtv$-form (w state)))
        ((when err)
         (er soft 'svtv-data-run-defsvtv$ "Error translating defsvtv$ form: ~@0~%" make-defsvtv-args-form))
        (form (svtv-data-run-defsvtv$-form make-defsvtv-args-form
                                           ',env ',svtv-data)))
     (trans-eval-default-warning form 'svtv-data-run-defsvtv$ state t)))

(defmacro svtv-data-run-defsvtv$ (defsvtv$-form
                                   &key
                                   (env 'nil)
                                   (svtv-data 'svtv-data))
  (svtv-data-run-defsvtv$-fn defsvtv$-form
                             env svtv-data))



  

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
 (make-event
  (b* (((mv err result svtv-data)
        (svtv-data-run-defsvtv$
         (defsvtv$-phasewise my-svtv
           :design *my-design*
           :phases
           ((:label the-phase
             :inputs (("in" in))
             :outputs (("out" out)))
            (:label the-next-phase
             :inputs (("in" in2))
             :outputs (("out" out2)))))
         :env '((in . 5) (in2 . 9))))
       (expected '((OUT . #ux1A) (OUT2 . #ux16)))
       ((unless (equal result expected))
        (mv (msg "Wrong answer: expected ~x0 result ~x1~%" expected result)
            nil state svtv-data)))
    (mv err '(value-triple :ok) state svtv-data))))
