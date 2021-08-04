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
(include-book "eval-phases")
(include-book "chase-base")
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
                                   (vcd-wiremap 'vcd-wiremap)
                                   (vcd-vals 'vcd-vals)
                                   (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable svtv-data$ap)
  ;;                      :do-not-induct t)))
  (b* ((design (svtv-data->design svtv-data))
       (phase-fsm (svtv-data->phase-fsm svtv-data)))
    (stobj-let ((moddb (svtv-data->moddb svtv-data))
                (aliases (svtv-data->aliases svtv-data)))
               (vcd-wiremap vcd-vals state)
               (fsm-debug ins initst phase-fsm
                          :top-mod (design->top design)
                          :filename filename)
               (mv vcd-wiremap vcd-vals state))))


(define svtv-data-chase-repl (&key 
                              (svtv-data 'svtv-data)
                              (svtv-chase-data 'svtv-chase-data)
                              (state 'state))
  :guard (and (open-input-channel-p *standard-oi* :object state)
              (svtv-data->flatten-validp svtv-data))
  (b* ((design  (svtv-data->design svtv-data)))
    (stobj-let ((moddb (svtv-data->moddb svtv-data))
                (aliases (svtv-data->aliases svtv-data)))
               (svtv-chase-data state)
               (b* ((svtv-chase-data (set-svtv-chase-data->modidx (moddb-modname-get-index
                                                                   (design->top design)
                                                                   moddb)
                                                                  svtv-chase-data)))
                 (svtv-chase-repl))
               (mv svtv-chase-data state))))


(define svtv-data-chase-phase-fsm ((ins svex-envlist-p)
                                   (initst svex-env-p)
                                   &key
                                   ((probes svtv-probealist-p) 'nil)
                                   ((namemap svtv-name-lhs-map-p) 'nil)
                                   (svtv-data 'svtv-data)
                                   (svtv-chase-data 'svtv-chase-data)
                                   (state 'state))
  :guard (and (open-input-channel-p *standard-oi* :object state)
              (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  :returns (mv new-svtv-chase-data new-state)
  (b* (((base-fsm fsm) (svtv-data->phase-fsm svtv-data))
       ((flatnorm-res flatnorm) (svtv-data->flatnorm svtv-data))
       (svtv-chase-data (set-svtv-chase-data->stack nil svtv-chase-data))
       (evaldata (make-svtv-evaldata
                  :nextstate (make-fast-alist fsm.nextstate)
                  :inputs (make-fast-alists ins)
                  :initst (make-fast-alist initst)))
       (svtv-chase-data (set-svtv-chase-data->probes probes svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->namemap namemap svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->evaldata evaldata svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->updates (make-fast-alist fsm.values) svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->delays (make-fast-alist flatnorm.delays) svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->assigns (make-fast-alist flatnorm.assigns) svtv-chase-data)))
    (svtv-data-chase-repl)))



(define svtv-data-debug-cycle-fsm ((ins svex-envlist-p)
                                   (initst svex-env-p)
                                   &key
                                   ((filename stringp) '"svtv-debug.vcd")
                                   (svtv-data 'svtv-data)
                                   (vcd-wiremap 'vcd-wiremap)
                                   (vcd-vals 'vcd-vals)
                                   (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  (b* ((base-ins (svtv-cycle-run-fsm-inputs ins (svtv-data->cycle-phases svtv-data))))
    (svtv-data-debug-phase-fsm base-ins initst :filename filename)))



(define svtv-probealist-cycle-adjust-aux ((x svtv-probealist-p)
                                          (cycle-len posp)
                                          (cycle-outphase natp))
  :returns (new-x svtv-probealist-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (consp (car x))))
        (svtv-probealist-cycle-adjust-aux (cdr x) cycle-len cycle-outphase))
       ((cons var (svtv-probe pr)) (car x)))
    (cons (cons (svar-fix var) (change-svtv-probe pr :time (+ (* pr.time (lposfix cycle-len))
                                                   (lnfix cycle-outphase))))
          (svtv-probealist-cycle-adjust-aux (cdr x) cycle-len cycle-outphase))))

(define svtv-probealist-cycle-adjust ((x svtv-probealist-p)
                                      (phases svtv-cyclephaselist-p))
  :returns (new-x svtv-probealist-p)
  (b* ((len (pos-fix (len phases)))
       (outphase (or (svtv-cycle-output-phase phases) 0)))
    (svtv-probealist-cycle-adjust-aux x len outphase)))
       


(define svtv-data-chase-cycle-fsm ((ins svex-envlist-p)
                                   (initst svex-env-p)
                                   &key
                                   ((probes svtv-probealist-p) 'nil)
                                   ((namemap svtv-name-lhs-map-p) 'nil)
                                   (svtv-data 'svtv-data)
                                   (svtv-chase-data 'svtv-chase-data)
                                   (state 'state))
  :guard (and (open-input-channel-p *standard-oi* :object state)
              (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  :returns (mv new-svtv-chase-data new-state)
  (b* ((phases (svtv-data->cycle-phases svtv-data))
       (base-ins (svtv-cycle-run-fsm-inputs ins phases))
       (probes (svtv-probealist-cycle-adjust probes phases)))
    (svtv-data-chase-phase-fsm base-ins initst :probes probes :namemap namemap)))


;; (defthm svex-alist-keys-of-svtv-data->cycle-nextstate
;;   (implies (and (svtv-data$ap svtv-data)
;;                 ;; (svtv-data$c->base-fsm-validp svtv-data)
;;                 (svtv-data$c->cycle-fsm-validp svtv-data))
;;            (equal (svex-alist-keys (base-fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))
;;                   (svex-alist-keys (base-fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
;;   :hints(("Goal" :in-theory (enable svtv-data$ap))))

(defthm svex-alist-keys-of-svtv-data->pipeline-initst
  (implies (and (svtv-data$ap svtv-data)
                ;; (svtv-data$c->base-fsm-validp svtv-data)
                ;; (svtv-data$c->cycle-fsm-validp svtv-data)
                (svtv-data$c->pipeline-validp svtv-data))
           (equal (svex-alist-keys (pipeline-setup->initst (svtv-data$c->pipeline-setup svtv-data)))
                  (svex-alist-keys (base-fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap svtv-data$c-pipeline-okp))))

(define svtv-pipeline-setup-to-cycle-inputs ((env svex-env-p)
                                             (setup pipeline-setup-p)
                                             (cycle-fsm base-fsm-p)
                                             (namemap svtv-name-lhs-map-p))
  :returns (mv (cycle-ins svex-envlist-p)
               (initst svex-env-p))
  (b* (((acl2::with-fast env))
       ((pipeline-setup setup))
       (rename-ins (svex-alistlist-eval setup.inputs env))
       (rename-overrides (svex-alistlist-eval setup.overrides env))
       (initst (svex-alist-eval setup.initst env))
       (outvars (svtv-probealist-outvars setup.probes))
       (len (len outvars))
       (fsm (make-svtv-fsm :base-fsm cycle-fsm
                           :namemap namemap))
       (cycle-ins (svtv-fsm-run-input-envs
                   (take len rename-ins)
                   rename-overrides fsm)))
    (mv cycle-ins initst))
  ///
  (defret initst-alist-keys-of-<fn>
    (equal (alist-keys initst)
           (svex-alist-keys (pipeline-setup->initst setup)))))

(define svtv-data-debug-pipeline-aux ((env svex-env-p)
                                      (setup pipeline-setup-p)
                                      &key
                                      ((filename stringp) '"svtv-debug.vcd")
                                      (svtv-data 'svtv-data)
                                      (vcd-wiremap 'vcd-wiremap)
                                      (vcd-vals 'vcd-vals)
                                      (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))

  (b* (((mv cycle-ins initst)
        (svtv-pipeline-setup-to-cycle-inputs env setup
                                             (svtv-data->phase-fsm svtv-data)
                                             (svtv-data->namemap svtv-data))))
    (svtv-data-debug-cycle-fsm cycle-ins initst :filename filename)))


(define svtv-data-debug-pipeline ((env svex-env-p)
                                  &key
                                  ((filename stringp) '"svtv-debug.vcd")
                                  (svtv-data 'svtv-data)
                                  (vcd-wiremap 'vcd-wiremap)
                                  (vcd-vals 'vcd-vals)
                                  (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst (svtv-data->pipeline-setup svtv-data)))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  (svtv-data-debug-pipeline-aux
   env (svtv-data->pipeline-setup svtv-data)
   :filename filename))


(define svtv-data-chase-pipeline-aux ((env svex-env-p)
                                      (setup pipeline-setup-p)
                                      &key
                                      (svtv-data 'svtv-data)
                                      (svtv-chase-data 'svtv-chase-data)
                                      (state 'state))
  :guard (and (open-input-channel-p *standard-oi* :object state)
              (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  :returns (mv new-svtv-chase-data new-state)
  (b* (((mv cycle-ins initst)
        (svtv-pipeline-setup-to-cycle-inputs env
                                             setup
                                             (svtv-data->phase-fsm svtv-data)
                                             (svtv-data->namemap svtv-data)))
       ((pipeline-setup setup))
       (namemap (and (svtv-data->namemap-validp svtv-data)
                     (svtv-data->namemap svtv-data))))
    (svtv-data-chase-cycle-fsm cycle-ins initst :probes setup.probes :namemap namemap)))

(define svtv-data-chase-pipeline ((env svex-env-p)
                                  &key
                                  (svtv-data 'svtv-data)
                                  (svtv-chase-data 'svtv-chase-data)
                                  (state 'state))
  :guard (and (open-input-channel-p *standard-oi* :object state)
              (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst (svtv-data->pipeline-setup svtv-data)))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  :returns (mv new-svtv-chase-data new-state)
  (svtv-data-chase-pipeline-aux env (svtv-data->pipeline-setup svtv-data)))





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
           (defsvtv-stobj-pipeline-setup x ,svtv-data :skip-cycle t))
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


       
       
    
       
(define svtv-fsm-run-probes ((ins svex-envlist-p)
                             (initst svex-env-p)
                             (probes svtv-probealist-p)
                             (namemap svtv-name-lhs-map-p)
                             (fsm base-fsm-p))
  :returns (result svex-env-p)
  (b* (((base-fsm fsm))
       ((with-fast fsm.values initst))
       (renamed-values (svtv-name-lhs-map-compose namemap fsm.values))
       ((with-fast renamed-values))
       (evaldata (make-svtv-evaldata :nextstate fsm.nextstate
                                     :inputs (make-fast-alistlist ins)
                                     :initst initst))
       (res
        (svtv-probealist-eval probes renamed-values evaldata)))
    (clear-memoize-table 'svex-eval-svtv-phases-call)
    res))


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
  ;; TODO: The chase and debug (vcd dump) utils in this file only need the
  ;; phase FSM to be valid.  This one requires the cycle FSM to be valid.  It
  ;; will evaluate faster with the cycle FSM, so we should keep doing this when
  ;; the cycle FSM is valid, but we should add the capability to do this with
  ;; only the phase FSM.  We already have a function to adjust the input alists
  ;; -- svtv-cycle-run-fsm-inputs -- we just need one to adjust the probes so
  ;; that they refer to the right phases, and then we could run usign the phase
  ;; FSM.
  (if (svtv-data->cycle-fsm-validp svtv-data)
      (svtv-fsm-run-probes ins initst probes
                           (svtv-data->namemap svtv-data)
                           (svtv-data->cycle-fsm svtv-data))
    (b* ((phases (svtv-data->cycle-phases svtv-data)))
      (svtv-fsm-run-probes (svtv-cycle-run-fsm-inputs ins phases)
                           initst
                           (svtv-probealist-cycle-adjust probes phases)
                           (svtv-data->namemap svtv-data)
                           (svtv-data->phase-fsm svtv-data)))))
         



(define svtv-data-run-pipeline-aux ((env svex-env-p)
                                    (setup pipeline-setup-p)
                                    &key
                                    (svtv-data 'svtv-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
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
         (defsvtv-stobj-pipeline-setup x ,svtv-data :skip-cycle t))
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



(defun svtv-data-chase-defsvtv$-form (make-defsvtv-args-form
                                      args)
  (b* (((unless (keyword-value-listp args))
        (er hard? 'svtv-data-chase-defsvtv$ "Args should be a keyword-value list~%"))
       (env (cadr (assoc-keyword :env args)))
       (args (remove-keywords '(:env) args))
       (svtv-data (lookup-keyword-with-default :svtv-data 'svtv-data args))
       (svtv-chase-data (lookup-keyword-with-default :svtv-chase-data 'svtv-chase-data args)))
    `(b* ((x ,make-defsvtv-args-form)
          ((mv err pipeline-setup ,svtv-data)
           (defsvtv-stobj-pipeline-setup x ,svtv-data :skip-cycle t))
          ((when err)
           (mv err ,svtv-data ,svtv-chase-data state))
          ((mv ,svtv-chase-data state)
           (svtv-data-chase-pipeline-aux ,env pipeline-setup . ,args)))
       (mv err ,svtv-data ,svtv-chase-data state))))

(defun svtv-data-chase-defsvtv$-fn (defsvtv$-form args)
  (declare (xargs :mode :program))
  `(b* (((mv err make-defsvtv-args-form)
         (translate-defsvtv-form-for-debug ',defsvtv$-form (w state)))
        ((when err)
         (er soft 'svtv-data-chase-defsvtv$
             "Error translating defsvtv$ form: ~@0~%" make-defsvtv-args-form))
        (form (svtv-data-chase-defsvtv$-form make-defsvtv-args-form ',args)))
     (trans-eval-default-warning form 'svtv-data-chase-defsvtv$ state t)))


(defmacro svtv-data-chase-defsvtv$ (defsvtv$-form
                                     &rest args
                                     ;; (env 'nil)
                                     ;; (svtv-data 'svtv-data)
                                     ;; (svtv-chase-data 'svtv-chase-data)
                                     ;; (moddb 'moddb)
                                     ;; (aliases 'aliases)
                                     ;; (vcd-wiremap 'vcd-wiremap)
                                     ;; (vcd-vals 'vcd-vals)
                                     ;; (skip-flatten 'nil)
                                     )
  (svtv-data-chase-defsvtv$-fn defsvtv$-form args))



  

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
  (b* (((mv err (cons ?stobjs-out
                      (list ?err2 result ?replaced-svtv-data))
            state)
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
       (stobjs-out-expected  '(nil nil svtv-data))
       ((unless (equal stobjs-out stobjs-out-expected))
        (mv (msg "Unexpected stobjs-out: ~x0 expected: ~x1~%" stobjs-out stobjs-out-expected)
            nil state))
       ((when err)
        (mv (msg "Unexpected trans-eval error: ~x0~%" err)
            nil state))
       ((when err2)
        (mv (msg "Unexpected error: ~x0~%" err2)
            nil state))
       (expected '((OUT . #ux1A) (OUT2 . #ux16)))
       ((unless (equal result expected))
        (mv (msg "Wrong answer: expected ~x0 result ~x1~%" expected result)
            nil state)))
    (mv err '(value-triple :ok) state))))

#||

(defconst *my-design2*
  (make-design
   :top "top"
   :modalist
   (make-fast-alist
    (list (cons "top"
                (make-module
                 :wires (list (make-wire :name "ctr"
                                         :width 5
                                         :low-idx 0)
                              (make-wire :name "inc"
                                         :width 1
                                         :low-idx 0)
                              (make-wire :name "reset"
                                         :width 1
                                         :low-idx 0)
                              (make-wire :name "ctrnext"
                                         :width 5
                                         :low-idx 3))
                 :assigns (list (cons (list (make-lhrange
                                             :w 5
                                             :atom (make-lhatom-var :name "ctrnext" :rsh 0))) ;; lhs
                                      (make-driver :value
                                                   (svcall ?
                                                           (svcall zerox 1 "reset")
                                                           0
                                                           (svcall + (svcall ? (svcall zerox 1 "inc") 1 0)
                                                                   (svcall zerox 5 "ctr")))))
                                (cons (list (make-lhrange
                                             :w 5
                                             :atom (make-lhatom-var :name "ctr" :rsh 0)))
                                      (make-driver :value (make-svar :name "ctrnext" :delay 1))))))))))

(svtv-data-chase-defsvtv$
 (defsvtv$ my-svtv
   :design *my-design2*
   :inputs
   '(("reset"  1 0 0 0)
     ("inc"    inc0 inc1 inc2 inc3))
   :outputs
   '(("ctr"    _ _ _ lastctr)))
 :env '((inc0 . 0) (inc1 . 1) (inc2 . 0) (inc3 . 1)))


||#
