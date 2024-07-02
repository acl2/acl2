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
(include-book "cycle-probe")
(include-book "eval-phases")
(include-book "chase-base")
(local (include-book "std/io/base" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))


(acl2::defstobj-clone svtv-data2 svtv-data :suffix "2")


;; (svtv-cycle-run-fsm-inputs ins phases) produces a set of inputs for the base
;; fsm given the cycle phases and inputs for the cycle fsm.

;; (svtv-fsm-to-fsm-inputs
;;   (take (len (svtv-probealist-outvars probes)) ins)
;;   override-vals override-tests fsm)
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
                                    (fsm fsm-p)
                                    aliases vcd-wiremap vcd-vals
                                    (p vl-printedlist-p))
  :guard-hints (("goal" :do-not-induct t))
  :guard (and (<= (aliass-length aliases) (vcdwires-length vcd-wiremap))
              (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
              (<= (aliass-length aliases) (4vecs-length vcd-vals))
              (not (hons-dups-p (svex-alist-keys (fsm->nextstate fsm))))
              (equal (alist-keys prev-state)
                     (svex-alist-keys (fsm->nextstate fsm))))
  :returns (mv vcd-vals1
               (p1 vl-printedlist-p)
               (final-state svex-env-p))
  (b* (((when (atom inalists))
        (mv vcd-vals (vl::vl-printedlist-fix p) (svex-env-fix prev-state)))
       ((fsm fsm))
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
                   (fsm fsm-p)
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
              (not (hons-dups-p (svex-alist-keys (fsm->nextstate fsm))))
              (equal (alist-keys initst)
                     (svex-alist-keys (fsm->nextstate fsm))))
  :guard-hints (("Goal" :do-not-induct t))
  (b* (((fsm fsm))
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
  ;; (local
  ;;  (defret no-duplicate-nextstates-when-equal-<fn>
  ;;    (implies (and (equal y
  ;;                         (svex-alist-keys (fsm->nextstate fsm)))
  ;;                  (not err))
  ;;             (no-duplicatesp-equal y))
  ;;    :fn svtv-design-to-fsm))
  
  (defthm no-duplicate-nextstates-of-base-nextstate
    (implies (and (svtv-data$ap svtv-data)
                  (svtv-data$c->flatnorm-validp svtv-data)
                  (svtv-data$c->phase-fsm-validp svtv-data))
             (no-duplicatesp-equal (svex-alist-keys (fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
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
              (svtv-data->flatnorm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
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


(define svtv-chase$-repl (&key 
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

(define svtv-override-alist ((assigns svex-alist-p)
                             (config phase-fsm-config-p))
  :returns (override-alist svex-alist-p)
  (make-fast-alist
   (svarlist-to-override-alist
    (svtv-assigns-override-vars
     assigns (phase-fsm-config->override-config config))))
  ///
  (memoize 'svtv-override-alist))

;; Provides everything but the evaldata/evaldata2.
(define svtv-data-phase-set-svtv-chase-data (&key
                                             ((labels symbol-listp) 'nil)
                                             ((probes svtv-probealist-p) 'nil)
                                             ((namemap svtv-name-lhs-map-p) 'nil)
                                             (svtv-data 'svtv-data)
                                             (svtv-chase-data 'svtv-chase-data))
  :returns new-svtv-chase-data
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data))
  (b* (((fsm fsm) (svtv-data->phase-fsm svtv-data))
       ((flatnorm-res flatnorm) (svtv-data->flatnorm svtv-data))
       (svtv-chase-data (set-svtv-chase-data->stack nil svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->phaselabels labels svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->probes probes svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->namemap namemap svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->updates (make-fast-alist fsm.values) svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->delays (make-fast-alist flatnorm.delays) svtv-chase-data))
       (svtv-chase-data (set-svtv-chase-data->assigns (make-fast-alist flatnorm.assigns) svtv-chase-data))
       (override-alist (svtv-override-alist flatnorm.assigns (svtv-data->phase-fsm-setup svtv-data))))
    (set-svtv-chase-data->override-alist (make-fast-alist override-alist) svtv-chase-data)))


(define svtv-data-phase-fsm-evaldata ((ins svex-envlist-p)
                                      (initst svex-env-p)
                                      &key
                                      (svtv-data 'svtv-data))
  :returns (evaldata svtv-evaldata-p)
  (b* (((fsm fsm) (svtv-data->phase-fsm svtv-data)))
    (make-svtv-evaldata
     :nextstate (make-fast-alist fsm.nextstate)
     :inputs (make-fast-alists ins)
     :initst (make-fast-alist initst))))



;; (define svtv-data-chase-phase-fsm ((ins svex-envlist-p)
;;                                    (initst svex-env-p)
;;                                    &key
;;                                    ((labels symbol-listp) 'nil)
;;                                    ((probes svtv-probealist-p) 'nil)
;;                                    ((namemap svtv-name-lhs-map-p) 'nil)
;;                                    (svtv-data 'svtv-data)
;;                                    (svtv-chase-data 'svtv-chase-data)
;;                                    (state 'state))
;;   :guard (and (open-input-channel-p *standard-oi* :object state)
;;               (svtv-data->phase-fsm-validp svtv-data)
;;               (svtv-data->flatten-validp svtv-data)
;;               (equal (alist-keys initst)
;;                      (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
;;   :returns (mv new-svtv-chase-data new-state)
;;   (b* ((svtv-chase-data (svtv-data-set-svtv-chase-data :labels labels
;;                                                        :probes probes
;;                                                        :namemap namemap))
;;        (svtv-chase-data (set-svtv-chase-data->evaldata (svtv-data-phase-fsm-evaldata ins initst) svtv-chase-data)))
;;     (svtv-chase-repl)))



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
              (svtv-data->flatnorm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  (b* ((base-ins (svtv-cycle-run-fsm-inputs ins (svtv-data->cycle-phases svtv-data))))
    (svtv-data-debug-phase-fsm base-ins initst :filename filename)))




(define svtv-labels-cycle-adjust-aux ((labels symbol-listp)
                                      (cycle-len posp)
                                      (cycle-outphase natp))
  :prepwork ((local (defthm symbol-listp-of-repeat
                      (implies (symbolp x)
                               (symbol-listp (repeat n x)))
                      :hints(("Goal" :in-theory (enable repeat)))))
             (local (defthm symbol-listp-of-append
                      (implies (and (symbol-listp x) (symbol-listp y))
                               (symbol-listp (append x y))))))
  :guard (< cycle-outphase cycle-len)
  :returns (phase-labels symbol-listp)
  (if (atom labels)
      nil
    (append (repeat (lnfix cycle-outphase) nil)
            (list (mbe :logic (acl2::symbol-fix (car labels)) :exec (car labels)))
            (repeat (- (lposfix cycle-len) (+ (lnfix cycle-outphase) 1)) nil)
            (svtv-labels-cycle-adjust-aux (cdr labels) cycle-len cycle-outphase))))
       

(define svtv-labels-cycle-adjust ((labels symbol-listp)
                                  (phases svtv-cyclephaselist-p))
  :guard (or (svtv-cycle-output-phase phases) (not phases))
  :prepwork ((local (defthm svtv-cycle-output-phase-less-than-len
                      (implies (svtv-cycle-output-phase phases)
                               (< (svtv-cycle-output-phase phases) (len phases)))
                      :hints(("Goal" :in-theory (enable svtv-cycle-output-phase)))
                      :rule-classes :linear)))
  :returns (phase-labels symbol-listp)
  (svtv-labels-cycle-adjust-aux labels (pos-fix (len phases))
                                (or (svtv-cycle-output-phase phases) 0)))


(define svtv-data-cycle-set-svtv-chase-data (&key
                                             ((labels symbol-listp) 'nil)
                                             ((probes svtv-probealist-p) 'nil)
                                             ((namemap svtv-name-lhs-map-p) 'nil)
                                             (svtv-data 'svtv-data)
                                             (svtv-chase-data 'svtv-chase-data))
  :returns new-svtv-chase-data
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              (or (svtv-cycle-output-phase (svtv-data->cycle-phases svtv-data))
                  (not (svtv-data->cycle-phases svtv-data))))
  (b* ((phases (svtv-data->cycle-phases svtv-data)))
    (svtv-data-phase-set-svtv-chase-data
     :labels (svtv-labels-cycle-adjust labels phases)
     :probes (svtv-probealist-cycle-adjust probes phases)
     :namemap namemap)))

(define svtv-data-cycle-fsm-evaldata ((ins svex-envlist-p)
                                      (initst svex-env-p)
                                      &key
                                      (svtv-data 'svtv-data))
  :returns (evaldata svtv-evaldata-p)
  (b* ((phases (svtv-data->cycle-phases svtv-data))
       (base-ins (svtv-cycle-run-fsm-inputs ins phases)))
    (svtv-data-phase-fsm-evaldata base-ins initst)))


;; (defthm svex-alist-keys-of-svtv-data->cycle-nextstate
;;   (implies (and (svtv-data$ap svtv-data)
;;                 ;; (svtv-data$c->fsm-validp svtv-data)
;;                 (svtv-data$c->cycle-fsm-validp svtv-data))
;;            (equal (svex-alist-keys (fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))
;;                   (svex-alist-keys (fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
;;   :hints(("Goal" :in-theory (enable svtv-data$ap))))

(defthm svex-alist-keys-of-svtv-data->pipeline-initst
  (implies (and (svtv-data$ap svtv-data)
                ;; (svtv-data$c->fsm-validp svtv-data)
                ;; (svtv-data$c->cycle-fsm-validp svtv-data)
                (svtv-data$c->pipeline-validp svtv-data))
           (equal (svex-alist-keys (pipeline-setup->initst (svtv-data$c->pipeline-setup svtv-data)))
                  (svex-alist-keys (fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap svtv-data$c-pipeline-okp))))

(define svtv-pipeline-setup-to-cycle-inputs ((env svex-env-p)
                                             (setup pipeline-setup-p)
                                             (namemap svtv-name-lhs-map-p))
  :returns (mv (cycle-ins svex-envlist-p)
               (initst svex-env-p))
  (b* (((acl2::with-fast env))
       ((pipeline-setup setup))
       (initst (svex-alist-eval setup.initst env))
       (outvars (svtv-probealist-outvars setup.probes))
       (len (len outvars))
       (cycle-ins (svtv-fsm-to-fsm-inputs
                   (take len (svex-alistlist-eval setup.inputs env))
                   (svex-alistlist-eval setup.override-vals env)
                   (svex-alistlist-eval setup.override-tests env)
                   namemap)))
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
              (svtv-data->flatnorm-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data)))))

  (b* (((mv cycle-ins initst)
        (svtv-pipeline-setup-to-cycle-inputs env setup
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
              (svtv-data->flatnorm-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst (svtv-data->pipeline-setup svtv-data)))
                     (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  (svtv-data-debug-pipeline-aux
   env (svtv-data->pipeline-setup svtv-data)
   :filename filename))


(define svtv-data-pipeline-set-svtv-chase-data-aux ((setup pipeline-setup-p)
                                                    &key
                                                    ((labels symbol-listp) 'nil)
                                                    (svtv-data 'svtv-data)
                                                    (svtv-chase-data 'svtv-chase-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              (or (svtv-cycle-output-phase (svtv-data->cycle-phases svtv-data))
                  (not (svtv-data->cycle-phases svtv-data))))
  (b* (((pipeline-setup setup))
       (namemap (and (svtv-data->namemap-validp svtv-data)
                     (svtv-data->namemap svtv-data))))
    (svtv-data-cycle-set-svtv-chase-data :labels labels :probes setup.probes :namemap namemap)))

(define svtv-data-pipeline-set-svtv-chase-data (&key
                                                ((labels symbol-listp) 'nil)
                                                (svtv-data 'svtv-data)
                                                (svtv-chase-data 'svtv-chase-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              (or (svtv-cycle-output-phase (svtv-data->cycle-phases svtv-data))
                  (not (svtv-data->cycle-phases svtv-data))))
  (svtv-data-pipeline-set-svtv-chase-data-aux (svtv-data->pipeline-setup svtv-data)
                                              :labels labels))

(define svtv-data-pipeline-evaldata-aux ((env svex-env-p)
                                         (setup pipeline-setup-p)
                                         &key
                                         (svtv-data 'svtv-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              (or (svtv-cycle-output-phase (svtv-data->cycle-phases svtv-data))
                  (not (svtv-data->cycle-phases svtv-data))))
  :returns (evaldata svtv-evaldata-p)
  (b* (((mv cycle-ins initst)
        (svtv-pipeline-setup-to-cycle-inputs env
                                             setup
                                             (svtv-data->namemap svtv-data))))
    (svtv-data-cycle-fsm-evaldata cycle-ins initst)))

(define svtv-data-pipeline-evaldata ((env svex-env-p)
                                     &key
                                     (svtv-data 'svtv-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatten-validp svtv-data)
              (or (svtv-cycle-output-phase (svtv-data->cycle-phases svtv-data))
                  (not (svtv-data->cycle-phases svtv-data))))
  :returns (evaldata svtv-evaldata-p)
  (svtv-data-pipeline-evaldata-aux env (svtv-data->pipeline-setup svtv-data)))




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
                             (fsm fsm-p))
  :returns (result svex-env-p)
  (b* (((fsm fsm))
       ((with-fast fsm.values fsm.nextstate initst))
       (renamed-values (svtv-name-lhs-map-compose namemap fsm.values))
       ((with-fast renamed-values))
       (evaldata (make-svtv-evaldata :nextstate fsm.nextstate
                                     :inputs (make-fast-alists ins)
                                     :initst initst))
       (res
        (svtv-probealist-eval probes renamed-values evaldata)))
    (clear-memoize-table 'svex-eval-svtv-phases-call)
    res))

(define svtv-data-run-phase-fsm ((ins svex-envlist-p)
                                 (initst svex-env-p)
                                 (probes svtv-probealist-p)
                                 &key
                                 (svtv-data 'svtv-data))
  :returns (result svex-env-p)
  (svtv-fsm-run-probes ins initst probes
                       (svtv-data->namemap svtv-data)
                       (svtv-data->phase-fsm svtv-data)))


(define svtv-data-run-cycle-fsm ((ins svex-envlist-p)
                                 (initst svex-env-p)
                                 (probes svtv-probealist-p)
                                 &key
                                 (svtv-data 'svtv-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
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
      (svtv-data-run-phase-fsm (make-fast-alist (svtv-cycle-run-fsm-inputs ins phases))
                              initst
                              (svtv-probealist-cycle-adjust probes phases)))))
         



(define svtv-data-run-pipeline-aux ((env svex-env-p)
                                    (setup pipeline-setup-p)
                                    &key
                                    (svtv-data 'svtv-data))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  :returns (result svex-env-p)
  (b* (((mv cycle-ins initst)
        (svtv-pipeline-setup-to-cycle-inputs env setup (svtv-data->namemap svtv-data))))
    (svtv-data-run-cycle-fsm cycle-ins initst (pipeline-setup->probes setup))))





(define svtv-debug-get-defsvtv-args (form state)
  :returns (mv err val state)
  :mode :program
  (b* (((mv err make-defsvtv-args-form)
        (translate-defsvtv-form-for-debug form (w state)))
       ((when err)
        (er soft 'svtv-debug-get-defsvtv-args "Error translating defsvtv$ form: ~@0~%" make-defsvtv-args-form))
       ((mv err (cons ?stobjs-out defsvtv-args) state)
        (trans-eval make-defsvtv-args-form 'svtv-debug-get-defsvtv-args state t))
       ((when err)
        (er soft 'svtv-debug-get-defsvtv-args "Error evaluating make-defsvtv-args form ~x0: ~@1" make-defsvtv-args-form err))
       ;; ((unless (defsvtv-args-p defsvtv-args))
       ;;  (er soft 'svtv-debug-get-defsvtv-args "Evaluated ~x0, but the result was not a defsvtv-args object~%" make-defsvtv-args-form))
       
       ;; ((unless (modalist-addr-p (design->modalist (defsvtv-args->design defsvtv-args))))
       ;;  (er soft 'svtv-debug-get-defsvtv-args "Evaluated ~x0, but the design specified did not satisfy ~x1~%"
       ;;      make-defsvtv-args-form '(modalist-addr-p (design->modalist x))))
       )
    (mv nil defsvtv-args state)))


(define svtv-data-defsvtv-args-setup-chase ((args defsvtv-args-p)
                                            (env svex-env-p)
                                            &key
                                            (svtv-data 'svtv-data)
                                            (svtv-chase-data 'svtv-chase-data))
  :guard (and (modalist-addr-p (design->modalist (defsvtv-args->design args))))
  :returns (mv err new-svtv-chase-data new-svtv-data)
  (b* ((args (defsvtv-args-expand-stages args))
       ((mv err pipeline-setup svtv-data)
        (defsvtv-stobj-pipeline-setup args svtv-data :skip-cycle t))
       ((when err)
        (er hard? 'svtv-chase$ "Error setting up svtv-data and getting pipeline-setup obj: ~@0~%" err)
        (mv err svtv-chase-data svtv-data))
       (labels (subst nil 'acl2::? (defsvtv-args->labels args)))
       ((unless (symbol-listp labels))
        (er hard? 'svtv-chase$ "Expected labels to be a symbol list: ~x0~%" labels)
        (mv err svtv-chase-data svtv-data))
       (phases  (svtv-data->cycle-phases svtv-data))
       ((unless (or (svtv-cycle-output-phase phases)
                    (not phases)))
        (er hard? 'svtv-chase$ "Expected output phase to exist in cycle-phases~%")
        (mv "Expected output phase to exist in cycle-phases~%"
            svtv-chase-data svtv-data))
       (svtv-chase-data (svtv-data-pipeline-set-svtv-chase-data-aux pipeline-setup :labels labels))
       (svtv-chase-data
        (set-svtv-chase-data->evaldata
         (svtv-data-pipeline-evaldata-aux env pipeline-setup)
         svtv-chase-data)))
    (mv nil svtv-chase-data svtv-data))
  ///
  (defret flatten-validp-of-<fn>
    (implies (not err) (svtv-data$c->flatten-validp new-svtv-data))))


(define svtv-data-chase-defsvtv-args ((args defsvtv-args-p)
                                      (env svex-env-p)
                                      &key
                                      (svtv-data 'svtv-data)
                                      (svtv-chase-data 'svtv-chase-data)
                                      (state 'state))
  :guard (and (modalist-addr-p (design->modalist (defsvtv-args->design args)))
              (open-input-channel-p *standard-oi* :object state))
  :returns (mv err new-svtv-chase-data new-svtv-data new-state)
  (b* (((mv err svtv-chase-data svtv-data)
        (svtv-data-defsvtv-args-setup-chase args env))
       ((when err) (mv err svtv-chase-data svtv-data state))
       (svtv-chase-data (set-svtv-chase-data->evaldata2 nil svtv-chase-data))
       ((mv svtv-chase-data state) (svtv-chase$-repl)))
    (mv nil svtv-chase-data svtv-data state)))

(define svtv-data-defsvtv-args-evaldata ((args defsvtv-args-p)
                                         (env svex-env-p)
                                         &key
                                         (svtv-data 'svtv-data))
  :guard (and (modalist-addr-p (design->modalist (defsvtv-args->design args))))
  :returns (mv err (evaldata (implies (not err) (svtv-evaldata-p evaldata))) new-svtv-data)
  (b* ((args (defsvtv-args-expand-stages args))
       ((mv err pipeline-setup svtv-data)
        (defsvtv-stobj-pipeline-setup args svtv-data :skip-cycle t))
       ((when err)
        (er hard? 'svtv-chase$ "Error setting up svtv-data and getting pipeline-setup obj: ~@0~%" err)
        (mv err nil svtv-data))
       (phases  (svtv-data->cycle-phases svtv-data))
       ((unless (or (svtv-cycle-output-phase phases)
                    (not phases)))
        (er hard? 'svtv-chase$ "Expected output phase to exist in cycle-phases~%")
        (mv "Expected output phase to exist in cycle-phases~%"
            nil svtv-data)))
    (mv nil
        (svtv-data-pipeline-evaldata-aux env pipeline-setup)
        svtv-data)))








(define svtv-chase$-defsvtv-form (form
                                  (env svex-env-p)
                                  &key
                                  (svtv-data 'svtv-data)
                                  (svtv-chase-data 'svtv-chase-data)
                                  (state 'state))
  :mode :program
  (b* (((mv err defsvtv-args state)
        (svtv-debug-get-defsvtv-args form state))
       ((when err)
        (er hard? 'svtv-chase$ "Error recreating defsvtv-args object: ~@0~%" err)
        (mv err svtv-chase-data svtv-data state)))
    ;; ec-call to get rid of invariant risk
    (ec-call (svtv-data-chase-defsvtv-args-fn defsvtv-args env svtv-data svtv-chase-data state))))


(define svtv-chase$-compare-offsets-by-labels ((common-labels symbol-listp)
                                               (labels1 symbol-listp)
                                               (labels2 symbol-listp))
  :guard (and (subsetp-eq common-labels labels1)
              (subsetp-eq common-labels labels2))
  :guard-hints (("goal" :expand ((:free (labels) (subsetp-equal common-labels labels)))))
  :prepwork ((local (defthm acl2-numberp-when-natp
                      (implies (natp x)
                               (acl2-numberp x)))))
  :returns (offsets integer-listp)
  (if (atom common-labels)
      nil
    (cons (- (acl2::index-of (car common-labels) labels2)
             (acl2::index-of (car common-labels) labels1))
          (svtv-chase$-compare-offsets-by-labels (cdr common-labels) labels1 labels2))))

(define svtv-chase$-compare-most-frequent-offset ((offsets integer-listp)
                                                  (seen integer-listp)
                                                  (most-frequent integerp)
                                                  (frequency natp))
  :returns (most-freq-offset integerp :rule-classes :type-prescription)
  (b* (((when (atom offsets))
        (lifix most-frequent))
       (offset1 (car offsets))
       ((when (member offset1 seen))
        (svtv-chase$-compare-most-frequent-offset (cdr offsets) seen most-frequent frequency))
       (count (count offset1 offsets))
       ((when (<= count (lnfix frequency)))
        (svtv-chase$-compare-most-frequent-offset (cdr offsets) (cons offset1 seen) most-frequent frequency)))
    (svtv-chase$-compare-most-frequent-offset (cdr offsets) (cons offset1 seen) offset1 count)))
   

(define svtv-chase$-compare-decide-offset ((offset maybe-integerp)
                                           (labels1 symbol-listp)
                                           (labels2 symbol-listp))
  :returns (final-offset integerp :rule-classes :type-prescription)
  :prepwork ((local (defthm subsetp-equal-intersection-1
                      (implies (subsetp-equal x z)
                               (subsetp-equal (intersection-equal x y) z))))
             (local (defthm subsetp-equal-intersection-2
                      (implies (subsetp-equal y z)
                               (subsetp-equal (intersection-equal x y) z)))))
  (b* (((when offset)
        (lifix offset))
       (common-labels (remove-eq nil (intersection-eq labels1 labels2)))
       ((unless common-labels) 0)
       (offsets-by-label (svtv-chase$-compare-offsets-by-labels common-labels labels1 labels2)))
    (svtv-chase$-compare-most-frequent-offset offsets-by-label nil 0 0)))
       
                                           

(define svtv-chase-offsets-remove-unlisted ((labels symbol-listp)
                                            (offset-phases symbol-listp))
  ;; Replaces any labels not in offset-phases with nil.
  (if (atom labels)
      nil
    (cons (and (member-eq (car labels) offset-phases)
               (car labels))
          (svtv-chase-offsets-remove-unlisted (cdr labels) offset-phases))))

(define svtv-chase-offsets-maybe-remove-unlisted ((labels symbol-listp)
                                                  (offset-phases symbol-listp))
  ;; Replaces any labels not in offset-phases with nil, but only if offset-phases isn't empty.
  (if (consp offset-phases)
      (svtv-chase-offsets-remove-unlisted labels offset-phases)
    labels))

(define svtv-chase$-compare-defsvtv-forms (&key
                                           form1
                                           (env1 svex-env-p)
                                           (form2)
                                           (env2 svex-env-p)
                                           (offset)
                                           (offset-phases)
                                           (svtv-data 'svtv-data)
                                           (svtv-chase-data 'svtv-chase-data)
                                           (state 'state))
  :mode :program
  (b* (((mv err defsvtv-args state)
        (svtv-debug-get-defsvtv-args form1 state))
       ((when err)
        (er hard? 'svtv-chase$ "Error recreating defsvtv-args object: ~@0~%" err)
        (mv err svtv-chase-data svtv-data state))
       ((mv err defsvtv-args2 state)
        (if form2
            (svtv-debug-get-defsvtv-args form2 state)
          (mv nil defsvtv-args state)))
       ((when err)
        (er hard? 'svtv-chase$ "Error recreating defsvtv-args object: ~@0~%" err)
        (mv err svtv-chase-data svtv-data state))
       (defsvtv-args2 (defsvtv-args-expand-stages defsvtv-args2))
       ((mv err svtv-chase-data svtv-data)
        (svtv-data-defsvtv-args-setup-chase defsvtv-args env1))
       ((when err)
        (mv err svtv-chase-data svtv-data state))
       ((mv err evaldata2 svtv-data)
        (svtv-data-defsvtv-args-evaldata defsvtv-args2 env2))
       ((when err)
        (mv err svtv-chase-data svtv-data state))
       (svtv-chase-data (set-svtv-chase-data->evaldata2 evaldata2 svtv-chase-data))
       (offset (svtv-chase$-compare-decide-offset offset
                                                  (svtv-chase-offsets-maybe-remove-unlisted
                                                   (svtv-chase-data->phaselabels svtv-chase-data) offset-phases)
                                                  (svtv-chase-offsets-maybe-remove-unlisted
                                                   (subst nil 'acl2::?
                                                          (svtv-labels-cycle-adjust
                                                           (defsvtv-args->labels defsvtv-args2)
                                                           (defsvtv-args->cycle-phases defsvtv-args2)))
                                                   offset-phases)))
       (svtv-chase-data (set-svtv-chase-data->data2-offset offset svtv-chase-data))
       ((mv svtv-chase-data state) (svtv-chase$-repl)))
    (mv nil svtv-chase-data svtv-data state)))


(define svtv-chase$ ((svtv svtv-p)
                     (env svex-env-p)
                     &key
                     (svtv-data 'svtv-data)
                     (svtv-chase-data 'svtv-chase-data)
                     (state 'state))
  :mode :program
  (svtv-chase$-defsvtv-form (svtv->form svtv) env))


(defmacro svtv-data-chase-defsvtv$ (form
                                    &key
                                    env
                                    (svtv-data 'svtv-data)
                                    (svtv-chase-data 'svtv-chase-data))
  (prog2$ (cw "~x0: deprecated -- use ~x1~%" 'svtv-data-chase-defsvtv$ 'svtv-chase-defsvtv$)
          `(svtv-chase$-defsvtv-form ',form ,env :svtv-data ,svtv-data :svtv-chase-data ,svtv-chase-data)))

(defmacro svtv-chase-defsvtv$ (form
                               &key
                               env
                               (svtv-data 'svtv-data)
                               (svtv-chase-data 'svtv-chase-data))
  `(svtv-chase$-defsvtv-form ',form ,env :svtv-data ,svtv-data :svtv-chase-data ,svtv-chase-data))



(define svtv-chase$-compare-aux (&key
                                form
                                svtv
                                env
                                form1
                                svtv1
                                env1
                                form2
                                svtv2
                                env2
                                (offset)
                                (offset-phases)
                                (svtv-data 'svtv-data)
                                (svtv-chase-data 'svtv-chase-data)
                                (state 'state))
  :mode :program
  (svtv-chase$-compare-defsvtv-forms
   :form1 (or form1
              form
              (and svtv1 (svtv->form svtv1))
              (and svtv (svtv->form svtv))
              (er hard? 'svtv-chase-compare-aux "Need an SVTV or form!~%"))
   :form2 (or form2
              (and svtv2 (svtv->form svtv2))) ;; otherwise the same as form1, implicitly
   :env1 (or env1 env)
   :env2 (or env2 env)
   :offset offset
   :offset-phases offset-phases))
  

(defmacro svtv-chase$-compare ( &key
                                form
                                svtv
                                env
                                form1
                                svtv1
                                env1
                                form2
                                svtv2
                                env2
                                (offset)
                                (offset-phases)
                                (svtv-data 'svtv-data)
                                (svtv-chase-data 'svtv-chase-data))
  `(svtv-chase$-compare-aux
    :form ',form
    :svtv ,svtv
    :env ,env
    :form1 ',form1
    :svtv1 ,svtv1
    :env1 ,env1
    :form2 ',form2
    :svtv2 ,svtv2
    :env2 ,env2
    :offset ,offset
    :offset-phases ',offset-phases
    :svtv-data ,svtv-data
    :svtv-chase-data ,svtv-chase-data))







(define svtv-data-debug-defsvtv-args ((args defsvtv-args-p)
                                      (env svex-env-p)
                                      &key
                                      ((filename stringp) '"svtv-debug.vcd")
                                      (svtv-data 'svtv-data)
                                      (vcd-wiremap 'vcd-wiremap)
                                      (vcd-vals 'vcd-vals)
                                      (state 'state))
  :guard (and (modalist-addr-p (design->modalist (defsvtv-args->design args)))
              (open-input-channel-p *standard-oi* :object state))
  (b* (((mv err pipeline-setup svtv-data)
        (defsvtv-stobj-pipeline-setup (defsvtv-args-expand-stages args) svtv-data :skip-cycle t))
       ((when err)
        (er hard? 'svtv-debug$ "Error setting up svtv-data and getting pipeline-setup obj: ~@0~%" err)
        (mv vcd-wiremap vcd-vals svtv-data state))
       ((mv vcd-wiremap vcd-vals state)
        (svtv-data-debug-pipeline-aux env pipeline-setup :filename filename)))
    (mv vcd-wiremap vcd-vals svtv-data state)))


(define svtv-debug$-defsvtv-form (form
                                  (env svex-env-p)
                                  &key
                                  ((filename stringp) '"svtv-debug.vcd")
                                  (svtv-data 'svtv-data)
                                  (vcd-wiremap 'vcd-wiremap)
                                  (vcd-vals 'vcd-vals)
                                  (state 'state))
  :mode :program
  (b* (((mv err defsvtv-args state)
        (svtv-debug-get-defsvtv-args form state))
       ((when err)
        (er hard? 'svtv-debug$ "Error recreating defsvtv-args object: ~@0~%" err)
        (mv vcd-wiremap vcd-vals svtv-data state)))
    ;; ec-call to get rid of invariant risk
    (ec-call (svtv-data-debug-defsvtv-args-fn defsvtv-args env filename svtv-data vcd-wiremap vcd-vals state))))

(define svtv-debug$ ((svtv svtv-p)
                     (env svex-env-p)
                     &key
                     ((filename stringp) '"svtv-debug.vcd")
                     (svtv-data 'svtv-data)
                     (vcd-wiremap 'vcd-wiremap)
                     (vcd-vals 'vcd-vals)
                     (state 'state))
  :mode :program
  (svtv-debug$-defsvtv-form (svtv->form svtv) env :filename filename))

(defmacro svtv-data-debug-defsvtv$ (form
                                    &key
                                    env
                                    (filename '"svtv-debug.vcd")
                                    (svtv-data 'svtv-data)
                                    (vcd-wiremap 'vcd-wiremap)
                                    (vcd-vals 'vcd-vals))
  (prog2$ (cw "~x0: deprecated -- use ~x1~%" 'svtv-data-debug-defsvtv$ 'svtv-debug-defsvtv$)
          `(svtv-debug$-defsvtv-form ',form ,env :filename ,filename :svtv-data ,svtv-data :vcd-wiremap ,vcd-wiremap :vcd-vals ,vcd-vals)))

(defmacro svtv-debug-defsvtv$ (form
                               &key
                               env
                               (filename '"svtv-debug.vcd")
                               (svtv-data 'svtv-data)
                               (vcd-wiremap 'vcd-wiremap)
                               (vcd-vals 'vcd-vals))
  `(svtv-debug$-defsvtv-form ',form ,env :filename ,filename :svtv-data ,svtv-data :vcd-wiremap ,vcd-wiremap :vcd-vals ,vcd-vals))



(define svtv-data-run-defsvtv-args ((args defsvtv-args-p)
                                    (env svex-env-p)
                                    &key
                                    (svtv-data 'svtv-data))
  :guard (and (modalist-addr-p (design->modalist (defsvtv-args->design args))))
  (b* (((mv err pipeline-setup svtv-data)
        (defsvtv-stobj-pipeline-setup (defsvtv-args-expand-stages args) svtv-data :skip-cycle t))
       ((when err)
        (er hard? 'svtv-run$ "Error setting up svtv-data and getting pipeline-setup obj: ~@0~%" err)
        (mv nil svtv-data))
       (result
        (svtv-data-run-pipeline-aux env pipeline-setup)))
    (svtv-print-alist-readable result)
    (mv result svtv-data)))


(define svtv-run$-defsvtv-form (form
                                  (env svex-env-p)
                                  &key
                                  (svtv-data 'svtv-data)
                                  (state 'state))
  :mode :program
  (b* (((mv err defsvtv-args state)
        (svtv-debug-get-defsvtv-args form state))
       ((when err)
        (er hard? 'svtv-run$ "Error recreating defsvtv-args object: ~@0~%" err)
        (mv nil svtv-data state))
       ;; ((unless (open-input-channel-p *standard-oi* :object state))
       ;;  (er hard? 'svtv-run$ "Error: ~x0 isn't an open object input channel!?~%" '*standard-oi*)
       ;;  (mv nil svtv-data state))
       ((mv result svtv-data)
        ;; ec-call to get rid of invariant risk
        (ec-call (svtv-data-run-defsvtv-args-fn defsvtv-args env svtv-data))))
    (mv result svtv-data state)))

(define svtv-run$ ((svtv svtv-p)
                   (env svex-env-p)
                   &key
                   (svtv-data 'svtv-data)
                   (state 'state))
  :mode :program
  (svtv-run$-defsvtv-form (svtv->form svtv) env))

(defmacro svtv-data-run-defsvtv$ (form
                                    &key
                                    env
                                    (svtv-data 'svtv-data))
  (prog2$ (cw "~x0: deprecated -- use ~x1~%" 'svtv-data-run-defsvtv$ 'svtv-run-defsvtv$)
          `(svtv-run$-defsvtv-form ',form ,env :svtv-data ,svtv-data)))

(defmacro svtv-run-defsvtv$ (form
                             &key
                             env
                             (svtv-data 'svtv-data))
  `(svtv-run$-defsvtv-form ',form ,env :svtv-data ,svtv-data))



  

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
                                   (make-wire :name "mid"
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
                                       :value (svcall zerox 5 "mid")))
                                     (cons
                                      (list (make-lhrange
                                             :w 5
                                             :atom
                                             (make-lhatom-var
                                              :name "mid"
                                              :rsh 0)))
                                      (make-driver
                                       :value (svcall bitnot
                                                      (svcall zerox 5 "in")))))))))))
(local
 (make-event
  (b* (((mv result svtv-data
            state)
        (svtv-run-defsvtv$
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
    (mv nil '(value-triple :ok) state svtv-data))))

(local
 (make-event
  (b* (((mv result svtv-data state)
        (svtv-run-defsvtv$
         (defsvtv$ my-svtv
           :design *my-design*
           :phases
           `((:label the-phase
             ,@'(:inputs (("in" in)))
             :outputs (("out" out)))
            (:label the-next-phase
             :inputs (("in" in2))
             :outputs (("out" out2)))))
         :env '((in . 5) (in2 . 9))))
       (expected '((OUT . #ux1A) (OUT2 . #ux16)))
       ((unless (equal result expected))
        (mv (msg "Wrong answer: expected ~x0 result ~x1~%" expected result)
            nil state svtv-data)))
    (mv nil '(value-triple :ok) state svtv-data))))

(local
 (defsvtv$ my-svtv
   :design *my-design*
   :phases
   `((:label the-phase
      ,@'(:inputs (("in" in)))
      :outputs (("out" out)))
     (:label the-next-phase
      :inputs (("in" in2))
      :outputs (("out" out2))))))

(local
 (make-event
  (b* (((mv result svtv-data state)
        (svtv-run$ (my-svtv) '((in . 5) (in2 . 9))))
       (expected '((OUT . #ux1A) (OUT2 . #ux16)))
       ((unless (equal result expected))
        (mv (msg "Wrong answer: expected ~x0 result ~x1~%" expected result)
            nil state svtv-data)))
    (mv nil '(value-triple :ok) state svtv-data))))




#||

(local
 (defconst *my-design3*
   (make-design
    :top "my-mod"
    :modalist (list
               (cons "my-mod"
                     (make-module
                      :wires (list (make-wire :name "in"
                                              :width 5
                                              :low-idx 0)
                                   (make-wire :name "mid"
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
                                       :value (svcall zerox 5 (svex-var (make-svar :name "mid" :delay 1)))))
                                     (cons
                                      (list (make-lhrange
                                             :w 5
                                             :atom
                                             (make-lhatom-var
                                              :name "mid"
                                              :rsh 0)))
                                      (make-driver
                                       :value (svcall bitnot
                                                      (svcall zerox 5 "in")))))))))))
(sv::svtv-chase-defsvtv$
  (defsvtv$ my-svtv
           :design *my-design3*
           :phases
           '((:label the-phase
              :inputs (("in" in))
              :overrides (("mid" mid :cond mid-ovr)))
             (:label next-phase
              :outputs (("out" out)))))
  :env '((in . #x9) (mid . #xf) (mid-ovr . #xc)))

(sv::svtv-chase$-compare
:form (defsvtv$ my-svtv
           :design *my-design3*
           :phases
           '((:label the-phase
              :inputs (("in" in))
              :overrides (("mid" mid :cond mid-ovr)))
             (:label next-phase
              :outputs (("out" out)))))
  :env1 '((in . #x9) (mid . #xf) (mid-ovr . #xc))
   :env2  '((in . #x8) (mid . #xe) (mid-ovr . #xc)))

(sv::svtv-chase$-compare
:form2 (defsvtv$ my-svtv
           :design *my-design3*
           :phases
           '((:label setup)
             (:label the-phase
              :inputs (("in" in))
              :overrides (("mid" mid :cond mid-ovr)))
             (:label next-phase
              :outputs (("out" out)))))
:form1 (defsvtv$ my-svtv
           :design *my-design3*
           :phases
           '((:label the-phase
              :inputs (("in" in)))
             (:label next-phase
              :outputs (("out" out)))))
  :env2 '((in . #x9) (mid . #xf) (mid-ovr . #xc))
   :env1  '((in . #x8) (mid . #xe) (mid-ovr . #xc))
  :offset 1)


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



(defxdoc svtv-chase$
  :parents (svex-stvs)
  :short "Diagnose hardware or stimulus bugs by studying an SVTV run in a special-purpose
          read-eval-print loop."
  :long
  "<p>To enter this read-eval-print loop for the first time, run:</p>
@({
 (svtv-chase$ svtv env)
 })

<p>where SVTV is an svtv object (as produced by defsvtv) and env is an
assignment to the input/override signals of that SVTV.  Depending on the
complexity of the SVTV, the initial setup done by this command may take a few
minutes.</p>

<p>When setup is complete, you'll be shown an @('SVTV-CHASE >') prompt.  Typing
@('?') at this prompt shows the commands that may be used there.  Typically
you'll start by going to a signal of interest at a certain phase, using the @('O') or
@('G') commands.  At a given signal/phase, SVTV-CHASE will print the type of
signal -- primary input, initial state, previous state, or internal signal.
For internal signals, it will also print the list of signals that are this
signal's immediate dependencies.  To see the expression driving the current
signal, you may enter @('EXPR').  The next step is usually to select one of the
signal's dependencies and go to it, by typing its number.  To go back to the
signal you just left, you may type @('B') to pop the stack of signal/phase
positions.</p>

<p>At some point you may want to exit the read-eval-print loop, which you can
do by typing @('X') at the prompt.  To re-enter the loop, you can skip the
initial setup by running @('(svtv-chase$-repl)').</p>

<p>See @(see svtv-chase-defsvtv$) for a utility that gives the same behavior
but doesn't require the SVTV to be defined already.</p>")

(defxdoc svtv-chase-defsvtv$
  :parents (svtv-chase$)
  :short "Enter the @(see svtv-chase$) read-eval-print loop without first defining an SVTV."
  :long "<p>Usage:</p>
@({
 (svtv-chase-defsvtv$
   ;; entire form used to define an SVTV.  May also be DEFSVTV$.
   (defsvtv$-phasewise ...)
   :env env)
 })

<p>See @(see svtv-chase$).  This version is useful in cases where a
user is debugging the signal settings of an SVTV.  It skips the composition of
the cycle FSM and pipeline stages, which on large designs can greatly shorten
the debug loop.</p>")


(defxdoc svtv-chase$-compare
  :parents (svtv-chase$)
  :short "Compare two runs of a module using the @(see svtv-chase$) utility."
  :long "<p>This sets up and runs @(see svtv-chase$) to compare two runs of the
same module.  These two runs can either be a single SVTV run with different
input environments, or two different SVTVs (though they should both be on the
same design, or the results won't make sense).  In the latter case the two
SVTVs may have different environments or both run the same one.  In case one of
the SVTVs takes more time to initialize than the other, an offset can be given
to align the time steps.  See the sample invocations below.</p>

<p>The SVTVs may either be given as SVTV objects or @(see defsvtv$) forms.</p>

<p>Sample invocations:</p>

@({
 ;; Compare two runs of the same SVTV
 (svtv-chase$-compare
  :svtv (my-svtv)
  :env1 '((a . 10) (b . 1))
  :env2 '((a . 9) (b . 1)))

 ;; Compare two runs of an SVTV given by a defsvtv$ form
 (svtv-chase$-compare
  :form (defsvtv$ my-svtv :design *my-design* :steps ...)
  :env1 '((a . 10) (b . 1))
  :env2 '((a . 9) (b . 1)))

 ;; Compare two SVTVS given by different defsvtv$ forms, on two envs,
 ;; where time step N in form1 corresponds to time step N-6 in form2
 (svtv-chase$-compare
  :form1 (defsvtv$ my-svtv :design *my-design* :steps ...)
  :form2 (defsvtv$ my-svtv :design *my-design* :steps ...)
  :env1 '((a . 10) (b . 1))
  :env2 '((a . 9) (b . 1))
  :offset -6)

 ;; Compare an existing SVTV with another SVTV given by a form, both on the same env,
 ;; and where time step N in (my-svtv) corresponds to time step N+4 in form2
 (svtv-chase$-compare
   :svtv1 (my-svtv)
   :form2 (defsvtv$ my-svtv :design *my-design* :steps ...)
   :env '((a . 10) (b . 1))
   :offset 4)
 })

<p>Since it is sometimes confusing to determine the correct offset between the
two SVTVs, there is an automatic method for making that determination which
considers the labels given to the stages, finding the offset that lines up the
most labels if there are common labels between the two SVTVs.</p>

")

(defxdoc svtv-debug$
  :parents (svex-stvs)
  :short "Dump a VCD waveform showing the internal signals of an SVTV."
  :long "<p>To dump such a VCD file, use the form:</p>
@({
 (svtv-debug$ svtv env
    :filename \"foo.vcd\") ;; default \"svtv-debug.vcd\"
 })

<p>See @(see svtv-debug-defsvtv$) for a utility that dumps a VCD without
requiring the SVTV to be defined already.</p>")


(defxdoc svtv-debug-defsvtv$
  :parents (svtv-debug$)
  :short "Dump a VCD waveform for an SVTV, without first having defined the SVTV."
  :long "<p>Usage:</p>
@({
 (svtv-debug-defsvtv$
   ;; entire form used to define an SVTV.  May also be DEFSVTV$.
   (defsvtv$-phasewise ...)
   :env env
   :filename \"my-file.vcd\") ;; default \"svtv-debug.vcd\"
 })

<p>See @(see svtv-debug$).  This version is useful in cases where a
user is debugging the signal settings of an SVTV.  It skips the composition of
the cycle FSM and pipeline stages, which on large designs can greatly shorten
the debug loop.</p>")


(defxdoc svtv-run-defsvtv$
  :parents (svtv-run)
  :short "Run an SVTV without first defining it."
  :long "<p>Usage:</p>
@({
 (svtv-run-defsvtv$
   ;; entire form used to define an SVTV.  May also be DEFSVTV$.
   (defsvtv$-phasewise ...)
   :env env)
 })

<p>This runs a concrete simulation of an SVTV without first fully defining it,
producing a mapping from output variable names to 4vec values.  It skips the
composition of the cycle FSM and pipeline stages, which on large designs can
greatly shorten the debug loop.</p>")
