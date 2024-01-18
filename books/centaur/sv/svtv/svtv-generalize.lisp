; SV - Symbolic Vector Hardware Analysis Framework
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

(in-package "SV")

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

;; TEMP
;; (include-book "svtv-override-proof")


(include-book "svtv-idealize-defs")
(include-book "svtv-data-override-transparency")
(include-book "fsm-override-smart-check")
(include-book "override-part-selects")
(include-book "process")
(include-book "std/util/defredundant" :dir :system)
(include-book "override-common")
(include-book "centaur/fgl/def-fgl-thm" :dir :system)
(include-book "centaur/fgl/def-fgl-rewrite" :dir :system)
(include-book "centaur/fgl/config" :dir :system)
(include-book "override-thm-common")
;; (local (include-book "svtv-idealize-proof"))
(local (include-book "svtv-to-fsm"))
(local (include-book "svtv-spec-override-transparency"))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :Dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :Dir :System))

(local (std::add-default-post-define-hook :fix))

(std::defredundant :names (fsm-overridekey-transparent-p-of-fsm-to-cycle
                           fsm-ovcongruent-p-of-fsm-to-cycle))


(defthm 4vec-override-mux-<<=-of-same-test/val
  (4vec-override-mux-<<= test val test val ref)
  :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=-by-badbit))))

(defthm 4vec-muxtest-subsetp-of-same
  (4vec-muxtest-subsetp x x)
  :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp))))

(defthm 4vec-override-mux-ok-of-same
  (4vec-override-mux-ok test val test val ref-p ref)
  :hints(("Goal" :in-theory (enable 4vec-override-mux-ok))))

(defcong set-equiv svex-envs-equivalent (svex-env-reduce keys x) 1
  :hints (("goal" :in-theory (enable svex-envs-equivalent
                                     svex-envs-similar))))

(defthmd svtv-spec->initst-alist-of-svtv-data-obj->spec
  (equal (svtv-spec->initst-alist (svtv-data-obj->spec x))
         (pipeline-setup->initst (svtv-data-obj->pipeline-setup x)))
  :hints(("Goal" :in-theory (enable svtv-data-obj->spec))))

(defthmd svtv-spec->in-alists-of-svtv-data-obj->spec
  (equal (svtv-spec->in-alists (svtv-data-obj->spec x))
         (pipeline-setup->inputs (svtv-data-obj->pipeline-setup x)))
  :hints(("Goal" :in-theory (enable svtv-data-obj->spec))))

(defthmd svtv-spec->initst-alist-of-svtv-data-obj->ideal-spec
  (equal (svtv-spec->initst-alist (svtv-data-obj->ideal-spec x))
         (pipeline-setup->initst (svtv-data-obj->pipeline-setup x)))
  :hints(("Goal" :in-theory (enable svtv-data-obj->ideal-spec))))

(defthmd svtv-spec->fsm-of-svtv-data-obj->spec
  (equal (svtv-spec->fsm (svtv-data-obj->spec x))
         (svtv-data-obj->phase-fsm x))
  :hints(("Goal" :in-theory (enable svtv-data-obj->spec))))

(defthmd svtv-spec->cycle-phases-of-svtv-data-obj->spec
  (equal (svtv-spec->cycle-phases (svtv-data-obj->spec x))
         (svtv-data-obj->cycle-phases x))
  :hints(("Goal" :in-theory (enable svtv-data-obj->spec))))

(defthmd svtv-spec->override-val-alists-of-svtv-data-obj->spec
  (equal (svtv-spec->override-val-alists (svtv-data-obj->spec x))
         (pipeline-setup->override-vals (svtv-data-obj->pipeline-setup x)))
  :hints(("Goal" :in-theory (enable svtv-data-obj->spec))))

(defthmd svtv-spec->override-test-alists-of-svtv-data-obj->spec
  (equal (svtv-spec->override-test-alists (svtv-data-obj->spec x))
         (pipeline-setup->override-tests (svtv-data-obj->pipeline-setup x)))
  :hints(("Goal" :in-theory (enable svtv-data-obj->spec))))

(defthmd svtv-spec->probes-of-svtv-data-obj->spec
  (equal (svtv-spec->probes (svtv-data-obj->spec x))
         (pipeline-setup->probes (svtv-data-obj->pipeline-setup x)))
  :hints(("Goal" :in-theory (enable svtv-data-obj->spec))))

(defthmd svtv-spec->namemap-of-svtv-data-obj->spec
  (equal (svtv-spec->namemap (svtv-data-obj->spec x))
         (svtv-data-obj->namemap x))
  :hints(("Goal" :in-theory (enable svtv-data-obj->spec))))



(defthmd svtv-spec->in-alists-of-svtv-data-obj->ideal-spec
  (equal (svtv-spec->in-alists (svtv-data-obj->ideal-spec x))
         (pipeline-setup->inputs (svtv-data-obj->pipeline-setup x)))
  :hints(("Goal" :in-theory (enable svtv-data-obj->ideal-spec))))

(defthmd svtv-spec->in-alists-of-svtv-data-obj->ideal-spec
  (equal (svtv-spec->in-alists (svtv-data-obj->ideal-spec x))
         (pipeline-setup->inputs (svtv-data-obj->pipeline-setup x)))
  :hints(("Goal" :in-theory (enable svtv-data-obj->ideal-spec))))

(defthm svex-env-reduce-<<=-same
  (svex-env-<<= (svex-env-reduce keys x) x)
  :hints(("Goal" :in-theory (enable svex-env-<<=))))

(defthm svtv-override-triplemap-envs-ok-of-same-envs
  (svtv-override-triplemap-envs-ok triplemap pipe-env pipe-env spec-run)
  :hints(("Goal" :in-theory (enable svtv-override-triplemap-envs-ok
                                    svtv-override-triple-envs-ok))))

(defthm svtv-override-triplemaplist-envs-ok-of-same-envs
  (svtv-override-triplemaplist-envs-ok triplemaplist pipe-envs pipe-envs spec-run)
  :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-envs-ok))))

;; (defthmd set-equiv-by-mergesort-equal
;;   (implies (syntaxp (and (quotep x) (quotep y)))
;;            (equal (set-equiv x y)
;;                   (equal (mergesort x) (mergesort y))))
;;   :hints (("goal" :use ((:instance set::mergesort-under-set-equiv (x x))
;;                         (:instance set::mergesort-under-set-equiv (x y)))
;;            :in-theory (disable set::mergesort-under-set-equiv))))

;; Just a few theorems from svtv-idealize-proof are needed for this event.  We'll import them redundantly here.
;; (std::defredundant :names (set-equiv-by-mergesort-equal
;;                            ;; SET-EQUIV-IMPLIES-SVEX-ENVS-EQUIVALENT-SVEX-ENV-REDUCE-1
;;                            SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1
;;                            ;; SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-SPEC-RUN
;;                            ;; SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-IDEAL-SPEC-RUN
;;                            ;; svex-env-reduce-<<=-same
;;                            ;; svtv-override-triplemaplist-envs-ok-of-same-envs
;;                            ;; 4vec-override-mux-<<=-of-same-test/val
;;                            ;; 4vec-override-mux-ok-of-same
;;                            ))


(defthmd delays-of-design->flatnorm-of-svtv-data-obj
  (b* (((svtv-data-obj data))
       ((flatnorm-setup data.flatnorm-setup)))
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                  data.flatten-validp
                  data.flatnorm-validp
                  data.flatnorm-setup.monotonify)
             (equal (flatnorm-res->delays (design->flatnorm data.design))
                    (flatnorm-res->delays data.flatnorm))))
  :hints(("Goal" :in-theory (enable design->flatnorm
                                    svtv-normalize-assigns))))

(defthmd no-duplicatesp-by-hons-dups-p
  (implies (and (syntaxp (cmr::term-variable-free-p x))
                (not (acl2::hons-dups-p x)))
           (no-duplicatesp-equal x))
  :hints(("Goal" :in-theory (disable hons-dups-p))))

(cmr::def-force-execute hons-dups-p-when-variable-free
  acl2::hons-dups-p)


(defsection svex-alist-eval-of-fal-extract

  (defthmd fal-extract-is-svex-env-reduce
    (implies (and (svarlist-p vars)
                  (svex-env-p env))
             (equal (acl2::fal-extract vars env)
                    (svex-env-reduce vars env)))
    :hints(("Goal" :in-theory (enable acl2::fal-extract
                                      svex-env-reduce
                                      svex-env-lookup
                                      svex-env-boundp))))

  (local (defthm cdr-hons-assoc-equal-when-svex-alist-p
           (implies (svex-alist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable svex-alist-p)))))

  (defthmd fal-extract-is-svex-alist-reduce
    (implies (and (svarlist-p vars)
                  (svex-alist-p alist))
             (equal (acl2::fal-extract vars alist)
                    (svex-alist-reduce vars alist)))
    :hints(("Goal" :in-theory (enable acl2::fal-extract
                                      svex-alist-reduce
                                      svex-lookup))))

  (local (defthm hons-assoc-equal-of-svex-alist-eval
           (equal (hons-assoc-equal v (svex-alist-eval al env))
                  (and (svar-p v)
                       (hons-assoc-equal v al)
                       (cons v (svex-eval (cdr (hons-assoc-equal v al)) env))))
           :hints(("Goal" :in-theory (enable svex-alist-eval)))))

  (local (defthm car-of-hons-assoc-equal
           (equal (car (hons-assoc-equal k x))
                  (and (hons-assoc-equal k x) k))))

  ;; bozo -- redundant with svtv-stobj-decomp
  (defthm svex-alist-eval-of-fal-extract
    (implies (svarlist-p vars)
             (equal (svex-alist-eval (fal-extract vars al) env)
                    (svex-env-reduce vars (svex-alist-eval al env))))
    :hints(("Goal" :in-theory (enable fal-extract svex-env-reduce svex-alist-eval svarlist-p)))))



(define 4vec-non-x-p ((x 4vec-p))
  (b* (((4vec x)))
    (equal (logandc2 x.upper x.lower) 0))
  ///
  (defthmd 4vec-<<=-when-4vec-non-x-p
    (implies (4vec-non-x-p x)
             (equal (4vec-<<= x y)
                    (4vec-equiv x y)))
    :hints(("Goal" :in-theory (enable 4vec-<<= 4vec-fix-is-4vec-of-fields))
           (bitops::logbitp-reasoning))))



(defthmd svex-env-lookup-when-non-x-p-and-<<=
  (implies (and (svex-env-<<= env1 env2)
                (4vec-non-x-p (svex-env-lookup k env1)))
           (equal (svex-env-lookup k env2)
                  (svex-env-lookup k env1)))
  :hints(("Goal" :use ((:instance svex-env-<<=-necc (x env1) (y env2) (var k)))
          :in-theory (e/d (4vec-<<=-when-4vec-non-x-p)
                          (svex-env-<<=-necc)))))

(define svex-env-non-x-p ((x svex-env-p))
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (svar-p (caar x)))))
             (4vec-non-x-p (cdar x)))
         (svex-env-non-x-p (cdr x))))
  ///
  (defthmd lookup-when-svex-env-non-x-p
    (implies (and (svex-env-non-x-p x)
                  (svex-env-boundp k x))
             (4vec-non-x-p (svex-env-lookup k x)))
    :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-lookup
                                      hons-assoc-equal))))


  (defthmd svex-env-reduce-when-svex-env-non-x-p-and-<<=
    (implies (and (svex-env-non-x-p (svex-env-reduce vars env1))
                  (svex-env-<<= env1 env2)
                  (set-equiv (alist-keys (svex-env-fix env1)) (alist-keys (svex-env-fix env2))))
             (equal (svex-env-reduce vars env1)
                    (svex-env-reduce vars env2)))
    :hints(("Goal" :in-theory (enable svex-env-reduce-redef
                                      svex-env-boundp-iff-member-alist-keys
                                      svex-env-lookup-when-non-x-p-and-<<=)
            :induct (len vars))))

  (local (in-theory (enable svex-env-fix))))

(defthm svex-env-reduce-of-nil
  (Equal (svex-env-reduce nil x) nil)
  :hints(("Goal" :in-theory (enable svex-env-reduce))))


(defthm svex-env-reduce-when-not-consp
  (implies (not (consp keys))
           (Equal (svex-env-reduce keys x) nil))
  :hints(("Goal" :in-theory (enable svex-env-reduce))))



(fgl::disable-execution svtv-spec-run)
(fgl::remove-fgl-rewrite svtv-spec-run-fn)



(defconst *svtv-generalize-template*
  '(defsection <name>-refinement
     (local (in-theory nil))


     (:@ :phase-fsm
      (local
       (encapsulate nil
         (local (defthm phase-fsm-is-data-phase-fsm-hons-equal
                  (hons-equal (hons-copy (<phase-fsm>))
                              (hons-copy (svtv-data-obj->phase-fsm (<data>))))
                  :hints (("goal" :in-theory '((hons-equal)
                                               (hons-copy)
                                               (<phase-fsm>)
                                               (<data>)
                                               (svtv-data-obj->phase-fsm))))))
         (defthm phase-fsm-is-data-phase-fsm
           (equal (<phase-fsm>)
                  (svtv-data-obj->phase-fsm (<data>)))
           :hints (("goal" :use phase-fsm-is-data-phase-fsm-hons-equal
                    :in-theory '(hons-equal hons-copy)))))))

     
     ((:@ :svtv-spec progn)
      (:@ (not :svtv-spec) local)
      (progn
        (with-output :off (event)
          (make-event
           (b* (((svtv-data-obj x) (<data>))
                ((pipeline-setup setup) x.pipeline-setup))
             `(define <specname> ()
                :returns (spec svtv-spec-p
                               :hints (("goal" :in-theory '(svtv-spec-p-of-svtv-spec
                                                            <specname>))))
                :guard-hints (("goal" :in-theory '(SVTV-DATA-OBJ-P-OF-<DATA>
                                                   ,@(:@ :phase-fsm '(phase-fsm-is-data-phase-fsm))
                                                   fsm-p-of-svtv-data-obj->phase-fsm
                                                   (svex-alist-p)
                                                   (svtv-probealist-p)
                                                   (svex-alistlist-p)
                                                   (svtv-cyclephaselist-p)
                                                   (svtv-name-lhs-map-p))))
                (make-svtv-spec :fsm
                                ,@(:@ :phase-fsm '((<phase-fsm>)))
                                ,@(:@ (not :phase-fsm) '((svtv-data-obj->phase-fsm (<data>))))
                                :cycle-phases ',x.cycle-phases
                                :namemap ',x.namemap
                                :probes ',setup.probes
                                :in-alists ',setup.inputs
                                :override-test-alists ',setup.override-tests
                                :override-val-alists ',setup.override-vals
                                :initst-alist ',setup.initst)))))

        (in-theory (disable (<specname>)))))

     (local
      (defthmd <specname>-def
        (equal (<specname>)
               (svtv-data-obj->spec (<data>)))
        :hints(("Goal" :in-theory '(<specname>
                                    svtv-data-obj->spec
                                    (<data>)
                                    (svtv-data-obj->pipeline-setup)
                                    (svtv-data-obj->namemap)
                                    (svtv-data-obj->cycle-phases)
                                    (pipeline-setup->probes)
                                    (pipeline-setup->inputs)
                                    (pipeline-setup->override-tests)
                                    (pipeline-setup->override-vals)
                                    (pipeline-setup->initst)
                                    (:@ :phase-fsm phase-fsm-is-data-phase-fsm))))))

     
     ((:@ :svtv-spec progn)
      (:@ (not :svtv-spec) local)

      (make-event
       `(define <specname>-fsm-override-test-vars ()
        :guard-hints (("goal" :in-theory '((:EXECUTABLE-COUNTERPART IF)
                                           (:EXECUTABLE-COUNTERPART SVAR-OVERRIDETYPE-P)
                                           (:REWRITE FLATNORM-RES-P-OF-SVTV-DATA-OBJ->FLATNORM)
                                           (:REWRITE PHASE-FSM-CONFIG-P-OF-SVTV-DATA-OBJ->PHASE-FSM-SETUP)
                                           (:REWRITE SVARLIST-P-OF-SVTV-ASSIGNS-OVERRIDE-VARS)
                                           (:REWRITE SVEX-ALIST-P-OF-FLATNORM-RES->ASSIGNS)
                                           (:REWRITE
                                            SVTV-ASSIGNS-OVERRIDE-CONFIG-P-OF-PHASE-FSM-CONFIG->OVERRIDE-CONFIG)
                                           (:REWRITE SVTV-DATA-OBJ-P-OF-<DATA>))))
        ',(b* (((svtv-data-obj x) (<data>))
             (override-vars (svtv-assigns-override-vars
                             (flatnorm-res->assigns x.flatnorm)
                             (phase-fsm-config->override-config x.phase-fsm-setup))))
            (svarlist-change-override override-vars :test)))))

     (local (defthmd <specname>-fsm-override-test-vars-def
              (equal (<specname>-fsm-override-test-vars)
                     (b* (((svtv-data-obj x) (<data>))
                          (override-vars (svtv-assigns-override-vars
                                          (flatnorm-res->assigns x.flatnorm)
                                          (phase-fsm-config->override-config x.phase-fsm-setup))))
                       (svarlist-change-override override-vars :test)))
              :hints (("goal" :in-theory '((<specname>-fsm-override-test-vars)
                                           (<data>)
                                           (svtv-assigns-override-vars)
                                           (svtv-data-obj->flatnorm)
                                           (flatnorm-res->assigns)
                                           (phase-fsm-config->override-config)
                                           (svtv-data-obj->phase-fsm-setup)
                                           (svarlist-change-override))))))

     (make-event
      `(define <name>-triplemaplist ()
       :prepwork ((local (in-theory nil)))
       :returns (triplemaps svtv-override-triplemaplist-p
                            :hints (("goal" :in-theory '((<name>-triplemaplist)
                                                         (svtv-override-triplemaplist-p)))))
        ',(b* (((svtv-data-obj x) (<data>))
               ((pipeline-setup x.pipeline-setup)))
            (svtv-construct-triplemaplist x.pipeline-setup.override-tests
                                          x.pipeline-setup.override-vals
                                          x.pipeline-setup.probes))))

     (local
      (defsection <name>-triplemaplist
        ;; (local (defthmd <name>-triplemaplist-def
        ;;          (Equal (<name>-triplemaplist)
        ;;                 (b* (((svtv-data-obj x) (<data>))
        ;;                      ((pipeline-setup x.pipeline-setup)))
        ;;                   (svtv-construct-triplemaplist x.pipeline-setup.override-tests
        ;;                                                 x.pipeline-setup.override-vals
        ;;                                                 x.pipeline-setup.probes)))))
        (local (std::set-define-current-function <name>-triplemaplist))
       
        (defret syntax-check-of-<name>-triplemaplist
          (b* (((svtv-data-obj x) (<data>))
               ((pipeline-setup x.pipeline-setup)))
            (svtv-override-triplemaplist-syntax-check x.pipeline-setup.override-tests
                                                      x.pipeline-setup.override-vals
                                                      x.pipeline-setup.probes
                                                      triplemaps))
          :hints(("Goal" :in-theory '((:EXECUTABLE-COUNTERPART <DATA>)
                                      (:EXECUTABLE-COUNTERPART <NAME>-TRIPLEMAPLIST)
                                      (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->OVERRIDE-TESTS$INLINE)
                                      (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->OVERRIDE-VALS$INLINE)
                                      (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->PROBES$INLINE)
                                      (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->PIPELINE-SETUP$INLINE)
                                      (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLEMAPLIST-SYNTAX-CHECK)))))))

     (:@ :triplecheck
      (make-event
       (b* ((keys (:@ :inclusive-overridekeys
                   (b* (((svtv-data-obj x) (<data>))
                        ((pipeline-setup x.pipeline-setup)))
                     (svtv-overridekeys-full x.pipeline-setup.override-tests x.namemap)))
                  (:@ (not :inclusive-overridekeys)
                   (svtv-override-triplemaplist-overridekeys (<name>-triplemaplist)
                                                             (svtv-data-obj->namemap (<data>))))))
       `(define <name>-overridekeys ()
        :returns (overridekeys svarlist-p
                               :hints (("goal" :in-theory '((<name>-overridekeys)
                                                            (svarlist-p)))))
        :guard-hints (("goal" :in-theory '(SVTV-DATA-OBJ-P-OF-<DATA>
                                           SVTV-OVERRIDE-TRIPLEMAPLIST-P-OF-<NAME>-TRIPLEMAPLIST
                                           SVTV-NAME-LHS-MAP-P-OF-SVTV-DATA-OBJ->NAMEMAP
                                           (:EXECUTABLE-COUNTERPART IF)
                                           (:REWRITE PIPELINE-SETUP-P-OF-SVTV-DATA-OBJ->PIPELINE-SETUP)
                                           (:REWRITE SVEX-ALISTLIST-P-OF-PIPELINE-SETUP->OVERRIDE-TESTS))))
        ',keys
        ///
        (in-theory (disable (<name>-overridekeys)))))))
      
     (define <name>-input-vars ()
       :prepwork ((local (in-theory nil))
                  (make-event
                   `(defconst *<name>-input-vars*
                      ',(b* (((svtv-data-obj x) (<data>))
                             ((pipeline-setup x.pipeline-setup)))
                          (mergesort (append (svex-alist-vars x.pipeline-setup.initst)
                                             (svex-alistlist-vars x.pipeline-setup.inputs)))))))
       :returns (vars svarlist-p
                      :hints (("goal" :in-theory '((svarlist-p)
                                                   (<name>-input-vars)))))
       *<name>-input-vars*
       ///
       (in-theory (disable (<name>-input-vars))))

     (local 
      (defthm <data>-facts
        (b* (((svtv-data-obj x) (<data>))
             ((pipeline-setup x.pipeline-setup)))
          (and x.flatten-validp
               x.flatnorm-validp
               x.phase-fsm-validp
               x.cycle-fsm-validp
               x.pipeline-validp
               (flatnorm-setup->monotonify x.flatnorm-setup)

               (svarlist-override-p (svtv-cyclephaselist-keys x.cycle-phases) nil)
               (svtv-cyclephaselist-unique-i/o-phase x.cycle-phases)
               (equal (svex-alist-keys-list x.pipeline-setup.override-vals)
                      (svex-alist-keys-list x.pipeline-setup.override-tests))
               (no-duplicatesp-each (svex-alist-keys-list x.pipeline-setup.override-tests))
               (svarlist-override-p
                (svtv-name-lhs-map-list-all-keys
                 (svtv-name-lhs-map-inverse-list
                  (svtv-name-lhs-map-extract-list
                   (take (len (svtv-probealist-outvars x.pipeline-setup.probes))
                         (svex-alist-keys-list x.pipeline-setup.override-tests))
                   x.namemap)))
                nil)
               (<= (len x.pipeline-setup.override-tests)
                   (len (svtv-probealist-outvars x.pipeline-setup.probes)))

               (svex-alistlist-check-monotonic x.pipeline-setup.inputs)
               (svex-alistlist-check-monotonic x.pipeline-setup.override-vals)
               (svex-alistlist-check-monotonic x.pipeline-setup.override-tests)
               (svex-alist-check-monotonic x.pipeline-setup.initst)

               ;; (equal (* (len x.cycle-phases)
               ;;           (len (svtv-probealist-outvars x.pipeline-setup.probes)))
               ;;        *<name>-phase-count*)

               (set-equiv (append (svex-alist-vars x.pipeline-setup.initst)
                                  (svex-alistlist-vars x.pipeline-setup.inputs))
                          (<name>-input-vars))))
        :hints(("Goal" :in-theory
                '((:EXECUTABLE-COUNTERPART <)
                  (:EXECUTABLE-COUNTERPART EQUAL)
                  (:EXECUTABLE-COUNTERPART <DATA>)
                  (:EXECUTABLE-COUNTERPART FLATNORM-SETUP->MONOTONIFY$INLINE)
                  (:EXECUTABLE-COUNTERPART IF)
                  (:EXECUTABLE-COUNTERPART LEN)
                  (:EXECUTABLE-COUNTERPART NO-DUPLICATESP-EACH)
                  (:EXECUTABLE-COUNTERPART NOT)
                  (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->INITST$INLINE)
                  (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->INPUTS$INLINE)
                  (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->OVERRIDE-TESTS$INLINE)
                  (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->OVERRIDE-VALS$INLINE)
                  (:EXECUTABLE-COUNTERPART PIPELINE-SETUP->PROBES$INLINE)
                  (:EXECUTABLE-COUNTERPART SVARLIST-OVERRIDE-P)
                  (:EXECUTABLE-COUNTERPART SVEX-ALIST-CHECK-MONOTONIC)
                  (:EXECUTABLE-COUNTERPART SVEX-ALIST-KEYS-LIST)
                  (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-CHECK-MONOTONIC)
                  (:EXECUTABLE-COUNTERPART SVTV-CYCLEPHASELIST-KEYS)
                  (:EXECUTABLE-COUNTERPART SVTV-CYCLEPHASELIST-UNIQUE-I/O-PHASE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->CYCLE-FSM-VALIDP$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->CYCLE-PHASES$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->FLATNORM-SETUP$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->FLATNORM-VALIDP$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->FLATTEN-VALIDP$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->NAMEMAP$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->PHASE-FSM-VALIDP$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->PIPELINE-SETUP$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->PIPELINE-VALIDP$INLINE)
                  (:EXECUTABLE-COUNTERPART SVTV-NAME-LHS-MAP-EXTRACT-LIST)
                  (:EXECUTABLE-COUNTERPART SVTV-NAME-LHS-MAP-INVERSE-LIST)
                  (:EXECUTABLE-COUNTERPART SVTV-NAME-LHS-MAP-LIST-ALL-KEYS)
                  (:EXECUTABLE-COUNTERPART SVTV-PROBEALIST-OUTVARS)
                  (:EXECUTABLE-COUNTERPART TAKE)
                  ;; set-equiv-by-mergesort-equal
                  (mergesort)
                  (append)
                  (svex-alist-vars)
                  (svex-alistlist-vars)
                  (<name>-input-vars))))))

        
     ((:@ :svtv-spec progn)
      (:@ (not :svtv-spec) local)
      
      (defsection <specname>
        (local (std::set-define-current-function <specname>))
        
        (local (defthm <name>-is-<data>-pipeline
                 (equal (svtv->outexprs (<name>))
                        (svtv-data-obj->pipeline (<data>)))
                 :hints(("Goal" :in-theory '((<data>)
                                             (<name>)
                                             (svtv->outexprs)
                                             (svtv-data-obj->pipeline)
                                             (equal))))))

        (local (defthm svtv-run-of-<name>-is-eval-<data>-pipeline
                 (equal (svtv-run (<name>) env
                                  :boolvars boolvars
                                  :simplify simplify
                                  :quiet quiet
                                  :readable readable
                                  :allvars allvars)
                        (svex-alist-eval (svtv-data-obj->pipeline (<data>)) env))
                 :hints(("Goal" :in-theory '((:DEFINITION HONS-COPY)
                                             (:DEFINITION MAKE-FAST-ALIST)
                                             (:DEFINITION ACL2::SVTV-RUN-FN)
                                             (:REWRITE <NAME>-IS-<DATA>-PIPELINE)
                                             (:REWRITE RETURN-TYPE-OF-SVEX-ALIST-EVAL-FOR-SYMBOLIC)
                                             (:REWRITE SVEX-ALIST-EVAL-OF-SVEX-ENV-FIX-ENV))))))

        (local (defthm <data>-facts-for-spec
                 (b* (((svtv-data-obj x) (<data>)))
                   (and x.cycle-fsm-validp
                        x.pipeline-validp
                        x.flatten-validp
                        (svtv-cyclephaselist-has-outputs-captured x.cycle-phases)))
                 :hints(("Goal" :in-theory '((:EXECUTABLE-COUNTERPART <DATA>)
                                             (:EXECUTABLE-COUNTERPART SVTV-CYCLEPHASELIST-HAS-OUTPUTS-CAPTURED)
                                             (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->CYCLE-FSM-VALIDP$INLINE)
                                             (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->CYCLE-PHASES$INLINE)
                                             (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->FLATTEN-VALIDP$INLINE)
                                             (:EXECUTABLE-COUNTERPART SVTV-DATA-OBJ->PIPELINE-VALIDP$INLINE))))))


        (defretd svtv-run-of-<name>-is-svtv-spec-run-of-<specname>
          (svex-envs-equivalent (svtv-run (<name>) env
                                          :boolvars boolvars
                                          :simplify simplify
                                          :quiet quiet
                                          :readable readable
                                          :allvars allvars)
                                (svtv-spec-run spec env))
          :hints(("Goal" :in-theory '(<specname>-def
                                      (:EQUIVALENCE SVEX-ENVS-EQUIVALENT-IS-AN-EQUIVALENCE)
                                      (:REWRITE <DATA>-CORRECT)
                                      (:REWRITE <DATA>-FACTS-FOR-SPEC)
                                      (:REWRITE
                                       SVTV-RUN-OF-<NAME>-IS-EVAL-<DATA>-PIPELINE)
                                      (:REWRITE SVTV-SPEC-RUN-OF-SVTV-DATA-OBJ->SPEC)))))

        (defthm <specname>-fsm-ovmonotonic
          (b* ((x (svtv-spec->fsm (<specname>))))
            (fsm-ovmonotonic x))
          :hints(("Goal" :in-theory '(<specname>-def
                                      <SPECNAME>-FSM-OVERRIDE-TEST-VARS-DEF
                                      (:REWRITE fsm-OVMONOTONIC-OF-SVTV-DATA-OBJ->PHASE-FSM)
                                      (:REWRITE <DATA>-CORRECT)
                                      (:REWRITE <DATA>-FACTS)
                                      (:REWRITE SVTV-SPEC->FSM-OF-SVTV-DATA-OBJ->SPEC)
                                      (:TYPE-PRESCRIPTION fsm-OVMONOTONIC)))))
        
        (defthm <specname>-facts
          (b* (((svtv-spec x) (<specname>)))
            (and 
             (svarlist-override-p (svtv-cyclephaselist-keys x.cycle-phases) nil)
             (svtv-cyclephaselist-unique-i/o-phase x.cycle-phases)
             (equal (svex-alist-keys-list x.override-val-alists)
                    (svex-alist-keys-list x.override-test-alists))
             (no-duplicatesp-each (svex-alist-keys-list x.override-test-alists))
             (svarlist-override-p
              (svtv-name-lhs-map-list-all-keys
               (svtv-name-lhs-map-inverse-list
                (svtv-name-lhs-map-extract-list
                 (take (len (svtv-probealist-outvars x.probes))
                       (svex-alist-keys-list x.override-test-alists))
                 x.namemap)))
              nil)
             (<= (len x.override-test-alists)
                 (len (svtv-probealist-outvars x.probes)))

             (svex-alistlist-check-monotonic x.in-alists)
             (svex-alistlist-check-monotonic x.override-val-alists)
             (svex-alistlist-check-monotonic x.override-test-alists)
             (svex-alist-check-monotonic x.initst-alist)

             ;; (equal (* (len x.cycle-phases)
             ;;           (len (svtv-probealist-outvars x.pipeline-setup.probes)))
             ;;        *<name>-phase-count*)

             (set-equiv (append (svex-alist-vars x.initst-alist)
                                (svex-alistlist-vars x.in-alists))
                        (<name>-input-vars))))
          :hints(("Goal" :in-theory
                  '(<specname>-def
                    (:EQUIVALENCE ACL2::SET-EQUIV-IS-AN-EQUIVALENCE)
                    (:EXECUTABLE-COUNTERPART NOT)
                    (:REWRITE <DATA>-FACTS)
                    (:REWRITE SVTV-SPEC->CYCLE-PHASES-OF-SVTV-DATA-OBJ->SPEC)
                    (:REWRITE SVTV-SPEC->IN-ALISTS-OF-SVTV-DATA-OBJ->SPEC)
                    (:REWRITE SVTV-SPEC->INITST-ALIST-OF-SVTV-DATA-OBJ->SPEC)
                    (:REWRITE SVTV-SPEC->NAMEMAP-OF-SVTV-DATA-OBJ->SPEC)
                    (:REWRITE SVTV-SPEC->OVERRIDE-TEST-ALISTS-OF-SVTV-DATA-OBJ->SPEC)
                    (:REWRITE SVTV-SPEC->OVERRIDE-VAL-ALISTS-OF-SVTV-DATA-OBJ->SPEC)
                    (:REWRITE SVTV-SPEC->PROBES-OF-SVTV-DATA-OBJ->SPEC)))))))
     
     (:@ :ideal
      (define <ideal-name> ()
        :returns (spec svtv-spec-p
                       :hints (("goal" :in-theory '(<ideal-name>
                                                    svtv-spec-p-of-svtv-data-obj->ideal-spec))))
        :guard-hints (("goal" :in-theory '(<data>-correct
                                           svtv-data-obj-p-of-<data>
                                           <data>-flatten-validp)))
        :prepwork ((local (defthmd <data>-flatten-validp
                            (svtv-data-obj->flatten-validp (<data>))
                            :hints(("Goal" :in-theory '((svtv-data-obj->flatten-validp)
                                                        (<data>)))))))
        (svtv-data-obj->ideal-spec (<data>))
        ///
        (fgl::remove-fgl-rewrite <ideal-name>)
        (fgl::disable-execution <ideal-name>)
        (in-theory (disable (<ideal-name>)))))
     ;; (defconst *<name>-phase-count*
     ;;   (b* (((svtv-data-obj x) (<data>))
     ;;        ((pipeline-setup x.pipeline-setup)))
     ;;     (* (len x.cycle-phases)
     ;;        (len (svtv-probealist-outvars x.pipeline-setup.probes)))))

     

     (:@ :ideal
      (local (defthm <data>-override-syntax-check
               (b* (((svtv-data-obj x) (<data>))
                    (override-vars (svtv-assigns-override-vars
                                    (flatnorm-res->assigns x.flatnorm)
                                    (phase-fsm-config->override-config x.phase-fsm-setup)))
                    (override-keys override-vars))
                 (svtv-spec-override-syntax-checks
                  (svtv-data-obj->spec x)
                  override-keys
                  (<name>-triplemaplist)))
               :hints(("Goal" :in-theory '((<data>)
                                           (svtv-data-obj->spec)
                                           (svtv-spec-override-syntax-checks)
                                           (<name>-triplemaplist)
                                           (svtv-data-obj->flatnorm)
                                           (flatnorm-res->assigns)
                                           (svtv-data-obj->phase-fsm-setup)
                                           (phase-fsm-config->override-config)
                                           (svtv-assigns-override-vars)
                                           (svarlist-change-override)))))))
     (:@ :ideal
      (local (defthm <data>-ideal-override-syntax-check
               (b* (((svtv-data-obj x) (<data>))
                    (override-vars (svtv-assigns-override-vars
                                    (flatnorm-res->assigns x.flatnorm)
                                    (phase-fsm-config->override-config x.phase-fsm-setup)))
                    (override-keys override-vars))
                 (svtv-spec-override-syntax-checks
                  (svtv-data-obj->ideal-spec x)
                  override-keys
                  (<name>-triplemaplist)))
               :hints (("goal" :use <data>-override-syntax-check
                        :in-theory '(svtv-spec-stimulus-equiv-implies-equal-svtv-spec-override-syntax-checks-1
                                     svtv-spec-stimulus-equiv-of-svtv-data-obj->ideal-spec
                                     <data>-correct
                                     <data>-facts))))))
                                      
                                       
     (:@ :triplecheck
      (local (defthm <data>-generalize-override-syntax-check
               (b* (((svtv-data-obj x) (<data>))
                    (override-keys (<name>-overridekeys)))
                 (svtv-spec-override-syntax-checks
                  (svtv-data-obj->spec x)
                  override-keys
                  (<name>-triplemaplist)))
               :hints(("Goal" :in-theory '((<data>)
                                           (<name>-overridekeys)
                                           (svtv-data-obj->spec)
                                           (<name>-triplemaplist)
                                           (svtv-spec-override-syntax-checks)
                                           (svtv-data-obj->flatnorm)
                                           (flatnorm-res->assigns)
                                           (svtv-data-obj->phase-fsm-setup)
                                           (phase-fsm-config->override-config)
                                           (svtv-assigns-override-vars)
                                           (svarlist-change-override)))))))

     (:@ (and :triplecheck
              :svtv-spec)
      (local (defthm <specname>-override-syntax-check
               (b* (((svtv-data-obj x) (<data>))
                    (override-keys (<name>-overridekeys)))
                 (svtv-spec-override-syntax-checks
                  (<specname>)
                  override-keys
                  (<name>-triplemaplist)))
               :hints(("Goal" :in-theory '(<specname>-def
                                           <specname>-fsm-override-test-vars-def
                                           <data>-generalize-override-syntax-check))))))

     ;; (:@ :triplecheck
     ;;  (local (defthm svexlist-check-overridetriples-of-<data>
     ;;           (b* (((svtv-data-obj x) (<data>))
     ;;                ((fsm x.phase-fsm))
     ;;                (overridekeys (<name>-overridekeys))
     ;;                (triples (svar->svex-override-triplelist
     ;;                          (svarlist-to-override-triples overridekeys)
     ;;                          x.phase-fsm.values)))
     ;;             (and (not (svexlist-check-overridetriples (svex-alist-vals x.phase-fsm.values) triples))
     ;;                  (not (svexlist-check-overridetriples (svex-alist-vals x.phase-fsm.nextstate) triples))))
     ;;           :hints (("goal" :in-theory '((<data>)
     ;;                                        (svex-alist-vals)
     ;;                                        (svtv-data-obj->phase-fsm)
     ;;                                        (<name>-overridekeys)
     ;;                                        (svar->svex-override-triplelist)
     ;;                                        (svarlist-to-override-triples)
     ;;                                        (fsm->values)
     ;;                                        (fsm->nextstate)
     ;;                                        (svexlist-check-overridetriples)))))))

     (:@ :triplecheck
      (:@ :phase-fsm
       (make-event
        ;; make-event wrapper for the case where this book is included locally
        '(def-override-transparent <phase-fsm>-override-transparent-for-<name>
           :fsm (<phase-fsm>) :keys (<name>-overridekeys)
           (:@ :fgl-semantic-check :fgl-semantic-check t)
           (:@ (not :default-aignet-transforms) :use-default-aignet-transforms nil)))
       (local
        (defthm fsm-override-transparent-p-of-<data>
          (fsm-overridekey-transparent-p
           (svtv-data-obj->phase-fsm (<data>))
           (<name>-overridekeys))
          :hints (("goal" :in-theory '(phase-fsm-is-data-phase-fsm)
                   :use <phase-fsm>-override-transparent-for-<name>)))))
      (:@ (not :phase-fsm)
       (local
        (def-override-transparent fsm-override-transparent-p-of-<data>
          :fsm (svtv-data-obj->phase-fsm (<data>)) :keys (<name>-overridekeys)
          (:@ :fgl-semantic-check :fgl-semantic-check t)
          (:@ (not :default-aignet-transforms) :use-default-aignet-transforms nil))))

      (:@ :svtv-spec
       (defthm <specname>-fsm-override-transparent-p
        (fsm-overridekey-transparent-p
         (svtv-spec->fsm (<specname>))
         (<name>-overridekeys))
        :hints (("goal" :in-theory '(<specname>-def
                                     svtv-spec->fsm-of-svtv-data-obj->spec
                                     fsm-override-transparent-p-of-<data>))))))

     (:@ :triplecheck
        
      (defthm
        <name>-refines-<name>
        (b* ((spec-run (svtv-run (<name>) spec-pipe-env))
             (impl-run (svtv-run (<name>) pipe-env)))
          (implies
           (and
            (svtv-override-triplemaplist-envs-ok (<name>-triplemaplist)
                                                 pipe-env spec-pipe-env spec-run)
            (svex-env-<<= (svex-env-reduce (<name>-input-vars)
                                           pipe-env)
                          spec-pipe-env))
           (svex-env-<<= impl-run spec-run)))
        :hints
        (("goal"
          :in-theory
          '((:congruence
             set-equiv-implies-svex-envs-equivalent-svex-env-reduce-1)
            (:congruence svex-envs-similar-implies-equal-svex-env-<<=-1)
            (:congruence svex-envs-similar-implies-equal-svex-env-<<=-2)
            svex-envs-similar-implies-equal-svtv-override-triplemaplist-envs-ok-4
            (:definition not)
            (:rewrite <data>-correct)
            (:rewrite <data>-facts)
            (:rewrite svtv-run-of-<name>-is-svtv-spec-run-of-<specname>)
            (:rewrite syntax-check-of-<name>-triplemaplist)
            (:type-prescription len)
            (:type-prescription svex-env-<<=)
            svtv-spec->initst-alist-of-svtv-data-obj->spec
            svtv-spec->in-alists-of-svtv-data-obj->spec
            override-transparency-of-svtv-data-obj->spec
            fsm-override-transparent-p-of-<data>
            <data>-generalize-override-syntax-check
            <specname>-def
            svtv-spec->fsm-of-svtv-data-obj->spec
            (svex-envlist-all-keys)
            (svarlist-nonoverride-p))
          :do-not-induct t)))

      (:@ :svtv-spec
       (defthm
         <specname>-refines-<name>
         (b* ((spec-run (svtv-spec-run (<specname>) spec-pipe-env 
                                       :base-ins spec-base-ins
                                       :initst spec-initst))
              (impl-run (svtv-run (<name>) pipe-env)))
           (implies
            (and
             (svtv-override-triplemaplist-envs-ok (<name>-triplemaplist)
                                                  pipe-env spec-pipe-env spec-run)
             (svex-env-<<= (svex-env-reduce (<name>-input-vars)
                                            pipe-env)
                           spec-pipe-env)
             (svarlist-nonoverride-p (svex-envlist-all-keys spec-base-ins) :test))
            (svex-env-<<= impl-run spec-run)))
         :hints
         (("goal"
           :in-theory
           '((:congruence
              set-equiv-implies-svex-envs-equivalent-svex-env-reduce-1)
             (:congruence svex-envs-similar-implies-equal-svex-env-<<=-1)
             (:congruence svex-envs-similar-implies-equal-svex-env-<<=-2)
             svex-envs-similar-implies-equal-svtv-override-triplemaplist-envs-ok-4
             (:definition not)
             (:rewrite <data>-correct)
             (:rewrite <data>-facts)
             (:rewrite svtv-run-of-<name>-is-svtv-spec-run-of-<specname>)
             (:rewrite syntax-check-of-<name>-triplemaplist)
             (:type-prescription len)
             (:type-prescription svex-env-<<=)
             svtv-spec->initst-alist-of-svtv-data-obj->spec
             svtv-spec->in-alists-of-svtv-data-obj->spec
             override-transparency-of-svtv-data-obj->spec
             fsm-override-transparent-p-of-<data>
             <data>-generalize-override-syntax-check
             <specname>-def
             svtv-spec->fsm-of-svtv-data-obj->spec
             (svex-envlist-all-keys)
             (svarlist-nonoverride-p))
           :do-not-induct t)))

       (defthm
         <specname>-refines-<specname>
         (b* ((spec-run (svtv-spec-run (<specname>) spec-pipe-env 
                                       :base-ins spec-base-ins
                                       :initst spec-initst))
              (impl-run (svtv-spec-run (<specname>) pipe-env)))
           (implies
            (and
             (svtv-override-triplemaplist-envs-ok (<name>-triplemaplist)
                                                  pipe-env spec-pipe-env spec-run)
             (svex-env-<<= (svex-env-reduce (<name>-input-vars)
                                            pipe-env)
                           spec-pipe-env)
             (svarlist-nonoverride-p (svex-envlist-all-keys spec-base-ins) :test))
            (svex-env-<<= impl-run spec-run)))
         :hints
         (("goal"
           :in-theory
           '((:congruence
              set-equiv-implies-svex-envs-equivalent-svex-env-reduce-1)
             (:congruence svex-envs-similar-implies-equal-svex-env-<<=-1)
             (:congruence svex-envs-similar-implies-equal-svex-env-<<=-2)
             svex-envs-similar-implies-equal-svtv-override-triplemaplist-envs-ok-4
             (:definition not)
             (:rewrite <data>-correct)
             (:rewrite <data>-facts)
             (:rewrite syntax-check-of-<name>-triplemaplist)
             (:type-prescription len)
             (:type-prescription svex-env-<<=)
             svtv-spec->initst-alist-of-svtv-data-obj->spec
             svtv-spec->in-alists-of-svtv-data-obj->spec
             override-transparency-of-svtv-data-obj->spec
             fsm-override-transparent-p-of-<data>
             <data>-generalize-override-syntax-check
             <specname>-def
             svtv-spec->fsm-of-svtv-data-obj->spec
             (svex-envlist-all-keys)
             (svarlist-nonoverride-p))
           :do-not-induct t)))))

     ;; (local (defthm <data>-syntax-checks
     ;;          (SVTV-SPEC-OVERRIDE-SYNTAX-CHECKS
     ;;           (SVTV-DATA-OBJ->IDEAL-SPEC (<DATA>))
     ;;           (SVTV-ASSIGNS-OVERRIDE-VARS
     ;;            (FLATNORM-RES->ASSIGNS (SVTV-DATA-OBJ->FLATNORM (<DATA>)))
     ;;            (PHASE-FSM-CONFIG->OVERRIDE-CONFIG
     ;;             (SVTV-DATA-OBJ->PHASE-FSM-SETUP (<DATA>))))
     ;;           (SVARLIST-CHANGE-OVERRIDE
     ;;            (SVTV-ASSIGNS-OVERRIDE-VARS
     ;;             (FLATNORM-RES->ASSIGNS (SVTV-DATA-OBJ->FLATNORM (<DATA>)))
     ;;             (PHASE-FSM-CONFIG->OVERRIDE-CONFIG
     ;;              (SVTV-DATA-OBJ->PHASE-FSM-SETUP (<DATA>))))
     ;;            :TEST)
     ;;           (<NAME>-TRIPLEMAPLIST))
     ;;          :hints (("goal" :in-theory '((<data>)
     ;;                                       svtv-data-obj->ideal-spec
     ;;                                       ))

     (:@ :svtv-spec
      (defret no-duplicate-state-keys-of-<specname>
        (no-duplicatesp-equal (svex-alist-keys (fsm->nextstate (svtv-spec->fsm spec))))
        :hints (("goal" :in-theory '(<data>-facts
                                     <data>-correct
                                     <specname>-def
                                     fields-of-svtv-data-obj->ideal-spec
                                     alist-keys-of-flatnorm->ideal-fsm
                                     svex-alist-keys-of-delays-of-flatnorm-add-overrides
                                     delays-of-design->flatnorm-of-svtv-data-obj))
                (and stable-under-simplificationp
                     '(:in-theory '(hons-dups-p-when-variable-free
                                    no-duplicatesp-by-hons-dups-p)))
                )
        :fn <specname>)

      (defret initst-keys-of-<specname>
        (equal (svex-alist-keys (svtv-spec->initst-alist spec))
               (svex-alist-keys (fsm->nextstate (svtv-spec->fsm spec))))
        :hints (("goal" :in-theory '(<data>-facts
                                     <data>-correct
                                     <specname>-def
                                     svtv-data-obj->spec
                                     svtv-spec->fsm-of-svtv-spec
                                     svtv-spec->initst-alist-of-svtv-spec
                                     fsm-fix-when-fsm-p
                                     fsm-p-of-svtv-data-obj->phase-fsm
                                     svex-alist-fix-when-svex-alist-p
                                     svex-alist-p-of-pipeline-setup->initst))
                (and stable-under-simplificationp
                     '(:in-theory '((<data>)
                                    (svex-alist-keys)
                                    (pipeline-setup->initst)
                                    (fsm->nextstate)
                                    (svtv-data-obj->phase-fsm)
                                    (svtv-data-obj->pipeline-setup))))
                )
        :fn <specname>)

      (defret probe-keys-of-<specname>
        (equal (alist-keys (svtv-spec->probes spec))
               (svex-alist-keys (svtv->outexprs (<name>))))
        :hints (("goal" :in-theory '(<data>-facts
                                     <data>-correct
                                     <specname>-def
                                     svtv-data-obj->spec
                                     svtv-spec->probes-of-svtv-spec
                                     svtv-probealist-fix-when-svtv-probealist-p
                                     svtv-probealist-p-of-pipeline-setup->probes))
                (and stable-under-simplificationp
                     '(:in-theory '((<data>)
                                    (<name>)
                                    (svtv->outexprs)
                                    (svex-alist-keys)
                                    (alist-keys)
                                    (pipeline-setup->probes)
                                    (svtv-data-obj->pipeline-setup)))))
        :fn <specname>)

      (defret cycle-outputs-captured-of-<specname>
        (svtv-cyclephaselist-has-outputs-captured
         (svtv-spec->cycle-phases spec))
        :hints (("goal" :in-theory '(<data>-facts
                                     <data>-correct
                                     <specname>-def
                                     svtv-data-obj->spec
                                     svtv-spec->cycle-phases-of-svtv-spec
                                     svtv-cyclephaselist-fix-when-svtv-cyclephaselist-p
                                     svtv-cyclephaselist-p-of-svtv-data-obj->cycle-phases))
                (and stable-under-simplificationp
                     '(:in-theory '((<data>)
                                    (svtv-data-obj->cycle-phases)
                                    (svtv-cyclephaselist-has-outputs-captured)))))
        :fn <specname>)

      (defthm nextstate-keys-non-override-of-<specname>
        (svarlist-override-p (svex-alist-keys (fsm->nextstate (svtv-spec->fsm (<specname>)))) nil)
        :hints(("Goal" :in-theory '((<specname>)
                                    (svtv-spec->fsm)
                                    (fsm->nextstate)
                                    (svex-alist-keys)
                                    (svarlist-override-p)))))

      (defthm fsm-overridekey-transparent-p-of-<specname>-cycle
        (fsm-overridekey-transparent-p
         (svtv-spec->cycle-fsm (<specname>))
         (<name>-overridekeys))
        :hints(("Goal" :in-theory '(svtv-spec->cycle-fsm
                                    fsm-overridekey-transparent-p-of-fsm-to-cycle
                                    <specname>-fsm-override-transparent-p
                                    <specname>-facts
                                    nextstate-keys-non-override-of-<specname>))))

      (defthm fsm-ovcongruent-of-<specname>
        (fsm-ovcongruent (svtv-spec->fsm (<specname>)))
        :hints(("Goal" :in-theory '(<specname>-def
                                    fsm-ovcongruent-of-svtv-data-obj->phase-fsm
                                    <data>-correct
                                    <data>-facts
                                    svtv-spec->fsm-of-svtv-data-obj->spec))))

      (defthm fsm-ovcongruent-of-<specname>-cycle
        (fsm-ovcongruent (svtv-spec->cycle-fsm (<specname>)))
        :hints(("Goal" :in-theory '(svtv-spec->cycle-fsm
                                    fsm-ovcongruent-of-<specname>
                                    fsm-ovcongruent-p-of-fsm-to-cycle
                                    <specname>-facts
                                    nextstate-keys-non-override-of-<specname>))))
                              
  
      (defthm svtv-spec-fsm-syntax-check-of-<specname>
        (svtv-spec-fsm-syntax-check (<specname>))
        :hints(("Goal" :in-theory '((<specname>)
                                    (svtv-spec-fsm-syntax-check)))))



      (defthm svex-alist-all-xes-of-<specname>-initst
        (svex-alist-all-xes-p (svtv-spec->initst-alist (<specname>)))
        :hints(("Goal" :in-theory '((svex-alist-all-xes-p)
                                    (svtv-spec->initst-alist)
                                    (<specname>)))))

      (defthm svarlist-nonoverride-test-of-<specname>-cyclephaselist-keys
        (svarlist-nonoverride-p (svtv-cyclephaselist-keys (svtv-spec->cycle-phases (<specname>))) :test)
        :hints(("Goal" :in-theory '((<specname>)
                                    (svtv-spec->cycle-phases)
                                    (svtv-cyclephaselist-keys)
                                    (svarlist-nonoverride-p))))))

     
     (:@ :ideal
      (defret no-duplicate-state-keys-of-<ideal-name>
        (no-duplicatesp-equal (svex-alist-keys (fsm->nextstate (svtv-spec->fsm spec))))
        :hints (("goal" :in-theory '(<data>-facts
                                     <data>-correct
                                     <ideal-name>
                                     design->ideal-fsm
                                     fields-of-svtv-data-obj->ideal-spec
                                     alist-keys-of-flatnorm->ideal-fsm
                                     svex-alist-keys-of-delays-of-flatnorm-add-overrides
                                     delays-of-design->flatnorm-of-svtv-data-obj))
                (and stable-under-simplificationp
                     '(:in-theory '(hons-dups-p-when-variable-free
                                    no-duplicatesp-by-hons-dups-p)))
                )
        :fn <ideal-name>)

      (defret initst-keys-of-<ideal-name>
        (equal (svex-alist-keys (svtv-spec->initst-alist spec))
               (svex-alist-keys (fsm->nextstate (svtv-spec->fsm spec))))
        :hints (("goal" :in-theory '(<data>-facts
                                     <data>-correct
                                     <ideal-name>
                                     design->ideal-fsm
                                     fields-of-svtv-data-obj->ideal-spec
                                     alist-keys-of-flatnorm->ideal-fsm
                                     svex-alist-keys-of-delays-of-flatnorm-add-overrides
                                     delays-of-design->flatnorm-of-svtv-data-obj))
                (and stable-under-simplificationp
                     '(:in-theory '((<data>)
                                    (flatnorm-res->delays)
                                    (svex-alist-keys)
                                    (svtv-data-obj->flatnorm)
                                    (pipeline-setup->initst)
                                    (svtv-data-obj->pipeline-setup)))))
        :fn <ideal-name>)

      (defret probe-keys-of-<ideal-name>
        (equal (alist-keys (svtv-spec->probes spec))
               (svex-alist-keys (svtv->outexprs (<name>))))
        :hints (("goal" :in-theory '(<data>-facts
                                     <data>-correct
                                     <ideal-name>
                                     design->ideal-fsm
                                     fields-of-svtv-data-obj->ideal-spec
                                     alist-keys-of-flatnorm->ideal-fsm
                                     svex-alist-keys-of-delays-of-flatnorm-add-overrides
                                     delays-of-design->flatnorm-of-svtv-data-obj))
                (and stable-under-simplificationp
                     '(:in-theory '((<data>)
                                    (<name>)
                                    (svtv->outexprs)
                                    (svex-alist-keys)
                                    (alist-keys)
                                    (pipeline-setup->probes)
                                    (svtv-data-obj->pipeline-setup)))))
        :fn <ideal-name>)

      (defret cycle-outputs-captured-of-<ideal-name>
        (svtv-cyclephaselist-has-outputs-captured
         (svtv-spec->cycle-phases spec))
        :hints (("goal" :in-theory '(<ideal-name>
                                     fields-of-svtv-data-obj->ideal-spec
                                     (svtv-data-obj->cycle-phases)
                                     (svtv-cyclephaselist-has-outputs-captured)
                                     (<data>))))
        :fn <ideal-name>)



      (defret <ideal-name>-refines-<name>
        (b* (((svtv-spec spec))
             (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
             (impl-run (svtv-run (<name>) pipe-env)))
          (implies (and
                    (svtv-override-triplemaplist-envs-ok (<name>-triplemaplist) pipe-env spec-pipe-env spec-run)

                    (svex-env-<<= (svex-env-reduce (<name>-input-vars) pipe-env)
                                  spec-pipe-env)
                    (svarlist-nonoverride-p (svex-envlist-all-keys spec-base-ins) :test))
                   (svex-env-<<= impl-run spec-run)))
        :hints(("Goal" :in-theory '((:CONGRUENCE
                                     SET-EQUIV-IMPLIES-SVEX-ENVS-EQUIVALENT-SVEX-ENV-REDUCE-1)
                                    (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
                                    (:DEFINITION <IDEAL-NAME>)
                                    <specname>-def
                                    (:DEFINITION NOT)
                                    (:REWRITE <DATA>-CORRECT)
                                    (:REWRITE <DATA>-FACTS)
                                    ;; (:REWRITE SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-SPEC-RUN)
                                    (:REWRITE
                                     SVTV-RUN-OF-<NAME>-IS-SVTV-SPEC-RUN-OF-<SPECNAME>)
                                    (:REWRITE SYNTAX-CHECK-OF-<NAME>-TRIPLEMAPLIST)
                                    (:TYPE-PRESCRIPTION LEN)
                                    (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
                                    svtv-spec->initst-alist-of-svtv-data-obj->spec
                                    svtv-spec->in-alists-of-svtv-data-obj->spec
                                    OVERRIDE-TRANSPARENCY-OF-SVTV-DATA-OBJ->SPEC/IDEAL-SPEC-ABSTRACTION
                                    <DATA>-OVERRIDE-SYNTAX-CHECK
                                    ;; (:TYPE-PRESCRIPTION SVTV-OVERRIDE-TRIPLEMAPLIST-OK)
                                    )
                :do-not-induct t))
        :fn <ideal-name>)

      (defret <ideal-name>-refines-<ideal-name>
        (b* (((svtv-spec spec))
             (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
             (impl-run (svtv-spec-run spec pipe-env)))
          (implies (and
                    (svtv-override-triplemaplist-envs-ok (<name>-triplemaplist) pipe-env spec-pipe-env spec-run)

                    (svex-env-<<= (svex-env-reduce (<name>-input-vars) pipe-env)
                                  spec-pipe-env)
                    (svarlist-nonoverride-p (svex-envlist-all-keys spec-base-ins) :test))
                   (svex-env-<<= impl-run spec-run)))
        :hints(("Goal" :in-theory '((:CONGRUENCE
                                     SET-EQUIV-IMPLIES-SVEX-ENVS-EQUIVALENT-SVEX-ENV-REDUCE-1)
                                    (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
                                    (:DEFINITION <IDEAL-NAME>)
                                    <specname>-def
                                    (:DEFINITION NOT)
                                    (:REWRITE <DATA>-CORRECT)
                                    (:REWRITE <DATA>-FACTS)
                                    ;; (:REWRITE SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-IDEAL-SPEC-RUN)
                                    (:REWRITE
                                     SVTV-RUN-OF-<NAME>-IS-SVTV-SPEC-RUN-OF-<SPECNAME>)
                                    (:REWRITE SYNTAX-CHECK-OF-<NAME>-TRIPLEMAPLIST)
                                    (:TYPE-PRESCRIPTION LEN)
                                    (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
                                    OVERRIDE-TRANSPARENCY-OF-SVTV-DATA-OBJ->IDEAL-SPEC
                                    svtv-spec->initst-alist-of-svtv-data-obj->ideal-spec
                                    svtv-spec->in-alists-of-svtv-data-obj->ideal-spec
                                    <DATA>-IDEAL-OVERRIDE-SYNTAX-CHECK
                                    ;; (:TYPE-PRESCRIPTION SVTV-OVERRIDE-TRIPLEMAPLIST-OK)
                                    )
                :do-not-induct t))
        :fn <ideal-name>)

      (defret <ideal-name>-refines-<name>-on-same-envs
        (b* ((spec-run (svtv-spec-run spec pipe-env :base-ins spec-base-ins :initst spec-initst))
             (impl-run (svtv-run (<name>) pipe-env)))
          (implies (svarlist-nonoverride-p (svex-envlist-all-keys spec-base-ins) :test)
                   (svex-env-<<= impl-run spec-run)))
        :hints (("goal" :in-theory '(<ideal-name>-refines-<name>
                                     svtv-override-triplemaplist-envs-ok-of-same-envs
                                     svex-env-reduce-<<=-same
                                     (svex-envlist-all-keys)
                                     (svarlist-nonoverride-p))))
        :fn <ideal-name>)

      (defret <ideal-name>-refines-<ideal-name>-on-same-envs
        (b* (((svtv-spec spec))
             (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
             (impl-run (svtv-spec-run spec spec-pipe-env)))
          (implies (svarlist-nonoverride-p (svex-envlist-all-keys spec-base-ins) :test)
                   (svex-env-<<= impl-run spec-run)))
        :hints (("goal" :in-theory '(<ideal-name>-refines-<ideal-name>
                                     svtv-override-triplemaplist-envs-ok-of-same-envs
                                     svex-env-reduce-<<=-same
                                     (svex-envlist-all-keys)
                                     (svarlist-nonoverride-p))))
        :fn <ideal-name>)

      (define <ideal-name>-exec ((env svex-env-p)
                                 (output-vars svarlist-p))
        :enabled t
        :guard-hints (("goal" :use ((:instance <ideal-name>-refines-<name>-on-same-envs
                                     (pipe-env env) (spec-base-ins nil) (spec-initst nil)))
                       :in-theory '(svex-alist-eval-of-fal-extract
                                    svex-alist-p-of-svtv->outexprs
                                    svex-env-fix-when-svex-env-p
                                    keys-of-svtv-spec-run
                                    (svex-env-p)
                                    (svex-envlist-p)
                                    (svex-envlist-all-keys)
                                    (svarlist-nonoverride-p)
                                    svtv-run
                                    svtv-p-of-<name>
                                    svtv-spec-p-of-<ideal-name>
                                    svex-env-p-of-svex-alist-eval
                                    alist-keys-of-svex-alist-eval
                                    (make-fast-alist)
                                    make-fast-alist
                                    return-type-of-svex-alist-eval-for-symbolic
                                    svex-alist-eval-of-svex-env-fix-env
                                    svex-env-p-of-svtv-spec-run
                                    acl2::hons-dups-p-no-duplicatesp
                                    no-duplicate-state-keys-of-<ideal-name>
                                    initst-keys-of-<ideal-name>
                                    probe-keys-of-<ideal-name>
                                    cycle-outputs-captured-of-<ideal-name>
                                    svarlist-p-when-not-consp
                                    svex-env-reduce-of-nil
                                    svex-env-p-of-svex-env-reduce
                                    svex-env-reduce-when-svex-env-non-x-p-and-<<=
                                    )))
        :hooks ((:fix :hints (("goal" :in-theory '(SVTV-SPEC-RUN-FN-OF-SVEX-ENV-FIX-PIPE-ENV
                                                   svex-env-reduce-of-svarlist-fix-keys
                                                   <ideal-name>-exec)))))
        (mbe :logic (sv::svex-env-reduce output-vars
                                         (sv::svtv-spec-run (<ideal-name>) env))
             :exec (b* ((run (and (consp output-vars)
                                  (sv::svtv-run (<name>) env :include output-vars)))
                        ((when (sv::svex-env-non-x-p run)) run))
                     (sv::svex-env-reduce output-vars
                                          (sv::svtv-spec-run (<ideal-name>) env))))
        ///
        (fgl::remove-fgl-rewrite <ideal-name>-exec)
        (fgl::disable-execution <ideal-name>-exec)

        (fgl::def-fgl-rewrite <ideal-name>-exec-fgl
          (equal (<ideal-name>-exec env output-vars)
                 (b* ((run (and (consp output-vars)
                                (sv::svtv-run (<name>) (svex-env-fix env)
                                              :include (svarlist-fix output-vars))))
                      ((when (sv::svex-env-non-x-p run)) run))
                   (sv::svex-env-reduce output-vars
                                        (sv::svtv-spec-run (<ideal-name>) env))))
          :hints (("goal"
                   :use ((:instance <ideal-name>-refines-<name>-on-same-envs
                          (pipe-env env) (spec-base-ins nil) (spec-initst nil)))
                   :in-theory '(<ideal-name>-exec
                                svex-alist-eval-of-fal-extract
                                svex-alist-p-of-svtv->outexprs
                                svarlist-fix-under-iff
                                svex-env-fix-when-svex-env-p
                                svarlist-p-of-svarlist-fix
                                keys-of-svtv-spec-run
                                (svex-env-p)
                                (svex-envlist-p)
                                (svex-envlist-all-keys)
                                (svarlist-nonoverride-p)
                                svtv-run
                                svtv-p-of-<name>
                                svtv-spec-p-of-<ideal-name>
                                svex-env-p-of-svex-alist-eval
                                alist-keys-of-svex-alist-eval
                                (make-fast-alist)
                                make-fast-alist
                                return-type-of-svex-alist-eval-for-symbolic
                                svex-alist-eval-of-svex-env-fix-env
                                svex-env-p-of-svtv-spec-run
                                acl2::hons-dups-p-no-duplicatesp
                                no-duplicate-state-keys-of-<ideal-name>
                                initst-keys-of-<ideal-name>
                                probe-keys-of-<ideal-name>
                                cycle-outputs-captured-of-<ideal-name>
                                svarlist-p-when-not-consp
                                svex-env-reduce-of-nil
                                svex-env-reduce-of-svarlist-fix-keys
                                svex-env-p-of-svex-env-reduce
                                svex-env-reduce-when-svex-env-non-x-p-and-<<=
                                svex-env-reduce-when-not-consp
                                ))))))

     (:@ (and :svtv-spec :fsm)
      (:@ :define-fsm
       (define <fsmname> ()
         :guard-hints (("goal" :in-theory '(acl2::hons-dups-p-no-duplicatesp
                                            no-duplicate-state-keys-of-<specname>
                                            svtv-spec-p-of-<specname>)))
         :returns (cycle fsm-p
                         :hints (("goal" :in-theory '(fsm-p-of-svtv-spec->cycle-fsm
                                                      <fsmname>))))
         (svtv-spec->cycle-fsm (<specname>))
         ///
         ;; Associate the svtv-spec with this FSM in the svtv-spec-to-fsm-table
         ;; and vice versa in the fsm-to-svtv-spec table
         (table svtv-spec-to-fsm-table '<specname> '<fsmname>)
         (table fsm-to-svtv-spec-table '<fsmname> '<specname>)
         (in-theory (disable (<fsmname>)))
         
         (defthm cycle-fsm-of-<specname>
           (equal (svtv-spec->cycle-fsm (<specname>))
                  (<fsmname>))
           :hints(("Goal" :in-theory (disable (<specname>)))))

         (defthm fsm-overridekey-transparent-p-of-<fsmname>-wrt-<name>-overridekeys
           (fsm-overridekey-transparent-p
            (<fsmname>)
            (<name>-overridekeys))
           :hints(("Goal" :in-theory '(fsm-overridekey-transparent-p-of-<specname>-cycle
                                       <fsmname>))))

         (defthm fsm-ovcongruent-of-<fsmname>
           (fsm-ovcongruent (<fsmname>))
           :hints(("Goal" :in-theory '(fsm-ovcongruent-of-<specname>-cycle
                                       <fsmname>))))

         (defthm no-duplicate-state-keys-of-<fsmname>
           (no-duplicatesp-equal (svex-alist-keys (fsm->nextstate (<fsmname>))))
           :hints (("goal" :in-theory '(NEXTSTATE-KEYS-OF-SVTV-SPEC->CYCLE-FSM
                                        <fsmname>
                                        no-duplicate-state-keys-of-<specname>))))

         (defthm nextstate-keys-non-override-of-<fsmname>
           (svarlist-override-p (svex-alist-keys (fsm->nextstate (<fsmname>))) nil)
           :hints(("Goal" :in-theory '(nextstate-keys-non-override-of-<specname>
                                       nextstate-keys-of-svtv-spec->cycle-fsm
                                       <fsmname>))))))

      (:@ (not :define-fsm)
       (defthm cycle-fsm-of-<specname>
         (equal (svtv-spec->cycle-fsm (<specname>))
                (<fsmname>))
         :hints(("Goal" :in-theory `(svtv-spec->cycle-fsm
                                     (<specname>)
                                     (svtv-spec->fsm)
                                     (svtv-spec->cycle-phases)
                                     <fsmname>
                                     ,@(let ((spec (cdr (assoc '<fsmname> (table-alist 'fsm-to-svtv-spec-table world)))))
                                         (and spec `((,spec))))
                                     . ,'((:@ :phase-fsm (<phase-fsm>))
                                          (:@ (not :phase-fsm)
                                           (svtv-data-obj->phase-fsm)
                                           (<data>)))))))
       
       (table svtv-spec-to-fsm-table '<specname> '<fsmname>)

       (defthm fsm-overridekey-transparent-p-of-<fsmname>-wrt-<name>-overridekeys
         (fsm-overridekey-transparent-p
          (<fsmname>)
          (<name>-overridekeys))
         :hints(("Goal" :in-theory '(
                                     cycle-fsm-of-<specname>)
                 :use fsm-overridekey-transparent-p-of-<specname>-cycle))))
      
      (define <name>-fsm-bindings ()
        :returns (bindings lhprobe-map-p
                           :hints (("goal" :in-theory '(lhprobe-map-p-of-svtv-spec-fsm-bindings
                                                        <name>-fsm-bindings))))
        :guard-hints (("goal" :in-theory '(svtv-spec-fsm-syntax-check-of-<specname>
                                           svtv-spec-p-of-<specname>)))
        (svtv-spec-fsm-bindings (<specname>)))

      (define <name>-fsm-constraints ()
        :returns (constrants lhprobe-constraintlist-p
                             :hints (("goal" :in-theory '(lhprobe-constraintlist-p-of-svtv-spec-fsm-constraints
                                                          <name>-fsm-constraints))))
        :guard-hints (("goal" :in-theory '(svtv-spec-fsm-syntax-check-of-<specname>
                                           svtv-spec-p-of-<specname>)))
        (svtv-spec-fsm-constraints (<specname>))
        ///
        (make-event
         `(defthm max-stage-of-<name>-fsm-constraints
            (equal (lhprobe-constraintlist-max-stage (<name>-fsm-constraints))
                   ,(lhprobe-constraintlist-max-stage (<name>-fsm-constraints)))
            :hints(("Goal" :in-theory '((<name>-fsm-constraints)
                                        (lhprobe-constraintlist-max-stage)))))))

      (make-event
       `(defthm outvars-len-of-<specname>
          (equal (len (svtv-probealist-outvars (svtv-spec->probes (<specname>))))
                 ,(len (svtv-probealist-outvars (svtv-spec->probes (<specname>)))))
          :hints(("Goal" :in-theory '((<specname>)
                                      (svtv-spec->probes)
                                      (svtv-probealist-outvars)
                                      (len))))))

      (define <name>-fsm-output-map ()
        :returns (map lhprobe-map-p
                      :hints (("goal" :in-theory '(lhprobe-map-p-of-svtv-probealist-to-lhprobe-map
                                                   <name>-fsm-output-map))))
        :guard-hints (("goal" :in-theory '(svtv-probealist-p-of-svtv-spec->probes
                                           svtv-name-lhs-map-p-of-svtv-spec->namemap
                                           svtv-spec-p-of-<specname>)))
        (b* (((svtv-spec x) (<specname>))
             ((acl2::with-fast x.namemap)))
          (svtv-probealist-to-lhprobe-map x.probes x.namemap))
        ///
        (make-event
         `(defthm svtv-spec-cycle-outs->pipe-out-of-<specname>
            (implies (and (hons-get (svar-fix var) (<name>-fsm-output-map))
                          (<= ,(len (svtv-probealist-outvars (svtv-spec->probes (<specname>))))
                              (len outs)))
                     (equal (svex-env-lookup var (svtv-spec-cycle-outs->pipe-out (<specname>) outs))
                            (lhprobe-eval (cdr (hons-assoc-equal (svar-fix var) (<name>-fsm-output-map))) outs)))
            :hints(("Goal" :in-theory '((:DEFINITION <NAME>-FSM-OUTPUT-MAP)
                                        (:DEFINITION HONS-GET)
                                        (:REWRITE CDR-CONS)
                                        (:REWRITE LOOKUP-IN-SVTV-SPEC-CYCLE-OUTS->PIPE-OUT)
                                        (:REWRITE LOOKUP-OF-SVTV-PROBEALIST-TO-LHPROBE-MAP)
                                        (:REWRITE MAYBE-SVAR-P-P-WHEN-SVAR-P)
                                        (:REWRITE OUTVARS-LEN-OF-<SPECNAME>)
                                        (:REWRITE SVAR-P-OF-SVAR-FIX)
                                        (:REWRITE SVAR-P-WHEN-MAYBE-SVAR-P-P)
                                        (:REWRITE SVTV-PROBEALIST-FIX-WHEN-SVTV-PROBEALIST-P)
                                        (:REWRITE SVTV-PROBEALIST-P-OF-SVTV-SPEC->PROBES)
                                        (:REWRITE SVTV-SPEC-FSM-SYNTAX-CHECK-IMPLIES-PROBE-VARS-SUBSET-OF-NAMEMAP)
                                        (:REWRITE SVTV-SPEC-FSM-SYNTAX-CHECK-OF-<SPECNAME>))))))))))


(defun def-svtv-refinement-fn (svtv-name
                               data-name
                               fsm-name
                               phase-fsm-name
                               ideal
                               fgl-semantic-check
                               omit-default-aignet-transforms
                               svtv-spec
                               inclusive-overridekeys
                               define-fsm
                               pkg-sym)
  (declare (xargs :mode :program))
  (acl2::template-subst *svtv-generalize-template*
                        :str-alist `(("<NAME>" . ,(symbol-name svtv-name))
                                     ("<FSMNAME>" . ,(symbol-name fsm-name))
                                     ("<PHASE-FSM>" . ,(symbol-name phase-fsm-name))
                                     ("<DATA>" . ,(symbol-name data-name))
                                     ("<IDEAL-NAME>" . ,(symbol-name ideal))
                                     ("<SPECNAME>" . ,(if (and svtv-spec
                                                               (not (eq svtv-spec t)))
                                                          (symbol-name svtv-spec)
                                                        (concatenate 'string (symbol-name svtv-name) "-SPEC"))))
                        :atom-alist (and phase-fsm-name
                                         `((<phase-fsm> . ,phase-fsm-name)))
                        :features (append (if ideal
                                              '(:ideal)
                                            '(:triplecheck))
                                          (and phase-fsm-name '(:phase-fsm))
                                          (and fsm-name '(:fsm))
                                          (and define-fsm '(:define-fsm))
                                          (and fgl-semantic-check
                                               '(:fgl-semantic-check))
                                          (and svtv-spec '(:svtv-spec))
                                          (and (not omit-default-aignet-transforms)
                                               '(:default-aignet-transforms))
                                          (and inclusive-overridekeys
                                               '(:inclusive-overridekeys)))
                        :pkg-sym (or pkg-sym ideal svtv-name)))

(defmacro def-svtv-refinement (svtv-name data-name
                                         &key
                                         fsm
                                         phase-fsm
                                         define-fsm
                                         ideal fgl-semantic-check
                                         omit-default-aignet-transforms
                                         svtv-spec
                                         inclusive-overridekeys pkg-sym)
  `(make-event
    (def-svtv-refinement-fn ',svtv-name ',data-name ',fsm ',phase-fsm ',ideal ',fgl-semantic-check
      ',omit-default-aignet-transforms
      ',svtv-spec ',inclusive-overridekeys ',define-fsm ',pkg-sym)))



(defmacro def-svtv-ideal (ideal-name svtv-name data-name &key pkg-sym svtv-spec inclusive-overridekeys)
  `(make-event
    (def-svtv-refinement-fn ',svtv-name ',data-name nil nil ',ideal-name nil nil ',svtv-spec ',inclusive-overridekeys nil ',pkg-sym)))

(defmacro def-svtv-override-thms (name export &key pkg-sym svtv-spec inclusive-overridekeys)
  `(make-event
    (def-svtv-refinement-fn ',name ',export nil nil nil nil nil ',svtv-spec ',inclusive-overridekeys nil ',pkg-sym)))


;;; For each decomposition proof, we'll have a fixed set of signals overridden
;;; on both the spec and impl side.  On the spec side, this set of signals will
;;; likely be constant over several theorems that we want to compose together;
;;; this will be specified by svtv-override-triples-envs-match.  On the impl
;;; side, we'll have a more explicit env, not just a free variable with hyps
;;; but an alist constructed with cons/append/etc. We'll extract from this term
;;; a substitution which should contain all the constant bindings and bind all
;;; other variables to themselves, so that (svex-alist-eval subst env) ~= env.






(define svtv-override-subst-matches-env ((subst svex-alist-p)
                                         (env svex-env-p))
  :verify-guards nil
  (svex-envs-equivalent (svex-alist-eval subst env) env))


(defevaluator subst-matches-env-ev subst-matches-env-ev-list
  ((cons x y)
   (binary-append x y)
   (svtv-override-subst-matches-env subst env))
  :namedp t)

(acl2::def-ev-pseudo-term-fty-support subst-matches-env-ev subst-matches-env-ev-list)

(define svex-env-pair-term-extract-substitution ((x pseudo-termp))
  :returns (mv ok (subst svex-alist-p))
  (acl2::pseudo-term-case x
    :var (mv nil nil)
    :const (mv t (cond ((atom x.val) nil)
                       ((not (svar-p (car x.val))) nil)
                       (t (list (cons (car x.val) (ec-call (svex-quote (cdr x.val))))))))
    :lambda (mv nil nil)
    :fncall (case x.fn
              (cons (b* (((list car cdr) x.args))
                      (acl2::pseudo-term-case car
                        :const (mv t
                                   (and (svar-p car.val)
                                        (acl2::pseudo-term-case cdr
                                          :const (list (cons car.val (ec-call (svex-quote cdr.val))))
                                          :otherwise (list (cons car.val (svex-var car.val))))))
                        :otherwise (mv nil nil))))
              (otherwise (mv nil nil))))
  ///
  (defret true-listp-of-<fn>
    (true-listp subst) :rule-classes :type-prescription)


  (defret <fn>-matches-eval
    (implies ok
             (svex-envs-equivalent (svex-alist-eval subst (cons (subst-matches-env-ev x a) rest))
                                   (list (subst-matches-env-ev x a))))
    :hints(("Goal" :in-theory (enable svex-alist-eval
                                      svex-envs-equivalent
                                      svex-envs-similar
                                      svex-env-lookup
                                      svex-env-fix
                                      svex-eval))))

  (defret svex-lookup-of-<fn>
    (implies ok
             (iff (svex-lookup k subst)
                  (svex-env-boundp k (list (subst-matches-env-ev x a)))))
    :hints(("Goal" :in-theory (enable svex-env-boundp svex-lookup
                                      svex-env-fix))))



  (defret eval-svex-lookup-append-of-<fn>-when-not-boundp
    (implies (and ok
                  (not (svex-env-boundp k first)))
             (equal (svex-eval (svex-lookup k subst) (append first rest))
                    (svex-eval (svex-lookup k subst) rest)))
    :hints(("Goal" :in-theory (enable svex-lookup svex-eval))))

  (defret eval-svex-lookup-cons-of-<fn>-when-not-boundp
    (implies (and ok
                  (not (svex-env-boundp k (list first))))
             (equal (svex-eval (svex-lookup k subst) (cons first rest))
                    (svex-eval (svex-lookup k subst) rest)))
    :hints(("Goal" :in-theory (enable svex-lookup svex-env-lookup svex-env-boundp svex-eval)))))

(define svex-env-term-extract-substitution ((x pseudo-termp))
  :returns (mv ok (subst svex-alist-p))
  :measure (acl2::pseudo-term-count x)
  :verify-guards nil
  (acl2::pseudo-term-case x
    :var (mv nil nil)
    :const (mv t (ec-call (svex-env-to-subst x.val)))
    :lambda (mv nil nil)
    :fncall (case x.fn
              (cons
               (b* (((unless (eql (len x.args) 2)) (mv nil nil))
                    ((mv ok1 subst1) (svex-env-pair-term-extract-substitution (first x.args)))
                    ((mv ok2 subst2) (svex-env-term-extract-substitution (second x.args))))
                 (mv (and ok1 ok2) (append subst1 subst2))))
              (binary-append
               (b* (((unless (eql (len x.args) 2)) (mv nil nil))
                    ((mv ok1 subst1) (svex-env-term-extract-substitution (first x.args)))
                    ((mv ok2 subst2) (svex-env-term-extract-substitution (second x.args))))
                 (mv (and ok1 ok2) (append subst1 subst2))))
              (otherwise (mv nil nil))))

  ///
  (defret true-listp-of-<fn>
    (true-listp subst) :rule-classes :type-prescription)
  (verify-guards svex-env-term-extract-substitution)

  (local (defthm cdr-hons-assoc-equal-under-iff-when-svex-alist-p
           (implies (svex-alist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable svex-alist-p)))))

  (defret svex-lookup-of-<fn>
    (implies (and ok
                  (bind-free '((a . a)) (a)))
             (iff (svex-lookup k subst)
                  (svex-env-boundp k (subst-matches-env-ev x a))))
    :hints(("Goal" :in-theory (enable svex-env-boundp
                                      svex-env-fix))))


  (defret eval-svex-lookup-append-of-<fn>-when-not-boundp
    (implies (and ok
                  (not (svex-env-boundp k first)))
             (equal (svex-eval (svex-lookup k subst) (append first rest))
                    (svex-eval (svex-lookup k subst) rest))))

  (defret eval-svex-lookup-cons-of-<fn>-when-not-boundp
    (implies (and ok
                  (not (svex-env-boundp k (list first))))
             (equal (svex-eval (svex-lookup k subst) (cons first rest))
                    (svex-eval (svex-lookup k subst) rest))))

  (local (include-book "clause-processors/find-subterms" :dir :system))


  (local
   (progn
     (defun-sk fn-matches-eval-cond (x a)
       (forall rest
               (b* (((mv ok subst) (svex-env-term-extract-substitution x)))
                 (implies ok
                          (svex-envs-equivalent (svex-alist-eval subst (append (subst-matches-env-ev x a) rest))
                                                (subst-matches-env-ev x a)))))
       :rewrite :direct)

     (in-theory (disable fn-matches-eval-cond))


     (defthm true-list-fix-under-svex-envs-equivalent
       (svex-envs-equivalent (true-list-fix x) x)
       :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                         svex-env-lookup
                                         svex-env-boundp))))

     (defthm fn-matches-eval-cond-implies-special
       (implies (fn-matches-eval-cond x a)
                (b* (((mv ok subst) (svex-env-term-extract-substitution x)))
                  (implies ok
                           (svex-envs-equivalent (svex-alist-eval subst (subst-matches-env-ev x a))
                                                 (subst-matches-env-ev x a)))))
       :hints (("goal" :use ((:instance fn-matches-eval-cond-necc (rest nil)))
                :in-theory (disable fn-matches-eval-cond-necc))))

     (defthm fn-matches-cond-implies-eval-lookup
       (implies (fn-matches-eval-cond x a)
                (b* (((mv ok subst) (svex-env-term-extract-substitution x)))
                  (implies (and ok
                                (svex-lookup k subst))
                           (equal (svex-eval (svex-lookup k subst) (append (subst-matches-env-ev x a) rest))
                                  (svex-env-lookup k (subst-matches-env-ev x a))))))
       :hints (("goal" :use ((:instance svex-env-lookup-of-svex-alist-eval
                              (x (mv-nth 1 (svex-env-term-extract-substitution x)))
                              (env (append (subst-matches-env-ev x a) rest))))
                :in-theory (disable svex-env-lookup-of-svex-alist-eval))))

     (defthm my-svex-env-lookup-of-cons
       (equal (svex-env-lookup key (cons pair rest))
              (if (and (consp pair)
                       (svar-p (car pair))
                       (equal (svar-fix key) (car pair)))
                  (4vec-fix (cdr pair))
                (svex-env-lookup key rest)))
       :hints(("Goal" :in-theory (enable svex-env-lookup))))

     (defthm my-svex-env-boundp-of-cons
       (equal (svex-env-boundp key (cons pair rest))
              (if (and (consp pair)
                       (svar-p (car pair))
                       (equal (svar-fix key) (car pair)))
                  t
                (svex-env-boundp key rest)))
       :hints(("Goal" :in-theory (enable svex-env-boundp))))


     (defthm fn-matches-eval-lemma
       (fn-matches-eval-cond x a)
       :hints (("goal" :induct (svex-env-term-extract-substitution x)
                :in-theory (disable (:d svex-env-term-extract-substitution))
                :do-not-induct t)
               (and stable-under-simplificationp
                    `(:expand (,(car (last clause))
                               (svex-env-term-extract-substitution x)
                               (:free (env) (svex-alist-eval nil env)))))
               (and stable-under-simplificationp
                    (eq (caar (last clause)) 'svex-envs-equivalent)
                    `(:computed-hint-replacement
                      ((let ((call (acl2::find-call-lst 'svex-envs-equivalent-witness clause)))
                         (and call
                              `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badkey)))))))
                      :expand (,(car (last clause)))))))))

  (defret <fn>-matches-eval
    (implies ok
             (and (svex-envs-equivalent (svex-alist-eval subst (append (subst-matches-env-ev x a) rest))
                                        (subst-matches-env-ev x a))
                  (svex-envs-equivalent (svex-alist-eval subst (subst-matches-env-ev x a))
                                        (subst-matches-env-ev x a))))
    :hints (("goal" :do-not-induct t))))

(define svtv-override-subst-matches-env-metafn ((x pseudo-termp))
  :hooks nil
  (acl2::pseudo-term-case x
    :fncall (b* (((unless (and (eq x.fn 'svtv-override-subst-matches-env)
                               (equal (len x.args) 2)))
                  x)
                 ((list subst env) x.args)
                 ((unless (acl2::pseudo-term-case subst :const)) x)
                 ((mv extract-ok subst-extract)
                  (svex-env-term-extract-substitution env)))
              (if (and extract-ok (equal subst-extract (acl2::pseudo-term-const->val subst)))
                  ''t
                x))
    :otherwise x)
  ///
  (defthm svtv-override-subst-matches-env-meta
    (equal (subst-matches-env-ev x a)
           (subst-matches-env-ev (svtv-override-subst-matches-env-metafn x) a))
    :hints(("Goal" :in-theory (e/d (svtv-override-subst-matches-env)
                                   (svex-env-term-extract-substitution-matches-eval))
            :use ((:instance svex-env-term-extract-substitution-matches-eval
                   (x (second (acl2::pseudo-term-call->args x)))))))
    :rule-classes ((:meta :trigger-fns (svtv-override-subst-matches-env)))))











;; Now, find what assumptions we need satisfied about the spec result given (1)
;; the keys of the implementation env, and (2) the override-consts that the
;; spec-env satisfies (as in svtv-override-triplemaplist-envs-match).

;; Impl-subst in practice will be an svex-alist pairing variables with themselves
;; (other variables are assumed not to be bound).  But we could also bind
;; variables to constants if we know they will be bound that way in the
;; implementation env.

(defthm 4vec-muxtest-subsetp-of-neg1
  (4vec-muxtest-subsetp x -1)
  :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp))))

(defthm 4vec-muxtest-subsetp-when-1mask-0
  (implies (equal (4vec-1mask x) 0)
           (4vec-muxtest-subsetp x y))
  :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp))))



;; ;; Simplifying the svtv-override-triplemaplist-muxtests-subsetp.  We should
;; ;; concrete values for all the tests -- from the impl-env, we have the
;; ;; substitution with svtv-override-subst-matches-env, and from the spec-env, we
;; ;; have spec-override-consts.

;; ;; So for muxtests-subsetp, we should be able to just check these two envs by
;; ;; execution and not leave behind any further proof obligations.

;; (define svtv-override-test-check-muxtest-subsetp ((test svex-p)
;;                                                   (impl-subst svex-alist-p)
;;                                                   (spec-override-consts svex-env-p))
;;   :returns (ok)
;;   (b* (((when (svex-case test :quote))
;;         ;; Doesn't need to be checked because impl and spec test will both evaluate to the same.
;;         t)
;;        (spec-test (svex-eval test spec-override-consts))
;;        ((when (equal (4vec-1mask spec-test) 0))
;;         ;; Always satisfies 4vec-muxtest-subsetp
;;         t)
;;        (impl-test (svex-subst test impl-subst))
;;        ((when (equal impl-test (svex-quote (2vec -1))))
;;         ;; Always satisfies 4vec-muxtest-subsetp
;;         t))
;;     (svex-case impl-test
;;       :quote (or (4vec-muxtest-subsetp spec-test impl-test.val)
;;                  (cw "======  WARNING  =======~%~
;; Muxtest check failed: ~x0 evaluated to ~x1 (spec), ~x2 (impl) which does not satisfy ~x3~%"
;;                      test spec-test impl-test.val))
;;       :otherwise (cw "======  WARNING  =======~%~
;; Muxtest check failed: ~x0 evaluated to ~x1 (spec) but reduced to a non-constant for impl: ~x2~%"
;;                      test spec-test impl-test)))
;;   ///
;;   (defretd 4vec-muxtest-subsetp-when-<fn>
;;     :pre-bind ((test (svtv-override-triple->test triple)))
;;     (implies (and (svtv-override-triple-envs-match triple spec-env spec-override-consts)
;;                   (svtv-override-subst-matches-env impl-subst impl-env)
;;                   ok)
;;              (4vec-muxtest-subsetp (svex-eval test spec-env)
;;                                    (svex-eval test impl-env)))
;;     :hints(("Goal" :in-theory (e/d (svtv-override-triple-envs-match
;;                                     svtv-override-subst-matches-env)
;;                                    (svex-eval-of-svex-subst))
;;             :use ((:instance svex-eval-of-svex-subst
;;                    (pat (svtv-override-triple->test triple))
;;                    (al impl-subst)
;;                    (env impl-env)))))))


;; (define svtv-override-triplemap-check-muxtest-subsetp ((x svtv-override-triplemap-p)
;;                                                        (impl-subst svex-alist-p)
;;                                                        (spec-override-consts svex-env-p))
;;   :returns (ok)
;;   (if (atom x)
;;       t
;;     (and (or (not (mbt (and (consp (car x))
;;                             (svar-p (caar x)))))
;;              (svtv-override-test-check-muxtest-subsetp (svtv-override-triple->test (cdar x))
;;                                                        impl-subst spec-override-consts))
;;          (svtv-override-triplemap-check-muxtest-subsetp (cdr x) impl-subst spec-override-consts)))
;;   ///
;;   (defretd svex-envs-svexlist-muxtests-subsetp-when-<fn>
;;     (implies (and (svtv-override-triplemap-envs-match x spec-env spec-override-consts)
;;                   (svtv-override-subst-matches-env impl-subst impl-env)
;;                   ok)
;;              (svex-envs-svexlist-muxtests-subsetp (svtv-override-triplemap->tests x) spec-env impl-env))
;;     :hints(("Goal" :in-theory (e/d (svtv-override-triplemap-envs-match
;;                                     svex-envs-svexlist-muxtests-subsetp
;;                                     svtv-override-triplemap->tests
;;                                     4vec-muxtest-subsetp-when-svtv-override-test-check-muxtest-subsetp)))))

;;   (local (in-theory (enable svtv-override-triplemap-fix))))


;; (define svtv-override-triplemaplist-check-muxtest-subsetp ((x svtv-override-triplemaplist-p)
;;                                                            (impl-subst svex-alist-p)
;;                                                            (spec-override-consts svex-env-p))
;;   :returns (ok)
;;   (if (atom x)
;;       t
;;     (and (svtv-override-triplemap-check-muxtest-subsetp (car x) impl-subst spec-override-consts)
;;          (svtv-override-triplemaplist-check-muxtest-subsetp (cdr x) impl-subst spec-override-consts)))
;;   ///
;;   (defretd svtv-override-triplemaplist-muxtests-subsetp-when-<fn>
;;     (implies (and (svtv-override-triplemaplist-envs-match x spec-env spec-override-consts)
;;                   (svtv-override-subst-matches-env impl-subst impl-env)
;;                   ok)
;;              (svtv-override-triplemaplist-muxtests-subsetp x spec-env impl-env))
;;     :hints(("Goal" :in-theory (e/d (svtv-override-triplemaplist-envs-match
;;                                     svtv-override-triplemaplist-muxtests-subsetp
;;                                     svex-envs-svexlist-muxtests-subsetp-when-svtv-override-triplemap-check-muxtest-subsetp)))))

;;   ;; !!! This will be used to compute the list of tests that need to be
;;   ;; resolved when generalizing an SVTV theorem.
;;   (defthmd svtv-override-triplemaplist-muxtests-subsetp-simplify-for-idealize
;;     (implies (and (syntaxp (cmr::term-variable-free-p x))
;;                   (svtv-override-triplemaplist-envs-match x spec-env spec-override-consts)
;;                   (bind-free (b* (((mv ok subst) (svex-env-term-extract-substitution impl-env)))
;;                                (and ok
;;                                     `((impl-subst . ',(make-fast-alist subst)))))
;;                              (impl-subst))
;;                   (svtv-override-subst-matches-env impl-subst impl-env)
;;                   (svtv-override-triplemaplist-check-muxtest-subsetp x impl-subst (make-fast-alist spec-override-consts)))
;;              (svtv-override-triplemaplist-muxtests-subsetp x spec-env impl-env))
;;     :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-muxtests-subsetp-when-svtv-override-triplemaplist-check-muxtest-subsetp))))

;;   (cmr::def-force-execute svtv-override-triplemaplist-check-muxtest-subsetp-when-variable-free
;;     svtv-override-triplemaplist-check-muxtest-subsetp))









;; For resolving the svtv-override-triplemaplist-envs-ok check, we'll analyze
;; the known constants and produce a list of things we still need to check.
;; These will take the form of a svtv-override-checklist.  Each item to check
;; shows that a certain triplemap entry satisfies svtv-override-triple-envs-ok.



(defprod svtv-override-check
  ((impl-test svex-p)
   (impl-val svex-p)
   (spec-test svex-p)
   (spec-val svex-p)
   (refvar maybe-svar-p))
  :layout :list)


(deflist svtv-override-checklist :elt-type svtv-override-check :true-listp t)



  
                              


(define svtv-override-checklist-ok ((x svtv-override-checklist-p)
                                    (impl-env svex-env-p)
                                    (spec-env svex-env-p)
                                    (ref-env svex-env-p))
  :returns (ok)
  (if (atom x)
      t
    (and (b* (((svtv-override-check x1) (car x)))
           (mbe :logic
                (4vec-override-mux-ok  (svex-eval x1.impl-test impl-env)
                                  (svex-eval x1.impl-val impl-env)
                                  (svex-eval x1.spec-test spec-env)
                                  (svex-eval x1.spec-val spec-env)
                                  x1.refvar
                                  (svex-env-lookup x1.refvar ref-env))
                :exec
                (4vec-override-mux-ok  (svex-eval x1.impl-test impl-env)
                                  (svex-eval x1.impl-val impl-env)
                                  (svex-eval x1.spec-test spec-env)
                                  (svex-eval x1.spec-val spec-env)
                                  x1.refvar
                                  (if x1.refvar
                                      (svex-env-lookup x1.refvar ref-env)
                                    0))))
         (svtv-override-checklist-ok (cdr x) impl-env spec-env ref-env)))
  ///
  (defthm svtv-override-checklist-ok-of-cons-quote
    (implies (syntaxp (quotep x1))
             (equal (svtv-override-checklist-ok (cons x1 rest) impl-env spec-env ref-env)
                    (and (b* (((svtv-override-check x1)))
                           (4vec-override-mux-ok
                            (svex-case x1.impl-test
                              :quote x1.impl-test.val
                              :var (svex-env-lookup x1.impl-test.name impl-env)
                              :otherwise (svex-eval x1.impl-test impl-env))
                            (svex-case x1.impl-val
                              :quote x1.impl-val.val
                              :var (svex-env-lookup x1.impl-val.name impl-env)
                              :otherwise (svex-eval x1.impl-val impl-env))
                            (svex-case x1.spec-test
                              :quote x1.spec-test.val
                              :var (svex-env-lookup x1.spec-test.name spec-env)
                              :otherwise (svex-eval x1.spec-test spec-env))
                            (svex-case x1.spec-val
                              :quote x1.spec-val.val
                              :var (svex-env-lookup x1.spec-val.name spec-env)
                              :otherwise (svex-eval x1.spec-val spec-env))
                            x1.refvar
                            (svex-env-lookup x1.refvar ref-env)))
                         (svtv-override-checklist-ok rest impl-env spec-env ref-env))))
    :hints(("Goal" :in-theory (enable svex-eval))))

  (defthm svtv-override-checklist-ok-of-cons
    (equal (svtv-override-checklist-ok (cons x1 rest) impl-env spec-env ref-env)
           (and (b* (((svtv-override-check x1)))
                  (4vec-override-mux-ok (svex-eval x1.impl-test impl-env)
                                  (svex-eval x1.impl-val impl-env)
                                  (svex-eval x1.spec-test spec-env)
                                  (svex-eval x1.spec-val spec-env)
                                  x1.refvar
                                  (svex-env-lookup x1.refvar ref-env)))
                (svtv-override-checklist-ok rest impl-env spec-env ref-env))))

  (defthm svtv-override-checklist-ok-of-append
    (equal (svtv-override-checklist-ok (append x y) impl-env spec-env ref-env)
           (and (svtv-override-checklist-ok x impl-env spec-env ref-env)
                (svtv-override-checklist-ok y impl-env spec-env ref-env))))

  (defthm svtv-override-checklist-ok-of-nil
    (svtv-override-checklist-ok nil impl-env spec-env ref-env)))


(defthm 4vec-bit?!-when-test-empty
  (implies (equal (4vec-1mask test) 0)
           (equal (4vec-bit?! test then else) (4vec-fix else)))
  :hints(("Goal" :in-theory (e/d (4vec-bit?! 4vec-1mask 4vec-bitmux)
                                 (lognot logior)))))


(defthm 4vec-override-mux-<<=-when-impl-test-empty
  (implies (equal (4vec-1mask impl-test) 0)
           (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref))
  :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=))))

;; (defthm 4vec-override-mux-ok-when-impl-test-empty
;;   (implies (equal (4vec-1mask impl-test) 0)
;;            (4vec-override-mux-ok 0 impl-val spec-test spec-val spec-ref))
;;   :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=))))



(define svtv-override-triple-analyze-necessary-envs-ok-check ((x svtv-override-triple-p)
                                                              (impl-subst svex-alist-p)
                                                              (spec-override-consts svex-env-p))
  :returns (checks svtv-override-checklist-p)
  (b* (((svtv-override-triple x))
       ((when (and (svex-case x.test :quote)
                   (svex-case x.val :quote)))
        ;; Doesn't need to be checked because 4vec-override-mux-<<= of same tests and vals is always true.
        nil)
       (impl-test (svex-subst x.test impl-subst))
       (impl-val (svex-subst x.val impl-subst))
       (spec-test (svex-eval x.test spec-override-consts))
       (spec-val  (svex-eval x.val spec-override-consts))
       (spec-val-expr (if (2vec-p spec-val) (svex-quote spec-val) x.val))

       (mux-<<=-ok (or (and x.refvar
                            (svex-case impl-test :quote)
                            (equal (4vec-1mask (svex-quote->val impl-test)) 0))
                       (equal impl-val (svex-x))))
       (muxtest-ok (svex-case impl-test
                     :quote (or (if x.refvar
                                    (4vec-muxtest-subsetp spec-test impl-test.val)
                                  (equal spec-test impl-test.val))
                                (cw "======  WARNING  =======~%~
Muxtest check failed: ~x0 evaluated to ~x1 (spec), ~x2 (impl) which does not satisfy ~x3~%"
                                    x.test spec-test impl-test.val
                                    (if x.refvar '4vec-muxtest-subsetp 'equal)))
                     :otherwise
                     (or (and x.refvar (eql (4vec-1mask spec-test) 0))
                         (cw "======  WARNING  =======~%~
Muxtest check failed: ~x0 evaluated to ~x1 (spec) but reduced to a non-constant for impl: ~x2~%"
                             x.test spec-test impl-test))))
       ((when (and mux-<<=-ok muxtest-ok))
        nil))
    (list (svtv-override-check impl-test impl-val
                               (svex-quote spec-test)
                               spec-val-expr
                               x.refvar)))
  ///
  
  (defret <fn>-correct
    (implies (and (svtv-override-subst-matches-env impl-subst impl-env)
                  (svtv-override-triple-envs-match x spec-env spec-override-consts))
             (equal (svtv-override-checklist-ok checks impl-env spec-env ref-env)
                    (svtv-override-triple-envs-ok x impl-env spec-env ref-env)))
    :hints(("Goal" :in-theory (e/d (svtv-override-triple-envs-ok
                                    4vec-override-mux-ok
                                    svtv-override-triple-envs-match
                                    svtv-override-subst-matches-env)
                                   (svex-eval-of-svex-subst))
            :use ((:instance svex-eval-of-svex-subst
                   (pat (svtv-override-triple->test x))
                   (al impl-subst)
                   (env impl-env))
                  (:instance svex-eval-of-svex-subst
                   (pat (svtv-override-triple->val x))
                   (al impl-subst)
                   (env impl-env)))))))



(define svtv-override-triplemap-analyze-necessary-envs-ok-checks ((x svtv-override-triplemap-p)
                                                                  (impl-subst svex-alist-p)
                                                                  (spec-override-consts svex-env-p))
  :returns (checks svtv-override-checklist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-override-triplemap-analyze-necessary-envs-ok-checks (cdr x) impl-subst spec-override-consts))
       (checks1 (svtv-override-triple-analyze-necessary-envs-ok-check (cdar x) impl-subst spec-override-consts)))
    (mbe :logic (append checks1
                        (svtv-override-triplemap-analyze-necessary-envs-ok-checks (cdr x) impl-subst spec-override-consts))
         :exec (if checks1
                   (append checks1
                           (svtv-override-triplemap-analyze-necessary-envs-ok-checks (cdr x) impl-subst spec-override-consts))
                 (svtv-override-triplemap-analyze-necessary-envs-ok-checks (cdr x) impl-subst spec-override-consts))))
  ///
  (defret <fn>-correct
    (implies (and (svtv-override-subst-matches-env impl-subst impl-env)
                  (svtv-override-triplemap-envs-match x spec-env spec-override-consts))
             (equal (svtv-override-checklist-ok checks impl-env spec-env ref-env)
                    (svtv-override-triplemap-envs-ok x impl-env spec-env ref-env)))
    :hints(("Goal" :in-theory (e/d (svtv-override-triplemap-envs-ok
                                    svtv-override-triplemap-envs-match)))))

  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemaplist-analyze-necessary-envs-ok-checks ((x svtv-override-triplemaplist-p)
                                                                      (impl-subst svex-alist-p)
                                                                      (spec-override-consts svex-env-p))
  :returns (checks svtv-override-checklist-p)
  (if (atom x)
      nil
    (append (svtv-override-triplemap-analyze-necessary-envs-ok-checks (car x) impl-subst spec-override-consts)
            (svtv-override-triplemaplist-analyze-necessary-envs-ok-checks (cdr x) impl-subst spec-override-consts)))
  ///
  (defret <fn>-correct
    (implies (and (svtv-override-subst-matches-env impl-subst impl-env)
                  (svtv-override-triplemaplist-envs-match x spec-env spec-override-consts))
             (equal (svtv-override-checklist-ok checks impl-env spec-env spec-run)
                    (svtv-override-triplemaplist-envs-ok x impl-env spec-env spec-run)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-envs-ok
                                      svtv-override-triplemaplist-envs-match))))

  ;; !!! This will be used to compute the list of tests that need to be
  ;; resolved when generalizing an SVTV theorem.
  (defthmd svtv-override-triplemaplist-envs-ok-simplify-for-idealize
    (implies (and (syntaxp (cmr::term-variable-free-p x))
                  (svtv-override-triplemaplist-envs-match x spec-env spec-override-consts)
                  (bind-free (b* (((mv ok subst) (svex-env-term-extract-substitution impl-env)))
                               (and ok
                                    `((impl-subst . ',(make-fast-alist subst)))))
                             (impl-subst))
                  (svtv-override-subst-matches-env impl-subst impl-env))
             (equal (svtv-override-triplemaplist-envs-ok x impl-env spec-env spec-run)
                    (svtv-override-checklist-ok
                     (svtv-override-triplemaplist-analyze-necessary-envs-ok-checks x impl-subst (make-fast-alist spec-override-consts))
                     impl-env spec-env spec-run)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-analyze-necessary-envs-ok-checks-correct))))

  (cmr::def-force-execute svtv-override-triplemaplist-analyze-necessary-envs-ok-checks-when-variable-free
    svtv-override-triplemaplist-analyze-necessary-envs-ok-checks))









(defthm 4vec-bit?!-same-then-else
  (equal (4vec-bit?! test then then) (4vec-fix then))
  :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))
         (bitops::logbitp-reasoning)))


(defthm 4vec-override-mux-ok-when-no-spec-override-and-impl-val-same-as-ref
  (implies (and (equal (4vec-1mask spec-test) 0)
                val-p)
           (4vec-override-mux-ok impl-test val spec-test spec-val val-p val))
  :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=
                                    4vec-override-mux-ok))))



(def-ruleset! svtv-generalized-thm-rules
  '(
    (:CONGRUENCE
     CONS-4VEC-EQUIV-CONGRUENCE-ON-V-UNDER-SVEX-ENV-EQUIV)
    (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
    (:DEFINITION 4VEC-EQUIV$INLINE)
    (:definition svtv-override-triple-envs-ok)

    (:DEFINITION SVEX-ENV-FASTLOOKUP)
    (:DEFINITION SYNP)
    (:EXECUTABLE-COUNTERPART 2VEC-P$INLINE)
    (:EXECUTABLE-COUNTERPART 4VEC-<<=)
    (:EXECUTABLE-COUNTERPART 4VEC-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART ALIST-KEYS)
    (:executable-counterpart make-fast-alist)
    (:EXECUTABLE-COUNTERPART ACL2::HONS-DUPS-P)
    (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
    (:EXECUTABLE-COUNTERPART NFIX)
    (:EXECUTABLE-COUNTERPART SVAR-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART SVAR-P)
    (:EXECUTABLE-COUNTERPART SVARLIST-FILTER)
    (:EXECUTABLE-COUNTERPART SVEX-ENV-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-IDENTITY-SUBST)
    (:EXECUTABLE-COUNTERPART SVEX-KIND$INLINE)
    (:EXECUTABLE-COUNTERPART SVEX-VAR->NAME$INLINE)
    (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLE->REFVAR$INLINE)
    (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLE->TEST$INLINE)
    (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLE->VAL$INLINE)
    (:executable-counterpart svex-quote->val$inline)
    (:executable-counterpart svex-var->name$inline)
    (:executable-counterpart svtv-override-check->impl-test$inline)
    (:executable-counterpart svtv-override-check->impl-val$inline)
    (:executable-counterpart svtv-override-check->spec-test$inline)
    (:executable-counterpart svtv-override-check->spec-val$inline)
    (:executable-counterpart svtv-override-check->refvar$inline)
    (:executable-counterpart 4vec-1mask)
    (:executable-counterpart SVTV-OVERRIDE-TRIPLEMAPLIST-ANALYZE-NECESSARY-ENVS-OK-CHECKS)
    (:META HONS-INTERSECTION-FORCE-EXECUTE)
    (:meta svtv-override-triplemaplist-analyze-necessary-envs-ok-checks-when-variable-free)
    ;; (:meta svtv-override-triplemaplist-check-muxtest-subsetp-when-variable-free)
    (:meta svtv-override-subst-matches-env-meta)
    (:REWRITE 4VEC-<<=-2VEC)
    (:rewrite 4vec-<<=-self)

    (:REWRITE 4VEC-BIT?!-MONOTONIC-ON-NONTEST-ARGS)
    (:REWRITE 4VEC-FIX-OF-4VEC)
    (:REWRITE 4VEC-FIX-UNDER-4VEC-EQUIV)
    (:REWRITE 4VEC-P-OF-SVEX-ENV-LOOKUP)
    (:REWRITE ALIST-KEYS-OF-CONS)
    (:REWRITE ACL2::APPEND-OF-CONS)
    (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
    (:REWRITE CAR-CONS)
    (:REWRITE CDR-CONS)
    (:REWRITE SVARLIST-FIX-WHEN-SVARLIST-P)
    (:REWRITE SVEX-ENV-<<=-EACH-OF-CONS)
    (:REWRITE SVEX-ENV-<<=-EACH-OF-NIL)
    (:REWRITE
     SVEX-ENV-<<=-IS-SVEX-ENV-<<=-EACH-WHEN-NO-DUPLICATE-KEYS)
    (:REWRITE SVEX-ENV-<<=-NECC)
    (:REWRITE SVEX-ENV-<<=-SELF)
    (:REWRITE SVEX-ENV-EXTRACT-OF-CONS)
    (:REWRITE SVEX-ENV-EXTRACT-OF-NIL)
    (:REWRITE SVEX-ENV-FIX-OF-ACONS)
    (:REWRITE SVEX-ENV-LOOKUP-IN-SVTV-RUN-WITH-INCLUDE)
    (:REWRITE SVEX-ENV-LOOKUP-OF-CONS)
    (:REWRITE SVEX-ENV-LOOKUP-WHEN-INTEGERP-AND-<<=)
    (:REWRITE SVEX-ENV-REDUCE-OF-KNOWN-KEYS)
    (:REWRITE SVEX-EVAL-OF-QUOTED)
    ;; (:REWRITE SVTV-OVERRIDE-TRIPLELIST-MUXES-<<=-OF-CONS)
    ;; (:REWRITE SVTV-OVERRIDE-TRIPLELIST-MUXES-<<=-OF-NIL)

    (:rewrite svtv-override-checklist-ok-of-cons-quote)
    (:rewrite svtv-override-checklist-ok-of-nil)
    ;; (:rewrite svtv-override-triplemaplist-muxtests-subsetp-simplify-for-idealize)
    (:rewrite svtv-override-triplemaplist-envs-ok-simplify-for-idealize)
    ;; (:rewrite SVTV-OVERRIDE-TRIPLEMAPLIST-MUXES-<<=-SIMPLIFY-WHEN-KEYS)
    ;; (:rewrite SVTV-OVERRIDE-TRIPLELIST-MUXES-<<=-OF-CONS)
    ;; (:rewrite SVTV-OVERRIDE-TRIPLELIST-MUXES-<<=-OF-nil)

    (:rewrite 4VEC-OVERRIDE-MUX-OK-OF-SAME)
    (:rewrite 4VEC-OVERRIDE-MUX-<<=-OF-4vec-fix-impl-val)
    (:rewrite 4vec-override-MUX-ok-when-no-spec-override-and-impl-val-same-as-ref)

    (:rewrite svex-env-lookup-of-svex-env-reduce)
    (:executable-counterpart member-equal)
    (:executable-counterpart svarlist-fix$inline)
    4vec-override-mux-ok-of-4vec-fix-ref-val
    4vec-override-mux-ok-of-4vec-fix-spec-val
    4vec-override-mux-ok-of-4vec-fix-spec-test
    4vec-override-mux-ok-of-4vec-fix-impl-val
    4vec-override-mux-ok-of-4vec-fix-impl-test
    ))


;; Svtv-override-triplemaplist-envs-match shortcut.
;; Reduce svtv-override-triplemaplist-envs-match on a concrete spec and concrete-keyed env to a small set of checks.

(define svtv-override-triplelist-envs-match ((triplelist svtv-override-triplelist-p)
                                            (env svex-env-p)
                                            (spec svex-env-p))
  :returns (ok)
  (if (atom triplelist)
      t
    (and (svtv-override-triple-envs-match (car triplelist) env spec)
         (svtv-override-triplelist-envs-match (cdr triplelist) env spec)))
  ///
  (defthm svtv-override-triplelist-envs-match-of-cons-quote
    (implies (syntaxp (quotep first))
             (equal (svtv-override-triplelist-envs-match (cons first rest) env spec)
                    (and (b* (((svtv-override-triple first)))
                           (and (svex-case first.test
                                  :quote t
                                  :var (4vec-1mask-equiv (svex-env-lookup first.test.name env)
                                                         (svex-env-lookup first.test.name spec))
                                  :otherwise (4vec-1mask-equiv (svex-eval first.test env)
                                                               (svex-eval first.test spec)))
                                (svex-case first.val
                                  :quote t
                                  :var (4vec-<<= (svex-env-lookup first.val.name spec)
                                                 (svex-env-lookup first.val.name env))
                                  :otherwise (4vec-<<= (svex-eval first.val spec)
                                                       (svex-eval first.val env)))))
                         (svtv-override-triplelist-envs-match rest env spec))))
    :hints(("Goal" :in-theory (enable svtv-override-triple-envs-match
                                      svex-eval))))

  (defthm svtv-override-triplelist-envs-match-of-cons
    (equal (svtv-override-triplelist-envs-match (cons first rest) env spec)
           (and (svtv-override-triple-envs-match first env spec)
                (svtv-override-triplelist-envs-match rest env spec))))

  (defthm svtv-override-triplelist-envs-match-of-append
    (equal (svtv-override-triplelist-envs-match (append first rest) env spec)
           (and (svtv-override-triplelist-envs-match first env spec)
                (svtv-override-triplelist-envs-match rest env spec))))

  (defthm svtv-override-triplelist-envs-match-of-nil
    (svtv-override-triplelist-envs-match nil env spec)))

(define svtv-override-triple-envs-match-checks ((triple svtv-override-triple-p)
                                                (env-subst svex-alist-p)
                                                (spec svex-env-p))
  :returns (checks svtv-override-triplelist-p)
  (b* (((svtv-override-triple triple))
       (env-test (svex-subst triple.test env-subst))
       (test-ok (and (svex-case env-test :quote)
                     (equal (svex-quote->val env-test)
                            (svex-eval triple.test spec))))
       (spec-val (svex-eval triple.val spec))
       (val-ok (or (equal spec-val (4vec-x))
                   (b* ((env-val (svex-subst triple.val env-subst)))
                     (and (svex-case env-val :quote)
                          (4vec-<<= spec-val (svex-quote->val  env-val)))))))
    (and (not (and test-ok val-ok))
         (list (svtv-override-triple-fix triple))))
  ///
  (defret <fn>-correct
    (implies (svtv-override-subst-matches-env env-subst env)
             (equal (svtv-override-triplelist-envs-match checks env spec)
                    (svtv-override-triple-envs-match triple env spec)))
    :hints (("goal" :in-theory (e/d (svtv-override-subst-matches-env
                                     svtv-override-triple-envs-match)
                                    (svex-eval-of-svex-subst))
            :use ((:instance svex-eval-of-svex-subst
                   (pat (svtv-override-triple->test triple))
                   (al env-subst)
                   (env env))
                  (:instance svex-eval-of-svex-subst
                   (pat (svtv-override-triple->val triple))
                   (al env-subst)
                   (env env)))))))



(define svtv-override-triplemap-envs-match-checks ((triplemap svtv-override-triplemap-p)
                                                   (env-subst svex-alist-p)
                                                   (spec svex-env-p))
  :returns (checks svtv-override-triplelist-p)
  (b* (((when (atom triplemap)) nil)
       ((unless (mbt (and (consp (car triplemap))
                          (svar-p (caar triplemap)))))
        (svtv-override-triplemap-envs-match-checks (cdr triplemap) env-subst spec))
       (checks1 (svtv-override-triple-envs-match-checks (cdar triplemap) env-subst spec)))
    (mbe :logic (append checks1 (svtv-override-triplemap-envs-match-checks (cdr triplemap) env-subst spec))
         :exec (if checks1
                   (append checks1 (svtv-override-triplemap-envs-match-checks (cdr triplemap) env-subst spec))
                 (svtv-override-triplemap-envs-match-checks (cdr triplemap) env-subst spec))))

  ///
  (defret <fn>-correct
    (implies (svtv-override-subst-matches-env env-subst env)
             (equal (svtv-override-triplelist-envs-match checks env spec)
                    (svtv-override-triplemap-envs-match triplemap env spec)))
    :hints (("goal" :in-theory (e/d (svtv-override-triplemap-envs-match)))))

  (local (in-theory (enable svtv-override-triplemap-fix))))


(define svtv-override-triplemaplist-envs-match-checks ((triplemaps svtv-override-triplemaplist-p)
                                                       (env-subst svex-alist-p)
                                                       (spec svex-env-p))
  :returns (checks svtv-override-triplelist-p)
  (b* (((when (atom triplemaps)) nil))
    (append (svtv-override-triplemap-envs-match-checks (car triplemaps) env-subst spec)
            (svtv-override-triplemaplist-envs-match-checks (cdr triplemaps) env-subst spec)))

  ///
  (defret <fn>-correct
    (implies (svtv-override-subst-matches-env env-subst env)
             (equal (svtv-override-triplelist-envs-match checks env spec)
                    (svtv-override-triplemaplist-envs-match triplemaps env spec)))
    :hints (("goal" :in-theory (e/d (svtv-override-triplemaplist-envs-match)))))


  (defthm svtv-override-triplemaplist-envs-match-simplify
    (implies (and (syntaxp (cmr::term-variable-free-p x))
                  (syntaxp (quotep spec))
                  (bind-free (b* (((mv ok subst) (svex-env-term-extract-substitution env)))
                               (and ok
                                    `((env-subst . ',(make-fast-alist subst)))))
                             (env-subst))
                  (svtv-override-subst-matches-env env-subst env)
                  (equal checks (svtv-override-triplemaplist-envs-match-checks x env-subst (make-fast-alist spec)))
                  (syntaxp (quotep checks)))
             (equal (svtv-override-triplemaplist-envs-match x env spec)
                    (svtv-override-triplelist-envs-match checks env spec))))

  (cmr::def-force-execute svtv-override-triplemaplist-envs-match-checks-when-variable-free
    svtv-override-triplemaplist-envs-match-checks)

  (in-theory (enable svtv-override-triplemaplist-envs-match-checks-when-variable-free)))



(define svtv-override-triple-test/val-vars  ((x svtv-override-triple-p))
  :returns (vars svarlist-p)
  (b* (((svtv-override-triple x)))
    (append (svex-vars x.test) (svex-vars x.val)))
  ///
  (defret svtv-override-triple-envs-match-remove-irrelevant-pair
    (implies (and (not (member-equal var vars))
                  (svar-p var)) ;; bozo shouldn't be necessary
             (equal (svtv-override-triple-envs-match x (cons (cons var val) env) spec)
                    (svtv-override-triple-envs-match x env spec)))
    :hints(("Goal" :in-theory (enable svtv-override-triple-envs-match))))

  (defret true-listp-of-<fn>
    (true-listp vars)
    :rule-classes :type-prescription))

(define svtv-override-triplemap-test/val-vars  ((x svtv-override-triplemap-p))
  :returns (vars svarlist-p)
  (if (Atom x)
      nil
    (append (and (mbt (and (consp (car x))
                           (svar-p (caar x))))
                 (svtv-override-triple-test/val-vars (cdar x)))
            (svtv-override-triplemap-test/val-vars (cdr x))))
  ///
  (defret svtv-override-triplemap-envs-match-remove-irrelevant-pair
    (implies (and (not (member-equal var vars))
                  (svar-p var)) ;; bozo shouldn't be necessary
             (equal (svtv-override-triplemap-envs-match x (cons (cons var val) env) spec)
                    (svtv-override-triplemap-envs-match x env spec)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemap-envs-match))))

  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemaplist-test/val-vars  ((x svtv-override-triplemaplist-p))
  :returns (vars svarlist-p)
  (if (Atom x)
      nil
    (append (svtv-override-triplemap-test/val-vars (car x))
            (svtv-override-triplemaplist-test/val-vars (cdr x))))
  ///
  (defretd svtv-override-triplemaplist-envs-match-remove-irrelevant-pair
    (implies (and (not (member-equal var vars))
                  (svar-p var)) ;; bozo shouldn't be necessary
             (equal (svtv-override-triplemaplist-envs-match x (cons (cons var val) env) spec)
                    (svtv-override-triplemaplist-envs-match x env spec)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-envs-match)))))

(define svtv-override-triplemaplist-test/val-var-set  ((x svtv-override-triplemaplist-p))
  :returns (vars svar-key-alist-p)
  :prepwork ((local (defthm svar-key-alist-p-of-pairlis$-nil
                      (implies (svarlist-p x)
                               (svar-key-alist-p (pairlis$ x nil)))
                      :hints(("Goal" :in-theory (enable pairlis$))))))
  (make-fast-alist (pairlis$ (svtv-override-triplemaplist-test/val-vars x) nil))
  ///
  (memoize 'svtv-override-triplemaplist-test/val-var-set)
  (defret svtv-override-triplemaplist-envs-match-remove-irrelevant-pair-top
    (implies (and (not (hons-get var vars))
                  (svar-p var)) ;; bozo shouldn't be necessary
             (equal (svtv-override-triplemaplist-envs-match x (cons (cons var val) env) spec)
                    (svtv-override-triplemaplist-envs-match x env spec)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-envs-match-remove-irrelevant-pair))))

  (cmr::def-force-execute svtv-override-triplemaplist-test/val-var-set-when-variable-free
    svtv-override-triplemaplist-test/val-var-set)

  (in-theory (enable svtv-override-triplemaplist-test/val-var-set-when-variable-free)))



(defxdoc svex-decomposition-methodology
  :parents (sv)
  :short "High-level description of decomposition methodology for @(see SVTV)s."
  :long "<p>In hardware verification, it is important to be able to break down
proofs into pieces. An important technique for this purpose is to assume that
certain internal signals have particular values at particular times, and prove
something about their fanout logic. For symbolic simulation, the best
performance for this method is obtained by replacing the fanin logic of these
signals with free symbolic values, which we call \"overriding\" those
signals. In order to compose together multiple proofs using this technique, it
is important to be able to use a theorem proved about a design's behavior with
certain signals overridden to prove a theorem about the design without (some
of) those overrides.</p>

<p>See also the @(see sv-tutorial) and in particular the topic @(see
decomposition-proofs), which walks through a runnable example.</p>

<p>As a high-level example, suppose we prove that the partial product summation
of a multiplier is correct by overriding the partial product signals.  Note:
the following uses a made-up syntax, for illustration purposes only.  In our
real framework, @('run-design') would be replaced by @('svtv-run'), @('lookup')
would be replaced by @('svex-env-lookup'), etc.</p>

@({
 (defthm multiplier-pp-sum-correct-override
    (implies (unsigned-byte-p 128 partial-products-value)
             (let* ((run (run-design (multiplier)
                                     :inputs `((opcode . ,*multiply-opcode*))
                                     :overrides `((partial-product-signal . ,partial-products-value)))))
                 (equal (lookup 'multiplier-output run)
                        (pp-sum-spec partial-products-value)))))
 }})


<p>Additionally, suppose that we've proved that the same multiplier computes a
correct Booth encoding as its partial products signal:</p>

@({
 (defthm multiplier-booth-encoding-correct
    (implies (and (unsigned-byte-p 16 a) (unsigned-byte-p 16 b))
             (let* ((run (run-design (multiplier)
                                     :inputs `((opcode . ,*multiply-opcode*)
                                               (a-input . ,a)
                                               (b-input . ,b)))))
               (equal (lookup 'partial-product-signal run)
                      (booth-enc-spec a b)))))
 })

<p>We'd like to be able to compose these two theorems and prove the multiplier
correct from end to end.  But the design here has been run with two different
settings for the inputs and overrides, and these can't be reconciled as-is.  At
a high level, our decomposition methodology works by allowing theorems such as
these -- which are convenient to prove using symbolic simulation -- to be
generalized into theorems that can be straightforwardly composed. Using the
same made-up syntax:</p>

@({
 (defthm multiplier-pp-sum-correct-gen
   (let* ((opcode (lookup 'opcode input-env))
          (run (run-design (multiplier) :inputs input-env))
          (partial-products-value (lookup 'partial-product-signal run))
          (result (lookup 'multiplier-output run)))
      (implies (and (equal opcode *multiply-opcode*)
                    (unsigned-byte-p 128 partial-products-value))
               (equal result (pp-sum-spec partial-products-value)))))
 })

<p>Notice this has been changed in two ways:</p>

<ul>
<li>First, the @(':inputs') argument, which used to be an explicit alist, is
now a free variable with a hypothesis assuming that the inputs that were given
before (opcode bound to @('*multiply-opcode*')) are correctly bound there.</li>

<li>Second, the overrides are replaced by references to observations of
internal signals.  That is, we're no longer replacing the fanin cone of
@('partial-product-signal') with a variable, as we wanted for symbolic
simulation; rather, we're looking at whatever the value of that signal happens
to be, and proving that the multiplier output satisfies its spec based on that
signal.</li>
</ul>

<p>The booth encoding theorem can be changed similarly, although since it had
no overrides only the first change applies here:</p>

@({
 (defthm multiplier-booth-encoding-correct-gen
   (let* ((opcode (lookup 'opcode input-env))
          (a      (lookup 'a-input input-env))
          (b      (lookup 'b-input input-env))
          (run (run-design (multiplier) :inputs input-env))
          (partial-products-value (lookup 'partial-product-signal run)))
      (implies (and (equal opcode *multiply-opcode*)
                    (unsigned-byte-p 16 a)
                    (unsigned-byte-p 16 b))
               (equal partial-products-value (booth-enc-spec a b)))))
 })

<p>Notice that these theorems now can be composed! In fact, given a lemma about
the bit width of @('booth-enc-spec'), we can obtain:</p>

@({
 (defthm multiplier-computes-pp-sum-of-booth-enc
   (let* ((opcode (lookup 'opcode input-env))
          (a      (lookup 'a-input input-env))
          (b      (lookup 'b-input input-env))
          (run (run-design (multiplier) :inputs input-env))
          (result (lookup 'multiplier-output run)))
      (implies (and (equal opcode *multiply-opcode*)
                    (unsigned-byte-p 16 a)
                    (unsigned-byte-p 16 b))
               (equal result (pp-sum-spec (booth-enc-spec a b))))))
 })

<p>This methodology's main user interface is @(see def-svtv-generalized-thm).
See that topic for usage.  In the rest of this topic we'll discuss how this
works and the solutions to certain complications.</p>


<p>To produce the generalized forms of the theorems above, we want a particular
property of the design: that if we override a signal with the value that it
would have had anyway, then the values of all signals are preserved. Stated in
terms of our imaginary @('run-design') function above, for the particular case
of the partial-products-value of our multiplier design:</p>

@({
 (defthm multiplier-partial-product-overrides-transparent
   (let* ((base-run (run-design (multiplier) :inputs input-env))
          (partial-products-value (lookup 'partial-product-signal base-run))
          (override-run (run-design (multiplier)
                                    :inputs input-env
                                    :overrides `((partial-product-signal . ,partial-products-value)))))
      (all-lookups-equivalent override-run base-run)))
 })

<p>This theorem, along with a couple of other simpler facts that allow the
generalization of the input environment, would be sufficient to let us
generalize @('multiplier-pp-sum-correct-override') to
@('multiplier-pp-sum-correct-gen').</p>

<p>Generally we also want to allow for multiple potentially overriden signals in different combinations:</p>

@({
 (defthm multiplier-partial-product-overrides-transparent
   (let* ((base-run (run-design (multiplier) :inputs input-env))
          (override-run (run-design (multiplier)
                                    :inputs input-env
                                    :overrides override-env)))
      (implies (override-signals-consistent-with-base-run override-env base-run)
               (all-lookups-equivalent override-run base-run))))
 })

<p>Here we imagine @('override-signals-consistent-with-base-run') would check
that all internal signals of the design that are bound in @('override-env') are
bound to the same value in @('base-run').</p>

<p>This overrides-transparent condition seems intuitively obvious and we would like
to prove it for all designs.  However, it is actually a fairly deep property of
the design object, and as we'll see, depending how we compose the design
together it may or may not be true.</p>

<p>We have two underlying methods for ensuring that this property holds. The
first method method proves this property of the actual SVTV we're used to
working with. This uses a syntactic check, which is fast and reliable but may
fail on designs with apparent combinational loops, such as designs with
latch-based logic or signals that feed into their own clock gates.  If the
syntactic check fails, an equivalence check using <see topic='@(url
fgl::fgl)'>FGL</see> may also be used; performance of this check is uncertain
but seems to usually work in practice.</p>

<p>The second method does not prove the overrides-transparent condition of the
actual SVTV, but instead proves it of an uncomputed idealized version of the
SVTV.  This method doesn't require a syntactic check or equivalence check and
will work on any design.  However, proofs by composition will then be about the
idealized SVTV, even though the lower-level proofs by symbolic simulation are
done on the usual SVTV.  This can be a disadvantage because we don't then know
whether the properties shown by composition are true of the SVTV. See @(see
svtv-decomposition-choosing-a-method) for more on this topic.</p>

<p>The syntactic check method works by checking the expressions that make up
the finite-state machine derived from the circuit.  Overrides are accomplished
by replacing references to signals with override muxes, essentially @('(if
override-condition override-value original-signal-value)').  The syntactic
check finds all such override muxes and ensures that the original signal value
in each one matches the final value of the overridden signal.  If this is true,
then it implies the overrides-correct condition above.  However, this syntactic
condition can fail to hold in cases where there are combinational loops or
apparent combinational loops.  Even dependency loops on a vector variable where the
dependencies between the bits are acyclic can cause this check to fail if any
overridden signals are involved in such a loop.</p>

<p>The correct way to deal with 0-delay combinational loops is to compute a
<i>fixpoint</i>.  That is, for a given setting of the circuit inputs and
stateholding elements, begin at a state setting these values for the
inputs/states and all internal signals set to X.  Apply the internal signals'
update functions to obtain a new state.  Repeat this until we reach a fixpoint.
It is a theorem that if all signals have finite bit widths and the update
functions respect X-monotonicity, then a fixpoint is reached by the time we
have repeated this @('n') times where @('n') is the total number of bits in all
internal signals.  A more in-depth exploration of this algorithm is written in
@(see least-fixpoint).</p>

<p>Because of the number of repetitions needed, it isn't always practical to
actually compute the fixpoint.  Instead, in the second method we use an
approximate composition method that is efficient, practially useful, and
conservative with respect to the fixpoint: that is, if a signal's value in this
approximate composition is non-X, then its fixpoint value must be the same.</p>

<p>The approximate composition does not always satisfy the overrides-correct
condition above.  For example, if we override a signal that is part of a
0-delay combinational loop and its fanin logic therefore appears more than once
in different forms (composed with itself a different number of times), then
overriding all occurrences of that fanin logic with the signal's final value
isn't guaranteed to preserve the value of other signals.</p>

<p>However, the overrides-correct condition is true of the fixpoint. One
version of this is proved in \"centaur/sv/svex/fixpoint-override\" as
@('svex-alist-eval-override-fixpoint-equivalent-to-reference-fixpoint'); a
somewhat more general version is proved in
@('svex-alist-eval-fixpoint-override-impl-equiv-spec').</p>


<p>This leads us to the following methodology for composing hardware proofs
with overrides:</p>

<ul>

<li>Compute a symbolic representation <i>approx</i> of the desired run of the
design based on the approximate composition -- in particular, using @(see
defsvtv$).</li>

<li>Define a non-executable function <i>ideal</i> that logically computes the
analogous run with the fixpoint composition.  This can be done using @(see
def-svtv-ideal).</li>

<li>To prove composition-friendly facts about <i>ideal</i>, first prove a lemma
with overrides about <i>approx</i> (such as
@('multiplier-pp-sum-correct-override') and use the conservativity of
<i>approx</i> with respect to <i>ideal</i> along with the overrides-correct
property of <i>ideal</i> to prove the composition-friendly fact (such as
@('multiplier-pp-sum-correct-gen')) about <i>ideal</i>. This is automated by
@(see def-svtv-generalized-thm).
</li>

</ul>

<p>Alternatively, to use the syntactic check method instead:</p>

<ul>

<li>Compute a symbolic representation of the desired run of the
design based on the approximate composition -- in particular, using @(see
defsvtv$).</li>

<li>Check that the approximate composition satisfies the syntactic check
described above regarding override muxes, or fall back on the FGL equivalence
check to prove override transparency if the syntactic check fails.  This can be
done using @('def-svtv-refinement').</li>

<li>To prove composition-friendly facts about the SVTV, first prove a lemma
with overrides along with the overrides-correct
property of the SVTV to prove the composition-friendly fact (such as
@('multiplier-pp-sum-correct-gen')). This is automated by
@(see def-svtv-generalized-thm).
</li>

</ul>

<p>See @(see svtv-decomposition-choosing-a-method) for pros and cons of the above methods.</p>

")


(defxdoc def-svtv-ideal
  :parents (svex-decomposition-methodology)
  :short "Define a non-executable, fixpoint-based analogue of a @(see symbolic-test-vector) and prove properties that allow it to be used in decomposition proofs."
  :long "<p>See also @(see def-svtv-refinement), of which this is a wrapper.</p>

<p>To use this, first define an SVTV using @(see defsvtv$)
and (immediately after) save the contents of the resulting @(see svtv-data)
stobj to an object using @(see def-svtv-data-export).  Then invoke
@('def-svtv-ideal') as follows:</p>

@({
 (def-svtv-ideal ideal-name svtv-name data-name)
 })

<p>For example,</p>

@({
 (sv::defsvtv$ my-mod-run ...)

 ;; must be immediately after the defsvtv$ (or at least ensure that the
 ;; svtv-data stobj is not modified in between)
 (sv::def-svtv-data-export my-mod-data)

 ;; may occur later, no more reliance on the svtv-data stobj:
 (sv::def-svtv-ideal my-mod-ideal my-mod-run my-mod-data)
 })

<p>This produces a 0-ary function (not intended to be executed) named
@('my-mod-ideal'), which returns an @(see svtv-spec) object encapsulating the
same pipeline run as in @('my-mod-run'), but based on a fixpoint composition of
the module's assignments rather than the approximate composition that is
computed for the SVTV.  See @(see svex-decomposition-methodology) for
further explanation.  A few important properties relating @('my-mod-ideal') and
@('my-mod-run') are proved:</p>

<ul>

<li>@('my-mod-ideal-refines-my-mod-run') -- this allows us to infer facts about
@('my-mod-ideal') from proofs about @('my-mod-run'), where potentially the
@('my-mod-run') proof may be done with override signals that may be removed
from the theorem about @('my-mod-ideal').</li>

<li>@('my-mod-ideal-refines-my-mod-run-on-same-envs') -- special case of the
above theorem where the input environments are the same, i.e. no overrides are
removed.</li>

<li>@('my-mod-ideal-refines-my-mod-ideal') -- this allows us to remove
overrides from theorems about @('my-mod-ideal').</li>

</ul>

<p>Additionally, the @('def-svtv-ideal') event produces a function named (in
our example) @('my-mod-ideal-exec'), which (logically) produces some subset of
the output signals of a @(see svtv-spec-run) of @('my-mod-ideal'), but
accomplishes this (when successful) executing @(see svtv-run) of
@('my-mod-run').  If the outputs from the @('svtv-run') contain no Xes, then
this is the same as the @('svtv-spec-run') of @('my-mod-ideal').</p>


")


(defxdoc svtv-decomposition-choosing-a-method
  :parents (svex-decomposition-methodology)
  :short "Summary of the relative advantages of the ideal-based vs
syntactic-check-based methods for SVTV decomposition."
  :long "

<p>See @(see svex-decomposition-methodology) for background on these choices.
This topic pertains to the choice in SVTV decomposition proofs of whether, in
proofs using @(see def-svtv-generalized-thm), to target the SVTV
itself (showing the override transparency property using a syntactic check),
the SVTV-spec analogous to that SVTV (also using the syntactic check), or the
idealized SVTV-spec based on a fixpoint composition (without needing the
syntactic check).</p>

<p>The main advantage of the ideal-based method is that the syntactic check of
the other method might not pass on your design, and the FGL equivalence
check-based fallback method might be too expensive.  If these checks pass, you
can do your decomposition proofs using the syntax check method, and
subsequently if needed you can always define an ideal later; any theorems
already proved about the SVTV are true of it as well.  However, it's also
possible that the syntactic check will work on some set of overrides but fail
if more override signals are added because some new signal to be overridden is
involved in an apparent combinational loop. This is mainly of concern if there
is latch-based logic in the design, but can come up in other situations.</p>

<p>The disadvantage of the ideal-based method is that what you've proved about
the ideal isn't always provable about the computed SVTV.  Generally we only
know that the computed SVTV's results are conservative approximations of those
of the ideal SVTV.  If we can show that the computed SVTV's results are non-X
for some case, then we know it's equivalent to the ideal SVTV for that case.
But this has to be proved without overrides, which can be prohibitively
expensive. In most cases it's good enough to know these facts about the ideal.
However, if (e.g.) we want to prove via equivalence checking that some new
design produces the same result as an original design, which we've proven
correct via decomposition, then the equivalence check has to be done between
the computed SVTVs, but we really want to show that the ideal SVTV for the new
design is equivalent to the ideal SVTV of the original design.  Assuming the
equivalence check passes, it's still possible that the new design's SVTV and
ideal SVTV along with the original design's SVTV all produce X in some case
where the correct result (and the result computed by the original design's
ideal SVTV) is non-X.</p>

<p>If the syntactic check works on your design for all the override signals
needed, you can choose to phrase your generalized theorems on the SVTV itself
or an analogous SVTV-spec object.  This decision isn't as important because the
two types of generalized theorems can be reproved about the other object.  If
the generalized theorems are proved about SVTV-spec objects, they can be
reproved about the SVTV itself by using the equivalence between the SVTV and
SVTV-spec (a theorem named according to the scheme
@('svtv-run-of-SVTV-is-svtv-spec-run-of-SVTVSPEC')).  If proved about the SVTV
object, it can be proved about the SVTV-spec by doing a duplicate
@('def-svtv-generalized-thm') with the @(':svtv-spec') argument added and the
lemma proved using the original generalized theorem.</p>

")

(defxdoc def-svtv-generalized-thm
  :parents (svex-decomposition-methodology)
  :short "Prove a theorem about an idealized SVTV via a symbolic simulation lemma about the SVTV itself."
  :long "
<p>See @(see svex-decomposition-methodology) for background on the methodology that this supports.</p>

<p>Usage:</p>
@({
 (def-svtv-generalized-thm theorem-name
   :svtv svtv-name
   :ideal ideal-name
   :svtv-spec svtv-spec-name
   :input-vars input-variable-list
   :input-var-bindings input-variable-binding-list
   :override-vars override-variable-list
   :x-override-vars x-override-variable-list
   :override-var-bindings override-variable-binding-list
   :spec-override-vars override-variable-list
   :spec-override-var-bindings override-variable-binding-list
   :output-vars output-variable-list
   :output-parts output-part-list
   :hyp hypothesis-term
   :concl conclusion-term
   :final-hyp hyp-term
   :enable rules-list
   :unsigned-byte-hyps nil
   :no-lemmas nil
   :no-integerp nil
   :lemma-nonlocal nil
   :lemma-defthm nil
   :lemma-args nil
   :lemma-use-ideal nil
   :hints hints
   :rule-classes rule-classes
   :pkg-sym sym)
 })

<p>For each of the keyword arguments, if absent a default will be looked up in
the @(see table) @('svtv-generalized-thm-defaults'), which may be (locally)
modified by users in order to avoid (for example) the need to repeatedly
specify the same SVTV and ideal in every form.</p>

<p>Prerequisite: See @(see def-svtv-refinement) and @(see def-svtv-ideal)
for the possible ways of
showing that the override transparency property holds of your design, which is
required for the use of this utility.</p>

<p>The generalized theorem produced by this utility may be about either a run
of the given SVTV, of an idealized SVTV-spec as produced by @(see
def-svtv-ideal), or of an SVTV-spec object equivalent to the SVTV.</p>

<ul>

<li>If the @(':ideal') argument is given, it must be the name of the idealized
svtv-spec function as defined by @(see def-svtv-ideal).  This allows the use of
the fixpoint-based methodology disucssed in @(see
svex-decomposition-methodology), which avoids the syntactic check on the FSM
that is otherwise needed.  The generalized theorem will be about the
@(see svtv-spec-run) of this idealized svtv-spec object.  This argument should
be mutually exclusive with the @(':svtv-spec') argument.</li>

<li>If the @(':svtv-spec') argument is given, it must be the name of the
svtv-spec function produced by @(see def-svtv-refinement) with the optional
@(':svtv-spec') argument, and that event will do the syntactic check necessary
to ensure override transparency.  The generalized theorem will be about the
@(see svtv-spec-run) of this object. The @(see svtv-spec-run) takes extra
inputs @('base-ins') and @('initst') that makes this more general than the run
of the SVTV (which always has Xes for the initial state and any inputs not
bound in the SVTV stimulus pattern).</li>

<li>If neither the @(':svtv-spec') nor the @(':ideal') argument is given, then
the generalized theorem will be about the @('svtv-run') of the SVTV itself.
The @(see def-svtv-refinement) event must have done the syntactic check
necessary to ensure override transparency.</li>

</ul>

<p>We briefly describe the arguments of the macro and then we'll describe the
theorem proved in FGL and the generalized corollary this macro generates.</p>

<h3>Arguments</h3>

<p>Several arguments come in pairs with the naming convention
@(':<arg>, :more-<arg>').  This allows one of these (typically the @(':more')
version) to be set by the defaults table while the other still be set in
individual theorems.  We note below which arguments support this and how the
two arguments are combined.</p>

<ul>

<li>@(':svtv') is the name of the SVTV.  This argument must always be provided
either explicitly or via the defaults table.</li>

<li>@(':ideal') and @(':svtv-spec') affect the form of the generalized theorem; see above.</li>

<li>@(':input-vars') are the names of any input variables of the SVTV that will
appear in the hypothesis or conclusion, except those that are bound in
@(':input-var-bindings'). Instead of a list of signals, users may pass \":all\"
parameter to get all the input variables that are not bound.  If not @(':all'),
additional input variables can be specified in @(':more-input-vars'); the two
sets of input variables are appended.</li>

<li>@(':input-var-bindings') (appended with @(':more-input-var-bindings) is a
list of @('let')-like bindings of input variables to expressions.</li>

<li>@(':override-vars') (appended with @(':more-override-vars'))
is a list of override-value variables of the SVTV to be
overridden in the FGL lemma but not overridden in the generalized theorem.
Each such variable must have a corresponding output sampling the same signal at
the same time so as to support eliminating the override.</li>

<li>@(':override-var-bindings') (appended with @(':more-override-var-bindings'))
is a list of @('let')-like bindings of override
value variables to expressions, to be overridden in the lemma but not
overridden in the generalized theorem.  Each such variable must have a
corresponding output sampling the same signal at the same time so as to support
eliminating the override.</li>

<li>@(':x-override-vars') (appended with @(':more-x-override-vars')) is a list
of override-value variables that will be overriden to X in the lemma, and not
mentioned in the final theorem; effectively, this asserts that these signals
are not relevant to the current computation and prunes them out of the fanin
cone by forcing them to X.</li>

<li>@(':spec-override-vars') (appended with @(':more-spec-override-vars'))
is a list of override-value variables of the SVTV
to be overridden in both the FGL theorem and the resulting generalized theorem.
The difference between @(':override-vars') and @(':spec-override-vars') is that
the @(':override-vars') will not be overridden in the generalized theorem, but
the @(':spec-override-vars') still will.</li>

<li>@(':spec-override-var-bindings') (appended with @(':more-spec-override-var-bindings'))
is a list of @('let')-like bindings of
override value variables to expressions, which will be overridden in both the
FGL theorem and generalized theorem.</li>

<li>@(':output-vars') (appended with @(':more-output-vars'))
is a list of output variables of the SVTV that are used in the conclusion.</li>

<li>@(':output-parts') is a list of 4vec expressions -- part selects, zero
extends, shifts, concatenations -- of the output variables.  The given parts of
the outputs will be proved to be integerp in order to use a monotonicity
argument.  Variables that are not mentioned in output-parts will be proved
integerp as a whole.</li>

<li>@(':hyp') (conjoined with @(':more-hyp') is a term (default T), which may
reference variables listed in input-vars and override-vars as well as variables
used in the expressions of input-bindings.</li>

<li>@(':concl') is a term which may reference the same variables available to
@(':hyp') as well as the output-vars.</li>

<li>@(':final-hyp') is a term (default T) with is conjoined at the beginning of
the hypotheses only of the final theorem. This is sometimes convenient for
adding syntaxp or bind-free directives.</li>

<li>@(':enable') is a list of rules to be included in the theory for the final
generalized theorm, mainly useful when specifying @(':output-parts').</li>

<li>@(':no-lemmas') says to skip the initial override theorem and monotonicity
lemma and tries to prove the final (generalized) theorem directly, with the
hints given by the user.</li>

<li>@(':hints') are hints for the final theorem, used by themselves if @(':no-lemmas')
is set and in addition to the automatically provided hints if not.</li>

<li>@(':lemma-defthm') defaults to @('fgl::def-fgl-thm') but can be set
to (e.g.) @('defthm') or @('fgl::def-fgl-param-thm') to change how the initial
lemma is proved.</li>

<li>@(':lemma-args') gives additional arguments to be passed to the form
proving the initial lemma, which could be hints for a @('defthm') form or FGL
keyword args for @('fgl::def-fgl-thm') or @('fgl::def-fgl-param-thm').</li>

<li>@(':lemma-use-ideal') phrases the lemma in terms of a run of the ideal
svtv-spec, rather than the SVTV.</li>

<li>@(':lemma-use-svtv-spec') phrases the lemma in terms of a run of
the (non-ideal) svtv-spec, rather than the SVTV.</li>

<li>@(':lemma-nonlocal') makes the lemma not be local.</li>

<li>@(':lemma-custom-concl') gives a custom conclusion for the lemma, different
from the one to be used in the final theorem.  Can be convenient if it is
easier to prove the lemma in a different form which still implies the form of
the conclusion in the final theorem.</li>

<li>@(':lemma-no-run') makes the lemma not bind the output variables, skipping
the svtv-run (in the common case, or the svtv-spec-run in others); may be
useful with @(':lemma-custom-concl').</li>

<li>@(':no-integerp') says to skip proving @('integerp') of each output in the
initial override theorem.  The @(':enable') option typically must be used to
provide additional rules for the final theorem to show that the lemma implies
the outputs are integers.</li>

<li>@(':integerp-separate') says to prove @('integerp') of each output in a second
lemma, not the initial override theorem.</li>

<li>@(':integerp-defthm') defaults to @('defthm') but can be set to (e.g.)
@('fgl::def-fgl-thm') to choose a different method of proving the integerp
lemma, when @(':integerp-separate') is set.</li>

<li>@(':integerp-args') gives a list of arguments for the event proving the
integerp lemma, when @(':integerp-separate') is set).  If none are given, the
default is to provide a hint using an instance of the override lemma and
disabling it, since commonly the override lemma itself implies all the outputs
are integers.</li>

<li>@(':final-defthm') defaults to @('defthm') but can be set to a different
macro to change how the final generalized theorem is proved</li>

<li>@(':final-defthm-args') gives additional arguments to the form proving the
final generalized theorem.</li>

<li>@(':rule-classes') gives the rule classes of the theorem proved.</li>

<li>@(':unsigned-byte-hyps') says to automatically add @('unsigned-byte-p')
hypotheses for each input and override variable.</li>

<li>@(':run-before-concl') gives a term that is placed in the override lemma
within @('(progn$ run-before-concl concl)'), perhaps to do some extra printing
in case of a counterexample.</li>

<li>@(':integerp-run-before-concl') gives a term to add to the integerp lemma
when @(':integerp-separate') is set, similar to @(':run-before-concl').</li>

<li>@(':pkg-sym') defaults to the theorem name, and picks the package that
various symbols are generated in.</li>

</ul>

<h3>Initial override lemma</h3>

<p>The initial override theorem is typically proved with FGL, but can be done
otherwise using the @(':lemma-defthm') argument. It says that under the given
hypotheses, a run of the SVTV on a particular, explicitly constructed
environment produces outputs satisfying the conclusion.  In addition, it proves
that those outputs are integers (whereas they could otherwise be arbitrary
@(see 4vec)s including X and Z bits).  The environment is constructed as
follows:</p>

<ul>
<li>Input variables bound in @(':input-var-bindings') are bound to their respective values</li>
<li>Input variables listed in @(':input-vars') are bound to variables of the same name</li>
<li>Override value variables listed in @(':override-vars') and
@(':spec-override-vars') are bound to variables of the same name</li>
<li>Override value variables bound in @(':override-var-bindings') and
@(':spec-override-var-bindings') are bound to their respective values</li>

<li>Override test variables corresponding to the override value variables
listed in @(':override-vars'), @(':override-var-bindings'),
@(':spec-override-vars'), and @(':spec-override-var-bindings') are all bound to
-1.</li>

</ul>

<p>For example, the following form:</p>

@({
 (def-svtv-generalized-thm partial-prods-to-product
   :svtv multiplier-svtv
   :ideal multiplier-svtv-ideal
   :input-var-bindings ((opcode *mul-opcode*))
   :spec-override-var-bindings ((clkgates 0))
   :override-vars (partial-products)
   :output-vars (product)
   :hyp (unsigned-byte-p 128 partial-products)
   :concl (equal product (sum-partial-products partial-products)))
 })
<p>produces approximately the following initial lemma:</p>
@({
 (fgl::def-fgl-thm partial-prods-to-product-override-lemma
   (implies (unsigned-byte-p 128 partial-products)
            (b* ((run (svtv-run (multiplier-svtv)
                                `((opcode . ,*mul-opcode*)
                                  (partial-products . ,partial-products)
                                  (clkgates . 0)
                                  (override-partial-products . -1)
                                  (override-clkgates . -1))
                       :include '(product)))
                 (product (svex-env-lookup 'product run)))
              (and (integerp product)
                   (equal product (sum-partial-products partial-products))))))
 })

<p>The @(':lemma-use-ideal') option would replace the @('svtv-run') form with the
following form:</p>

@({
  (svex-env-reduce '(product)
                   (svtv-spec-run (multiplier-svtv-ideal)
                                 `((opcode . ,*mul-opcode*)
                                   (partial-products . ,partial-products)
                                   ...)))
 })


<h3>Generalized theorem</h3>

<p>The generalized theorem refers to a single free variable @('env') rather
than a free variable for each input and override value.  It binds @('run') to
the run of the ideal on that env.  Input variables -- both those listed in
@(':input-vars') and the keys of @(':input-var-bindings') -- are bound to their
lookups in @('env'), and hypotheses are added stating that the keys of
@(':input-var-bindings') are bound to their respective values. Outputs are
bound (as usual) to their lookups in @('run'), and override variables from
@(':override-vars') and @(':override-var-bindings') are additionally bound to
the lookups of their respective reference variables in @('run').  Override
variables listed in @(':spec-override-vars') and
@(':spec-override-var-bindings') are still overridden, i.e. the value variables
are looked up in @('env') similar to inputs.  An additional hypothesis states
that the only override test variables that are set in the env are those
corresponding to the value variables listed in @(':spec-override-vars') and
@(':spec-override-var-bindings'): this is the
@('svtv-override-triplemaplist-envs-match') hypothesis in the theorem below.
Finally, when the @(':ideal') or @(':svtv-spec') options are used, the generalized
theorem refers to @('svtv-spec-run') instead of @('svtv-run') which allows an
additional setting of input and initial
state variables not set by the SVTV itself; these are given respectively by
@('base-ins') and @('initst') in the theorem.  Base-ins, however, must be
assumed not to set any additional override test variables.  The
@('svarlist-nonoverride-p') hypothesis of the theorem below ensures this.</p>

<p>For example, the form above produces approximately the following generalized
theorem, which we have annotated to say where each binding and hypothesis comes
from:</p>
@({
 (defthm partial-prods-to-product
   (b* (;; Input variables bound to their lookups in env
        (opcode (svex-env-lookup 'opcode env))
        ;; Spec-override variables bound to their lookups in env
        (clkgates (svex-env-lookup 'clkgates env))

        ;; Run the idealized SVTV
        (run (svtv-spec-run (multiplier-svtv-ideal) env :base-ins base-ins :initst initst))

        ;; Override variables bound to their lookups in run
        (partial-products (svex-env-lookup 'partial-products run))
        ;; Output variables bound to their lookups in run
        (product (svex-env-lookup 'product run)))
     (implies (and ;; Hyp given by the user
                   (unsigned-byte-p 128 partial-products)
                   ;; Implicit hyp from input-var-bindings
                   (equal opcode *mul-opcode*)
                   ;; Implicit hyp from spec-override-var-bindings
                   (equal clkgates 0)
                   ;; Env only overrides those variables mentioned in spec-override-vars/bindings
                   (svtv-override-triplelist-envs-match
                    (multiplier-svtv-triplemaplist)
                    env
                    '((override-clkgates . -1)))
                   ;; Base-ins doesn't add any override test settings
                   (svarlist-nonoverride-p (svex-envlist-all-keys base-ins) :test))
             ;; Conclusion given by the user
             (equal product (sum-partial-products partial-products)))))
 })
")

(defxdoc def-svtv-refinement
  :parents (svex-decomposition-methodology)
  :short "For a given SVTV, prove the theorems necessary to use that SVTV
in (de)composition proofs using @(see def-svtv-generalized-thm), as in the
@(see svex-decomposition-methodology)."
  :long "

<p>Prerequisite: An SVTV defined with @(see defsvtv$), and an @(see
svtv-data-obj) created using @(see def-svtv-data-export) immediately after
defining that SVTV.</p>

<p>Usage:</p>

@({
 (def-svtv-refinement svtv-name data-name
         ;; optional:
         :fgl-semantic-check t
         :omit-default-aignet-transforms t
         :ideal idealname
         :svtv-spec specname
         :fsm my-fsm-name
         :define-fsm t
         :inclusive-overridekeys t
         :pkg-sym pkg-sym)
 })

<p>A particular type of invocation has an alias, @(see def-svtv-ideal) -- in
particular, these two forms are equivalent:</p>
@({
 (def-svtv-ideal ideal-name svtv-name data-name)
 (def-svtv-refinement svtv-name data-name :ideal ideal-name)
 })

<p>This form either proves the override transparency property (discussed in
@(see svex-decomposition-methodology)) of the given SVTV, or defines an
idealized SVTV and proves the override transparency property about it.</p>

<p>If the @(':ideal') is provided, this is like an invocation of @(see
def-svtv-ideal): it produces an idealized svtv-spec object that is a refinement
of the given SVTV and proves that it satisfies the override-transparency
property.  The top-level theorems are then called
@('idealname-refines-idealname') (the ideal SVTV-spec satisfies the
override-transparency property on its own) and
@('idealname-refines-svtvname') (relating the ideal SVTV-spec with the original
SVTV).</p>

<p>If not, then the syntactic check method is used to prove the
override-transparency property of the given SVTV itself. If the
@(':fgl-semantic-check') keyword argument is set, then if any overrides fail
the syntactic check for the override transparency property, an FGL proof will
be attempted to show the same property using equivalence checking -- see below.
The main theorem, showing that it satisfies the override-transparency
property, is @('svtvname-refines-svtvname').  If the @(':svtv-spec') argument
is given, this also defines a function (with the given name) with the same
behavior as the original SVTV and adds another refinement theorem,
@('specname-refines-svtvname').</p>

<p>The FGL proof of override transparency, attempted only when
@(':fgl-semantic-check') is set and some overrides fail the syntactic check,
requires the \"centaur/fgl/top\" book to be included.  Additionally, by default
a special <see topic='@(url aignet::aignet)'>AIGNET</see> simplification
routine is used in the equivalence check.  This can be overridden with
@(':omit-default-aignet-transforms'), but if not, the
\"centaur/aignet/transforms\" and \"centaur/ipasir/ipasir-backend\" books must
also be loaded.  The latter requires an <see topic='@(url
ipasir::ipasir)'>IPASIR</see> shared library to be available and the
IPASIR_SHARED_LIBRARY environment variable set accordingly; see @(see
ipasir::building-an-ipasir-solver-library) for how to get one. In summary, the
following include-books are usually needed when using the FGL semantic
check:</p>
@({
 (include-book \"centaur/fgl/top\" :dir :system)
 (include-book \"centaur/aignet/transforms\" :dir :system)
 (include-book \"centaur/ipasir/ipasir-backend\" :dir :system)
 })
")


