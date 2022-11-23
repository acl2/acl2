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

(include-book "svtv-idealize-defs")
(include-book "process")
(include-book "std/util/defredundant" :dir :system)
(include-book "override-common")
(include-book "override-thm-common")
(include-book "centaur/fgl/def-fgl-thm" :dir :system)
(include-book "centaur/fgl/def-fgl-rewrite" :dir :system)
(include-book "centaur/fgl/config" :dir :system)
(local (include-book "svtv-idealize-proof"))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :Dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :Dir :System))

(local (std::add-default-post-define-hook :fix))

;; Just a few theorems from svtv-idealize-proof are needed for this event.  We'll import them redundantly here.
(std::defredundant :names (set-equiv-by-mergesort-equal
                           SET-EQUIV-IMPLIES-SVEX-ENVS-EQUIVALENT-SVEX-ENV-REDUCE-1
                           SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1
                           SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-SPEC-RUN
                           SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-IDEAL-SPEC-RUN
                           svex-env-reduce-<<=-same
                           svtv-override-triplemaplist-muxes-<<=-of-same-envs
                           svtv-override-triplemaplist-muxtests-subsetp-of-same-envs
                           4vec-override-mux-<<=-of-same-test/val))


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





(defconst *svtv-idealize-template*
  '(defsection <name>-idealize
     (local (in-theory nil))
  
     (define <name>-triplemaplist ()
       :prepwork ((local (in-theory nil)))
       :returns (triplemaps svtv-override-triplemaplist-p
                            :hints (("goal" :in-theory '(svtv-override-triplemaplist-p-of-svtv-construct-triplemaplist
                                                         <name>-triplemaplist))))
       :guard-hints (("goal" :in-theory '((:EXECUTABLE-COUNTERPART IF)
                                          (:REWRITE PIPELINE-SETUP-P-OF-SVTV-DATA-OBJ->PIPELINE-SETUP)
                                          (:REWRITE SVEX-ALISTLIST-P-OF-PIPELINE-SETUP->OVERRIDE-TESTS)
                                          (:REWRITE SVEX-ALISTLIST-P-OF-PIPELINE-SETUP->OVERRIDE-VALS)
                                          (:REWRITE SVTV-DATA-OBJ-P-OF-<DATA>)
                                          (:REWRITE SVTV-PROBEALIST-P-OF-PIPELINE-SETUP->PROBES)
                                          (:TYPE-PRESCRIPTION SVTV-CONSTRUCT-TRIPLEMAPLIST))))
       (b* (((svtv-data-obj x) (<data>))
            ((pipeline-setup x.pipeline-setup)))
         (svtv-construct-triplemaplist x.pipeline-setup.override-tests
                                       x.pipeline-setup.override-vals
                                       x.pipeline-setup.probes))
       ///
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
                                     (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLEMAPLIST-SYNTAX-CHECK)))))
       (in-theory (disable (<name>-triplemaplist))))

     (define <name>-input-vars ()
       :prepwork ((local (in-theory nil))
                  (defconst *<name>-input-vars*
                    (b* (((svtv-data-obj x) (<data>))
                         ((pipeline-setup x.pipeline-setup)))
                      (mergesort (append (svex-alist-vars x.pipeline-setup.initst)
                                         (svex-alistlist-vars x.pipeline-setup.inputs))))))
       :returns (vars svarlist-p
                      :hints (("goal" :in-theory '((svarlist-p)
                                                   (<name>-input-vars)))))
       *<name>-input-vars*
       ///
       (in-theory (disable (<name>-input-vars))))

     (local
      (define <name>-spec ()
        :prepwork ((local (in-theory nil)))
        :returns (spec svtv-spec-p
                       :hints (("goal" :in-theory '(svtv-spec-p-of-svtv-data-obj->spec
                                                    <name>-spec))))
        :guard-hints (("goal" :in-theory '(SVTV-DATA-OBJ-P-OF-<DATA>)))
        (svtv-data-obj->spec (<data>))
        ///
        (in-theory (disable (<name>-spec)))
  
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

  
        (defretd svtv-run-of-<name>-is-svtv-spec-run-of-<name>-spec
          (svex-envs-equivalent (svtv-run (<name>) env
                                          :boolvars boolvars
                                          :simplify simplify
                                          :quiet quiet
                                          :readable readable
                                          :allvars allvars)
                                (svtv-spec-run spec env))
          :hints(("Goal" :in-theory '((:DEFINITION <NAME>-SPEC)
                                      (:EQUIVALENCE SVEX-ENVS-EQUIVALENT-IS-AN-EQUIVALENCE)
                                      (:REWRITE <DATA>-CORRECT)
                                      (:REWRITE <DATA>-FACTS-FOR-SPEC)
                                      (:REWRITE
                                       SVTV-RUN-OF-<NAME>-IS-EVAL-<DATA>-PIPELINE)
                                      (:REWRITE SVTV-SPEC-RUN-OF-SVTV-DATA-OBJ->SPEC)))))))

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
       (in-theory (disable (<ideal-name>)))

       (fgl::remove-fgl-rewrite <ideal-name>)
       (fgl::disable-execution <ideal-name>)
       ;; (defconst *<name>-phase-count*
       ;;   (b* (((svtv-data-obj x) (<data>))
       ;;        ((pipeline-setup x.pipeline-setup)))
       ;;     (* (len x.cycle-phases)
       ;;        (len (svtv-probealist-outvars x.pipeline-setup.probes)))))

       (local (defthm <data>-facts
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
                          set-equiv-by-mergesort-equal
                          (mergesort)
                          (append)
                          (svex-alist-vars)
                          (svex-alistlist-vars)
                          (<name>-input-vars))))))

       (defret no-duplicate-state-keys-of-<ideal-name>
         (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm spec))))
         :hints (("goal" :in-theory '(<data>-facts
                                      <data>-correct
                                      <ideal-name>
                                      design->ideal-fsm
                                      fields-of-svtv-data-obj->ideal-spec
                                      svex-alist-keys-of-flatnorm->ideal-fsm-nextstate
                                      svex-alist-keys-of-delays-of-flatnorm-add-overrides
                                      delays-of-design->flatnorm-of-svtv-data-obj))
                 (and stable-under-simplificationp
                      '(:in-theory '(hons-dups-p-when-variable-free
                                     no-duplicatesp-by-hons-dups-p)))
                 ))
       
       (defret initst-keys-of-<ideal-name>
         (equal (svex-alist-keys (svtv-spec->initst-alist spec))
                (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm spec))))
         :hints (("goal" :in-theory '(<data>-facts
                                      <data>-correct
                                      <ideal-name>
                                      design->ideal-fsm
                                      fields-of-svtv-data-obj->ideal-spec
                                      svex-alist-keys-of-flatnorm->ideal-fsm-nextstate
                                      svex-alist-keys-of-delays-of-flatnorm-add-overrides
                                      delays-of-design->flatnorm-of-svtv-data-obj))
                 (and stable-under-simplificationp
                      '(:in-theory '((<data>)
                                     (flatnorm-res->delays)
                                     (svex-alist-keys)
                                     (svtv-data-obj->flatnorm)
                                     (pipeline-setup->initst)
                                     (svtv-data-obj->pipeline-setup))))))

       (defret probe-keys-of-<ideal-name>
         (equal (alist-keys (svtv-spec->probes spec))
                (svex-alist-keys (svtv->outexprs (<name>))))
         :hints (("goal" :in-theory '(<data>-facts
                                      <data>-correct
                                      <ideal-name>
                                      design->ideal-fsm
                                      fields-of-svtv-data-obj->ideal-spec
                                      svex-alist-keys-of-flatnorm->ideal-fsm-nextstate
                                      svex-alist-keys-of-delays-of-flatnorm-add-overrides
                                      delays-of-design->flatnorm-of-svtv-data-obj))
                 (and stable-under-simplificationp
                      '(:in-theory '((<data>)
                                     (<name>)
                                     (svtv->outexprs)
                                     (svex-alist-keys)
                                     (alist-keys)
                                     (pipeline-setup->probes)
                                     (svtv-data-obj->pipeline-setup))))))

       (defret cycle-outputs-captured-of-<ideal-name>
         (svtv-cyclephaselist-has-outputs-captured
          (svtv-spec->cycle-phases spec))
         :hints (("goal" :in-theory '(<ideal-name>
                                      fields-of-svtv-data-obj->ideal-spec
                                      (svtv-data-obj->cycle-phases)
                                      (svtv-cyclephaselist-has-outputs-captured)
                                      (<data>)))))
         
  

       (defret <ideal-name>-refines-<name>
         (b* (((svtv-spec spec))
              (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
              (impl-run (svtv-run (<name>) pipe-env)))
           (implies (and 
                     (svtv-override-triplemaplist-muxes-<<= (<name>-triplemaplist) pipe-env spec-pipe-env spec-run)
                     (svtv-override-triplemaplist-muxtests-subsetp (<name>-triplemaplist) spec-pipe-env pipe-env)
                
                     (svex-env-<<= (svex-env-reduce (<name>-input-vars) pipe-env)
                                   spec-pipe-env)
                     (svarlist-override-p (svex-envlist-all-keys spec-base-ins) nil))
                    (svex-env-<<= impl-run spec-run)))
         :hints(("Goal" :in-theory '((:CONGRUENCE
                                      SET-EQUIV-IMPLIES-SVEX-ENVS-EQUIVALENT-SVEX-ENV-REDUCE-1)
                                     (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
                                     (:DEFINITION <IDEAL-NAME>)
                                     (:DEFINITION <NAME>-SPEC)
                                     (:DEFINITION NOT)
                                     (:REWRITE <DATA>-CORRECT)
                                     (:REWRITE <DATA>-FACTS)
                                     (:REWRITE SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-SPEC-RUN)
                                     (:REWRITE
                                      SVTV-RUN-OF-<NAME>-IS-SVTV-SPEC-RUN-OF-<NAME>-SPEC)
                                     (:REWRITE SYNTAX-CHECK-OF-<NAME>-TRIPLEMAPLIST)
                                     (:TYPE-PRESCRIPTION LEN)
                                     (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
                                     ;; (:TYPE-PRESCRIPTION SVTV-OVERRIDE-TRIPLEMAPLIST-OK)
                                     )
                 :do-not-induct t)))

       (defret <ideal-name>-refines-<ideal-name>
         (b* (((svtv-spec spec))
              (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
              (impl-run (svtv-spec-run spec pipe-env)))
           (implies (and 
                     (svtv-override-triplemaplist-muxes-<<= (<name>-triplemaplist) pipe-env spec-pipe-env spec-run)
                     (svtv-override-triplemaplist-muxtests-subsetp (<name>-triplemaplist) spec-pipe-env pipe-env)
                
                     (svex-env-<<= (svex-env-reduce (<name>-input-vars) pipe-env)
                                   spec-pipe-env)
                     (svarlist-override-p (svex-envlist-all-keys spec-base-ins) nil))
                    (svex-env-<<= impl-run spec-run)))
         :hints(("Goal" :in-theory '((:CONGRUENCE
                                      SET-EQUIV-IMPLIES-SVEX-ENVS-EQUIVALENT-SVEX-ENV-REDUCE-1)
                                     (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
                                     (:DEFINITION <IDEAL-NAME>)
                                     (:DEFINITION <NAME>-SPEC)
                                     (:DEFINITION NOT)
                                     (:REWRITE <DATA>-CORRECT)
                                     (:REWRITE <DATA>-FACTS)
                                     (:REWRITE SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-IDEAL-SPEC-RUN)
                                     (:REWRITE
                                      SVTV-RUN-OF-<NAME>-IS-SVTV-SPEC-RUN-OF-<NAME>-SPEC)
                                     (:REWRITE SYNTAX-CHECK-OF-<NAME>-TRIPLEMAPLIST)
                                     (:TYPE-PRESCRIPTION LEN)
                                     (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
                                     ;; (:TYPE-PRESCRIPTION SVTV-OVERRIDE-TRIPLEMAPLIST-OK)
                                     )
                 :do-not-induct t)))

       (defret <ideal-name>-refines-<name>-on-same-envs
         (b* ((spec-run (svtv-spec-run spec pipe-env :base-ins spec-base-ins :initst spec-initst))
              (impl-run (svtv-run (<name>) pipe-env)))
           (implies (svarlist-override-p (svex-envlist-all-keys spec-base-ins) nil)
                    (svex-env-<<= impl-run spec-run)))
         :hints (("goal" :in-theory '(<ideal-name>-refines-<name>
                                      svtv-override-triplemaplist-muxtests-subsetp-of-same-envs
                                      svtv-override-triplemaplist-muxes-<<=-of-same-envs
                                      svex-env-reduce-<<=-same
                                      (svex-envlist-all-keys)
                                      (svarlist-override-p)))))

       (defret <ideal-name>-refines-<ideal-name>-on-same-envs
         (b* (((svtv-spec spec))
              (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
              (impl-run (svtv-spec-run spec spec-pipe-env)))
           (implies (svarlist-override-p (svex-envlist-all-keys spec-base-ins) nil)
                    (svex-env-<<= impl-run spec-run)))
         :hints (("goal" :in-theory '(<ideal-name>-refines-<ideal-name>
                                      svtv-override-triplemaplist-muxtests-subsetp-of-same-envs
                                      svtv-override-triplemaplist-muxes-<<=-of-same-envs
                                      svex-env-reduce-<<=-same
                                      (svex-envlist-all-keys)
                                      (svarlist-override-p))))))

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
                                   (svarlist-override-p)
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
                               (svarlist-override-p)
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
                               )))))))


(defun def-svtv-ideal-fn (ideal-name svtv-name data-name)
  (declare (xargs :mode :program))
  (acl2::template-subst *svtv-idealize-template*
                        :str-alist `(("<NAME>" . ,(symbol-name svtv-name))
                                     ("<DATA>" . ,(symbol-name data-name))
                                     ("<IDEAL-NAME>" . ,(symbol-name ideal-name)))
                        :pkg-sym ideal-name))

(defmacro def-svtv-ideal (ideal-name svtv-name data-name)
  (def-svtv-ideal-fn ideal-name svtv-name data-name))




;;; For each decomposition proof, we'll have a fixed set of signals overridden
;;; on both the spec and impl side.  On the spec side, this set of signals will
;;; likely be constant over several theorems that we want to compose together;
;;; this will be specified by svtv-override-triples-envs-match.  On the impl
;;; side, we'll have a more explicit env, not just a free variable with hyps
;;; but an alist constructed with cons/append/etc. We'll extract from this term
;;; a substitution which should contain all the constant bindings and bind all
;;; other variables to themselves, so that (svex-alist-eval subst env) ~= env.



;; The following functions say:
;; - Every triplemap test evaluated in env matches its evaluation in spec.
;; - Every triplemap value evaluated in env is >>= its evaluation in spec.
(define svtv-override-triple-envs-match ((triple svtv-override-triple-p)
                                         (env svex-env-p)
                                         (spec svex-env-p))
  (b* (((svtv-override-triple triple)))
    (and (equal (svex-eval triple.test env) (svex-eval triple.test spec))
         (4vec-<<= (svex-eval triple.val spec) (svex-eval triple.val env)))))

(define svtv-override-triplemap-envs-match ((triplemap svtv-override-triplemap-p)
                                            (env svex-env-p)
                                            (spec svex-env-p))
  :returns (ok)
  (if (atom triplemap)
      t
    (if (mbt (and (consp (car triplemap))
                  (svar-p (caar triplemap))))
        (and (svtv-override-triple-envs-match (cdar triplemap) env spec)
             (svtv-override-triplemap-envs-match (cdr triplemap) env spec))
      (svtv-override-triplemap-envs-match (cdr triplemap) env spec)))
  ///
  (defret <fn>-implies
    (implies (and ok
                  (svar-p key)
                  (hons-assoc-equal key triplemap))
             (b* ((triple (cdr (hons-assoc-equal key (svtv-override-triplemap-fix triplemap)))))
               (and (equal (svex-eval (svtv-override-triple->test triple) env)
                           (svex-eval (svtv-override-triple->test triple) spec))
                    (4vec-<<= (svex-eval (svtv-override-triple->test triple) spec)
                              (svex-eval (svtv-override-triple->test triple) env)))))
    :hints(("Goal" :in-theory (enable svtv-override-triplemap-fix
                                      svtv-override-triple-envs-match))))

  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemaplist-envs-match ((triplemaps svtv-override-triplemaplist-p)
                                                (env svex-env-p)
                                                (spec svex-env-p))
  (if (atom triplemaps)
      t
    (and (svtv-override-triplemap-envs-match (car triplemaps) env spec)
         (svtv-override-triplemaplist-envs-match (cdr triplemaps) env spec))))





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




;; Simplifying the svtv-override-triplemaplist-muxtests-subsetp.  We should
;; concrete values for all the tests -- from the impl-env, we have the
;; substitution with svtv-override-subst-matches-env, and from the spec-env, we
;; have spec-override-consts.

;; So for muxtests-subsetp, we should be able to just check these two envs by
;; execution and not leave behind any further proof obligations.

(define svtv-override-test-check-muxtest-subsetp ((test svex-p)
                                                  (impl-subst svex-alist-p)
                                                  (spec-override-consts svex-env-p))
  :returns (ok)
  (b* (((when (svex-case test :quote))
        ;; Doesn't need to be checked because impl and spec test will both evaluate to the same.
        t)
       (spec-test (svex-eval test spec-override-consts))
       ((when (equal (4vec-1mask spec-test) 0))
        ;; Always satisfies 4vec-muxtest-subsetp
        t)
       (impl-test (svex-subst test impl-subst))
       ((when (equal impl-test (svex-quote (2vec -1))))
        ;; Always satisfies 4vec-muxtest-subsetp
        t))
    (svex-case impl-test
      :quote (or (4vec-muxtest-subsetp spec-test impl-test.val)
                 (cw "======  WARNING  =======~%~
Muxtest check failed: ~x0 evaluated to ~x1 (spec), ~x2 (impl) which does not satisfy ~x3~%"
                     test spec-test impl-test.val))
      :otherwise (cw "======  WARNING  =======~%~
Muxtest check failed: ~x0 evaluated to ~x1 (spec) but reduced to a non-constant for impl: ~x2~%"
                     test spec-test impl-test)))
  ///
  (defretd 4vec-muxtest-subsetp-when-<fn>
    :pre-bind ((test (svtv-override-triple->test triple)))
    (implies (and (svtv-override-triple-envs-match triple spec-env spec-override-consts)
                  (svtv-override-subst-matches-env impl-subst impl-env)
                  ok)
             (4vec-muxtest-subsetp (svex-eval test spec-env)
                                   (svex-eval test impl-env)))
    :hints(("Goal" :in-theory (e/d (svtv-override-triple-envs-match
                                    svtv-override-subst-matches-env)
                                   (svex-eval-of-svex-subst))
            :use ((:instance svex-eval-of-svex-subst
                   (pat (svtv-override-triple->test triple))
                   (al impl-subst)
                   (env impl-env)))))))


(define svtv-override-triplemap-check-muxtest-subsetp ((x svtv-override-triplemap-p)
                                                       (impl-subst svex-alist-p)
                                                       (spec-override-consts svex-env-p))
  :returns (ok)
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (svar-p (caar x)))))
             (svtv-override-test-check-muxtest-subsetp (svtv-override-triple->test (cdar x))
                                                       impl-subst spec-override-consts))
         (svtv-override-triplemap-check-muxtest-subsetp (cdr x) impl-subst spec-override-consts)))
  ///
  (defretd svex-envs-svexlist-muxtests-subsetp-when-<fn>
    (implies (and (svtv-override-triplemap-envs-match x spec-env spec-override-consts)
                  (svtv-override-subst-matches-env impl-subst impl-env)
                  ok)
             (svex-envs-svexlist-muxtests-subsetp (svtv-override-triplemap->tests x) spec-env impl-env))
    :hints(("Goal" :in-theory (e/d (svtv-override-triplemap-envs-match
                                    svex-envs-svexlist-muxtests-subsetp
                                    svtv-override-triplemap->tests
                                    4vec-muxtest-subsetp-when-svtv-override-test-check-muxtest-subsetp)))))

  (local (in-theory (enable svtv-override-triplemap-fix))))


(define svtv-override-triplemaplist-check-muxtest-subsetp ((x svtv-override-triplemaplist-p)
                                                           (impl-subst svex-alist-p)
                                                           (spec-override-consts svex-env-p))
  :returns (ok)
  (if (atom x)
      t
    (and (svtv-override-triplemap-check-muxtest-subsetp (car x) impl-subst spec-override-consts)
         (svtv-override-triplemaplist-check-muxtest-subsetp (cdr x) impl-subst spec-override-consts)))
  ///
  (defretd svtv-override-triplemaplist-muxtests-subsetp-when-<fn>
    (implies (and (svtv-override-triplemaplist-envs-match x spec-env spec-override-consts)
                  (svtv-override-subst-matches-env impl-subst impl-env)
                  ok)
             (svtv-override-triplemaplist-muxtests-subsetp x spec-env impl-env))
    :hints(("Goal" :in-theory (e/d (svtv-override-triplemaplist-envs-match
                                    svtv-override-triplemaplist-muxtests-subsetp
                                    svex-envs-svexlist-muxtests-subsetp-when-svtv-override-triplemap-check-muxtest-subsetp)))))
  
  ;; !!! This will be used to compute the list of tests that need to be
  ;; resolved when generalizing an SVTV theorem.
  (defthmd svtv-override-triplemaplist-muxtests-subsetp-simplify-for-idealize
    (implies (and (syntaxp (cmr::term-variable-free-p x))
                  (svtv-override-triplemaplist-envs-match x spec-env spec-override-consts)
                  (bind-free (b* (((mv ok subst) (svex-env-term-extract-substitution impl-env)))
                               (and ok
                                    `((impl-subst . ',(make-fast-alist subst)))))
                             (impl-subst))
                  (svtv-override-subst-matches-env impl-subst impl-env)
                  (svtv-override-triplemaplist-check-muxtest-subsetp x impl-subst (make-fast-alist spec-override-consts)))
             (svtv-override-triplemaplist-muxtests-subsetp x spec-env impl-env))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-muxtests-subsetp-when-svtv-override-triplemaplist-check-muxtest-subsetp))))

  (cmr::def-force-execute svtv-override-triplemaplist-check-muxtest-subsetp-when-variable-free
    svtv-override-triplemaplist-check-muxtest-subsetp))













(defprod svtv-override-check
  ((impl-test svex-p)
   (impl-val svex-p)
   (spec-test svex-p)
   (spec-val svex-p)
   (refvar svar-p))
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
           (4vec-override-mux-<<= (svex-eval x1.impl-test impl-env)
                                  (svex-eval x1.impl-val impl-env)
                                  (svex-eval x1.spec-test spec-env)
                                  (svex-eval x1.spec-val spec-env)
                                  (svex-env-lookup x1.refvar ref-env)))
         (svtv-override-checklist-ok (cdr x) impl-env spec-env ref-env)))
  ///
  (defthm svtv-override-checklist-ok-of-cons-quote
    (implies (syntaxp (quotep x1))
             (equal (svtv-override-checklist-ok (cons x1 rest) impl-env spec-env ref-env)
                    (and (b* (((svtv-override-check x1)))
                           (4vec-override-mux-<<=
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
                            (svex-env-lookup x1.refvar ref-env)))
                         (svtv-override-checklist-ok rest impl-env spec-env ref-env))))
    :hints(("Goal" :in-theory (enable svex-eval))))

  (defthm svtv-override-checklist-ok-of-cons
    (equal (svtv-override-checklist-ok (cons x1 rest) impl-env spec-env ref-env)
           (and (b* (((svtv-override-check x1)))
                  (4vec-override-mux-<<= (svex-eval x1.impl-test impl-env)
                                  (svex-eval x1.impl-val impl-env)
                                  (svex-eval x1.spec-test spec-env)
                                  (svex-eval x1.spec-val spec-env)
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
  :hints(("Goal" :in-theory (e/d (4vec-bit?! 4vec-1mask)
                                 (lognot logior)))))


(defthm 4vec-override-mux-<<=-when-impl-test-empty
  (implies (equal (4vec-1mask impl-test) 0)
           (4vec-override-mux-<<= impl-test impl-val spec-test spec-val spec-ref))
  :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=))))



(define svtv-override-triple-analyze-necessary-mux-<<=-check ((x svtv-override-triple-p)
                                                              (impl-subst svex-alist-p)
                                                              (spec-override-consts svex-env-p))
  :returns (checks svtv-override-checklist-p)
  (b* (((svtv-override-triple x))
       ((when (and (svex-case x.test :quote)
                   (svex-case x.val :quote)))
        ;; Doesn't need to be checked because 4vec-override-mux-<<= of same tests and vals is always true.
        nil)
       (impl-test (svex-subst x.test impl-subst))
       ((when (and (svex-case impl-test :quote)
                   (equal (4vec-1mask (svex-quote->val impl-test)) 0)))
        ;; Doesn't need to be checked because 4vec-override-mux-<<= is true when 4vec-mask of impl-test is 0
        nil)
       (impl-val (svex-subst x.val impl-subst))
       ((when (equal impl-val (svex-x)))
        ;; Doesn't need to be checked because 4vec-override-mux-<<= is true when impl-val is x.
        nil)
       (spec-test (svex-eval x.test spec-override-consts))
       (spec-val  (svex-eval x.val spec-override-consts))
       (spec-val-expr (if (2vec-p spec-val) (svex-quote spec-val) x.val)))
    (list (svtv-override-check impl-test impl-val
                               (svex-quote spec-test)
                               spec-val-expr
                               x.refvar)))
  ///
  (defret <fn>-correct
    (implies (and (svtv-override-subst-matches-env impl-subst impl-env)
                  (svtv-override-triple-envs-match x spec-env spec-override-consts))
             (equal (svtv-override-checklist-ok checks impl-env spec-env ref-env)
                    (svtv-override-triple-mux-<<= x impl-env spec-env ref-env)))
    :hints(("Goal" :in-theory (e/d (svtv-override-triple-mux-<<=
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



(define svtv-override-triplemap-analyze-necessary-mux-<<=-checks ((x svtv-override-triplemap-p)
                                                                  (impl-subst svex-alist-p)
                                                                  (spec-override-consts svex-env-p))
  :returns (checks svtv-override-checklist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-override-triplemap-analyze-necessary-mux-<<=-checks (cdr x) impl-subst spec-override-consts))
       (checks1 (svtv-override-triple-analyze-necessary-mux-<<=-check (cdar x) impl-subst spec-override-consts)))
    (mbe :logic (append checks1
                        (svtv-override-triplemap-analyze-necessary-mux-<<=-checks (cdr x) impl-subst spec-override-consts))
         :exec (if checks1
                   (append checks1
                           (svtv-override-triplemap-analyze-necessary-mux-<<=-checks (cdr x) impl-subst spec-override-consts))
                 (svtv-override-triplemap-analyze-necessary-mux-<<=-checks (cdr x) impl-subst spec-override-consts))))
  ///
  (defret <fn>-correct
    (implies (and (svtv-override-subst-matches-env impl-subst impl-env)
                  (svtv-override-triplemap-envs-match x spec-env spec-override-consts))
             (equal (svtv-override-checklist-ok checks impl-env spec-env ref-env)
                    (svtv-override-triplemap-muxes-<<= x impl-env spec-env ref-env)))
    :hints(("Goal" :in-theory (e/d (svtv-override-triplemap-muxes-<<=
                                    svtv-override-triplemap-envs-match)))))

  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks ((x svtv-override-triplemaplist-p)
                                                                      (impl-subst svex-alist-p)
                                                                      (spec-override-consts svex-env-p))
  :returns (checks svtv-override-checklist-p)
  (if (atom x)
      nil
    (append (svtv-override-triplemap-analyze-necessary-mux-<<=-checks (car x) impl-subst spec-override-consts)
            (svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks (cdr x) impl-subst spec-override-consts)))
  ///
  (defret <fn>-correct
    (implies (and (svtv-override-subst-matches-env impl-subst impl-env)
                  (svtv-override-triplemaplist-envs-match x spec-env spec-override-consts))
             (equal (svtv-override-checklist-ok checks impl-env spec-env spec-run)
                    (svtv-override-triplemaplist-muxes-<<= x impl-env spec-env spec-run)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-muxes-<<=
                                      svtv-override-triplemaplist-envs-match))))

  ;; !!! This will be used to compute the list of tests that need to be
  ;; resolved when generalizing an SVTV theorem.
  (defthmd svtv-override-triplemaplist-muxes-<<=-simplify-for-idealize
    (implies (and (syntaxp (cmr::term-variable-free-p x))
                  (svtv-override-triplemaplist-envs-match x spec-env spec-override-consts)
                  (bind-free (b* (((mv ok subst) (svex-env-term-extract-substitution impl-env)))
                               (and ok
                                    `((impl-subst . ',(make-fast-alist subst)))))
                             (impl-subst))
                  (svtv-override-subst-matches-env impl-subst impl-env))
             (equal (svtv-override-triplemaplist-muxes-<<= x impl-env spec-env spec-run)
                    (svtv-override-checklist-ok
                     (svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks x impl-subst (make-fast-alist spec-override-consts))
                     impl-env spec-env spec-run)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks-correct))))

  (cmr::def-force-execute svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks-when-variable-free
    svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks))









(defthm 4vec-bit?!-same-then-else
  (equal (4vec-bit?! test then then) (4vec-fix then))
  :hints(("Goal" :in-theory (enable 4vec-bit?!))
         (bitops::logbitp-reasoning)))


(defthm 4vec-override-mux-<<=-when-no-spec-override-and-impl-val-same-as-ref
  (implies (equal (4vec-1mask spec-test) 0)
           (4vec-override-mux-<<= impl-test val spec-test spec-val val))
  :hints(("Goal" :in-theory (enable 4vec-override-mux-<<=))))


                
(def-ruleset! svtv-idealized-thm-rules
  '(
    (:CONGRUENCE
     CONS-4VEC-EQUIV-CONGRUENCE-ON-V-UNDER-SVEX-ENV-EQUIV)
    (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
    (:DEFINITION 4VEC-EQUIV$INLINE)
    (:definition svtv-override-triple-mux-<<=)

    (:DEFINITION SVEX-ENV-FASTLOOKUP)
    (:DEFINITION SVTV-OVERRIDE-TRIPLE-MUX-<<=)
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
    (:executable-counterpart SVTV-OVERRIDE-TRIPLEMAPLIST-ANALYZE-NECESSARY-MUX-<<=-CHECKS)
    (:META HONS-INTERSECTION-FORCE-EXECUTE)
    (:meta svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks-when-variable-free)
    (:meta svtv-override-triplemaplist-check-muxtest-subsetp-when-variable-free)
    (:meta svtv-override-subst-matches-env-meta)
    (:REWRITE 4VEC-<<=-2VEC)
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
    (:rewrite svtv-override-triplemaplist-muxtests-subsetp-simplify-for-idealize)
    (:rewrite svtv-override-triplemaplist-muxes-<<=-simplify-for-idealize)
    ;; (:rewrite SVTV-OVERRIDE-TRIPLEMAPLIST-MUXES-<<=-SIMPLIFY-WHEN-KEYS)
    ;; (:rewrite SVTV-OVERRIDE-TRIPLELIST-MUXES-<<=-OF-CONS)
    ;; (:rewrite SVTV-OVERRIDE-TRIPLELIST-MUXES-<<=-OF-nil)

    (:rewrite 4VEC-OVERRIDE-MUX-<<=-OF-SAME-TEST/VAL)
    (:rewrite 4vec-override-mux-<<=-when-no-spec-override-and-impl-val-same-as-ref)

    (:rewrite svex-env-lookup-of-svex-env-reduce)
    (:executable-counterpart member-equal)
    (:executable-counterpart svarlist-fix$inline)
    ))


(define svtv-override-triplemaplist->tests ((x svtv-override-triplemaplist-p))
  :returns (tests svexlist-p)
  (if (atom x)
      nil
    (append (svtv-override-triplemap->tests (car x))
            (svtv-override-triplemaplist->tests (cdr x)))))

(define svtv-override-triplemap->vals ((triplemap svtv-override-triplemap-p))
  :returns (vals svexlist-p)
  (if (atom triplemap)
      nil
    (if (mbt (and (consp (car triplemap))
                  (svar-p (caar triplemap))))
        (cons (svtv-override-triple->val (cdar triplemap))
              (svtv-override-triplemap->vals (cdr triplemap)))
      (svtv-override-triplemap->vals (cdr triplemap))))
  ///
  (local (in-theory (enable svtv-override-triplemap-fix))))

(define svtv-override-triplemaplist->vals ((x svtv-override-triplemaplist-p))
  :returns (vals svexlist-p)
  (if (atom x)
      nil
    (append (svtv-override-triplemap->vals (car x))
            (svtv-override-triplemaplist->vals (cdr x)))))




(program)


;; In the context of these svtv-idthm functions, triples is an alist mapping
;; value variables to reference variables, derived from the triplemaplist.
(defun svtv-idthm-override-var-instantiation (override-vars triple-val-alist triples-name ideal)
  (b* (((when (Atom override-vars)) nil)
       (valvar (car override-vars))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-idealized-thm "Override name not present in triples ~x0: ~x1~%"
                            (list triples-name) valvar)))
    (cons `(,valvar (svex-env-lookup ',(svtv-override-triple->refvar trip)
                                     (svtv-spec-run (,ideal)
                                                    env
                                                    :base-ins base-ins
                                                    :initst initst)))
          (svtv-idthm-override-var-instantiation (cdr override-vars) triple-val-alist triples-name ideal))))

(defun svtv-idthm-spec-override-var-instantiation (override-vars)
  (b* (((when (Atom override-vars)) nil)
       (valvar (car override-vars)))
    (cons `(,valvar (svex-env-lookup ',valvar env))
          (svtv-idthm-spec-override-var-instantiation (cdr override-vars)))))


(defun svtv-idthm-override-subst (override-vars triple-val-alist triples-name)
  (b* (((when (Atom override-vars)) nil)
       (valvar (car override-vars))
       (trip (cdr (hons-get valvar triple-val-alist)))
       ((unless trip) (er hard? 'def-svtv-idealized-thm "Override name not present in triples ~x0: ~x1~%"
                          (list triples-name) valvar))
       ((svtv-override-triple trip)))
    ;(cons (cons valvar trip.val)
    (if (svex-case trip.test :var)
        (cons (cons (svex-var->name trip.test) -1)
              (svtv-idthm-override-subst (cdr override-vars) triple-val-alist triples-name))
      (svtv-idthm-override-subst (cdr override-vars) triple-val-alist triples-name))))



(defun svtv-idthm-final-thm (x)
  (b* (((svtv-generalized-thm x))
       (template
         '(<defthm> <name>
            (b* (((svassocs <input-var-svassocs>
                            <spec-override-svassocs>) env)
                 (run (svtv-spec-run (<ideal>) env
                                     :base-ins base-ins
                                     :initst initst))
                 ((svassocs <override-svassocs>) run))
              (implies (and (svtv-override-triplemaplist-envs-match
                             (<triplemaps>) env <const-overrides>)
                            <hyp>
                            <input-binding-hyp>
                            <override-binding-hyp>
                            (svarlist-override-p (svex-envlist-all-keys base-ins) nil))
                       (b* (((svassocs <outputs>) run))
                         <concl>)))
            <args>
            (:@ :no-lemmas <hints-hints>)
            (:@ (not :no-lemmas)
             :hints (("Goal" :use ((:instance
                                    (:@ (not :use-ideal) <ideal>-refines-<svtv>)
                                    (:@ :use-ideal <ideal>-refines-<ideal>)
                                    (spec-pipe-env env)
                                    (spec-base-ins base-ins)
                                    (spec-initst initst)
                                    (pipe-env (b* ((?run (svtv-spec-run (<ideal>) env
                                                                        :base-ins base-ins
                                                                        :initst initst))
                                                   ((svassocs <override-inst-svassocs>) run)
                                                   ((svassocs <spec-override-inst-svassocs>
                                                              <input-unbound-svassocs>) env))
                                                (APPEND <input-bindings>
                                                        <input-vars>
                                                        <override-tests>
                                                        <override-bindings>
                                                        <override-vals>))))
                                   (:instance <name>-override-lemma
                                    <spec-override-var-instantiation>
                                    <override-var-instantiation>
                                    <input-var-instantiation>))
                      :in-theory (acl2::e/d**
                                  ((:EXECUTABLE-COUNTERPART <SVTV>-TRIPLEMAPLIST)
                                   (:REWRITE SVARLIST-P-OF-<SVTV>-INPUT-VARS)
                                   (:ruleset svtv-idealized-thm-rules))
                                  )
                      )
                     . <hints>))
            :rule-classes <rule-classes>)))
    (acl2::template-subst
     template
     :atom-alist
     `((<hyp> . ,x.hyp)
       (<concl> . ,x.concl)
       (<ideal> . ,x.ideal)
       (<defthm> . ,x.final-defthm)
       (<triplemaps> . ,x.triples-name)
       (<const-overrides> . ',(svtv-idthm-override-subst
                               (append (alist-keys x.spec-override-var-bindings) x.spec-override-vars)
                               x.triple-val-alist x.triples-name))
       (<hints> . ,x.hints)
       (<input-bindings> . (list . ,(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings)))
       (<input-vars> . (list . ,(svtv-genthm-var-alist-termlist x.input-vars)))
       (<override-tests> . ',(svtv-genthm-override-test-alist
                              (append (alist-keys x.override-var-bindings)
                                      (alist-keys x.spec-override-var-bindings)
                                      x.spec-override-vars
                                      x.override-vars)
                              x.triple-val-alist x.triples-name))
       (<override-bindings> . (list . ,(svtv-genthm-input-var-bindings-alist-termlist
                                        (append x.spec-override-var-bindings x.override-var-bindings))))
       (<override-vals> . (list . ,(svtv-genthm-var-alist-termlist (append x.spec-override-vars x.override-vars))))
       (<rule-classes> . ,x.rule-classes))
     :splice-alist
     `((<input-var-svassocs> . ,(append x.input-vars (strip-cars x.input-var-bindings)))
       (<input-unbound-svassocs> . ,x.input-vars)
       (<override-svassocs> . ,(svtv-genthm-override-svassocs (append x.override-vars (alist-keys x.override-var-bindings))
                                                              x.triple-val-alist x.triples-name))
       (<override-inst-svassocs> . ,(svtv-genthm-override-svassocs x.override-vars
                                                              x.triple-val-alist x.triples-name))
       (<spec-override-svassocs> . ,(svtv-genthm-override-svassocs (append x.spec-override-vars (alist-keys x.spec-override-var-bindings))
                                                                   x.triple-val-alist x.triples-name))
       (<spec-override-inst-svassocs> . ,(svtv-genthm-override-svassocs x.spec-override-vars
                                                                        x.triple-val-alist x.triples-name))
       (<input-binding-hyp> .  ,(svtv-genthm-input-binding-hyp-termlist x.input-var-bindings))
       (<override-binding-hyp> .  ,(svtv-genthm-input-binding-hyp-termlist (append x.spec-override-var-bindings
                                                                                   x.override-var-bindings)))
       (<override-var-instantiation> . ,(svtv-idthm-override-var-instantiation x.override-vars x.triple-val-alist x.triples-name x.ideal))
       (<spec-override-var-instantiation> . ,(svtv-idthm-spec-override-var-instantiation x.spec-override-vars))
       (<input-var-instantiation> . ,(svtv-genthm-input-var-instantiation x.input-vars))
       (<outputs> . ,x.output-vars)
       (<enable> . ,x.enable)
       (<hints-hints> . ,(and x.hints `(:hints ,x.hints)))
       (<args> . ,x.final-args))
     :str-alist `(("<NAME>" . ,(symbol-name x.name))
                  ("<SVTV>" . ,(symbol-name x.svtv))
                  ("<IDEAL>" . ,(symbol-name x.ideal)))
     :features (append (and x.no-lemmas '(:no-lemmas))
                       (and x.lemma-use-ideal '(:use-ideal)))
     :pkg-sym x.pkg-sym)))




(defun svtv-idealized-thm-events (x)
  (b* (((svtv-generalized-thm x))
       (err (svtv-genthm-error x))
       ((when err) (er hard? `(def-svtv-idealized-thm ,x.name) "Error: ~@0" err)))
    `(defsection ,x.name
       ,@(and (not x.no-lemmas)
              (let ((lemma (svtv-genthm-initial-override-lemma x)))
                (if x.lemma-nonlocal
                    `(,lemma)
                  `((local ,lemma)))))
       ,(svtv-idthm-final-thm x))))



(defun svtv-idealized-thm-fn (name args state)
  (declare (xargs :stobjs state))
  (b* ((defaults (table-alist 'svtv-idealized-thm-defaults (w state)))
       (ctx `(def-svtv-idealized-thm ,name))
       ((std::extract-keyword-args
         :defaults defaults
         :ctx ctx
         svtv
         ideal
         spec-override-var-bindings
         spec-override-vars
         override-var-bindings
         override-vars
         input-vars
         output-vars
         output-parts
         input-var-bindings
         enable
         unsigned-byte-hyps
         (hyp 't)
         concl
         (lemma-defthm 'fgl::def-fgl-thm)
         lemma-args
         lemma-nonlocal
         lemma-use-ideal
         no-lemmas
         no-integerp
         hints
         (final-defthm 'defthm)
         final-args
         (rule-classes ':rewrite)
         (pkg-sym name))
        args)
       
       ((mv err trans-parts state) (svtv-genthm-translate-lst output-parts ctx (w state) state))
       ((when err) (er soft ctx "Couldn't translate output-parts: ~@0~%" err))
       (output-part-vars (all-vars1-lst trans-parts nil))
       ((mv err svtv-val) (magic-ev-fncall svtv nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list svtv)))
       (triplemaplist (acl2::template-subst
                 '<svtv>-triplemaplist
                 :str-alist `(("<SVTV>" . ,(symbol-name svtv)))
                 :pkg-sym pkg-sym))
       ((mv err triplemaplist-val) (magic-ev-fncall triplemaplist nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list triplemaplist)))

       (triplelist (svtv-override-triplemaplist-to-triplelist triplemaplist-val))
       (triple-val-alist (svtv-override-triplelist-val-alist triplelist))

       
       (input-vars (if (equal input-vars :all)
                       (b* ((all-ins (svtv->ins svtv-val))
                            (ovr-controls (svex-alist-vars (svtv-override-triplemaplist->tests triplemaplist-val)))
                            (ovr-signals (svex-alist-vars (svtv-override-triplemaplist->vals triplemaplist-val)))
                            (all-ins (acl2::hons-set-diff all-ins (append ovr-controls ovr-signals
                                                                          (alist-keys input-var-bindings)))))
                         all-ins)
                     input-vars))
       (hyp (if unsigned-byte-hyps
                (b* ((inmasks (svtv->inmasks svtv-val))
                     (inputs (append input-vars override-vars spec-override-vars))
                     (masks (acl2::fal-extract inputs inmasks)))
                  `(and ,@(svtv-unsigned-byte-hyps masks) ,hyp))
              hyp))
       
       ;; (override-subst (make-fast-alist (svtv-idthm-override-subst override-vars triple-val-alist triplemaplist)))
       ;; (mux-<<=-triples
       ;;  (svtv-override-triplemaplist-analyze-necessary-mux-<<=-checks triplemaplist-val override-subst))
       ;; (muxtests (svtv-override-triplemaplist-analyze-necessary-muxtests triplemaplist-val override-subst (make-fast-alist const-overrides)))
       
       ;; (constlist-hyp `(and ,(if mux-<<=-triples
       ;;                           `(svtv-override-triplelist-muxes-<<=-of-nil(if consts
       ;;                    `(svtv-override-constantlist-ok ',consts run)
       ;;                  t))
       ((acl2::with-fast triple-val-alist)))

    (value
     (svtv-idealized-thm-events
      (make-svtv-generalized-thm
       :name name
       :override-vars override-vars
       :override-var-bindings override-var-bindings
       :spec-override-vars spec-override-vars
       :spec-override-var-bindings spec-override-var-bindings
       :input-vars input-vars
       :output-vars output-vars
       :output-parts output-parts
       :output-part-vars output-part-vars
       :input-var-bindings input-var-bindings
       :enable enable
       :hyp hyp
       :concl concl
       :svtv svtv
       :ideal ideal
       :lemma-nonlocal lemma-nonlocal
       :lemma-defthm lemma-defthm
       :lemma-args lemma-args
       :lemma-use-ideal lemma-use-ideal
       :hints hints
       :triples-name triplemaplist
       :triple-val-alist triple-val-alist
       :no-lemmas no-lemmas
       :no-integerp no-integerp
       :final-defthm final-defthm
       :final-args final-args
       :rule-classes rule-classes
       :pkg-sym pkg-sym)))))

(defmacro def-svtv-idealized-thm (name &rest args)
  `(make-event (svtv-idealized-thm-fn ',name ',args state)))




(logic)

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
                                  :var (equal (svex-env-lookup first.test.name env)
                                              (svex-env-lookup first.test.name spec))
                                  :otherwise (equal (svex-eval first.test env)
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




(defxdoc svex-fixpoint-decomposition-methodology
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

<p>This methodology's main user interface is @(see def-svtv-idealized-thm).
See that topic for usage.  In the rest of this topic we'll discuss how this
works and the solutions to certain complications.</p>


<p>To produce the generalized forms of the theorems above, we want a particular
property of the design: that if we override a signal with the value that it
would have had anyway, then the values of all signals are preserved. Stated in
terms of our imaginary @('run-design') function above, for the particular case
of the partial-products-value of our multiplier design:</p>

@({
 (defthm multiplier-partial-product-overrides-correct
   (let* ((base-run (run-design (multiplier) :inputs input-env))
          (partial-products-value (lookup 'partial-product-signal base-run))
          (override-run (run-design (multiplier)
                                    :inputs input-env
                                    :overrides `((partial-product-signal . ,partial-products-value)))))
      (all-lookups-equivalent override-run base-run)))
 })

<p>This theorem, along with a couple of other simpler facts that allow the
generalization of the input environment would be sufficient to let us
generalize @('multiplier-pp-sum-correct-override') to
@('multiplier-pp-sum-correct-gen').</p>

<p>Generally we also want to allow for multiple override signals in different combinations.
potentially overridden signals:</p>

@({
 (defthm multiplier-partial-product-overrides-correct
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

<p>This overrides-correct condition seems intuitively obvious and we would like
to prove it for all designs.  However, it is actually a fairly deep property of
the design object, and as we'll see, depending how we compose the design
together it may or may not be true.</p>

<p>The problematic cases have to do with designs where there are 0-delay
combinational loops.  These can occur due to latch-based logic or clock gating
logic, often enough that it isn't workable to just disallow them.</p>

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
actually compute the fixpoint.  Instead we use an approximate composition
method that is efficient, practially useful, and conservative with respect to
the fixpoint: that is, if a signal's value in this approximate composition is
non-X, then its fixpoint value must be the same.</p>

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
@(see def-svtv-idealized-thm).
</li>

</ul>
")


(defxdoc def-svtv-ideal
  :parents (svex-fixpoint-decomposition-methodology)
  :short "Define a non-executable, fixpoint-based analogue of a @(see symbolic-test-vector)."
  :long " <p>To use this, first define an SVTV using @(see defsvtv$)
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
computed for the SVTV.  See @(see svex-fixpoint-decomposition-methodology) for
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


(defxdoc def-svtv-idealized-thm
  :parents (svex-fixpoint-decomposition-methodology)
  :short "Prove a theorem about an idealized SVTV via a symbolic simulation lemma about the SVTV itself."
  :long "
<p>See @(see svex-fixpoint-decomposition-methodology) for background on the methodology that this supports.</p>

<p>Usage:</p>
@({
 (def-svtv-idealized-thm theorem-name
   :svtv svtv-name
   :ideal ideal-name
   :input-vars input-variable-list
   :input-var-bindings input-variable-binding-list
   :override-vars override-variable-list
   :override-var-bindings override-variable-binding-list
   :spec-override-vars override-variable-list
   :spec-override-var-bindings override-variable-binding-list
   :output-vars output-variable-list
   :output-parts output-part-list
   :hyp hypothesis-term
   :concl conclusion-term
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

<p>Prerequisite: What we are calling the \"ideal\" here must be a @(see
svtv-spec) object created for the given SVTV, which can be done using @(see
def-svtv-ideal).</p>

<p>We briefly describe the arguments of the macro and then we'll describe the
theorem proved in FGL and the generalized corollary this macro generates.</p>

<h3>Arguments</h3>

<ul>
<li>@(':svtv') is the name of the SVTV</li>

<li>@(':ideal') must be the name of the \"ideal\" function produced by @(see
def-svtv-ideal), a 0-ary function that produces a @(see svtv-spec) object
reflecting the same run as the SVTV, but based on a full fixpoint of the
hardware module.</li>

<li>@(':input-vars') are the names of any input variables of the SVTV that will
appear in the hypothesis or conclusion, except those that are bound in
@(':input-var-bindings'). Instead of a list of signals, users may pass \":all\"
parameter to get all the input variables that are not bound.</li>

<li>@(':input-var-bindings') is a list of @('let')-like bindings of input
variables to expressions.</li>

<li>@(':override-vars') is a list of override-value variables of the SVTV to be
overridden in the FGL theorem.</li>

<li>@(':override-var-bindings') is a list of @('let')-like bindings of override
value variables to expressions.</li>

<li>@(':spec-override-vars') is a list of override-value variables of the SVTV
to be overridden in both the FGL theorem and the resulting generalized theorem.
The difference between @(':override-vars') and @(':spec-override-vars') is that
the @(':override-vars') will not be overridden in the generalized theorem, but
the @(':spec-override-vars') still will.</li>

<li>@(':spec-override-var-bindings') is a list of @('let')-like bindings of
override value variables to expressions, which will be overridden in both the
FGL theorem and generalized theorem.</li>

<li>@(':output-vars') is a list of output variables of the SVTV that are used in the conclusion.</li>

<li>@(':output-parts') is a list of 4vec expressions -- part selects, zero
extends, shifts, concatenations -- of the output variables.  The given parts of
the outputs will be proved to be integerp in order to use a monotonicity
argument.  Variables that are not mentioned in output-parts will be proved
integerp as a whole.</li>

<li>@(':hyp') is a term (default T), which may reference variables
listed in input-vars and override-vars as well as variables used in the
expressions of input-bindings</li>

<li>@(':concl') is a term which may reference the same variables available to
@(':hyp') as well as the output-vars.</li>

<li>@(':enable') is a list of rules to be included in the theory for the final
generalized theorm, mainly useful when specifying @(':output-parts').</li>

<li>@(':no-lemmas') says to skip the initial override theorem and monotonicity
lemma and tries to prove the final (generalized) theorem directly, with the
hints given by the user.</li>

<li>@(':lemma-defthm') defaults to @('fgl::def-fgl-thm') but can be set
to (e.g.) @('defthm') or @('fgl::def-fgl-param-thm') to change how the initial
lemma is proved.</li>

<li>@(':lemma-args') gives additional arguments to be passed to the form
proving the initial lemma, which could be hints for a @('defthm') form or FGL
keyword args for @('fgl::def-fgl-thm') or @('fgl::def-fgl-param-thm').</li>

<li>@(':lemma-use-ideal') phrases the lemma in terms of a run of the ideal
svtv-spec, rather than the SVTV.</li>

<li>@(':no-integerp') says to skip proving @('integerp') of each output in the
initial override theorem.  The @(':enable') option typically must be used to
provide additional rules for the final theorem to show that the lemma implies
the outputs are integers.</li>

<li>@(':hints') are hints for the final theorem, used by themselves if @(':no-lemmas')
is set and in addition to the automatically provided hints if not.</li>

<li>@(':final-defthm') defaults to @('defthm') but can be set to a different
macro to change how the final generalized theorem is proved</li>

<li>@(':final-defthm-args') gives additional arguments to the form proving the
final generalized theorem.</li>

<li>@(':rule-classes') gives the rule classes of the theorem proved.</li>

<li>@(':unsigned-byte-hyps') says to automatically add @('unsigned-byte-p')
hypotheses for each input and override variable.</li>
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
 (def-svtv-idealized-thm partial-prods-to-product
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
Finally, the svtv-spec-run allows an additional setting of input and initial
state variables not set by the SVTV itself; these are given respectively by
@('base-ins') and @('initst') in the theorem.  Base-ins, however, must be
assumed not to set any additional override test variables.</p>

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
                   (svarlist-override-p (svex-envlist-all-keys base-ins) nil))
             ;; Conclusion given by the user
             (equal product (sum-partial-products partial-products)))))
 })
")
