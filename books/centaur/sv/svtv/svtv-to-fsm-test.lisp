; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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

(include-book "svtv-to-fsm")
(include-book "svtv-generalize")
(include-book "centaur/fgl/top" :dir :system)
(include-book "svtv-stobj-defsvtv")
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "centaur/sv/vl/top" :dir :system)
(include-book "oslib/ls" :dir :system)
(include-book "svtv-stobj-debug")
; cert_param: (uses-glucose)

(defconsts (*vl-design* state)
  (b* (((mv (vl::vl-loadresult loadres) state)
        (vl::vl-load (vl::make-vl-loadconfig :start-files '("svtv_to_fsm_test_counter.sv")))))
    (mv loadres.design state)))

(defconsts (*sv-design* *vl-good* *vl-bad*)
  (b* (((mv errmsg svex good bad)
        (vl::vl-design->sv-design "counter" *vl-design* (vl::make-vl-simpconfig))))
    (and errmsg
         (raise "~@0~%" errmsg))
    (mv svex good bad)))


(defsvtv$ counter-invar-run
  :design *sv-design*
  :cycle-phases (list (make-svtv-cyclephase :constants '(("clk" . 1)))
                      (make-svtv-cyclephase :constants '(("clk" . 0))
                                            :inputs-free t
                                            :outputs-captured t))
  :stages ((:label curr
            :inputs (("inc" inc)
                     ("reset" 0))
            :overrides (("sum" sum :cond sum-ovr :output sum-prev)
                        ("sum1" sum1 :cond sum1-ovr)))
           (:label next
            :outputs (("sum" sum-out)
                      ("sum1" sum1-out)))))

(def-svtv-data-export counter-invar-run-data)

(def-svtv-refinement counter-invar-run counter-invar-run-data
  :svtv-spec counter-invar-spec :inclusive-overridekeys t
  :fsm-name counter-fsm :define-fsm t)

(value-triple (acl2::tshell-ensure))

(def-svtv-generalized-thm counter-invar-svtv-thm
  :svtv counter-invar-run
  :svtv-spec counter-invar-spec
  :input-vars :all
  :output-vars (sum-out sum1-out)
  :unsigned-byte-hyps t
  :override-vars (sum)
  :spec-override-vars (sum1)
  :hyp (and (<= sum 11)
            (<= sum1 10))
  :concl (and (<= sum-out 11)
              (<= sum1-out 10)))


(def-svtv-to-fsm-thm counter-invar-fsm-thm
  :svtv-spec-thmname counter-invar-svtv-thm
  :svtv counter-invar-run
  :svtv-spec counter-invar-spec
  :fsm counter-fsm
  :input-vars :all
  :output-vars (sum-out sum1-out)
  :unsigned-byte-hyps t
  :override-vars (sum)
  :spec-override-vars (sum1)
  :hyp (and (<= sum 11)
            (<= sum1 10))
  :concl (and (<= sum-out 11)
              (<= sum1-out 10)))





;; (defthm counter-invar-fsm-thm
;;   (b* (((svtv-spec svtv) (counter-invar-spec))
;;        (fsm (svtv-spec->cycle-fsm svtv))
;;        (outs (base-fsm-eval envs initst fsm))
;;        ((sv::svassocs inc sum1)
;;         (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings svtv) envs outs))
;;        ((sv::svassocs (sum 'sum-prev) sum-out (?sum1-out 'sum1-out))
;;         (svtv-spec-cycle-outs->pipe-out svtv outs)))
;;     (implies (and (lhprobe-constraintlist-overridemux-eval
;;                    (svtv-spec-fsm-constraints (counter-invar-spec)) envs outs)
;;                   (svex-envlists-ovtestequiv envs
;;                                              '((((:VAR "sum1" . 32) . 15))
;;                                                NIL))
;;                   (unsigned-byte-p 1 inc)
;;                   (unsigned-byte-p 4 sum1)
;;                   (unsigned-byte-p 4 sum)
;;                   (<= sum 11)
;;                   (<= sum1 10)
;;                   (equal (len envs) 2))
;;              (and (<= sum-out 11)
;;                   (<= sum1-out 10)
;;                   )))
;;   :hints (("goal" :use ((:instance fsm-eval-when-overridekeys-envlists-agree*
;;                          (x (svtv-spec->cycle-fsm (counter-invar-spec)))
;;                          (impl-envs
;;                           (b* ((x (counter-invar-spec))
;;                                (fsm (svtv-spec->cycle-fsm x))
;;                                (outs (base-fsm-eval envs initst fsm))
;;                                (svtv-env (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings x) envs outs))
;;                                (fsm-envs (svtv-spec-pipe-env->cycle-envs x svtv-env))
;;                                (full-fsm-envs (svex-envlist-x-override
;;                                                fsm-envs
;;                                                (svex-envlist-remove-override
;;                                                 (svex-envlist-remove-override envs :test) :val))))
;;                             full-fsm-envs))
;;                          (spec-envs envs)
;;                          (initst initst)
;;                          (overridekeys (COUNTER-INVAR-RUN-OVERRIDEKEYS)))
;;                         (:instance counter-invar-svtv-thm
;;                          (env (b* ((x (counter-invar-spec))
;;                                    (fsm (svtv-spec->cycle-fsm x))
;;                                    (outs (base-fsm-eval envs initst fsm))
;;                                    (svtv-env (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings x) envs outs)))
;;                                 svtv-env))
;;                          (base-ins (svtv-cycle-run-fsm-inputs
;;                                     (svex-envlist-remove-override
;;                                      (svex-envlist-remove-override envs :test) :val)
;;                                     (svtv-spec->cycle-phases (counter-invar-spec))))))

;;            :in-theory (e/d (svtv-spec-run-in-terms-of-cycle-fsm
;;                             CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
;;                             svex-envlists-ovtests-ok-when-variable-free)
;;                            (fsm-eval-when-overridekeys-envlists-agree*
;;                             counter-invar-svtv-thm
;;                             LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL
;;                             unsigned-byte-p
;;                             acl2::fal-extract-of-cons))
;;                       ;; :in-theory '((:CONGRUENCE SET-EQUIV-IMPLIES-EQUAL-SVARLIST-NONOVERRIDE-P-1)
;;                       ;;   (:CONGRUENCE SVEX-ENVLISTS-EQUIVALENT-IMPLIES-EQUAL-SVTV-SPEC-CYCLE-OUTS->PIPE-OUT-2)
;;                       ;;   (:CONGRUENCE SVEX-ENVLISTS-OVTESTSIMILAR-IMPLIES-IFF-SVEX-ENVLISTS-OVTESTS-OK-1)
;;                       ;;   (:CONGRUENCE SVEX-ENVLISTS-OVTESTSIMILAR-IMPLIES-IFF-SVEX-ENVLISTS-OVTESTS-OK-2)
;;                       ;;   (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-BASE-FSM-EVAL-2)
;;                       ;;   (:DEFINITION DOUBLE-REWRITE)
;;                       ;;   (:DEFINITION NOT)
;;                       ;;   (:DEFINITION SYNP)
;;                       ;;   (:EQUIVALENCE SVEX-ENVLISTS-OVTESTEQUIV-IS-AN-EQUIVALENCE)
;;                       ;;   (:EQUIVALENCE SVEX-ENVLISTS-OVTESTSIMILAR-IS-AN-EQUIVALENCE)
;;                       ;;   (:EXECUTABLE-COUNTERPART FAL-EXTRACT)
;;                       ;;   (:EXECUTABLE-COUNTERPART FORCE-EXECUTE)
;;                       ;;   (:EXECUTABLE-COUNTERPART LHPROBE-MAP-EVAL)
;;                       ;;   (:EXECUTABLE-COUNTERPART LHPROBE-MAP-VARS)
;;                       ;;   (:EXECUTABLE-COUNTERPART MAKE-FAST-ALIST)
;;                       ;;   (:EXECUTABLE-COUNTERPART MAKE-FAST-ALISTS)
;;                       ;;   (:EXECUTABLE-COUNTERPART NOT)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVAR-OVERRIDETYPE-EQUIV$INLINE)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVARLIST-FIX$INLINE)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVARLIST-NONOVERRIDE-P)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVARLIST-OVERRIDE-P)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-EVAL)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-NONCALL-P)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-VARS)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVEX-ENVLIST-1MASK)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLELIST-ENVS-MATCH)
;;                       ;;   (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLEMAPLIST-RELEVANT-VARS)
;;                       ;;   (:META FORCE-EXECUTE-FORCE-EXECUTE)
;;                       ;;   (:META SVTV-OVERRIDE-SUBST-MATCHES-ENV-META)
;;                       ;;   (:META SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-CHECKS-WHEN-VARIABLE-FREE)
;;                       ;;   (:REWRITE ALISTLIST-EVAL-OF-TEST-ALISTS-UNDER-BINDINGS)
;;                       ;;   (:REWRITE BASE-FSM-OVCONGRUENT-OF-COUNTER-INVAR-SPEC-CYCLE)
;;                       ;;   (:REWRITE BASE-FSM-OVERRIDEKEY-TRANSPARENT-P-OF-COUNTER-INVAR-SPEC-CYCLE)
;;                       ;;   (:REWRITE ACL2::COMMUTATIVITY-OF-APPEND-UNDER-SET-EQUIV)
;;                       ;;   (:REWRITE CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES)
;;                       ;;   (:REWRITE COUNTER-INVAR-SPEC-FACTS)
;;                       ;;   (:REWRITE CYCLE-OUTPUTS-CAPTURED-OF-COUNTER-INVAR-SPEC)
;;                       ;;   (:REWRITE FAL-EXTRACT-CONST-OF-SVTV-SPEC-FSM-BINDINGS)
;;                       ;;   (:REWRITE LHPROBE-MAP-OVERRIDEMUX-EVAL-WHEN-ONLY-TEST-VARS)
;;                       ;;   (:REWRITE NEXTSTATE-KEYS-NON-OVERRIDE-OF-COUNTER-INVAR-SPEC)
;;                       ;;   (:REWRITE NEXTSTATE-KEYS-OF-SVTV-SPEC->CYCLE-FSM)
;;                       ;;   (:REWRITE AIGNET::SIMPCODE-P-WHEN-UNSIGNED-BYTE-P)
;;                       ;;   (:REWRITE SVARLIST-NONOVERRIDE-P-OF-APPEND)
;;                       ;;   (:REWRITE SVARLIST-NONOVERRIDE-P-OF-SVARLIST-REMOVE-OVERRIDE)
;;                       ;;   (:REWRITE SVARLIST-NONOVERRIDE-TEST-OF-counter-invar-spec-CYCLEPHASELIST-KEYS)
;;                       ;;   (:REWRITE SVEX-ALIST-ALL-XES-OF-COUNTER-INVAR-SPEC-INITST)
;;                       ;;   (:REWRITE SVEX-ENV-REDUCE-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL)
;;                       ;;   (:REWRITE SVEX-ENV-X-OVERRIDE-WHEN-SVEX-ALIST-ALL-XES-P)
;;                       ;;   (:REWRITE SVEX-ENVLIST-ALL-KEYS-OF-REMOVE-OVERRIDE)
;;                       ;;   (:REWRITE SVEX-ENVLIST-ALL-KEYS-OF-SVTV-CYCLE-RUN-FSM-INPUTS)
;;                       ;;   (:REWRITE SVEX-ENVLISTS-OVTESTS-OK-WHEN-VARIABLE-FREE)
;;                       ;;   (:REWRITE SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-RELEVANT-VARS)
;;                       ;;   (:REWRITE SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-SIMPLIFY)
;;                       ;;   (:REWRITE SVTV-SPEC-FSM-SYNTAX-CHECK-OF-COUNTER-INVAR-SPEC)
;;                       ;;   (:REWRITE SVTV-SPEC-PIPE-ENV->CYCLE-ENVS-UNDER-SVEX-ENVLISTS-OVTESTSIMILAR)
;;                       ;;   (:REWRITE SVTV-SPEC-RUN-IN-TERMS-OF-CYCLE-FSM)
;;                       ;;   (:REWRITE AIGNET::UNSIGNED-BYTE-P-WHEN-SIMPCODE-P)
;;                       ;;   (:REWRITE-QUOTED-CONSTANT SVEX-ENVLIST-1MASK-UNDER-SVEX-ENVLISTS-1MASK-EQUIV)
;;                       ;;   (:TYPE-PRESCRIPTION LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL)
;;                       ;;   (:TYPE-PRESCRIPTION OVERRIDEKEYS-ENVLISTS-AGREE*)
;;                       ;;   (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
;;            :do-not-induct t))
;;   :otf-flg t)







;; (define counter-invar-fsm-bindings ()
;;   :returns (bindings lhprobe-map-p)
;;   (svtv-spec-fsm-bindings (counter-invar-spec)))

;; (define counter-invar-fsm-outmap ()
;;   :returns (map lhprobe-map-p)
;;   (b* (((svtv-spec x) (counter-invar-spec))
;;        ((acl2::with-fast x.namemap)))
;;     (svtv-probealist-to-lhprobe-map x.probes x.namemap)))




;; (defthm outvars-len-of-counter-invar-spec
;;   (equal (len (svtv-probealist-outvars (svtv-spec->probes (counter-invar-spec)))) 2)
;;   :hints(("Goal" :in-theory (enable (counter-invar-spec)))))
  

;; (defthm svtv-spec-cycle-outs->pipe-out-of-counter-invar-spec
;;   (implies (and (hons-get (svar-fix var) (counter-invar-fsm-outmap))
;;                 (<= 2 (len outs)))
;;            (equal (svex-env-lookup var (svtv-spec-cycle-outs->pipe-out (counter-invar-spec) outs))
;;                   (lhprobe-eval (cdr (hons-assoc-equal (svar-fix var) (counter-invar-fsm-outmap))) outs)))
;;   :hints(("Goal" :in-theory (e/d (counter-invar-fsm-outmap
;;                                   lookup-in-svtv-spec-cycle-outs->pipe-out)
;;                                  ((counter-invar-fsm-outmap))))))


;; (local (in-theory (disable nth take
;;                            acl2::take-of-cons
;;                            acl2::take-of-1)))



;; (defthm counter-invar-fsm-thm-gen11-direct
;;   (b* (((svtv-spec svtv) (counter-invar-spec))
;;        (fsm (svtv-spec->cycle-fsm svtv))
;;        (outs (base-fsm-eval envs initst fsm))
;;        (inc (lhs-eval-zero '("inc") (nth 0 envs)))
;;        (sum1 (lhs-eval-zero '((4 :VAR "sum1" . 16)) (nth 0 envs)))
       
;;        ;; ((sv::svassocs inc sum1)
;;        ;;  (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings svtv) envs outs))
;;        (sum (lhs-eval-zero '((4 . "sum")) (nth 0 outs)))
;;        (sum-out (lhs-eval-zero '((4 . "sum")) (nth 1 outs)))
;;        (sum1-out (lhs-eval-zero '((4 . "sum1")) (nth 1 outs))))
;;     (implies (and (lhprobe-constraintlist-overridemux-eval
;;                    (svtv-spec-fsm-constraints (counter-invar-spec))
;;                    envs outs)
;;                   (svex-envlists-ovtestsimilar envs
;;                                              ;; '((((:VAR "sum1" . 32) . 15))
;;                                              ;;   NIL)
;;                                              '((((:VAR "sum1" . 32) . 15)
;;                                                 ;; ((:VAR "sum" . 32) 15 . 0)
;;                                                 )
;;                                                NIL))
;;                   (unsigned-byte-p 1 inc)
;;                   (unsigned-byte-p 4 sum1)
;;                   (unsigned-byte-p 4 sum)
;;                   (<= sum 11)
;;                   (<= sum1 10)
;;                   (equal (len envs) 2))
;;              (and (<= sum-out 11)
;;                   (<= sum1-out 10)
;;                   )))
;;   :hints (("goal" :use ((:instance fsm-eval-when-overridekeys-envlists-agree*
;;                          (x (svtv-spec->cycle-fsm (counter-invar-spec)))
;;                          (impl-envs
;;                           (b* ((x (counter-invar-spec))
;;                                (fsm (svtv-spec->cycle-fsm x))
;;                                (outs (base-fsm-eval envs initst fsm))
;;                                (svtv-env (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings x) envs outs))
;;                                (fsm-envs (svtv-spec-pipe-env->cycle-envs x svtv-env))
;;                                (full-fsm-envs (svex-envlist-x-override
;;                                                fsm-envs
;;                                                (svex-envlist-remove-override
;;                                                 (svex-envlist-remove-override envs :test) :val))))
;;                             full-fsm-envs))
;;                          (spec-envs envs)
;;                          (initst initst)
;;                          (overridekeys (COUNTER-INVAR-RUN-OVERRIDEKEYS)))
;;                         (:instance counter-invar-svtv-thm
;;                          (env (b* ((x (counter-invar-spec))
;;                                    (fsm (svtv-spec->cycle-fsm x))
;;                                    (outs (base-fsm-eval envs initst fsm))
;;                                    (svtv-env (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings x) envs outs)))
;;                                 svtv-env))
;;                          (base-ins (svtv-cycle-run-fsm-inputs
;;                                     (svex-envlist-remove-override
;;                                      (svex-envlist-remove-override envs :test) :val)
;;                                     (svtv-spec->cycle-phases (counter-invar-spec))))))
;;            :in-theory 
;;            '(;; LHS-EVAL-ZERO-SVEX-ENV-EQUIV-CONGRUENCE-ON-ENV
;;              ;;                            SVEX-ENVLISTS-SIMILAR-IMPLIES-EQUAL-BASE-FSM-EVAL-1
;;              ;; SVEX-ENVLISTS-EQUIVALENT-REFINES-SVEX-ENVLISTS-SIMILAR
;;              (:congruence SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-LHS-EVAL-ZERO-2)
;;              (:congruence 4VEC-1MASK-EQUIV-IMPLIES-EQUAL-4VEC-BIT?!-1)
;;              (:COMPOUND-RECOGNIZER ACL2::NATP-COMPOUND-RECOGNIZER)
;;              (:CONGRUENCE SET-EQUIV-IMPLIES-EQUAL-SVARLIST-NONOVERRIDE-P-1)
;;              (:CONGRUENCE
;;               SVEX-ENVLISTS-OVTESTSIMILAR-IMPLIES-IFF-SVEX-ENVLISTS-OVTESTS-OK-1)
;;              (:CONGRUENCE
;;               SVEX-ENVLISTS-OVTESTSIMILAR-IMPLIES-IFF-SVEX-ENVLISTS-OVTESTS-OK-2)
;;              (:CONGRUENCE SVEX-ENVLISTS-SIMILAR-IMPLIES-SVEX-ENVS-SIMILAR-NTH-2)
;;              (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-BASE-FSM-EVAL-2)
;;              (:DEFINITION DOUBLE-REWRITE)
;;              (:DEFINITION HONS-GET)
;;              (:DEFINITION LHPROBE-EVAL)
;;              (:DEFINITION MAX)
;;              (:DEFINITION NOT)
;;              (:DEFINITION SYNP)
;;              (:EQUIVALENCE SVEX-ENVLISTS-OVTESTEQUIV-IS-AN-EQUIVALENCE)
;;              (:EQUIVALENCE SVEX-ENVLISTS-OVTESTSIMILAR-IS-AN-EQUIVALENCE)
;;              (:EQUIVALENCE SVEX-ENVS-1MASK-EQUIV-IS-AN-EQUIVALENCE)
;;              (:EXECUTABLE-COUNTERPART 2VEC->VAL$INLINE)
;;              (:EXECUTABLE-COUNTERPART 2VEC-P$INLINE)
;;              (:EXECUTABLE-COUNTERPART CDR)
;;              (:EXECUTABLE-COUNTERPART COUNTER-INVAR-run-fsm-output-map)
;;              (:EXECUTABLE-COUNTERPART EQUAL)
;;              (:EXECUTABLE-COUNTERPART FAL-EXTRACT)
;;              (:EXECUTABLE-COUNTERPART FORCE-EXECUTE)
;;              (:EXECUTABLE-COUNTERPART HONS-ASSOC-EQUAL)
;;              (:EXECUTABLE-COUNTERPART LHPROBE->LHS$INLINE)
;;              (:EXECUTABLE-COUNTERPART LHPROBE->SIGNEDP$INLINE)
;;              (:EXECUTABLE-COUNTERPART LHPROBE->STAGE$INLINE)
;;              (:EXECUTABLE-COUNTERPART LHPROBE-CHANGE-OVERRIDE)
;;              (:EXECUTABLE-COUNTERPART LHPROBE-MAP-EVAL)
;;              (:EXECUTABLE-COUNTERPART LHPROBE-MAP-VARS)
;;              (:EXECUTABLE-COUNTERPART LHPROBE-VARS)
;;              (:EXECUTABLE-COUNTERPART LHS-EVAL-ZERO)
;;              (:EXECUTABLE-COUNTERPART LHS-VARS)
;;              (:EXECUTABLE-COUNTERPART LHS-WIDTH)
;;              (:EXECUTABLE-COUNTERPART ACL2::LOGHEAD$INLINE)
;;              (:EXECUTABLE-COUNTERPART ACL2::LOGMASK$INLINE)
;;              (:EXECUTABLE-COUNTERPART MAKE-FAST-ALIST)
;;              (:EXECUTABLE-COUNTERPART MAKE-FAST-ALISTS)
;;              (:EXECUTABLE-COUNTERPART NTH)
;;              (:EXECUTABLE-COUNTERPART SVAR-FIX$INLINE)
;;              (:EXECUTABLE-COUNTERPART SVAR-OVERRIDETYPE-EQUIV$INLINE)
;;              (:EXECUTABLE-COUNTERPART SVARLIST-FIX$INLINE)
;;              (:EXECUTABLE-COUNTERPART SVARLIST-NONOVERRIDE-P)
;;              (:EXECUTABLE-COUNTERPART SVARLIST-OVERRIDE-P)
;;              (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-EVAL)
;;              (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-NONCALL-P)
;;              (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-VARS)
;;              (:EXECUTABLE-COUNTERPART SVEX-ENVLIST-1MASK)
;;              (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLELIST-ENVS-MATCH)
;;              (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLEMAPLIST-RELEVANT-VARS)
;;              (:EXECUTABLE-COUNTERPART SVTV-SPEC-FSM-BINDINGS)
;;              (:executable-counterpart svtv-override-triplemaplist-test-only-p)
;;              (:META FORCE-EXECUTE-FORCE-EXECUTE)
;;              (:META SVTV-OVERRIDE-SUBST-MATCHES-ENV-META)
;;              (:META
;;               SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-CHECKS-WHEN-VARIABLE-FREE)
;;              (:REWRITE 4VEC-BIT?!-MASK-OF-LHS-EVAL-ZERO)
;;              (:REWRITE ALISTLIST-EVAL-OF-TEST-ALISTS-UNDER-BINDINGS)
;;              (:REWRITE BASE-FSM-OVCONGRUENT-OF-COUNTER-INVAR-SPEC-CYCLE)
;;              (:REWRITE
;;               BASE-FSM-OVERRIDEKEY-TRANSPARENT-P-OF-COUNTER-INVAR-SPEC-CYCLE)
;;              (:REWRITE ACL2::COMMUTATIVITY-OF-APPEND-UNDER-SET-EQUIV)
;;              (:REWRITE CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES)
;;              (:REWRITE COUNTER-INVAR-SPEC-FACTS)
;;              (:REWRITE CYCLE-OUTPUTS-CAPTURED-OF-COUNTER-INVAR-SPEC)
;;              (:REWRITE FAL-EXTRACT-CONST-OF-SVTV-SPEC-FSM-BINDINGS)
;;              (:REWRITE HONS-ASSOC-EQUAL-OF-SVTV-SPEC-FSM-BINDINGS)
;;              (:REWRITE LEN-OF-BASE-FSM-EVAL)
;;              (:REWRITE LEN-OF-SVEX-ENVLIST-X-OVERRIDE)
;;              (:REWRITE LEN-OF-SVTV-SPEC-PIPE-ENV->CYCLE-ENVS)
;;              (:REWRITE LHPROBE-MAP-FIX-WHEN-LHPROBE-MAP-P)
;;              (:REWRITE lhprobe-map-overridemux-eval-when-only-test-vars-under-svex-env-1mask-equiv)
;;              (:REWRITE LHPROBE-MAP-P-OF-SVTV-SPEC-FSM-BINDINGS)
;;              (:REWRITE LHPROBE-OVERRIDEMUX-EVAL-SPLIT-ON-VAR-OVERRIDETYPE)
;;              (:REWRITE LHS-EVAL-ZERO-NTH-UNDER-OVTESTEQUIV)
;;              (:REWRITE LHS-EVAL-ZERO-NTH-UNDER-OVTESTsimilar)
;;              (:REWRITE LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL)
;;              (:REWRITE NEXTSTATE-KEYS-NON-OVERRIDE-OF-COUNTER-INVAR-SPEC)
;;              (:REWRITE NEXTSTATE-KEYS-OF-SVTV-SPEC->CYCLE-FSM)
;;              (:REWRITE OUTVARS-LEN-OF-COUNTER-INVAR-SPEC)
;;              (:REWRITE SVARLIST-NONOVERRIDE-P-OF-APPEND)
;;              (:REWRITE SVARLIST-NONOVERRIDE-P-OF-SVARLIST-REMOVE-OVERRIDE)
;;              (:REWRITE
;;               SVARLIST-NONOVERRIDE-TEST-OF-COUNTER-INVAR-SPEC-CYCLEPHASELIST-KEYS)
;;              (:REWRITE SVEX-ALIST-ALL-XES-OF-COUNTER-INVAR-SPEC-INITST)
;;              (:REWRITE SVEX-ENV-REDUCE-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL)
;;              (:REWRITE SVEX-ENV-X-OVERRIDE-WHEN-SVEX-ALIST-ALL-XES-P)
;;              (:REWRITE SVEX-ENVLIST-ALL-KEYS-OF-REMOVE-OVERRIDE)
;;              (:REWRITE SVEX-ENVLIST-ALL-KEYS-OF-SVTV-CYCLE-RUN-FSM-INPUTS)
;;              (:REWRITE SVEX-ENVLISTS-OVTESTS-OK-WHEN-VARIABLE-FREE)
;;              (:REWRITE SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-RELEVANT-VARS-TEST-ONLY)
;;              (:REWRITE SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-SIMPLIFY)
;;              (:REWRITE SVTV-SPEC-CYCLE-OUTS->PIPE-OUT-OF-COUNTER-INVAR-SPEC)
;;              (:REWRITE SVTV-SPEC-FSM-SYNTAX-CHECK-OF-COUNTER-INVAR-SPEC)
;;              (:REWRITE
;;               SVTV-SPEC-PIPE-ENV->CYCLE-ENVS-UNDER-SVEX-ENVLISTS-OVTESTSIMILAR)
;;              (:REWRITE SVTV-SPEC-RUN-IN-TERMS-OF-CYCLE-FSM)
;;              ;; (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)
;;              (:REWRITE-QUOTED-CONSTANT
;;               SVEX-ENVLIST-1MASK-UNDER-SVEX-ENVLISTS-1MASK-EQUIV)
;;              (:TYPE-PRESCRIPTION LEN)
;;              (:TYPE-PRESCRIPTION LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL)
;;              (:TYPE-PRESCRIPTION OVERRIDEKEYS-ENVLISTS-AGREE*)
;;              (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
;;            :do-not-induct t)))



;; (defthm counter-invar-fsm-thm-gen11
;;   (b* (((svtv-spec svtv) (counter-invar-spec))
;;        (fsm (svtv-spec->cycle-fsm svtv))
;;        (outs (base-fsm-eval envs initst fsm))
;;        (inc (lhs-eval-zero '("inc") (nth 0 envs)))
;;        (sum1 (lhs-eval-zero '((4 :VAR "sum1" . 16)) (nth 0 envs)))
       
;;        ;; ((sv::svassocs inc sum1)
;;        ;;  (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings svtv) envs outs))
;;        (sum (lhs-eval-zero '((4 . "sum")) (nth 0 outs)))
;;        (sum-out (lhs-eval-zero '((4 . "sum")) (nth 1 outs)))
;;        (sum1-out (lhs-eval-zero '((4 . "sum1")) (nth 1 outs))))
;;     (implies (and (lhprobe-constraintlist-overridemux-eval
;;                    (svtv-spec-fsm-constraints (counter-invar-spec))
;;                    envs outs)
;;                   (svex-envlists-ovtestequiv envs
;;                                              '((((:VAR "sum1" . 32) . 15))
;;                                                NIL))
;;                   (unsigned-byte-p 1 inc)
;;                   (unsigned-byte-p 4 sum1)
;;                   (unsigned-byte-p 4 sum)
;;                   (<= sum 11)
;;                   (<= sum1 10)
;;                   (equal (len envs) 2))
;;              (and (<= sum-out 11)
;;                   (<= sum1-out 10)
;;                   )))
;;   :hints (("goal" :use ((:instance counter-invar-fsm-thm))
           
;;            :in-theory (e/d (svtv-spec-run-in-terms-of-cycle-fsm
;;                             CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
;;                             svex-envlists-ovtests-ok-when-variable-free
;;                             lhprobe-eval
;;                             base-fsm-eval-of-base-fsm-final-state
;;                             hons-assoc-equal-of-svtv-spec-fsm-bindings)
;;                            (fsm-eval-when-overridekeys-envlists-agree*
;;                             ;; LHPROBE-OVERRIDEMUX-EVAL-SPLIT-ON-VAR-OVERRIDETYPE
;;                             nthcdr-of-base-fsm-eval-is-base-fsm-eval
;;                             counter-invar-fsm-thm
;;                             counter-invar-fsm-thm-gen1
;;                             ;; LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL
;;                             unsigned-byte-p
;;                             acl2::fal-extract-of-cons
;;                             take nth len nthcdr
;;                             acl2::nth-when-zp
;;                             acl2::nth-when-too-large-cheap
;;                             lhs-eval-zero-of-cons
;;                             acl2::take-of-len-free
;;                             acl2::take-of-too-many
;;                             acl2::take-when-atom
;;                             acl2::len-when-atom
;;                             acl2::nthcdr-when-atom
;;                             acl2::consp-of-nthcdr
;;                             consp-of-base-fsm-eval
;;                             acl2::natp-when-integerp
;;                             acl2::nthcdr-when-zp
;;                             (tau-system)))
;;            :do-not-induct t))
;;   :otf-flg t)



;; (defthm counter-invar-fsm-thm-gen1
;;   (b* (((svtv-spec svtv) (counter-invar-spec))
;;        (fsm (svtv-spec->cycle-fsm svtv))
;;        (outs (base-fsm-eval envs initst fsm))
;;        ((sv::svassocs inc sum1)
;;         (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings svtv)
;;                                       (nthcdr cycle0 envs)
;;                                       (nthcdr cycle0 outs)))
;;        ((sv::svassocs (sum 'sum-prev) sum-out (?sum1-out 'sum1-out))
;;         (svtv-spec-cycle-outs->pipe-out svtv (nthcdr cycle0 outs))))
;;     (implies (and (lhprobe-constraintlist-overridemux-eval
;;                    (svtv-spec-fsm-constraints (counter-invar-spec))
;;                    (nthcdr cycle0 envs)
;;                    (nthcdr cycle0 outs))
;;                   (svex-envlists-ovtestequiv (take 2 (nthcdr cycle0 envs))
;;                                              '((((:VAR "sum1" . 32) . 15))
;;                                                NIL))
;;                   (unsigned-byte-p 1 inc)
;;                   (unsigned-byte-p 4 sum1)
;;                   (unsigned-byte-p 4 sum)
;;                   (<= sum 11)
;;                   (<= sum1 10)
;;                   (natp cycle0)
;;                   (<= (+ cycle0 2) (len envs)))
;;              (and (<= sum-out 11)
;;                   (<= sum1-out 10)
;;                   )))
;;   :hints (("goal" :use ((:instance counter-invar-fsm-thm
;;                          (envs (take 2 (nthcdr cycle0 envs)))
;;                          (initst (b* ((x (counter-invar-spec))
;;                                       (fsm (svtv-spec->cycle-fsm x)))
;;                                    (base-fsm-final-state (take cycle0 envs) initst (base-fsm->nextstate fsm))))))
           
;;            :in-theory (e/d (svtv-spec-run-in-terms-of-cycle-fsm
;;                             CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
;;                             svex-envlists-ovtests-ok-when-variable-free)
;;                            (fsm-eval-when-overridekeys-envlists-agree*
;;                             counter-invar-svtv-thm
;;                             LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL
;;                             unsigned-byte-p
;;                             acl2::fal-extract-of-cons
;;                             counter-invar-fsm-thm
;;                             base-fsm-eval-of-cons
;;                             take nth len nthcdr
;;                             acl2::take-of-len-free
;;                             acl2::take-of-too-many
;;                             acl2::take-when-atom
;;                             acl2::len-when-atom
;;                             acl2::nthcdr-when-atom
;;                             acl2::consp-of-nthcdr
;;                             consp-of-base-fsm-eval
;;                             acl2::natp-when-integerp
;;                             acl2::nthcdr-when-zp
;;                             (tau-system)
;;                             ))
;;            :do-not-induct t)))











;; (defthm counter-invar-fsm-thm-gen
;;   (b* (((svtv-spec svtv) (counter-invar-spec))
;;        (fsm (svtv-spec->cycle-fsm svtv))
;;        (outs (base-fsm-eval envs initst fsm))
;;        (inc (lhs-eval-zero '("inc") (nth cycle0 envs)))
;;        (sum1 (lhs-eval-zero '((4 :VAR "sum1" . 16)) (nth cycle0 envs)))
       
;;        ;; ((sv::svassocs inc sum1)
;;        ;;  (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings svtv) envs outs))
;;        (sum (lhs-eval-zero '((4 . "sum")) (nth cycle0 outs)))
;;        (sum-out (lhs-eval-zero '((4 . "sum")) (nth cycle1 outs)))
;;        (sum1-out (lhs-eval-zero '((4 . "sum1")) (nth cycle1 outs))))
;;     (implies (and (lhprobe-constraintlist-overridemux-eval
;;                    (svtv-spec-fsm-constraints (counter-invar-spec))
;;                    (nthcdr cycle0 envs)
;;                    (nthcdr cycle0 outs))
;;                   (svex-envlists-ovtestsimilar (take 2 (nthcdr cycle0 envs))
;;                                              '((((:VAR "sum1" . 32) . 15))
;;                                                NIL))
;;                   (unsigned-byte-p 1 inc)
;;                   (unsigned-byte-p 4 sum1)
;;                   (unsigned-byte-p 4 sum)
;;                   (<= sum 11)
;;                   (<= sum1 10)
;;                   (natp cycle0)
;;                   (natp cycle1)
;;                   (equal cycle1 (+ 1 cycle0))
;;                   (< cycle1 (len envs)))
;;              (and (<= sum-out 11)
;;                   (<= sum1-out 10)
;;                   )))
;;   :hints (("goal" :use ((:instance counter-invar-fsm-thm-gen11-direct
;;                          (envs (take 2 (nthcdr cycle0 envs)))
;;                          (initst (b* ((x (counter-invar-spec))
;;                                       (fsm (svtv-spec->cycle-fsm x)))
;;                                    (base-fsm-final-state (take cycle0 envs) initst (base-fsm->nextstate fsm))))))
           
           
;;            ;; :in-theory (e/d (svtv-spec-run-in-terms-of-cycle-fsm
;;            ;;                  CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
;;            ;;                  svex-envlists-ovtests-ok-when-variable-free
;;            ;;                  base-fsm-eval-of-base-fsm-final-state
;;            ;;                  nthcdr-of-take)
;;            ;;                 (fsm-eval-when-overridekeys-envlists-agree*
;;            ;;                  counter-invar-svtv-thm
;;            ;;                  nthcdr-of-base-fsm-eval-is-base-fsm-eval
;;            ;;                  LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL
;;            ;;                  unsigned-byte-p
;;            ;;                  acl2::fal-extract-of-cons
;;            ;;                  base-fsm-eval-of-cons
;;            ;;                  lhs-eval-zero-of-cons
;;            ;;                  take nth len nthcdr
;;            ;;                  acl2::take-of-len-free
;;            ;;                  acl2::take-of-too-many
;;            ;;                  acl2::take-when-atom
;;            ;;                  acl2::len-when-atom
;;            ;;                  consp-of-base-fsm-eval
;;            ;;                  acl2::natp-when-integerp
;;            ;;                  (tau-system)
;;            ;;                  ))
;;            :in-theory '((:COMPOUND-RECOGNIZER ACL2::NATP-COMPOUND-RECOGNIZER)
;;                         (:CONGRUENCE ACL2::NAT-EQUIV-IMPLIES-EQUAL-NTH-1)
;;                         (:CONGRUENCE ACL2::NAT-EQUIV-IMPLIES-EQUAL-NTHCDR-1)
;;                         (:DEFINITION NOT)
;;                         (:EXECUTABLE-COUNTERPART <)
;;                         (:EXECUTABLE-COUNTERPART BINARY-+)
;;                         (:EXECUTABLE-COUNTERPART EQUAL)
;;                         (:EXECUTABLE-COUNTERPART NFIX)
;;                         (:LINEAR
;;                          LHPROBE-CONSTRAINTLIST-MAX-STAGE-OF-SVTV-SPEC-FSM-CONSTRAINTS)
;;                         (:REWRITE APPEND-TAKE-TAKE-NTHCDR)
;;                         (:REWRITE BASE-FSM-EVAL-OF-BASE-FSM-FINAL-STATE)
;;                         (:REWRITE BASE-FSM-EVAL-OF-TAKE)
;;                         (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
;;                         (:REWRITE COMMUTATIVITY-OF-+)
;;                         (:REWRITE CYCLE-FSM-OF-COUNTER-INVAR-SPEC)
;;                         (:REWRITE FIX-OF-NUMBER)
;;                         (:REWRITE INVERSE-OF-+)
;;                         (:REWRITE ACL2::LEN-OF-TAKE)
;;                         (:REWRITE LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL-OF-TAKE-ENVS)
;;                         (:REWRITE LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL-OF-TAKE-OUTS)
;;                         (:REWRITE ACL2::NFIX-UNDER-NAT-EQUIV)
;;                         (:REWRITE ACL2::NFIX-WHEN-NATP)
;;                         (:REWRITE ACL2::NTH-OF-NTHCDR)
;;                         (:REWRITE ACL2::NTH-OF-TAKE)
;;                         (:REWRITE NTHCDR-OF-TAKE)
;;                         (:REWRITE OUTVARS-LEN-OF-COUNTER-INVAR-SPEC)
;;                         (:REWRITE UNICITY-OF-0)
;;                         (:TYPE-PRESCRIPTION INTEGERP-OF-LHPROBE-CONSTRAINTLIST-MAX-STAGE)
;;                         (:TYPE-PRESCRIPTION LEN)
;;                         (:TYPE-PRESCRIPTION LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL)
;;                         (:TYPE-PRESCRIPTION NFIX))
;;            :do-not-induct t))
;;   :otf-flg t)


;; (defthm counter-invar-fsm-thm-gen-1step
;;   (b* (((svtv-spec svtv) (counter-invar-spec))
;;        (fsm (svtv-spec->cycle-fsm svtv))
;;        (outs (base-fsm-eval envs initst fsm))
;;        (inc (lhs-eval-zero '("inc") (nth cycle0 envs)))
;;        (sum1 (lhs-eval-zero '((4 :VAR "sum1" . 16)) (nth cycle0 envs)))
       
;;        ;; ((sv::svassocs inc sum1)
;;        ;;  (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings svtv) envs outs))
;;        (sum (lhs-eval-zero '((4 . "sum")) (nth cycle0 outs)))
;;        (sum-out (lhs-eval-zero '((4 . "sum")) (nth cycle1 outs)))
;;        (sum1-out (lhs-eval-zero '((4 . "sum1")) (nth cycle1 outs))))
;;     (implies (and (equal (+ -1 cycle1) cycle0)
;;                   (lhprobe-constraintlist-overridemux-eval
;;                    (svtv-spec-fsm-constraints (counter-invar-spec))
;;                    (nthcdr cycle0 envs)
;;                    (nthcdr cycle0 outs))
;;                   (svex-envlists-ovtestequiv (take 2 (nthcdr cycle0 envs))
;;                                              '((((:VAR "sum1" . 32) . 15))
;;                                                NIL))
;;                   (unsigned-byte-p 1 inc)
;;                   (unsigned-byte-p 4 sum1)
;;                   (unsigned-byte-p 4 sum)
;;                   (<= sum 11)
;;                   (<= sum1 10)
;;                   (natp cycle0)
;;                   (natp cycle1)
;;                   (< cycle1 (len envs)))
;;              (and (<= sum-out 11)
;;                   (<= sum1-out 10)
;;                   )))
;;   :hints (("goal" :use ((:instance counter-invar-fsm-thm
;;                          (envs (take 2 (nthcdr cycle0 envs)))
;;                          (initst (b* ((x (counter-invar-spec))
;;                                       (fsm (svtv-spec->cycle-fsm x)))
;;                                    (base-fsm-final-state (take cycle0 envs) initst (base-fsm->nextstate fsm))))))
           
           
;;            :in-theory (e/d (svtv-spec-run-in-terms-of-cycle-fsm
;;                             CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
;;                             svex-envlists-ovtests-ok-when-variable-free
;;                             base-fsm-eval-of-base-fsm-final-state
;;                             lhprobe-eval
;;                             hons-assoc-equal-of-svtv-spec-fsm-bindings)
;;                            (fsm-eval-when-overridekeys-envlists-agree*
;;                             counter-invar-svtv-thm
;;                             nthcdr-of-base-fsm-eval-is-base-fsm-eval
;;                             ;; LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL
;;                             unsigned-byte-p
;;                             acl2::fal-extract-of-cons
;;                             counter-invar-fsm-thm
;;                             base-fsm-eval-of-cons
;;                             lhs-eval-zero-of-cons
;;                             take nth len nthcdr
;;                             acl2::take-of-len-free
;;                             acl2::take-of-too-many
;;                             acl2::take-when-atom
;;                             acl2::len-when-atom
;;                             acl2::nthcdr-when-atom
;;                             acl2::consp-of-nthcdr
;;                             consp-of-base-fsm-eval
;;                             acl2::natp-when-integerp
;;                             acl2::nthcdr-when-zp
;;                             (tau-system)
;;                             ))
;;            :do-not-induct t))
;;   :otf-flg t)



           
;;            :in-theory (e/d (svtv-spec-run-in-terms-of-cycle-fsm
;;                             CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
;;                             svex-envlists-ovtests-ok-when-variable-free
;;                             base-fsm-eval-of-base-fsm-final-state
;;                             lhprobe-eval
;;                             hons-assoc-equal-of-svtv-spec-fsm-bindings)
;;                            (fsm-eval-when-overridekeys-envlists-agree*
;;                             ;; LHPROBE-OVERRIDEMUX-EVAL-SPLIT-ON-VAR-OVERRIDETYPE
;;                             nthcdr-of-base-fsm-eval-is-base-fsm-eval
;;                             counter-invar-fsm-thm
;;                             counter-invar-fsm-thm-gen1
;;                             ;; LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL
;;                             unsigned-byte-p
;;                             acl2::fal-extract-of-cons
;;                             take nth len nthcdr
;;                             acl2::nth-when-zp
;;                             acl2::nth-when-too-large-cheap
;;                             lhs-eval-zero-of-cons
;;                             acl2::take-of-len-free
;;                             acl2::take-of-too-many
;;                             acl2::take-when-atom
;;                             acl2::len-when-atom
;;                             acl2::nthcdr-when-atom
;;                             acl2::consp-of-nthcdr
;;                             consp-of-base-fsm-eval
;;                             acl2::natp-when-integerp
;;                             acl2::nthcdr-when-zp
;;                             (tau-system)))
