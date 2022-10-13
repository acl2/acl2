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
(include-book "centaur/fgl/def-fgl-thm" :dir :system)
(local (include-book "svtv-idealize-proof"))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))


;; Just a few theorems from svtv-idealize-proof are needed for this event.  We'll import them redundantly here.
(std::defredundant :names (set-equiv-by-mergesort-equal
                           SET-EQUIV-IMPLIES-SVEX-ENVS-EQUIVALENT-SVEX-ENV-REDUCE-1
                           SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1
                           SVTV-DATA-OBJ->IDEAL-SPEC-RUN-REFINES-SVTV-SPEC-RUN))


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
                                          svtv-data-obj-p-of-<data>)))
       (svtv-data-obj->ideal-spec (<data>))
  
       ///
       (in-theory (disable (<ideal-name>)))

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

  

       (defret <ideal-name>-refines-<name>
         (b* (((svtv-spec spec))
              (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
              (impl-run (svtv-run (<name>) pipe-env)))
           (implies (and 
                     (svtv-override-triplemaplist-ok (<name>-triplemaplist) pipe-env spec-run)
                
                     (svex-env-<<= (svex-env-reduce (<name>-input-vars) pipe-env)
                                   spec-pipe-env))
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
                                     (:TYPE-PRESCRIPTION SVTV-OVERRIDE-TRIPLEMAPLIST-OK))
                 :do-not-induct t))))))


(defun def-svtv-ideal-fn (ideal-name svtv-name data-name)
  (declare (xargs :mode :program))
  (acl2::template-subst *svtv-idealize-template*
                        :str-alist `(("<NAME>" . ,(symbol-name svtv-name))
                                     ("<DATA>" . ,(symbol-name data-name))
                                     ("<IDEAL-NAME>" . ,(symbol-name ideal-name)))
                        :pkg-sym ideal-name))

(defmacro def-svtv-ideal (ideal-name svtv-name data-name)
  (def-svtv-ideal-fn ideal-name svtv-name data-name))





;;; Theory for svtv-idealized-theorem events.



(define svtv-override-triplelist-ok ((x svtv-override-triplelist-p)
                                     (pipe-env svex-env-p)
                                     (ref-env svex-env-p))
  :returns (ok)
  (if (atom x)
      t
    (and (svtv-override-triple-ok (car x) pipe-env ref-env)
         (svtv-override-triplelist-ok (cdr x) pipe-env ref-env)))
  ///
  (defthm svtv-override-triplelist-ok-of-cons
    (equal (svtv-override-triplelist-ok (cons x y) pipe-env ref-env)
           (and (svtv-override-triple-ok x pipe-env ref-env)
                (svtv-override-triplelist-ok y pipe-env ref-env))))
  (defthm svtv-override-triplelist-ok-of-append
    (equal (svtv-override-triplelist-ok (append x y) pipe-env ref-env)
           (and (svtv-override-triplelist-ok x pipe-env ref-env)
                (svtv-override-triplelist-ok y pipe-env ref-env))))

  (defthm svtv-override-triplelist-ok-of-nil
    (svtv-override-triplelist-ok nil pipe-env ref-env)))

(defprod svtv-override-constant
  ((test 4vec-p)
   (val 4vec-p)
   (refvar svar-p))
  :layout :list)

(deflist svtv-override-constantlist :elt-type svtv-override-constant :true-listp t)


(define svtv-override-constantlist-ok ((x svtv-override-constantlist-p)
                                     (ref-env svex-env-p))
  :returns (ok)
  (if (atom x)
      t
    (and (b* (((svtv-override-constant x1) (car x)))
           (4vec-override-values-ok-<<= x1.test x1.val (svex-env-lookup x1.refvar ref-env)))
         (svtv-override-constantlist-ok (cdr x) ref-env)))
  ///
  (defthm svtv-override-constantlist-ok-of-append
    (equal (svtv-override-constantlist-ok (append x y) ref-env)
           (and (svtv-override-constantlist-ok x ref-env)
                (svtv-override-constantlist-ok y ref-env))))

  (defthm svtv-override-constantlist-ok-of-nil
    (svtv-override-constantlist-ok nil ref-env)))

(define svtv-override-triplelist-ok ((x svtv-override-triplelist-p)
                                     (pipe-env svex-env-p)
                                     (ref-env svex-env-p))
  :returns (ok)
  (if (atom x)
      t
    (and (svtv-override-triple-ok (car x) pipe-env ref-env)
         (svtv-override-triplelist-ok (cdr x) pipe-env ref-env)))
  ///
  (defthm svtv-override-triplelist-ok-of-append
    (equal (svtv-override-triplelist-ok (append x y) pipe-env ref-env)
           (and (svtv-override-triplelist-ok x pipe-env ref-env)
                (svtv-override-triplelist-ok y pipe-env ref-env))))

  (defthm svtv-override-triplelist-ok-of-nil
    (svtv-override-triplelist-ok nil pipe-env ref-env)))




(define svtv-override-triplemap-split ((x svtv-override-triplemap-p)
                                                      (subst svex-alist-p))
  :returns (mv (consts svtv-override-constantlist-p)
               (triples svtv-override-triplelist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-override-triplemap-split (cdr x) subst))
       ((svtv-override-triple x1) (cdar x))
       (new-test (svex-subst x1.test subst))
       (new-val (svex-subst x1.val subst))
       ((when (or (equal new-test (svex-x))
                  (equal new-val (svex-x))))
        (svtv-override-triplemap-split (cdr x) subst))
       ((mv rest-consts rest-trips)
        (svtv-override-triplemap-split (cdr x) subst))
       ((when (and (svex-case new-test :quote)
                   (svex-case new-val :quote)))
        (mv (cons (make-svtv-override-constant
                   :test (svex-quote->val new-test)
                   :val (svex-quote->val new-val)
                   :refvar x1.refvar)
                  rest-consts)
            rest-trips)))
    (mv rest-consts
        (cons (change-svtv-override-triple x1
                                           :test new-test
                                           :val new-val)
              rest-trips)))
  ///
  (defret triplemap-ok-iff-consts-and-triples-ok-of-<fn>
    (iff (and (svtv-override-constantlist-ok consts ref-env)
              (svtv-override-triplelist-ok triples pipe-env ref-env))
         (svtv-override-triplemap-ok x (svex-alist-eval subst pipe-env) ref-env))
    :hints(("Goal" :in-theory (enable svtv-override-triplemap-ok
                                      svtv-override-triplelist-ok
                                      svtv-override-constantlist-ok
                                      svtv-override-triple-ok)
            :induct <call>)
           (and stable-under-simplificationp
                '(:use ((:instance svex-eval-of-svex-subst
                         (pat (svtv-override-triple->test (cdar x)))
                         (al subst)
                         (env pipe-env))
                        (:instance svex-eval-of-svex-subst
                         (pat (svtv-override-triple->val (cdar x)))
                         (al subst)
                         (env pipe-env)))
                  :in-theory (disable svex-eval-of-svex-subst))))
    :rule-classes nil)
  
  (defret svtv-override-triplelist-ok-of-<fn>
    (implies (svtv-override-constantlist-ok consts ref-env)
             (equal (svtv-override-triplelist-ok triples pipe-env ref-env)
                    (svtv-override-triplemap-ok x (svex-alist-eval subst pipe-env) ref-env)))
    :hints(("Goal" :use triplemap-ok-iff-consts-and-triples-ok-of-<fn>)))

  (defret svtv-override-constantlist-ok-of-<fn>
    (implies (svtv-override-triplelist-ok triples pipe-env ref-env)
             (equal (svtv-override-constantlist-ok consts ref-env)
                    (svtv-override-triplemap-ok x (svex-alist-eval subst pipe-env) ref-env)))
    :hints(("Goal" :use triplemap-ok-iff-consts-and-triples-ok-of-<fn>)))

  (defret triplemap-ok-implies-<fn>-ok
    (implies (svtv-override-triplemap-ok x (svex-alist-eval subst pipe-env) ref-env)
             (and (svtv-override-triplelist-ok triples pipe-env ref-env)
                  (svtv-override-constantlist-ok consts ref-env)))
    :hints(("Goal" :use triplemap-ok-iff-consts-and-triples-ok-of-<fn>))))

(define svtv-override-triplemaplist-split ((x svtv-override-triplemaplist-p)
                                                          (subst svex-alist-p))
  :returns (mv (consts svtv-override-constantlist-p)
               (triples svtv-override-triplelist-p))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv first-consts first-triples) (svtv-override-triplemap-split (car x) subst))
       ((mv rest-consts rest-triples) (svtv-override-triplemaplist-split (cdr x) subst)))
    (mv (append first-consts rest-consts)
        (append first-triples rest-triples)))
  ///

  (defret triplemaplist-ok-iff-consts-and-triples-ok-of-<fn>
    (iff (and (svtv-override-constantlist-ok consts ref-env)
              (svtv-override-triplelist-ok triples pipe-env ref-env))
         (svtv-override-triplemaplist-ok x (svex-alist-eval subst pipe-env) ref-env))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-ok)))
    :rule-classes nil)
  
  (defret svtv-override-triplelist-ok-of-<fn>
    (implies (svtv-override-constantlist-ok consts ref-env)
             (equal (svtv-override-triplelist-ok triples pipe-env ref-env)
                    (svtv-override-triplemaplist-ok x (svex-alist-eval subst pipe-env) ref-env)))
    :hints (("goal" :use triplemaplist-ok-iff-consts-and-triples-ok-of-<fn>)))

  (defret svtv-override-constantlist-ok-of-<fn>
    (implies (svtv-override-triplelist-ok triples pipe-env ref-env)
             (equal (svtv-override-constantlist-ok consts ref-env)
                    (svtv-override-triplemaplist-ok x (svex-alist-eval subst pipe-env) ref-env)))
    :hints (("goal" :use triplemaplist-ok-iff-consts-and-triples-ok-of-<fn>)))

  (defret triplemaplist-ok-implies-<fn>-ok
    (implies (svtv-override-triplemaplist-ok x (svex-alist-eval subst pipe-env) ref-env)
             (and (svtv-override-triplelist-ok triples pipe-env ref-env)
                  (svtv-override-constantlist-ok consts ref-env)))
    :hints(("Goal" :use triplemaplist-ok-iff-consts-and-triples-ok-of-<fn>)))

  (local (defcong svex-envs-similar equal (svtv-override-triple-ok triple pipe-env ref-env) 2
           :hints(("Goal" :in-theory (enable svtv-override-triple-ok)))))
  
  (local (defcong svex-envs-similar equal (svtv-override-triplemap-ok triplemap pipe-env ref-env) 2
           :hints(("Goal" :in-theory (enable svtv-override-triplemap-ok)))))

  (local (defcong svex-envs-similar equal (svtv-override-triplemaplist-ok triplemaplist pipe-env ref-env) 2
           :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-ok)))))

  (local (defthm member-alist-keys
           (iff (member-equal k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))
  
  (local (defthm svex-env-extract-alist-keys-under-svex-envs-similar
           (implies (equal keys (alist-keys (svex-env-fix x)))
                    (svex-envs-similar (svex-env-extract keys x)
                                       x))
           :hints(("Goal" :in-theory (enable svex-envs-similar
                                             svex-env-lookup)))))

  (local (defret triplemaplist-ok-implies-<fn>-consts-ok-special
           (implies (and (bind-free '((pipe-env . pipe-env)) (pipe-env))
                         (svtv-override-triplemaplist-ok x (svex-alist-eval subst pipe-env) ref-env))
                    (svtv-override-constantlist-ok consts ref-env))))
  
  (defthmd svtv-override-triplemaplist-ok-simplify-when-known-keys
    (implies (and (syntaxp (quotep x))
                  (equal pipe-keys (alist-keys (svex-env-fix pipe-env)))
                  (syntaxp (quotep pipe-keys))
                  (equal consts-and-triples (svtv-override-triplemaplist-split
                                             x (svex-identity-subst pipe-keys))))
             (equal (svtv-override-triplemaplist-ok x pipe-env ref-env)
                    (and (svtv-override-constantlist-ok (mv-nth 0 consts-and-triples) ref-env)
                         (svtv-override-triplelist-ok (mv-nth 1 consts-and-triples) pipe-env ref-env))))
    :hints (("Goal" :in-theory (disable svtv-override-triplemaplist-split)))))






(def-ruleset! svtv-idealized-thm-rules
  '((:CONGRUENCE
     4VEC-OVERRIDE-VALUES-OK-<<=-4VEC-EQUIV-CONGRUENCE-ON-VAL)
    (:CONGRUENCE
     CONS-4VEC-EQUIV-CONGRUENCE-ON-V-UNDER-SVEX-ENV-EQUIV)
    (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
    (:DEFINITION 4VEC-EQUIV$INLINE)
    (:DEFINITION 4VEC-OVERRIDE-VALUES-OK-<<=)

    (:DEFINITION SVEX-ENV-FASTLOOKUP)
    (:DEFINITION SVTV-OVERRIDE-TRIPLE-OK)
    (:DEFINITION SYNP)
    (:EXECUTABLE-COUNTERPART 2VEC-P$INLINE)
    (:EXECUTABLE-COUNTERPART 4VEC-<<=)
    (:EXECUTABLE-COUNTERPART 4VEC-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART ALIST-KEYS)
    
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
    (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLEMAPLIST-SPLIT)
    (:META HONS-INTERSECTION-FORCE-EXECUTE)
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
    (:REWRITE SVTV-OVERRIDE-TRIPLELIST-OK-OF-CONS)
    (:REWRITE SVTV-OVERRIDE-TRIPLELIST-OK-OF-NIL)
    (:REWRITE
     SVTV-OVERRIDE-TRIPLEMAPLIST-OK-SIMPLIFY-WHEN-KNOWN-KEYS)))

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





(defun svtv-idthm-final-thm (x)
  (b* (((svtv-generalized-thm x))
       (template
         '(defthm <name>
            (b* (((svassocs <input-var-svassocs>) env)
                 (run (svtv-spec-run (<ideal>) env
                                     :base-ins base-ins
                                     :initst initst))
                 ((svassocs <override-svassocs>) run))
              (implies (and <constlist-hyp>
                            <hyp>
                            <input-binding-hyp>)
                       (b* (((svassocs <outputs>) run))
                         <concl>)))
            :hints (:@ :no-lemmas <hints>)
            (:@ (not :no-lemmas)
             (("Goal" :use ((:instance <ideal>-refines-<svtv>
                             (spec-pipe-env env)
                             (spec-base-ins base-ins)
                             (spec-initst initst)
                             (pipe-env (b* ((?run (svtv-spec-run (<ideal>) env
                                                                 :base-ins base-ins
                                                                 :initst initst))
                                            ((svassocs <override-svassocs>) run)
                                            ((svassocs <input-unbound-svassocs>) env))
                                         (APPEND <input-bindings>
                                                 <input-vars>
                                                 <override-tests>
                                                 <override-vals>))))
                            (:instance <name>-override-lemma
                             <override-var-instantiation>
                             <input-var-instantiation>))
               :in-theory (acl2::e/d**
                           ((:EXECUTABLE-COUNTERPART <SVTV>-TRIPLEMAPLIST)
                            (:REWRITE SVARLIST-P-OF-<SVTV>-INPUT-VARS)
                            (:ruleset svtv-idealized-thm-rules))
                           )
               )
              . <hints>)))))
    (acl2::template-subst
     template
     :atom-alist
     `((<hyp> . ,x.hyp)
       (<concl> . ,x.concl)
       (<ideal> . ,x.ideal)
       (<constlist-hyp> . ,x.constlist-hyp)
       (<hints> . ,x.hints)
       (<input-bindings> . (list . ,(svtv-genthm-input-var-bindings-alist-termlist x.input-var-bindings)))
       (<input-vars> . (list . ,(svtv-genthm-var-alist-termlist x.input-vars)))
       (<override-tests> . ',(svtv-genthm-override-test-alist x.override-vars x.triple-val-alist x.triples-name))
       (<override-vals> . (list . ,(svtv-genthm-var-alist-termlist x.override-vars))))
     :splice-alist
     `((<input-var-svassocs> . ,(append x.input-vars (strip-cars x.input-var-bindings)))
       (<input-unbound-svassocs> . ,x.input-vars)
       (<override-svassocs> . ,(svtv-genthm-override-svassocs x.override-vars x.triple-val-alist x.triples-name))
       (<input-binding-hyp> .  ,(svtv-genthm-input-binding-hyp-termlist x.input-var-bindings))
       (<override-var-instantiation> . ,(svtv-idthm-override-var-instantiation x.override-vars x.triple-val-alist x.triples-name x.ideal))
       (<input-var-instantiation> . ,(svtv-genthm-input-var-instantiation x.input-vars))
       (<outputs> . ,x.output-vars)
       (<enable> . ,x.enable))
     :str-alist `(("<NAME>" . ,(symbol-name x.name))
                  ("<SVTV>" . ,(symbol-name x.svtv))
                  ("<IDEAL>" . ,(symbol-name x.ideal)))
     :features (and x.no-lemmas '(:no-lemmas))
     :pkg-sym x.pkg-sym)))




(defun svtv-idealized-thm-events (x)
  (b* (((svtv-generalized-thm x))
       (err (svtv-genthm-error x))
       ((when err) (er hard? `(def-svtv-idealized-thm ,x.name) "Error: ~@0" err)))
    `(defsection ,x.name
       ,@(and (not x.no-lemmas)
              `((local ,(svtv-genthm-initial-override-lemma x))))
       ,(svtv-idthm-final-thm x))))



(defun svtv-idealized-thm-fn (name args state)
  (declare (xargs :stobjs state))
  (b* ((defaults (table-alist 'svtv-idealized-thm-defaults (w state)))
       (ctx `(def-svtv-generalized-thm ,name))
       ((std::extract-keyword-args
         :defaults defaults
         :ctx ctx
         svtv
         ideal
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
         no-lemmas
         no-integerp
         hints
         rule-classes
         (pkg-sym name))
        args)
       
       ((mv err trans-parts state) (svtv-genthm-translate-lst output-parts ctx (w state) state))
       ((when err) (er soft ctx "Couldn't translate output-parts: ~@0~%" err))
       (output-part-vars (all-vars1-lst trans-parts nil))
       ((mv err svtv-val) (magic-ev-fncall svtv nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list svtv)))
       (hyp (if unsigned-byte-hyps
                (b* ((inmasks (svtv->inmasks svtv-val))
                     (inputs (append input-vars override-vars))
                     (masks (acl2::fal-extract inputs inmasks)))
                  `(and ,@(svtv-unsigned-byte-hyps masks) ,hyp))
              hyp))
       (triplemaplist (acl2::template-subst
                 '<svtv>-triplemaplist
                 :str-alist `(("<SVTV>" . ,(symbol-name svtv)))
                 :pkg-sym pkg-sym))
       ((mv err triplemaplist-val) (magic-ev-fncall triplemaplist nil state t t))
       ((when err) (er soft ctx "Couldn't evaluate ~x0" (list triplemaplist)))
       ((mv consts &)
        (svtv-override-triplemaplist-split triplemaplist-val nil))

       (triplelist (svtv-override-triplemaplist-to-triplelist triplemaplist-val))
       (triple-val-alist (svtv-override-triplelist-val-alist triplelist))
       
       (constlist-hyp (if consts
                          `(svtv-override-constantlist-ok ',consts run)
                        t))
       ((acl2::with-fast triple-val-alist)))

    (value
     (svtv-idealized-thm-events
      (make-svtv-generalized-thm
       :name name
       :override-vars override-vars
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
       :lemma-defthm lemma-defthm
       :lemma-args lemma-args
       :hints hints
       :triples-name triplemaplist
       :triple-val-alist triple-val-alist
       :no-lemmas no-lemmas
       :no-integerp no-integerp
       :constlist-hyp constlist-hyp
       :rule-classes rule-classes
       :pkg-sym pkg-sym)))))

(defmacro def-svtv-idealized-thm (name &rest args)
  `(make-event (svtv-idealized-thm-fn ',name ',args state)))







(deftheory foo
  '(
    ; (:EXECUTABLE-COUNTERPART <NAME>-TRIPLEMAPLIST)
    ; (:REWRITE SVARLIST-P-OF-<NAME>-INPUT-VARS)


    (:CONGRUENCE
     4VEC-OVERRIDE-VALUES-OK-<<=-4VEC-EQUIV-CONGRUENCE-ON-VAL)
    (:CONGRUENCE
     CONS-4VEC-EQUIV-CONGRUENCE-ON-V-UNDER-SVEX-ENV-EQUIV)
    (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1)
    (:DEFINITION 4VEC-EQUIV$INLINE)
    (:DEFINITION 4VEC-OVERRIDE-VALUES-OK-<<=)

    (:DEFINITION SVEX-ENV-FASTLOOKUP)
    (:DEFINITION SVTV-OVERRIDE-TRIPLE-OK)
    (:DEFINITION SYNP)
    (:EXECUTABLE-COUNTERPART 2VEC-P$INLINE)
    (:EXECUTABLE-COUNTERPART 4VEC-<<=)
    (:EXECUTABLE-COUNTERPART 4VEC-FIX$INLINE)
    (:EXECUTABLE-COUNTERPART ALIST-KEYS)
    
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
    (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLEMAPLIST-SPLIT)
    (:META HONS-INTERSECTION-FORCE-EXECUTE)
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
    (:REWRITE SVTV-OVERRIDE-TRIPLELIST-OK-OF-CONS)
    (:REWRITE SVTV-OVERRIDE-TRIPLELIST-OK-OF-NIL)
    (:REWRITE
     SVTV-OVERRIDE-TRIPLEMAPLIST-OK-SIMPLIFY-WHEN-KNOWN-KEYS)))
