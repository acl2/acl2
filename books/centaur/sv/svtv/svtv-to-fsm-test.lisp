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
  :svtv-spec counter-invar-spec :inclusive-overridekeys t)

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

(defthm svtv-spec-fsm-syntax-check-of-counter-invar-spec
  (svtv-spec-fsm-syntax-check (counter-invar-spec))
  :hints(("Goal" :in-theory '((counter-invar-spec)
                              (svtv-spec-fsm-syntax-check)))))



(cmr::def-force-execute svtv-spec-fsm-bindings-when-variable-free svtv-spec-fsm-bindings)
(local (in-theory (enable svtv-spec-fsm-bindings-when-variable-free)))

(cmr::def-force-execute svtv-cyclephaselist-keys-when-variable-free svtv-cyclephaselist-keys)
(local (in-theory (enable svtv-cyclephaselist-keys-when-variable-free)))



(defthm svarlist-override-p*-of-svex-env-filter-override*
  (svarlist-override-p* (alist-keys (svex-env-filter-override* env types)) types)
  :hints(("Goal" :in-theory (enable svarlist-override-p* alist-keys svex-env-filter-override*))))

(defthm svarlist-override-p*-of-svex-envlist-filter-override*
  (svarlist-override-p* (svex-envlist-all-keys (svex-envlist-filter-override* env types)) types)
  :hints(("Goal" :in-theory (enable svarlist-override-p* svex-envlist-all-keys svex-envlist-filter-override*))))

(defthm cyclephaselist-has-outputs-captured-of-counter-invar-spec
  (svtv-cyclephaselist-has-outputs-captured (svtv-spec->cycle-phases (counter-invar-spec)))
  :hints (("goal" :in-theory '((svtv-cyclephaselist-has-outputs-captured)
                               (svtv-spec->cycle-phases)
                               (counter-invar-spec)))))



(local (in-theory (disable (tau-system))))


(defcong svex-envs-similar svex-envs-similar (svex-env-x-override x y) 1
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(define svex-alist-all-xes-p ((x svex-alist-p))
  (if (atom x)
      t
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (and (equal (cdar x) (svex-x))
             (svex-alist-all-xes-p (cdr x)))
      (svex-alist-all-xes-p (cdr x))))
  ///
  (defthmd lookup-when-svex-alist-all-xes-p
    (implies (and (svex-alist-all-xes-p x)
                  (svex-lookup k x))
             (equal (svex-lookup k x) (svex-x)))
    :hints(("Goal" :in-theory (enable svex-lookup-redef))))

  (defthmd eval-when-svex-alist-all-xes-under-svex-envs-similar
    (implies (svex-alist-all-xes-p x)
             (svex-envs-similar (svex-alist-eval x env) nil))
    :hints(("Goal" :in-theory (enable lookup-when-svex-alist-all-xes-p
                                      svex-envs-similar))))
  
  (defthm svex-alist-<<=-when-svex-alist-all-xes-p
    (implies (svex-alist-all-xes-p x)
             (svex-alist-<<= x y))
    :hints(("Goal" :in-theory (enable svex-alist-<<=
                                      eval-when-svex-alist-all-xes-under-svex-envs-similar)
            :do-not-induct t)))

  (defthm svex-env-x-override-when-svex-alist-all-xes-p
    (implies (svex-alist-all-xes-p x)
             (svex-envs-similar (svex-env-x-override
                                 (svex-alist-eval x env)
                                 env2)
                                env2))
    :hints(("Goal" :in-theory (enable eval-when-svex-alist-all-xes-under-svex-envs-similar)
            :do-not-induct t))))

(defthm svex-alist-all-xes-of-counter-invar-spec-initst
  (svex-alist-all-xes-p (svtv-spec->initst-alist (counter-invar-spec)))
  :hints(("Goal" :in-theory '((svex-alist-all-xes-p)
                              (svtv-spec->initst-alist)
                              (counter-invar-spec)))))


(defthm svex-envlist-all-keys-of-svtv-cycle-fsm-inputs-when-no-i/o-phase
  (implies (svtv-cyclephaselist-no-i/o-phase phases)
           (set-equiv (svex-envlist-all-keys (svtv-cycle-fsm-inputs env phases))
                      (And (consp phases)
                           (svtv-cyclephaselist-keys phases))))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-no-i/o-phase
                                    svtv-cyclephaselist-keys
                                    svtv-cycle-fsm-inputs
                                    svtv-cycle-step-fsm-inputs
                                    svex-envlist-all-keys))))
             
(defthm svex-envlist-all-keys-of-svtv-cycle-fsm-inputs-when-unique-i/o-phase
  (implies (svtv-cyclephaselist-unique-i/o-phase phases)
           (set-equiv (svex-envlist-all-keys (svtv-cycle-fsm-inputs env phases))
                      (append (svtv-cyclephaselist-keys phases)
                              (alist-keys (svex-env-fix env)))))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-unique-i/o-phase
                                    svtv-cyclephaselist-keys
                                    svtv-cycle-fsm-inputs
                                    svtv-cycle-step-fsm-inputs
                                    svex-envlist-all-keys))))

(defthm svex-envlist-all-keys-of-append
  (equal (svex-envlist-all-keys (append x y))
         (append (svex-envlist-all-keys x)
                 (svex-envlist-all-keys y)))
  :hints(("Goal" :in-theory (enable svex-envlist-all-keys))))

(defthm svex-envlist-all-keys-of-svtv-cycle-run-fsm-inputs
  (implies (svtv-cyclephaselist-unique-i/o-phase phases)
           (set-equiv (svex-envlist-all-keys (svtv-cycle-run-fsm-inputs envs phases))
                      (and (consp envs)
                           (append (svtv-cyclephaselist-keys phases)
                                   (svex-envlist-all-keys envs)))))
  :hints(("Goal" :in-theory (e/d (svtv-cycle-run-fsm-inputs
                                  svex-envlist-all-keys)
                                 (append)))))


(defthm consp-of-svex-envlist-filter-override*
  (equal (consp (svex-envlist-filter-override* envs types))
         (consp envs))
  :hints(("Goal" :in-theory (enable svex-envlist-filter-override*))))
                

(defthm svarlist-nonoverride-p-of-cons
  (implies (not (svar-override-p var type))
           (equal (svarlist-nonoverride-p (cons var rest) type)
                  (svarlist-nonoverride-p rest type)))
  :hints(("Goal" :in-theory (enable svarlist-nonoverride-p))))

(defthm svex-env-x-override-remove-test-vars
  (implies (and (svex-env-<<= (svex-env-remove-override a :test)
                              (svex-env-remove-override b :test))
                (svex-envs-similar (svex-env-filter-override a :test)
                                   (svex-env-filter-override b :test)))
           (svex-envs-similar (svex-env-x-override a (svex-env-remove-override b :test)) b))
  :hints ((and stable-under-simplificationp
               (b* ((lit (car (last clause)))
                    (witness `(svex-envs-similar-witness . ,(cdr lit))))
                 `(:expand (,(car (last clause)))
                   :use ((:instance svex-env-<<=-necc
                          (x (svex-env-remove-override a :test))
                          (y (svex-env-remove-override b :test))
                          (var ,witness))

                         (:instance svex-envs-similar-necc
                          (x (svex-env-filter-override a :test))
                          (y (svex-env-filter-override b :test))
                          (k ,witness)))
                   :in-theory (disable svex-env-<<=-necc
                                       SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-LOOKUP-2))))))

(defthm svex-envlist-x-override-remove-test-vars
  (implies (and (svex-envlist-<<= (svex-envlist-remove-override a :test)
                              (svex-envlist-remove-override b :test))
                (svex-envlists-similar (svex-envlist-filter-override a :test)
                                       (svex-envlist-filter-override b :test))
                )
           (svex-envlists-similar (svex-envlist-x-override a (svex-envlist-remove-override b :test)) b))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                    svex-envlists-similar-rec
                                    svex-envlist-remove-override
                                    svex-envlist-filter-override
                                    svex-envlist-x-override)
          :induct (svex-envlist-x-override a b))))


(defthm svex-env-<<=-of-append-left
  (implies (and (svex-env-<<= a c)
                (svex-env-<<= b c))
           (svex-env-<<= (append a b) c))
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(encapsulate
  nil
  (local (defun ind (a b c)
           (declare (Xargs :measure (+ (len a) (len b))))
           (if (and (atom a) (atom b))
               (list c)
             (ind (cdr a) (Cdr b) (cdr c)))))

  (local (defthm true-list-fix-under-svex-env-equv
           (svex-env-equiv (true-list-fix x) x)
           :hints(("Goal" :in-theory (enable svex-env-fix true-list-fix)))))
  
  (defthm svex-envlist-<<=-of-append-each-left
    (implies (and (svex-envlist-<<= a c)
                  (svex-envlist-<<= b c))
             (svex-envlist-<<= (append-each a b) c))
    :hints(("goal" :in-theory (e/d (svex-envlist-<<= append-each))
            :induct (ind a b c)))))


(defthmd svex-env-<<=-of-remove-when-svarlist-override-p
  (implies (and (svarlist-override-p (alist-keys (svex-env-fix x)) type)
                (not (svar-overridetype-equiv type type1)))
           (iff (svex-env-<<= x (svex-env-remove-override y type1))
                (svex-env-<<= x y)))
  :hints (("goal" :in-theory (disable svar-overridetype-equiv))
          (and stable-under-simplificationp
               (b* ((lit (assoc 'svex-env-<<= clause))
                    (?witness `(svex-env-<<=-witness . ,(cdr lit)))
                    (?other (if (eq (caddr lit) 'y)
                               '(svex-env-remove-override y type1)
                             'y)))
                 `(:expand (,lit)
                   :use ((:instance svex-env-<<=-necc
                          (x x) (y ,other) (var ,witness)))
                   :in-theory (e/d (svex-env-lookup-when-not-boundp
                                    svex-env-boundp-iff-member-alist-keys
                                    member-when-svar-override-p-diff)
                                   (svex-env-<<=-necc
                                    svar-overridetype-equiv
                                    acl2::alist-keys-member-hons-assoc-equal)))))))
                 

(defthmd svex-envlist-<<=-of-remove-when-svarlist-override-p
  (implies (and (svarlist-override-p (svex-envlist-all-keys x) type)
                (not (svar-overridetype-equiv type type1)))
           (iff (svex-envlist-<<= x (svex-envlist-remove-override y type1))
                (svex-envlist-<<= x y)))
  :hints(("Goal" :in-theory (enable svex-envlist-all-keys
                                    svex-envlist-<<=
                                    svex-envlist-remove-override
                                    svex-env-<<=-of-remove-when-svarlist-override-p))))

(defthm svex-envlist-<<=-of-svtv-fsm-namemap-envlist-override
  (implies (and (bind-free (and (consp x)
                                (equal (car x)  'svtv-fsm-namemap-envlist)
                                (quotep (nth 3 x))
                                `((type . ,(nth 3 x)))))
                (svarlist-override-p (svex-envlist-all-keys x) type)
                (not (svar-overridetype-equiv type type1)))
           (iff (svex-envlist-<<= x (svex-envlist-remove-override y type1))
                (svex-envlist-<<= x y)))
  :hints(("Goal" :in-theory (enable svex-envlist-<<=-of-remove-when-svarlist-override-p))))



(define lookup-of-SVTV-SPEC-FSM-BINDINGS-WHEN-VARIABLE-FREE-hyp ((x pseudo-termp) mfc state)
  (declare (ignore mfc state))
  :returns (hyp pseudo-termp)
  (case-match x
    (('hons-assoc-equal & ('svtv-spec-fsm-bindings . &)) ''t)
    (& ''nil)))


(DEFTHM lookup-of-SVTV-SPEC-FSM-BINDINGS-WHEN-VARIABLE-FREE
  (IMPLIES
   (AND (PSEUDO-TERMP X)
        (ALISTP ACL2::A)
        (ACL2::MEXTRACT-EV-GLOBAL-FACTS)
        (acl2::mextract-ev (lookup-of-svtv-spec-fsm-bindings-when-variable-free-hyp x mfc state) acl2::a))
   (EQUAL
    (ACL2::MEXTRACT-EV X ACL2::A)
    (ACL2::MEXTRACT-EV
     (CMR::EXECUTE-TERM-WHEN-VARIABLE-FREE X MFC STATE)
     ACL2::A)))
  :HINTS
  (("Goal" :IN-THEORY
    '(CMR::EXECUTE-TERM-WHEN-VARIABLE-FREE-CORRECT)))
  :RULE-CLASSES
  ((:META :TRIGGER-FNS (hons-assoc-equal))))


(defcong svex-envlists-similar equal (lhprobe-eval x envs) 2
  :hints(("Goal" :in-theory (enable lhprobe-eval
                                    svex-envlists-similar-rec))))

(defcong svex-envlists-similar equal (lhprobe-map-eval x envs) 2
  :hints(("Goal" :in-theory (enable lhprobe-map-eval
                                    svex-envlists-similar-rec))))

;; ;; want to show this is true:

;; (SVEX-ENVLISTS-SIMILAR
;;  (SVTV-FSM-NAMEMAP-ENVLIST
;;   (SVEX-ALISTLIST-EVAL
;;    (TAKE
;;      (LEN (SVTV-PROBEALIST-OUTVARS (SVTV-SPEC->PROBES (COUNTER-INVAR-SPEC))))
;;      (SVTV-SPEC->OVERRIDE-TEST-ALISTS (COUNTER-INVAR-SPEC)))
;;    (LHPROBE-MAP-EVAL (SVTV-SPEC-FSM-BINDINGS (COUNTER-INVAR-SPEC))
;;                      ENVS))
;;   (SVTV-SPEC->NAMEMAP (COUNTER-INVAR-SPEC))
;;   :TEST)
;;  '((((:VAR "sum1" . 32) . 15)
;;     ((:VAR "sum" . 32) . 15))
;;    NIL))

;; ;; under the assumption:

;; (SVEX-ENVLISTS-SIMILAR (SVEX-ENVLIST-FILTER-OVERRIDE ENVS :TEST)
;;                            '((((:VAR "sum1" . 32) . 15)
;;                               ((:VAR "sum" . 32) . 15))
;;                              NIL))

;; ;; this is true because the alists:
;; (TAKE
;;      (LEN (SVTV-PROBEALIST-OUTVARS (SVTV-SPEC->PROBES (COUNTER-INVAR-SPEC))))
;;      (SVTV-SPEC->OVERRIDE-TEST-ALISTS (COUNTER-INVAR-SPEC)))

(defcong svex-envs-similar equal (svex-envs-agree vars x y) 2
  :hints(("Goal" :in-theory (enable svex-envs-agree))))

(defcong svex-envs-similar equal (svex-envs-agree vars x y) 3
  :hints(("Goal" :in-theory (enable svex-envs-agree))))

(local (defthm lhprobe-map-eval-of-fal-extract
         (implies (svarlist-p vars)
                  (svex-envs-similar (lhprobe-map-eval (fal-extract vars x) env)
                                     (svex-env-extract vars (lhprobe-map-eval x env))))
         :hints(("Goal" :in-theory (enable svex-envs-similar)))))

(local (defthm svex-envs-agree-of-svex-env-extract-second
         (svex-envs-agree vars x (svex-env-extract vars x))
         :hints(("Goal" :in-theory (enable svex-envs-agree-by-witness)))))

(defthm svex-env-extract-of-filter-override
  (implies (svarlist-override-p vars type)
           (equal (svex-env-extract vars (svex-env-filter-override x type))
                  (svex-env-extract vars x)))
  :hints(("Goal" :in-theory (enable svex-env-extract svarlist-override-p))))

(defthm svex-envlist-extract-of-filter-override
  (implies (svarlist-override-p vars type)
           (equal (svex-envlist-extract-keys vars (svex-envlist-filter-override x type))
                  (svex-envlist-extract-keys vars x)))
  :hints(("Goal" :in-theory (enable svex-envlist-extract-keys svex-envlist-filter-override))))

(local (defthm lhprobe-map-eval-of-svex-envlist-extract-vars-similar
         (IMPLIES
                 (SUBSETP-EQUAL (LHPROBE-MAP-VARS X)
                                (SVARLIST-FIX VARS))
                 (svex-envs-similar
                   (LHPROBE-MAP-EVAL X (SVEX-ENVLIST-EXTRACT-KEYS VARS ENVS))
                   (LHPROBE-MAP-EVAL X ENVS)))))

;; reference only variables (though none in this case) that are mapped to override-test vars by bindings.
;; So something like this:
(defthm filter-envs-when-alist/lhprobe-vars
  (implies (and (svex-envlists-similar (svex-envlist-filter-override envs :test) const)
                (syntaxp (quotep const))
                (equal alistvars (svex-alistlist-vars alists))
                (syntaxp (quotep alistvars))
                (equal lhvars (lhprobe-map-vars (fal-extract alistvars (lhprobe-map-fix lhmap))))
                (syntaxp (quotep lhvars))
                (svarlist-override-p lhvars :test))
           (equal (svex-alistlist-eval alists (lhprobe-map-eval lhmap envs))
                  (svex-alistlist-eval alists (lhprobe-map-eval lhmap const))))
  :hints (("goal" :use ((:instance svex-alistlist-eval-when-envs-agree
                         (x alists)
                         (env1 (lhprobe-map-eval lhmap envs))
                         (env2 (lhprobe-map-eval (fal-extract (svex-alistlist-vars alists) (lhprobe-map-fix lhmap))
                                                 envs)))
                        (:instance svex-alistlist-eval-when-envs-agree
                         (x alists)
                         (env1 (lhprobe-map-eval lhmap const))
                         (env2 (lhprobe-map-eval (fal-extract (svex-alistlist-vars alists) (lhprobe-map-fix lhmap))
                                                 const)))
                        (:instance lhprobe-map-eval-of-svex-envlist-extract-vars-similar
                         (x (fal-extract (svex-alistlist-vars alists) (lhprobe-map-fix lhmap)))
                         (vars (lhprobe-map-vars (fal-extract (svex-alistlist-vars alists) (lhprobe-map-fix lhmap))))
                         (envs (svex-envlist-filter-override envs :test)))
                        (:instance lhprobe-map-eval-of-svex-envlist-extract-vars-similar
                         (x (fal-extract (svex-alistlist-vars alists) (lhprobe-map-fix lhmap)))
                         (vars (lhprobe-map-vars (fal-extract (svex-alistlist-vars alists) (lhprobe-map-fix lhmap))))
                         (envs envs)))
           :in-theory (disable svex-alistlist-eval-when-envs-agree
                               lhprobe-map-eval-of-svex-envlist-extract-vars
                               lhprobe-map-eval-of-svex-envlist-extract-vars-similar)
           :do-not-induct t)))

(cmr::def-force-execute svex-alistlist-vars-when-variable-free svex-alistlist-vars)
(cmr::def-force-execute lhprobe-map-vars-when-variable-free lhprobe-map-vars)
(cmr::def-force-execute SVTV-FSM-NAMEMAP-ENVLIST-when-variable-free SVTV-FSM-NAMEMAP-ENVLIST)
(local (in-theory (enable svex-alistlist-vars-when-variable-free
                          lhprobe-map-vars-when-variable-free
                          svtv-fsm-namemap-envlist-when-variable-free)))



(local (in-theory (disable unsigned-byte-p)))

(defthm counter-invar-fsm-thm
  (b* (((svtv-spec svtv) (counter-invar-spec))
       (fsm (svtv-spec->cycle-fsm svtv))
       ((sv::svassocs inc sum1)
        (lhprobe-map-eval (svtv-spec-fsm-bindings svtv) envs))
       (outs (base-fsm-eval envs initst fsm))
       ((sv::svassocs (sum 'sum-prev) sum-out sum1-out)
        (svtv-spec-cycle-outs->pipe-out svtv outs)))
    (implies (and (lhprobe-constraintlist-eval (svtv-spec-fsm-constraints (counter-invar-spec)) envs)
                  (svex-envlists-similar (svex-envlist-filter-override envs :test)
                                         '((((:VAR "sum1" . 32) . 15)
                                            ;; ((:VAR "sum" . 32) . 15)
                                            )
                                           NIL))
                  (unsigned-byte-p 1 inc)
                  (unsigned-byte-p 4 sum1)
                  (unsigned-byte-p 4 sum)
                  (<= sum 11)
                  (<= sum1 10)
                  (equal (len envs) 2))
             (and (<= sum-out 11)
                  (<= sum1-out 10))))
  :hints (("goal" :use ((:instance counter-invar-svtv-thm
                         (env (lhprobe-map-eval (svtv-spec-fsm-bindings (counter-invar-spec)) envs))
                         (base-ins (svtv-cycle-run-fsm-inputs
                                    (svex-envlist-remove-override envs :test)
                                    (svtv-spec->cycle-phases (counter-invar-spec))))))
           :in-theory (e/d (lhprobe-eval lhatom-eval-zero lhprobe-map-eval
                                         svex-env-lookup-of-cons
                                         svtv-spec-run-in-terms-of-cycle-fsm
                                         CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
                                         lookup-of-svtv-spec-fsm-bindings-when-variable-free)
                           (counter-invar-svtv-thm
                            acl2::take-of-too-many
                            SVTV-SPEC-FSM-BINDINGS-WHEN-VARIABLE-FREE
                            ;; LOOKUP-OF-LHPROBE-MAP-EVAL
                            ))
           :do-not-induct t)
          ;; (and stable-under-simplificationp
          ;;      '(:in-theory (e/d (lhprobe-eval lhatom-eval-zero lhprobe-map-eval
          ;;                                svex-env-lookup-of-cons
          ;;                                svtv-spec-run-in-terms-of-cycle-fsm
          ;;                                CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
          ;;                                lookup-of-svtv-spec-fsm-bindings-when-variable-free)
          ;;                  (counter-invar-svtv-thm
          ;;                   acl2::take-of-too-many
          ;;                   ;; SVTV-SPEC-FSM-BINDINGS-WHEN-VARIABLE-FREE
          ;;                   ;; LOOKUP-OF-LHPROBE-MAP-EVAL
          ;;                   ))))
          )
  :otf-flg t)
                  
