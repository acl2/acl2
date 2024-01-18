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

;; (include-book "svtv-fsm-ideal")
(include-book "cycle-probe")
(include-book "assign")
(include-book "../svex/4vec-x-override")
(local (include-book "../svex/svex-lattice"))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/floor-mod" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (in-theory (disable floor mod)))

(local (std::add-default-post-define-hook :fix))

;; How to "run" an ideal FSM as a pseudo-SVTV --

;; When we do cutpoint proofs using SVTVs, the composition is done relative to
;; the idealized FSM, but we still want to give a high-level, SVTV-like
;; interface for it.  So we wrap it in a structure like an SVTV that has all
;; the mappings etc. to give it that interface.

(defthm svex-env-p-nth-of-svex-envlist
  (implies (svex-envlist-p x)
           (svex-env-p (nth n x))))

(defthm nthcdr-of-svex-envlist-fix
  (equal (nthcdr n (svex-envlist-fix x))
         (svex-envlist-fix (nthcdr n x)))
  :hints(("Goal" :in-theory (enable svex-envlist-fix))))


(defthm svtv-cycle-output-phase-iff-has-outputs-captured
  (iff (svtv-cycle-output-phase phases)
       (svtv-cyclephaselist-has-outputs-captured phases))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-has-outputs-captured))))

(defthm svtv-cycle-output-phase-type-when-has-outputs-captured
  (implies (svtv-cyclephaselist-has-outputs-captured x)
           (natp (svtv-cycle-output-phase x)))
  :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                    svtv-cyclephaselist-has-outputs-captured)))
  :rule-classes :type-prescription)

(defthm svtv-cyclephaselist-has-outputs-captured-when-atom
  (implies (atom x)
           (not (svtv-cyclephaselist-has-outputs-captured x)))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured))))

(define svex-envlist-phase-outputs-extract-cycle-outputs ((phases svtv-cyclephaselist-p)
                                                          (phase-outs svex-envlist-p))
  :guard (svtv-cycle-output-phase phases)
  :returns (cycle-outs svex-envlist-p)
  :measure (len phase-outs)
  :verify-guards nil
  (mbe :logic
       (if (<= (len phase-outs)
               (svtv-cycle-output-phase phases))
           nil
         (cons (svex-env-fix (nth (svtv-cycle-output-phase phases) phase-outs))
               (svex-envlist-phase-outputs-extract-cycle-outputs
                phases
                (nthcdr (if (mbt (consp phases))
                            (len phases)
                          1)
                        phase-outs))))
       :exec
       (b* ((outphase (svtv-cycle-output-phase phases))
            (rest (nthcdr (len phases) phase-outs))
            ((when (atom rest))
             (if (<= (len phase-outs) outphase)
                 nil
               (list (nth outphase phase-outs)))))
         (cons (nth outphase phase-outs)
               (svex-envlist-phase-outputs-extract-cycle-outputs phases rest))))
  ///



  (local (defthm svtv-cycle-output-phase-<-len
           (implies (svtv-cyclephaselist-has-outputs-captured phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                             svtv-cyclephaselist-has-outputs-captured)))
           :rule-classes :linear))

  (local (defun nth-of-extract-ind (n phases phase-outs)
           (if (zp n)
               (list phases phase-outs)
             (nth-of-extract-ind (1- n) phases (nthcdr (len phases) phase-outs)))))

  (local (defthm natp-of-times-decr-lemma
           (implies (and (posp n)
                         (natp len)
                         (natp m))
                    (natp (+ (- len)
                             m
                             (* n len))))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))
           :rule-classes :type-prescription))

  (local (defthm plus-x-y-minus-x-z
           (equal (+ x y (* -1 x) z)
                  (+ y z))))

  (defret nth-of-<fn>
    (implies (svtv-cyclephaselist-has-outputs-captured phases)
             (Equal (nth n cycle-outs)
                    (svex-env-fix (nth (+ (svtv-cycle-output-phase phases)
                                          (* (nfix n) (len phases)))
                                       phase-outs))))
    :hints (("goal" :induct (nth-of-extract-ind n phases phase-outs)
             :expand (<call>))))

  (local (defthm svtv-cycle-output-phase-when-not-outputs-captured
           (implies (not (svtv-cyclephaselist-has-outputs-captured phases))
                    (not (svtv-cycle-output-phase phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase
                                             svtv-cyclephaselist-has-outputs-captured)))))

  (defret len-of-<fn>
    (implies (consp phases)
             (equal (len cycle-outs)
                    (+ (floor (len phase-outs) (len phases))
                       (if (< (svtv-cycle-output-phase phases)
                              (mod (len phase-outs) (len phases)))
                           1
                         0))))
    :hints(("Goal" :induct <call>
            :expand ((:with acl2::mod-redef (mod (len phase-outs) (len phases)))
                     (:with acl2::floor-redef (floor (len phase-outs) (len phases)))))
           (and stable-under-simplificationp
                '(:cases ((svtv-cyclephaselist-has-outputs-captured phases))))))

  (local (defthm svtv-cyclephaselist-has-outputs-captured-implies-posp-len
           (implies (svtv-cyclephaselist-has-outputs-captured phases)
                    (posp (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cyclephaselist-has-outputs-captured)))
           :rule-classes :forward-chaining))

  (defthm svtv-probealist-extract-of-probealist-cycle-adjust
    (implies (svtv-cyclephaselist-has-outputs-captured phases)
             (equal (svtv-probealist-extract (svtv-probealist-cycle-adjust probes phases) phase-outputs)
                    (svtv-probealist-extract probes (svex-envlist-phase-outputs-extract-cycle-outputs phases phase-outputs))))
    :hints(("Goal" :in-theory (enable svtv-probealist-extract
                                      svtv-probealist-cycle-adjust
                                      svtv-probealist-cycle-adjust-aux)
            :induct (len probes))))

  (local
   (defthm svtv-name-lhs-map-eval-list-under-iff
     (iff (svtv-name-lhs-map-eval-list namemap envs)
          (consp envs))
     :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list)))))

  (local (defthm consp-of-svex-envlist-phase-outputs-extract-cycle-outputs
           (equal (consp (svex-envlist-phase-outputs-extract-cycle-outputs phases envs))
                  (< (svtv-cycle-output-phase phases) (len envs)))
           :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs)))))


  (local (defthm mod-0-when-less
           (implies (and (natp x) (natp y)
                         (< x y))
                    (equal (equal 0 (mod x y))
                           (equal x 0)))
           :hints (("goal" :in-theory (e/d (acl2::mod-redef) (mod))))))


  (local (defthm nthcdr-of-svtv-name-lhs-map-eval-list
           (equal (nthcdr n (svtv-name-lhs-map-eval-list namemap envs))
                  (svtv-name-lhs-map-eval-list namemap (nthcdr n envs)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list)))))


  (local (defthm consp-of-svtv-name-lhs-map-eval-list
           (equal (consp (svtv-name-lhs-map-eval-list namemap envs))
                  (consp envs))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval-list)))))

  (defthm svex-envlist-phase-outputs-extract-cycle-outputs-of-svtv-name-lhs-map-eval-list
    (implies (and ; (equal 0 (mod (len envs) (len phases)))
                  (svtv-cyclephaselist-has-outputs-captured phases))
             (equal (svex-envlist-phase-outputs-extract-cycle-outputs phases (svtv-name-lhs-map-eval-list namemap envs))
                    (svtv-name-lhs-map-eval-list namemap (svex-envlist-phase-outputs-extract-cycle-outputs phases envs))))
    :hints(("Goal" :in-theory (enable svex-envlist-phase-outputs-extract-cycle-outputs
                                      svtv-name-lhs-map-eval-list
                                      acl2::mod-redef)
            :induct (svex-envlist-phase-outputs-extract-cycle-outputs phases envs)
            :expand ((svex-envlist-phase-outputs-extract-cycle-outputs phases
                                                                       (svtv-name-lhs-map-eval-list namemap envs))))
           (and stable-under-simplificationp
                '(:cases ((equal (len envs) (svtv-cycle-output-phase phases)))))))

  (local (defthm nthcdr-when-gte-len
           (implies (<= (len x) (nfix n))
                    (not (consp (nthcdr n x) )))))

  (verify-guards svex-envlist-phase-outputs-extract-cycle-outputs
    :hints ((and stable-under-simplificationp
                 '(:expand ((SVEX-ENVLIST-PHASE-OUTPUTS-EXTRACT-CYCLE-OUTPUTS
                             PHASES
                             (NTHCDR (LEN PHASES) PHASE-OUTS))))))))






(defthmd svex-envlists-similar-rec
  (equal (svex-envlists-similar x y)
         (if (or (atom x) (atom y))
             (and (atom x) (atom y))
           (and (svex-envs-similar (car x) (car y))
                (svex-envlists-similar (cdr x) (cdr y)))))
  :hints (("goal" :cases ((svex-envlists-similar x y))
           :do-not-induct t)
          (and stable-under-simplificationp
               (b* ((lit (assoc 'svex-envlists-similar clause)))
                 `(:expand (,lit)))))
  :rule-classes ((:definition :install-body nil
                  :controller-alist ((svex-envlists-similar t t)))))


(encapsulate nil
  ;; move
  (defthm svex-env-<<=-self
    (svex-env-<<= a a)
    :hints(("Goal" :in-theory (enable svex-env-<<=))))

  (defthm svex-envlist-<<=-self
    (svex-envlist-<<= a a)
    :hints(("Goal" :in-theory (enable svex-envlist-<<=))))

  (defthm 4vec-<<=-x-means-equiv-x
    (equal (4vec-<<= x (4vec-x))
           (4vec-equiv x (4vec-x)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable 4vec-<<=
                                      4vec-fix-is-4vec-of-fields)))
            (bitops::logbitp-reasoning)))


  (defthm svex-env-<<=-nil-means-similar-to-nil
    (equal (svex-env-<<= x nil)
           (svex-envs-similar x nil))
    :hints (("Goal" :cases ((svex-env-<<= x nil)))
            (and stable-under-simplificationp
                 '(:expand ((svex-envs-similar x nil))
                   :use ((:instance svex-env-<<=-necc
                          (var (svex-envs-similar-witness x nil))
                          (x x) (y nil))))))))

(define svex-envlist-x-override ((a svex-envlist-p)
                                 (b svex-envlist-p))
  :returns (res svex-envlist-p)
  (cond ((atom b) (svex-envlist-fix a))
        ((atom a) (svex-envlist-fix b))
        (t (cons (svex-env-x-override (car a) (car b))
                 (svex-envlist-x-override (cdr a) (cdr b)))))
  ///
  (defret <fn>-when-a-<<=-b
    (implies (and (svex-envlist-<<= a b)
                  (<= (len a) (len b)))
             (svex-envlists-similar res b))
    :hints(("Goal" :in-theory (enable svex-envlists-similar-rec
                                      svex-envlist-<<=))))

  (local (defthm len-equal-0
           (Equal (equal (len x) 0) (atom x))))

  (defret <fn>-when-b-empty
    (implies (and (subsetp-equal b '(nil))
                  (<= (len b) (len a)))
             (equal res (svex-envlist-fix a)))
    :hints(("Goal" :in-theory (enable svex-envlists-similar-rec
                                      svex-envlist-<<=)
            :induct t
            :expand ((svex-env-x-override (car a) nil)))))

  (defret <fn>-lower-bound
    (svex-envlist-<<= a res)
    :hints(("Goal" :in-theory (e/d (svex-envlist-<<=)))))

  (defret len-of-<fn>
    (equal (len res) (max (len a) (len b))))


  (defthm svex-envlist-x-override-monotonic-on-b
    (implies (svex-envlist-<<= b1 b2)
             (svex-envlist-<<= (svex-envlist-x-override a b1)
                               (svex-envlist-x-override a b2)))
    :hints(("Goal" :in-theory (e/d (svex-envlist-<<= svex-envlist-fix)))))

  (defthm svex-envlist-x-override-monotonic-on-a-when-b-is-empty
    (implies (and (svex-envlist-<<= a1 a2)
                  (svex-envlists-similar b nil))
             (svex-envlist-<<= (svex-envlist-x-override a1 b)
                               (svex-envlist-x-override a2 b)))
    :hints(("Goal" :in-theory (e/d (svex-envlist-<<=))))))



(defprod svtv-spec
  :parents (svex-stvs)
  :short "A data object representing a run of an FSM, similar to an SVTV but
without computing the unrolling of the FSM."
  :long "

<p>When creating an @(see svtv) using @(see defsvtv$), a phase FSM is created
for the given design and subsequently that phase FSM is composed further into a
clock cycle FSM and then a combinational pipeline, which is an unrolling of the
cycle FSM.  This pipeline unrolling is the main content of an SVTV
object (namely, its @('outexprs') field).  An svtv-spec object contains the
data necessary to compute the pipeline, but not the unrolled cycle FSM or
pipeline itself.  It can be shown that an @(see svtv-run) of an SVTV is equal
to the @(see svtv-spec-run) of an analogous svtv-spec object.</p>
"
  ((fsm base-fsm-p "The FSM to be run")
   (cycle-phases svtv-cyclephaselist-p
                 "The list of @(see svtv-cyclephase) objects representing the clock cycle")
   (namemap svtv-name-lhs-map-p "Mapping from namemap names to @(see lhs) objects in terms of FSM signal names")
   (probes svtv-probealist-p "Specification for which outputs/internal signals should be sampled when, in terms of namemap names")
   (in-alists svex-alistlist-p "Specification for what (symbolic) inputs are set at what cycles -- a list of binding alists (one for each cycle) of namemap names to constants and user variable names.")
   (override-test-alists svex-alistlist-p "Specification for what override tests are set at what cycles -- similar to in-alists")
   (override-val-alists svex-alistlist-p "Specification for what override values are set at what cycles -- similar to in-alists")
   (initst-alist svex-alist-p "Initial state, mapping from FSM previous-state variables to constants and user variable names")))

(define svtv-spec-pipe-env->phase-envs ((x svtv-spec-p) (pipe-env svex-env-p))
  :returns (phase-envs svex-envlist-p)
  (b* (((svtv-spec x))
       (svtv-fsm-ins (svex-alistlist-eval x.in-alists pipe-env))
       (svtv-fsm-tests (svex-alistlist-eval x.override-test-alists pipe-env))
       (svtv-fsm-vals (svex-alistlist-eval x.override-val-alists pipe-env))
       (cycle-ins (svtv-fsm-to-base-fsm-inputs
                   (take (len (svtv-probealist-outvars x.probes))
                         svtv-fsm-ins)
                   svtv-fsm-vals svtv-fsm-tests x.namemap)))
    (svtv-cycle-run-fsm-inputs cycle-ins x.cycle-phases))

  ///
  (defret len-of-<fn>
    (equal (len phase-envs)
           (b* (((svtv-spec x)))
             (* (len x.cycle-phases)
                (len (svtv-probealist-outvars x.probes)))))))

(define svtv-spec-phase-outs->pipe-out ((x svtv-spec-p)
                                        (phase-outs svex-envlist-p))
  :returns (pipe-out svex-env-p)
  :guard (svtv-cyclephaselist-has-outputs-captured (svtv-spec->cycle-phases x))
  (b* (((svtv-spec x))
       (cycle-outs (svex-envlist-phase-outputs-extract-cycle-outputs
                    x.cycle-phases phase-outs))
       (svtv-fsm-outs (svtv-name-lhs-map-eval-list x.namemap cycle-outs)))
    (svtv-probealist-extract x.probes svtv-fsm-outs))
  ///

  (defret keys-of-<fn>
    (equal (alist-keys pipe-out)
           (alist-keys (svtv-spec->probes x)))))

(define svtv-spec-run ((x svtv-spec-p)
                       (pipe-env svex-env-p)
                       &key
                       (base-ins svex-envlist-p)
                       (initst svex-env-p))
  :parents (svtv-spec)
  :short "Run an @(see svtv-spec) object and return its outputs"
  :returns (pipe-out svex-env-p)
  :guard (and (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm x)))))
              (equal (svex-alist-keys (svtv-spec->initst-alist x))
                     (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm x))))
              (svtv-cyclephaselist-has-outputs-captured (svtv-spec->cycle-phases x)))
  (b* (((svtv-spec x))
       (phase-ins (svtv-spec-pipe-env->phase-envs x pipe-env))
       (full-ins (svex-envlist-x-override phase-ins base-ins))
       (full-initst (svex-env-x-override (svex-alist-eval x.initst-alist pipe-env) initst))
       (phase-outs (mbe :logic (base-fsm-eval full-ins full-initst x.fsm)
                        :exec (base-fsm-eval full-ins (svex-env-extract (svex-alist-keys (base-fsm->nextstate x.fsm)) full-initst)
                                             x.fsm))))
    (svtv-spec-phase-outs->pipe-out x phase-outs))
  ///
  (defret keys-of-<fn>
    (equal (alist-keys pipe-out)
           (alist-keys (svtv-spec->probes x)))))








(define svtv-spec-pipe-env->cycle-envs ((x svtv-spec-p)
                                        (pipe-env svex-env-p))
  :returns (cycle-envs svex-envlist-p)
  (b* (((svtv-spec x))
       (svtv-fsm-ins (svex-alistlist-eval x.in-alists pipe-env))
       (svtv-fsm-tests (svex-alistlist-eval x.override-test-alists pipe-env))
       (svtv-fsm-vals (svex-alistlist-eval x.override-val-alists pipe-env)))
    (svtv-fsm-to-base-fsm-inputs
     (take (len (svtv-probealist-outvars x.probes))
           svtv-fsm-ins)
     svtv-fsm-vals svtv-fsm-tests x.namemap))
  ///

  (defret len-of-<fn>
    (b* (((svtv-spec x)))
      (equal (len cycle-envs)
             (len (svtv-probealist-outvars x.probes)))))
  
  (defretd svtv-spec-pipe-env->phase-envs-in-terms-of-cycle-envs
    (equal (svtv-spec-pipe-env->phase-envs x pipe-env)
           (svtv-cycle-run-fsm-inputs cycle-envs (svtv-spec->cycle-phases x)))
    :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->phase-envs)))))


(define svtv-spec-cycle-outs->pipe-out ((x svtv-spec-p) (cycle-outs svex-envlist-p))
  :returns (pipe-out svex-env-p)
  (b* (((svtv-spec x))
       (svtv-fsm-outs (svtv-name-lhs-map-eval-list x.namemap cycle-outs)))
    (svtv-probealist-extract x.probes svtv-fsm-outs))
  ///
  (defret keys-of-<fn>
    (equal (alist-keys pipe-out)
           (alist-keys (svtv-spec->probes x))))

  (defthmd svtv-spec-phase-outs->pipe-out-in-terms-of-cycle-outs
    (equal (svtv-spec-phase-outs->pipe-out x phase-outs)
           (svtv-spec-cycle-outs->pipe-out
            x (svex-envlist-phase-outputs-extract-cycle-outputs
               (svtv-spec->cycle-phases x) phase-outs)))
    :hints(("Goal" :in-theory (enable svtv-spec-phase-outs->pipe-out)))))


(local (defthm svex-envlist-x-override-of-append
         (implies (equal (len x1) (len y1))
                  (equal (svex-envlist-x-override (append x1 x2) (append y1 y2))
                         (append (svex-envlist-x-override x1 y1) (svex-envlist-x-override x2 y2))))
         :hints(("Goal" :in-theory (enable svex-envlist-x-override)))))

(local (defthm svex-envlists-equivalent-of-append
         (implies (equal (len x1) (len y1))
                  (equal (svex-envlists-equivalent (append x1 x2) (append y1 y2))
                         (and (svex-envlists-equivalent x1 y1)
                              (svex-envlists-equivalent x2 y2))))
         :hints(("Goal" :in-theory (enable svex-envlists-equivalent-redef
                                           svex-envlist-x-override)
                 :induct (svex-envlist-x-override x1 y1)))))


(defthm svex-env-x-override-same
  (svex-envs-equivalent (svex-env-x-override a a)
                        a)
  :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

(defthm svex-env-x-override-of-append-same
  (svex-envs-equivalent (svex-env-x-override (append a b) (append a c))
                        (append a (svex-env-x-override b c)))
  :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

(defthm svex-envlist-x-override-of-cycle-step-fsm-inputs
  (svex-envs-equivalent (svex-env-x-override (svtv-cycle-step-fsm-inputs pipe-cycle-ins cycle-phase)
                                             (svtv-cycle-step-fsm-inputs orig-cycle-ins cycle-phase))
                        (svtv-cycle-step-fsm-inputs (svex-env-x-override pipe-cycle-ins orig-cycle-ins) cycle-phase))
  :hints(("Goal" :in-theory (enable svtv-cycle-step-fsm-inputs svex-envlist-x-override svex-envlists-equivalent-redef))))

(defthm svex-envlist-x-override-of-cycle-fsm-inputs
  (svex-envlists-equivalent (svex-envlist-x-override (svtv-cycle-fsm-inputs pipe-cycle-ins cycle-phases)
                                                     (svtv-cycle-fsm-inputs orig-cycle-ins cycle-phases))
                            (svtv-cycle-fsm-inputs (svex-env-x-override pipe-cycle-ins orig-cycle-ins) cycle-phases))
  :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs svex-envlist-x-override svex-envlists-equivalent-redef))))

(defthm svex-envlist-x-override-of-cycle-run-fsm-inputs
  (svex-envlists-equivalent (svex-envlist-x-override (svtv-cycle-run-fsm-inputs pipe-cycle-ins cycle-phases)
                                                     (svtv-cycle-run-fsm-inputs orig-cycle-ins cycle-phases))
                            (svtv-cycle-run-fsm-inputs (svex-envlist-x-override pipe-cycle-ins orig-cycle-ins) cycle-phases))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs svex-envlist-x-override)
          :induct t
          :do-not-induct t)))


(encapsulate nil
  (local (include-book "arithmetic/top" :dir :system))
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

  (local (defthm outputs-captured-implies-consp
           (implies (svtv-cyclephaselist-has-outputs-captured cycle-phases)
                    (consp cycle-phases))
           :rule-classes :forward-chaining))
  
  (defthm base-fsm-eval-of-base-fsm-to-cycle
    (implies (and (svtv-cyclephaselist-has-outputs-captured cycle-phases))
             (equal (base-fsm-eval ins initst (base-fsm-to-cycle cycle-phases x simp))
                    (svex-envlist-phase-outputs-extract-cycle-outputs
                     cycle-phases
                     (base-fsm-eval
                      (svtv-cycle-run-fsm-inputs ins cycle-phases)
                      initst x))))
    :hints ((acl2::equal-by-nths-hint)
            '(:in-theory (enable mod)))))

(define svtv-spec->cycle-fsm ((x svtv-spec-p))
  :guard (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm x)))))
  :returns (cycle base-fsm-p)
  (b* (((svtv-spec x)))
    (base-fsm-to-cycle x.cycle-phases x.fsm nil))
  ///
  (defthmd svtv-spec-run-in-terms-of-cycle-fsm
    (implies (svtv-cyclephaselist-has-outputs-captured (svtv-spec->cycle-phases x))
             (equal (svtv-spec-run x pipe-env :base-ins (svtv-cycle-run-fsm-inputs cycle-base-ins
                                                                                   (svtv-spec->cycle-phases x))
                                   :initst initst)
                    (b* ((cycle-envs-from-pipe (svtv-spec-pipe-env->cycle-envs x pipe-env))
                         (cycle-envs-full (svex-envlist-x-override cycle-envs-from-pipe cycle-base-ins))
                         (initst-from-pipe (svex-alist-eval (svtv-spec->initst-alist x) pipe-env))
                         (initst-full (svex-env-x-override initst-from-pipe initst))
                         (cycle-outs (base-fsm-eval cycle-envs-full initst-full (svtv-spec->cycle-fsm x))))
                      (svtv-spec-cycle-outs->pipe-out x cycle-outs))))
    :hints(("Goal" :in-theory (enable svtv-spec-run
                                      svtv-spec-pipe-env->phase-envs-in-terms-of-cycle-envs svtv-spec-phase-outs->pipe-out-in-terms-of-cycle-outs))))

  (defthm nextstate-keys-of-svtv-spec->cycle-fsm
    (equal (svex-alist-keys (base-fsm->nextstate (svtv-spec->cycle-fsm x)))
           (svex-alist-keys (base-fsm->nextstate (svtv-spec->fsm x))))))






