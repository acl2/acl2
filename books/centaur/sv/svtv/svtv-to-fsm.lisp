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

(include-book "../svex/override-transparency-and-ovmonotonicity")
(include-book "svtv-to-fsm-defs")
(include-book "override-envlist-defs")
(include-book "fsm-override-transparency")
(include-book "override-thm-common")
(local (include-book "svtv-spec-override-transparency"))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/misc/hons-sets" :dir :system))
(local (include-book "std/util/defredundant" :dir :system))

(local (include-book "clause-processors/find-subterms" :dir :system))

(local (std::add-default-post-define-hook :fix))

#|

This file works out a logical connection between SVTVs (i.e. pipelines) and
their underlying FSMs, so that theorems about FSMs can be derived from theorems
about SVTVs and vice versa, in such a way that the theorems about FSMs are
appropriate for reasoning, composition, etc.

An SVTV run is the same as an SVTV-spec run.  Inputs for the phase FSM are
derived from inputs for the SVTV using svtv-spec-pipe-env->phase-envs, which is
basically a nesting of three steps.

 - evaluate the input/override-test/override-val alistlists under the SVTV
input (pipe-env), getting a cyclewise list of input/override-test/override-val
envs each in terms of the namemap names

 - svtv-fsm-to-fsm-inputs on those envlists, resulting in a cyclewise list of
combined envs in terms of the FSM variables

 - svtv-cycle-run-fsm-inputs on that envlist, resulting in a phasewise list of
combined envs in terms of the FSM variables.

The initial state for the phase FSM is also derived from the pipe env, just by evaluating the initst-alist.

Portions of the inputs and initial state that are still X can then be
overridden with values by the base-ins and initst envs (except we assume that
no override tests are bound in the base-ins).  This ensures that the final
inputs to fsm-eval are latticewise greater than or equal the ones strictly
derived from the pipeline env, and the same on override-tests.

The phase FSM is evaluated on the resulting envlist/initst using fsm-eval.
This produces a list of phasewise output envs.

The output envs are translated to an SVTV output alist using
svtv-spec-phase-outs->pipe-out, which is three steps: the cycle outputs are
extracted from the phase outputs by dropping non-sampled
phases (svex-envlist-phase-outputs-extract-cycle-outputs), the FSM-named
outputs are translated to namemap-named outputs by evaluating the namemap under
the output envs, then the SVTV outputs are extracted from this using
svtv-probealist-extract.

We want to allow reasoning both at the phase- and cycle-FSM levels, so we'll
separate out the cycle processing from these steps and gather the rest into two
functions (aside from x-overriding): pipe-env->cycle-fsm-envs followed by
svtv-cycle-run-fsm-inputs, and on the output side
svtv-envlist-phase-outputs-extract-cycle-outputs followed by
cycle-fsm-outputs->pipe-outputs (names TBD).

We want to be able to reason in two directions, though one is more important
than the other.

Most importantly, we want to be able, given some theorems proved about
an SVTV, to prove some similar theorems about its underlying FSM, that we can then compose
together.  For example, showing an inductive invariant is preserved by running
a cycle in an SVTV, and using this to show that this property is indeed
invariant on the FSM.

Less important but still desirable is to be able to map back the other way:
take a theorem proved about an FSM run and show that a similar property holds
of an SVTV run. This is less important because SVTV properties are less
expressive than FSM properties, so proving SVTV properties from FSM properties
is mostly desirable just from an aesthetic standpoint of making it easier to
understand the properties.

Note. Deriving FSM properties from pipeline properties is a first step,
following which is adding proof machinery for reasoning about/composing FSM
properties. For the former, we just need to be able to translate pipeline
properties to FSM properties, which doesn't require too much in the way of
temporal logic -- we just want to express the input constraints implicit in the
SVTV property as a conjunction of simple statements about variables bound in
fixed phases of the FSM inputs, and (often though maybe not always) translate
overrides to constraints about outputs where the FSM inputs have no
overrides. (Note this can be done with existing machinery as long as all
overrides come in override triples at the SVTV level, but we may want to add
machinery to do it strictly at the FSM level so that SVTVs don't need to be
burdened with unnecessary outputs and conditional overrides in cases where
signals are intended to always be overridden.)
Later when we want to compose properties about the FSM we'll want to have more
of a temporal logic so as to be able to easily express, e.g.,
"after holding reset 4 cycles, then waiting 2 without any operations issued,
then waiting N cycles with well-formed operations perhaps being issued, running
OPCODE on DATA (one cycle later) produces RESULT (two cycles later)."



To prove an FSM theorem given an SVTV theorem, we need to instantiate the
SVTV(-spec) theorem in such a way that we can show the run of the FSM inside
the SVTV-spec run is the same as the run of the FSM in our target theorem.
Svtv-spec-run takes inputs x (the svtv-spec), pipe-env, base-ins, and initst.
Suppose our FSM theorem is about (fsm-eval envs initst fsm) -- we then
instantiate this theorem with:
 - pipe-env set to (lhprobe-map-eval (svtv-spec-fsm-bindings x) envs)
 - base-ins set to (svex-envlist-remove-override envs :test)
 - initst set to the initst for our fsm run.

Additionally we assume (lhprobe-constraint-eval (svtv-spec-fsm-constraints x)
envs).  We need this if SVTV sets certain signals to constants or to the same
variables as other inputs; this assumes that these signals are constant
(such as when the SVTV assigns the input to a constant) or the same (such as
when the SVTV uses the same input variable for multiple signals or for signals
in different times) in our FSM envs.

This sort of assumption suffices to prove essentially the same theorem about
the FSM as was proved about the SVTV-spec.  Under the lhprobe-constraint-eval
assumption, we can show that the svtv-spec-run with the inputs set as above
produces the same results as those of the FSM


 The input assumptions for an SVTV theorem consist of the implicit
assumptions of the SVTV (that is, bindings of namemap signals to constant
values) and theorem hypotheses about the values bound to SVTV input variables.
To accommodate both, we will have a function that extracts the value of a
namemap name at a given cycle from the cycle FSM inputs.  This is in a sense
easier than deriving the FSM inputs from the namemap + pipe env, as we do for
svtv-spec-run, because it just requires evaluating the namemap, not inverting
it.  We just need to do the proof work (or find it among the override
machinery) to show that it works.  For constant bindings, we will add
hypotheses saying the extraction equals the constant value, and for variable
bindings bind the extractions to those variables so that we can drop in the
hyps of the SVTV theorem.  As a later optimization we may want to consolidate
the constant-binding hyps into a data object so they don't grow too numerous
and clutter things up -- this may be part of a larger effort to establish a
temporal logic usable for reasoning.





Suppose we have a generalized theorem about an svtv-spec.  I.e., the main
variable is an input environment and there are various hyps about its bindings.

To be able to use that theorem to prove one about the FSM, we need to provide an env which
 1) satisfies the hyps and
 2) produces FSM inputs that are equivalent to the ones in our theorem.

Suppose we have a function (cycle-envs->pipe-env spec envs) which takes the
list of cycle inputs and the svtv-spec object and produces a pipe-env. For 1),
we need to reduce lookups in the resulting pipe-env to lookups in the cycle
inputs, and we need to have adequate hypotheses about the cycle inputs to imply
the hyps instantiated theorem about the svtv-spec's pipe-inputs.  For 2), we
need to know that svtv-spec-pipe-env->cycle-envs maps the pipe env back to
something compatible with the cycle inputs.  Defining "compatible" here is a
little complicated.  First, we can't expect svtv-spec-pipe-env->cycle-envs to
map any pipe env to an exact cycle inputs -- the pipe env doesn't contain
enough information for that.  Instead, svtv-spec-run allows an additional input
base-ins, which can override Xes from the pipe-derived inputs using
svex-envlist-x-override.  We can supply our original cycle inputs as the
base-ins, so that we only have to show that the pipe-derived cycle inputs are
<<= the originals*.  A few complications here:

 - In svtv-spec-run, the base-ins are applied to the phase-ins, not the
cycle-ins; we can solve this by mapping our cycle-ins to phase-ins using existing
function svtv-spec-cycle-run-fsm-inputs (adding off cycles with only the clock
bound) and show that
 (svex-envlist-x-override (svtv-cycle-run-fsm-inputs pipe-cycle-ins cycle-phases)
                          (svtv-cycle-run-fsm-inputs orig-cycle-ins cycle-phases))
is equivalent to
 (svtv-spec-cycle-run-fsm-inputs (svex-envlist-x-override pipe-cycle-ins orig-cycle-ins) cycle-phases)
(DONE)

 - SVTV-spec generalized thms currently assume that base-ins binds only
non-override variables.  We should change this to allow override-value
variables as well (DONE).  But we can't allow override-test variables because they
aren't monotonic.  We therefore need to filter override-test variables out of
the inputs that we use as the base-ins, and assume that the only overrides set
in the cycle-ins are the ones that can be set by the SVTV.

Subtasks:

 - fix svtv-spec generalized thms so that they allow override-value variables
in base-ins (done).

 - define the consistency condition for fsm inputs: equal on override-test
variables, >>= than the pipe-derived envs on others.  It would be convenient if
override-test variables only had to match 4vec-1masks.  Hopefully we can show
that when the FSM is override-transparent on a set of keys, the override-test
vars of those keys are only sensitive to 4vec-1mask.  Fortunately, this is
actually already done: overridekeys-envlists-ok, which says all variables in
all envs have to satisfy svar-overridekeys-envs-ok.  Conveniently, for override
test variables in the overridekeys, we only have to satisfy
4vec-override-mux-<<= and 4vec-muxtest-subsetp conditions, which only care
about 1mask; other params have to be equal, and everything else has to be <<=.





The main theorem we're going to use is
fsm-eval-with-conservative-fsm-when-overridekeys-envlists-ok.

This requires our FSM to be overridekey-transparent wrt the overridekeys.  This
is proven during def-svtv-refinement but we need to export the property.  We might
allow the property to be proven once and for all, shared among several SVTVs on
the same FSM, but this is tricky due to involving different sets of overridekeys.

(define svtv-spec-fsm-envs->bindings->fsm-envs ((x svtv-spec-p) (envs svex-envlist-p) (outs svex-envlist-p))
   (b* ((svtv-env (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings x) envs outs)))
     (svex-envlist-x-override (svtv-spec-pipe-env->cycle-envs x svtv-env)
                              (svex-envlist-remove-override envs :test))))

We want to show that the above function produces inst-envs satisfying
 (overridekeys-envlists-agree* overridekeys inst-envs envs outs)

given that the constraints are satisfied and the override-tests bound in envs
are muxtest-subsetp of the ones from the svtv-spec.

In particular this requires
 - non-overridekey variables in (svtv-spec-pipe-env->cycle-envs x svtv-env) are <<= those of envs.
 - Overrides tests set by (svtv-spec-pipe-env->cycle-envs x svtv-env) may or may not be set in envs.
   Any override test set in envs must be set in inst-envs.
   - For an override test set in both, the override values must match
   - For an override test set in inst-envs and not envs, the override value set in inst-envs must match the output.


|#





;; (defflexsum svar/4vec
;;   (:4vec
;;    :cond (if (consp x)
;;              (integerp (car x))
;;            (integerp x))
;;    :fields ((val :type 4vec-p :acc-body x))
;;    :ctor-body val)
;;   (:svar
;;    :cond t
;;    :fields ((var :type svar-p :acc-body x))
;;    :ctor-body var)
;;   :prepwork ((local (defthm svar-not-4vec-p
;;                       (implies (svar-p x) (not (4vec-p x)))
;;                       :hints(("Goal" :in-theory (enable svar-p 4vec-p)))))
;;              (local (defthm 4vec-not-svar-p
;;                       (implies (4vec-p x) (not (svar-p x)))))
;;              (local (defthm integerp-car-when-svar-p
;;                       (implies (svar-p x)
;;                                (not (integerp (car x))))
;;                       :hints(("Goal" :in-theory (enable svar-p)))))
;;              (local (defthm integerp-car-of-4vec
;;                       (implies (and (4vec-p x)
;;                                     (consp x))
;;                                (integerp (car x)))
;;                       :hints(("Goal" :in-theory (enable 4vec-p)))))))

(defxdoc svtv-to-fsm
  :parents (svtv)
  :short "Umbrella topic about proving FSM properties from SVTV properties")

(local (xdoc::set-default-parents svtv-to-fsm))



;; (define lhprobe-eval-signx ((x lhprobe-p)
;;                       (envs svex-envlist-p))
;;   :parents (lhprobe)
;;   :short "Evaluator for an @(see lhprobe) with respect to an envlist giving the values of signals over time."
;;   :returns (val 4vec-p)
;;   (b* (((lhprobe x))
;;        (env (nth x.stage envs)))
;;     (lhs-eval-signx x.lhs env)))

(local (defthm nth-of-svex-envlist-fix-no-split
         (equal (nth n (svex-envlist-fix x))
                (svex-env-fix (nth n x)))
         :hints(("Goal" :in-theory (enable svex-envlist-fix)))))

; Matt K. mod: Avoid ACL2(p) error.
(acl2::set-waterfall-parallelism nil)

(local (defthm 4vec-bit?!-of-4vec-concat
         (equal (4vec-bit?! (4vec-concat n test1 test2)
                            (4vec-concat n then1 then2)
                            (4vec-concat n else1 else2))
                (4vec-concat n (4vec-bit?! test1 then1 else1)
                             (4vec-bit?! test2 then2 else2)))
         :hints (("goal" :in-theory (enable 4vec-concat 4vec-bit?! 4vec-bitmux 4vec-1mask))
                 (bitops::logbitp-reasoning))))

(local (defthm 4vec-bit?!-of-4vec-rsh
         (equal (4vec-bit?! (4vec-rsh n test)
                            (4vec-rsh n then)
                            (4vec-rsh n else))
                (4vec-rsh n (4vec-bit?! test then else)))
         :hints (("goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-bit?! 4vec-bitmux 4vec-1mask))
                 (bitops::logbitp-reasoning))))

(local (defthm 4vec-bit?!-of-4vec-sign-ext
         (equal (4vec-bit?! (4vec-sign-ext n test)
                            (4vec-sign-ext n then)
                            (4vec-sign-ext n else))
                (4vec-sign-ext n (4vec-bit?! test then else)))
         :hints (("goal" :in-theory (enable 4vec-sign-ext 4vec-shift-core 4vec-bit?! 4vec-bitmux 4vec-1mask))
                 (bitops::logbitp-reasoning))))



(defsection lhs-overridemux-eval-signx
  (local (in-theory (enable lhs-overridemux-eval-signx)))
  (defthm lhs-overridemux-eval-signx-when-overridetype
    (implies (svarlist-override-p (lhs-vars x) type)
             (equal (lhs-overridemux-eval-signx x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhs-eval-signx (lhs-change-override x :test) env)
                                    (lhs-eval-signx x env)
                                    (lhs-eval-signx (lhs-change-override x nil) out))
                      (lhs-eval-signx x env))))
    :hints(("Goal" :in-theory (e/d (lhs-eval-signx lhatom-overridemux-eval
                                      lhs-vars lhatom-vars
                                      lhs-change-override
                                      lhatom-change-override
                                      svarlist-override-p
                                      lhatom-eval-zero
                                      svar-override-p-when-other)
                                   (svar-overridetype-equiv))))
    :otf-flg t)

  
  (defthm lhs-overridemux-eval-signx-split-on-var-overridetype
    (implies (and (syntaxp (quotep x))
                  (equal vars (lhs-vars x))
                  (bind-free (and (quotep vars)
                                  (let ((vars (unquote vars)))
                                    (if (consp vars)
                                        (let ((var (car vars)))
                                          (and (svar-override-okp var)
                                               `((type . ',(cond ((svar-override-p var :test) :test)
                                                                 ((svar-override-p var :val) :val)
                                                                 (t nil))))))
                                      '((type . 'nil)))))
                             (type))
                  (svarlist-override-p vars type))
             (equal (lhs-overridemux-eval-signx x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhs-eval-signx (lhs-change-override x :test) env)
                                    (lhs-eval-signx x env)
                                    (lhs-eval-signx (lhs-change-override x nil) out))
                      (lhs-eval-signx x env)))))

  (defthm lhs-overridemux-eval-signx-of-lhs-change-override
    (equal (lhs-overridemux-eval-signx (lhs-change-override x type) env out)
           (if (svar-overridetype-equiv type :val)
               (4vec-bit?! (lhs-eval-signx (lhs-change-override x :test) env)
                           (lhs-eval-signx (lhs-change-override x type) env)
                           (lhs-eval-signx (lhs-change-override x nil) out))
             (lhs-eval-signx (lhs-change-override x type) env)))
    :hints (("goal" :use ((:instance lhs-overridemux-eval-signx-split-on-var-overridetype
                           (vars (lhs-vars (lhs-change-override x type)))
                           (x (lhs-change-override x type))))))))

(defsection lhs-overridemux-eval-zero
  (local (in-theory (enable lhs-overridemux-eval-zero)))

  (defthm lhs-overridemux-eval-zero-when-overridetype
    (implies (svarlist-override-p (lhs-vars x) type)
             (equal (lhs-overridemux-eval-zero x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhs-eval-zx (lhs-change-override x :test) env)
                                    (lhs-eval-zx x env)
                                    (lhs-eval-zx (lhs-change-override x nil) out))
                      (lhs-eval-zx x env))))
    :hints(("Goal" :in-theory (e/d (lhs-eval-zx lhatom-overridemux-eval
                                      lhs-vars lhatom-vars
                                      lhs-change-override
                                      lhatom-change-override
                                      svarlist-override-p
                                      lhatom-eval-zero
                                      svar-override-p-when-other)
                                   (svar-overridetype-equiv))))
    :otf-flg t)

  (defthm lhs-overridemux-eval-zero-split-on-var-overridetype
    (implies (and (syntaxp (quotep x))
                  (equal vars (lhs-vars x))
                  (bind-free (and (quotep vars)
                                  (let ((vars (unquote vars)))
                                    (if (consp vars)
                                        (let ((var (car vars)))
                                          (and (svar-override-okp var)
                                               `((type . ',(cond ((svar-override-p var :test) :test)
                                                                 ((svar-override-p var :val) :val)
                                                                 (t nil))))))
                                      '((type . 'nil)))))
                             (type))
                  (svarlist-override-p vars type))
             (equal (lhs-overridemux-eval-zero x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhs-eval-zx (lhs-change-override x :test) env)
                                    (lhs-eval-zx x env)
                                    (lhs-eval-zx (lhs-change-override x nil) out))
                      (lhs-eval-zx x env)))))
  
  (defthm lhs-overridemux-eval-zero-of-lhs-change-override
    (equal (lhs-overridemux-eval-zero (lhs-change-override x type) env out)
           (if (svar-overridetype-equiv type :val)
               (4vec-bit?! (lhs-eval-zx (lhs-change-override x :test) env)
                           (lhs-eval-zx (lhs-change-override x type) env)
                           (lhs-eval-zx (lhs-change-override x nil) out))
             (lhs-eval-zx (lhs-change-override x type) env)))
    :hints (("goal" :use ((:instance lhs-overridemux-eval-zero-split-on-var-overridetype
                           (vars (lhs-vars (lhs-change-override x type)))
                           (x (lhs-change-override x type))))))))

(defsection lhprobe-overridemux-eval
  (local (in-theory (enable lhprobe-overridemux-eval)))
  (defthm lhprobe-overridemux-eval-when-overridetype
    (implies (svarlist-override-p (lhprobe-vars x) type)
             (equal (lhprobe-overridemux-eval x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhprobe-eval (lhprobe-change-override x :test) env)
                                    (lhprobe-eval x env)
                                    (lhprobe-eval (lhprobe-change-override x nil) out))
                      (lhprobe-eval x env))))
    :hints(("Goal" :use ((:instance lhs-overridemux-eval-zero-split-on-var-overridetype
                          (x (lhprobe->lhs x))
                          (vars (lhs-vars (lhprobe->lhs x)))
                          (env (nth (lhprobe->stage x) env))
                          (out (nth (lhprobe->stage x) out)))
                         (:instance lhs-overridemux-eval-signx-split-on-var-overridetype
                          (x (lhprobe->lhs x))
                          (vars (lhs-vars (lhprobe->lhs x)))
                          (env (nth (lhprobe->stage x) env))
                          (out (nth (lhprobe->stage x) out))))
            :in-theory (enable lhprobe-change-override
                               lhprobe-eval
                               lhprobe-vars)))
    :otf-flg t)

  (defthm lhprobe-overridemux-eval-split-on-var-overridetype
    (implies (and (syntaxp (quotep x))
                  (equal vars (lhprobe-vars x))
                  (bind-free (and (quotep vars)
                                  (let ((vars (unquote vars)))
                                    (if (consp vars)
                                        (let ((var (car vars)))
                                          (and (svar-override-okp var)
                                               `((type . ',(cond ((svar-override-p var :test) :test)
                                                                 ((svar-override-p var :val) :val)
                                                                 (t nil))))))
                                      '((type . 'nil)))))
                             (type))
                  (svarlist-override-p vars type))
             (equal (lhprobe-overridemux-eval x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhprobe-eval (lhprobe-change-override x :test) env)
                                    (lhprobe-eval x env)
                                    (lhprobe-eval (lhprobe-change-override x nil) out))
                      (lhprobe-eval x env))))
    :hints(("Goal" :in-theory (disable lhprobe-overridemux-eval)))))


(defsection lhprobe/4vec-overridemux-eval
  (local (in-theory (enable lhprobe/4vec-overridemux-eval)))
  (local (defthm 4vec-bit?!-self
           (equal (4vec-bit?! y x x)
                  (4vec-fix x))
           :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))
                  (bitops::logbitp-reasoning))))

  (defthm lhprobe/4vec-overridemux-eval-when-overridetype
    (implies (svarlist-override-p (lhprobe/4vec-vars x) type)
             (equal (lhprobe/4vec-overridemux-eval x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhprobe/4vec-eval (lhprobe/4vec-change-override x :test) env)
                                    (lhprobe/4vec-eval x env)
                                    (lhprobe/4vec-eval (lhprobe/4vec-change-override x nil) out))
                      (lhprobe/4vec-eval x env))))
    :hints(("Goal" :use ((:instance lhprobe-overridemux-eval-split-on-var-overridetype))
            :in-theory (enable lhprobe/4vec-change-override
                               lhprobe/4vec-eval
                               lhprobe/4vec-vars)))
    :otf-flg t)

  (defthm lhprobe/4vec-overridemux-eval-split-on-var-overridetype
    (implies (and (syntaxp (quotep x))
                  (equal vars (lhprobe/4vec-vars x))
                  (bind-free (and (quotep vars)
                                  (let ((vars (unquote vars)))
                                    (if (consp vars)
                                        (let ((var (car vars)))
                                          (and (svar-override-okp var)
                                               `((type . ',(cond ((svar-override-p var :test) :test)
                                                                 ((svar-override-p var :val) :val)
                                                                 (t nil))))))
                                      '((type . 'nil)))))
                             (type))
                  (svarlist-override-p vars type))
             (equal (lhprobe/4vec-overridemux-eval x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhprobe/4vec-eval (lhprobe/4vec-change-override x :test) env)
                                    (lhprobe/4vec-eval x env)
                                    (lhprobe/4vec-eval (lhprobe/4vec-change-override x nil) out))
                      (lhprobe/4vec-eval x env))))
    :hints(("Goal" :in-theory (disable lhprobe/4vec-overridemux-eval)))))

(defsection lhprobe-map-overridemux-eval
  (local (in-theory (enable lhprobe-map-overridemux-eval)))
  (defthm lhprobe-map-overridemux-eval-when-overridetype
    (implies (and (svarlist-override-p (lhprobe-map-vars x) type)
                  (not (equal (svar-overridetype-fix type) :val)))
             (equal (lhprobe-map-overridemux-eval x env out)
                    (lhprobe-map-eval x env)))
    :hints(("Goal" :in-theory (enable lhprobe-overridemux-eval-when-overridetype
                                      lhprobe-map-vars
                                      lhprobe-map-eval)))))













(defsection svtv-spec-fsm-constraints-for-lhprobe
  (local (in-theory (enable svtv-spec-fsm-constraints-for-lhprobe)))
  (local (std::set-define-current-function svtv-spec-fsm-constraints-for-lhprobe))
  (defret constraints-eval-of-<fn>
    (equal (lhprobe-constraintlist-eval constraints envs)
           (equal (lhprobe-eval lhprobe envs)
                  (svar/4vec-eval binding (lhprobe-map-eval bindings envs))))
    :hints(("Goal" :in-theory (enable lhprobe-constraintlist-eval
                                      lhprobe-constraint-eval
                                      svar/4vec-eval
                                      lhprobe/4vec-eval))))

  (defret constraints-overridemux-eval-of-<fn>
    (equal (lhprobe-constraintlist-overridemux-eval constraints envs outs)
           (equal (lhprobe-overridemux-eval lhprobe envs outs)
                  (svar/4vec-eval binding (lhprobe-map-overridemux-eval bindings envs outs))))
    :hints(("Goal" :in-theory (enable lhprobe-constraintlist-overridemux-eval
                                      lhprobe-constraint-overridemux-eval
                                      svar/4vec-eval
                                      lhprobe/4vec-overridemux-eval
                                      lhprobe/4vec-eval))))

  (defret lhprobe-constraintlist-max-stage-of-<fn>
    (implies (and (<= (lhprobe->stage lhprobe) bound)
                  (<= (lhprobe-map-max-stage bindings) bound))
             (<= (lhprobe-constraintlist-max-stage constraints) bound))
    :hints(("Goal" :in-theory (enable lhprobe-constraintlist-max-stage
                                      lhprobe-constraint-max-stage)))))


;; (define svex-envs-ovtestsimilar ((x svex-env-p) (y svex-env-p))
;;   (ec-call (svex-envs-1mask-equiv (svex-env-filter-override x :test)
;;                                   (svex-env-filter-override y :test)))
;;   ///
;;   (defthm svex-envs-ovtestsimilar-implies
;;     (implies (and (svex-envs-ovtestsimilar x y)
;;                   (svar-override-p k :test))
;;              (4vec-1mask-equiv (svex-env-lookup k x)
;;                                (svex-env-lookup k y)))
;;     :hints (("goal" :use ((:instance svex-envs-1mask-equiv-necc
;;                            (x (svex-env-filter-override x :test))
;;                            (y (svex-env-filter-override y :test))))
;;              :in-theory (disable svex-envs-1mask-equiv-necc
;;                                  svex-envs-1mask-equiv-implies-4vec-1mask-equiv-svex-env-lookup-2))))

;;   (defequiv svex-envs-ovtestsimilar)

;;   (defrefinement svex-envs-similar svex-envs-ovtestsimilar))





(defsection svex-envs-ovtestsubsetp
  (defun-sk svex-envs-ovtestsubsetp (x y)
    (forall k
            (implies (svar-override-p k :test)
                     (4vec-muxtest-subsetp (svex-env-lookup k x)
                                           (svex-env-lookup k y))))
    :rewrite :direct)

  (in-theory (disable svex-envs-ovtestsubsetp))

  (defcong svex-envs-ovtestsimilar iff (svex-envs-ovtestsubsetp x y) 1
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'svex-envs-ovtestsubsetp clause))
                        (wit `(svex-envs-ovtestsubsetp-witness . ,(cdr lit)))
                        (other (if (eq (cadr lit) 'x) 'x-equiv 'x)))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtestsubsetp-necc
                            (k ,wit)
                            (x ,other))
                           (:instance svex-envs-ovtestsimilar-necc
                            (y x-equiv)
                            (k ,wit)))
                     :in-theory (disable svex-envs-ovtestsubsetp-necc))))))

  (defcong svex-envs-ovtestsimilar iff (svex-envs-ovtestsubsetp x y) 2
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'svex-envs-ovtestsubsetp clause))
                        (wit `(svex-envs-ovtestsubsetp-witness . ,(cdr lit)))
                        (other (if (eq (caddr lit) 'y) 'y-equiv 'y)))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtestsubsetp-necc
                            (k ,wit)
                            (y ,other))
                           (:instance svex-envs-ovtestsimilar-necc
                            (x y-equiv)
                            (k ,wit)))
                     :in-theory (disable svex-envs-ovtestsubsetp-necc)))))))


(define svex-envlists-ovtestsubsetp ((x svex-envlist-p) (y svex-envlist-p))
  (if (Atom x)
      (atom y)
    (and (consp y)
         (ec-call (svex-envs-ovtestsubsetp (car x) (car y)))
         (svex-envlists-ovtestsubsetp (cdr x) (cdr y))))
  ///
  (defcong svex-envlists-ovtestsimilar iff (svex-envlists-ovtestsubsetp x y) 1
    :hints(("Goal" :in-theory (enable svex-envlists-ovtestsimilar))))
  (defcong svex-envlists-ovtestsimilar iff (svex-envlists-ovtestsubsetp x y) 2
    :hints(("Goal" :in-theory (enable svex-envlists-ovtestsimilar)))))


(defsection svex-envs-ovtests-ok
  (defun-sk svex-envs-ovtests-ok (x y overridekeys)
    (forall k
            (implies (svar-override-p k :test)
                     (and (implies (svarlist-member-nonoverride k overridekeys)
                                   (4vec-muxtest-subsetp (svex-env-lookup k x)
                                                         (svex-env-lookup k y)))
                          (implies (not (svarlist-member-nonoverride k overridekeys))
                                   (4vec-1mask-equiv (svex-env-lookup k x)
                                                     (svex-env-lookup k y))))))
    :rewrite :direct)

  (in-theory (disable svex-envs-ovtests-ok))

  (defcong svex-envs-ovtestsimilar iff (svex-envs-ovtests-ok x y overridekeys) 1
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'svex-envs-ovtests-ok clause))
                        (wit `(svex-envs-ovtests-ok-witness . ,(cdr lit)))
                        (other (if (eq (cadr lit) 'x) 'x-equiv 'x)))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtests-ok-necc
                            (k ,wit)
                            (x ,other))
                           (:instance svex-envs-ovtestsimilar-necc
                            (y x-equiv)
                            (k ,wit)))
                     :in-theory (disable svex-envs-ovtests-ok-necc))))))

  (defcong svex-envs-ovtestsimilar iff (svex-envs-ovtests-ok x y overridekeys) 2
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'svex-envs-ovtests-ok clause))
                        (wit `(svex-envs-ovtests-ok-witness . ,(cdr lit)))
                        (other (if (eq (caddr lit) 'y) 'y-equiv 'y)))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtests-ok-necc
                            (k ,wit)
                            (y ,other))
                           (:instance svex-envs-ovtestsimilar-necc
                            (x y-equiv)
                            (k ,wit)))
                     :in-theory (disable svex-envs-ovtests-ok-necc))))))

  (defcong svarlist-equiv iff (svex-envs-ovtests-ok x y overridekeys) 3
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'svex-envs-ovtests-ok clause))
                        (wit `(svex-envs-ovtests-ok-witness . ,(cdr lit)))
                        (other (if (eq (cadddr lit) 'overridekeys) 'overridekeys-equiv 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtests-ok-necc
                            (k ,wit)
                            (overridekeys ,other)))
                     :in-theory (disable svex-envs-ovtests-ok-necc))))))

  (defcong set-equiv iff (svex-envs-ovtests-ok x y overridekeys) 3
    :hints ((and stable-under-simplificationp
                 (let* ((lit (assoc 'svex-envs-ovtests-ok clause))
                        (wit `(svex-envs-ovtests-ok-witness . ,(cdr lit)))
                        (other (if (eq (cadddr lit) 'overridekeys) 'overridekeys-equiv 'overridekeys)))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtests-ok-necc
                            (k ,wit)
                            (overridekeys ,other)))
                     :in-theory (disable svex-envs-ovtests-ok-necc)))))))


(define svex-envlists-ovtests-ok ((x svex-envlist-p) (y svex-envlist-p) (overridekeys svarlist-p))
  (if (Atom x)
      (atom y)
    (and (consp y)
         (ec-call (svex-envs-ovtests-ok (car x) (car y) overridekeys))
         (svex-envlists-ovtests-ok (cdr x) (cdr y) overridekeys)))
  ///
  (defcong svex-envlists-ovtestsimilar iff (svex-envlists-ovtests-ok x y overridekeys) 1
    :hints(("Goal" :in-theory (enable svex-envlists-ovtestsimilar))))
  (defcong svex-envlists-ovtestsimilar iff (svex-envlists-ovtests-ok x y overridekeys) 2
    :hints(("Goal" :in-theory (enable svex-envlists-ovtestsimilar)))))



(local (local (include-book "svtv-spec-override-transparency")))

(local
 (define 4vec-override-mux-agrees-badbit ((impl-test 4vec-p)
                                          (impl-val 4vec-p)
                                          (spec-test 4vec-p)
                                          (spec-val 4vec-p)
                                          (spec-ref 4vec-p))
   :returns (badbit natp :rule-classes :type-prescription)
   (b* ((spec-mux (4vec-bit?! spec-test spec-val spec-ref)))
     (4vec-equiv-badbit (4vec-bit?! impl-test impl-val spec-mux)
                        spec-mux))
   ///
   (local (Defthm 4vec-bit-index-of-4vec-bit?!
            (equal (4vec-bit-index n (4vec-bit?! test then else))
                   (if (eql (4vec-bit-index n test) 1)
                       (4vec-bit-index n then)
                     (4vec-bit-index n else)))
            :hints(("Goal" :in-theory (enable 4vec-bit-index
                                              4vec-bit?! 4vec-bitmux 4vec-1mask b-ite)))))

   (defthmd 4vec-override-mux-agrees-implies-bit-index
     (implies (and (4vec-override-mux-agrees impl-test impl-val spec-test spec-val spec-ref)
                   (equal 1 (4vec-bit-index n impl-test)))
              (equal (4vec-bit-index n impl-val)
                     (if (eql (4vec-bit-index n spec-test) 1)
                         (4vec-bit-index n spec-val)
                       (4vec-bit-index n spec-ref))))
     :hints(("Goal" :in-theory (e/d (4vec-override-mux-agrees))
             :use ((:instance (:theorem (implies (equal x y)
                                                 (equal (4vec-bit-index n x)
                                                        (4vec-bit-index n y))))
                    (x (4vec-bit?! impl-test impl-val (4vec-bit?! spec-test spec-val spec-ref)))
                    (y (4vec-bit?! spec-test spec-val spec-ref)))))))

   (defretd 4vec-override-mux-agrees-when-badbit
     (implies (or (not (equal 1 (4vec-bit-index badbit impl-test)))
                  (equal (4vec-bit-index badbit impl-val)
                         (if (eql (4vec-bit-index badbit spec-test) 1)
                             (4vec-bit-index badbit spec-val)
                           (4vec-bit-index badbit spec-ref))))
              (4vec-override-mux-agrees impl-test impl-val spec-test spec-val spec-ref))
     :hints(("Goal" :in-theory (enable 4vec-override-mux-agrees
                                       4vec-equiv-when-badbit))))

   (defretd 4vec-override-mux-agrees-by-badbit
     (implies (acl2::rewriting-positive-literal `(4vec-override-mux-agrees ,impl-test ,impl-val ,spec-test ,spec-val ,spec-ref))
              (equal (4vec-override-mux-agrees impl-test impl-val spec-test spec-val spec-ref)
                     (or (not (equal 1 (4vec-bit-index badbit impl-test)))
                         (equal (4vec-bit-index badbit impl-val)
                                (if (eql (4vec-bit-index badbit spec-test) 1)
                                    (4vec-bit-index badbit spec-val)
                                  (4vec-bit-index badbit spec-ref))))))
     :hints(("Goal" :in-theory (e/d (4vec-override-mux-agrees-when-badbit
                                     4vec-override-mux-agrees-implies-bit-index)
                                    (<fn>)))))))


;; (define svtv-name-lhs-map-eval-signx ((x svtv-name-lhs-map-p)
;;                                     (env svex-env-p))
;;   :returns (res svex-env-p)
;;   (b* (((when (atom x)) nil)
;;        ((unless (mbt (and (consp (car x))
;;                           (svar-p (caar x)))))
;;         (svtv-name-lhs-map-eval-signx (cdr x) env)))
;;     (cons (Cons (caar x) (lhs-eval-signx (cdar x) env))
;;           (svtv-name-lhs-map-eval-signx (cdr x) env)))
;;   ///
;;   (defret svex-env-boundp-of-<fn>
;;     (iff (svex-env-boundp k res)
;;          (hons-assoc-equal (svar-fix k) (svtv-name-lhs-map-fix x)))
;;     :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
;;                                       svex-env-boundp-of-cons-split))))
;;   (defret svex-env-lookup-of-<fn>
;;     (equal (svex-env-lookup k res)
;;            (let ((pair (hons-assoc-equal (svar-fix k) (svtv-name-lhs-map-fix x))))
;;              (if pair (lhs-eval-signx (cdr pair) env) (4vec-x))))
;;     :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons-split
;;                                       svtv-name-lhs-map-fix))))

;;   (defthm alist-keys-of-svtv-name-lhs-map-eval-signx
;;            (equal (alist-keys (svtv-name-lhs-map-eval-signx x env))
;;                   (alist-keys (svtv-name-lhs-map-fix x)))
;;            :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
;;                                              svtv-name-lhs-map-eval-signx
;;                                              alist-keys))))

;;   (local (in-theory (enable svtv-name-lhs-map-fix))))



(local
 (defsection 4vec-bit-index-of-lhs-eval-signx
   (local (defthm 4vec-bit-index-of-4vec-concat
            (implies (natp w)
                     (equal (4vec-bit-index n (4vec-concat (2vec w) x y))
                            (if (< (nfix n) w)
                                (4vec-bit-index n x)
                              (4vec-bit-index (- (nfix n) w) y))))
            :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-concat)))))

   (local (defthm 4vec-bit-index-of-4vec-sign-ext
            (implies (posp w)
                     (equal (4vec-bit-index n (4vec-sign-ext (2vec w) x))
                            (if (< (nfix n) w)
                                (4vec-bit-index n x)
                              (4vec-bit-index (1- w) x))))
            :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-sign-ext)))))

   (local (defthm 4vec-bit-index-of-4vec-rsh
            (implies (natp sh)
                     (equal (4vec-bit-index n (4vec-rsh (2vec sh) x))
                            (4vec-bit-index (+ (nfix n) sh) x)))
            :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-rsh 4vec-shift-core)))))

   (local (defthm 4vec-bit-index-of-0
            (equal (4vec-bit-index n 0)
                   0)
            :hints(("Goal" :in-theory (enable 4vec-bit-index)))))
  
   (defthm 4vec-bit-index-of-lhs-eval-signx
     (equal (4vec-bit-index n (lhs-eval-signx x env))
            (if (< (nfix n) (lhs-width x))
                (lhbit-eval-zero (lhs-bitproj n x) env)
              (if (posp (lhs-width x))
                  (lhbit-eval-zero (lhs-bitproj (1- (lhs-width x)) x) env)
                0)))
     :hints(("Goal" :in-theory (enable lhs-eval-signx lhs-bitproj lhatom-bitproj lhatom-eval-zero
                                       lhs-width)
             :expand ((LHBIT-EVAL-ZERO '(:Z) ENV)
                      (:free (name idx) (lhbit-eval-zero (lhbit-var name idx) env)))
             :induct (lhs-bitproj n x))))))

(defthm lhs-width-of-lhs-change-override
  (equal (lhs-width (lhs-change-override x type))
         (lhs-width x))
  :hints(("Goal" :in-theory (enable lhs-width lhs-change-override))))

(defthm lhs-width-equal-0
  (equal (Equal (lhs-width x) 0)
         (atom x))
  :hints(("Goal" :in-theory (enable lhs-width))))

(defsection svtv-spec-fsm-constraints-for-alist
  (local (in-theory (enable svtv-spec-fsm-constraints-for-alist)))
  (local (std::set-define-current-function svtv-spec-fsm-constraints-for-alist))
  (local (include-book "std/alists/fast-alist-clean" :dir :system))
  (local (include-book "std/lists/sets" :dir :system))
  (local (include-book "std/alists/fal-extract" :dir :system))

  ;; (defretd constraints-eval-of-<fn>
  ;;   (implies (and (lhprobe-constraintlist-eval constraints envs)
  ;;                 ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
  ;;                 ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
  ;;                 (member-equal v (alist-keys (svtv-name-lhs-map-fix namemap)))
  ;;                 )
  ;;            (equal (svar/4vec-eval (cdr (hons-assoc-equal v (svar/4vec-alist-fix x)))
  ;;                                   (lhprobe-map-eval bindings envs))
  ;;                   (svex-env-lookup v
  ;;                                    (svtv-name-lhs-map-eval-signx
  ;;                                     (svtv-name-lhs-map-vals-change-override
  ;;                                      (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
  ;;                                                         (svtv-name-lhs-map-fix namemap))
  ;;                                      overridetype)
  ;;                                     (nth stage envs)))))
  ;;   :hints(("Goal" :in-theory (e/d (svtv-name-lhs-map-eval
  ;;                                   fal-extract
  ;;                                   alist-keys
  ;;                                   svar/4vec-alist-fix
  ;;                                   svar/4vec-alist-eval
  ;;                                   svtv-name-lhs-map-vals-change-override
  ;;                                   lhprobe-eval)
  ;;                                  ((:d <fn>)))
  ;;           :induct <call> :do-not-induct t
  ;;           :expand ((lhprobe-constraintlist-eval nil envs)
  ;;                    <call>))))

  (local (defthm hons-assoc-equal-of-svtv-name-lhs-map-vals-change-override-under-iff
           (iff (hons-assoc-equal v (svtv-name-lhs-map-vals-change-override x type))
                (hons-assoc-equal v (svtv-name-lhs-map-fix x)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-vals-change-override)))))

  ;; (equal (lhprobe-constraintlist-overridemux-eval constraints envs outs)
  ;;            (equal (lhprobe-overridemux-eval lhprobe envs outs)
  ;;                   (svar/4vec-eval binding (lhprobe-map-overridemux-eval bindings envs outs))))

  (defretd constraints-overridemux-eval-of-<fn>
    (implies (and (lhprobe-constraintlist-overridemux-eval constraints envs outs)
                  ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
                  ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
                  (member-equal v (alist-keys (svtv-name-lhs-map-fix namemap)))
                  (hons-assoc-equal v (svar/4vec-alist-fix x))
                  )
             (equal (svar/4vec-eval (cdr (hons-assoc-equal v (svar/4vec-alist-fix x)))
                                    (lhprobe-map-overridemux-eval bindings envs outs))
                    (lhprobe-overridemux-eval (make-lhprobe :lhs (lhs-change-override (cdr (hons-assoc-equal v (svtv-name-lhs-map-fix namemap))) overridetype)
                                                            :stage stage
                                                            :signedp (lhprobe-signedness-for-alist overridetype (cdr (hons-assoc-equal v (svar/4vec-alist-fix x)))))
                                              envs outs))
                    ;; (if (svar-overridetype-equiv overridetype :val)
                    ;;     (4vec-bit?!
                    ;;      (svex-env-lookup v
                    ;;                       (svtv-name-lhs-map-eval-signx
                    ;;                        (svtv-name-lhs-map-vals-change-override
                    ;;                         (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                    ;;                                            (svtv-name-lhs-map-fix namemap))
                    ;;                         :test)
                    ;;                        (nth stage envs)))
                    ;;      (svex-env-lookup v
                    ;;                       (svtv-name-lhs-map-eval-signx
                    ;;                        (svtv-name-lhs-map-vals-change-override
                    ;;                         (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                    ;;                                            (svtv-name-lhs-map-fix namemap))
                    ;;                         :val)
                    ;;                        (nth stage envs)))
                    ;;      (svex-env-lookup v
                    ;;                       (svtv-name-lhs-map-eval-signx
                    ;;                        (svtv-name-lhs-map-vals-change-override
                    ;;                         (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                    ;;                                            (svtv-name-lhs-map-fix namemap))
                    ;;                         nil)
                    ;;                        (nth stage outs))))
                    ;;   (svex-env-lookup v
                    ;;                    (svtv-name-lhs-map-eval-signx
                    ;;                     (svtv-name-lhs-map-vals-change-override
                    ;;                      (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                    ;;                                         (svtv-name-lhs-map-fix namemap))
                    ;;                      overridetype)
                    ;;                     (nth stage envs))))
                    )
    :hints(("Goal" :in-theory (e/d (;; svtv-name-lhs-map-eval-signx
                                    fal-extract
                                    alist-keys
                                    svar/4vec-alist-fix
                                    svar/4vec-alist-eval
                                    svtv-name-lhs-map-vals-change-override)
                                   ((:d <fn>)
                                    alist-keys
                                    svar-p-when-maybe-svar-p-p
                                    svar-overridetype-equiv
                                    fal-extract))
            :induct <call> :do-not-induct t
            :expand ((lhprobe-constraintlist-overridemux-eval nil envs outs)
                     (:free (lhs signedp) (lhprobe-overridemux-eval (lhprobe lhs stage signedp) envs outs))
                     (:free (overridetype) <call>)))))


  (local (defthm subsetp-equal-lhs-vars-of-svtv-name-lhs-map-lookup
           (implies (and (hons-assoc-equal key namemap)
                         (svar-p key))
                    (subsetp-equal (lhs-vars (cdr (hons-assoc-equal key namemap)))
                                   (svtv-name-lhs-map-vars namemap)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-vars alist-keys)))))

  (local (defthm subsetp-svtv-name-lhs-map-vars-of-fal-extract
           (subsetp-equal (svtv-name-lhs-map-vars (fal-extract keys (svtv-name-lhs-map-fix namemap)))
                          (svtv-name-lhs-map-vars namemap))
           :hints(("Goal" :in-theory (enable fal-extract svtv-name-lhs-map-vars)
                   :induct (len keys)))))

  (local (defthm svar-override-p-when-member-2
           (implies (and (member-equal (svar-fix v) x)
                         (svarlist-override-p x type))
                    (svar-override-p v type))
           :hints(("Goal" :in-theory (enable svarlist-fix svarlist-override-p)))))

  (local (defthm svarlist-override-p-when-subsetp
           (implies (and (svarlist-override-p x type)
                         (subsetp-equal (svarlist-fix y) (svarlist-fix x) ))
                    (svarlist-override-p y type))
           :hints(("Goal" :in-theory (enable svarlist-override-p svarlist-fix subsetp-equal)
                   :expand ((svarlist-fix y)
                            (svarlist-override-p y type))
                   :induct (svarlist-override-p y type)))))

  (local (defthm svarlist-override-p-svtv-name-lhs-map-vars-of-fal-extract
           (implies (svarlist-override-p (svtv-name-lhs-map-vars namemap) type)
                    (svarlist-override-p (svtv-name-lhs-map-vars (fal-extract keys (svtv-name-lhs-map-fix namemap))) type))
           :hints(("Goal" :in-theory (disable subsetp-svtv-name-lhs-map-vars-of-fal-extract)
                   :use subsetp-svtv-name-lhs-map-vars-of-fal-extract))))

  (local
   (defthm alist-keys-of-fast-alist-clean-under-set-equiv
     (set-equiv (alist-keys (fast-alist-clean x))
                (alist-keys x))
     :hints(("Goal" :in-theory (e/d (acl2::set-unequal-witness-rw
                                     acl2::alist-keys-member-hons-assoc-equal)
                                    (acl2::hons-assoc-equal-iff-member-alist-keys))))))


  (local (defthm hons-assoc-equal-of-svar-change-override-lhs-map-keys-change-override
           (implies (svarlist-override-p (alist-keys (svtv-name-lhs-map-fix map)) nil)
                    (equal (cdr (hons-assoc-equal (svar-change-override v type)
                                                  (svtv-name-lhs-map-keys-change-override map type)))
                           (cdr (hons-assoc-equal (svar-change-override v nil)
                                                  (svtv-name-lhs-map-fix map)))))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svtv-name-lhs-map-fix
                                             alist-keys
                                             svtv-name-lhs-map-keys-change-override
                                             equal-of-svar-change-override)))))

  (local (defthm hons-assoc-equal-of-lhs-map-keys-change-override
           (implies (and (syntaxp (not (equal type ''nil)))
                         (svarlist-override-p (alist-keys (svtv-name-lhs-map-fix map)) nil)
                         (svar-override-p v type)
                         (svar-p v))
                    (equal (cdr (hons-assoc-equal v
                                                  (svtv-name-lhs-map-keys-change-override map type)))
                           (cdr (hons-assoc-equal (svar-change-override v nil)
                                                  (svtv-name-lhs-map-fix map)))))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svtv-name-lhs-map-fix
                                             alist-keys
                                             svtv-name-lhs-map-keys-change-override
                                             equal-of-svar-change-override)))))

  (local (defthm svtv-name-lhs-map-keys-change-override-when-same
           (implies (svarlist-override-p (alist-keys (svtv-name-lhs-map-fix map)) type)
                    (equal (svtv-name-lhs-map-keys-change-override map type)
                           (svtv-name-lhs-map-fix map)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-keys-change-override
                                             alist-keys
                                             svarlist-override-p)))))

  (local (defret <fn>-correct-gen
           (implies (and (lhbit-case lhbit :var)
                         (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix x)))
                         (lhs-equiv (cdr (hons-assoc-equal (lhbit-var->name lhbit) y))
                                    (cdr (hons-assoc-equal (lhbit-var->name lhbit) x))))
                    (equal (lhs-bitproj (lhbit-var->idx lhbit)
                                        (cdr (hons-assoc-equal (lhbit-var->name lhbit) y)))
                           (lhbit-var var idx)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             alist-keys)))
           :fn svtv-name-lhs-map-var/idx-find))

  (local (defthm no-duplicate-keys-of-fal-extract
           (implies (no-duplicatesp-equal keys)
                    (no-duplicatesp-equal (alist-keys (fal-extract keys x))))
           :hints(("Goal" :in-theory (e/d (alist-keys fal-extract
                                                      acl2::alist-keys-member-hons-assoc-equal)
                                          (acl2::hons-assoc-equal-iff-member-alist-keys))))))

  (local (defthm alist-keys-of-svar/4vec-alist-eval
           (equal (alist-keys (svar/4vec-alist-eval x env))
                  (alist-keys (svar/4vec-alist-fix x)))
           :hints(("Goal" :in-theory (enable svar/4vec-alist-fix
                                             svar/4vec-alist-eval
                                             alist-keys)))))

  (local (defthm alist-keys-of-svtv-name-lhs-map-vals-change-override
           (equal (alist-keys (svtv-name-lhs-map-vals-change-override x type))
                  (alist-keys (svtv-name-lhs-map-fix x)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-vals-change-override
                                             alist-keys)))))

  (local (defthm alist-keys-of-fal-extract-when-subsetp
           (implies (subsetp-equal keys (alist-keys x))
                    (equal (alist-keys (fal-extract keys x))
                           (true-list-fix keys)))
           :hints(("Goal" :in-theory (enable fal-extract alist-keys)))))

  (local (defthm hons-assoc-equal-of-svtv-name-lhs-vals-change-override
           (equal (hons-assoc-equal v (svtv-name-lhs-map-vals-change-override map type))
                  (let ((look (hons-assoc-equal v (svtv-name-lhs-map-fix map))))
                    (and look (cons v (lhs-change-override (cdr look) type)))))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-vals-change-override)))))

  (local (defthm lhs-bitproj-of-lhs-change-override
           (equal (lhs-bitproj n (lhs-change-override lhs type))
                  (b* ((proj (lhs-bitproj n lhs)))
                    (lhbit-case proj
                      :z proj
                      :var (lhbit-var (svar-change-override proj.name type) proj.idx))))
           :hints(("Goal" :in-theory (enable lhs-bitproj lhs-change-override
                                             lhatom-bitproj
                                             lhatom-change-override)))))

  (local (defthm 4vec-bit-index-of-x
           (equal (4vec-bit-index n (4vec-x))
                  (4vec-1x))
           :hints(("Goal" :in-theory (enable 4vec-bit-index)))))

  (defret <fn>-lookup-lemma2
    (implies (lhbit-case lhbit :var)
             (hons-assoc-equal (lhbit-var->name lhbit)
                               (svtv-name-lhs-map-fix x)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix)))
    :fn svtv-name-lhs-map-var/idx-find)

  (local (defthm subsetp-alist-keys-fal-extract
           (subsetp-equal (alist-keys (fal-extract keys x)) (alist-keys x))
           :hints(("Goal" :in-theory (enable alist-keys fal-extract)))))

  (local
   (defret <fn>-lookup-lemma3
     (implies (and (lhbit-case lhbit :var)
                   (subsetp-equal (alist-keys (svtv-name-lhs-map-fix x)) keys))
              (member-equal (lhbit-var->name lhbit) keys))
     :hints(("Goal" :use (<fn>-lookup-lemma2)
             :in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                             (<fn>-lookup-lemma2
                              acl2::alist-keys-member-hons-assoc-equal
                              HONS-ASSOC-EQUAL-OF-SVTV-NAME-LHS-MAP-FIX))))
     :fn svtv-name-lhs-map-var/idx-find))

  (local (defthm svarlist-p-keys-of-svar/4vec-alist-p
           (implies (svar/4vec-alist-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable svar/4vec-alist-p alist-keys)))))

  (local
   (defret svtv-name-lhs-map-var/idx-find-of-fal-extract-lookup-consp
     :pre-bind ((xx x)
                (x (fal-extract keys x)))
     (implies (and (lhbit-case lhbit :var)
                   (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix x))))
              (consp (cdr (hons-assoc-equal (lhbit-var->name lhbit) xx))))
     :hints(("Goal" :use ((:instance svtv-name-lhs-map-var/idx-find-lookup-consp
                           (x (fal-extract keys x))))
             :in-theory (disable svtv-name-lhs-map-var/idx-find-lookup-consp)))
     :fn svtv-name-lhs-map-var/idx-find))

  (local
   (defret svtv-name-lhs-map-var/idx-find-of-fal-extract-lookup-width
     :pre-bind ((xx x)
                (x (fal-extract keys x)))
     (implies (and (lhbit-case lhbit :var)
                   (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix x))))
              (< (lhbit-var->idx lhbit)
                 (lhs-width (cdr (hons-assoc-equal (lhbit-var->name lhbit) xx)))))
     :hints(("Goal" :use ((:instance svtv-name-lhs-map-var/idx-find-lookup-width
                           (x (fal-extract keys x))))
             :in-theory (disable svtv-name-lhs-map-var/idx-find-lookup-width)))
     :fn svtv-name-lhs-map-var/idx-find))


  ;; (defretd constraints-eval-of-<fn>-implies
  ;;   (implies (and (lhprobe-constraintlist-eval constraints envs)
  ;;                 ;; x maps namemap names to consts/svtv vars
  ;;                 ;; namemap maps namemap names to fsm lhses
  ;;                 ;; envs each map fsm vars to values
  ;;                 ;; bindings maps svtv vars to fsm lhprobes

  ;;                 ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
  ;;                 ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
  ;;                 (no-duplicatesp-equal (alist-keys (svar/4vec-alist-fix x)))
  ;;                 (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
  ;;                 (not (equal (svar-overridetype-fix overridetype) :test)))
  ;;            (svex-env-<<=
  ;;             (svtv-fsm-namemap-env  ;; fsm vars (overridetype) to values
  ;;              (svar/4vec-alist-eval ;; namemap names to values
  ;;               x
  ;;               (lhprobe-map-eval bindings envs)) ;; svtv vars to values
  ;;              namemap overridetype)
  ;;             (nth stage envs)))
  ;;   :hints (("goal" :in-theory (e/d (svtv-fsm-namemap-env
  ;;                                    svtv-fsm-env-inversemap
  ;;                                    constraints-eval-of-<fn>
  ;;                                    svex-env-<<=
  ;;                                    ACL2::HONS-ASSOC-EQUAL-IFF-MEMBER-ALIST-KEYS
  ;;                                    4vec-<<=-by-badbit
  ;;                                    LHBIT-EVAL-X
  ;;                                    lhbit-eval-zero)
  ;;                                   (<fn>
  ;;                                    acl2::alist-keys-member-hons-assoc-equal
  ;;                                    eval-svtv-name-lhs-map-inverse-of-lookup-gen
  ;;                                    HONS-ASSOC-EQUAL-OF-SVAR/4VEC-ALIST-FIX
  ;;                                    HONS-ASSOC-EQUAL-OF-SVTV-NAME-LHS-MAP-FIX))
  ;;            :do-not-induct t)
  ;;           (and stable-under-simplificationp
  ;;                (let ((call (acl2::find-call-lst 'svex-env-<<=-witness clause)))
  ;;                  (and call
  ;;                       `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badkey)))))))
  ;;           (and stable-under-simplificationp
  ;;                (let ((call (acl2::find-call-lst '4vec-<<=-badbit clause)))
  ;;                  (and call
  ;;                       `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))))

  (local (Defthm member-of-svarlist-change-override-rw
           (implies (syntaxp (not (equal type ''nil)))
                    (iff (member-equal v (svarlist-change-override x type))
                         (and (svar-p v)
                              (svar-override-p v type)
                              (svarlist-member-nonoverride v x))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             equal-of-svar-change-override)))))

  (local (defthm hons-assoc-equal-when-not-member-alist-keys
           (implies (not (member-equal k (alist-keys x)))
                    (equal (hons-assoc-equal k x) nil))))

  (local (defthm equal-of-4vec-x-override
           (iff (equal (4vec-x-override x y) y)
                (and (4vec-p y)
                     (4vec-<<= x y)))))

  (local (defthmd 4vec-muxtest-subsetp-implies-bit-1mask-0
           (implies (and (4vec-muxtest-subsetp x y)
                         (equal 0 (4vec-1mask (4vec-bit-index bit y))))
                    (equal (4vec-1mask (4vec-bit-index bit x)) 0))
           :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp 4vec-1mask 4vec-bit-index bool->bit))
                  (logbitp-reasoning))))

  (local (defthm 4vec-1mask-of-bit-index-lookup-when-svex-envs-ovtests-ok
           (implies (and (svex-envs-ovtests-ok x y overridekeys)
                         (svar-override-p key :test)
                         (double-rewrite (equal 0 (4vec-1mask (4vec-bit-index bit (svex-env-lookup key y))))))
                    (equal (4vec-1mask (4vec-bit-index bit (svex-env-lookup key x))) 0))
           :hints (("goal" :use ((:instance svex-envs-ovtests-ok-necc
                                  (k key))
                                 (:instance 4vec-muxtest-subsetp-implies-bit-1mask-0
                                  (x (svex-env-lookup key x))
                                  (y (svex-env-lookup key y))))
                    :in-theory (disable svex-envs-ovtests-ok-necc)))))

  (local (defthmd 4vec-1mask-of-4vec-bit-index
           (equal (4vec-1mask (4vec-bit-index n x))
                  (if (equal (4vec-bit-index n x) 1) 1 0))
           :hints(("Goal" :in-theory (enable 4vec-bit-index bool->bit)))))

  (local (defthmd 4vec-1mask-of-4vec-bit-index-is-bit-index-of-1mask
           (equal (4vec-1mask (4vec-bit-index n x))
                  (4vec-bit-index n (4vec-1mask x)))
           :hints(("Goal" :in-theory (enable 4vec-bit-index 4vec-1mask bool->bit
                                             4vec->lower 4vec->upper)))))

  (local (defthmd 4vec-1mask-of-bit-index-lookup-when-svex-envs-ovtests-ok-nonoverridekey
           (implies (and (svex-envs-ovtests-ok x y overridekeys)
                         (svar-override-p key :test)
                         (not (svarlist-member-nonoverride key overridekeys)))
                    (equal (4vec-1mask (4vec-bit-index bit (svex-env-lookup key x)))
                           (4vec-1mask (4vec-bit-index bit (svex-env-lookup key y)))))
           :hints (("goal" :use ((:instance svex-envs-ovtests-ok-necc
                                  (k key)))
                    :in-theory (e/d (4vec-1mask-equiv
                                     4vec-1mask-of-4vec-bit-index-is-bit-index-of-1mask)
                                    (svex-envs-ovtests-ok-necc))))))

  (local (defthm bit-index-lookup-when-svex-envs-ovtests-ok
           (implies (and (svex-envs-ovtests-ok x y overridekeys)
                         (svar-override-p key :test)
                         (double-rewrite (not (equal 1 (4vec-bit-index bit (svex-env-lookup key y))))))
                    (not (equal (4vec-bit-index bit (svex-env-lookup key x)) 1)))
           :hints (("goal" :use 4vec-1mask-of-bit-index-lookup-when-svex-envs-ovtests-ok
                    :in-theory (enable 4vec-1mask-of-4vec-bit-index)))))

  (local (defthm bit-index-lookup-when-svex-envs-ovtests-ok-nonoverridekey
           (implies (and (svex-envs-ovtests-ok x y overridekeys)
                         (svar-override-p key :test)
                         (not (svarlist-member-nonoverride key overridekeys)))
                    (equal (equal (4vec-bit-index bit (svex-env-lookup key x)) 1)
                           (equal 1 (4vec-bit-index bit (svex-env-lookup key y)))))
           :hints (("goal" :use 4vec-1mask-of-bit-index-lookup-when-svex-envs-ovtests-ok-nonoverridekey
                    :in-theory (enable 4vec-1mask-of-4vec-bit-index)))))

  (local (defthm 4vec-bit-index-of-0
           (equal (4vec-bit-index n 0) 0)
           :hints(("Goal" :in-theory (enable 4vec-bit-index)))))

  ;; (local (Defthm hons-assoc-equal-lhs-map-inverse-iff
  ;;          (iff (hons-assoc-equal key (mv-nth 1 (svtv-name-lhs-map-inverse map)))
  ;;               (member-equal key (Svtv-name-lhs-map-vars map)))
  ;;          :hints(("Goal" :in-theory '((:REWRITE ACL2::HONS-ASSOC-EQUAL-IFF-MEMBER-ALIST-KEYS)
  ;;                                      (:REWRITE KEYS-OF-SVTV-NAME-LHS-MAP-INVERSE)
  ;;                                      (:REWRITE ACL2::SUBSETP-MEMBER . 1)
  ;;                                      (:REWRITE ACL2::SUBSETP-REFL)
  ;;                                      (:TYPE-PRESCRIPTION MEMBER-EQUAL))))))


  ;; (local (Defthm if-of-hons-assoc-equal-lhs-map-inverse
  ;;          (equal (if (hons-assoc-equal key (mv-nth 1 (svtv-name-lhs-map-inverse map))) x y)
  ;;                 (if (member-equal key (Svtv-name-lhs-map-vars map)) x y))))

  (local (Defthmd if-of-hons-assoc-equal-member-alist-keys
           (equal (if (hons-assoc-equal key a) x y)
                  (if (member-equal key (alist-keys a)) x y))))

  (local (defthm equal-1-of-if
           (implies (and (not (equal 1 x))
                         (not (equal 1 y)))
                    (not (equal 1 (if test x y))))))

  (local (defthm subsetp-equal-lhs-vars-of-svtv-name-lhs-map-lookup
           (implies (and (hons-assoc-equal key namemap)
                         (svar-p key))
                    (subsetp-equal (lhs-vars (cdr (hons-assoc-equal key namemap)))
                                   (svtv-name-lhs-map-vars namemap)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-vars alist-keys)))))

  (local (defthm subsetp-svtv-name-lhs-map-vars-of-fal-extract
           (subsetp-equal (svtv-name-lhs-map-vars (fal-extract keys (svtv-name-lhs-map-fix namemap)))
                          (svtv-name-lhs-map-vars namemap))
           :hints(("Goal" :in-theory (enable fal-extract svtv-name-lhs-map-vars)
                   :induct (len keys)))))

  (local (defthm not-member-map-vars-of-fal-extract
           (implies (not (member-equal v (svtv-name-lhs-map-vars namemap)))
                    (not (member-equal v (svtv-name-lhs-map-vars
                                          (fal-extract vars (svtv-name-lhs-map-fix namemap))))))))

  ;; (local (defthmd equal-of-4vec-1mask-bit-index
  ;;          (equal (equal (4vec-1mask (4vec-bit-index n x))
  ;;                        (4vec-1mask (4vec-bit-index m y)))
  ;;                 (iff (equal (4vec-1mask (4vec-bit-index n x)) 1)
  ;;                      (euqal (4vec-1mask (4vec-bit-index m y)) 1)))
  ;;          :hints(("Goal" :in-theory (enable 4vec-1mask-of-4vec-bit-index)))))

  (local (Defthm 4vec-bit-index-of-4vec-bit?!
           (equal (4vec-bit-index n (4vec-bit?! test then else))
                  (if (eql (4vec-bit-index n test) 1)
                      (4vec-bit-index n then)
                    (4vec-bit-index n else)))
           :hints(("Goal" :in-theory (enable 4vec-bit-index
                                             4vec-bit?! 4vec-bitmux 4vec-1mask b-ite)))))

  (local (defthm equal-4vec-bit?!-by-badbit
           (implies (acl2::rewriting-positive-literal
                     `(equal (4vec-bit?! ,a ,b ,c) (4vec-bit?! ,x ,y ,z)))
                    (equal (equal (4vec-bit?! a b c) (4vec-bit?! x y z))
                           (b* ((badbit (4vec-equiv-badbit (4vec-bit?! a b c) (4vec-bit?! x y z))))
                             (equal (4vec-bit-index badbit (4vec-bit?! a b c))
                                    (4vec-bit-index badbit (4vec-bit?! x y z))))))
           :hints (("goal" :use ((:instance 4vec-equiv-by-badbit
                                  (a (4vec-bit?! a b c))
                                  (b (4vec-bit?! x y z))))
                    :in-theory (disable 4vec-bit-index-of-4vec-bit?!)))))

  (local (defthm equal-4vec-bit?!-0-by-badbit
           (implies (acl2::rewriting-positive-literal
                     `(equal '0 (4vec-bit?! ,x ,y ,z)))
                    (equal (equal 0 (4vec-bit?! x y z))
                           (b* ((badbit (4vec-equiv-badbit 0 (4vec-bit?! x y z))))
                             (equal (4vec-bit-index badbit 0)
                                    (4vec-bit-index badbit (4vec-bit?! x y z))))))
           :hints (("goal" :use ((:instance 4vec-equiv-by-badbit
                                  (a 0)
                                  (b (4vec-bit?! x y z))))
                    :in-theory (disable 4vec-bit-index-of-4vec-bit?!)))))


  (defthmd constraints-overridemux-eval-of-svtv-spec-fsm-constraints-for-alist-implies
    (b* ((in-constraints (svtv-spec-fsm-constraints-for-alist in-alist stage namemap nil bindings))
         (val-constraints (svtv-spec-fsm-constraints-for-alist val-alist stage namemap :val bindings))
         (bindings-eval (lhprobe-map-overridemux-eval bindings envs outs))
         (in-env (svar/4vec-alist-eval in-alist bindings-eval))
         (val-env (svar/4vec-alist-eval val-alist bindings-eval))
         ;; (test-env (svar/4vec-alist-eval test-alist bindings-eval))
         )
      (implies (and (lhprobe-constraintlist-overridemux-eval in-constraints envs outs)
                    (lhprobe-constraintlist-overridemux-eval val-constraints envs outs)
                    ;; x maps namemap names to consts/svtv vars
                    ;; namemap maps namemap names to fsm lhses
                    ;; envs each map fsm vars to values
                    ;; bindings maps svtv vars to fsm lhprobes

                    ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
                    ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
                    (no-duplicatesp-equal (alist-keys (svar/4vec-alist-fix in-alist)))
                    (no-duplicatesp-equal (alist-keys (svar/4vec-alist-fix val-alist)))
                    (equal (alist-keys (svar/4vec-alist-fix val-alist))
                           (alist-keys ;; (svar/4vec-alist-fix test-alist)
                            (svex-env-fix test-env)))
                    (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                    ;; (subsetp-equal (svtv-name-lhs-map-vars (FAL-EXTRACT (ALIST-KEYS (SVAR/4VEC-ALIST-FIX TEST-ALIST))
                    ;;                                                     (SVTV-NAME-LHS-MAP-FIX NAMEMAP)))
                    ;;                (svarlist-change-override overridekeys nil))
                    (svex-envs-ovtests-ok (nth stage envs)
                                          (svtv-fsm-phase-inputs in-env val-env test-env namemap)
                                          overridekeys))
               (overridekeys-envs-agree*
                overridekeys
                (svex-env-x-override
                 (svtv-fsm-phase-inputs in-env val-env test-env namemap)
                 (svex-env-remove-override
                  (svex-env-remove-override (nth stage envs) :test)
                  :val))
                (nth stage envs)
                (nth stage outs))))
    :hints (("goal" :in-theory (e/d (overridekeys-envs-agree*-by-witness)
                                    (svtv-spec-fsm-constraints-for-alist))
             :do-not-induct t)
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'overridekeys-envs-agree*-badguy clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badkey)))))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svar-overridekeys-envs-agree*
                                    svtv-fsm-phase-inputs
                                    svtv-fsm-namemap-env
                                    svtv-fsm-env-inversemap
                                    4vec-<<=-by-badbit
                                    4vec-1mask-equiv-by-badbit
                                    4vec-muxtest-subsetp-by-badbit
                                    4vec-override-mux-agrees-by-badbit
                                    lhbit-eval-x
                                    lhbit-eval-zero
                                    lhprobe-overridemux-eval
                                    constraints-overridemux-eval-of-svtv-spec-fsm-constraints-for-alist
                                    acl2::hons-assoc-equal-iff-member-alist-keys
                                    if-of-hons-assoc-equal-member-alist-keys
                                    hons-assoc-equal-when-not-member-alist-keys
                                    4vec-1mask-of-4vec-bit-index
                                    member-when-not-svar-override-p
                                    svar-override-p-when-other
                                    svex-env-lookup-when-not-boundp
                                    svex-env-boundp-iff-member-alist-keys)
                                   (svtv-spec-fsm-constraints-for-alist
                                    eval-svtv-name-lhs-map-inverse-of-lookup-gen
                                    acl2::alist-keys-member-hons-assoc-equal
                                    hons-assoc-equal-of-svar/4vec-alist-fix
                                    hons-assoc-equal-of-svtv-name-lhs-map-fix))
                   :do-not-induct t))
            (and stable-under-simplificationp
                 (let ((call (or
                              (acl2::find-call-lst '4vec-<<=-badbit clause)
                              (acl2::find-call-lst '4vec-equiv-badbit clause)
                              (acl2::find-call-lst '4vec-1mask-equiv-badbit clause)
                              (acl2::find-call-lst '4vec-muxtest-subsetp-badbit clause)
                              (acl2::find-call-lst '4vec-override-mux-agrees-badbit clause))))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))
            ))



  (defret lhprobe-constraintlist-max-stage-of-<fn>
    (implies (and (<= (nfix stage) bound)
                  (<= (lhprobe-map-max-stage bindings) bound))
             (<= (lhprobe-constraintlist-max-stage constraints) bound))
    :hints(("Goal" :in-theory (enable lhprobe-constraintlist-max-stage
                                      lhprobe-constraint-max-stage))))

  (local (in-theory (enable svar/4vec-alist-fix))))


(defsection svtv-spec-fsm-constraints-for-alists
  (local (in-theory (enable svtv-spec-fsm-constraints-for-alists)))
  (local (std::set-define-current-function svtv-spec-fsm-constraints-for-alists))

  (local (include-book "std/lists/nthcdr" :dir :system))

  (local (defun ind (in-alists val-alists test-alists stage)
           (if (Atom in-alists)
               (list val-alists test-alists stage )
             (ind (cdr in-alists) (cdr val-alists) (cdr test-alists) (1+ (nfix stage))))))

  (local (defthm fal-extract-of-append
           (equal (fal-extract (append x y) z)
                  (append (fal-extract x z)
                          (fal-extract y z)))
           :hints(("Goal" :in-theory (enable fal-extract)))))

  (local (defthm svtv-name-lhs-map-vars-of-append
           (equal (svtv-name-lhs-map-vars (append x y))
                  (append (svtv-name-lhs-map-vars x) (svtv-name-lhs-map-vars y)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-vars)))))

  (local (defthm svex-alist-eval-when-noncall-p
           (implies (svex-alist-noncall-p x)
                    (equal (svex-alist-eval x env)
                           (svar/4vec-alist-eval x env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svar/4vec-alist-eval
                                             svex-alist-noncall-p
                                             svar/4vec-eval-in-terms-of-svex-eval)))))

  (local (defthm svex-alist-keys-when-noncall-p
           (implies (svex-alist-noncall-p x)
                    (Equal (svex-alist-keys x)
                           (alist-keys (svar/4vec-alist-fix x))))
           :hints(("Goal" :in-theory (enable svex-alist-keys
                                             svex-alist-noncall-p
                                             alist-keys
                                             svar/4vec-alist-fix)))))

  (defthmd constraints-overridemux-eval-of-svtv-spec-fsm-constraints-for-alists-implies
    (b* ((in-constraints (svtv-spec-fsm-constraints-for-alists in-alists stage namemap nil bindings))
         (val-constraints (svtv-spec-fsm-constraints-for-alists val-alists stage namemap :val bindings))
         (bindings-eval (lhprobe-map-overridemux-eval bindings envs outs))
         (in-envs   (svex-alistlist-eval in-alists bindings-eval))
         (val-envs  (svex-alistlist-eval val-alists bindings-eval)))
      (implies (and (lhprobe-constraintlist-overridemux-eval in-constraints envs outs)
                    (lhprobe-constraintlist-overridemux-eval val-constraints envs outs)
                    (equal (len in-alists) (len val-alists))
                    (equal (len in-alists) (len test-envs))
                    ;; x maps namemap names to consts/svtv vars
                    ;; namemap maps namemap names to fsm lhses
                    ;; envs each map fsm vars to values
                    ;; bindings maps svtv vars to fsm lhprobes

                    ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
                    ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
                    (svex-alistlist-noncall-p in-alists)
                    (svex-alistlist-noncall-p val-alists)
                    ;; (svex-alistlist-noncall-p test-alists)
                    (no-duplicatesp-each (svex-alist-keys-list in-alists))
                    (no-duplicatesp-each (svex-alist-keys-list val-alists))
                    (equal (svex-alist-keys-list val-alists)
                           (svex-envlist-keys-list test-envs))
                    (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                    ;; (subsetp-equal (svtv-name-lhs-map-vars
                    ;;                 (FAL-EXTRACT (svex-ALISTlist-all-keys test-alists)
                    ;;                              (SVTV-NAME-LHS-MAP-FIX NAMEMAP)))
                    ;;                (svarlist-change-override overridekeys nil))
                    (svex-envlists-ovtests-ok (nthcdr stage envs)
                                              (svtv-fsm-to-fsm-inputs in-envs val-envs test-envs namemap)
                                              overridekeys))
               (overridekeys-envlists-agree*
                overridekeys
                (svex-envlist-x-override
                 (svtv-fsm-to-fsm-inputs in-envs val-envs test-envs namemap)
                 (svex-envlist-remove-override
                  (svex-envlist-remove-override (nthcdr stage envs) :test)
                  :val))
                (nthcdr stage envs)
                (nthcdr stage outs))))
    :hints(("Goal" :in-theory (enable svex-alistlist-eval
                                      svex-alistlist-noncall-p
                                      svex-alist-keys-list
                                      svex-envlist-keys-list
                                      no-duplicatesp-each
                                      svex-alistlist-all-keys
                                      svex-envlists-ovtests-ok
                                      svex-envlist-x-override
                                      svtv-fsm-to-fsm-inputs
                                      overridekeys-envlists-agree*
                                      svex-envlist-remove-override
                                      constraints-overridemux-eval-of-svtv-spec-fsm-constraints-for-alist-implies)
            :expand ((LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL NIL ENVS OUTS)
                     (svtv-spec-fsm-constraints-for-alists val-alists stage namemap :Val bindings)
                     (svtv-spec-fsm-constraints-for-alists in-alists stage namemap  nil bindings)
                     (:free (y) (svex-envlist-x-override nil y))
                     (:free (a b envs outs)
                      (overridekeys-envlists-agree* overridekeys (cons a b) envs outs))
                     (:free (envs a b) (svex-envlists-ovtestsubsetp envs (cons a b))))
            :induct (ind in-alists val-alists test-envs stage)
            :do-not-induct t)))



  (defret lhprobe-constraintlist-max-stage-of-<fn>
    (implies (and (<= (+ -1 (len x) (nfix stage)) bound)
                  (<= (lhprobe-map-max-stage bindings) bound))
             (<= (lhprobe-constraintlist-max-stage constraints) bound))
    :hints(("Goal" :in-theory (enable lhprobe-constraintlist-max-stage
                                      lhprobe-constraint-max-stage)))))


(local (defthmd svtv-fsm-to-fsm-inputs-norm-override-vals-length
         (implies (and (equal new-override-vals (take (len ins) override-vals))
                       (syntaxp (not (equal new-override-vals override-vals))))
                  (equal (svtv-fsm-to-fsm-inputs ins override-vals override-tests namemap)
                         (svtv-fsm-to-fsm-inputs ins new-override-vals override-tests namemap)))
         :hints(("Goal" :in-theory (enable svtv-fsm-to-fsm-inputs)))))

(local (defthmd svtv-fsm-to-fsm-inputs-norm-override-tests-length
         (implies (and (equal new-override-tests (take (len ins) override-tests))
                       (syntaxp (not (equal new-override-tests override-tests))))
                  (equal (svtv-fsm-to-fsm-inputs ins override-vals override-tests namemap)
                         (svtv-fsm-to-fsm-inputs ins override-vals new-override-tests namemap)))
         :hints(("Goal" :in-theory (enable svtv-fsm-to-fsm-inputs)))))



(local (defthm take-of-svex-alistlist-eval
         (equal (take len (svex-alistlist-eval x env))
                (svex-alistlist-eval (take len x) env))
         :hints(("Goal" :in-theory (e/d (svex-alistlist-eval
                                         svex-alist-eval)
                                        (acl2::take-of-too-many
                                         acl2::take-when-atom))))))




(defsection svtv-spec-fsm-constraints
  (local (in-theory (enable svtv-spec-fsm-constraints)))
  (local (std::set-define-current-function svtv-spec-fsm-constraints))
  ;; Suppose we have an SVTV with an override-test set to -1 and the
  ;; corresponding override-val set to 0, and we want to show that FSM envs
  ;; without any overrride tests set comply with this.  The evaluation of the
  ;; constraints will correctly require that the FSM output corresponding to the override is 0.  But the

  (local (defthm svex-env-extract-of-append-when-not-intersectp
           (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix env1))))
                    (equal (svex-env-extract vars (append env1 env2))
                           (svex-env-extract vars env2)))
           :hints(("Goal" :in-theory (e/d (svex-env-extract intersectp-equal
                                                            svarlist-fix
                                                            svex-env-boundp-iff-member-alist-keys)
                                          (acl2::alist-keys-member-hons-assoc-equal))))))

  (local (defthm svex-alistlist-eval-of-append-non-intersect
           (implies (not (intersectp-equal (svex-alistlist-vars x) (alist-keys (svex-env-fix env1))))
                    (equal (Svex-alistlist-eval x (append env1 env2))
                           (svex-alistlist-eval x env2)))
           :hints(("Goal" :in-theory (enable svex-alistlist-eval
                                             svex-alistlist-vars
                                             svex-alist-eval-equal-when-extract-vars-similar)))))

  (defretd constraints-eval-of-<fn>-implies
    (implies (and (lhprobe-constraintlist-overridemux-eval constraints envs outs)
                  (svtv-spec-fsm-syntax-check x))
             (b* ((svtv-env (lhprobe-map-overridemux-eval
                             (svtv-spec-fsm-bindings x) envs outs))
                  ((svtv-spec x))
                  (fsm-envs (svtv-spec-pipe-env->cycle-envs x svtv-env))
                  (full-fsm-envs (svex-envlist-x-override
                                  fsm-envs
                                  (svex-envlist-remove-override
                                   (svex-envlist-remove-override envs :test) :val))))
               (implies (svex-envlists-ovtests-ok envs fsm-envs overridekeys)
                        (overridekeys-envlists-agree*
                         overridekeys
                         full-fsm-envs
                         envs outs))))
    :hints(("Goal" :in-theory (enable svtv-spec-fsm-syntax-check
                                      svtv-spec-pipe-env->cycle-envs
                                      svtv-fsm-to-fsm-inputs-norm-override-vals-length
                                      svtv-fsm-to-fsm-inputs-norm-override-tests-length
                                      take-of-svex-alistlist-eval)
            :use ((:instance constraints-overridemux-eval-of-svtv-spec-fsm-constraints-for-alists-implies
                   (in-alists (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->in-alists x)))
                   (val-alists (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->override-val-alists x)))
                   (test-envs (svex-alistlist-eval (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->override-test-alists x))
                                               (lhprobe-map-overridemux-eval
                                                (svtv-spec-fsm-bindings x) envs outs)))
                   (bindings (svtv-spec-fsm-bindings x))
                   (namemap (svtv-spec->namemap x))
                   (stage 0))))))


  (defretd constraints-eval-of-<fn>-implies-gen
    (implies (and (lhprobe-constraintlist-overridemux-eval constraints envs outs)
                  (svtv-spec-fsm-syntax-check x))
             (b* ((svtv-env (append test-bindings
                                    (lhprobe-map-overridemux-eval
                                     (svtv-spec-fsm-bindings x) envs outs)))
                  ((svtv-spec x))
                  (fsm-envs (svtv-spec-pipe-env->cycle-envs x svtv-env))
                  (full-fsm-envs (svex-envlist-x-override
                                  fsm-envs
                                  (svex-envlist-remove-override
                                   (svex-envlist-remove-override envs :test) :val))))
               (implies (and (svex-envlists-ovtests-ok envs fsm-envs overridekeys)
                             (not (acl2::hons-intersect-p (svtv-spec-non-test-vars x) (alist-keys (svex-env-fix test-bindings)))))
                        (overridekeys-envlists-agree*
                         overridekeys
                         full-fsm-envs
                         envs outs))))
    :hints(("Goal" :in-theory (enable svtv-spec-fsm-syntax-check
                                      svtv-spec-non-test-vars
                                      svtv-spec-pipe-env->cycle-envs
                                      svtv-fsm-to-fsm-inputs-norm-override-vals-length
                                      svtv-fsm-to-fsm-inputs-norm-override-tests-length
                                      take-of-svex-alistlist-eval)
            :use ((:instance constraints-overridemux-eval-of-svtv-spec-fsm-constraints-for-alists-implies
                   (in-alists (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->in-alists x)))
                   (val-alists (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->override-val-alists x)))
                   (test-envs (svex-alistlist-eval (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->override-test-alists x))
                                                   (append test-bindings
                                                           (lhprobe-map-overridemux-eval
                                                            (svtv-spec-fsm-bindings x) envs outs))))
                   (bindings (svtv-spec-fsm-bindings x))
                   (namemap (svtv-spec->namemap x))
                   (stage 0))))))

  (defret lhprobe-constraintlist-max-stage-of-<fn>
    (<= (lhprobe-constraintlist-max-stage constraints) (1- (len (svtv-probealist-outvars (Svtv-spec->probes x)))))
    :rule-classes ((:linear :trigger-terms ((lhprobe-constraintlist-max-stage
                                             (svtv-spec-fsm-constraints x)))))))


(cmr::def-force-execute svtv-spec-non-test-vars-force-execute svtv-spec-non-test-vars)

(local
 (defthm svex-envs-equivalent-when-similar-and-alist-keys-equiv
  (implies (set-equiv (alist-keys (svex-env-fix x)) (alist-keys (svex-env-fix y)))
           (equal (svex-envs-equivalent x y)
                  (svex-envs-similar x y)))
  :hints (("goal" :cases ((svex-envs-equivalent x y)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-envs-equivalent
                                  SVEX-ENV-BOUNDP-IFF-MEMBER-ALIST-KEYS)))))
  :otf-flg t))

(defsection fsm-override-p-of-cycle

  (local (defthmd not-member-by-svar-override-p-lemma
           (implies (and (svarlist-override-p x type1)
                         (svar-override-p v type2)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (member-equal v x)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p-when-other)))))

  (local (defthmd not-member-by-svar-override-p
           (implies (and (svarlist-equiv x-equiv (double-rewrite x))
                         (svarlist-override-p x-equiv type1)
                         (svar-equiv v-equiv (double-rewrite v))
                         (svar-override-p v-equiv type2)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (member-equal v x)))
           :hints(("Goal" :in-theory (enable not-member-by-svar-override-p-lemma)))))

  (local (defthmd not-member-by-svar-change-override
           (implies (and (svarlist-equiv x-equiv (double-rewrite x))
                         (svarlist-override-p x-equiv type1)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (member-equal (svar-change-override v type2) x)))
           :hints(("Goal" :use ((:instance not-member-by-svar-override-p-lemma
                                 (v (svar-change-override v type2))))))))



  (local (defthm overridekeys-envs-agree-of-append-nonoverride
           (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)
                         (svarlist-override-p (alist-keys (svex-env-fix x)) nil))
                    (overridekeys-envs-agree overridekeys
                                             (append x impl-env)
                                             (append x spec-env)
                                             spec-outs))
           :hints (("goal" :do-not-induct t)
                   (and stable-under-simplificationp
                        (let ((lit (car (last clause))))
                          `(:expand (,lit)
                            :use ((:instance overridekeys-envs-agree-implies
                                   (v (overridekeys-envs-agree-badguy . ,(cdr lit)))))
                            :in-theory (disable overridekeys-envs-agree-implies))))
                   (and stable-under-simplificationp
                        (let ((call (acl2::find-call-lst 'overridekeys-envs-agree-badguy clause)))
                          (and call
                               `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badkey)))))))
                   (and stable-under-simplificationp
                        '(:in-theory (e/d (svar-overridekeys-envs-agree
                                           svex-env-lookup-when-not-boundp
                                           svex-env-boundp-iff-member-alist-keys
                                           not-member-by-svar-override-p
                                           not-member-by-svar-change-override)
                                          (overridekeys-envs-agree-implies
                                           acl2::alist-keys-member-hons-assoc-equal)))))))

  ;; (defthmd svex-alist-overridekey-transparent-p-necc-direct
  ;;   (implies (and (svex-alist-overridekey-transparent-p x overridekeys subst)
  ;;                 (overridekeys-envs-agree overridekeys impl-env spec-env (svex-alist-eval subst spec-env)))
  ;;            (equal (svex-alist-eval x impl-env)
  ;;                   (svex-alist-eval x spec-env)))
  ;;   :hints(("Goal" :use svex-alist-overridekey-transparent-p-necc)))


  ;; (defthm svtv-cycle-step-phase-nextsts-when-svex-alist-overridekey-transparent-p
  ;;   (implies (and (svex-alist-overridekey-transparent-p nextst overridekeys values)
  ;;                 (overridekeys-envs-agree overridekeys impl-env spec-env (svex-alist-eval values spec-env))
  ;;                 (svarlist-override-p (svex-alist-keys nextst) nil)
  ;;                 (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil))
  ;;            (equal (svtv-cycle-step-phase-nextsts impl-env prev-st phase nextst)
  ;;                   (svtv-cycle-step-phase-nextsts spec-env prev-st phase nextst)))
  ;;   :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
  ;;                                   fsm-step-env)
  ;;                                  (overridekeys-envs-agree-of-append-nonoverride))
  ;;           :use ((:instance overridekeys-envs-agree-of-append-nonoverride
  ;;                  (x (append (svex-env-extract (svex-alist-keys nextst) prev-st)
  ;;                             (svtv-cyclephase->constants phase)))
  ;;                  (spec-outs (svex-alist-eval values spec-env)))
  ;;                 (:instance svex-alist-overridekey-transparent-p-necc
  ;;                  (impl-env (append (svex-env-extract (svex-alist-keys nextst) prev-st)
  ;;                                    (svtv-cyclephase->constants phase)
  ;;                                    impl-env))
  ;;                  (spec-env (append (svex-env-extract (svex-alist-keys nextst) prev-st)
  ;;                                    (svtv-cyclephase->constants phase)
  ;;                                    spec-env))
  ;;                  (subst values))))))

  (defthm svtv-cycle-step-phase-nextsts-when-svex-alist-overridekey-transparent-p
    (b* (((fsm x)))
      (implies (and (fsm-overridekey-transparent-p x overridekeys)
                    (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)
                    (svex-envs-equivalent spec-outs
                                          (mv-nth 0 (svtv-cycle-step-phase spec-env prev-st phase x)))
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    (iff (svtv-cyclephase->outputs-captured phase)
                         (svtv-cyclephase->inputs-free phase)))
               (equal (svtv-cycle-step-phase-nextsts impl-env prev-st phase x.nextstate)
                      (svtv-cycle-step-phase-nextsts spec-env prev-st phase x.nextstate))))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    svtv-cycle-step-phase-outs
                                    fsm-step-env
                                    fsm-overridekey-transparent-p)
                                   (overridekeys-envs-agree-of-append-nonoverride))
            :use ((:instance overridekeys-envs-agree-of-append-nonoverride
                   (x (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                              (svtv-cyclephase->constants phase)))
                   (spec-outs (mv-nth 0 (svtv-cycle-step-phase spec-env prev-st phase x))))
                  (:instance svex-alist-overridekey-transparent-p-necc
                   (x (fsm->nextstate x))
                   (impl-env (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                                     (svtv-cyclephase->constants phase)
                                     impl-env))
                   (spec-env (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                                     (svtv-cyclephase->constants phase)
                                     spec-env))
                   (subst (fsm->values x)))))))

  (defthm svtv-cycle-step-phase-outs-when-svex-alist-overridekey-transparent-p
    (b* (((fsm x)))
      (implies (and (fsm-overridekey-transparent-p x overridekeys)
                    (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)
                    (svex-envs-equivalent spec-outs
                                          (mv-nth 0 (svtv-cycle-step-phase spec-env prev-st phase x)))
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    (svtv-cyclephase->outputs-captured phase)
                    (svtv-cyclephase->inputs-free phase))
               (equal (svtv-cycle-step-phase-outs impl-env prev-st phase x)
                      (svtv-cycle-step-phase-outs spec-env prev-st phase x))))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    svtv-cycle-step-phase-outs
                                    fsm-step-env
                                    fsm-overridekey-transparent-p)
                                   (overridekeys-envs-agree-of-append-nonoverride))
            :use ((:instance overridekeys-envs-agree-of-append-nonoverride
                   (x (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                              (svtv-cyclephase->constants phase)))
                   (spec-outs (mv-nth 0 (svtv-cycle-step-phase spec-env prev-st phase x))))
                  (:instance svex-alist-overridekey-transparent-p-necc
                   (x (fsm->values x))
                   (impl-env (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                                     (svtv-cyclephase->constants phase)
                                     impl-env))
                   (spec-env (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                                     (svtv-cyclephase->constants phase)
                                     spec-env))
                   (subst (fsm->values x)))))))

  (defthm svtv-cycle-step-phase-nextsts-normalize-env-when-not-inputs-free
    (implies (and (syntaxp (not (equal env ''nil)))
                  (not (svtv-cyclephase->inputs-free phase)))
             (equal (svtv-cycle-step-phase-nextsts env prev-st phase x)
                    (svtv-cycle-step-phase-nextsts nil prev-st phase x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts))))

  (defthm svtv-cycle-eval-nextst-when-svex-alist-overridekey-transparent-p-no-i/o-phase
    (b* (((fsm x)))
      (implies (and (syntaxp (not (equal env ''nil)))
                    (svtv-cyclephaselist-no-i/o-phase phases))
               (equal (svtv-cycle-eval-nextst env prev-st phases x)
                      (svtv-cycle-eval-nextst nil prev-st phases x))))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-nextst
                                      svtv-cyclephaselist-no-i/o-phase))))

  (defthm svtv-cycle-eval-nextst-when-svex-alist-overridekey-transparent-p-unique-i/o-phase
    (b* (((fsm x)))
      (implies (and (fsm-overridekey-transparent-p x overridekeys)
                    (overridekeys-envs-agree overridekeys impl-env spec-env
                                             (svtv-cycle-eval-outs spec-env prev-st phases x))
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svtv-cyclephaselist-unique-i/o-phase phases))
               (equal (svtv-cycle-eval-nextst impl-env prev-st phases x.nextstate)
                      (svtv-cycle-eval-nextst spec-env prev-st phases x.nextstate))))
    :hints(("Goal" :in-theory (enable (:i svtv-cycle-eval-nextst)
                                      svtv-cyclephaselist-unique-i/o-phase)
            :induct (svtv-cycle-eval-nextst impl-env prev-st phases (fsm->nextstate x))
            :expand ((:free (impl-env x) (svtv-cycle-eval-nextst impl-env prev-st phases x))
                     (svtv-cycle-eval-outs spec-env prev-st phases x)
                     (svtv-cyclephaselist-keys phases)))))

  (defthm svtv-cycle-eval-outs-when-svex-alist-overridekey-transparent-p-unique-i/o-phase
    (b* (((fsm x)))
      (implies (and (fsm-overridekey-transparent-p x overridekeys)
                    (overridekeys-envs-agree overridekeys impl-env spec-env
                                             (svtv-cycle-eval-outs spec-env prev-st phases x))
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svtv-cyclephaselist-unique-i/o-phase phases))
               (equal (svtv-cycle-eval-outs impl-env prev-st phases x)
                      (svtv-cycle-eval-outs spec-env prev-st phases x))))
    :hints(("Goal" :in-theory (enable (:i svtv-cycle-eval-outs)
                                      svtv-cyclephaselist-unique-i/o-phase)
            :induct (svtv-cycle-eval-outs impl-env prev-st phases x)
            :expand ((:free (spec-env) (svtv-cycle-eval-outs spec-env prev-st phases x))
                     (svtv-cyclephaselist-keys phases)))))

  (defthm svtv-cycle-step-phase-outs-of-extract-initst-keys
    (b* (((fsm x)))
      (equal (svtv-cycle-step-phase-outs env (svex-env-extract (svex-alist-keys x.nextstate) prev-st) phase x)
             (svtv-cycle-step-phase-outs env prev-st phase x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-outs))))

  (defthm svtv-cycle-step-phase-nextsts-of-extract-initst-keys
    (equal (svtv-cycle-step-phase-nextsts env (svex-env-extract (svex-alist-keys nextst) prev-st) phase nextst)
           (svtv-cycle-step-phase-nextsts env prev-st phase nextst))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts))))

  (defthm svtv-cycle-eval-outs-of-extract-initst-keys
    (b* (((fsm x)))
      (equal (svtv-cycle-eval-outs env (svex-env-extract (svex-alist-keys x.nextstate) prev-st) phases x)
             (svtv-cycle-eval-outs env prev-st phases x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs))))

  (defthm svtv-cycle-eval-nextst-of-extract-initst-keys
    (equal (svtv-cycle-eval-nextst env (svex-env-extract (svex-alist-keys x.nextstate) prev-st) phases x.nextstate)
           (svtv-cycle-eval-nextst env prev-st phases x.nextstate))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-nextst))))

  (local
   (defthm extract-keys-when-overridekeys-envs-agree
     (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)
                   (svarlist-override-p keys nil))
              (equal (svex-env-extract keys impl-env)
                     (svex-env-extract keys spec-env)))
     :hints(("Goal" :in-theory (enable svex-env-extract
                                       svarlist-override-p)
             :induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance overridekeys-envs-agree-implies
                          (v (car keys))))
                   :in-theory (enable svar-overridekeys-envs-agree
                                      svar-override-p-when-other))))))

  (local (defthm svtv-cycle-eval-outs-when-initst-is-impl-env
           (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)
                         (svarlist-override-p (svex-alist-keys (fsm->nextstate x)) nil))
                    (equal (svtv-cycle-eval-outs impl-env impl-env phases x)
                           (svtv-cycle-eval-outs impl-env spec-env phases x)))
           :hints (("goal" :use ((:instance svtv-cycle-eval-outs-of-extract-initst-keys
                                  (prev-st impl-env)
                                  (env impl-env))
                                 (:instance svtv-cycle-eval-outs-of-extract-initst-keys
                                  (prev-st spec-env)
                                  (env impl-env)))))))

  (defthm fsm-overridekey-transparent-p-of-fsm-to-cycle
    (implies (and (fsm-overridekey-transparent-p fsm overridekeys)
                  (svarlist-override-p (svex-alist-keys (fsm->nextstate fsm)) nil)
                  (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil))
             (fsm-overridekey-transparent-p (fsm-to-cycle phases fsm nil) overridekeys))
    :hints(("Goal" :in-theory (enable fsm-to-cycle))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))) ;; fsm-overridekey-transparent-p
           (and stable-under-simplificationp
                `(:expand ((:with svex-alist-overridekey-transparent-p
                            ,(car (last clause))))))
           (and stable-under-simplificationp
                        (let ((call (acl2::find-call-lst 'svex-alist-overridekey-transparent-p-witness clause)))
                          (and call
                               `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . impl-env)
                                                                                            ((mv-nth '1 ,call) . spec-env)))))))))

  (local (defthm member-equal-when-nonoverride-p
           (implies (and (svar-override-p v type)
                         (svarlist-nonoverride-p x type))
                    (not (member-equal (svar-fix v) x)))
           :hints(("Goal" :in-theory (enable svarlist-nonoverride-p)))))

  (local (defthm member-equal-svar-change-override-when-nonoverride-p
           (implies (and (svarlist-nonoverride-p x type))
                    (not (member-equal (svar-change-override v type) x)))
           :hints (("goal" :use ((:instance member-equal-when-nonoverride-p
                                  (v (svar-change-override v type))))
                    :in-theory (disable member-equal-when-nonoverride-p)))))


  (local
   (defthm svex-envs-ovsimilar-of-append
    (implies (And (svex-envs-ovsimilar c d)
                  (svarlist-nonoverride-p (alist-keys (svex-env-fix a)) :test)
                  (svarlist-nonoverride-p (alist-keys (svex-env-fix a)) :val))
             (equal (svex-envs-ovsimilar (append a c) (append a d))
                    t))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (car (last clause)))
                      (witness `(svex-envs-ovsimilar-witness . ,(cdr lit))))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovsimilar-necc (x c) (y d)
                            (v ,witness))
                           (:instance svex-envs-ovsimilar-necc (x c) (y d)
                            (v (svar-change-override ,witness :test))))
                     :in-theory (enable svex-env-boundp-iff-member-alist-keys
                                        member-when-not-svar-override-p)
                     :do-not-induct t))))))

  (local (defthm svarlist-nonoverride-p-when-svarlist-override-p
           (implies (and (svarlist-override-p x type)
                         (not (equal (svar-overridetype-fix type) (svar-overridetype-fix type2))))
                    (svarlist-nonoverride-p x type2))
           :hints(("Goal" :in-theory (enable svarlist-nonoverride-p svarlist-override-p
                                             svar-override-p-when-other)))))

  (local
   (defthm svex-envs-ovsimilar-of-append-2
     (implies (And (svex-envs-ovsimilar c d)
                   (svarlist-override-p (alist-keys (svex-env-fix a)) nil)
                   (svarlist-override-p (alist-keys (svex-env-fix b)) nil))
             (equal (svex-envs-ovsimilar (append a b c) (append a b d))
                    t))
   :hints (("goal" :use ((:instance svex-envs-ovsimilar-of-append (a (append a b))))
            :in-theory (disable svex-envs-ovsimilar-of-append)))))

  (defthm svtv-cycle-step-phase-nextsts-when-ovcongruent
    (b* (((fsm x)))
      (implies (and (fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    ;; (iff (svtv-cyclephase->outputs-captured phase)
                    ;;      (svtv-cyclephase->inputs-free phase))
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-step-phase-nextsts env1 prev-st phase x.nextstate)
                                            (svtv-cycle-step-phase-nextsts env2 prev-st phase x.nextstate))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    svtv-cycle-step-phase-outs
                                    fsm-step-env
                                    fsm-ovcongruent))
            :use ((:instance svex-alist-ovcongruent-necc
                   (x (fsm->nextstate x))
                   (env1 (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                                 (svtv-cyclephase->constants phase)
                                 env1))
                   (env2 (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                                 (svtv-cyclephase->constants phase)
                                 env2)))))))

  (defthm svtv-cycle-step-phase-outs-when-ovcongruent
    (b* (((fsm x)))
      (implies (and (fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-step-phase-outs env1 prev-st phase x)
                                            (svtv-cycle-step-phase-outs env2 prev-st phase x))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    svtv-cycle-step-phase-outs
                                    fsm-step-env
                                    fsm-ovcongruent))
            :use ((:instance svex-alist-ovcongruent-necc
                   (x (fsm->values x))
                   (env1 (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                                 (svtv-cyclephase->constants phase)
                                 env1))
                   (env2 (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                                 (svtv-cyclephase->constants phase)
                                 env2)))))))

  (local
   (defthmd extract-keys-when-ovsimilar
     (implies (and (svex-envs-ovsimilar env1 env2)
                   (svarlist-override-p keys nil))
              (equal (equal (svex-env-extract keys env1)
                            (svex-env-extract keys env2))
                     t))
     :hints(("Goal" :in-theory (enable svex-env-extract
                                       svarlist-override-p)
             :induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance svex-envs-ovsimilar-necc
                          (v (car keys)) (x env1) (y env2)))
                   :in-theory (enable svar-override-p-when-other))))))

  (defthm svtv-cycle-step-phase-outs-when-ovcongruent-2
    (b* (((fsm x)))
      (implies (and (fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-step-phase-outs env1 env1 phase x)
                                            (svtv-cycle-step-phase-outs env2 env2 phase x))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    svtv-cycle-step-phase-outs
                                    fsm-step-env
                                    fsm-ovcongruent))
            :use ((:instance svex-alist-ovcongruent-necc
                   (x (fsm->values x))
                   (env1 (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) env1)
                                 (svtv-cyclephase->constants phase)
                                 env1))
                   (env2 (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) env1)
                                 (svtv-cyclephase->constants phase)
                                 env2)))
                  (:instance extract-keys-when-ovsimilar
                   (keys (svex-alist-keys (fsm->nextstate x)))))
            )))

  (defthm svtv-cycle-step-phase-nextsts-when-ovcongruent-2
    (b* (((fsm x)))
      (implies (and (fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-step-phase-nextsts env1 env1 phase x.nextstate)
                                            (svtv-cycle-step-phase-nextsts env2 env2 phase x.nextstate))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    fsm-step-env
                                    fsm-ovcongruent))
            :use ((:instance svex-alist-ovcongruent-necc
                   (x (fsm->nextstate x))
                   (env1 (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) env1)
                                 (svtv-cyclephase->constants phase)
                                 env1))
                   (env2 (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) env1)
                                 (svtv-cyclephase->constants phase)
                                 env2)))
                  (:instance extract-keys-when-ovsimilar
                   (keys (svex-alist-keys (fsm->nextstate x)))))
            )))


  (defthm svtv-cycle-eval-outs-when-ovcongruent
    (b* (((fsm x)))
      (implies (and (fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-eval-outs env1 prev-st phases x)
                                            (svtv-cycle-eval-outs env2 prev-st phases x))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-eval-outs))
            :induct (svtv-cycle-eval-outs env1 prev-st phases x)
            :expand ((:free (env1) (svtv-cycle-eval-outs env1 prev-st phases x))
                     (svtv-cyclephaselist-keys phases)))
           (and stable-under-simplificationp
                '(:use ((:instance svtv-cycle-step-phase-nextsts-when-ovcongruent
                         (phase (car phases))))
                  :in-theory (disable svtv-cycle-step-phase-nextsts-when-ovcongruent)))))

  (defthm svtv-cycle-eval-outs-when-ovcongruent-2
    (b* (((fsm x)))
      (implies (and (fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-eval-outs env1 env1 phases x)
                                            (svtv-cycle-eval-outs env2 env2 phases x))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-eval-outs))
            :expand ((svtv-cycle-eval-outs env1 env1 phases x)
                     (svtv-cycle-eval-outs env2 env2 phases x)
                     (svtv-cyclephaselist-keys phases)))
           (and stable-under-simplificationp
                '(:use ((:instance svtv-cycle-step-phase-nextsts-when-ovcongruent-2
                         (phase (car phases))))
                  :in-theory (disable svtv-cycle-step-phase-nextsts-when-ovcongruent-2)))))

  (defthm svtv-cycle-eval-nextst-when-ovcongruent
    (b* (((fsm x)))
      (implies (and (fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-eval-nextst env1 prev-st phases x.nextstate)
                                            (svtv-cycle-eval-nextst env2 prev-st phases x.nextstate))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-eval-nextst))
            :induct (svtv-cycle-eval-nextst env1 prev-st phases (fsm->nextstate x))
            :expand ((:free (env1) (svtv-cycle-eval-nextst env1 prev-st phases (fsm->nextstate x)))
                     (svtv-cyclephaselist-keys phases)))
           (and stable-under-simplificationp
                '(:use ((:instance svtv-cycle-step-phase-nextsts-when-ovcongruent
                         (phase (car phases))))
                  :in-theory (disable svtv-cycle-step-phase-nextsts-when-ovcongruent)))))

  (defthm svtv-cycle-eval-nextst-when-ovcongruent-2
    (b* (((fsm x)))
      (implies (and (fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-eval-nextst env1 env1 phases x.nextstate)
                                            (svtv-cycle-eval-nextst env2 env2 phases x.nextstate))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-eval-nextst)
                                   (SVEX-ENVS-EQUIVALENT-WHEN-SIMILAR-AND-ALIST-KEYS-EQUIV))
            :expand ((svtv-cycle-eval-nextst env1 env1 phases (fsm->nextstate x))
                     (svtv-cycle-eval-nextst env2 env2 phases (fsm->nextstate x))
                     (svtv-cyclephaselist-keys phases)))
           (and stable-under-simplificationp
                '(:use ((:instance svtv-cycle-step-phase-nextsts-when-ovcongruent-2
                         (phase (car phases)))
                        (:instance extract-keys-when-ovsimilar
                         (keys (svex-alist-keys (fsm->nextstate x)))))
                  :in-theory (disable svtv-cycle-step-phase-nextsts-when-ovcongruent-2
                                      SVEX-ENVS-EQUIVALENT-WHEN-SIMILAR-AND-ALIST-KEYS-EQUIV)))))

  (defthm fsm-ovcongruent-p-of-fsm-to-cycle
    (implies (and (fsm-ovcongruent fsm)
                  (svarlist-override-p (svex-alist-keys (fsm->nextstate fsm)) nil)
                  ;; (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                  )
             (fsm-ovcongruent (fsm-to-cycle phases fsm nil)))
    :hints(("Goal" :in-theory (enable fsm-to-cycle fsm-ovcongruent))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))
           (and stable-under-simplificationp
                        (let ((call (acl2::find-call-lst 'svex-alist-ovcongruent-witness clause)))
                          (and call
                               `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                            ((mv-nth '1 ,call) . env2))))))))))




(cmr::def-force-execute force-execute-force-execute force-execute)
(in-theory (enable force-execute-force-execute))





(defcong 4vec-1mask-equiv 4vec-1mask-equiv (4vec-rsh sh x) 2
  :hints(("Goal" :in-theory (enable 4vec-1mask-equiv 4vec-rsh 4vec-1mask 4vec-shift-core))
         (bitops::logbitp-reasoning)))

(defcong svex-envs-1mask-equiv  4vec-1mask-equiv (lhatom-eval x env) 2
  :hints(("Goal" :in-theory (enable lhatom-eval))))

(defcong svex-envs-1mask-equiv  4vec-1mask-equiv (lhatom-eval-zero x env) 2
  :hints(("Goal" :in-theory (enable lhatom-eval-zero))))

(defcong 4vec-1mask-equiv 4vec-1mask-equiv (4vec-concat sh x y) 2
  :hints(("Goal" :in-theory (enable 4vec-1mask-equiv 4vec-concat 4vec-1mask))
         (bitops::logbitp-reasoning)))

(defcong 4vec-1mask-equiv 4vec-1mask-equiv (4vec-concat sh x y) 3
  :hints(("Goal" :in-theory (enable 4vec-1mask-equiv 4vec-concat 4vec-1mask))
         (bitops::logbitp-reasoning)))

(defcong 4vec-1mask-equiv 4vec-1mask-equiv (4vec-sign-ext sh x) 2
  :hints(("Goal" :in-theory (enable 4vec-1mask-equiv 4vec-sign-ext 4vec-1mask))
         (bitops::logbitp-reasoning)))

(defcong svex-envs-1mask-equiv  4vec-1mask-equiv (lhs-eval x env) 2
  :hints(("Goal" :in-theory (enable lhs-eval lhrange-eval))))

(defcong svex-envs-1mask-equiv  4vec-1mask-equiv (lhs-eval-zx x env) 2
  :hints(("Goal" :in-theory (enable lhs-eval-zx))))

(defcong svex-envs-1mask-equiv  4vec-1mask-equiv (lhs-eval-signx x env) 2
  :hints(("Goal" :in-theory (enable lhs-eval-signx))))


(local (defthm svex-envs-1mask-equiv-of-cons
         (implies (and (svex-envs-1mask-equiv x y)
                       (double-rewrite (4vec-1mask-equiv xv yv)))
                  (equal (svex-envs-1mask-equiv (cons (cons k xv) x) (cons (cons k yv) y)) t))
         :hints ((and stable-under-simplificationp
                      (b* ((lit (car (last clause))))
                        `(:expand (,lit)
                          :in-theory (enable svex-env-lookup-of-cons-split)))))))



(defcong svex-envs-1mask-equiv svex-envs-1mask-equiv (svtv-name-lhs-map-eval x env) 2
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval))))


(defthmd svex-alist-eval-1mask-equiv-congruence-when-noncall-p
  (implies (and (svex-alist-noncall-p x)
                (svex-envs-1mask-equiv env1 env2))
           (equal (svex-envs-1mask-equiv (svex-alist-eval x env1)
                                         (svex-alist-eval x env2))
                  t))
  :hints (("goal" :in-theory (enable svex-alist-eval svex-alist-noncall-p)
           :induct t
           :expand ((:free (env) (svex-eval (cdar x) env))))))

(defthmd svex-alistlist-eval-1mask-equiv-congruence-when-noncall-p
  (implies (and (svex-alistlist-noncall-p x)
                (svex-envs-1mask-equiv env1 env2))
           (equal (svex-envlists-1mask-equiv (svex-alistlist-eval x env1)
                                             (svex-alistlist-eval x env2))
                  t))
  :hints (("goal" :in-theory (enable svex-alistlist-eval svex-alistlist-noncall-p
                                     svex-envlists-1mask-equiv
                                     svex-alist-eval-1mask-equiv-congruence-when-noncall-p))))


(defthmd svtv-fsm-namemap-env-1mask-equiv-congruence
  (implies (and (svex-alist-noncall-p alist)
                (svex-envs-1mask-equiv env1 env2))
           (equal (svex-envs-1mask-equiv (svtv-fsm-namemap-env (svex-alist-eval alist env1) map :test)
                                         (svtv-fsm-namemap-env (svex-alist-eval alist env2) map :test))
                  t))
  :hints(("Goal" :in-theory (enable svtv-fsm-namemap-env)
          :use ((:instance svex-alist-eval-1mask-equiv-congruence-when-noncall-p
                 (x alist))))))

(defthmd svtv-fsm-namemap-envlist-1mask-equiv-congruence
  (implies (and (svex-alistlist-noncall-p alists)
                (svex-envs-1mask-equiv env1 env2))
           (equal (svex-envlists-1mask-equiv (svtv-fsm-namemap-envlist (svex-alistlist-eval alists env1) map :test)
                                             (svtv-fsm-namemap-envlist (svex-alistlist-eval alists env2) map :test))
                  t))
  :hints(("Goal" :in-theory (enable svtv-fsm-namemap-envlist
                                    svex-alistlist-eval
                                    svex-alistlist-noncall-p
                                    svex-envlists-1mask-equiv
                                    svtv-fsm-namemap-env-1mask-equiv-congruence))))



;; (defcong svex-envs-1mask-equiv svex-envs-1mask-equiv (svtv-fsm-namemap-env env namemap :test) 1
;;   :hints(("Goal" :in-theory (enable svtv-fsm-namemap-env))))

(defrefinement svex-envs-1mask-equiv svex-envs-ovtestsimilar
  :hints (("goal" :in-theory (enable svex-envs-ovtestsimilar))))

(defrefinement svex-envlists-1mask-equiv svex-envlists-ovtestsimilar
  :hints (("goal" :in-theory (enable svex-envlists-ovtestsimilar
                                     svex-envlists-1mask-equiv))))

(defthmd svtv-fsm-namemap-envlist-ovtestsimilar-congruence
  (implies (and (svex-alistlist-noncall-p alists)
                (svex-envs-1mask-equiv env1 env2))
           (equal (svex-envlists-ovtestsimilar (svtv-fsm-namemap-envlist (svex-alistlist-eval alists env1) map :test)
                                               (svtv-fsm-namemap-envlist (svex-alistlist-eval alists env2) map :test))
                  t))
  :hints (("goal" :use svtv-fsm-namemap-envlist-1mask-equiv-congruence)))

(defthmd lhatom-eval-zero-when-override-test-vars-and-ovtestsimilar
  (implies (and (svarlist-override-p (lhatom-vars x) :test)
                (svex-envs-ovtestsimilar env1 env2))
           (equal (4vec-1mask-equiv (lhatom-eval-zero x env1)
                                    (lhatom-eval-zero x env2))
                  t))
  :hints(("Goal" :in-theory (enable lhatom-eval-zero
                                    lhatom-vars
                                    svarlist-override-p)
          :use ((:instance svex-envs-ovtestsimilar-necc
                 (k (lhatom-var->name x))
                 (x env1) (y env2))))))

(defthmd lhs-eval-signx-when-override-test-vars-and-ovtestsimilar
  (implies (and (svarlist-override-p (lhs-vars x) :test)
                (svex-envs-ovtestsimilar env1 env2))
           (equal (4vec-1mask-equiv (lhs-eval-signx x env1)
                                    (lhs-eval-signx x env2))
                  t))
  :hints(("Goal" :in-theory (enable lhs-vars)
          :induct (lhs-vars x)
          :expand ((:free (env) (lhs-eval-signx x env))))
         (and stable-under-simplificationp
              '(:use ((:instance lhatom-eval-zero-when-override-test-vars-and-ovtestsimilar
                       (x (lhrange->atom (car x)))))))))


(defthmd lhs-eval-zx-when-override-test-vars-and-ovtestsimilar
  (implies (and (svarlist-override-p (lhs-vars x) :test)
                (svex-envs-ovtestsimilar env1 env2))
           (equal (4vec-1mask-equiv (lhs-eval-zx x env1)
                                    (lhs-eval-zx x env2))
                  t))
  :hints(("Goal" :in-theory (enable lhs-vars)
          :induct (lhs-vars x)
          :expand ((:free (env) (lhs-eval-zx x env))))
         (and stable-under-simplificationp
              '(:use ((:instance lhatom-eval-zero-when-override-test-vars-and-ovtestsimilar
                       (x (lhrange->atom (car x)))))))))

(defthm svex-envs-ovtestsimilar-nth-when-svex-envlists-ovtestsimilar
    (implies (svex-envlists-ovtestsimilar x y)
             (equal (svex-envs-ovtestsimilar (nth n x) (nth n y)) t))
    :hints(("Goal" :in-theory (enable svex-envlists-ovtestsimilar))))

(defthmd lhprobe-eval-when-override-test-vars-and-ovtestsimilar
  (implies (and (svarlist-override-p (lhprobe-vars x) :test)
                (svex-envlists-ovtestsimilar envs1 envs2))
           (equal (4vec-1mask-equiv (lhprobe-eval x envs1)
                                    (lhprobe-eval x envs2))
                  t))
  :hints(("Goal" :in-theory (enable lhprobe-eval
                                    lhprobe-vars
                                    lhs-eval-signx-when-override-test-vars-and-ovtestsimilar
                                    lhs-eval-zx-when-override-test-vars-and-ovtestsimilar))))

(defthmd lhprobe-map-eval-when-override-test-vars-and-ovtestsimilar
  (implies (and (svarlist-override-p (lhprobe-map-vars x) :test)
                (svex-envlists-ovtestsimilar envs1 envs2))
           (equal (svex-envs-1mask-equiv (lhprobe-map-eval x envs1)
                                         (lhprobe-map-eval x envs2))
                  t))
  :hints(("Goal" :in-theory (enable lhprobe-map-eval
                                    lhprobe-map-vars
                                    lhprobe-eval-when-override-test-vars-and-ovtestsimilar))))




(local (defthm car-hons-assoc-equal
         (equal (car (hons-assoc-equal k x))
                (and (hons-assoc-equal k x) k))))

(defsection svtv-spec-pipe-env->cycle-envs-under-svex-envlists-ovtestsimilar
 (defcong svex-envs-ovtestsimilar svex-envs-ovtestsimilar (append x y) 2
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 (let* ((lit (car (last clause)))
                        (wit `(svex-envs-ovtestsimilar-witness . ,(cdr lit))))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtestsimilar-necc
                            (x y-equiv)
                            (k ,wit))))))))

 (local (defthm not-member-when-svarlist-nonoverride-p
          (implies (and (svarlist-nonoverride-p x type)
                        (svar-override-p v type))
                   (not (member-equal (svar-fix v) x)))
          :hints(("Goal" :in-theory (enable svarlist-nonoverride-p)))))

 (local (defthm svex-envs-ovtestsimilar-to-nil-when-nonoverride-p
          (implies (svarlist-nonoverride-p (alist-keys (svex-env-fix x)) :test)
                   (equal (svex-envs-ovtestsimilar x nil) t))
          :hints(("Goal" :in-theory (e/d (svex-envs-ovtestsimilar
                                            svex-env-lookup-when-not-boundp
                                            svex-env-boundp-iff-member-alist-keys)
                                         (acl2::alist-keys-member-hons-assoc-equal))))))



  (local (defthm alist-keys-of-svtv-name-lhs-map-eval-x
           (equal (alist-keys (svtv-name-lhs-map-eval-x x env))
                  (alist-keys (svtv-name-lhs-map-fix x)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-eval-x
                                             alist-keys)))))

  (local (defthm alist-keys-of-svtv-name-lhs-map-eval
           (equal (alist-keys (svtv-name-lhs-map-eval x env))
                  (alist-keys (svtv-name-lhs-map-fix x)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-eval
                                             alist-keys)))))

  (local (defthm alist-keys-of-svtv-name-lhs-map-vals-change-override
           (equal (alist-keys (svtv-name-lhs-map-vals-change-override x type))
                  (alist-keys (svtv-name-lhs-map-fix x)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-vals-change-override
                                             alist-keys)))))

  (local (defthm svarlist-override-p-alist-keys-of-svtv-fsm-namemap-env
          (svarlist-override-p (alist-keys (svtv-fsm-namemap-env alist map type)) type)
          :hints(("Goal" :in-theory (enable svtv-fsm-namemap-env)))))

 (local (defthm svarlist-nonoverride-p-when-svarlist-override-p
           (implies (and (svarlist-override-p x type)
                         (not (equal (svar-overridetype-fix type) (svar-overridetype-fix type2))))
                    (svarlist-nonoverride-p x type2))
           :hints(("Goal" :in-theory (enable svarlist-nonoverride-p svarlist-override-p
                                             svar-override-p-when-other)))))

 (local (defthm svarlist-nonoverride-p-alist-keys-of-svtv-fsm-namemap-env
          (implies (not (equal (svar-overridetype-fix type) (svar-overridetype-fix type2)))
                   (svarlist-nonoverride-p (alist-keys (svtv-fsm-namemap-env alist map type)) type2))
          :hints (("Goal" :use ((:instance svarlist-override-p-alist-keys-of-svtv-fsm-namemap-env))
                   :in-theory (disable svarlist-override-p-alist-keys-of-svtv-fsm-namemap-env)))))


  (defthm svtv-fsm-namemap-env-under-svex-envs-ovtestsimilar
    (implies (not (equal (svar-overridetype-fix type) :test))
             (svex-envs-ovtestsimilar (svtv-fsm-namemap-env alist map type) nil)))

  (defthm svtv-fsm-phase-inputs-under-svex-envs-ovtestsimilar
    (svex-envs-ovtestsimilar (svtv-fsm-phase-inputs inputs override-vals override-tests map)
                             (svtv-fsm-namemap-env override-tests map :test))
    :hints(("Goal" :in-theory (enable svtv-fsm-phase-inputs))))
  
  (defthm svtv-fsm-to-fsm-inputs-under-svex-envlists-ovtestsimilar
    (svex-envlists-ovtestsimilar (svtv-fsm-to-fsm-inputs inputs override-vals override-tests map)
                                 (svtv-fsm-namemap-envlist (take (len inputs) override-tests) map :test))
    :hints(("Goal" :in-theory (enable svtv-fsm-namemap-envlist
                                      svtv-fsm-to-fsm-inputs
                                      svex-envlists-ovtestsimilar))))

  (defthm svtv-spec-pipe-env->cycle-envs-under-svex-envlists-ovtestsimilar
    (svex-envlists-ovtestsimilar (svtv-spec-pipe-env->cycle-envs x pipe-env)
                                 (b* (((svtv-spec x)))
                                   (svtv-fsm-namemap-envlist
                                    (svex-alistlist-eval
                                     (svtv-spec->override-test-alists* x)
                                     pipe-env)
                                    x.namemap :test)))
    :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->cycle-envs
                                      svtv-spec->override-test-alists*
                                      take-of-svex-alistlist-eval))))

  (local (defthm lhprobe-map-overridemux-eval-of-fal-extract
           (implies (svarlist-p vars)
                    (equal (lhprobe-map-overridemux-eval (fal-extract vars bindings) envs outs)
                           (svex-env-reduce vars (lhprobe-map-overridemux-eval bindings envs outs))))
           :hints (("goal" :induct (fal-extract vars bindings)
                    :in-theory (enable svex-env-reduce-redef
                                       lhprobe-map-overridemux-eval
                                       fal-extract)))))

  (local (defthm svex-envs-agree-of-reduce-2
           (svex-envs-agree vars x (svex-env-reduce vars x))
           :hints(("Goal" :in-theory (enable svex-envs-agree-by-witness)))))


;; (SVEX-ENVLISTS-OVTESTS-OK
;;      ENVS
;;      (SVTV-SPEC-PIPE-ENV->CYCLE-ENVS
;;           (COUNTER-INVAR-SPEC)
;;           (LHPROBE-MAP-OVERRIDEMUX-EVAL
;;                (SVTV-SPEC-FSM-BINDINGS (COUNTER-INVAR-SPEC))
;;                ENVS
;;                (fsm-EVAL ENVS INITST
;;                               (SVTV-SPEC->CYCLE-FSM (COUNTER-INVAR-SPEC)))))
;;      (COUNTER-INVAR-RUN-OVERRIDEKEYS))


;; (SVEX-ENVLISTS-OVTESTS-OK
;;  '((((:VAR "sum1" . 32) . 15)) NIL)
;;  (SVTV-FSM-NAMEMAP-ENVLIST
;;       (SVEX-ALISTLIST-EVAL
;;            (SVTV-SPEC->OVERRIDE-TEST-ALISTS* (COUNTER-INVAR-SPEC))
;;            (LHPROBE-MAP-OVERRIDEMUX-EVAL
;;                 (SVTV-SPEC-FSM-BINDINGS (COUNTER-INVAR-SPEC))
;;                 ENVS
;;                 (fsm-EVAL ENVS INITST
;;                                (SVTV-SPEC->CYCLE-FSM (COUNTER-INVAR-SPEC)))))
;;       (SVTV-SPEC->NAMEMAP (COUNTER-INVAR-SPEC))
;;       :TEST)
;;  (COUNTER-INVAR-RUN-OVERRIDEKEYS))

  (defthm alistlist-eval-of-test-alists-under-bindings
    (implies (And (syntaxp (and (consp test-alists)
                                (equal (car test-alists) 'svtv-spec->override-test-alists*)))
                  (equal test-alists-eval (force-execute test-alists))
                  (syntaxp (quotep test-alists-eval))
                  (svex-alistlist-noncall-p test-alists-eval)
                  (equal bindings-eval (force-execute bindings))
                  (syntaxp (quotep bindings-eval))
                  (equal alist-vars (svex-alistlist-vars test-alists-eval))
                  (syntaxp (quotep alist-vars))
                  (equal bindings-trim (acl2::fal-extract alist-vars bindings-eval))
                  (equal bindings-vars (lhprobe-map-vars bindings-trim))
                  (svarlist-override-p bindings-vars :test)
                  (svex-envlists-ovtestsimilar norm-envs (double-rewrite envs))
                  (syntaxp (quotep norm-envs)))
             (svex-envlists-ovtestsimilar
              (SVTV-FSM-NAMEMAP-ENVLIST
               (svex-alistlist-eval
                test-alists
                (lhprobe-map-overridemux-eval bindings envs outs))
               namemap :test)
              (force-execute
               (svtv-fsm-namemap-envlist
                (svex-alistlist-eval test-alists-eval
                                     (lhprobe-map-eval bindings-trim (make-fast-alists norm-envs)))
                namemap :test))))
    :hints (("goal" :use ((:instance lhprobe-map-overridemux-eval-of-fal-extract
                           (vars (svex-alistlist-vars test-alists)))
                          (:instance svex-alistlist-eval-when-envs-agree
                           (x test-alists)
                           (env1 (lhprobe-map-overridemux-eval bindings envs outs))
                           (env2 (lhprobe-map-eval (fal-extract (svex-alistlist-vars test-alists) bindings) envs)))
                          (:instance lhprobe-map-eval-when-override-test-vars-and-ovtestsimilar
                           (x (fal-extract (svex-alistlist-vars test-alistS) bindings))
                           (envs1 envs) (envs2 norm-envs))
                          ;; (:instance SVEX-ALISTLIST-EVAL-1MASK-EQUIV-CONGRUENCE-WHEN-NONCALL-P
                          ;;  (x test-alists)
                          ;;  (env1 (lhprobe-map-eval (fal-extract (svex-alistlist-vars test-alists) bindings) envs))
                          ;;  (env2 (lhprobe-map-eval (fal-extract (svex-alistlist-vars test-alists) bindings) norm-envs)))
                          )
             :in-theory (e/d (svtv-fsm-namemap-envlist-ovtestsimilar-congruence
                              force-execute)
                             (lhprobe-map-overridemux-eval-of-fal-extract)))))


  (local (defthm svex-envs-agree-of-append-same
           (iff (svex-envs-agree vars (append env1 env2) (append env1 env3))
                (svex-envs-agree (set-difference-equal (svarlist-fix vars)
                                                       (alist-keys (svex-env-fix env1)))
                                 env2 env3))
           :hints (("goal" :in-theory (e/d ((:i len)
                                            svex-env-lookup-of-append
                                            svex-env-boundp-iff-member-alist-keys)
                                           (acl2::alist-keys-member-hons-assoc-equal))
                    :induct (len vars)
                    :expand ((:free (env1 env2) (svex-envs-agree vars env1 env2))
                             (svarlist-fix vars)
                             (:free (b) (set-difference-equal nil b))
                             (:free (a b c) (set-difference-equal (cons a b) c))
                             (:free (a b) (svex-envs-agree (cons a b) env2 env3))
                             (svex-envs-agree nil env2 env3))))))

  (local (defthm svex-envs-1mask-equiv-of-append-same
           (implies (svex-envs-1mask-equiv x y)
                    (equal (svex-envs-1mask-equiv (append z x) (append z y)) t))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause)))
                          :in-theory (enable svex-env-lookup-of-append))))))

  (defthm alistlist-eval-of-test-alists-under-bindings-gen
    (implies (And (syntaxp (and (consp test-alists)
                                (equal (car test-alists) 'svtv-spec->override-test-alists*)
                                (quotep test-env)))
                  (equal test-alists-eval (force-execute test-alists))
                  (syntaxp (quotep test-alists-eval))
                  (svex-alistlist-noncall-p test-alists-eval)
                  (equal bindings-eval (force-execute bindings))
                  (syntaxp (quotep bindings-eval))
                  (equal alist-vars (svex-alistlist-vars test-alists-eval))
                  (syntaxp (quotep alist-vars))
                  (equal env-vars (alist-keys (svex-env-fix test-env)))
                  (syntaxp (quotep env-vars))
                  (equal relevant-vars (acl2::hons-set-diff alist-vars env-vars))
                  (equal bindings-trim (acl2::fal-extract relevant-vars bindings-eval))
                  (equal bindings-vars (lhprobe-map-vars bindings-trim))
                  (svarlist-override-p bindings-vars :test)
                  (svex-envlists-ovtestsimilar norm-envs (double-rewrite envs))
                  (syntaxp (quotep norm-envs)))
             (svex-envlists-ovtestsimilar
              (SVTV-FSM-NAMEMAP-ENVLIST
               (svex-alistlist-eval
                test-alists
                (append test-env
                        (lhprobe-map-overridemux-eval bindings envs outs)))
               namemap :test)
              (force-execute
               (svtv-fsm-namemap-envlist
                (svex-alistlist-eval test-alists-eval
                                     (append test-env
                                             (lhprobe-map-eval bindings-trim (make-fast-alists norm-envs))))
                namemap :test))))
    :hints (("goal" :use ((:instance lhprobe-map-overridemux-eval-of-fal-extract
                           (vars (acl2::hons-set-diff (svex-alistlist-vars test-alists)
                                                      (alist-keys (svex-env-fix test-env)))))
                          (:instance svex-alistlist-eval-when-envs-agree
                           (x test-alists)
                           (env1 (append test-env (lhprobe-map-overridemux-eval bindings envs outs)))
                           (env2 (append test-env
                                         (lhprobe-map-eval
                                          (fal-extract
                                           (acl2::hons-set-diff (svex-alistlist-vars test-alists)
                                                                (alist-keys (svex-env-fix test-env)))
                                           bindings) envs))))
                          (:instance lhprobe-map-eval-when-override-test-vars-and-ovtestsimilar
                           (x (fal-extract
                               (acl2::hons-set-diff (svex-alistlist-vars test-alists)
                                                    (alist-keys (svex-env-fix test-env)))
                               bindings))
                           (envs1 envs) (envs2 norm-envs))
                          ;; (:instance SVEX-ALISTLIST-EVAL-1MASK-EQUIV-CONGRUENCE-WHEN-NONCALL-P
                          ;;  (x test-alists)
                          ;;  (env1 (lhprobe-map-eval (fal-extract (svex-alistlist-vars test-alists) bindings) envs))
                          ;;  (env2 (lhprobe-map-eval (fal-extract (svex-alistlist-vars test-alists) bindings) norm-envs)))
                          )
             :in-theory (e/d (svtv-fsm-namemap-envlist-ovtestsimilar-congruence
                              force-execute)
                             (lhprobe-map-overridemux-eval-of-fal-extract
                              lhprobe-map-eval-when-override-test-vars-and-ovtestsimilar
                              svex-alistlist-eval-when-envs-agree))
             :do-not-induct t))))
           ;; ?


(define svex-envs-check-ovtests-ok-rec ((keys svarlist-p)
                                        (x svex-env-p)
                                        (y svex-env-p)
                                        (overridekey-set))
  (if (atom keys)
      t
    (and (b* ((k (car keys)))
           (or (not (svar-override-p k :test))
               (if (hons-get (svar-fix k) overridekey-set)
                   (4vec-muxtest-subsetp (svex-env-lookup k x)
                                         (svex-env-lookup k y))
                 (4vec-1mask-equiv (svex-env-lookup k x)
                                   (svex-env-lookup k y)))))
         (svex-envs-check-ovtests-ok-rec (cdr keys) x y overridekey-set)))
  ///

  (local (defthm 4vec-fix-equal-svex-env-lookup-forward
           (implies (equal (4vec-fix x) (svex-env-lookup v y))
                    (4vec-equiv x (svex-env-lookup v y)))
           :rule-classes :forward-chaining))

  (local (defthm svex-envs-ovtests-ok-of-cons
           (implies (and (iff (svex-env-boundp k x) (svex-env-boundp k y))
                         (or (not (svex-env-boundp k x))
                             (and (4vec-equiv vx (svex-env-lookup k x))
                                  (4vec-equiv vy (svex-env-lookup k y)))))
                    (iff (svex-envs-ovtests-ok (cons (cons k vx) x)
                                               (cons (cons k vy) y)
                                               overridekeys)
                         (and (or (not (svar-p k))
                                  (not (svar-override-p k :test))
                                  (if (svarlist-member-nonoverride k overridekeys)
                                      (4vec-muxtest-subsetp vx vy)
                                    (4vec-1mask-equiv vx vy)))
                              (svex-envs-ovtests-ok x y overridekeys))))
           :hints (("goal" :in-theory (e/d (svex-env-lookup-of-cons-split
                                            svex-env-lookup-when-not-boundp)
                                           (svex-envs-ovtests-ok-necc)))
                   (and stable-under-simplificationp
                        (b* ((lit (assoc 'svex-envs-ovtests-ok clause))
                             (wit (if lit
                                      `(svex-envs-ovtests-ok-witness . ,(cdr lit))
                                    'k))
                             (other-x (if (or (not lit) (eq (cadr lit) 'x)) '(cons (cons k vx) x) 'x))
                             (other-y (if (or (not lit) (eq (cadr lit) 'x)) '(cons (cons k vy) y) 'y)))
                          `(,@(and lit `(:expand (,lit)))
                            :use ((:instance svex-envs-ovtests-ok-necc
                                   (k ,wit) (x ,other-x) (y ,other-y)))))))))


  (local (Defthm member-of-svarlist-change-override-rw
           (implies (syntaxp (not (equal type ''nil)))
                    (iff (member-equal v (svarlist-change-override x type))
                         (and (svar-p v)
                              (svar-override-p v type)
                              (svarlist-member-nonoverride v x))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             equal-of-svar-change-override)))))

  (defthm svex-envs-ovtests-ok-of-nils
    (svex-envs-ovtests-ok nil nil keys)
    :hints(("Goal" :in-theory (enable svex-envs-ovtests-ok))))

  (defthm svex-envs-check-ovtests-ok-rec-correct
    (iff (svex-envs-check-ovtests-ok-rec keys x y (pairlis$ (svarlist-change-override overridekeys :test) nil))
         (svex-envs-ovtests-ok (svex-env-extract keys x)
                               (svex-env-extract keys y)
                               overridekeys))
    :hints(("Goal" :in-theory (enable svex-env-extract))))

  (defthm svex-envs-ovtests-ok-of-extract-superset-1
    (implies (subsetp-equal (alist-keys (svex-env-fix x)) (svarlist-fix keys))
             (iff (svex-envs-ovtests-ok (svex-env-extract keys x) y overridekeys)
                  (svex-envs-ovtests-ok x y overridekeys)))
    :hints (("goal" :in-theory (e/d (svex-env-lookup-of-cons-split
                                     svex-env-lookup-when-not-boundp
                                     svex-env-boundp-iff-member-alist-keys)
                                    (svex-envs-ovtests-ok-necc
                                     acl2::alist-keys-member-hons-assoc-equal)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'svex-envs-ovtests-ok clause))
                      (wit `(svex-envs-ovtests-ok-witness . ,(cdr lit)))
                      (other-x (if (eq (cadr lit) 'x) '(svex-env-extract keys x) 'x)))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtests-ok-necc
                            (k ,wit) (x ,other-x) (y y))))))))

  (defthm svex-envs-ovtests-ok-of-extract-superset-2
    (implies (subsetp-equal (alist-keys (svex-env-fix y)) (svarlist-fix keys))
             (iff (svex-envs-ovtests-ok x (svex-env-extract keys y) overridekeys)
                  (svex-envs-ovtests-ok x y overridekeys)))
    :hints (("goal" :in-theory (e/d (svex-env-lookup-of-cons-split
                                     svex-env-lookup-when-not-boundp
                                     svex-env-boundp-iff-member-alist-keys)
                                    (svex-envs-ovtests-ok-necc
                                     acl2::alist-keys-member-hons-assoc-equal)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'svex-envs-ovtests-ok clause))
                      (wit `(svex-envs-ovtests-ok-witness . ,(cdr lit)))
                      (other-y (if (eq (caddr lit) 'y) '(svex-env-extract keys y) 'y)))
                   `(:expand (,lit)
                     :use ((:instance svex-envs-ovtests-ok-necc
                            (k ,wit) (y ,other-y) (x x)))))))))


(define svex-envs-check-ovtests-ok ((x svex-env-p)
                                    (y svex-env-p)
                                    (overridekey-set))
  (svex-envs-check-ovtests-ok-rec (append (alist-keys (svex-env-fix x))
                                          (alist-keys (svex-env-fix y)))
                                  x y overridekey-set)
  ///
  (defthm svex-envs-check-ovtests-ok-correct
    (iff (svex-envs-check-ovtests-ok x y (pairlis$ (svarlist-change-override overridekeys :test) nil))
         (svex-envs-ovtests-ok x y overridekeys))
    :hints(("Goal" :in-theory (disable svex-env-extract-of-append)))))

(define svex-envlists-check-ovtests-ok-rec ((x svex-envlist-p)
                                            (y svex-envlist-p)
                                            (overridekey-set))
  (if (atom x)
      (atom y)
    (And (consp y)
         (svex-envs-check-ovtests-ok (car x) (car y) overridekey-set)
         (svex-envlists-check-ovtests-ok-rec (cdr x) (cdr y) overridekey-set)))
  ///

  (defthm svex-envlists-check-ovtests-ok-rec-correct
    (iff (svex-envlists-check-ovtests-ok-rec x y (pairlis$ (svarlist-change-override overridekeys :test) nil))
         (svex-envlists-ovtests-ok x y overridekeys))
    :hints(("Goal" :in-theory (enable svex-envlists-ovtests-ok)))))


(define svex-envlists-check-ovtests-ok ((x svex-envlist-p)
                                        (y svex-envlist-p)
                                        (overridekeys svarlist-p))
  (svex-envlists-check-ovtests-ok-rec (make-fast-alists x)
                                      (make-fast-alists y)
                                      (make-fast-alist (pairlis$ (svarlist-change-override overridekeys :test) nil)))
  ///
  (defthmd svex-envlists-check-ovtests-ok-correct
    (iff (svex-envlists-check-ovtests-ok x y overridekeys)
         (svex-envlists-ovtests-ok x y overridekeys))))


(defthm svex-envlists-ovtests-ok-when-variable-free
  (implies (syntaxp (and (cmr::term-variable-free-p x)
                         (cmr::term-variable-free-p y)
                         (cmr::term-variable-free-p overridekeys)))
           (equal (svex-envlists-ovtests-ok x y overridekeys)
                  (force-execute (svex-envlists-check-ovtests-ok x y overridekeys))))
  :hints(("Goal" :in-theory (enable force-execute
                                    svex-envlists-check-ovtests-ok-correct))))



(defthm svex-envlist-all-keys-of-append
  (equal (svex-envlist-all-keys (append x y))
         (append (svex-envlist-all-keys x)
                 (svex-envlist-all-keys y)))
  :hints(("Goal" :in-theory (enable svex-envlist-all-keys))))

(defthm svex-envlist-all-keys-of-svtv-cycle-fsm-inputs-no-i/o
  (implies (svtv-cyclephaselist-no-i/o-phase phases)
           (set-equiv (svex-envlist-all-keys
                       (svtv-cycle-fsm-inputs ins phases))
                      (svtv-cyclephaselist-keys phases)))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-keys
                                    svtv-cyclephaselist-no-i/o-phase
                                    svtv-cycle-fsm-inputs
                                    svex-envlist-all-keys
                                    svtv-cycle-step-fsm-inputs))))

(defthm svex-envlist-all-keys-of-svtv-cycle-fsm-inputs
  (implies (svtv-cyclephaselist-unique-i/o-phase phases)
           (set-equiv (svex-envlist-all-keys
                       (svtv-cycle-fsm-inputs ins phases))
                      (append (alist-keys (svex-env-fix ins))
                              (svtv-cyclephaselist-keys phases))))
  :hints(("Goal" :in-theory (enable svtv-cyclephaselist-keys
                                    svtv-cyclephaselist-unique-i/o-phase
                                    svtv-cycle-fsm-inputs
                                    svex-envlist-all-keys
                                    svtv-cycle-step-fsm-inputs))))

(defthm svex-envlist-all-keys-of-svtv-cycle-run-fsm-inputs
  (implies (svtv-cyclephaselist-unique-i/o-phase phases)
           (set-equiv (svex-envlist-all-keys
                       (svtv-cycle-run-fsm-inputs ins phases))
                      (and (Consp ins)
                           (append (svex-envlist-all-keys ins)
                                   (svtv-cyclephaselist-keys phases)))))
  :hints(("Goal" :in-theory (enable svtv-cycle-run-fsm-inputs
                                    svex-envlist-all-keys))))

(defthm svarlist-remove-override-of-append
  (equal (svarlist-remove-override (append x y) type)
         (append (svarlist-remove-override x type)
                 (svarlist-remove-override y type)))
  :hints(("Goal" :in-theory (enable svarlist-remove-override))))

(defthm alist-keys-of-svex-env-remove-override
  (equal (alist-keys (svex-env-remove-override x type))
         (svarlist-remove-override (alist-keys (svex-env-fix x)) type))
  :hints(("Goal" :in-theory (enable svex-env-remove-override
                                    svarlist-remove-override)
          :expand ((svex-env-fix x)
                   (:free (a b) (alist-keys (cons a b))))
          :induct t)))

(defthm svex-envlist-all-keys-of-remove-override
  (equal (svex-envlist-all-keys (svex-envlist-remove-override envs type))
         (svarlist-remove-override (svex-envlist-all-keys envs) type))
  :hints(("Goal" :in-theory (enable svex-envlist-all-keys svex-envlist-remove-override)
          :expand ((svarlist-remove-override nil type)))))


(defthm svarlist-nonoverride-p-of-svarlist-remove-override-same
  (svarlist-nonoverride-p (svarlist-remove-override x type) type)
  :hints(("Goal" :in-theory (e/d (svarlist-nonoverride-p
                                  svarlist-remove-override)))))

(defthm svarlist-nonoverride-p-of-svarlist-remove-override
  (iff (svarlist-nonoverride-p (svarlist-remove-override x type1) type2)
       (if (svar-overridetype-equiv type1 type2)
           t
         (svarlist-nonoverride-p x type2)))
  :hints(("Goal" :in-theory (e/d (svarlist-nonoverride-p
                                    svarlist-remove-override
                                    svar-override-p-when-other)
                                 (svar-overridetype-equiv))
          :induct t)))


(defcong svex-envs-similar svex-envs-similar (svex-env-x-override x y) 1
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(defsection svex-alist-all-xes-p
  (local (std::set-define-current-function svex-alist-all-xes-p))
  (local (in-theory (enable svex-alist-all-xes-p)))

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
            :do-not-induct t)))

  (local (in-theory (enable svex-alist-fix))))

(defcong svex-envlists-equivalent equal (svtv-spec-cycle-outs->pipe-out x outs) 2
  :hints(("Goal" :in-theory (enable svtv-spec-cycle-outs->pipe-out))))

;; (SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH
;;  (COUNTER-INVAR-RUN-TRIPLEMAPLIST)
;;  (LHPROBE-MAP-OVERRIDEMUX-EVAL
;;   (SVTV-SPEC-FSM-BINDINGS (COUNTER-INVAR-SPEC))
;;   ENVS
;;   (fsm-EVAL ENVS INITST
;;                  (SVTV-SPEC->CYCLE-FSM (COUNTER-INVAR-SPEC))))
;;  '((SUM1-OVR . -1)))





(defsection svex-envs-ovtestequiv
  ;; (def-universal-equiv svex-envs-ovtestequiv
  ;;   :qvars (k)
  ;;   :equiv-terms ((4vec-1mask-equiv (svex-env-lookup k x))))

  (defun-sk svex-envs-ovtestequiv (x y)
    (forall k
            (implies (svar-override-p k :test)
                     (equal (equal (svex-env-lookup k x)
                                   (svex-env-lookup k y))
                            t)))
    :rewrite :direct)


  (in-theory (disable svex-envs-ovtestequiv
                      svex-envs-ovtestequiv-necc))

  (local (defthm svex-envs-ovtestequiv-necc-tmp
           (implies (and (svex-envs-ovtestequiv x y)
                         (svar-override-p k :test))
                    (equal (svex-env-lookup k x)
                           (svex-env-lookup k y)))
           :hints(("Goal" :in-theory (enable svex-envs-ovtestequiv-necc)))))

  (defequiv svex-envs-ovtestequiv
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-envs-ovtestequiv-necc)))))

  (local (in-theory (disable svex-envs-ovtestequiv-necc-tmp)))

  (defrefinement  svex-envs-similar svex-envs-ovtestequiv
    :hints(("Goal" :in-theory (enable svex-envs-ovtestequiv))))

  (defrefinement  svex-envs-ovtestequiv svex-envs-ovtestsimilar
    :hints(("Goal" :in-theory (enable svex-envs-ovtestsimilar)
            :use ((:instance svex-envs-ovtestequiv-necc
                   (k (svex-envs-ovtestsimilar-witness x y))))))))


(define svex-envlists-ovtestequiv ((x svex-envlist-p) (y svex-envlist-p))
  (if (Atom x)
      (atom y)
    (and (consp y)
         (ec-call (svex-envs-ovtestequiv (car x) (car y)))
         (svex-envlists-ovtestequiv (cdr x) (cdr y))))
  ///
  (defequiv svex-envlists-ovtestequiv :otf-flg t)

  (defrefinement svex-envlists-similar svex-envlists-ovtestequiv
    :hints(("Goal" :in-theory (enable svex-envlists-similar-rec))))

  (defrefinement svex-envlists-ovtestequiv svex-envlists-ovtestsimilar
    :hints(("Goal" :in-theory (enable svex-envlists-ovtestsimilar)))))



(define svtv-override-triple-relevant-vars ((triple svtv-override-triple-p)
                                            (spec svex-env-p))
  :returns (vars svarlist-p)
  (b* (((svtv-override-triple triple)))
    (if (equal (svex-eval triple.val spec) (4vec-x))
        (svex-vars triple.test)
      (append (svex-vars triple.test)
              (svex-vars triple.val))))
  ///
  (defthm svtv-override-triple-relevant-vars-correct
    (implies (subsetp-equal (svtv-override-triple-relevant-vars triple spec) (svarlist-fix vars))
             (equal (svtv-override-triple-envs-match triple (svex-env-reduce vars env) spec)
                    (svtv-override-triple-envs-match triple env spec)))
    :hints(("Goal" :in-theory (enable svtv-override-triple-envs-match)))))

(define svtv-override-triplemap-relevant-vars ((triplemap svtv-override-triplemap-p)
                                               (spec svex-env-p))
  :returns (vars svarlist-p)
  (if (atom triplemap)
      nil
    (append (and (mbt (and (Consp (car triplemap))
                           (svar-p (caar triplemap))))
                 (svtv-override-triple-relevant-vars (cdar triplemap) spec))
            (svtv-override-triplemap-relevant-vars (cdr triplemap) spec)))
  ///
  (defthm svtv-override-triplemap-relevant-vars-correct
    (implies (subsetp-equal (svtv-override-triplemap-relevant-vars triplemap spec) (svarlist-fix vars))
             (equal (svtv-override-triplemap-envs-match triplemap (svex-env-reduce vars env) spec)
                    (svtv-override-triplemap-envs-match triplemap env spec)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemap-envs-match))))

  (local (in-theory (enable svtv-override-triplemap-fix))))


(define svtv-override-triplemaplist-relevant-vars ((triplemaps svtv-override-triplemaplist-p)
                                                   (spec svex-env-p))
  :returns (vars svarlist-p)
  (if (atom triplemaps)
      nil
    (append (svtv-override-triplemap-relevant-vars (car triplemaps) spec)
            (svtv-override-triplemaplist-relevant-vars (cdr triplemaps) spec)))
  ///
  (defthm svtv-override-triplemaplist-relevant-vars-correct
    (implies (subsetp-equal (svtv-override-triplemaplist-relevant-vars triplemaps spec) (svarlist-fix vars))
             (equal (svtv-override-triplemaplist-envs-match triplemaps (svex-env-reduce vars env) spec)
                    (svtv-override-triplemaplist-envs-match triplemaps env spec)))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-envs-match)))))


(define svtv-override-triple-test-only-p ((triple svtv-override-triple-p)
                                          (spec svex-env-p))
  (b* (((svtv-override-triple triple)))
    (svex-case triple.test
      :call nil
      :otherwise (or (svex-case triple.val :quote)
                     (equal (svex-eval triple.val spec) (4vec-x)))))
  ///
  (defthm svtv-override-triple-test-only-p-correct
    (implies (and (svtv-override-triple-test-only-p triple spec)
                  (svex-envs-1mask-equiv env1 env2))
             (equal (equal (svtv-override-triple-envs-match triple env1 spec)
                           (svtv-override-triple-envs-match triple env2 spec))
                    t))
    :hints(("Goal" :in-theory (enable svtv-override-triple-envs-match)
            :expand ((:free (env) (svex-eval (svtv-override-triple->test triple) env)))))))



(define svtv-override-triplemap-test-only-p ((triplemap svtv-override-triplemap-p)
                                               (spec svex-env-p))
  (if (atom triplemap)
      t
    (and (or (not (mbt (and (Consp (car triplemap))
                            (svar-p (caar triplemap)))))
             (svtv-override-triple-test-only-p (cdar triplemap) spec))
         (svtv-override-triplemap-test-only-p (cdr triplemap) spec)))
  ///
  (defthm svtv-override-triplemap-test-only-p-correct
    (implies (and (svtv-override-triplemap-test-only-p triplemap spec)
                  (svex-envs-1mask-equiv env1 env2))
             (equal (equal (svtv-override-triplemap-envs-match triplemap env1 spec)
                           (svtv-override-triplemap-envs-match triplemap env2 spec))
                    t))
    :hints(("Goal" :in-theory (enable svtv-override-triplemap-envs-match)
            :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance svtv-override-triple-test-only-p-correct
                         (triple (cdar triplemap))))
                  :in-theory (disable svtv-override-triple-test-only-p-correct)))))

  (local (in-theory (enable svtv-override-triplemap-fix))))


(define svtv-override-triplemaplist-test-only-p ((triplemaps svtv-override-triplemaplist-p)
                                                   (spec svex-env-p))
  (if (atom triplemaps)
      t
    (and (svtv-override-triplemap-test-only-p (car triplemaps) spec)
         (svtv-override-triplemaplist-test-only-p (cdr triplemaps) spec)))
  ///
  (defthm svtv-override-triplemaplist-test-only-p-correct
    (implies (and (svtv-override-triplemaplist-test-only-p triplemaps spec)
                  (svex-envs-1mask-equiv env1 env2))
             (equal (equal (svtv-override-triplemaplist-envs-match triplemaps env1 spec)
                           (svtv-override-triplemaplist-envs-match triplemaps env2 spec))
                    t))
    :hints(("Goal" :in-theory (enable svtv-override-triplemaplist-envs-match)
            :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance svtv-override-triplemap-test-only-p-correct
                         (triplemap (car triplemaps))))
                  :in-theory (disable svtv-override-triplemap-test-only-p-correct))))))


;; (SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH
;;  (COUNTER-INVAR-RUN-TRIPLEMAPLIST)
;;  (LHPROBE-MAP-OVERRIDEMUX-EVAL
;;   (SVTV-SPEC-FSM-BINDINGS (COUNTER-INVAR-SPEC))
;;   ENVS
;;   (fsm-EVAL ENVS INITST
;;                  (SVTV-SPEC->CYCLE-FSM (COUNTER-INVAR-SPEC))))
;;  '((SUM1-OVR . -1)))


(defthm svtv-override-triplemaplist-envs-match-relevant-vars
  (implies (and (syntaxp (and (quotep spec)
                              (not (quotep env))))
                (equal triplemaps-eval (force-execute triplemaps))
                (syntaxp (quotep triplemaps-eval))
                (equal spec-fast (make-fast-alist spec))
                (equal relevant-vars (svtv-override-triplemaplist-relevant-vars triplemaps-eval spec-fast))
                (syntaxp (quotep relevant-vars))
                ;; need some rules here!
                (equal env-trim (svex-env-reduce relevant-vars env))
                (syntaxp (progn$ (cw "relevant-vars: ~x0~%" relevant-vars)
                                 (cw "env-trim: ~x0~%" env-trim)
                                 (quotep env-trim))))
           (equal (svtv-override-triplemaplist-envs-match triplemaps env spec)
                  (force-execute
                   (svtv-override-triplemaplist-envs-match triplemaps (make-fast-alist env-trim) spec-fast))))
  :hints(("Goal" :in-theory (enable force-execute))))


(defthmd svex-env-reduce-of-append-envs-under-svex-envs-1mask-equiv-special
  (implies (syntaxp (and (quotep vars) (quotep env1)))
           (svex-envs-1mask-equiv (svex-env-reduce vars (append env1 env2))
                                  (append (svex-env-reduce vars env1)
                                          (svex-env-reduce
                                           (acl2::hons-set-diff (svarlist-fix vars) (alist-keys (Svex-env-fix env1)))
                                           env2))))
  :hints(("Goal" :in-theory (e/d (svex-envs-1mask-equiv
                                  svex-env-boundp-iff-member-alist-keys)
                                 (acl2::alist-keys-member-hons-assoc-equal))
          :do-not-induct t)))

(defcong svex-envs-1mask-equiv svex-envs-1mask-equiv (append x y) 2
  :hints ((And stable-under-simplificationp
               `(:expand (,(car (last clause)))))))

(defthm svtv-override-triplemaplist-envs-match-relevant-vars-test-only
  (implies (and (syntaxp (and (quotep spec)
                              (not (quotep env))))
                (equal triplemaps-eval (force-execute triplemaps))
                (syntaxp (quotep triplemaps-eval))
                (equal spec-fast (make-fast-alist spec))
                (svtv-override-triplemaplist-test-only-p triplemaps-eval spec-fast)
                (equal relevant-vars (svtv-override-triplemaplist-relevant-vars triplemaps-eval spec-fast))
                (syntaxp (quotep relevant-vars))
                ;; need some rules here!
                (equal env-trim1 (svex-env-reduce relevant-vars env))
                (svex-envs-1mask-equiv env-trim (double-rewrite env-trim1))
                (syntaxp (progn$ (cw "relevant-vars: ~x0~%" relevant-vars)
                                 (cw "env-trim1: ~x0~%" env-trim1)
                                 (cw "env-trim: ~x0~%" env-trim)
                                 (quotep env-trim))))
           (equal (svtv-override-triplemaplist-envs-match triplemaps env spec)
                  (force-execute
                   (svtv-override-triplemaplist-envs-match triplemaps (make-fast-alist env-trim) spec-fast))))
  :hints(("Goal" :in-theory (e/d (force-execute) (svtv-override-triplemaplist-test-only-p-correct))
          :use ((:instance svtv-override-triplemaplist-test-only-p-correct
                 (env1 env-trim)
                 (env2 (svex-env-reduce
                        (svtv-override-triplemaplist-relevant-vars triplemaps spec)
                        env)))))))


(defthm svex-env-reduce-of-lhprobe-map-overridemux-eval
  (equal (svex-env-reduce vars (lhprobe-map-overridemux-eval bindings envs outs))
         (lhprobe-map-overridemux-eval (fal-extract (svarlist-fix vars) bindings) envs outs))
  :hints(("Goal" :in-theory (enable svarlist-fix)
          :induct (svarlist-fix vars)
          :expand ((:free (a b) (fal-extract (cons a b) bindings))
                   (:free (a b ev) (svex-env-reduce (cons a b) ev))
                   (:free (ev) (svex-env-reduce vars ev))
                   (fal-extract nil bindings)
                   (:free (a b) (lhprobe-map-overridemux-eval (cons a b) envs outs))
                   (lhprobe-map-overridemux-eval nil envs outs)))))

(defthm fal-extract-const-of-svtv-spec-fsm-bindings
  (implies (and (syntaxp (quotep vars))
                (equal bindings (force-execute (svtv-spec-fsm-bindings x)))
                (syntaxp (quotep bindings)))
           (equal (fal-extract vars (svtv-spec-fsm-bindings x))
                  (fal-extract vars (make-fast-alist bindings))))
  :hints(("Goal" :in-theory (enable force-execute))))


(defthmd lhatom-eval-zero-svex-envlists-ovtestequiv-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhatom-vars lhatom) :test)
                (svex-envs-ovtestequiv env1 env2))
           (equal (equal (lhatom-eval-zero lhatom env1)
                         (lhatom-eval-zero lhatom env2))
                  t))
  :hints(("Goal" :in-theory (enable lhatom-eval-zero
                                    lhatom-vars
                                    svarlist-override-p)
          :use ((:instance svex-envs-ovtestequiv-necc
                 (k (lhatom-var->name lhatom))
                 (x env1) (y env2))))))

(defthmd lhatom-eval-zero-svex-envlists-ovtestsimilar-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhatom-vars lhatom) :test)
                (svex-envs-ovtestsimilar env1 env2))
           (equal (4vec-1mask-equiv (lhatom-eval-zero lhatom env1)
                                    (lhatom-eval-zero lhatom env2))
                  t))
  :hints(("Goal" :in-theory (enable lhatom-eval-zero
                                    lhatom-vars
                                    svarlist-override-p)
          :use ((:instance svex-envs-ovtestsimilar-necc
                 (k (lhatom-var->name lhatom))
                 (x env1) (y env2))))))

(defthm lhs-eval-signx-svex-envlists-ovtestequiv-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhs-vars lhs) :test)
                (svex-envs-ovtestequiv env1 env2))
           (equal (equal (lhs-eval-signx lhs env1)
                         (lhs-eval-signx lhs env2))
                  t))
  :hints(("Goal" :in-theory (enable lhs-vars)
          :induct (lhs-vars lhs)
          :expand ((:free (env) (lhs-eval-signx lhs env))))
         (and stable-under-simplificationp
              '(:use ((:instance lhatom-eval-zero-svex-envlists-ovtestequiv-congruence-when-only-test-vars
                       (lhatom (lhrange->atom (car lhs)))))))))

(defthm lhs-eval-signx-svex-envlists-ovtestsimilar-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhs-vars lhs) :test)
                (svex-envs-ovtestsimilar env1 env2))
           (equal (4vec-1mask-equiv (lhs-eval-signx lhs env1)
                                    (lhs-eval-signx lhs env2))
                  t))
  :hints(("Goal" :in-theory (enable lhs-vars)
          :induct (lhs-vars lhs)
          :expand ((:free (env) (lhs-eval-signx lhs env))))
         (and stable-under-simplificationp
              '(:use ((:instance lhatom-eval-zero-svex-envlists-ovtestsimilar-congruence-when-only-test-vars
                       (lhatom (lhrange->atom (car lhs)))))))))

(defthm lhs-eval-zx-svex-envlists-ovtestequiv-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhs-vars lhs) :test)
                (svex-envs-ovtestequiv env1 env2))
           (equal (equal (lhs-eval-zx lhs env1)
                         (lhs-eval-zx lhs env2))
                  t))
  :hints(("Goal" :in-theory (enable lhs-vars)
          :induct (lhs-vars lhs)
          :expand ((:free (env) (lhs-eval-zx lhs env))))
         (and stable-under-simplificationp
              '(:use ((:instance lhatom-eval-zero-svex-envlists-ovtestequiv-congruence-when-only-test-vars
                       (lhatom (lhrange->atom (car lhs)))))))))


(defthm lhs-eval-zx-svex-envlists-ovtestsimilar-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhs-vars lhs) :test)
                (svex-envs-ovtestsimilar env1 env2))
           (equal (4vec-1mask-equiv (lhs-eval-zx lhs env1)
                                    (lhs-eval-zx lhs env2))
                  t))
  :hints(("Goal" :in-theory (enable lhs-vars)
          :induct (lhs-vars lhs)
          :expand ((:free (env) (lhs-eval-zx lhs env))))
         (and stable-under-simplificationp
              '(:use ((:instance lhatom-eval-zero-svex-envlists-ovtestsimilar-congruence-when-only-test-vars
                       (lhatom (lhrange->atom (car lhs)))))))))

(defthm svex-envs-ovtestequiv-nth-when-svex-envlists-ovtestequiv
  (implies (svex-envlists-ovtestequiv envs1 envs2)
           (equal (svex-envs-ovtestequiv (nth n envs1) (nth n envs2)) t))
  :hints(("Goal" :in-theory (enable svex-envlists-ovtestequiv))))

(defthm lhprobe-eval-svex-envlists-ovtestequiv-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhprobe-vars lhprobe) :test)
                (svex-envlists-ovtestequiv envs1 envs2))
           (equal (equal (lhprobe-eval lhprobe envs1)
                         (lhprobe-eval lhprobe envs2))
                  t))
  :hints(("Goal" :in-theory (enable lhprobe-eval
                                    lhprobe-vars))))

(defthm lhprobe-map-eval-svex-envlists-ovtestequiv-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhprobe-map-vars lhmap) :test)
                (svex-envlists-ovtestequiv envs1 envs2))
           (equal (equal (lhprobe-map-eval lhmap envs1)
                         (lhprobe-map-eval lhmap envs2))
                  t))
  :hints(("Goal" :in-theory (enable lhprobe-map-eval
                                    lhprobe-map-vars))))


(defthm lhprobe-eval-svex-envlists-ovtestsimilar-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhprobe-vars lhprobe) :test)
                (svex-envlists-ovtestsimilar envs1 envs2))
           (equal (4vec-1mask-equiv (lhprobe-eval lhprobe envs1)
                                    (lhprobe-eval lhprobe envs2))
                  t))
  :hints(("Goal" :in-theory (enable lhprobe-eval
                                    lhprobe-vars))))


;; (defthm svex-envs-1mask-equiv-of-cons
;;   (implies (and (svex-envs-1mask-equiv rest1 rest2)
;;                 (4vec-1mask-equiv val1 val2))
;;            (equal (svex-envs-1mask-equiv (cons (cons var val1) rest1)
;;                                          (cons (cons var val2) rest2))
;;                   t))
;;   :hints ((and stable-under-simplificationp
;;                `(:expand (,(car (last clause)))
;;                  :in-theory (enable svex-env-lookup-of-cons-split)))))

(defthm lhprobe-map-eval-svex-envlists-ovtestsimilar-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhprobe-map-vars lhmap) :test)
                (svex-envlists-ovtestsimilar envs1 envs2))
           (equal (svex-envs-1mask-equiv (lhprobe-map-eval lhmap envs1)
                                         (lhprobe-map-eval lhmap envs2))
                  t))
  :hints(("Goal" :in-theory (enable lhprobe-map-eval
                                    lhprobe-map-vars))))



(defthm lhprobe-map-overridemux-eval-when-only-test-vars
  (implies (and (syntaxp (quotep lhmap))
                (equal vars (lhprobe-map-vars lhmap))
                (syntaxp (quotep vars))
                (svarlist-override-p vars :test)
                (svex-envlists-ovtestequiv equiv-envs (double-rewrite envs))
                (syntaxp (and (not (equal equiv-envs envs))
                              (quotep equiv-envs)
                              (progn$ ;; (cw "equiv-envs: ~x0~%" equiv-envs)
                                      t)))
                (equal ans (lhprobe-map-eval lhmap (make-fast-alists equiv-envs)))
                (syntaxp (and (quotep ans)
                              (progn$ ;; (cw "ans: ~x0~%" ans)
                                      t))))
           (equal (lhprobe-map-overridemux-eval lhmap envs outs)
                  ans)))


(defthm lhprobe-map-overridemux-eval-when-only-test-vars-under-svex-env-1mask-equiv
  (implies (and (syntaxp (quotep lhmap))
                (equal vars (lhprobe-map-vars lhmap))
                (syntaxp (quotep vars))
                (svarlist-override-p vars :test)
                (svex-envlists-ovtestsimilar equiv-envs (double-rewrite envs))
                (syntaxp (and (not (equal equiv-envs envs))
                              (quotep equiv-envs)
                              (progn$ ;; (cw "equiv-envs: ~x0~%" equiv-envs)
                                      t)))
                (equal ans (lhprobe-map-eval lhmap (make-fast-alists equiv-envs)))
                (syntaxp (and (quotep ans)
                              (progn$ ;; (cw "ans: ~x0~%" ans)
                                      t))))
           (svex-envs-1mask-equiv (lhprobe-map-overridemux-eval lhmap envs outs)
                                  ans)))



;; needed from svtv-generalize:
;; svtv-override-triple-envs-match
;; svtv-override-triplemap-envs-match
;; svtv-override-triplemaplist-envs-match




(defsection svtv-probe-to-lhprobe
  (local (in-theory (enable svtv-probe-to-lhprobe)))
  (local (std::set-define-current-function svtv-probe-to-lhprobe))

  (defret lhprobe-eval-of-<fn>
    (b* (((svtv-probe x)))
      (implies (hons-assoc-equal x.signal (svtv-name-lhs-map-fix namemap))
               (equal (lhprobe-eval lhprobe envs)
                      (svex-env-lookup x.signal (svtv-name-lhs-map-eval namemap (nth x.time envs))))))
    :hints(("Goal" :in-theory (enable lhprobe-eval)))))



(defsection svtv-probealist-vars
  (local (std::set-define-current-function svtv-probealist-vars))
  (local (in-theory (enable svtv-probealist-vars)))

  (defthm svtv-probe->signal-of-lookup-member-svtv-probealist-vars
    (implies (hons-assoc-equal v x)
             (member-equal (svtv-probe->signal (cdr (hons-assoc-equal v x)))
                           (svtv-probealist-vars x))))

  (defthmd svtv-probe->signal-of-lookup-member-svtv-probealist-vars-rw
    (implies (and (hons-assoc-equal v x)
                  (subsetp-equal (svtv-probealist-vars x) keys))
             (member-equal (svtv-probe->signal (cdr (hons-assoc-equal v x))) keys))
    :hints (("goal" :use svtv-probe->signal-of-lookup-member-svtv-probealist-vars
             :in-theory (disable svtv-probe->signal-of-lookup-member-svtv-probealist-vars
                                 svtv-probealist-vars)))))


(defsection svtv-probealist-to-lhprobe-map
  (local (in-theory (enable svtv-probealist-to-lhprobe-map)))
  (local (std::set-define-current-function svtv-probealist-to-lhprobe-map))

  (defret lhprobe-map-eval-of-<fn>
    (implies (and (subsetp-equal (svtv-probealist-vars x) (alist-keys (svtv-name-lhs-map-fix namemap)))
                  (<= (len (svtv-probealist-outvars x)) (len envs)))
             (equal (lhprobe-map-eval map envs)
                    (svtv-probealist-extract x (svtv-name-lhs-map-eval-list namemap envs))))
    :hints(("Goal" :in-theory (enable svtv-probealist-extract
                                      lhprobe-map-eval
                                      svtv-probealist-vars
                                      svtv-probealist-outvars))))

  (defret lookup-of-<fn>
    (equal (hons-assoc-equal key map)
           (and (svar-p key)
                (b* ((pair (hons-assoc-equal key (svtv-probealist-fix x))))
                  (and pair
                       (cons key (svtv-probe-to-lhprobe (cdr pair) namemap))))))
    :hints(("Goal" :in-theory (enable svtv-probealist-fix))))


  (defthm svtv-probe->time-of-lookup-bounded-by-outvars-len
    (implies (hons-assoc-equal v probes)
             (< (svtv-probe->time (cdr (hons-assoc-equal v probes)))
                 (len (Svtv-probealist-outvars probes))))
    :hints(("Goal" :in-theory (enable svtv-probealist-outvars)))
    :rule-classes :linear)

  (defthmd lookup-in-svtv-spec-cycle-outs->pipe-out
    (b* (((svtv-spec x)))
      (implies (and (subsetp-equal (svtv-probealist-vars x.probes) (alist-keys x.namemap))
                    (<= (len (svtv-probealist-outvars x.probes)) (len envs)))
               (equal (svex-env-lookup v (svtv-spec-cycle-outs->pipe-out x envs))
                      (let ((pair (hons-assoc-equal (svar-fix v) (svtv-probealist-to-lhprobe-map x.probes x.namemap))))
                        (if pair
                            (lhprobe-eval (cdr pair) envs)
                          (4vec-x))))))
    :hints(("Goal" :in-theory (e/d (svtv-spec-cycle-outs->pipe-out
                                    acl2::hons-assoc-equal-iff-member-alist-keys
                                    svtv-probe->signal-of-lookup-member-svtv-probealist-vars-rw)
                                   (acl2::alist-keys-member-hons-assoc-equal)))))

  (local (defthm len-of-svtv-probealist-out-vars-when-atom-fix
           (implies (not (consp (svtv-probealist-fix x)))
                    (equal (Svtv-probealist-outvars x) nil))
           :hints(("Goal" :in-theory (enable svtv-probealist-outvars
                                             svtv-probealist-fix)))))

  (defret lhprobe-map-max-stage-of-<fn>
    (equal (lhprobe-map-max-stage map)
           (+ -1 (len (svtv-probealist-outvars x))))
    :hints(("Goal" :in-theory (enable lhprobe-map-max-stage
                                      svtv-probealist-outvars
                                      svtv-probealist-fix
                                      svtv-probe-to-lhprobe))))

  (local (in-theory (enable svtv-probealist-fix))))







(defthm fsm-eval-of-take
  (implies (<= (nfix n) (len envs))
           (equal (fsm-eval (take n envs) initst fsm)
                  (take n (fsm-eval envs initst fsm))))
  :hints(("Goal" :in-theory (e/d (fsm-eval take)
                                 (acl2::take-of-too-many
                                  acl2::take-when-atom)))))

(defthm svtv-spec-fsm-syntax-check-implies-probe-vars-subset-of-namemap
  (implies (svtv-spec-fsm-syntax-check x)
           (subsetp-equal (svtv-probealist-vars (svtv-spec->probes x))
                          (alist-keys (svtv-spec->namemap x))))
  :hints(("Goal" :in-theory (e/d (svtv-spec-fsm-syntax-check)
                                 (acl2::hons-subset)))))


(defthm svex-unroll-state-is-fsm-final-state
  (equal (svex-unroll-state nextstates envs initst)
         (fsm-final-state envs initst nextstates))
  :hints(("Goal" :in-theory (enable fsm-step fsm-step-env fsm-final-state svex-unroll-state)
          :induct (svex-unroll-state nextstates envs initst)
          :expand ((fsm-final-state envs initst nextstates)))))

(defthmd fsm-eval-of-fsm-final-state
  (equal (fsm-eval envs2
                        (fsm-final-state envs1 initst (fsm->nextstate fsm))
                        fsm)
         (nthcdr (len envs1) (fsm-eval (append envs1 envs2) initst fsm)))
  :hints (("goal" :induct (fsm-final-state envs1 initst (fsm->nextstate fsm))
           :in-theory (enable (:i fsm-final-state))
           :expand ((fsm-final-state envs1 initst (fsm->nextstate fsm))
                    (:free (a b) (fsm-eval (cons a b) initst fsm))))))








(defthmd hons-assoc-equal-of-svtv-spec-fsm-bindings
  (implies (and (syntaxp (quotep k))
                (equal svtv-spec (force-execute spec))
                (syntaxp (quotep svtv-spec)))
           (equal (hons-assoc-equal k (svtv-spec-fsm-bindings spec))
                  (hons-assoc-equal k (svtv-spec-fsm-bindings svtv-spec))))
  :hints(("Goal" :in-theory (enable force-execute))))



(defthm lhs-eval-zx-nth-under-ovtestequiv
  (implies (and (syntaxp (Quotep lhs))
                (svarlist-override-p (lhs-vars lhs) :test)
                (svex-envlists-ovtestequiv envs-val (double-rewrite envs))
                (syntaxp (and (not (equal envs envs-val))
                              (quotep envs-val))))
           (equal (lhs-eval-zx lhs (nth n envs))
                  (lhs-eval-zx lhs (make-fast-alist (nth n envs-val))))))


(defthm lhs-eval-zx-nth-under-ovtestsimilar
  (implies (and (syntaxp (Quotep lhs))
                (svarlist-override-p (lhs-vars lhs) :test)
                (svex-envlists-ovtestsimilar envs-val (double-rewrite envs))
                (syntaxp (and (not (equal envs envs-val))
                              (quotep envs-val))))
           (4vec-1mask-equiv (lhs-eval-zx lhs (nth n envs))
                             (lhs-eval-zx lhs (make-fast-alist (nth n envs-val))))))


(local (defthm 4vec-bit?!-of-4vec-concat-free
         (implies (And (2vec-p n)
                       (natp (2vec->val n)))
                  (equal (4vec-bit?! test
                                     (4vec-concat n then1 then2)
                                     (4vec-concat n else1 else2))
                         (4vec-concat n (4vec-bit?! test then1 else1)
                                      (4vec-bit?! (4vec-rsh n test) then2 else2))))
         :hints (("goal" :in-theory (enable 4vec-concat 4vec-bit?! 4vec-bitmux 4vec-1mask
                                            4vec-rsh 4vec-shift-core))
                 (bitops::logbitp-reasoning))))

(defsection 4vec-bit?!-mask-of-lhs-eval-zx
  (local (in-theory (disable (tau-system))))
  (local (defun ind (lhs mask)
           (if (atom lhs)
               mask
             (ind (cdr lhs) (4vec-rsh (2vec (lhrange->w (car lhs))) mask)))))

  (local (in-theory (disable logmask)))

  (local (defthm loghead-of-logtail-equal-mask
           (implies (case-split (equal (loghead (+ (nfix n) (nfix m)) x) (logmask (+ (nfix n) (nfix m)))))
                    (equal (equal (loghead n (logtail m x)) (logmask n))
                           t))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm loghead-of-logtail-not-equal-mask
           (implies (and (natp n) (natp m)
                         (case-split (not (equal (loghead n x) (logmask n)))))
                    (equal (equal (loghead (+ n m) x) (logmask (+ n m)))
                           nil))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm 4vec-concat-of-4vec-bit?!-when-mask
           (implies (and (2vec-p mask)
                         (2vec-p w)
                         (natp (2vec->val w))
                         (case-split
                           (equal (loghead (2vec->val w) (2vec->val mask))
                                  (logmask (2vec->val w)))))
                    (equal (4vec-concat w (4vec-bit?! mask a b) c)
                           (4vec-concat w a c)))
           :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-1mask 4vec-bitmux 4vec-concat))
                  (bitops::logbitp-reasoning))))


  (local (defthm 4vec-bit?!-mask-when-zero-ext
           (implies (and (2vec-p mask)
                         (equal (loghead n (2vec->val mask))
                                (logmask n))
                         (equal (4vec-rsh (2vec (nfix n)) lhs1) 0)
                         (equal (4vec-rsh (2vec (nfix n)) lhs2) 0))
                    (equal (4vec-bit?! mask lhs1 lhs2) (4vec-fix lhs1)))
           :hints (("goal" :in-theory (enable 4vec-bit?! 4vec-1mask 4vec-bitmux 4vec-rsh 4vec-shift-core))
                   (bitops::logbitp-reasoning :prune-examples nil))))

  (local (defthm 4vec-rsh-width-of-lhs-eval-zx
           (equal (4vec-rsh (2vec (lhs-width lhs)) (lhs-eval-zx lhs env))
                  0)
           :hints(("Goal" :in-theory (enable lhs-eval-zx lhs-width)))))
  
  (defthm 4vec-bit?!-mask-of-lhs-eval-zx
    (implies (and (syntaxp (and (quotep mask)
                                (quotep lhs)))
                  (2vec-p mask)
                  (equal w (lhs-width lhs))
                  (equal (loghead w (2vec->val mask))
                         (logmask w))
                  (equal (lhs-width lhs2) w))
             (equal (4vec-bit?! mask (lhs-eval-zx lhs env) (lhs-eval-zx lhs2 env2))
                    (lhs-eval-zx lhs env)))
    :hints (("goal" :use ((:instance 4vec-bit?!-mask-when-zero-ext
                           (n (lhs-width lhs))
                           (lhs1 (lhs-eval-zx lhs env))
                           (lhs2 (lhs-eval-zx lhs2 env2))))
             :in-theory (disable 4vec-bit?!-mask-when-zero-ext))))

  (defthm 4vec-bit?!-of-0
    (equal (4vec-bit?! 0 x y)
           (4vec-fix y))
    :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))))

  (defthm 4vec-bit?!-of-neg1
    (equal (4vec-bit?! -1 x y)
           (4vec-fix x))
    :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux)))))


(defthm append-take-take-nthcdr
  (equal (append (take n x) (take m (nthcdr n x)))
         (take (+ (nfix n) (nfix m)) x))
  :hints(("Goal" :induct (nthcdr n x)
          :in-theory (enable take nthcdr))))

(encapsulate nil
  (local (defun ind (n m x)
           (if (or (zp n) (zp m))
               (list m x)
             (ind (1- n) (1- m) (cdr x)))))
  (defthmd nthcdr-of-take
    (equal (nthcdr n (take m x))
           (take (nfix (- (nfix m) (nfix n))) (nthcdr n x)))
    :hints (("goal" :induct (ind n m x)
             :expand ((take m x)
                      (:free (x) (nthcdr n x)))))))


(local (include-book "std/lists/nth" :dir :system))
(std::defredundant :names (acl2::nth-of-nthcdr
                           acl2::nth-of-take))


(define svex-alistlist-removekeys ((keys svarlist-p) (alists svex-alistlist-p))
  (if (atom alists)
      nil
    (cons (svex-alist-removekeys keys (car alists))
          (svex-alistlist-removekeys keys (cdr alists)))))


(std::def-primitive-aggregate svtv-to-fsm-thm
  (thmname
   svtv-spec-thmname
   fsmname
   svtv
   svtv-spec
   triples-name

   input-vars
   output-vars
   override-vars
   spec-override-vars

   ;; eliminate-override-vars
   ;; eliminate-override-signals
   ;; eliminate-all-overrides
   remaining-override-vars
   new-eliminated-override-vars
   all-eliminated-override-vars
   override-test-envs

   outmap
   bindings
   triple-val-alist
   run-length

   hyp
   concl
   rule-classes

   cycle-num-rewrite-strategy
   base-cycle-var
   primary-output-var
   pkg-sym))


(defconst *svtv-to-fsm-first-thm-template*
  '(defthm <thmname>-fixed-envlist
     (b* ((fsm (<fsmname>))
          (outs (fsm-eval envs initst fsm))
          <bindings>)
       (implies (and (lhprobe-constraintlist-overridemux-eval
                      (<svtvname>-fsm-constraints) envs outs)
                     (svex-envlists-ovtestsimilar envs <override-test-envs>)
                     <hyp>
                     (equal (len envs) <run-length>))
                <concl>))
     :hints (("goal" :use ((:instance fsm-eval-when-overridekeys-envlists-agree*
                            (x (<fsmname>))
                            (impl-envs (b* ((fsm (<fsmname>))
                                            (outs (fsm-eval envs initst fsm))
                                            (svtv-env
                                             (append <test-env>
                                                     (lhprobe-map-overridemux-eval (<svtvname>-fsm-bindings) envs outs)))
                                            (fsm-envs (svtv-spec-pipe-env->cycle-envs (<specname>) svtv-env)))
                                         (svex-envlist-x-override
                                          fsm-envs
                                          (svex-envlist-remove-override
                                           (svex-envlist-remove-override envs :test) :val))))
                            (spec-envs envs)
                            (initst initst)
                            (overridekeys (<svtvname>-overridekeys))))
              ;;            :in-theory (e/d (svtv-spec-run-in-terms-of-cycle-fsm
              ;;                             CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
              ;;                             svex-envlists-ovtests-ok-when-variable-free)
              ;;                            (fsm-eval-when-overridekeys-envlists-agree*
              ;;                             <svtv-spec-thmname>
              ;;                             LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL
              ;;                             unsigned-byte-p
              ;;                             acl2::fal-extract-of-cons))
              :in-theory
              '(;; lhs-eval-zx-SVEX-ENV-EQUIV-CONGRUENCE-ON-ENV
                ;;                            SVEX-ENVLISTS-SIMILAR-IMPLIES-EQUAL-fsm-EVAL-1
                SVEX-ENVLISTS-EQUIVALENT-REFINES-SVEX-ENVLISTS-SIMILAR
                svex-envlists-equivalent-is-an-equivalence
                svex-envlists-similar-is-an-equivalence
                <svtvname>-fsm-constraints
                <svtvname>-fsm-bindings
                <svtvname>-fsm-output-map
                cycle-fsm-of-<specname>
                no-duplicate-state-keys-of-<fsmname>
                nextstate-keys-non-override-of-<fsmname>

                (:CONGRUENCE
                 SV::SVEX-ENVLISTS-EQUIVALENT-IMPLIES-EQUAL-SVTV-SPEC-CYCLE-OUTS->PIPE-OUT-2)
                
                (:congruence SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-lhs-eval-zx-2)
                (:congruence 4VEC-1MASK-EQUIV-IMPLIES-EQUAL-4VEC-BIT?!-1)
                (:COMPOUND-RECOGNIZER ACL2::NATP-COMPOUND-RECOGNIZER)
                (:CONGRUENCE SET-EQUIV-IMPLIES-EQUAL-SVARLIST-NONOVERRIDE-P-1)
                (:CONGRUENCE
                 SVEX-ENVLISTS-OVTESTSIMILAR-IMPLIES-IFF-SVEX-ENVLISTS-OVTESTS-OK-1)
                (:CONGRUENCE
                 SVEX-ENVLISTS-OVTESTSIMILAR-IMPLIES-IFF-SVEX-ENVLISTS-OVTESTS-OK-2)
                (:CONGRUENCE SVEX-ENVLISTS-SIMILAR-IMPLIES-SVEX-ENVS-SIMILAR-NTH-2)
                (:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-fsm-EVAL-2)
                (:DEFINITION DOUBLE-REWRITE)
                (:DEFINITION HONS-GET)
                (:DEFINITION LHPROBE-EVAL)
                (:DEFINITION MAX)
                (:DEFINITION NOT)
                (:DEFINITION SYNP)
; (:EQUIVALENCE SVEX-ENVLISTS-OVTESTEQUIV-IS-AN-EQUIVALENCE)
                (:EQUIVALENCE SVEX-ENVLISTS-OVTESTSIMILAR-IS-AN-EQUIVALENCE)
                (:EQUIVALENCE SVEX-ENVS-1MASK-EQUIV-IS-AN-EQUIVALENCE)
                (:EXECUTABLE-COUNTERPART 2VEC->VAL$INLINE)
                (:EXECUTABLE-COUNTERPART 2VEC-P$INLINE)
                (:EXECUTABLE-COUNTERPART CDR)
                (:EXECUTABLE-COUNTERPART <svtvname>-fsm-output-map)
                (:EXECUTABLE-COUNTERPART EQUAL)
                (:EXECUTABLE-COUNTERPART FAL-EXTRACT)
                (:EXECUTABLE-COUNTERPART FORCE-EXECUTE)
                (:EXECUTABLE-COUNTERPART HONS-ASSOC-EQUAL)
                (:EXECUTABLE-COUNTERPART LHPROBE->LHS$INLINE)
                (:EXECUTABLE-COUNTERPART LHPROBE->SIGNEDP$INLINE)
                (:EXECUTABLE-COUNTERPART LHPROBE->STAGE$INLINE)
                (:EXECUTABLE-COUNTERPART LHPROBE-CHANGE-OVERRIDE)
                (:EXECUTABLE-COUNTERPART LHPROBE-MAP-EVAL)
                (:EXECUTABLE-COUNTERPART LHPROBE-MAP-VARS)
                (:EXECUTABLE-COUNTERPART LHPROBE-VARS)
                (:EXECUTABLE-COUNTERPART lhs-eval-zx)
                (:EXECUTABLE-COUNTERPART LHS-VARS)
                (:EXECUTABLE-COUNTERPART LHS-WIDTH)
                (:EXECUTABLE-COUNTERPART ACL2::LOGHEAD$INLINE)
                (:EXECUTABLE-COUNTERPART ACL2::LOGMASK$INLINE)
                (:EXECUTABLE-COUNTERPART MAKE-FAST-ALIST)
                (:EXECUTABLE-COUNTERPART MAKE-FAST-ALISTS)
                (:EXECUTABLE-COUNTERPART NTH)
                (:EXECUTABLE-COUNTERPART SVAR-FIX$INLINE)
                (:EXECUTABLE-COUNTERPART SVAR-OVERRIDETYPE-EQUIV$INLINE)
                (:EXECUTABLE-COUNTERPART SVARLIST-FIX$INLINE)
                (:EXECUTABLE-COUNTERPART SVARLIST-NONOVERRIDE-P)
                (:EXECUTABLE-COUNTERPART SVARLIST-OVERRIDE-P)
                (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-EVAL)
                (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-NONCALL-P)
                (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-VARS)
                (:EXECUTABLE-COUNTERPART SVEX-ENVLIST-1MASK)
                (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLELIST-ENVS-MATCH)
                (:EXECUTABLE-COUNTERPART SVTV-OVERRIDE-TRIPLEMAPLIST-RELEVANT-VARS)
                (:EXECUTABLE-COUNTERPART SVTV-SPEC-FSM-BINDINGS)
                (:executable-counterpart svtv-override-triplemaplist-test-only-p)
                (:META FORCE-EXECUTE-FORCE-EXECUTE)
                (:META SVTV-OVERRIDE-SUBST-MATCHES-ENV-META)
                (:META
                 SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-CHECKS-WHEN-VARIABLE-FREE)
                (:REWRITE 4VEC-BIT?!-MASK-OF-lhs-eval-zx)
                (:REWRITE ALISTLIST-EVAL-OF-TEST-ALISTS-UNDER-BINDINGS)
                (:REWRITE ALISTLIST-EVAL-OF-TEST-ALISTS-UNDER-BINDINGS-gen)
                (:REWRITE fsm-OVCONGRUENT-OF-<FSMNAME>)
                (:REWRITE
                 fsm-OVERRIDEKEY-TRANSPARENT-P-OF-<FSMNAME>-wrt-<svtvname>-overridekeys)
                (:REWRITE ACL2::COMMUTATIVITY-OF-APPEND-UNDER-SET-EQUIV)
                (:REWRITE CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES)
                (:REWRITE CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES-gen)
                (:REWRITE <SPECNAME>-FACTS)
                (:REWRITE CYCLE-OUTPUTS-CAPTURED-OF-<SPECNAME>)
                (:REWRITE FAL-EXTRACT-CONST-OF-SVTV-SPEC-FSM-BINDINGS)
                (:REWRITE HONS-ASSOC-EQUAL-OF-SVTV-SPEC-FSM-BINDINGS)
                (:REWRITE LEN-OF-fsm-EVAL)
                (:REWRITE LEN-OF-SVEX-ENVLIST-X-OVERRIDE)
                (:REWRITE LEN-OF-SVTV-SPEC-PIPE-ENV->CYCLE-ENVS)
                (:REWRITE LHPROBE-MAP-FIX-WHEN-LHPROBE-MAP-P)
                (:REWRITE lhprobe-map-overridemux-eval-when-only-test-vars-under-svex-env-1mask-equiv)
                (:REWRITE LHPROBE-MAP-P-OF-SVTV-SPEC-FSM-BINDINGS)
                (:REWRITE LHPROBE-OVERRIDEMUX-EVAL-SPLIT-ON-VAR-OVERRIDETYPE)
; (:REWRITE lhs-eval-zx-NTH-UNDER-OVTESTEQUIV)
                (:REWRITE lhs-eval-zx-NTH-UNDER-OVTESTsimilar)
                (:REWRITE LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL)
                (:REWRITE NEXTSTATE-KEYS-NON-OVERRIDE-OF-<SPECNAME>)
                (:REWRITE NEXTSTATE-KEYS-OF-SVTV-SPEC->CYCLE-FSM)
                (:REWRITE OUTVARS-LEN-OF-<SPECNAME>)
                (:REWRITE SVARLIST-NONOVERRIDE-P-OF-APPEND)
                (:REWRITE SVARLIST-NONOVERRIDE-P-OF-SVARLIST-REMOVE-OVERRIDE)
                (:REWRITE
                 SVARLIST-NONOVERRIDE-TEST-OF-<SPECNAME>-CYCLEPHASELIST-KEYS)
                (:REWRITE SVEX-ALIST-ALL-XES-OF-<SPECNAME>-INITST)
                (:REWRITE SVEX-ENV-REDUCE-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL)
                (:REWRITE SVEX-ENV-X-OVERRIDE-WHEN-SVEX-ALIST-ALL-XES-P)
                (:REWRITE SVEX-ENVLIST-ALL-KEYS-OF-REMOVE-OVERRIDE)
                (:REWRITE SVEX-ENVLIST-ALL-KEYS-OF-SVTV-CYCLE-RUN-FSM-INPUTS)
                (:REWRITE SVEX-ENVLISTS-OVTESTS-OK-WHEN-VARIABLE-FREE)
                (:REWRITE SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-RELEVANT-VARS-TEST-ONLY)
                (:REWRITE SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-SIMPLIFY)
                (:REWRITE SVTV-SPEC-CYCLE-OUTS->PIPE-OUT-OF-<SPECNAME>)
                (:REWRITE SVTV-SPEC-FSM-SYNTAX-CHECK-OF-<SPECNAME>)
                (:REWRITE
                 SVTV-SPEC-PIPE-ENV->CYCLE-ENVS-UNDER-SVEX-ENVLISTS-OVTESTSIMILAR)
                (:REWRITE SVTV-SPEC-RUN-IN-TERMS-OF-CYCLE-FSM)
                ;; (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)
                (:REWRITE-QUOTED-CONSTANT
                 SVEX-ENVLIST-1MASK-UNDER-SVEX-ENVLISTS-1MASK-EQUIV)
                (:TYPE-PRESCRIPTION LEN)
                (:TYPE-PRESCRIPTION LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL)
                (:TYPE-PRESCRIPTION OVERRIDEKEYS-ENVLISTS-AGREE*)
                (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P)


                (:EXECUTABLE-COUNTERPART 4VEC-1MASK)
                (:REWRITE 4VEC-BIT?!-WHEN-TEST-EMPTY)
                (:REWRITE 4VEC-FIX-OF-4VEC)
                (:REWRITE 4VEC-P-OF-lhs-eval-zx)
                (:REWRITE-QUOTED-CONSTANT 4VEC-1MASK-IDENTITY)

                svex-env-lookup-of-append
                (svex-env-boundp)
                svtv-spec-non-test-vars-force-execute
                (acl2::hons-intersect-p)
                (alist-keys)
                (svex-env-fix)
                (hons-set-diff)
                svex-env-reduce-of-append-envs-under-svex-envs-1mask-equiv-special
                (svex-env-reduce)
                SVEX-ENVS-1MASK-EQUIV-IMPLIES-SVEX-ENVS-1MASK-EQUIV-APPEND-2
                (append)

                (sv::4vec-fix)
                (unsigned-byte-p)))
             (and stable-under-simplificationp
                  '(:use ((:instance <svtv-spec-thmname>
                           (env (b* ((fsm (<fsmname>))
                                     (outs (fsm-eval envs initst fsm)))
                                  (append <test-env>
                                          (lhprobe-map-overridemux-eval (<svtvname>-fsm-bindings) envs outs))))
                           (base-ins (svtv-cycle-run-fsm-inputs
                                      (svex-envlist-remove-override
                                       (svex-envlist-remove-override envs :test) :val)
                                      (svtv-spec->cycle-phases (<specname>)))))))))
     :rule-classes nil))





(define svtv-to-fsm-first-thm-input-var-bindings ((input-vars svarlist-p)
                                                  (bindings lhprobe-map-p)
                                                  (overridetype svar-overridetype-p)
                                                  (envs-var)) ;; envs/outs
  :hooks nil
  (b* (((when (atom input-vars)) nil)
       (in (car input-vars))
       (look (hons-get in bindings))
       ((unless look)
        (raise "SVTV input not found in bindings: ~x0~%" in)
        (svtv-to-fsm-first-thm-input-var-bindings (cdr input-vars) bindings overridetype envs-var))
       ((lhprobe probe) (cdr look)))
    (cons `(,in (,(if probe.signedp 'lhs-eval-signx 'lhs-eval-zx)
                 ',(lhs-change-override probe.lhs overridetype)
                 (nth ,probe.stage ,envs-var)))
          (svtv-to-fsm-first-thm-input-var-bindings (cdr input-vars) bindings overridetype envs-var))))




;; (append (svtv-to-fsm-first-thm-input-var-bindings '(inc) (counter-invar-run-fsm-bindings) nil 'envs)
;;         (svtv-to-fsm-first-thm-input-var-bindings '(sum1) (counter-invar-run-fsm-bindings) :val 'envs)
;;         (svtv-to-fsm-first-thm-input-var-bindings '(sum) (counter-invar-run-fsm-bindings) nil 'outs)
;;         (svtv-to-fsm-first-thm-input-var-bindings '(sum-out sum1-out) (counter-invar-run-fsm-output-map) nil 'outs))


(define svtv-to-fsm-first-thm (x)
  :mode :program
  (b* (((svtv-to-fsm-thm x))
       ((acl2::with-fast x.bindings x.outmap x.triple-val-alist))
       (var-bindings (append (svtv-to-fsm-first-thm-input-var-bindings x.input-vars x.bindings nil 'envs)
                             (svtv-to-fsm-first-thm-input-var-bindings
                              x.remaining-override-vars
                              x.bindings :val 'envs)
                             (svtv-to-fsm-first-thm-input-var-bindings
                              x.all-eliminated-override-vars
                              x.bindings nil 'outs)
                             (svtv-to-fsm-first-thm-input-var-bindings x.output-vars x.outmap nil 'outs)))
       (test-env (svtv-genthm-override-test-alist
                  x.new-eliminated-override-vars
                  x.triple-val-alist x.triples-name))
       ;; (run-length (len (svtv-probealist-outvars spec.probes)))
       )
    (acl2::template-subst *svtv-to-fsm-first-thm-template*
                          :atom-alist `((<fsmname> . ,x.fsmname)
                                        (<hyp> . ,x.hyp)
                                        (<concl> . ,x.concl)
                                        (<run-length> . ,x.run-length)
                                        (<svtv-spec-thmname> . ,x.svtv-spec-thmname)
                                        (<specname> . ,x.svtv-spec)
                                        (<override-test-envs> . ',x.override-test-envs)
                                        (<test-env> . ',test-env))
                          :splice-alist `((<bindings> . ,var-bindings))
                          :str-alist `(("<SVTVNAME>" . ,(symbol-name x.svtv))
                                       ("<SPECNAME>" . ,(symbol-name x.svtv-spec))
                                       ("<THMNAME>" . ,(symbol-name  x.thmname))
                                       ("<FSMNAME>" . ,(symbol-name  x.fsmname)))
                          :pkg-sym x.pkg-sym)))





(defconst *svtv-to-fsm-final-thm-template*
  '(defthm <thmname>
     (b* ((fsm (<fsmname>))
          (outs (fsm-eval envs initst fsm))
          <bindings>)
       (implies (and <cycle-num-equations>
                     (lhprobe-constraintlist-overridemux-eval
                      (<svtvname>-fsm-constraints)
                      (nthcdr <basecycle> envs)
                      (nthcdr <basecycle> outs))
                     (svex-envlists-ovtestsimilar (take <run-length> (nthcdr <basecycle> envs))
                                                  <override-test-envs>)
                     <hyp>
                     (>= (len envs) (+ <basecycle> <run-length>)))
                <concl>))
     :hints (("goal" :use ((:instance <thmname>-fixed-envlist
                            (envs (take <run-length> (nthcdr <basecycle> envs)))
                            (initst (b* ((fsm (<fsmname>)))
                                      (fsm-final-state (take <basecycle> envs) initst
                                                            (fsm->nextstate fsm))))))
                         ;; :in-theory (e/d (svtv-spec-run-in-terms-of-cycle-fsm
                         ;;    CONSTRAINTS-EVAL-OF-SVTV-SPEC-FSM-CONSTRAINTS-IMPLIES
                         ;;    svex-envlists-ovtests-ok-when-variable-free
                         ;;    fsm-eval-of-fsm-final-state
                         ;;    nthcdr-of-take)
                         ;;   (fsm-eval-when-overridekeys-envlists-agree*
                         ;;    <thmname>-fixed-envlist
                         ;;    nthcdr-of-fsm-eval-is-fsm-eval
                         ;;    LOOKUP-OF-LHPROBE-MAP-OVERRIDEMUX-EVAL
                         ;;    unsigned-byte-p
                         ;;    acl2::fal-extract-of-cons
                         ;;    fsm-eval-of-cons
                         ;;    lhs-eval-zx-of-cons
                         ;;    take nth len nthcdr
                         ;;    acl2::take-of-len-free
                         ;;    acl2::take-of-too-many
                         ;;    acl2::take-when-atom
                         ;;    acl2::len-when-atom
                         ;;    consp-of-fsm-eval
                         ;;    acl2::natp-when-integerp
                         ;;    (tau-system)
                         ;;    ))

              :in-theory '((:COMPOUND-RECOGNIZER ACL2::NATP-COMPOUND-RECOGNIZER)
                           (:CONGRUENCE ACL2::NAT-EQUIV-IMPLIES-EQUAL-NTH-1)
                           (:CONGRUENCE ACL2::NAT-EQUIV-IMPLIES-EQUAL-NTHCDR-1)
                           (:DEFINITION NOT)
                           (:EXECUTABLE-COUNTERPART <)
                           (:EXECUTABLE-COUNTERPART BINARY-+)
                           (:EXECUTABLE-COUNTERPART unary--)
                           (:EXECUTABLE-COUNTERPART EQUAL)
                           (:EXECUTABLE-COUNTERPART NFIX)
                           (:REWRITE APPEND-TAKE-TAKE-NTHCDR)
                           (:REWRITE fsm-EVAL-OF-fsm-FINAL-STATE)
                           (:REWRITE fsm-EVAL-OF-TAKE)
                           (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
                           (:REWRITE COMMUTATIVITY-OF-+)
                           (:REWRITE CYCLE-FSM-OF-<specname>)
                           (:REWRITE ACL2::DISTRIBUTIVITY-OF-MINUS-OVER-+)
                           (:REWRITE FIX-OF-NUMBER)
                           (:REWRITE ACL2::FOLD-CONSTS-IN-+)
                           (:REWRITE INVERSE-OF-+)
                           (:REWRITE ACL2::LEN-OF-TAKE)
                           (:REWRITE LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL-OF-TAKE-ENVS)
                           (:REWRITE LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL-OF-TAKE-OUTS)
                           (:REWRITE MAX-STAGE-OF-<SVTVNAME>-FSM-CONSTRAINTS)
                           (:REWRITE ACL2::NFIX-UNDER-NAT-EQUIV)
                           (:REWRITE ACL2::NFIX-WHEN-NATP)
                           (:REWRITE ACL2::NTH-OF-NTHCDR)
                           (:REWRITE ACL2::NTH-OF-TAKE)
                           (:REWRITE NTHCDR-OF-TAKE)
                           (:REWRITE OUTVARS-LEN-OF-<specname>)
                           (:REWRITE UNICITY-OF-0)
                           (:TYPE-PRESCRIPTION INTEGERP-OF-LHPROBE-CONSTRAINTLIST-MAX-STAGE)
                           (:TYPE-PRESCRIPTION LEN)
                           (:TYPE-PRESCRIPTION LHPROBE-CONSTRAINTLIST-OVERRIDEMUX-EVAL)
                           (:TYPE-PRESCRIPTION NFIX)

                           acl2::natp-when-gte-0
                           acl2::natp-when-integerp)
              ))
     :rule-classes <rule-classes>))






(define svtv-to-fsm-final-thm-var-bindings ((vars symbol-listp)
                                            (bindings lhprobe-map-p)
                                            (overridetype svar-overridetype-p)
                                            (envs-var symbolp) ;; envs/outs
                                            (x svtv-to-fsm-thm-p))
  :returns (mv bindings (equation-alist alistp))
  :hooks nil
  :guard (b* (((svtv-to-fsm-thm x)))
           (and (symbolp x.base-cycle-var)
                (symbolp x.pkg-sym)))
  :prepwork ((local (defthm alistp-remove-equal (implies (alistp x) (alistp (remove-equal k x))))))
  :verify-guards :after-returns
  (b* (((when (atom vars)) (mv nil nil))
       (in (car vars))
       (look (hons-get in bindings))
       ((unless look)
        (raise "SVTV input not found in bindings: ~x0~%" in)
        (svtv-to-fsm-final-thm-var-bindings
         (cdr vars) bindings overridetype envs-var x))
       ((lhprobe probe) (cdr look))
       ((mv rest-bindings rest-equations)
        (svtv-to-fsm-final-thm-var-bindings
         (cdr vars) bindings overridetype envs-var x))
       ((svtv-to-fsm-thm x))
       ;; Depending on the cycle-num-rewrite-strategy, we generate the cycle-var and equation differently:
       ;; :all-free -- cycle var <varname>-cycle-num, (equal cycle-var (+ probe.stage base-cycle-var))
       ;; :by-cycle -- cycle var <base-cycle-var>+stage,
       ;;              (equal cycle-var (+ probe.stage base-cycle-var)) (but uniquify)
       ;; :single-var -- cycle var is actual expression (+ pipe.stage base-cycle-var), no equations
       ((mv cycle-var equations)
        (case x.cycle-num-rewrite-strategy
          (:all-free (b* ((cycle-var (intern-in-package-of-symbol
                                      (concatenate 'string (symbol-name in) "-CYCLE-NUM")
                                      x.pkg-sym))
                          (eqn (if (eq in x.primary-output-var)
                                   `(and (integerp ,cycle-var)
                                         (<= ,probe.stage ,cycle-var)
                                         (equal ,x.base-cycle-var (- ,cycle-var ,probe.stage)))
                                 `(equal ,cycle-var (+ ,probe.stage ,x.base-cycle-var)))))
                       (mv cycle-var (cons (cons in eqn) rest-equations))))
          (:by-cycle (b* (((when (eql probe.stage 0))
                           (mv x.base-cycle-var rest-equations))
                          (cycle-var
                           (intern-in-package-of-symbol
                            (concatenate 'string (symbol-name x.base-cycle-var)
                                         "+" (str::natstr probe.stage))
                            x.pkg-sym))
                          (eqn (if (eq in x.primary-output-var)
                                   `(and (integerp ,cycle-var)
                                         (<= ,probe.stage ,cycle-var)
                                         (equal ,x.base-cycle-var (- ,cycle-var ,probe.stage)))
                                 `(equal ,cycle-var (+ ,probe.stage ,x.base-cycle-var))))
                          (eqns (b* ((look (rassoc-equal eqn rest-equations))
                                     ((unless look)
                                      (cons (cons in eqn) rest-equations))
                                     ((when (eq in x.primary-output-var))
                                      (cons (cons in eqn) (remove-equal look rest-equations))))
                                  rest-equations)))
                       (mv cycle-var eqns)))
          (t ;; :single-var
           (mv (if (eql probe.stage 0)
                   x.base-cycle-var
                 `(+ ,probe.stage ,x.base-cycle-var))
               rest-equations)))))
    (mv (cons `(,in (,(if probe.signedp 'lhs-eval-signx 'lhs-eval-zx)
                     ',(lhs-change-override probe.lhs overridetype)
                     (nth ,cycle-var ,envs-var)))
              rest-bindings)
        equations)))




;; (append (svtv-to-fsm-final-thm-var-bindings '(inc) (counter-invar-run-fsm-bindings) nil 'envs)
;;         (svtv-to-fsm-final-thm-var-bindings '(sum1) (counter-invar-run-fsm-bindings) :val 'envs)
;;         (svtv-to-fsm-final-thm-var-bindings '(sum) (counter-invar-run-fsm-bindings) nil 'outs)
;;         (svtv-to-fsm-final-thm-var-bindings '(sum-out sum1-out) (counter-invar-run-fsm-output-map) nil 'outs))






(define svtv-to-fsm-final-thm (x)
  :mode :program
  (b* (((svtv-to-fsm-thm x))
       ((acl2::with-fast x.bindings x.outmap x.triple-val-alist))
       ((mv var-bindings1 cycle-eqns1)
        (svtv-to-fsm-final-thm-var-bindings
         x.input-vars x.bindings nil 'envs x))
       ((mv var-bindings2 cycle-eqns2)
        (svtv-to-fsm-final-thm-var-bindings
         x.remaining-override-vars x.bindings :val 'envs x))
       ((mv var-bindings3 cycle-eqns3)
        (svtv-to-fsm-final-thm-var-bindings
         x.all-eliminated-override-vars x.bindings nil 'outs x))
       ((mv var-bindings4 cycle-eqns4)
        (svtv-to-fsm-final-thm-var-bindings
         x.output-vars x.outmap nil 'outs x))
       (var-bindings (append var-bindings1 var-bindings2 var-bindings3 var-bindings4))
       (cycle-eqns-all (append cycle-eqns1 cycle-eqns2 cycle-eqns3 cycle-eqns4))
       (cycle-eqns (case x.cycle-num-rewrite-strategy
                     (:single-var ;; cycle-eqns are empty anyway
                      `((natp ,x.base-cycle-var)))
                     (t
                      (b* ((first-cycle-eqn (cdr (assoc-eq x.primary-output-var cycle-eqns-all)))
                           (rest-cycle-eqns (remove-equal first-cycle-eqn (strip-cdrs cycle-eqns-all))))
                        (cons first-cycle-eqn rest-cycle-eqns)))))
       ;; (run-length (len (svtv-probealist-outvars spec.probes)))
       )
    (acl2::template-subst *svtv-to-fsm-final-thm-template*
                          :atom-alist `((<fsmname> . ,x.fsmname)
                                        (<hyp> . ,x.hyp)
                                        (<concl> . ,x.concl)
                                        (<run-length> . ,x.run-length)
                                        (<svtv-spec-thmname> . ,x.svtv-spec-thmname)
                                        (<specname> . ,x.svtv-spec)
                                        (<override-test-envs> . ',x.override-test-envs)
                                        (<basecycle> . ,x.base-cycle-var)
                                        (<thmname> . ,x.thmname)
                                        (<rule-classes> . ,x.rule-classes))
                          :splice-alist `((<bindings> . ,var-bindings)
                                          (<cycle-num-equations> . ,cycle-eqns))
                          :str-alist `(("<SVTVNAME>" . ,(symbol-name x.svtv))
                                       ("<SPECNAME>" . ,(symbol-name x.svtv-spec))
                                       ("<THMNAME>" . ,(symbol-name x.thmname))
                                       ("<FSMNAME>" . ,(symbol-name x.fsmname)))
                          :pkg-sym x.pkg-sym)))


(define parse-svtv-to-fsm-thm (thmname args state)
  :returns thmobj
  :mode :program :stobjs state
  (b* ((defaults (table-alist 'svtv-to-fsm-thm-defaults (w state)))
       (ctx `(def-svtv-to-fsm-thm ,thmname))
       (full-args args)
       ;; Allow svtv-spec-thmname as the second arg without a keyword
       (args (if (keywordp (car args)) args (cdr args)))
       ((std::extract-keyword-args
         :defaults defaults
         :ctx ctx
         svtv-spec-thmname

         eliminate-override-vars
         eliminate-override-signals
         ;; outmap
         ;; bindings
         ;; triple-val-alist
         ;; run-length

         ;; hyp
         ;; concl
         (rule-classes ':rewrite)

         ;; unsigned-byte-hyps
         ;; env-val-widths-hyp

         (cycle-num-rewrite-strategy ':by-cycle)
         (base-cycle-var 'base-cycle)
         primary-output-var
         (pkg-sym thmname))
        args)
       (svtv-spec-thmname (or svtv-spec-thmname
                              (and (not (keywordp (car full-args)))
                                   (car full-args))))

       ((unless (and svtv-spec-thmname (symbolp svtv-spec-thmname)))
        (er hard ctx "~x0 must be specified" :svtv-spec-thmname))
       (svtv-thm (cdr (assoc-eq svtv-spec-thmname (table-alist 'svtv-generalized-thm-table (w state)))))
       ((unless svtv-thm)
        (er hard ctx "No entry in the ~x0 for svtv-spec-thm ~x1" 'svtv-generalized-thm-table svtv-spec-thmname))

       ((unless (member-eq cycle-num-rewrite-strategy '(:all-free :by-cycle :single-var)))
        (er hard ctx "Unknown :cycle-num-rewrite-strategy argument ~x0: possible values are ~&1~%"
            cycle-num-rewrite-strategy '(:all-free :by-cycle :single-var)))

       ((svtv-generalized-thm svtv-thm))

       ((with-fast svtv-thm.triple-val-alist))

       ((unless svtv-thm.svtv-spec)
        (er hard ctx "The ~x0 must be about an svtv-spec, but ~x1 is not" :svtv-spec-thmname svtv-spec-thmname))

       (fsm (cdr (assoc svtv-thm.svtv-spec (table-alist 'svtv-spec-to-fsm-table (w state)))))
       ((unless fsm)
        (er hard ctx "The svtv-spec ~x0 associated with theorem ~x1 doesn't ~
                      have an associated FSM. Ensure that the svtv-spec was ~
                      defined using ~x2 with the ~x3 option."
            svtv-thm.svtv-spec svtv-spec-thmname 'def-svtv-refinement :fsm))

       ;; We only use the SVTV to get variable names (which we could do by
       ;; scanning the svtv-spec alists instead) and to get the names of
       ;; functions/theorems.
       ;; ((mv err svtv-val) (magic-ev-fncall svtv-thm.svtv nil state t t))
       ;; ((when err) (er hard ctx "Couldn't evaluate ~x0" (list svtv-thm.svtv))
       ;;  )
       ((mv err svtv-spec-val) (magic-ev-fncall svtv-thm.svtv-spec nil state t t))
       ((when err) (er hard ctx "Couldn't evaluate ~x0" (list svtv-thm.svtv-spec)))
       ((svtv-spec svtv-spec-val))
       ((acl2::with-fast svtv-spec-val.namemap))

       (primary-output-var (or primary-output-var (car svtv-thm.output-vars)))

       (svtv-actual-override-vars (svex-alistlist-vars svtv-spec-val.override-val-alists))
       (svtv-actual-input-vars  (svex-alistlist-vars svtv-spec-val.in-alists))
       (svtv-actual-override-signals (svex-alistlist-all-keys svtv-spec-val.override-val-alists))

       (thm-spec-override-vars (append (strip-cars svtv-thm.spec-override-var-bindings) svtv-thm.spec-override-vars))
       (thm-input-vars (append (strip-cars svtv-thm.input-var-bindings) svtv-thm.input-vars))
       (thm-override-vars (append (strip-cars svtv-thm.override-var-bindings) svtv-thm.override-vars))

       ;; Sometimes spec-override-vars are listed as inputs. Correct this...
       (real-spec-override-vars (acl2::hons-intersection
                                 (append thm-input-vars thm-spec-override-vars)
                                 svtv-actual-override-vars))
       (real-input-vars (acl2::hons-intersection thm-input-vars svtv-actual-input-vars))



       (eliminate-all-overrides (or (eq eliminate-override-signals :all)
                                    (eq eliminate-override-vars :all)))

       ((unless (or eliminate-all-overrides
                    (acl2::hons-subset eliminate-override-vars real-spec-override-vars)))
        (let ((missing (hons-set-diff eliminate-override-vars real-spec-override-vars)))
          (er hard? ctx "The ~x0 must be a subset of the theorem's spec-override-vars, but the following are not: ~x1"
              :eliminate-override-vars missing)))
       ((unless (or eliminate-all-overrides
                    (acl2::hons-subset eliminate-override-signals svtv-actual-override-signals)))
        (let ((missing (hons-set-diff eliminate-override-signals svtv-actual-override-signals)))
          (er hard? "The ~x0 must be a subset of the SVTV's overridden signals, but the following are not: ~x1"
              :eliminate-override-signals missing)))

       (hyps (append (svtv-genthm-hyp-to-list svtv-thm.user-final-hyp)
                     (svtv-genthm-input-binding-hyp-termlist svtv-thm.input-var-bindings)
                     (svtv-genthm-input-binding-hyp-termlist (append svtv-thm.spec-override-var-bindings
                                                                     svtv-thm.override-var-bindings))
                     (svtv-genthm-hyp-to-list svtv-thm.final-hyp)
                     (svtv-genthm-hyp-to-list svtv-thm.hyp)))

       (remaining-override-vars (and (not eliminate-all-overrides)
                                     (hons-set-diff real-spec-override-vars eliminate-override-vars)))
       (new-eliminated-override-vars (if eliminate-all-overrides
                                         real-spec-override-vars
                                       eliminate-override-vars))
       (all-eliminated-override-vars (append thm-override-vars
                                             new-eliminated-override-vars))

       (override-test-svtv-env (svtv-genthm-override-test-alist
                                remaining-override-vars
                                svtv-thm.triple-val-alist svtv-thm.triples-name))
       (override-test-envs (if eliminate-all-overrides
                               (make-list (len svtv-spec-val.override-test-alists) :initial-element nil)
                             (with-fast-alist override-test-svtv-env
                               (svex-envlist-1mask
                                (svex-alistlist-eval
                                 (svtv-fsm-namemap-alistlist
                                  (svex-alistlist-removekeys eliminate-override-signals svtv-spec-val.override-test-alists)
                                  svtv-spec-val.namemap
                                  :test)
                                 override-test-svtv-env))))))
    (make-svtv-to-fsm-thm
     :thmname thmname
     :svtv-spec-thmname svtv-spec-thmname
     :fsmname fsm
     :svtv svtv-thm.svtv
     :svtv-spec svtv-thm.svtv-spec
     :triples-name svtv-thm.triples-name

     :input-vars real-input-vars
     :override-vars thm-override-vars
     :spec-override-vars real-spec-override-vars
     :output-vars svtv-thm.output-vars

     ;; :eliminate-override-vars (and (not eliminate-all-overrides) eliminate-override-vars)
     ;; :eliminate-override-signals (and (not eliminate-all-overrides) eliminate-override-signals)
     ;; :eliminate-all-overrides eliminate-all-overrides
     :remaining-override-vars remaining-override-vars
     :new-eliminated-override-vars new-eliminated-override-vars
     :all-eliminated-override-vars all-eliminated-override-vars

     :override-test-envs override-test-envs

     :outmap (svtv-probealist-to-lhprobe-map svtv-spec-val.probes svtv-spec-val.namemap)
     :bindings (svtv-spec-fsm-bindings svtv-spec-val)
     :triple-val-alist svtv-thm.triple-val-alist
     :run-length (len (svtv-probealist-outvars svtv-spec-val.probes))

     :hyp `(and . ,hyps)
     :concl svtv-thm.concl
     :rule-classes rule-classes

     :cycle-num-rewrite-strategy cycle-num-rewrite-strategy
     :base-cycle-var base-cycle-var
     :primary-output-var primary-output-var
     :pkg-sym pkg-sym)))

(define svtv-to-fsm-thm-fn (thmname args state)
  :mode :program
  (b* ((x (parse-svtv-to-fsm-thm thmname args state)))
    (list 'progn
          (svtv-to-fsm-first-thm x)
          (svtv-to-fsm-final-thm x))))

(defmacro def-svtv-to-fsm-thm (thmname &rest args)
  `(make-event
    (svtv-to-fsm-thm-fn ',thmname ',args state)))






(defxdoc def-svtv-to-fsm-thm
  :parents (svex-decomposition-methodology)
  :short "Lower a theorem about a SVTV-SPEC to a statement about the underlying FSM."
  :long "

<p> This macro takes an existing theorem about an SVTV-SPEC and turns it into a
theorem about the cycle FSM underlying it.  This can be useful in order to
compose together theorems about multiple SVTVs that are based on the same FSM,
and to prove non-fixed temporal properties that can't be stated at the SVTV
level.</p>

<p>Usage example (from svtv-to-fsm-test.lisp):</p>
@({
 (def-svtv-to-fsm-thm counter-invar-fsm-thm
   :svtv-spec-thmname counter-invar-svtv-thm
; optional arguments
   :eliminate-override-vars (sum1)
   :eliminate-override-signals (\"sum1\")
   :rule-classes :rewrite    ;; this is the default
   :cycle-num-rewrite-strategy :by-cycle ;; this is the default
   :primary-output-var (sum-out)
   :base-cycle-var base-cycle  ;; this is the default
   :pkg-sym symbol-from-my-package)
 })

<p> Prerequisites. As with @(see def-svtv-generalized-thm), we need to first
show that the override transparency property holds of our SVTV and its
underlying FSM, using @(see def-svtv-refinement). For following
@('def-svtv-to-fsm-thm') events to work, @(see def-svtv-refinement) must be
invoked with the @(':svtv-spec') and @(':fsm-name') options. Unless the FSM is
already defined, the @(':define-fsm') option should be set as well.  For
example (from svtv-to-fsm-test.lisp):</p>

@({
 (def-svtv-refinement counter-invar-run counter-invar-run-data
   :svtv-spec counter-invar-spec
   :inclusive-overridekeys t
   :fsm counter-fsm
   :define-fsm t)
 })

<p>In addition, the theorem to be lowered to the FSM level should be one resulting from an invocation of @(see def-svtv-generalized-thm) with the @(':svtv-spec') option -- e.g.:</p>

@({
 (def-svtv-generalized-thm counter-invar-svtv-thm
   :svtv counter-invar-run
   :svtv-spec counter-invar-spec
   :input-vars :all
   :output-vars (sum-out sum1-out)
   :override-vars (sum)
   :spec-override-vars (sum1)
   :unsigned-byte-hyps t
   :hyp (and (<= sum 11)
             (<= sum1 10))
   :concl (and (<= sum-out 11)
               (<= sum1-out 10)))
 })

<p>Note: At the moment, the ideal FSM-based methodology isn't yet supported; it
should work, but we haven't gotten to it yet.</p>

<p>Given these two previous events, we have:</p>

<ul>
 <li>an FSM, @('counter-fsm')</li>
 <li>an @(see svtv-spec) object specifying a run of that FSM on a symbolic but temporally fixed sequence of inputs and a set of outputs to sample at fixed times in that sequence</li>
 <li>an @(see svtv) containing combinational @(see svex) expressions representing the outputs of the above @(see svtv-spec) in terms of their symbolic inputs, assuming initial states and all other inputs are X</li>
 <li>a theorem about the svtv-spec (likely proved by symbolic execution of the svtv).</li>
</ul>

<p>We now want to lower the theorem about the svtv-spec to a theorem about the FSM.  The following form
proves one:</p>

@({
 (def-svtv-to-fsm-thm counter-invar-fsm-thm
   :svtv-spec-thmname counter-invar-svtv-thm
   :fsm counter-fsm)
 })

<h3>Arguments</h3>

<p>The first argument to the macro gives the name of the theorem to be
generated.  The rest are keyword arguments:</p>

<ul>

<li>@(':svtv-spec-thmname') (required): The name of the theorem, generated by
@(see def-svtv-generalized-thm), that the new theorem is to be derived
from.</li>

 <li>@(':eliminate-override-vars'): Either @(':all') or a list of SVTV variables
that were left overridden in the svtv-spec-thm that we want to instead sample
as outputs in this theorem.  Typically these were ones listed as
@(':spec-override-vars') in the svtv-spec theorem, although they may in some
cases be listed as @(':input-vars').  If @(':all'), then all signals overridden
in the theorem will be eliminated and sampled as outputs, even ones that were
hard-coded overrides in the SVTV.</li>

 <li>@(':eliminate-override-signals'): Either @(':all') or a list of signal
names -- strings, like the signal names used in @(see defsvtv$) -- that are
overridden unconditionally in the SVTV that we instead want to sample as
outputs in this theorem.  Setting this to @(':all') has the same effect as
setting @(':eliminate-override-vars') to @(':all').</li>

 <li>@(':rule-classes'): the rule-classes argument for the final
theorem. Defaults to @(':rewrite').  Note that the final theorem may not be in
a very good form for a non-rewrite rule.</li>

<li>@(':cycle-num-rewrite-strategy'): one of @(':all-free'),
@(':by-cycle') (the default), or @(':single-var').  This affects the form of
the rewrite rule and how aggressively it tries to match the possible forms of
the cycle numbers at which signals are sampled.  In all three cases, every SVTV
variable mentiond in the theorem is bound to @('(lhs-eval-zx LHS (nth CYCLE
envs/outs))') where envs/outs is either the list of input environments or
outputs of the FSM simulation, LHS is canonical form of the concatenation of
variable selects comprising that SVTV variable, and CYCLE is some expression
giving the cycle number at which the variable is sampled or provided as input.
The form of CYCLE affects how the rule applies as a rewrite rule.  Ultimately,
all such cycles are relative to some base cycle, the first cycle at which any
variables are sampled from the envs/outs.  But if we express all cycles as
offsets relative to that base cycle, then it will be difficult to apply this
theorem as a rewrite rule: the left-hand side will contain expressions such as
@('(+ N base-cycle)') for various constant values of N, and these may not match
the way these cycle numbers are expressed in the target term.  This is still a
good option if we don't intend to use this as a rewrite rule or if the SVTV is
purely combinational so that everything happens in a single cycle; this is what
we do under the @(':single-var') setting.  Otherwise, we can use free variables
that are constrained to their proper values by hypotheses so as to make the
rewrite rule easier to apply.  Under the setting @(':all-free'), every SVTV
variable has a corresponding cycle-number variable that are all
independent (until restricted by the hypotheses).  Under the setting
@(':by-cycle'), there is one cycle-number variable for each cycle in which a
variable is sampled.</li>

 <li>@(':primary-output-var'): This is irrelevant if the
@(':cycle-num-rewrite-strategy') is set to @(':single-var').  Otherwise, this
should be set to the name of an output that is sampled in the
svtv-spec-thm (i.e., listed in the @(':output-vars') of the @(see
def-svtv-generalized-thm) form).  For best behavior as a rewrite rule, this
variable should occur in the LHS of the conclusion.  When applied as a rewrite
rule, this variable will essentially match an expression such as
@('(lhs-eval-zx \"signal\" (nth (+ 3 k) outs))') where outs is an evaluation
of the FSM. This will determine the time offset (here @('(+ 3 k)') minus the
time offset of this output variable in the SVTV) for this application of the
theorem.  If not specified, we pick an arbitrary variable from the SVTV
theorem's output-vars.</li>

 <li>@(':base-cycle-var'): A variable name to be used in the final theorem;
it's only important that it doesn't conflict with other variable names.  The
default is @('sv::base-cycle').</li>

 <li>@(':pkg-sym'): symbol that determines the package in which to put newly
generated names.  Defaults to the theorem name.</li>
</ul>

")

(define svtv-spec-cycle-fsm-inputsubsts ((x svtv-spec-p))
  :returns (substs svex-alistlist-p)
  (b* (((svtv-spec x)))
    (svtv-fsm-to-fsm-inputsubsts
     (take (len (svtv-probealist-outvars x.probes))
           x.in-alists)
     x.override-val-alists
     x.override-test-alists
     x.namemap))
  ///
  (defretd eval-of-<fn>
    (equal (svex-alistlist-eval substs env)
           (svtv-spec-pipe-env->cycle-envs x env))
    :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->cycle-envs)))))


(defthmd svtv-spec-pipe-env->cycle-envs-in-terms-of-inputsubst
  (equal (svtv-spec-pipe-env->cycle-envs x env)
         (svex-alistlist-eval (svtv-spec-cycle-fsm-inputsubsts x) env))
  :hints(("Goal" :in-theory (enable eval-of-svtv-spec-cycle-fsm-inputsubsts))))


(defthmd svtv-spec-cycle-fsm-inputsubsts-expand
  (implies (and (equal spec-eval (force-execute spec))
                (syntaxp (quotep spec-eval)))
           (equal (svtv-spec-cycle-fsm-inputsubsts spec)
                  (force-execute (sv::svtv-spec-cycle-fsm-inputsubsts spec-eval))))
  :hints(("Goal" :in-theory (enable force-execute))))


(defthmd lhs-eval-zx-of-svex-alist-eval
  (implies (and (syntaxp (and (quotep lhs) (quotep alist)))
                (equal subst (force-execute (lhs-subst-zero lhs alist))))
           (equal (lhs-eval-zx lhs (svex-alist-eval alist env))
                  (svex-eval subst env)))
  :hints(("Goal" :in-theory (enable force-execute))))

(defthmd unsigned-byte-p-of-4vec-concat
  (implies (and (integerp x)
                (natp n))
           (unsigned-byte-p n (4vec-concat n x 0)))
  :hints(("Goal" :in-theory (enable 4vec-concat
                                    4vec->upper
                                    4vec->lower
                                    4vec-fix 4vec))))


(defthmd svex-alist-eval-when-const
  (implies (and (syntaxp (quotep alist))
                (equal (svex-alist-vars alist) nil))
           (equal (svex-alist-eval alist env)
                  (force-execute (svex-alist-eval alist nil))))
  :hints(("Goal" :in-theory (enable force-execute
                                    svex-alist-eval-equal-when-extract-vars-similar))))



(encapsulate nil
  (local (defthm svex-alist-eval-of-nth
           (equal (svex-alist-eval (nth n x) env)
                  (nth n (svex-alistlist-eval x env)))))
  (local (in-theory (disable nth-of-svex-alistlist-eval)))
  
  (defthmd lhs-eval-zx-of-svtv-spec-pipe-env->cycle-envs
    (implies (and (syntaxp (and (quotep lhs)
                                (quotep n)))
                  (equal substs (force-execute (svtv-spec-cycle-fsm-inputsubsts spec)))
                  (syntaxp (quotep substs))
                  (equal subst (force-execute (lhs-subst-zero lhs (nth n substs)))))
             (equal (sv::lhs-eval-zx lhs (nth n (svtv-spec-pipe-env->cycle-envs spec env)))
                    (svex-eval subst env)))
    :hints(("Goal" :in-theory (enable force-execute
                                      eval-of-svtv-spec-cycle-fsm-inputsubsts)))))


(defthmd svex-envs-ovtestsimilar-of-svex-alist-eval-quote
  (implies (and (syntaxp (quotep alist))
                (equal test-alist (sv::force-execute (sv::svex-alist-filter-override alist :test)))
                (syntaxp (not (equal test-alist alist))))
           (equal (sv::svex-envs-ovtestsimilar (sv::svex-alist-eval alist env) other)
                  (sv::svex-envs-ovtestsimilar (sv::svex-alist-eval test-alist env) other)))
  :hints(("Goal" :in-theory (enable sv::force-execute)
          :cases ((sv::svex-envs-ovtestsimilar (sv::svex-alist-eval alist env) other)))
         (and stable-under-simplificationp
              '(:in-theory (enable sv::svex-envs-ovtestsimilar))))
  :otf-flg t)


(defthmd svex-envs-ovtestsimilar-of-quote
  (implies (and (syntaxp (quotep alist))
                (equal test-alist (sv::force-execute (sv::svex-env-1mask (sv::svex-env-filter-override alist :test))))
                (syntaxp (not (equal test-alist alist))))
           (equal (sv::svex-envs-ovtestsimilar alist other)
                  (sv::svex-envs-ovtestsimilar test-alist other)))
  :hints(("Goal" :in-theory (enable sv::force-execute)
          :cases ((sv::svex-envs-ovtestsimilar alist other)))
         (and stable-under-simplificationp
              '(:in-theory (enable sv::svex-envs-ovtestsimilar))))
  :otf-flg t)
