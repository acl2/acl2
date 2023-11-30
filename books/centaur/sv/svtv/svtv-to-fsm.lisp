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
(include-book "svtv-generalize-defs")
(include-book "override-envlist-defs")
(include-book "fsm-override-transparency")
(local (include-book "svtv-spec-override-transparency"))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

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

 - svtv-fsm-to-base-fsm-inputs on those envlists, resulting in a cyclewise list of
combined envs in terms of the FSM variables

 - svtv-cycle-run-fsm-inputs on that envlist, resulting in a phasewise list of
combined envs in terms of the FSM variables.

The initial state for the phase FSM is also derived from the pipe env, just by evaluating the initst-alist.

Portions of the inputs and initial state that are still X can then be
overridden with values by the base-ins and initst envs (except we assume that
no override tests are bound in the base-ins).  This ensures that the final
inputs to base-fsm-eval are latticewise greater than or equal the ones strictly
derived from the pipeline env, and the same on override-tests.

The phase FSM is evaluated on the resulting envlist/initst using base-fsm-eval.
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
Suppose our FSM theorem is about (base-fsm-eval envs initst fsm) -- we then
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

(define svar/4vec-p (x)
  :short "Recognizer for an object that is either an @(see svar) or @(see 4vec)"
  (or (svar-p x) (4vec-p x)))

(define svar/4vec-kind ((x svar/4vec-p))
  :parents (svar/4vec-p)
  :short "Kind function for svar/4vec type"
  :returns (kind (and (symbolp kind)
                      (not (booleanp kind)))
                 :rule-classes :type-prescription)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svar/4vec-p svar-p 4vec-p))))
  (if (consp x)
      (if (integerp (car x))
          :4vec
        :svar)
    (if (integerp x) :4vec (if (mbt (and x t)) :svar :4vec)))
  ///
  (defthm svar/4vec-kind-possibilities
    (or (equal (svar/4vec-kind x) :4vec)
        (equal (svar/4vec-kind x) :svar))
    :rule-classes ((:forward-chaining :trigger-terms ((svar/4vec-kind x)))))
  
  (defthm svar/4vec-p-when-when-kind-is-4vec
    (implies (equal (svar/4vec-kind x) :4vec)
             (equal (svar/4vec-p x) (4vec-p x)))
    :hints(("Goal" :in-theory (enable svar/4vec-p svar-p))))

  (defthm svar/4vec-p-when-when-kind-is-svar
    (implies (equal (svar/4vec-kind x) :svar)
             (equal (svar/4vec-p x) (svar-p x)))
    :hints(("Goal" :in-theory (enable svar/4vec-p 4vec-p))))

  (defthm svar/4vec-kind-when-svar-p
    (implies (svar-p x)
             (Equal (svar/4vec-kind x) :svar))
    :hints(("Goal" :in-theory (enable svar-p))))

  (defthm svar/4vec-kind-when-4vec-p
    (implies (4vec-p x)
             (Equal (svar/4vec-kind x) :4vec))
    :hints(("Goal" :in-theory (enable 4vec-p)))))

(defmacro svar/4vec-case (x &rest args)
  (fty::kind-casemacro-fn x args
                          '(svar/4vec-case svar/4vec-kind (:4vec 4vec) (:svar svar))))

(define svar/4vec-fix ((x svar/4vec-p))
  :returns (new-x svar/4vec-p :hints(("Goal" :in-theory (enable svar/4vec-p))))
  :parents (svar/4vec-p)
  :short "Fixing function for svar/4vec type"
  :hooks nil
  (mbe :logic (if (eq (svar/4vec-kind x) :4vec)
                  (4vec-fix x)
                (svar-fix x))
       :exec x)
  ///

  (defthm svar/4vec-fix-when-svar/4vec-p
    (implies (svar/4vec-p x)
             (equal (svar/4vec-fix x) x)))

  (fty::deffixtype svar/4vec :pred svar/4vec-p :fix svar/4vec-fix :equiv svar/4vec-equiv :define t)

  (defthm svar/4vec-fix-when-kind-is-4vec
    (implies (equal (svar/4vec-kind x) :4vec)
             (equal (svar/4vec-fix x) (4vec-fix x))))
  
  (defthm svar/4vec-fix-when-kind-is-svar
    (implies (equal (svar/4vec-kind x) :svar)
             (equal (svar/4vec-fix x) (svar-fix x))))

  (fty::deffixequiv svar/4vec-kind))


(defthm svex-p-when-svar/4vec-p
  (implies (svar/4vec-p x)
           (svex-p x))
  :hints(("Goal" :in-theory (enable svar/4vec-p svar-p 4vec-p svex-p))))

(defthm svar/4vec-p-when-svex-p
  (implies (and (not (svex-case x :call))
                (svex-p x))
           (svar/4vec-p x))
  :hints(("Goal" :in-theory (enable svar/4vec-p svar-p 4vec-p svex-p svex-kind))))

(defthm svar/4vec-fix-of-svex-fix
  (implies (not (svex-case x :call))
           (equal (svar/4vec-fix (svex-fix x))
                  (svar/4vec-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-fix svex-fix svex-kind
                                    svar/4vec-kind)
          :expand ((svex-fix x)))))

(defthmd svar/4vec-fix-in-terms-of-svex-fix
  (implies (not (svex-case x :call))
           (equal (svar/4vec-fix x)
                  (svex-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-fix svex-fix svex-kind
                                    svar/4vec-kind)
          :expand ((svex-fix x)))))

(defthmd svar/4vec-kind-when-svex-kind
  (implies (not (svex-case x :call))
           (equal (svar/4vec-kind x)
                  (if (equal (svex-kind x) :quote) :4vec :svar)))
  :hints(("Goal" :in-theory (enable svex-kind svar/4vec-kind))))

(define svar/4vec-eval ((x svar/4vec-p) (env svex-env-p))
  :returns (val 4vec-p)
  (svar/4vec-case x
    :4vec (4vec-fix x)
    :svar (svex-env-lookup x env))
  ///
  (defthmd svar/4vec-eval-in-terms-of-svex-eval
    (implies (not (svex-case x :call))
             (equal (svar/4vec-eval x env)
                    (svex-eval x env)))
    :hints (("goal" :expand ((svex-eval x env))
             :in-theory (enable svex-var->name svex-quote->val
                                svar/4vec-kind-when-svex-kind))))

  (defthm svar/4vec-eval-of-quote
    (implies (syntaxp (quotep x))
             (equal (svar/4vec-eval x env)
                    (svar/4vec-case x
                      :4vec (4vec-fix x)
                      :svar (svex-env-lookup x env))))))

(fty::defmap svar/4vec-alist :key-type svar :val-type svar/4vec-p :true-listp t)

(defthm svex-alist-p-when-svar/4vec-alist-p
  (implies (svar/4vec-alist-p x)
           (svex-alist-p x))
  :hints(("Goal" :in-theory (enable svar/4vec-alist-p svex-alist-p))))


(defthm svar/4vec-alist-p-when-svex-alist-p
  (implies (and (svex-alist-noncall-p x)
                (svex-alist-p x))
           (svar/4vec-alist-p x))
  :hints(("Goal" :in-theory (enable svex-alist-noncall-p
                                    svex-alist-p
                                    svar/4vec-alist-p))))

(defthm svar/4vec-alist-fix-of-svex-alist-fix
  (implies (svex-alist-noncall-p x)
           (equal (svar/4vec-alist-fix (svex-alist-fix x))
                  (svar/4vec-alist-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-alist-fix svex-alist-fix
                                    svex-alist-noncall-p
                                    svar/4vec-fix-in-terms-of-svex-fix))))

(defthmd svar/4vec-alist-fix-in-terms-of-svex-alist-fix
  (implies (svex-alist-noncall-p x)
           (equal (svar/4vec-alist-fix x)
                  (svex-alist-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-alist-fix svex-alist-fix
                                    svex-alist-noncall-p
                                    svar/4vec-fix-in-terms-of-svex-fix))))

(define svar/4vec-alist-eval ((x svar/4vec-alist-p) (env svex-env-p))
  :returns (val svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svar/4vec-alist-eval (cdr x) env)))
    (cons (cons (caar x) (svar/4vec-eval (cdar x) env))
          (svar/4vec-alist-eval (cdr x) env)))
  ///
  (defthmd svar/4vec-alist-eval-in-terms-of-svex-alist-eval
    (implies (svex-alist-noncall-p x)
             (equal (svar/4vec-alist-eval x env)
                    (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval
                                      svex-alist-noncall-p
                                      svar/4vec-eval-in-terms-of-svex-eval))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup v val)
           (let ((look (hons-assoc-equal (svar-fix v) (svar/4vec-alist-fix x))))
             (if look
                 (svar/4vec-eval (cdr look) env)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons))))
  
  (local (in-theory (enable svar/4vec-alist-fix))))
       

(fty::deflist svar/4vec-alistlist :elt-type svar/4vec-alist :true-listp t)

(defthm svex-alistlist-p-when-svar/4vec-alistlist-p
  (implies (svar/4vec-alistlist-p x)
           (svex-alistlist-p x))
  :hints(("Goal" :in-theory (enable svar/4vec-alistlist-p svex-alistlist-p))))


(defthm svar/4vec-alistlist-p-when-svex-alistlist-p
  (implies (and (svex-alistlist-noncall-p x)
                (svex-alistlist-p x))
           (svar/4vec-alistlist-p x))
  :hints(("Goal" :in-theory (enable svex-alistlist-noncall-p
                                    svex-alistlist-p
                                    svar/4vec-alistlist-p))))

(defthm svar/4vec-alistlist-fix-of-svex-alistlist-fix
  (implies (svex-alistlist-noncall-p x)
           (equal (svar/4vec-alistlist-fix (svex-alistlist-fix x))
                  (svar/4vec-alistlist-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-alistlist-fix svex-alistlist-fix
                                    svex-alistlist-noncall-p
                                    svar/4vec-alist-fix-in-terms-of-svex-alist-fix))))

(defthmd svar/4vec-alistlist-fix-in-terms-of-svex-alistlist-fix
  (implies (svex-alistlist-noncall-p x)
           (equal (svar/4vec-alistlist-fix x)
                  (svex-alistlist-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-alistlist-fix svex-alistlist-fix
                                    svex-alistlist-noncall-p
                                    svar/4vec-alist-fix-in-terms-of-svex-alist-fix))))

(define svar/4vec-alistlist-eval ((x svar/4vec-alistlist-p) (env svex-env-p))
  :returns (val svex-envlist-p)
  (if (atom x)
      nil
    (cons (svar/4vec-alist-eval (car x) env)
          (svar/4vec-alistlist-eval (cdr x) env)))
  ///
  (defthmd svar/4vec-alistlist-eval-in-terms-of-svex-alistlist-eval
    (implies (svex-alistlist-noncall-p x)
             (equal (svar/4vec-alistlist-eval x env)
                    (svex-alistlist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-alistlist-eval
                                      svex-alistlist-noncall-p
                                      svar/4vec-alist-eval-in-terms-of-svex-alist-eval)))))
  



(defprod lhprobe
  :short "Product type pairing an LHS (some list of FSM signal segments) and a
stage number, signifying the concatenated value of those segments at that
time."
  ((lhs lhs-p)
   (stage natp :rule-classes :type-prescription))
  :layout :fulltree)


(defthm lhatom-eval-zero-when-envs-agree
  (implies (svex-envs-agree (lhatom-vars x) env1 env2)
           (equal (lhatom-eval-zero x env1)
                  (lhatom-eval-zero x env2)))
  :hints(("Goal" :in-theory (enable lhatom-eval-zero
                                    lhatom-vars)
          :expand ((:free (v) (svex-envs-agree (list v) env1 env2))))))

(define lhs-eval-ext ((x lhs-p) (env svex-env-p))
  :returns (val 4vec-p)
  (if (atom x)
      0
    (if (atom (cdr x))
        (4vec-sign-ext (2vec (lhrange->w (car x)))
                       (lhatom-eval-zero (lhrange->atom (car x)) env))
      (4vec-concat (2vec (lhrange->w (car x)))
                   (lhatom-eval-zero (lhrange->atom (car x)) env)
                   (lhs-eval-ext (cdr x) env))))
  ///
  (defcong svex-envs-similar equal (lhs-eval-ext x env) 2
    :hints(("Goal" :in-theory (enable lhatom-eval-zero)))))

(defthm lhs-eval-zero-when-envs-agree
  (implies (svex-envs-agree (lhs-vars x) env1 env2)
           (equal (lhs-eval-zero x env1)
                  (lhs-eval-zero x env2)))
  :hints(("Goal" :in-theory (enable lhs-eval-zero
                                    lhs-vars))))

(defthm lhs-eval-ext-when-envs-agree
  (implies (svex-envs-agree (lhs-vars x) env1 env2)
           (equal (lhs-eval-ext x env1)
                  (lhs-eval-ext x env2)))
  :hints(("Goal" :in-theory (enable lhs-eval-ext
                                    lhs-vars))))

(define svex-envlists-agree ((vars svarlist-p)
                             (x svex-envlist-p)
                             (y svex-envlist-p))
  (if (atom x)
      (atom y)
    (and (consp y)
         (svex-envs-agree vars (car x) (car y))
         (svex-envlists-agree vars (cdr x) (cdr y))))
  ///
  (defthm svex-envs-agree-nth-when-svex-envlists-agree
    (implies (svex-envlists-agree vars x y)
             (svex-envs-agree vars (nth n x) (nth n y))))

  (defthm svex-envlists-agree-of-append-vars
    (iff (svex-envlists-agree (append vars1 vars2) x y)
         (and (svex-envlists-agree vars1 x y)
              (svex-envlists-agree vars2 x y)))))


(define lhprobe-eval ((x lhprobe-p)
                      (envs svex-envlist-p))
  :parents (lhprobe)
  :short "Evaluator for an @(see lhprobe) with respect to an envlist giving the values of signals over time."
  :returns (val 4vec-p)
  (b* (((lhprobe x))
       (env (nth x.stage envs)))
    (lhs-eval-ext x.lhs env)))



(define lhprobe-vars ((x lhprobe-p))
  :parents (lhprobe)
  :short "Collect variables present in an lhprobe"
  :returns (vars svarlist-p)
  (b* (((lhprobe x)))
    (lhs-vars x.lhs))
  ///


  (defthm svex-env-extract-nil-under-svex-envs-similar
    (svex-envs-similar (svex-env-extract vars nil) nil)
    :hints(("Goal" :in-theory (enable svex-envs-similar))))
  
  (defthm nth-of-svex-envlist-extract
    (svex-envs-similar (nth n (svex-envlist-extract-keys vars x))
                       (svex-env-extract vars (nth n x)))
    :hints(("Goal" :in-theory (enable svex-envlist-extract-keys))))


  (defthm lhs-eval-ext-of-svex-env-extract
    (implies (subsetp-equal (lhs-vars x) (Svarlist-fix vars))
             (equal (lhs-eval-ext x (svex-env-extract vars env))
                    (lhs-eval-ext x env)))
    :hints(("Goal" :in-theory (enable lhs-eval-ext
                                      lhatom-vars
                                      lhatom-eval-zero))))
  
  (defthm lhprobe-eval-of-svex-envlist-extract-vars
    (implies (subsetp-equal (lhprobe-vars x) (Svarlist-fix vars))
             (equal (lhprobe-eval x (svex-envlist-extract-keys vars envs))
                    (lhprobe-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe-eval))))

  (defthm lhprobe-eval-when-envs-agree
    (implies (svex-envlists-agree (lhprobe-vars x) envs1 envs2)
             (equal (lhprobe-eval x envs1)
                    (lhprobe-eval x envs2)))
    :hints(("Goal" :in-theory (enable lhprobe-eval
                                      lhprobe-vars))
           (and stable-under-simplificationp
                '(:use ((:instance lhs-eval-ext-when-envs-agree
                         (x (lhprobe->lhs x))
                         (env1 (nth (lhprobe->stage x) envs1))
                         (env2 (nth (lhprobe->stage x) envs2)))))))))


(define lhprobe-change-override ((x lhprobe-p)
                                 (type svar-overridetype-p))
  :returns (new-x lhprobe-p)
  (change-lhprobe x :lhs (lhs-change-override (lhprobe->lhs x) type)))



(fty::defmap lhprobe-map :key-type svar :val-type lhprobe :true-listp t
  :short "Mapping from variables to lhprobes, identifying SVTV variables with signals at a time")


(define lhprobe-map-eval ((x lhprobe-map-p)
                          (envs svex-envlist-p))
  :returns (eval svex-env-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (lhprobe-map-eval (cdr x) envs)))
    (cons (cons (caar x) (lhprobe-eval (cdar x) envs))
          (lhprobe-map-eval (cdr x) envs)))
  ///
  (defret lookup-of-<fn>
    (equal (svex-env-lookup v eval)
           (let ((look (hons-assoc-equal (svar-fix v) (lhprobe-map-fix x))))
             (if look
                 (lhprobe-eval (cdr look) envs)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons))))
  (local (in-theory (enable lhprobe-map-fix))))


(define lhprobe-map-vars ((x lhprobe-map-p))
  :parents (lhprobe)
  :short "Collect variables present in an lhprobe-map"
  :returns (vars svarlist-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (lhprobe-map-vars (cdr x))))
    (append (lhprobe-vars (cdar x))
            (lhprobe-map-vars (cdr x))))
  ///

  (defthm lhprobe-map-eval-of-svex-envlist-extract-vars
    (implies (subsetp-equal (lhprobe-map-vars x) (Svarlist-fix vars))
             (equal (lhprobe-map-eval x (svex-envlist-extract-keys vars envs))
                    (lhprobe-map-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe-map-eval))))

  (local (in-theory (enable lhprobe-map-fix)))

  (defthm lhprobe-map-eval-when-envs-agree
    (implies (svex-envlists-agree (lhprobe-map-vars x) envs1 envs2)
             (equal (lhprobe-map-eval x envs1)
                    (lhprobe-map-eval x envs2)))
    :hints(("Goal" :in-theory (enable lhprobe-map-eval
                                      lhprobe-map-vars)))))
       


(define lhprobe/4vec-p (x)
  :short "Recognizer for an object that is either a @(see lhprobe) or @(see 4vec)."
  (or (lhprobe-p x) (4vec-p x)))

(define lhprobe/4vec-kind ((x lhprobe/4vec-p))
  :parents (lhprobe/4vec-p)
  :short "Kind function for lhprobe/4vec type"
  :returns (kind (and (symbolp kind)
                      (not (booleanp kind)))
                 :rule-classes :type-prescription)
  (if (or (atom x)
          (integerp (car x)))
      :4vec
    :lhprobe)
  ///
  (defthm lhprobe/4vec-kind-possibilities
    (or (equal (lhprobe/4vec-kind x) :4vec)
        (equal (lhprobe/4vec-kind x) :lhprobe))
    :rule-classes ((:forward-chaining :trigger-terms ((lhprobe/4vec-kind x)))))
  
  (defthm lhprobe/4vec-p-when-when-kind-is-4vec
    (implies (equal (lhprobe/4vec-kind x) :4vec)
             (equal (lhprobe/4vec-p x) (4vec-p x)))
    :hints(("Goal" :in-theory (enable lhprobe/4vec-p lhprobe-p))))

  (defthm lhprobe/4vec-p-when-when-kind-is-lhprobe
    (implies (equal (lhprobe/4vec-kind x) :lhprobe)
             (equal (lhprobe/4vec-p x) (lhprobe-p x)))
    :hints(("Goal" :in-theory (enable lhprobe/4vec-p 4vec-p))))

  (defthm lhprobe/4vec-kind-when-lhprobe-p
    (implies (lhprobe-p x)
             (Equal (lhprobe/4vec-kind x) :lhprobe))
    :hints(("Goal" :in-theory (enable lhprobe-p))))

  (defthm lhprobe/4vec-kind-when-4vec-p
    (implies (4vec-p x)
             (Equal (lhprobe/4vec-kind x) :4vec))
    :hints(("Goal" :in-theory (enable 4vec-p)))))

(defmacro lhprobe/4vec-case (x &rest args)
  (fty::kind-casemacro-fn x args
                          '(lhprobe/4vec-case lhprobe/4vec-kind (:4vec 4vec) (:lhprobe lhprobe))))

(define lhprobe/4vec-fix ((x lhprobe/4vec-p))
  :parents (lhprobe/4vec-p)
  :hooks nil
  :short "Fixing function for lhprobe/4vec type"
  :returns (new-x lhprobe/4vec-p :hints(("Goal" :in-theory (enable lhprobe/4vec-p))))
  (mbe :logic (if (eq (lhprobe/4vec-kind x) :4vec)
                  (4vec-fix x)
                (lhprobe-fix x))
       :exec x)
  ///

  (defthm lhprobe/4vec-fix-when-lhprobe/4vec-p
    (implies (lhprobe/4vec-p x)
             (equal (lhprobe/4vec-fix x) x)))

  (fty::deffixtype lhprobe/4vec :pred lhprobe/4vec-p :fix lhprobe/4vec-fix :equiv lhprobe/4vec-equiv :define t)

  (defthm lhprobe/4vec-fix-when-kind-is-4vec
    (implies (equal (lhprobe/4vec-kind x) :4vec)
             (equal (lhprobe/4vec-fix x) (4vec-fix x))))
  
  (defthm lhprobe/4vec-fix-when-kind-is-lhprobe
    (implies (equal (lhprobe/4vec-kind x) :lhprobe)
             (equal (lhprobe/4vec-fix x) (lhprobe-fix x))))

  (fty::deffixequiv lhprobe/4vec-kind))

(define lhprobe/4vec-eval ((x lhprobe/4vec-p)
                           (envs svex-envlist-p))
  :short "Evaluator for @(see lhprobe/4vec-p) objects"
  :parents (lhprobe/4vec-p)
  :returns (val 4vec-p)
  (lhprobe/4vec-case x
    :lhprobe (lhprobe-eval x envs)
    :4vec (4vec-fix x)))


(define lhprobe/4vec-vars ((x lhprobe/4vec-p))
  :parents (lhprobe)
  :short "Collect variables present in an lhprobe/4vec"
  :returns (vars svarlist-p)
  (lhprobe/4vec-case x
    :4vec nil
    :lhprobe (lhprobe-vars x))
  ///


  
  (defthm lhprobe/4vec-eval-of-svex-envlist-extract-vars
    (implies (subsetp-equal (lhprobe/4vec-vars x) (Svarlist-fix vars))
             (equal (lhprobe/4vec-eval x (svex-envlist-extract-keys vars envs))
                    (lhprobe/4vec-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe/4vec-eval)))))

(define lhprobe/4vec-change-override ((x lhprobe/4vec-p)
                                      (type svar-overridetype-p))
  :returns (new-x lhprobe/4vec-p)
  (lhprobe/4vec-case x
    :4vec (4vec-fix x)
    :lhprobe (lhprobe-change-override x type)))


(define svtv-spec-fsm-bindings-for-lhprobe ((lhprobe lhprobe-p)
                                            (binding svar/4vec-p)
                                            (bindings-acc lhprobe-map-p))
  :returns (bindings lhprobe-map-p)
  (svar/4vec-case binding
    :4vec (lhprobe-map-fix bindings-acc)
    :svar
    ;; svtv variable, add a binding unless there is one already
    (b* ((binding-look (hons-get (svar-fix binding) (lhprobe-map-fix bindings-acc)))
         ((unless binding-look)
          (hons-acons (svar-fix binding) (lhprobe-fix lhprobe)
                      (lhprobe-map-fix bindings-acc))))
      (lhprobe-map-fix bindings-acc))))

(define svtv-spec-fsm-bindings-for-alist ((x svar/4vec-alist-p)
                                             (stage natp)
                                             (namemap svtv-name-lhs-map-p)
                                             (overridetype svar-overridetype-p)
                                             (bindings-acc lhprobe-map-p))
  :returns (bindings lhprobe-map-p)
  (b* (((when (atom x)) (lhprobe-map-fix bindings-acc))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-spec-fsm-bindings-for-alist (cdr x) stage namemap overridetype bindings-acc))
       ((cons var val) (car x))
       (look (hons-get var (svtv-name-lhs-map-fix namemap)))
       ((unless look)
        (svtv-spec-fsm-bindings-for-alist (cdr x) stage namemap overridetype bindings-acc))
       (lhs (cdr look))
       (lhprobe (make-lhprobe :lhs (lhs-change-override lhs overridetype) :stage stage))
       (bindings-acc (svtv-spec-fsm-bindings-for-lhprobe lhprobe val bindings-acc)))
    (svtv-spec-fsm-bindings-for-alist (cdr x) stage namemap overridetype bindings-acc))
  ///
  (local (in-theory (enable svar/4vec-alist-fix))))

(define svtv-spec-fsm-bindings-for-alists ((x svar/4vec-alistlist-p)
                                           (stage natp)
                                           (namemap svtv-name-lhs-map-p)
                                           (overridetype svar-overridetype-p)
                                           (bindings-acc lhprobe-map-p))
  :returns (bindings lhprobe-map-p)
  (if (atom x)
      (lhprobe-map-fix bindings-acc)
    (svtv-spec-fsm-bindings-for-alists
     (cdr x) (1+ (lnfix stage)) namemap overridetype
     (svtv-spec-fsm-bindings-for-alist (car x) stage namemap overridetype bindings-acc))))



(define svtv-spec-fsm-bindings ((x svtv-spec-p))
  :returns (bindings lhprobe-map-p)
  :guard (svtv-spec-fsm-syntax-check x)
  :guard-hints (("goal" :in-theory (enable svtv-spec-fsm-syntax-check)))
  (b* (((svtv-spec x))
       (len (len (svtv-probealist-outvars (svtv-spec->probes x))))
       ((acl2::with-fast x.namemap))
       (bindings (svtv-spec-fsm-bindings-for-alists (take len x.in-alists) 0 x.namemap nil nil))
       (bindings (svtv-spec-fsm-bindings-for-alists (take len x.override-val-alists) 0 x.namemap :val bindings)))
    (svtv-spec-fsm-bindings-for-alists (take len x.override-test-alists) 0 x.namemap :test bindings)))
       







(defprod lhprobe-constraint
  :short "Constraint equating an @(see lhprobe) (that is, a concatenation of signals at some time) equals either a @(see 4vec) constant or the value of another lhprobe."
  ((lhprobe lhprobe-p)
   (val lhprobe/4vec-p))
  :layout :fulltree)

(fty::deflist lhprobe-constraintlist :elt-type lhprobe-constraint-p :true-listp t)


(define lhprobe-constraint-eval ((x lhprobe-constraint-p)
                                 (envs svex-envlist-p))
  (b* (((lhprobe-constraint x)))
    (equal (lhprobe-eval x.lhprobe envs)
           (lhprobe/4vec-eval x.val envs))))

(define lhprobe-constraintlist-eval ((x lhprobe-constraintlist-p)
                                     (envs svex-envlist-p))
  (if (atom x)
      t
    (and (lhprobe-constraint-eval (car x) envs)
         (lhprobe-constraintlist-eval (cdr x) envs)))
  ///
  (defthm lhprobe-constraintlist-eval-of-append
    (equal (lhprobe-constraintlist-eval (append x y) envs)
           (and (lhprobe-constraintlist-eval x envs)
                (lhprobe-constraintlist-eval y envs)))))

(define lhatom-overridemux-eval ((x lhatom-p)
                                 (env svex-env-p)
                                 (out svex-env-p))
  :returns (val 4vec-p)
  (lhatom-case x
    :z 0
    :var (4vec-rsh (2vec x.rsh)
                   (if (svar-override-p x.name :val)
                       (4vec-bit?! (svex-env-fastlookup (svar-change-override x.name :test) env)
                                   (svex-env-fastlookup x.name env)
                                   (svex-env-fastlookup (svar-change-override x.name nil) out))
                     (svex-env-fastlookup x.name env)))))

(define lhs-overridemux-eval ((x lhs-p)
                              (env svex-env-p)
                              (out svex-env-p))
  :returns (val 4vec-p)
  (if (atom x)
      0
    (if (atom (cdr x))
        (4vec-sign-ext (2vec (lhrange->w (car x)))
                       (lhatom-overridemux-eval (lhrange->atom (car x)) env out))
      (4vec-concat (2vec (lhrange->w (car x)))
                   (lhatom-overridemux-eval (lhrange->atom (car x)) env out)
                   (lhs-overridemux-eval (cdr x) env out))))
  ///
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

  (defthm lhs-overridemux-eval-when-overridetype
    (implies (svarlist-override-p (lhs-vars x) type)
             (equal (lhs-overridemux-eval x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhs-eval-ext (lhs-change-override x :test) env)
                                    (lhs-eval-ext x env)
                                    (lhs-eval-ext (lhs-change-override x nil) out))
                      (lhs-eval-ext x env))))
    :hints(("Goal" :in-theory (e/d (lhs-eval-ext lhatom-overridemux-eval
                                      lhs-vars lhatom-vars
                                      lhs-change-override
                                      lhatom-change-override
                                      svarlist-override-p
                                      lhatom-eval-zero
                                      svar-override-p-when-other)
                                   (svar-overridetype-equiv))))
    :otf-flg t)
  
  (defthm lhs-overridemux-eval-split-on-var-overridetype
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
             (equal (lhs-overridemux-eval x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhs-eval-ext (lhs-change-override x :test) env)
                                    (lhs-eval-ext x env)
                                    (lhs-eval-ext (lhs-change-override x nil) out))
                      (lhs-eval-ext x env)))))

  (defthm lhs-vars-of-lhs-change-override
    (equal (lhs-vars (lhs-change-override x type))
           (svarlist-change-override (lhs-vars x) type))
    :hints(("Goal" :in-theory (enable svarlist-change-override lhs-change-override lhatom-change-override lhs-vars lhatom-vars))))

  (defthm lhs-change-override-of-lhs-change-override
    (equal (lhs-change-override (lhs-change-override x type1) type2)
           (lhs-change-override x type2))
    :hints(("Goal" :in-theory (enable lhs-change-override lhatom-change-override))))
  
  (defthm lhs-overridemux-eval-of-lhs-change-override
    (equal (lhs-overridemux-eval (lhs-change-override x type) env out)
           (if (svar-overridetype-equiv type :val)
               (4vec-bit?! (lhs-eval-ext (lhs-change-override x :test) env)
                           (lhs-eval-ext (lhs-change-override x type) env)
                           (lhs-eval-ext (lhs-change-override x nil) out))
             (lhs-eval-ext (lhs-change-override x type) env)))
    :hints (("goal" :use ((:instance lhs-overridemux-eval-split-on-var-overridetype
                           (vars (lhs-vars (lhs-change-override x type)))
                           (x (lhs-change-override x type))))))))


(define lhprobe-overridemux-eval ((x lhprobe-p)
                                  (envs svex-envlist-p)
                                  (outs svex-envlist-p))
  :returns (val 4vec-p)
  (b* (((lhprobe x))
       (env (nth x.stage envs))
       (out (nth x.stage outs)))
    (lhs-overridemux-eval x.lhs env out))
  ///

  (defthm lhprobe-overridemux-eval-when-overridetype
    (implies (svarlist-override-p (lhprobe-vars x) type)
             (equal (lhprobe-overridemux-eval x env out)
                    (if (svar-overridetype-equiv type :val)
                        (4vec-bit?! (lhprobe-eval (lhprobe-change-override x :test) env)
                                    (lhprobe-eval x env)
                                    (lhprobe-eval (lhprobe-change-override x nil) out))
                      (lhprobe-eval x env))))
    :hints(("Goal" :use ((:instance lhs-overridemux-eval-split-on-var-overridetype
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


(define lhprobe/4vec-overridemux-eval ((x lhprobe/4vec-p)
                                       (envs svex-envlist-p)
                                       (outs svex-envlist-p))
  :returns (val 4vec-p)
  (lhprobe/4vec-case x
    :lhprobe (lhprobe-overridemux-eval x envs outs)
    :4vec (4vec-fix x))
  ///
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

(define lhprobe-constraint-overridemux-eval ((x lhprobe-constraint-p)
                                             (envs svex-envlist-p)
                                             (outs svex-envlist-p))
  (b* (((lhprobe-constraint x)))
    (equal (lhprobe-overridemux-eval x.lhprobe envs outs)
           (lhprobe/4vec-overridemux-eval x.val envs outs))))

(define lhprobe-constraintlist-overridemux-eval ((x lhprobe-constraintlist-p)
                                                 (envs svex-envlist-p)
                                                 (outs svex-envlist-p))
  (if (atom x)
      t
    (and (lhprobe-constraint-overridemux-eval (car x) envs outs)
         (lhprobe-constraintlist-overridemux-eval (cdr x) envs outs)))
  ///
  (defthm lhprobe-constraintlist-overridemux-eval-of-append
    (equal (lhprobe-constraintlist-overridemux-eval (append x y) envs outs)
           (and (lhprobe-constraintlist-overridemux-eval x envs outs)
                (lhprobe-constraintlist-overridemux-eval y envs outs)))))


(define lhprobe-map-overridemux-eval ((x lhprobe-map-p)
                                      (envs svex-envlist-p)
                                      (outs svex-envlist-p))
  :returns (eval svex-env-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (lhprobe-map-overridemux-eval (cdr x) envs outs)))
    (cons (cons (caar x) (lhprobe-overridemux-eval (cdar x) envs outs))
          (lhprobe-map-overridemux-eval (cdr x) envs outs)))
  ///
  (defret lookup-of-<fn>
    (equal (svex-env-lookup v eval)
           (let ((look (hons-assoc-equal (svar-fix v) (lhprobe-map-fix x))))
             (if look
                 (lhprobe-overridemux-eval (cdr look) envs outs)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons))))

  (defret boundp-of-<fn>
    (iff (svex-env-boundp v eval)
         (hons-assoc-equal (svar-fix v) (lhprobe-map-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-boundp-of-cons-split))))
  
  (local (in-theory (enable lhprobe-map-fix)))

  (defthm lhprobe-map-overridemux-eval-when-overridetype
    (implies (and (svarlist-override-p (lhprobe-map-vars x) type)
                  (not (equal (svar-overridetype-fix type) :val)))
             (equal (lhprobe-map-overridemux-eval x env out)
                    (lhprobe-map-eval x env)))
    :hints(("Goal" :in-theory (enable lhprobe-overridemux-eval-when-overridetype
                                      lhprobe-map-vars
                                      lhprobe-map-eval)))))
    


    
    





(define svtv-spec-fsm-constraints-for-lhprobe ((lhprobe lhprobe-p)
                                               (binding svar/4vec-p)
                                               (bindings lhprobe-map-p))
  ;; Lhprobe is the LHS corresponding to some namemap name, which is mapped to binding in one of the input alists of the SVTV.

  ;; Add constraints based on equating lhprobe and binding under the assumption
  ;; that svtv variables are mapped to lhprobes as in bindings.

  
  
  :returns (constraints lhprobe-constraintlist-p)
  (svar/4vec-case binding
    :4vec
    ;; constant binding, add constraint
    (list (make-lhprobe-constraint
               :lhprobe lhprobe
               :val (4vec-fix binding)))
    :svar
    ;; svtv variable, must have a binding
    (b* ((binding-look (hons-get (svar-fix binding) (lhprobe-map-fix bindings)))
         ((unless binding-look)
          ;; add a constraint equating this hlprobe to x, I guess
          (list (make-lhprobe-constraint
                 :lhprobe lhprobe :val (4vec-x))))
         (binding-lhprobe (cdr binding-look))
         ((when (equal binding-lhprobe (lhprobe-fix lhprobe)))
          ;; same, no constraint necessary
          nil))
      (list (make-lhprobe-constraint
             :lhprobe lhprobe
             :val binding-lhprobe))))
  ///

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
                                      lhprobe/4vec-eval)))))


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



(defsection svex-envs-ovtestsimilar
  ;; (def-universal-equiv svex-envs-ovtestsimilar
  ;;   :qvars (k)
  ;;   :equiv-terms ((4vec-1mask-equiv (svex-env-lookup k x))))

  (defun-sk svex-envs-ovtestsimilar (x y)
    (forall k
            (implies (svar-override-p k :test)
                     (4vec-1mask-equiv (svex-env-lookup k x)
                                       (svex-env-lookup k y))))
    :rewrite :direct)

  (in-theory (disable svex-envs-ovtestsimilar
                      svex-envs-ovtestsimilar-necc))

  (defequiv svex-envs-ovtestsimilar
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-envs-ovtestsimilar-necc)))))

  (defrefinement  svex-envs-similar svex-envs-ovtestsimilar
    :hints(("Goal" :in-theory (enable svex-envs-ovtestsimilar)))))


(define svex-envlists-ovtestsimilar ((x svex-envlist-p) (y svex-envlist-p))
  (if (Atom x)
      (atom y)
    (and (consp y)
         (ec-call (svex-envs-ovtestsimilar (car x) (car y)))
         (svex-envlists-ovtestsimilar (cdr x) (cdr y))))
  ///
  (defequiv svex-envlists-ovtestsimilar)

  (defrefinement svex-envlists-similar svex-envlists-ovtestsimilar
    :hints(("Goal" :in-theory (enable svex-envlists-similar-rec)))))

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


(define svtv-name-lhs-map-eval-ext ((x svtv-name-lhs-map-p)
                                    (env svex-env-p))
  :returns (res svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-name-lhs-map-eval-ext (cdr x) env)))
    (cons (Cons (caar x) (lhs-eval-ext (cdar x) env))
          (svtv-name-lhs-map-eval-ext (cdr x) env)))
  ///
  (defret svex-env-boundp-of-<fn>
    (iff (svex-env-boundp k res)
         (hons-assoc-equal (svar-fix k) (svtv-name-lhs-map-fix x)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                      svex-env-boundp-of-cons-split))))
  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup k res)
           (let ((pair (hons-assoc-equal (svar-fix k) (svtv-name-lhs-map-fix x))))
             (if pair (lhs-eval-ext (cdr pair) env) (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons-split
                                      svtv-name-lhs-map-fix))))

  (defthm alist-keys-of-svtv-name-lhs-map-eval-ext
           (equal (alist-keys (svtv-name-lhs-map-eval-ext x env))
                  (alist-keys (svtv-name-lhs-map-fix x)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-eval-ext
                                             alist-keys))))
  
  (local (in-theory (enable svtv-name-lhs-map-fix))))



(local
 (defsection 4vec-bit-index-of-lhs-eval-ext
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
  
   (defthm 4vec-bit-index-of-lhs-eval-ext
     (equal (4vec-bit-index n (lhs-eval-ext x env))
            (if (< (nfix n) (lhs-width x))
                (lhbit-eval-zero (lhs-bitproj n x) env)
              (if (posp (lhs-width x))
                  (lhbit-eval-zero (lhs-bitproj (1- (lhs-width x)) x) env)
                0)))
     :hints(("Goal" :in-theory (enable lhs-eval-ext lhs-bitproj lhatom-bitproj lhatom-eval-zero
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

(define svtv-spec-fsm-constraints-for-alist ((x svar/4vec-alist-p)
                                             (stage natp)
                                             (namemap svtv-name-lhs-map-p)
                                             (overridetype svar-overridetype-p)
                                             (bindings lhprobe-map-p))
  :returns (constraints lhprobe-constraintlist-p)

  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-spec-fsm-constraints-for-alist (cdr x) stage namemap overridetype bindings))
       ((cons var val) (car x))
       (look (hons-get var (svtv-name-lhs-map-fix namemap)))
       ((unless look)
        (svtv-spec-fsm-constraints-for-alist (cdr x) stage namemap overridetype bindings))
       (lhs (cdr look))
       (lhprobe (make-lhprobe :lhs (lhs-change-override lhs overridetype) :stage stage)))
    (append       
     (svtv-spec-fsm-constraints-for-lhprobe lhprobe val bindings)
     (svtv-spec-fsm-constraints-for-alist (cdr x) stage namemap overridetype bindings)))
  ///
  (local (include-book "std/alists/fast-alist-clean" :dir :system))
  (local (include-book "std/lists/sets" :dir :system))
  (local (include-book "std/alists/fal-extract" :dir :system))

  (defretd constraints-eval-of-<fn>
    (implies (and (lhprobe-constraintlist-eval constraints envs)
                  ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
                  ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
                  (member-equal v (alist-keys (svtv-name-lhs-map-fix namemap)))
                  )
             (equal (svar/4vec-eval (cdr (hons-assoc-equal v (svar/4vec-alist-fix x)))
                                    (lhprobe-map-eval bindings envs))
                    (svex-env-lookup v
                                     (svtv-name-lhs-map-eval-ext
                                      (svtv-name-lhs-map-vals-change-override
                                       (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                                                          (svtv-name-lhs-map-fix namemap))
                                       overridetype)
                                      (nth stage envs)))))
    :hints(("Goal" :in-theory (e/d (svtv-name-lhs-map-eval
                                    fal-extract
                                    alist-keys
                                    svar/4vec-alist-fix
                                    svar/4vec-alist-eval
                                    svtv-name-lhs-map-vals-change-override
                                    lhprobe-eval)
                                   ((:d <fn>)))
            :induct <call> :do-not-induct t
            :expand ((lhprobe-constraintlist-eval nil envs)
                     <call>))))

  (local (defthm hons-assoc-equal-of-svtv-name-lhs-map-vals-change-override-under-iff
           (iff (hons-assoc-equal v (svtv-name-lhs-map-vals-change-override x type))
                (hons-assoc-equal v (svtv-name-lhs-map-fix x)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                             svtv-name-lhs-map-vals-change-override)))))
  
  (defretd constraints-overridemux-eval-of-<fn>
    (implies (and (lhprobe-constraintlist-overridemux-eval constraints envs outs)
                  ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
                  ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
                  (member-equal v (alist-keys (svtv-name-lhs-map-fix namemap)))
                  )
             (equal (svar/4vec-eval (cdr (hons-assoc-equal v (svar/4vec-alist-fix x)))
                                    (lhprobe-map-overridemux-eval bindings envs outs))
                    (if (svar-overridetype-equiv overridetype :val)
                        (4vec-bit?!
                         (svex-env-lookup v
                                          (svtv-name-lhs-map-eval-ext
                                           (svtv-name-lhs-map-vals-change-override
                                            (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                                                               (svtv-name-lhs-map-fix namemap))
                                            :test)
                                           (nth stage envs)))
                         (svex-env-lookup v
                                          (svtv-name-lhs-map-eval-ext
                                           (svtv-name-lhs-map-vals-change-override
                                            (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                                                               (svtv-name-lhs-map-fix namemap))
                                            :val)
                                           (nth stage envs)))
                         (svex-env-lookup v
                                          (svtv-name-lhs-map-eval-ext
                                           (svtv-name-lhs-map-vals-change-override
                                            (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                                                               (svtv-name-lhs-map-fix namemap))
                                            nil)
                                           (nth stage outs))))
                      (svex-env-lookup v
                                       (svtv-name-lhs-map-eval-ext
                                        (svtv-name-lhs-map-vals-change-override
                                         (acl2::fal-extract (alist-keys (svar/4vec-alist-fix x))
                                                            (svtv-name-lhs-map-fix namemap))
                                         overridetype)
                                        (nth stage envs))))))
    :hints(("Goal" :in-theory (e/d (svtv-name-lhs-map-eval-ext
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
                     (:free (lhs) (lhprobe-overridemux-eval (lhprobe lhs stage) envs outs))
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
  
  
  (defretd constraints-eval-of-<fn>-implies
    (implies (and (lhprobe-constraintlist-eval constraints envs)
                  ;; x maps namemap names to consts/svtv vars
                  ;; namemap maps namemap names to fsm lhses
                  ;; envs each map fsm vars to values
                  ;; bindings maps svtv vars to fsm lhprobes
                  
                  ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
                  ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
                  (no-duplicatesp-equal (alist-keys (svar/4vec-alist-fix x)))
                  (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                  (not (equal (svar-overridetype-fix overridetype) :test)))
             (svex-env-<<=
              (svtv-fsm-namemap-env  ;; fsm vars (overridetype) to values
               (svar/4vec-alist-eval ;; namemap names to values
                x
                (lhprobe-map-eval bindings envs)) ;; svtv vars to values
               namemap overridetype)
              (nth stage envs)))
    :hints (("goal" :in-theory (e/d (svtv-fsm-namemap-env
                                     svtv-fsm-env-inversemap
                                     constraints-eval-of-<fn>
                                     svex-env-<<=
                                     ACL2::HONS-ASSOC-EQUAL-IFF-MEMBER-ALIST-KEYS
                                     4vec-<<=-by-badbit
                                     LHBIT-EVAL-X
                                     lhbit-eval-zero)
                                    (<fn>
                                     acl2::alist-keys-member-hons-assoc-equal
                                     eval-svtv-name-lhs-map-inverse-of-lookup-gen
                                     HONS-ASSOC-EQUAL-OF-SVAR/4VEC-ALIST-FIX
                                     HONS-ASSOC-EQUAL-OF-SVTV-NAME-LHS-MAP-FIX))
             :do-not-induct t)
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-env-<<=-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badkey)))))))
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst '4vec-<<=-badbit clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))))

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
         (test-env (svar/4vec-alist-eval test-alist bindings-eval)))
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
                           (alist-keys (svar/4vec-alist-fix test-alist)))
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
                                    constraints-overridemux-eval-of-svtv-spec-fsm-constraints-for-alist
                                    acl2::hons-assoc-equal-iff-member-alist-keys
                                    if-of-hons-assoc-equal-member-alist-keys
                                    4vec-1mask-of-4vec-bit-index
                                    member-when-not-svar-override-p
                                    svar-override-p-when-other)
                                   (svtv-spec-fsm-constraints-for-alist
                                    eval-svtv-name-lhs-map-inverse-of-lookup-gen
                                    acl2::alist-keys-member-hons-assoc-equal
                                    hons-assoc-equal-of-svar/4vec-alist-fix
                                    hons-assoc-equal-of-svtv-name-lhs-map-fix))))
            (and stable-under-simplificationp
                 (let ((call (or
                              (acl2::find-call-lst '4vec-<<=-badbit clause)
                              (acl2::find-call-lst '4vec-equiv-badbit clause)
                              (acl2::find-call-lst '4vec-1mask-equiv-badbit clause)
                              (acl2::find-call-lst '4vec-muxtest-subsetp-badbit clause)
                              (acl2::find-call-lst '4vec-override-mux-agrees-badbit clause))))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badbit)))))))
            )
    :otf-flg t)
    
  (local (in-theory (enable svar/4vec-alist-fix))))


(define svtv-fsm-namemap-envlist ((envs svex-envlist-p)
                                  (map svtv-name-lhs-map-p)
                                  (overridetype svar-overridetype-p))
  (if (atom envs)
      nil
    (cons (svtv-fsm-namemap-env (car envs) map overridetype)
          (svtv-fsm-namemap-envlist (cdr envs) map overridetype))))



(define svtv-spec-fsm-constraints-for-alists ((x svar/4vec-alistlist-p)
                                              (stage natp)
                                              (namemap svtv-name-lhs-map-p)
                                              (overridetype svar-overridetype-p)
                                              (bindings lhprobe-map-p))
  :returns (constraints lhprobe-constraintlist-p)
  (if (atom x)
      nil
    (append (svtv-spec-fsm-constraints-for-alist (car x) stage namemap overridetype bindings)
            (svtv-spec-fsm-constraints-for-alists (cdr x) (1+ (lnfix stage)) namemap overridetype bindings)))
  ///


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
         (val-envs  (svex-alistlist-eval val-alists bindings-eval))
         (test-envs (svex-alistlist-eval test-alists bindings-eval)))
      (implies (and (lhprobe-constraintlist-overridemux-eval in-constraints envs outs)
                    (lhprobe-constraintlist-overridemux-eval val-constraints envs outs)
                    (equal (len in-alists) (len val-alists))
                    (equal (len in-alists) (len test-alists))
                    ;; x maps namemap names to consts/svtv vars
                    ;; namemap maps namemap names to fsm lhses
                    ;; envs each map fsm vars to values
                    ;; bindings maps svtv vars to fsm lhprobes
                  
                    ;; (subsetp-equal (alist-keys (svar/4vec-alist-fix x))
                    ;;                (alist-keys (svtv-name-lhs-map-fix namemap)))
                    (svex-alistlist-noncall-p in-alists)
                    (svex-alistlist-noncall-p val-alists)
                    (svex-alistlist-noncall-p test-alists)
                    (no-duplicatesp-each (svex-alist-keys-list in-alists))
                    (no-duplicatesp-each (svex-alist-keys-list val-alists))
                    (equal (svex-alist-keys-list val-alists)
                           (svex-alist-keys-list test-alists))
                    (svarlist-override-p (svtv-name-lhs-map-vars namemap) nil)
                    ;; (subsetp-equal (svtv-name-lhs-map-vars
                    ;;                 (FAL-EXTRACT (svex-ALISTlist-all-keys test-alists)
                    ;;                              (SVTV-NAME-LHS-MAP-FIX NAMEMAP)))
                    ;;                (svarlist-change-override overridekeys nil))
                    (svex-envlists-ovtests-ok (nthcdr stage envs)
                                              (svtv-fsm-to-base-fsm-inputs in-envs val-envs test-envs namemap)
                                              overridekeys))
               (overridekeys-envlists-agree*
                overridekeys
                (svex-envlist-x-override
                 (svtv-fsm-to-base-fsm-inputs in-envs val-envs test-envs namemap)
                 (svex-envlist-remove-override
                  (svex-envlist-remove-override (nthcdr stage envs) :test)
                  :val))
                (nthcdr stage envs)
                (nthcdr stage outs))))
    :hints(("Goal" :in-theory (enable svex-alistlist-eval
                                      svex-alistlist-noncall-p
                                      svex-alist-keys-list
                                      no-duplicatesp-each
                                      svex-alistlist-all-keys
                                      svex-envlists-ovtests-ok
                                      svex-envlist-x-override
                                      svtv-fsm-to-base-fsm-inputs
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
            :induct (ind in-alists val-alists test-alists stage)
            :do-not-induct t))))


(local (defthmd svtv-fsm-to-base-fsm-inputs-norm-override-vals-length
         (implies (and (equal new-override-vals (take (len ins) override-vals))
                       (syntaxp (not (equal new-override-vals override-vals))))
                  (equal (svtv-fsm-to-base-fsm-inputs ins override-vals override-tests namemap)
                         (svtv-fsm-to-base-fsm-inputs ins new-override-vals override-tests namemap)))
         :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs)))))

(local (defthmd svtv-fsm-to-base-fsm-inputs-norm-override-tests-length
         (implies (and (equal new-override-tests (take (len ins) override-tests))
                       (syntaxp (not (equal new-override-tests override-tests))))
                  (equal (svtv-fsm-to-base-fsm-inputs ins override-vals override-tests namemap)
                         (svtv-fsm-to-base-fsm-inputs ins override-vals new-override-tests namemap)))
         :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs)))))



(local (defthm take-of-svex-alistlist-eval
         (equal (take len (svex-alistlist-eval x env))
                (svex-alistlist-eval (take len x) env))
         :hints(("Goal" :in-theory (e/d (svex-alistlist-eval
                                         svex-alist-eval)
                                        (acl2::take-of-too-many
                                         acl2::take-when-atom))))))



(define svtv-spec-fsm-constraints ((x svtv-spec-p))
  :returns (constraints lhprobe-constraintlist-p)
  :guard (svtv-spec-fsm-syntax-check x)
  :guard-hints (("goal" :in-theory (enable svtv-spec-fsm-syntax-check)))
  (b* (((svtv-spec x))
       (bindings (svtv-spec-fsm-bindings x))
       (len (len (svtv-probealist-outvars (svtv-spec->probes x)))))
    (append (svtv-spec-fsm-constraints-for-alists (take len x.in-alists) 0 x.namemap nil bindings)
            (svtv-spec-fsm-constraints-for-alists (take len x.override-val-alists) 0 x.namemap :val bindings)))
  ///

  
  (defretd constraints-eval-of-<fn>-implies
    (implies (and (lhprobe-constraintlist-overridemux-eval constraints envs outs)
                  (svtv-spec-fsm-syntax-check x))
             (b* ((svtv-env (lhprobe-map-overridemux-eval (svtv-spec-fsm-bindings x) envs outs))
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
                                      svtv-fsm-to-base-fsm-inputs-norm-override-vals-length
                                      svtv-fsm-to-base-fsm-inputs-norm-override-tests-length
                                      take-of-svex-alistlist-eval)
            :use ((:instance constraints-overridemux-eval-of-svtv-spec-fsm-constraints-for-alists-implies
                   (in-alists (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->in-alists x)))
                   (val-alists (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->override-val-alists x)))
                   (test-alists (take (len (svtv-probealist-outvars (svtv-spec->probes x))) (svtv-spec->override-test-alists x)))
                   (bindings (svtv-spec-fsm-bindings x))
                   (namemap (svtv-spec->namemap x))
                   (stage 0)))))))


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

(defsection base-fsm-override-p-of-cycle

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
  ;;                                   base-fsm-step-env)
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
    (b* (((base-fsm x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
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
                                    base-fsm-step-env
                                    base-fsm-overridekey-transparent-p)
                                   (overridekeys-envs-agree-of-append-nonoverride))
            :use ((:instance overridekeys-envs-agree-of-append-nonoverride
                   (x (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                              (svtv-cyclephase->constants phase)))
                   (spec-outs (mv-nth 0 (svtv-cycle-step-phase spec-env prev-st phase x))))
                  (:instance svex-alist-overridekey-transparent-p-necc
                   (x (base-fsm->nextstate x))
                   (impl-env (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                                     (svtv-cyclephase->constants phase)
                                     impl-env))
                   (spec-env (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                                     (svtv-cyclephase->constants phase)
                                     spec-env))
                   (subst (base-fsm->values x)))))))

  (defthm svtv-cycle-step-phase-outs-when-svex-alist-overridekey-transparent-p
    (b* (((base-fsm x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
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
                                    base-fsm-step-env
                                    base-fsm-overridekey-transparent-p)
                                   (overridekeys-envs-agree-of-append-nonoverride))
            :use ((:instance overridekeys-envs-agree-of-append-nonoverride
                   (x (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                              (svtv-cyclephase->constants phase)))
                   (spec-outs (mv-nth 0 (svtv-cycle-step-phase spec-env prev-st phase x))))
                  (:instance svex-alist-overridekey-transparent-p-necc
                   (x (base-fsm->values x))
                   (impl-env (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                                     (svtv-cyclephase->constants phase)
                                     impl-env))
                   (spec-env (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                                     (svtv-cyclephase->constants phase)
                                     spec-env))
                   (subst (base-fsm->values x)))))))

  (defthm svtv-cycle-step-phase-nextsts-normalize-env-when-not-inputs-free
    (implies (and (syntaxp (not (equal env ''nil)))
                  (not (svtv-cyclephase->inputs-free phase)))
             (equal (svtv-cycle-step-phase-nextsts env prev-st phase x)
                    (svtv-cycle-step-phase-nextsts nil prev-st phase x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts))))
  
  (defthm svtv-cycle-eval-nextst-when-svex-alist-overridekey-transparent-p-no-i/o-phase
    (b* (((base-fsm x)))
      (implies (and (syntaxp (not (equal env ''nil)))
                    (svtv-cyclephaselist-no-i/o-phase phases))
               (equal (svtv-cycle-eval-nextst env prev-st phases x)
                      (svtv-cycle-eval-nextst nil prev-st phases x))))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-nextst
                                      svtv-cyclephaselist-no-i/o-phase))))

  (defthm svtv-cycle-eval-nextst-when-svex-alist-overridekey-transparent-p-unique-i/o-phase
    (b* (((base-fsm x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
                    (overridekeys-envs-agree overridekeys impl-env spec-env
                                             (svtv-cycle-eval-outs spec-env prev-st phases x))
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svtv-cyclephaselist-unique-i/o-phase phases))
               (equal (svtv-cycle-eval-nextst impl-env prev-st phases x.nextstate)
                      (svtv-cycle-eval-nextst spec-env prev-st phases x.nextstate))))
    :hints(("Goal" :in-theory (enable (:i svtv-cycle-eval-nextst)
                                      svtv-cyclephaselist-unique-i/o-phase)
            :induct (svtv-cycle-eval-nextst impl-env prev-st phases (base-fsm->nextstate x))
            :expand ((:free (impl-env x) (svtv-cycle-eval-nextst impl-env prev-st phases x))
                     (svtv-cycle-eval-outs spec-env prev-st phases x)
                     (svtv-cyclephaselist-keys phases)))))

  (defthm svtv-cycle-eval-outs-when-svex-alist-overridekey-transparent-p-unique-i/o-phase
    (b* (((base-fsm x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
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
    (b* (((base-fsm x)))
      (equal (svtv-cycle-step-phase-outs env (svex-env-extract (svex-alist-keys x.nextstate) prev-st) phase x)
             (svtv-cycle-step-phase-outs env prev-st phase x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-outs))))

  (defthm svtv-cycle-step-phase-nextsts-of-extract-initst-keys
    (equal (svtv-cycle-step-phase-nextsts env (svex-env-extract (svex-alist-keys nextst) prev-st) phase nextst)
           (svtv-cycle-step-phase-nextsts env prev-st phase nextst))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts))))
  
  (defthm svtv-cycle-eval-outs-of-extract-initst-keys
    (b* (((base-fsm x)))
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
                         (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil))
                    (equal (svtv-cycle-eval-outs impl-env impl-env phases x)
                           (svtv-cycle-eval-outs impl-env spec-env phases x)))
           :hints (("goal" :use ((:instance svtv-cycle-eval-outs-of-extract-initst-keys
                                  (prev-st impl-env)
                                  (env impl-env))
                                 (:instance svtv-cycle-eval-outs-of-extract-initst-keys
                                  (prev-st spec-env)
                                  (env impl-env)))))))

  (defthm base-fsm-overridekey-transparent-p-of-base-fsm-to-cycle
    (implies (and (base-fsm-overridekey-transparent-p fsm overridekeys)
                  (svarlist-override-p (svex-alist-keys (base-fsm->nextstate fsm)) nil)
                  (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil))
             (base-fsm-overridekey-transparent-p (base-fsm-to-cycle phases fsm nil) overridekeys))
    :hints(("Goal" :in-theory (enable base-fsm-to-cycle))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))) ;; base-fsm-overridekey-transparent-p
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
    (b* (((base-fsm x)))
      (implies (and (base-fsm-ovcongruent x)
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
                                    base-fsm-step-env
                                    base-fsm-ovcongruent))
            :use ((:instance svex-alist-ovcongruent-necc
                   (x (base-fsm->nextstate x))
                   (env1 (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                                 (svtv-cyclephase->constants phase)
                                 env1))
                   (env2 (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                                 (svtv-cyclephase->constants phase)
                                 env2)))))))
  
  (defthm svtv-cycle-step-phase-outs-when-ovcongruent
    (b* (((base-fsm x)))
      (implies (and (base-fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-step-phase-outs env1 prev-st phase x)
                                            (svtv-cycle-step-phase-outs env2 prev-st phase x))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    svtv-cycle-step-phase-outs
                                    base-fsm-step-env
                                    base-fsm-ovcongruent))
            :use ((:instance svex-alist-ovcongruent-necc
                   (x (base-fsm->values x))
                   (env1 (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                                 (svtv-cyclephase->constants phase)
                                 env1))
                   (env2 (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
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
    (b* (((base-fsm x)))
      (implies (and (base-fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-step-phase-outs env1 env1 phase x)
                                            (svtv-cycle-step-phase-outs env2 env2 phase x))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    svtv-cycle-step-phase-outs
                                    base-fsm-step-env
                                    base-fsm-ovcongruent))
            :use ((:instance svex-alist-ovcongruent-necc
                   (x (base-fsm->values x))
                   (env1 (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) env1)
                                 (svtv-cyclephase->constants phase)
                                 env1))
                   (env2 (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) env1)
                                 (svtv-cyclephase->constants phase)
                                 env2)))
                  (:instance extract-keys-when-ovsimilar
                   (keys (svex-alist-keys (base-fsm->nextstate x)))))
            )))

  (defthm svtv-cycle-step-phase-nextsts-when-ovcongruent-2
    (b* (((base-fsm x)))
      (implies (and (base-fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (alist-keys (svtv-cyclephase->constants phase)) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-step-phase-nextsts env1 env1 phase x.nextstate)
                                            (svtv-cycle-step-phase-nextsts env2 env2 phase x.nextstate))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-step-phase-nextsts
                                    base-fsm-step-env
                                    base-fsm-ovcongruent))
            :use ((:instance svex-alist-ovcongruent-necc
                   (x (base-fsm->nextstate x))
                   (env1 (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) env1)
                                 (svtv-cyclephase->constants phase)
                                 env1))
                   (env2 (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) env1)
                                 (svtv-cyclephase->constants phase)
                                 env2)))
                  (:instance extract-keys-when-ovsimilar
                   (keys (svex-alist-keys (base-fsm->nextstate x)))))
            )))

  
  (defthm svtv-cycle-eval-outs-when-ovcongruent
    (b* (((base-fsm x)))
      (implies (and (base-fsm-ovcongruent x)
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
    (b* (((base-fsm x)))
      (implies (and (base-fsm-ovcongruent x)
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
    (b* (((base-fsm x)))
      (implies (and (base-fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-eval-nextst env1 prev-st phases x.nextstate)
                                            (svtv-cycle-eval-nextst env2 prev-st phases x.nextstate))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-eval-nextst))
            :induct (svtv-cycle-eval-nextst env1 prev-st phases (base-fsm->nextstate x))
            :expand ((:free (env1) (svtv-cycle-eval-nextst env1 prev-st phases (base-fsm->nextstate x)))
                     (svtv-cyclephaselist-keys phases)))
           (and stable-under-simplificationp
                '(:use ((:instance svtv-cycle-step-phase-nextsts-when-ovcongruent
                         (phase (car phases))))
                  :in-theory (disable svtv-cycle-step-phase-nextsts-when-ovcongruent)))))

  (defthm svtv-cycle-eval-nextst-when-ovcongruent-2
    (b* (((base-fsm x)))
      (implies (and (base-fsm-ovcongruent x)
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                    (svex-envs-ovsimilar env1 env2))
               (equal (svex-envs-equivalent (svtv-cycle-eval-nextst env1 env1 phases x.nextstate)
                                            (svtv-cycle-eval-nextst env2 env2 phases x.nextstate))
                      t)))
    :hints(("Goal" :in-theory (e/d (svtv-cycle-eval-nextst)
                                   (SVEX-ENVS-EQUIVALENT-WHEN-SIMILAR-AND-ALIST-KEYS-EQUIV))
            :expand ((svtv-cycle-eval-nextst env1 env1 phases (base-fsm->nextstate x))
                     (svtv-cycle-eval-nextst env2 env2 phases (base-fsm->nextstate x))
                     (svtv-cyclephaselist-keys phases)))
           (and stable-under-simplificationp
                '(:use ((:instance svtv-cycle-step-phase-nextsts-when-ovcongruent-2
                         (phase (car phases)))
                        (:instance extract-keys-when-ovsimilar
                         (keys (svex-alist-keys (base-fsm->nextstate x)))))
                  :in-theory (disable svtv-cycle-step-phase-nextsts-when-ovcongruent-2
                                      SVEX-ENVS-EQUIVALENT-WHEN-SIMILAR-AND-ALIST-KEYS-EQUIV)))))

  (defthm base-fsm-ovcongruent-p-of-base-fsm-to-cycle
    (implies (and (base-fsm-ovcongruent fsm)
                  (svarlist-override-p (svex-alist-keys (base-fsm->nextstate fsm)) nil)
                  ;; (svtv-cyclephaselist-unique-i/o-phase phases)
                  (svarlist-override-p (svtv-cyclephaselist-keys phases) nil)
                  )
             (base-fsm-ovcongruent (base-fsm-to-cycle phases fsm nil)))
    :hints(("Goal" :in-theory (enable base-fsm-to-cycle base-fsm-ovcongruent))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))
           (and stable-under-simplificationp
                        (let ((call (acl2::find-call-lst 'svex-alist-ovcongruent-witness clause)))
                          (and call
                               `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                            ((mv-nth '1 ,call) . env2))))))))))



(define svtv-spec->override-test-alists* ((x svtv-spec-p))
  (b* (((svtv-spec x)))
    (take (len (svtv-probealist-outvars x.probes)) x.override-test-alists)))

(define svtv-spec->override-val-alists* ((x svtv-spec-p))
  (b* (((svtv-spec x)))
    (take (len (svtv-probealist-outvars x.probes)) x.override-val-alists)))

(define svtv-spec->in-alists* ((x svtv-spec-p))
  (b* (((svtv-spec x)))
    (take (len (svtv-probealist-outvars x.probes)) x.in-alists)))

(define force-execute (x) x)

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

(defcong svex-envs-1mask-equiv  4vec-1mask-equiv (lhs-eval-zero x env) 2
  :hints(("Goal" :in-theory (enable lhs-eval-zero))))

(defcong svex-envs-1mask-equiv  4vec-1mask-equiv (lhs-eval-ext x env) 2
  :hints(("Goal" :in-theory (enable lhs-eval-ext))))


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

(defthmd lhs-eval-ext-when-override-test-vars-and-ovtestsimilar
  (implies (and (svarlist-override-p (lhs-vars x) :test)
                (svex-envs-ovtestsimilar env1 env2))
           (equal (4vec-1mask-equiv (lhs-eval-ext x env1)
                                    (lhs-eval-ext x env2))
                  t))
  :hints(("Goal" :in-theory (enable lhs-vars)
          :induct (lhs-vars x)
          :expand ((:free (env) (lhs-eval-ext x env))))
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
                                    lhs-eval-ext-when-override-test-vars-and-ovtestsimilar))))

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
  
  (defthm svtv-fsm-to-base-fsm-inputs-under-svex-envlists-ovtestsimilar
    (svex-envlists-ovtestsimilar (svtv-fsm-to-base-fsm-inputs inputs override-vals override-tests map)
                                 (svtv-fsm-namemap-envlist (take (len inputs) override-tests) map :test))
    :hints(("Goal" :in-theory (enable svtv-fsm-namemap-envlist
                                      svtv-fsm-to-base-fsm-inputs
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
;;                (BASE-FSM-EVAL ENVS INITST
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
;;                 (BASE-FSM-EVAL ENVS INITST
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
                             (lhprobe-map-overridemux-eval-of-fal-extract))))))
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
;;   (BASE-FSM-EVAL ENVS INITST
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


;; (SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH
;;  (COUNTER-INVAR-RUN-TRIPLEMAPLIST)
;;  (LHPROBE-MAP-OVERRIDEMUX-EVAL
;;   (SVTV-SPEC-FSM-BINDINGS (COUNTER-INVAR-SPEC))
;;   ENVS
;;   (BASE-FSM-EVAL ENVS INITST
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

(defthm lhs-eval-ext-svex-envlists-ovtestequiv-congruence-when-only-test-vars
  (implies (and (svarlist-override-p (lhs-vars lhs) :test)
                (svex-envs-ovtestequiv env1 env2))
           (equal (equal (lhs-eval-ext lhs env1)
                         (lhs-eval-ext lhs env2))
                  t))
  :hints(("Goal" :in-theory (enable lhs-vars)
          :induct (lhs-vars lhs)
          :expand ((:free (env) (lhs-eval-ext lhs env))))
         (and stable-under-simplificationp
              '(:use ((:instance lhatom-eval-zero-svex-envlists-ovtestequiv-congruence-when-only-test-vars
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



(defthm lhprobe-map-overridemux-eval-when-only-test-vars
  (implies (and (syntaxp (quotep lhmap))
                (equal vars (lhprobe-map-vars lhmap))
                (syntaxp (quotep vars))
                (svarlist-override-p vars :test)
                (svex-envlists-ovtestequiv equiv-envs (double-rewrite envs))
                (syntaxp (and (not (equal equiv-envs envs))
                              (quotep equiv-envs)
                              (prog2$ (cw "equiv-envs: ~x0~%" equiv-envs)
                                      t)))
                (equal ans (lhprobe-map-eval lhmap (make-fast-alists equiv-envs)))
                (syntaxp (and (quotep ans)
                              (prog2$ (cw "ans: ~x0~%" ans)
                                      t))))
           (equal (lhprobe-map-overridemux-eval lhmap envs outs)
                  ans)))



;; needed from svtv-generalize:
;; svtv-override-triple-envs-match
;; svtv-override-triplemap-envs-match
;; svtv-override-triplemaplist-envs-match
