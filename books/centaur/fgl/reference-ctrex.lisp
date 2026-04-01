;; FGL - A Symbolic Simulation Framework for ACL2
;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FGL")

(include-book "fancy-ev")

(defxdoc reference-ctrex
  :parents (fgl-counterexamples)
  :short "Symbolic execution with a reference counterexample"
  :long "
<p>In most typical uses of FGL, we expect to be able to directly translate a
counterexample from SAT to an assignment to the theorem's variables. In that
case, we can analyze the counterexample by simply running the theorem on that
assignment and debugging its (concrete) execution.  This is the case if, e.g.,
the theorem variables are bitvectors and the Boolean variables considered in
the symbolic execution (and given an assignment of values by the SAT
counterexample) are the bits of those bitvectors. However, the more we move to
an abstract, high-level view, the less likely we can map a SAT counterexample
to theorem variables. But the SAT counterexample should give us a useful
diagnosis without doing so.</p>

<p>The idea behind the <em>reference counterexample</em> is that if a symbolic
execution gives rise to a counterexample, we can repeat that same symbolic
execution but keeping in mind that counterexample, i.e. printing some debugging
information during the symbolic simulation that reveals more information about
the counterexample.</p>

<h3>Setup</h3>

<p>To set up a reference counterexample, set the @('reference-ctrex-action')
field of the FGL configuration. See @(see fgl-config) object for how to do this
and the operation of that field. Generally, if the field is @('nil') (the
default) it signifies that no reference counterexample is being used.</p>

<h3>Ways of using the reference counterexample:</h3>

<p>The following functions can be executed by FGL rewrite rules inside @(see
syntax-bind), @(see syntax-interp), @(see syntaxp), and @(see bind-free)
forms.</p>

<h4>@('reference-ctrex-check-path-condition-satisfied')</h4>

<p>This function checks the stored reference counterexample against the current
path condition to see whether the counterexample satisfies the path condition;
that is, whether execution of the counterexample would have taken the current
control path traversed by the symbolic execution. If the
@('reference-ctrex-action') config field is @('nil'), then this function always
returns @('nil'). It also returns an updated @('interp-st'); the return values
are @('(mv pathcond-sat interp-st)').</p>

<p>A macro @('reference-ctrex-pathcond-check') wraps this in a
@('syntax-interp') and can be called in any @(see unequiv) context, such as the
second argument of @(see bind-var) or the first argument of @(see
fgl-prog2). Since it calls @(see syntax-interp) for itself, it should not be
used inside a syntactic evaluation environment such as @(see syntax-interp).</p>

<p>Example of the use of @('reference-ctrex-check-path-condition-satisfied'):</p>
@({
 (fgl::def-fgl-rewrite show-occurrences-of-foo-under-reference-ctrex-pathcond
   (equal (foo x)
          (fgl::fgl-progn
            (b* ((in-path (fgl::syntax-interp
                             (b* (((mv in-path &) (reference-ctrex-check-path-condition-satisfied 'interp-st)))
                               in-path))))
               (and in-path
                    (fgl::syntax-interp (cw \"Call of foo on ~x0 under counterexample~%\" x))))
            (fgl::abort-rewrite (foo x)))))
 })

<p>This may be shortened somewhat using the macro:</p>
@({
 (fgl::def-fgl-rewrite show-occurrences-of-foo-under-reference-ctrex-pathcond
   (equal (foo x)
          (fgl::fgl-progn
            (and (fgl::reference-ctrex-pathcond-check)
                 (fgl::syntax-interp (cw \"Call of foo on ~x0 under counterexample~%\" x)))
            (fgl::abort-rewrite (foo x)))))
 })


<h4>@('reference-ctrex-fgl-object-eval)</h4>

<p>This function attempts to evaluate an FGL object under the Boolean
assignment (and theorem variable assignment, if any) of the reference
counterexample. It may not be reliable for objects containing termlike
constructs (function calls, theorem variables). If the current symbolic
simulation is sufficiently similar to the one that generated the reference
counterexample (see Pitfalls below), symbolic Boolean and bitvector values
should be reliably correct.</p>

<p>A macro @('reference-ctrex-object-eval-msg') produces a @(see msgp) object
suitable for printing with @(see fmt) or @(see cw)'s @('~@') forms. It can be
called in any @(see unequiv) context, such as the second argument of @(see
bind-var) or the first argument of @(see fgl-prog2). It calls @(see
syntax-interp) for itself so it should not be used inside a syntactic
evaluation environment such as @(see syntax-interp).</p>

<h3>Pitfalls<h3>

<p>The functions that use the reference counterexample assume that the current
symbolic simulation has generated a prefix of the Boolean variables of those
generated by the symbolic simulation that produced the reference
counterexample. That is, the current symbolic simulation must be replicating
the same Boolean variable database that was produced when the counterexample
was generated. That means rewrite rules should take care not to generate
Boolean variables within code that is only run under a reference
counterexample. If you need to check the truth value of some object in such
code, you can check first whether it is already a Boolean variable using
@('interp-st-get-term->bvar') under a @('syntax-interp') context.</p>

")
;; <p>Second, the function @('reference-ctrex-eval') tries to evaluate a given
;; object in the reference counterexample.</p>

(local (include-book "std/lists/resize-list" :dir :System))


(local (defthm len-of-aignet-eval-tailrec
         (implies (and (<= (aignet::num-fanins aignet) (len bitarr))
                       (natp n))
                  (equal (len (aignet::aignet-eval-tailrec n bitarr aignet))
                         (len bitarr)))
         :hints(("Goal" :in-theory (e/d (aignet::aignet-eval-tailrec
                                         aignet::aignet-eval-step)
                                        (update-nth nth b-xor b-and))))))

(local (defthm len-of-aignet-invals->vals-tailrec
         (implies (and (<= (aignet::num-fanins aignet) (len bitarr))
                       (natp n))
                  (equal (len (aignet::aignet-invals->vals-tailrec n invals bitarr aignet))
                         (len bitarr)))
         :hints(("Goal" :in-theory (e/d (aignet::aignet-invals->vals-tailrec
                                         aignet::aignet-invals->vals-step)
                                        (update-nth nth b-xor b-and))))))

(local (defthm pathcond-boundedp-when-logicman-pathcond-p
         (implies (and (bind-free '((logicman . (interp-st->logicman interp-st))) (logicman))
                       (logicman-pathcond-p pathcond)
                       (lbfr-mode-is :aignet)
                       (<= (+ 1 (bfrstate->bound (logicman->bfrstate))) (nfix n)))
                  (aignet::bounded-pathcond-p (nth *pathcond-aignet* pathcond) n))
         :hints(("Goal" :in-theory (enable bfr-pathcond-p)))))


(define reference-ctrex-update-env ((interp-st interp-st-bfrs-ok))
  :returns new-interp-st
  (stobj-let
   ((logicman (interp-st->logicman interp-st))
    (reference-ctrex (interp-st->reference-ctrex interp-st)))
   (reference-ctrex)
   (b* (((unless (lbfr-mode-is :aignet)) reference-ctrex)
        (init-ins (reference-ctrex->initialized-ins reference-ctrex))
        (init-fanins (reference-ctrex->initialized-fanins reference-ctrex)))
     (stobj-let
      ((aignet (logicman->aignet logicman)))
      (reference-ctrex)
      (stobj-let
       ((env$ (reference-ctrex->env reference-ctrex))
        (bitarr (reference-ctrex->invals reference-ctrex)))
       (env$ bitarr)
       (stobj-let
        ((bitarr2 (env$->bitarr env$)))
        (bitarr2 bitarr)
        (b* ((env-length (bits-length bitarr2))
             (fanins (aignet::num-fanins aignet))
             (bitarr2 (if (< env-length fanins)
                          (resize-bits (* 2 fanins) bitarr2)
                        bitarr2))
             (bitarr (if (< (bits-length bitarr) (aignet::num-ins aignet))
                         (prog2$ (cw "~x0: not enough counterexample bits for the current Boolean variables!~%" __function__)
                                 (resize-bits (* 2 (aignet::num-ins aignet)) bitarr))
                       bitarr))
             (bitarr2 (if (< init-ins (aignet::num-ins aignet))
                          (aignet::aignet-invals->vals-tailrec init-ins bitarr bitarr2 aignet)
                        bitarr2))
             (bitarr2 (if (< init-fanins (aignet::num-fanins aignet))
                          (aignet::aignet-eval-tailrec init-fanins bitarr2 aignet)
                        bitarr2)))
          (mv bitarr2 bitarr))
        (mv env$ bitarr))
       reference-ctrex)
      reference-ctrex))
   interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :reference-ctrex))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))
  
  (defret bitarr-length-<fn>
    (implies (lbfr-mode-is :aignet (interp-st->logicman interp-st))
             (<= (aignet::num-fanins
                  (logicman->aignet
                   (interp-st->logicman interp-st)))
                 (len (env$->bitarr
                       (reference-ctrex->env
                        (interp-st->reference-ctrex new-interp-st))))))
    :rule-classes :linear))

(define reference-ctrex-check-path-condition-satisfied ((interp-st interp-st-bfrs-ok))
  :returns (mv satisfied new-interp-st)
  (b* (((fgl-config config) (interp-st->config interp-st))
       ((unless config.reference-ctrex-action) (mv nil interp-st))
       (interp-st (reference-ctrex-update-env interp-st)))
    (stobj-let
     ((logicman (interp-st->logicman interp-st))
      (pathcond (interp-st->pathcond interp-st))
      (reference-ctrex (interp-st->reference-ctrex interp-st)))
     (status)
     (b* (((unless (lbfr-mode-is :aignet)) nil))
       (stobj-let
        ((env$ (reference-ctrex->env reference-ctrex))
         (bitarr (reference-ctrex->invals reference-ctrex)))
        (status)
        (stobj-let
         ((bitarr2 (env$->bitarr env$)))
         (status)
         (stobj-let
          ((aignet-pathcond (pathcond-aignet pathcond)))
          (status)
          (aignet::aignet-pathcond-eval-exec aignet-pathcond bitarr2)
          status)
         status)
        status))
     (mv status interp-st)))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :reference-ctrex))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))
  
  ;; (make-event
  ;;  (cons 'progn (cdr (butlast *fancy-ev-primitive-thms* 1))))
  ;; not the last one since we don't take state
  ;; the first one is interp-st-get of which we have a better one above
  )

(fancy-ev-add-primitive reference-ctrex-check-path-condition-satisfied t)

(defxdoc reference-ctrex-check-path-condition-satisfied
  :parents (reference-ctrex)
  :short "Check whether the current path condition is true under the reference
counterexample; that is, whether we are in code that would be executed when
running that counterexample."
  :long "<p>See @(see reference-ctrex) for details.</p>")

(defmacro reference-ctrex-pathcond-check ()
  '(syntax-interp
    (b* (((mv res &) (reference-ctrex-check-path-condition-satisfied 'interp-st)))
      res)))

(defxdoc reference-ctrex-pathcond-check
  :parents (reference-ctrex)
  :short "Check whether the current path condition is true under the reference
counterexample; that is, whether we are in code that would be executed when
running that counterexample."
  :long "<p>See @(see reference-ctrex) for details.</p>")



(include-book "ctrex-utils")

(define reference-ctrex-fgl-object-eval ((x fgl-object-p)
                                         &optional
                                         (interp-st 'interp-st)
                                         (state 'state))
  :parents (reference-ctrex)
  :short "Evaluate an object under the reference counterexample."
  :long "<p>See @(see reference-ctrex) for details.</p>"
  :guard (and (interp-st-bfrs-ok interp-st)
              (fgl-object-bfrs-ok x (interp-st-bfr-state)))
  :returns (mv err val new-interp-st)
  :guard-hints (("goal" :in-theory (enable bfr-env$-p)))
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (mv "bad BFR mode" nil interp-st))
       (interp-st (reference-ctrex-update-env interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (reference-ctrex (interp-st->reference-ctrex interp-st)))
               (err val)
               (stobj-let ((env$ (reference-ctrex->env reference-ctrex)))
                          (err val)
                          (magic-fgl-object-eval x env$ logicman state)
                          (mv err val))
               (mv err val interp-st)))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :reference-ctrex))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))


(fancy-ev-add-primitive reference-ctrex-fgl-object-eval-fn
                        (and (fgl-object-p x)
                             (fgl-object-bfrs-ok x (interp-st-bfr-state))))


(defmacro reference-ctrex-object-eval-msg (x)
  `(let ((refctrex-eval-obj ,x))
     (syntax-interp
      (b* (((mv err val &) (reference-ctrex-fgl-object-eval refctrex-eval-obj)))
        (or err
            (msg "~x0" val))))))

(defxdoc reference-ctrex-object-eval-msg
  :parents (reference-ctrex)
  :short "Evaluate an object under the reference counterexample and return a message
suitable for printing the result."
  :long "<p>See @(see reference-ctrex) for details.</p>")


(define reference-ctrex-fgl-objectlist-eval ((x fgl-objectlist-p)
                                         &optional
                                         (interp-st 'interp-st)
                                         (state 'state))
  :guard (and (interp-st-bfrs-ok interp-st)
              (fgl-objectlist-bfrs-ok x (interp-st-bfr-state)))
  :returns (mv err val new-interp-st)
  :guard-hints (("goal" :in-theory (enable bfr-env$-p)))
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (mv "bad BFR mode" nil interp-st))
       (interp-st (reference-ctrex-update-env interp-st)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (reference-ctrex (interp-st->reference-ctrex interp-st)))
               (err val)
               (stobj-let ((env$ (reference-ctrex->env reference-ctrex)))
                          (err val)
                          (magic-fgl-objectlist-eval x env$ logicman state)
                          (mv err val))
               (mv err val interp-st)))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :reference-ctrex))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))


(fancy-ev-add-primitive reference-ctrex-fgl-objectlist-eval-fn
                        (and (fgl-objectlist-p x)
                             (fgl-objectlist-bfrs-ok x (interp-st-bfr-state))))


