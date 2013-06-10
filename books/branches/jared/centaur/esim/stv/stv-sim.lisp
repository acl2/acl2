; ESIM Symbolic Hardware Simulator
; Copyright (C) 2010-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.


; stv-sim.lisp -- general simulations for STVs, and final STV processing
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "centaur/vl/util/defs" :dir :system)
(include-book "../steps")

(local (defthm atom-listp-of-append
         (implies (and (atom-listp x)
                       (atom-listp y))
                  (atom-listp (append x y)))
         :hints(("Goal" :in-theory (disable (force))))))

(local (defthm atom-listp-of-pat-flatten1
         (atom-listp (pat-flatten1 x))
         :hints(("Goal" :in-theory (e/d (pat-flatten1)
                                        ((force)))))))


(defsection stv-fully-general-st-alist
  :parents (stv-process)
  :short "@(call stv-fully-general-st-alist) generates a single alist that will
provide the values for the initial state of @('mod') for a fully general
simulation."

  :long "<p>We basically just bind every state bit @('|foo|') to
@('|foo.INIT|').  These names can't clash with each other, or with those
produced by @(see stv-fully-general-in-alists).</p>

<p>We memoize this to ensure we'll get the same initial state alist across
different STVs that target the same module.</p>"

  (defund stv-fully-general-st-alist (mod)
    (declare (xargs :guard t))
    (b* ((sts      (mod-state mod))
         (flat-sts (pat-flatten sts nil))
         ((unless (symbol-listp flat-sts))
          (er hard? 'stv-fully-general-st-alist
              "Expected mod-state to produce a symbol pattern for ~x0." (gpl :n mod))))
      (pairlis$ flat-sts
                (stv-suffix-signals flat-sts ".INIT"))))

  (memoize 'stv-fully-general-st-alist))



(defsection stv-fully-general-in-alists
  :parents (stv-process)
  :short "@(call stv-fully-general-in-alists) generates @('n') alists which we
will use as the inputs to @('mod') to do an @('n')-phase, fully general
simulation."

  :long "<p>This is basically name mangling.  For instance, at phase 5 the
input @('|foo[3]|') will be represented by the variable @('|foo[3].P5|').
There can't be any name clashes since we're adding a such a suffix to every
signal.</p>

<p>We memoize this to ensure that we'll get the same fully general alist across
different STVs that target the same module for the same numbers of steps.</p>"

  (defund stv-fully-general-in-alist-n (n flat-ins)
    (declare (xargs :guard (and (symbol-listp flat-ins)
                                (natp n))))
    (pairlis$ flat-ins
              (stv-suffix-signals flat-ins (str::cat ".P" (str::natstr n)))))

  (memoize 'stv-fully-general-in-alist-n)

  (local (defthm c0
           (vl::cons-listp (pairlis$ x y))
           :hints(("Goal" :in-theory (enable pairlis$)))))

  (defthm cons-listp-of-stv-fully-general-in-alist-n
    (vl::cons-listp (stv-fully-general-in-alist-n n flat-ins))
    :hints(("Goal" :in-theory (enable stv-fully-general-in-alist-n))))

  (defund stv-fully-general-in-alists-aux (n flat-ins acc)
    (declare (xargs :guard (and (symbol-listp flat-ins)
                                (natp n))))
    (let ((acc (cons (stv-fully-general-in-alist-n n flat-ins) acc)))
      (if (zp n)
          acc
        (stv-fully-general-in-alists-aux (- n 1) flat-ins acc))))

  (defthm len-stv-fully-general-in-alists-aux
    (equal (len (stv-fully-general-in-alists-aux n flat-ins acc))
           (+ 1 (nfix n) (len acc)))
    :hints(("Goal" :in-theory (enable stv-fully-general-in-alists-aux))))

  (defthm cons-list-listp-of-stv-fully-general-in-alists-aux
    (implies (vl::cons-list-listp acc)
             (vl::cons-list-listp (stv-fully-general-in-alists-aux n flat-ins acc)))
    :hints(("Goal" :in-theory (enable stv-fully-general-in-alists-aux))))

  (defund stv-fully-general-in-alists (n mod)
    (declare (xargs :guard (posp n)))
    (b* ((ins      (gpl :i mod))
         (flat-ins (pat-flatten1 ins))
         ((when (mbe :logic (not (posp n)) :exec nil))
          nil)
         ((unless (symbol-listp flat-ins))
          (er hard? 'stv-fully-general-in-alists
              "Expected :i for ~x0 to be a symbol pattern." (gpl :n mod))
          (ec-call (stv-fully-general-in-alists-aux (- n 1) flat-ins nil))))
      (stv-fully-general-in-alists-aux (- n 1) flat-ins nil)))

  (defthm len-stv-fully-general-in-alists
    (equal (len (stv-fully-general-in-alists n mod))
           (nfix n))
    :hints(("Goal" :in-theory (enable stv-fully-general-in-alists))))

  (defthm cons-list-listp-of-stv-fully-general-in-alists
    (vl::cons-list-listp (stv-fully-general-in-alists n mod))
    :hints(("Goal" :in-theory (enable stv-fully-general-in-alists)))))


(defsection stv-fully-general-simulation-run
  :parents (stv-process)
  :short "Run an @('n') step, fully general simulation of @('mod')."

  :long "<p><b>Signature:</b> @(call stv-fully-general-simulation-run) returns
@('(mv init-st in-alists nst-alists out-alists NIL)').</p>

<p>The @('init-st') and @('in-alists') are just generated by @(see
stv-fully-general-st-alist) and @(see stv-fully-general-in-alists),
respectively, and are probably not very interesting.</p>

<p>The @('nst-alists') and @('out-alists') are each lists of @('n') alists,
representing the fully-general next states and outputs after each phase.  These
alists bind signal names to @(see 4v-sexprs) that do not have any assumptions
about the values given to the module at each phase.</p>

<p>See also @(see stv-fully-general-simulation-debug), which produces the same
alists and also produces a list of fully general alists for the internal wires
of the modules.  The extra @('nil') we return is for signature compatibility
with the @('-debug') version.</p>

<p>We memoize this function so that if we're reusing an STV, we can just reuse
the same general simulation repeatedly.  BOZO maybe we should be memoizing the
individual steps instead of the whole run.</p>"

  (defund stv-fully-general-simulation-run (n mod)
    "Returns (MV INIT-ST IN-ALISTS NST-ALISTS OUT-ALISTS NIL)"
    (declare (xargs :guard (posp n)))
    (b* ((in-alists     (stv-fully-general-in-alists n mod))
         (init-st-alist (stv-fully-general-st-alist mod))
         ((mv nsts outs)
          (ec-call
           (esim-sexpr-simp-steps mod in-alists init-st-alist))))
      (mv init-st-alist in-alists nsts outs nil)))

  (memoize 'stv-fully-general-simulation-run :aokp t))



(local
 (defsection basic-esim-lemmas

   (local (in-theory (enable esim-sexpr-simp-new-probe-steps)))

   (defthm len-of-esim-sexpr-simp-new-probe-steps-0
     (equal (len (mv-nth 0 (esim-sexpr-simp-new-probe-steps mod ins st)))
            (len ins)))

   (defthm len-of-esim-sexpr-simp-new-probe-steps-1
     (equal (len (mv-nth 1 (esim-sexpr-simp-new-probe-steps mod ins st)))
            (len ins)))

   (defthm len-of-esim-sexpr-simp-new-probe-steps-2
     (equal (len (mv-nth 2 (esim-sexpr-simp-new-probe-steps mod ins st)))
            (len ins)))))


(defsection stv-fully-general-simulation-debug
  :parents (stv-debug)
  :short "Run an @('n') step, fully general simulation of @('mod') just like
@(see stv-fully-general-simulation-run), but also gather the fully general
expressions for internal signals."

  :long "<p><b>Signature:</b> @(call stv-fully-general-simulation-debug)
returns @('(mv init-st in-alists nst-alists out-alists int-alists)').</p>

<p>This is practically identical to @(see stv-fully-general-simulation-run),
except that it also gathers up and returns a list of @('int-alists') which
contain the expressions for the internal signals of the module.</p>

<p>These expressions are useful for generating waveforms for debugging
simulations.  We could have just had @(see stv-fully-general-simulation-run)
always compute them, but computing the internal signals can be expensive so we
want to avoid it unless we're actually doing debugging.</p>

<p>Due to the structure of esim, we get a lot of memoized sharing between the
@('-run') and @('-debug') functions.  This works out very nicely, so that it's
not much more expensive to do a @('-debug') after first doing a @('-run') than
it is to just do a @('-debug') from the beginning.</p>

<p>We memoize this function so that if we're reusing an STV, we can just reuse
the same general simulation repeatedly as we debug with different values.  BOZO
as with the -run function, maybe we should be doing the memoization at the level
of individual steps, instead of memoizing the whole thing.</p>"

  (defund stv-fully-general-simulation-debug (n mod)
    ;; Same as -run, but includes internals for debugging
    "Returns (MV INIT-ST IN-ALISTS NST-ALISTS OUT-ALISTS INT-ALISTS)"
    (declare (xargs :guard (posp n)))
    (b* ((in-alists     (stv-fully-general-in-alists n mod))
         (init-st-alist (stv-fully-general-st-alist mod))
         ((mv nsts outs internals)
          (ec-call (esim-sexpr-simp-new-probe-steps mod in-alists init-st-alist))))
      (mv init-st-alist in-alists nsts outs internals)))

  (memoize 'stv-fully-general-simulation-debug :aokp t)

  (local (in-theory (enable stv-fully-general-simulation-debug)))

  (defthm len-of-stv-fully-general-simulation-debug-1
    (equal (len (mv-nth 1 (stv-fully-general-simulation-debug nphases mod)))
           (nfix nphases)))

  (defthm len-of-stv-fully-general-simulation-debug-2
    (equal (len (mv-nth 2 (stv-fully-general-simulation-debug nphases mod)))
           (nfix nphases)))

  (defthm len-of-stv-fully-general-simulation-debug-3
    (equal (len (mv-nth 3 (stv-fully-general-simulation-debug nphases mod)))
           (nfix nphases)))

  (defthm len-of-stv-fully-general-simulation-debug-4
    (equal (len (mv-nth 4 (stv-fully-general-simulation-debug nphases mod)))
           (nfix nphases)))

  (defthm cons-list-listp-of-stv-fully-general-simulation-debug-1
    (vl::cons-list-listp (mv-nth 1 (stv-fully-general-simulation-debug nphases mod)))))



; The final processing stuff could go in its own file, but we already have
; everything it depends on here, so for build time this seems like the right
; place for it.


(defsection stv-extract-relevant-signals
  :parents (stv-process)
  :short "Pull out the fully general expressions for the signals that we care
about, and bind them to the bit names of the simulation variables."

  :long "<p>@(call stv-extract-relevant-signals) is given:</p>

<ul>

<li>@('extract-alists'), the @(see stv-extraction-alists) we obtained from
@(see stv-compile),</li>

<li>@('out-alists'), the list of output alists we got from the fully general
simulation (e.g., from @(see stv-fully-general-simulation-run)), and</li>

<li>@('acc'), an accumulator to extend which should initially be nil.</li>

</ul>

<p>We walk down the @('extract-alists') and @('out-alists') together,
extracting the expressions for the signals that we care about at each phase,
and naming them with the output simulation variable bit names.</p>"

  (defund stv-extract-relevant-signals (extract-alists out-alists acc)
    (declare (xargs :guard t))
    (b* (((when (and (atom extract-alists)
                     (atom out-alists)))
          acc)

         ((when (or (atom extract-alists)
                    (atom out-alists)))
          (er hard? 'stv-extract-relevant-signals
              "Should have as many extract alists as out-alists."))

         (extr1 (car extract-alists))
         (outs1 (car out-alists))
         ((when (not extr1))
          ;; Optimization.  There is nothing to extract during this phase,
          ;; so just go on.  This is very common and lets us avoid making
          ;; a fast-alist for the out-alist at this step.
          (stv-extract-relevant-signals (cdr extract-alists)
                                        (cdr out-alists)
                                        acc))

         (user-bits  (alist-vals extr1))
         (want-names (alist-keys extr1))
         (outs1      (make-fast-alist outs1))
         (want-exprs (vl::look-up-each-fast want-names outs1))
         (-          (fast-alist-free outs1))
         (acc        (safe-pairlis-onto-acc user-bits want-exprs acc)))
      (stv-extract-relevant-signals (cdr extract-alists)
                                    (cdr out-alists)
                                    acc))))



(defsection stv-process
  :parents (symbolic-test-vectors)
  :short "Process a symbolic test vector and prepare it to be run."

  :long "<p><b>Signature:</b> @(call stv-process) returns a <see topic='@(url
processed-stv-p)'>processed STV.</see></p>

<p>The @('stv') should be an @(see stvdata-p), i.e., the bundled up original
symbolic test vector description that the user wrote; see @(see defstv).</p>

<p>The @('cstv') should be the already-compiled version of @('stv').  We take
this as an argument, rather than compiling it ourselves, to split up the build
process more nicely.</p>

<p>The @('mod') is the @(see esim) module that the @('stv') is being written
for.</p>

<p>An STV must be processed before it can be run with @(see stv-run).  This
processing can be expensive and involves several steps.  The @('mod') is
symbolically simulated using a fully-general multi-phase @(see esim)
simulation.  The relevant outputs are then extracted from this simulation and
specialized as suggested by this particular @('stv').  These restricted outputs
and other information is then saved into a @(see processed-stv-p) object that
can be given to @(see stv-run) or @(see stv-debug).</p>

<p>Note that there are many chances for memoization, e.g., if you have a lot of
different symbolic test vectors that all target the same module, they can reuse
the same @(see esim) simulation, so processing the first STV may be very
expensive but processing subsequent STVs can be much cheaper.</p>"

  (defund stv-process (stv cstv mod)
    (declare (xargs :guard (and (stvdata-p stv)
                                (compiled-stv-p cstv)
                                (good-esim-modulep mod))))
    (b* (((compiled-stv cstv) cstv)

         (need-internals
          ;; We can avoid computing the internal signals if we didn't ask for
          ;; any.  This is kind of silly, but it can save a lot of time if you
          ;; don't care about the internals at all.  This isn't ideal, better
          ;; would be to mark the CSTV with some flag that says whether it
          ;; needs any int-out bits.
          (consp cstv.expanded-ints))

         ((mv ?init-st-general
              ?in-alists-general
              ?nst-alists-general
              out-alists-general
              int-alists-general)
          ;; Do the fully general simulation for however many steps are needed.
          (if need-internals
              (time$ (stv-fully-general-simulation-debug cstv.nphases mod)
                     :msg "; stv-process debug simulation: ~st sec, ~sa bytes.~%"
                     :mintime 1/2)
            (time$ (stv-fully-general-simulation-run cstv.nphases mod)
                   :msg "; stv-process simulation: ~st sec, ~sa bytes.~%"
                   :mintime 1/2)))

         (relevant-signals-general
          ;; The out-alists-general and int-alists-general bind names to sexprs
          ;; based on the fully general inputs.  We probably don't care about
          ;; the vast majority of these names---usually we only care about a
          ;; few outputs at certain stages!  So now we pull out only the
          ;; signals we actually care about.  This seems like a good place to
          ;; stop distinguishing between internal and output signals, so that
          ;; the user just sees uniform output simulation variables.
          (time$ (let* ((acc nil)
                        (acc (stv-extract-relevant-signals cstv.out-extract-alists
                                                           out-alists-general
                                                           acc))
                        (acc
                         (if need-internals
                             (stv-extract-relevant-signals cstv.int-extract-alists
                                                           int-alists-general
                                                           acc)
                           acc)))
                   acc)
                 :msg "; stv-process extraction: ~st sec, ~sa bytes.~%"
                 :mintime 1/2))

         (relevant-signals-specialized
          ;; The general alists are still in terms of the fully general input
          ;; variables.  So, we now rewrite them using the restrict-alist,
          ;; which will basically (1) "assume" the concrete STV bindings, and
          ;; (2) replaces certain general input variables with the names of the
          ;; bits of the input simulation variables.
          (time$ (4v-sexpr-restrict-with-rw-alist relevant-signals-general
                                                  cstv.restrict-alist)
                 :msg "; stv-process specialization: ~st sec, ~sa bytes.~%"
                 :mintime 1/2)))

      (make-processed-stv :mod              mod
                          :user-stv         stv
                          :compiled-stv     cstv
                          :relevant-signals relevant-signals-specialized)))

  (local (in-theory (enable stv-process)))

  (defthm processed-stv-p-of-stv-process
    (implies (force (compiled-stv-p cstv))
             (equal (processed-stv-p (stv-process stv cstv mod))
                    (if (stv-process stv cstv mod)
                        t
                      nil)))))

