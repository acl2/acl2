; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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


; stv-sim.lisp -- general simulations for STVs, and final STV processing
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "centaur/vl2014/util/defs" :dir :system)
(include-book "../steps")
(include-book "std/typed-lists/cons-listp" :dir :system)
(local (include-book "std/typed-lists/atom-listp" :dir :system))

(local (defthm atom-listp-of-pat-flatten1
         (atom-listp (pat-flatten1 x))
         :hints(("Goal" :in-theory (e/d (pat-flatten1)
                                        ((force)))))))


(define stv-fully-general-st-alist
  :parents (stv-process)
  :short "Create the sexpr-alist to use as the initial state for fully general
simulations of a module."
  ((mod "The @(see esim) module."))
  :returns (state-alist "Alist binding every state bit @('|foo|') to
                         @('|foo.INIT|')")

  :long "<p>These names (obviously) can't clash with each other, or with those
produced by @(see stv-fully-general-in-alists).</p>

<p>We memoize this to ensure we'll get the same initial state alist across
different STVs that target the same module.</p>"

  (b* ((sts      (mod-state mod))
       (flat-sts (pat-flatten sts nil))
       ((unless (symbol-listp flat-sts))
        (raise "Expected mod-state to produce a symbol pattern for ~x0."
               (gpl :n mod))))
    (pairlis$ flat-sts
              (stv-suffix-signals flat-sts ".INIT")))
  ///
  (memoize 'stv-fully-general-st-alist))



(define stv-fully-general-in-alist-n ((n        natp)
                                      (flat-ins symbol-listp))
  :parents (stv-fully-general-in-alists)
  :long "<p>We memoize this to ensure that we'll get the same fully general
alist across different STVs that target the same module for the same numbers of
steps.</p>"

  :returns (nth-alist cons-listp)
  (pairlis$ flat-ins
            (stv-suffix-signals flat-ins (str::cat ".P" (str::natstr n))))

  :prepwork
  ((local (defthm c0
           (cons-listp (pairlis$ x y))
           :hints(("Goal" :in-theory (enable pairlis$))))))
  ///
  (memoize 'stv-fully-general-in-alist-n))


(define stv-fully-general-in-alists-aux ((n        natp)
                                         (flat-ins symbol-listp)
                                         acc)
  :parents (stv-fully-general-in-alists)
  :returns (in-alists cons-list-listp :hyp (cons-list-listp acc))
  (let ((acc (cons (stv-fully-general-in-alist-n n flat-ins) acc)))
    (if (zp n)
        acc
      (stv-fully-general-in-alists-aux (- n 1) flat-ins acc)))
  ///
  (defthm len-stv-fully-general-in-alists-aux
    (equal (len (stv-fully-general-in-alists-aux n flat-ins acc))
           (+ 1 (nfix n) (len acc)))))


(define stv-fully-general-in-alists
  :parents (stv-process)
  :short "Create the sexpr-alists to use as the inputs for each phase of fully
general simulations of a module."

  ((n   "The number of phases to simulate." posp)
   (mod "The @(see esim) module."))
  :returns (in-alists cons-list-listp)

  :long "<p>This is basically name mangling.  For instance, at phase 5 the
input @('|foo[3]|') will be represented by the variable @('|foo[3].P5|').
There can't be any name clashes since we're adding a such a suffix to every
signal.</p>"

  (b* ((ins      (gpl :i mod))
       (flat-ins (pat-flatten1 ins))
       ((when (mbe :logic (not (posp n)) :exec nil))
        nil)
       ((unless (symbol-listp flat-ins))
        (raise "Expected :i for ~x0 to be a symbol pattern." (gpl :n mod))
        (ec-call (stv-fully-general-in-alists-aux (- n 1) flat-ins nil))))
    (stv-fully-general-in-alists-aux (- n 1) flat-ins nil))
  ///
  (defthm len-stv-fully-general-in-alists
    (equal (len (stv-fully-general-in-alists n mod))
           (nfix n))))


(local (in-theory (disable good-esim-modulep)))

(define stv-run-esim
  :parents (stv-process)
  ((mod           "The module to run." good-esim-modulep)
   (in-alists     "A list of N alists, to be used at each phase.")
   (state-alists  "A list of N alists, to override particular state bits.")
   (initial-state "Initial state to use."))
  :guard (eql (len in-alists) (len state-alists))
  :returns (mv (nsts "A list of next-state alists.")
               (outs "A list of outputs alists."))
  (b* (((when (atom in-alists))
        (mv nil nil))
       (state-alist (append-without-guard (car state-alists) initial-state))
       ((mv nst1 out1)
        (esim-sexpr-simp mod (car in-alists) state-alist))
       ((mv nst-rest out-rest)
        (stv-run-esim mod (cdr in-alists) (cdr state-alists) nst1)))
    (mv (cons nst1 nst-rest)
        (cons out1 out-rest))))

(define stv-fully-general-simulation-run
  :parents (stv-process)
  :short "Run an @('n') step, fully general simulation of a module."

  ((n   "How many phases to simulate." posp)
   (mod "The @(see esim) module.")
   (override-stbits "List of override value and decision state bits"
                    symbol-listp))

  :returns
  (mv (init-st "Initial state alist that we used.  This is just generated by
                @(see stv-fully-general-st-alist) and is probably not very
                interesting.")

      (in-alists "Input alists that we used at each phase.  This is just
                  generated by @(see stv-fully-general-in-alists) and is
                  probably not very interesting.")

      (nst-alists "A list of @('n') alists that capture the fully general
                   next-state after each phase.")

      (out-alists "A list of @('n') alists that capture the fully general
                   outputs after each phase.")

      (nil "An extra output which is always @('nil'), for signature
            compatibility with @(see stv-fully-general-simulation-debug)."))

  :long "<p>This is a fully general simulation, so the nst/out-alists bind
signal names to @(see 4v-sexprs) in terms of the variables in the init-st and
in-alists.</p>

<p>See also @(see stv-fully-general-simulation-debug), which produces the same
outputs but also captures the internal signals after each phase.</p>

<p>We memoize this function so that if we're reusing an STV, we can just reuse
the same general simulation repeatedly.  BOZO maybe we should be memoizing the
individual steps instead of the whole run, to get more cross-stv sharing.</p>"

  (b* ((in-alists     (stv-fully-general-in-alists n mod))
       (init-st-alist (stv-fully-general-st-alist mod))
       (override-alists (stv-fully-general-in-alists-aux (- n 1) override-stbits nil))
       ((mv nsts outs)
        (ec-call
         (stv-run-esim mod in-alists override-alists init-st-alist))))
    (mv init-st-alist in-alists nsts outs nil))
  ///
  (memoize 'stv-fully-general-simulation-run :aokp t))





(define stv-run-esim-debug
  :parents (stv-process)
  ((mod           "The module to run." (and (good-esim-modulep mod)
                                            (new-good-esim-probe-modulep mod)))
   (in-alists     "A list of N alists, to be used at each phase.")
   (state-alists  "A list of N alists, to override particular state bits.")
   (initial-state "Initial state to use."))
  :guard (eql (len in-alists) (len state-alists))
  :returns (mv (nsts "A list of next-state alists.")
               (outs "A list of outputs alists.")
               (ints "A list of internals alists."))
  (b* (((when (atom in-alists))
        (mv nil nil nil))
       (state-alist (append-without-guard (car state-alists) initial-state))
       ((mv nst1 out1 int1)
        (esim-sexpr-simp-new-probe mod (car in-alists) state-alist))
       ((mv nst-rest out-rest int-rest)
        (stv-run-esim-debug mod (cdr in-alists) (cdr state-alists) nst1)))
    (mv (cons nst1 nst-rest)
        (cons out1 out-rest)
        (cons int1 int-rest)))
  ///
  (defthm len-of-stv-run-esim-debug-0
    (equal (len (mv-nth 0 (stv-run-esim-debug mod ins st-overrides initial-st)))
           (len ins)))

  (defthm len-of-stv-run-esim-debug-1
    (equal (len (mv-nth 1 (stv-run-esim-debug mod ins st-overrides initial-st)))
           (len ins)))

  (defthm len-of-stv-run-esim-debug-2
    (equal (len (mv-nth 2 (stv-run-esim-debug mod ins st-overrides initial-st)))
           (len ins))))



(define stv-fully-general-simulation-debug
  :parents (stv-debug)
  :short "Run an @('n') step, fully general simulation of @('mod') just like
@(see stv-fully-general-simulation-run), but also gather the fully general
expressions for internal signals."

  ((n   "How many phases to simulate." posp)
   (mod "The @(see esim) module.")
   (override-stbits "List of override value and decision state bits"
                    symbol-listp))

  :returns (mv (init-st    "As in @(see stv-fully-general-simulation-run)")
               (in-alists  "As in @(see stv-fully-general-simulation-run)")
               (nst-alists "As in @(see stv-fully-general-simulation-run)")
               (out-alists "As in @(see stv-fully-general-simulation-run)")

               (int-alists "A list of @('n') alists that capture the fully
                            general internal signals after each phase."))

  :long "<p>This is practically identical to @(see
stv-fully-general-simulation-run), except that it also gathers up and returns a
list of @('int-alists') which contain the expressions for the internal signals
of the module.</p>

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

  (b* ((in-alists     (stv-fully-general-in-alists n mod))
       (init-st-alist (stv-fully-general-st-alist mod))
       (override-alists (stv-fully-general-in-alists-aux (- n 1) override-stbits nil))
       ((mv nsts outs internals)
        (ec-call (stv-run-esim-debug mod in-alists override-alists init-st-alist))))
    (mv init-st-alist in-alists nsts outs internals))
  ///
  (memoize 'stv-fully-general-simulation-debug :aokp t)

  (local (in-theory (enable stv-fully-general-simulation-debug)))

  (defthm len-of-stv-fully-general-simulation-debug-1
    (equal (len (mv-nth 1 (stv-fully-general-simulation-debug nphases mod override-stbits)))
           (nfix nphases)))

  (defthm len-of-stv-fully-general-simulation-debug-2
    (equal (len (mv-nth 2 (stv-fully-general-simulation-debug nphases mod override-stbits)))
           (nfix nphases)))

  (defthm len-of-stv-fully-general-simulation-debug-3
    (equal (len (mv-nth 3 (stv-fully-general-simulation-debug nphases mod override-stbits)))
           (nfix nphases)))

  (defthm len-of-stv-fully-general-simulation-debug-4
    (equal (len (mv-nth 4 (stv-fully-general-simulation-debug nphases mod override-stbits)))
           (nfix nphases)))

  (defthm cons-list-listp-of-stv-fully-general-simulation-debug-1
    (cons-list-listp
     (mv-nth 1 (stv-fully-general-simulation-debug nphases mod override-stbits)))))



; The final processing stuff could go in its own file, but we already have
; everything it depends on here, so to optimize build time this seems like the
; right place for it.

(define stv-extract-relevant-signals
  :parents (stv-process)
  :short "Pull out the fully general expressions for the signals that we care
about, and bind them to the bit names of the simulation variables."

  ((extract-alists "The @(see stv-extraction-alists) we obtained from @(see
                    stv-compile).")
   (out-alists     "The list of output alists from the fully general simulation,
                    e.g., from @(see stv-fully-general-simulation-run).")
   (acc            "An accumulator to extend, which should initially be nil."))

  :long "<p>We walk down the @('extract-alists') and @('out-alists') together,
extracting the expressions for the signals that we care about at each phase,
and naming them with the output simulation variable bit names.</p>"

  (b* (((when (and (atom extract-alists)
                   (atom out-alists)))
        acc)

       ((when (or (atom extract-alists)
                  (atom out-alists)))
        (raise "Should have as many extract alists as out-alists."))

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
       (want-exprs (vl2014::look-up-each-fast want-names outs1))
       (-          (fast-alist-free outs1))
       (acc        (safe-pairlis-onto-acc user-bits want-exprs acc)))
    (stv-extract-relevant-signals (cdr extract-alists)
                                  (cdr out-alists)
                                  acc)))


(define stv-process
  :parents (symbolic-test-vectors)
  :short "Process a symbolic test vector and prepare it to be run."

  ((name "A name for this STV.  Used by @(see stv-debug)."
         symbolp)

   (stv  stvdata-p
         "The bundled up, original symbolic test vector description that the
          user wrote.  This isn't actually used for anything, except that we
          stuff it into the resulting processed-stv, perhaps mainly for
          documentation?")

   (cstv compiled-stv-p
         "An already-compiled version of @('stv').  We take this as an argument,
          rather than compiling it ourselves, mainly to parallelize the STV
          book building process.")

   (mod  good-esim-modulep
         "The @(see esim) module that @('stv') is being written for."))

  :returns (pstv (equal (processed-stv-p pstv)
                        (if pstv t nil))
                 :hyp (and (force (symbolp name))
                           (force (compiled-stv-p cstv)))
                 "The fully processed, ready-to-run STV.")

  :long "<p>An STV must be processed before it can be run with @(see stv-run).
This processing can be expensive and involves several steps.</p>

<ul>

<li>The @('mod') is symbolically simulated using a fully-general multi-phase
@(see esim) simulation.</li>

<li>The relevant outputs are then extracted from this simulation and
specialized as suggested by this particular @('stv').</li>

<li>These restricted outputs and other information is then saved into a @(see
processed-stv-p) object that can be given to @(see stv-run) or @(see
stv-debug).</li>

</ul>

<p>Note that there are many chances for memoization, e.g., if you have a lot of
different symbolic test vectors that all target the same module, they can reuse
the same @(see esim) simulation, so processing the first STV may be very
expensive but processing subsequent STVs can be much cheaper.</p>"

  (b* (((compiled-stv cstv) cstv)

       (need-internals
        ;; We can avoid computing the internal signals if we didn't ask for
        ;; any.  This is kind of silly, but it can save a lot of time if you
        ;; don't care about the internals at all.
        (not (subsetp cstv.int-extract-alists '(nil))))

       ((mv ?init-st-general
            ?in-alists-general
            nst-alists-general
            out-alists-general
            int-alists-general)
        ;; Do the fully general simulation for however many steps are needed.
        (if need-internals
            (time$ (stv-fully-general-simulation-debug cstv.nphases mod cstv.override-bits)
                   :msg "; stv-process debug simulation: ~st sec, ~sa bytes.~%"
                   :mintime 1/2)
          (time$ (stv-fully-general-simulation-run cstv.nphases mod cstv.override-bits)
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
                         acc))
                      (acc
                       (stv-extract-relevant-signals cstv.nst-extract-alists
                                                     nst-alists-general
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
        (time$ (with-fast-alist cstv.restrict-alist
                 (4v-sexpr-restrict-with-rw-alist relevant-signals-general
                                                  cstv.restrict-alist))
               :msg "; stv-process specialization: ~st sec, ~sa bytes.~%"
               :mintime 1/2)))

    (make-processed-stv :name             name
                        :user-stv         stv
                        :compiled-stv     cstv
                        :relevant-signals relevant-signals-specialized)))

