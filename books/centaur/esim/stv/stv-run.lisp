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


; stv-run.lisp -- main functions for running processed STVs
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "std/strings/hexify" :dir :system)
(include-book "centaur/misc/vecs-ints" :dir :system)
(include-book "centaur/vl2014/util/defs" :dir :system)
(include-book "centaur/4v-sexpr/bitspecs" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-rewrites" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-booleval" :dir :system)
(include-book "centaur/gl/gl-util" :dir :system)
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))


(defthm true-listp-of-safe-pairlis-onto-acc
  (implies (true-listp acc)
           (true-listp (safe-pairlis-onto-acc x y acc)))
  :rule-classes :type-prescription)

(define stv-simvar-inputs-to-bits
  :parents (stv-run)
  :short "Convert the user-level input alist (which binds simulation variables
to naturals) into a bit-level alist for @(see 4v-sexpr-eval)."

  ((user-alist  "The alist provided by the user that gives values to the input
                 simulation variables.  Each value should be a natural number that
                 is in the range for that simulation variable.")

   (in-usersyms "A fast alist that binds each input simulation variable for the
                 STV with a list of variables that represent its bits; see @(see
                 stv-compile), but in particular see the @('usersyms') output of
                 @(see stv-expand-input-entry)."))

  :long "<p>We try to translate every user-level binding, like @('(opcode
. 7)'), into a set of bit-level bindings, say something like:</p>

@({
  ((opcode[0] . *4vt*)
   (opcode[1] . *4vt*)
   (opcode[2] . *4vt*)
   (opcode[3] . *4vf*)
   ...)
})

<p>For each input simulation variable bound in the user-level alist, we
basically just need to look up the names of its bits in the @('in-usersyms')
alist, explode the value into @(see 4vp) bits, and then pairing up the bit
names with the values.  In the process, we do some basic sanity checking to
make sure that the names being bound exist and that the provided values are in
range.</p>

<p>The net result is a new alist that is suitable for @(see 4v-sexpr-eval) that
we can use to evaluate output expressions.</p>

<p>We don't check for duplicates in the user-alist, and if there are duplicates
it could lead to duplicate bindings in our resulting bit-level alist.  However,
the alist semantics are preserved because shadowed bindings are still shadowed
in the bit-level alist.</p>"

  (b* (((when (atom user-alist))
        nil)

       (rest  (stv-simvar-inputs-to-bits (cdr user-alist) in-usersyms))

       ((when (atom (car user-alist)))
        ;; Bad alist convention
        (cw "stv-simvar-inputs-to-bits: skipping malformed alist entry ~x0.~%"
            (car user-alist))
        rest)

       (name (caar user-alist))
       (val  (cdar user-alist))
       (look (hons-get name in-usersyms))

       ((unless look)
        (raise "Value given for ~x0, but this is not a simulation variable."
               name)
        rest)

       (vars  (cdr look))
       (nvars (len vars))

       (vals (cond ((eq val *4vx*)
                    (replicate nvars *4vx*))
                   ((and (natp val)
                         (< val (ash 1 nvars)))
                    (bool-to-4v-lst (int-to-v val nvars)))
                   (t
                    (progn$
                     (raise "Value ~x0 given for ~x1, but this value is not X ~
                             or in range for a ~x2-bit unsigned number."
                            val name nvars)
                     (replicate nvars *4vx*))))))

    (safe-pairlis-onto-acc vars vals rest)))


(define collect-bits-bound-to-x (keys alist)
  :parents (stv-assemble-output-alist)
  (b* (((when (atom keys))
        nil)
       (lookup (hons-get (car keys) alist))
       ((when (eq (cdr lookup) 'x))
        (cons (car keys)
              (collect-bits-bound-to-x (cdr keys) alist))))
    (collect-bits-bound-to-x (cdr keys) alist)))


(define stv-assemble-output-alist
  :parents (stv-run)
  :short "Convert the bit-level bindings from after @(see 4v-sexpr-eval) into
user-level bindings of the output simulation variables to naturals or X."

  ((bit-out-alist "A fast alist that binds the output simulation variable bit
                   names to their @(see 4vp) constants.  This alist should have
                   been produced by calling @(see 4v-sexpr-eval) on the
                   @('relevant-signals') sexprs of a @(see processed-stv-p).")

   (out-usersyms "An ordinary alist that binds each output simulation variable
                  for the STV with a list of variables that represent its bits;
                  see @(see stv-compile), but in particular see the
                  @('usersyms') output of @(see stv-expand-output-entry)"))

  :long "<p>We recur down @('out-usersyms').  For each output variable, we look
up the values of its bits in @('bit-out-alist'), and then try to combine these
bits into a single integer value.  If any bit is X, we just say the whole
output is X.</p>"

  (b* (((when (atom out-usersyms))
        nil)
       (rest (stv-assemble-output-alist bit-out-alist (cdr out-usersyms)))
       ((when (atom (car out-usersyms)))
        (raise "out-usersyms should be an alist.")
        rest)
       ((cons user-name bits) (car out-usersyms))
       (vals      (vl2014::look-up-each-fast bits bit-out-alist))
       (true-val  (4v-to-nat vals))
       (- (and (eq true-val 'x)
               (cw "Bits bound to X in ~x0: ~x1~%"
                   user-name (collect-bits-bound-to-x bits bit-out-alist)))))
    (cons (cons user-name true-val) rest)))


(define stv-print-alist (x)
  :parents (stv-run)
  :short "Dumb printing utility.  X is expected to be an alist binding symbols
          to values.  We print them out hexified and indented in a nice way."
  (b* (((when (atom x))
        nil)
       ((unless (consp (car x)))
        (raise "Malformed alist: Entry ~x0 is not a (key . val) pair.~%"
               (car x)))
       ((cons key val) (car x))
       ((unless (symbolp key))
        (raise "Malformed alist: name is not a symbolp.~%"
               (car x)))
       (- (cw "  ~s0:~t1~s2~%" key 20 (str::hexify val))))
    (stv-print-alist (cdr x))))

(define stv-run-collect-eval-signals ((pstv processed-stv-p)
                                      (skip))
  :returns (mv (sigs "alist binding the bits that we need to evaluate")
               (out-usersyms
                "for those outputs that aren't skipped, the mapping from names to bitname lists"))

  (b* (((processed-stv pstv) pstv)
       ((compiled-stv cstv) pstv.compiled-stv)

       (out-usersyms cstv.out-usersyms)

       ;; Start with all of the signals that we have in our STV.  These have
       ;; the expressions for the bits of the output simulation variables.
       (sigs        pstv.relevant-signals)

       ((when skip)
        (time$
         (b* (
              ;; As a sanity check, complain if there are any bits
              ;; that are being skipped that don't actually exist.
              (skip     (set::mergesort skip))
              (outnames (set::mergesort (alist-keys out-usersyms)))
              ((unless (set::subset skip outnames))
               (b* ((bad  (set::difference skip outnames))
                    ;; Don't use - or implicit progn$ on these, we want to make sure
                    ;; these get evaluated during GL runs.
                    (?msg (cw "Invalid skip!  Not outputs: ~&0." bad))
                    (?err (er hard? 'stv-run-fn "Invalid skip!  Not outputs: ~&0." bad)))
                 (mv sigs out-usersyms)))

              ;; Filter the out-usersyms down to just those that we want.
              (keep         (set::difference outnames skip))
              (out-usersyms (b* ((tmp (make-fal out-usersyms nil))
                                 (ret (fal-extract keep tmp)))
                              (fast-alist-free tmp)
                              ret))

              ;; Also filter the sigs down to just the bits we need.
              (keep-bits (vl2014::append-alist-vals out-usersyms))
              (sigs      (b* ((tmp (make-fal sigs nil))
                              (ret (fal-extract keep-bits tmp)))
                           (fast-alist-free tmp)
                           ret)))

           (mv sigs out-usersyms))

         :mintime 1/2
         :msg "; stv-run skips: ~st sec, ~sa bytes.")))

    (mv sigs out-usersyms)))

(define stv-run-make-eval-env ((pstv processed-stv-p)
                               (input-alist))
  (b* ((in-usersyms
        ;; These should already be a fast alist, but in case the object was
        ;; serialized and reloaded or something, we'll go ahead and try to
        ;; make them fast again.
        (make-fast-alist
         (compiled-stv->in-usersyms
          (processed-stv->compiled-stv pstv)))))

    ;; Construct the alist to evaluate with
    (time$ (stv-simvar-inputs-to-bits input-alist in-usersyms)
           :mintime 1/2
           :msg "; stv-run ev-alist: ~st sec, ~sa bytes.~%")))



(define stv-run
  :parents (symbolic-test-vectors)
  :short "Evaluate a symbolic test vector at particular, concrete inputs."

  ((pstv        processed-stv-p
                "The symbolic test vector to run.")

   (input-alist "An alist that should typically bind at least some of the input
                 simulation variables to natural numbers, or to the symbol X.
                 Any inputs that aren't mentioned are implicitly bound to X.")
   &key
   (skip        "Advanced option to avoid computing certain outputs; see below.")

   (quiet       "Suppress debugging output.  By default, @('stv-run') will print
                 certain debugging information.  This is generally convenient in
                 @(see def-gl-thm) forms involving an @('stv-run'), and will allow
                 you to see nicely-formatted debugging info when counter-examples
                 are found.  But you can use @(':quiet t') to suppress it."))

  :returns (out-alist "Alist binding user-level STV outputs to either natural
                       numbers or X.")

  :long "<p>Evaluating an stv basically involves three steps:</p>

<ol>

<li>We translate the @('input-alist') into bit-level bindings; see @(see
stv-simvar-inputs-to-bits).</li>

<li>Using these bit-level bindings, we evaluate the relevant output bits from
the processed STV, basically by calling @(see 4v-sexpr-eval) on each output
bit.</li>

<li>We take the evaluated output bits and merge them back into a user-level
alist that binds the output simulation variables to natural numbers or Xes; see
@(see stv-assemble-output-alist).</li>

</ol>

<p>The optional @('skip') argument may allow you to optimize this process,
especially in the context of @(see GL) proofs, when you don't care about the
values of certain output simulation variables.  For instance, suppose you have
a module that emits several flags in addition to its result, but you don't care
about the flags for some instructions.  Then, you can tell @('stv-run') to skip
computing the flags as you verify these instructions, which may lead to a big
savings when BDDs are involved.</p>"

  (time$
   (b* (((mv sigs out-usersyms)
         (stv-run-collect-eval-signals pstv skip))

        (- (or quiet
               (cw "STV Raw Inputs: ~x0.~%" input-alist)))

        (ev-alist (stv-run-make-eval-env pstv input-alist))

        ((with-fast ev-alist))

        ;; Evaluate the non-skipped signals.
        (evaled-out-bits
         (time$ (make-fast-alist (4v-sexpr-simp-and-eval-alist sigs ev-alist))
                :mintime 1/2
                :msg "; stv-run out-bits: ~st sec, ~sa bytes.~%"))

        (- (fast-alist-free ev-alist))

        ;; Assemble the non-skipped outputs.
        (assembled-outs
         (time$ (stv-assemble-output-alist evaled-out-bits out-usersyms)
                :mintime 1/2
                :msg "; stv-run outs: ~st sec, ~sa bytes.~%"))

        (- (fast-alist-free evaled-out-bits))

        ;; Debugging Support
        (- (or quiet
               (progn$ (cw "~%STV Inputs:~%")
                       (stv-print-alist input-alist)
                       (cw "~%STV Outputs:~%")
                       (stv-print-alist assembled-outs)
                       (cw "~%")))))

     assembled-outs)
   :msg "; stv-run: ~st sec, ~sa bytes.~%"
   :mintime 1))



(define stv-run-squash-dontcares
  :parents (symbolic-test-vectors)
  :short "Evaluate a symbolic test vector at particular, concrete inputs, and set all inputs and initial states that aren't bound to false."

  ((pstv        processed-stv-p
                "The symbolic test vector to run.")

   (input-alist "An alist that should typically bind at least some of the input
                 simulation variables to natural numbers, or to the symbol X.
                 Any inputs that aren't mentioned are implicitly bound to X.")
   &key
   (skip        "Advanced option to avoid computing certain outputs; see below.")

   (quiet       "Suppress debugging output.  By default, @('stv-run') will print
                 certain debugging information.  This is generally convenient in
                 @(see def-gl-thm) forms involving an @('stv-run'), and will allow
                 you to see nicely-formatted debugging info when counter-examples
                 are found.  But you can use @(':quiet t') to suppress it."))

  :returns (out-alist "Alist binding user-level STV outputs to either natural
                       numbers or X.")

  :long "<p>See @(see stv-run).  The only difference between @(see stv-run) and
this function is that this function uses @('4v-sexpr-eval-default') instead
of @(see 4v-sexpr-eval), which means that any variables not bound by the
user-provided inputs are set to false, instead of (effectively) X.</p>"


  (time$
   (b* (((mv sigs out-usersyms)
         (stv-run-collect-eval-signals pstv skip))

        (- (or quiet
               (cw "STV Raw Inputs: ~x0.~%" input-alist)))

        (ev-alist (stv-run-make-eval-env pstv input-alist))
        ((with-fast ev-alist))

        ;; Evaluate the non-skipped signals.
        (evaled-out-bits
         (time$ (make-fast-alist (4v-sexpr-eval-default-alist sigs ev-alist 'f))
                :mintime 1/2
                :msg "; stv-run out-bits: ~st sec, ~sa bytes.~%"))

        (- (fast-alist-free ev-alist))

        ;; Assemble the non-skipped outputs.
        (assembled-outs
         (time$ (stv-assemble-output-alist evaled-out-bits out-usersyms)
                :mintime 1/2
                :msg "; stv-run outs: ~st sec, ~sa bytes.~%"))

        (- (fast-alist-free evaled-out-bits))

        ;; Debugging Support
        (- (or quiet
               (progn$ (cw "~%STV Inputs:~%")
                       (stv-print-alist input-alist)
                       (cw "~%STV Outputs:~%")
                       (stv-print-alist assembled-outs)
                       (cw "~%")))))

     assembled-outs)
   :msg "; stv-run-squash-dontcares: ~st sec, ~sa bytes.~%"
   :mintime 1))


(define stv-run-check-dontcares
  :parents (symbolic-test-vectors)
  :short "Test that a given setting of the don't-care bits of an STV are indeed
don't-cares under the given input alist."

  ((pstv        processed-stv-p
                "The symbolic test vector to run.")

   (input-alist "An alist that should typically bind at least some of the input
                 simulation variables to natural numbers, or to the symbol X.
                 Any inputs that aren't mentioned are implicitly bound to X.")
   (dontcare-env "An alist that determines the setting of the don't-care inputs
                 to test.  This is fixed so that it binds variables only to T or F.")
   &key
   (skip        "Advanced option to avoid computing certain outputs; see below.")

   (quiet       "Suppress debugging output.  By default, @('stv-run') will print
                 certain debugging information.  This is generally convenient in
                 @(see def-gl-thm) forms involving an @('stv-run'), and will allow
                 you to see nicely-formatted debugging info when counter-examples
                 are found.  But you can use @(':quiet t') to suppress it."))

  :returns (out-alist "Alist binding user-level STV outputs to either natural
                       numbers or X.")

  :long "<p>Useful for cases where an STV output is X, this can be used to
prove a somewhat weaker theorem about a hardware module.  This function tests
that the evaluation of the non-skipped signals under the given input alist is
the same when:</p>
<ul>
<li>the s-expression variables not determined by the input alist are all set to
false, and</li>
<li>they are instead set according to the dontcare-env.</li>
</ul>
<p>It returns T if the two evaluations match and NIL if there is any difference.</p>

<p>If you prove (using GL) that this function always returns T under a given
input alist, you have shown that any Boolean setting of the initial states,
off-pipe inputs, etc., is irrelevant to the value produced under the given
input alist (which presumably includes settings for various control bits
specific to the instruction of interest).  You can then prove, say, that the
circuit meets its spec under a setting of all these don't-care bits to false,
and this then implies that the circuit meets its spec under every Boolean
setting of those bits.</p>"


  (time$
   (b* (((mv sigs ?out-usersyms)
         (stv-run-collect-eval-signals pstv skip))

        (- (or quiet
               (cw "STV Raw Inputs: ~x0.~%" input-alist)))

        (ev-alist (stv-run-make-eval-env pstv input-alist)))
     (4v-sexpr-alist-check-independent sigs ev-alist dontcare-env))
   :msg "; stv-run-check-dontcares: ~st sec, ~sa bytes.~%"
   :mintime 1)
  ///
  (defthm stv-run-check-dontcares-normalize-quiet
    (implies (syntaxp (not (equal quiet ''nil)))
             (equal (stv-run-check-dontcares pstv input-alist dontcare-env
                                             :skip skip :quiet quiet)
                    (stv-run-check-dontcares pstv input-alist dontcare-env
                                             :skip skip)))))

(defsection stv-run-independent-of-dontcares
  (defun-sk stv-run-independent-of-dontcares (pstv input-alist skip)
    (forall dontcare-env
            (stv-run-check-dontcares pstv input-alist dontcare-env :skip skip))
    :rewrite :direct)

  (in-theory (disable stv-run-independent-of-dontcares)))

(define stv-run-for-all-dontcares
  :parents (symbolic-test-vectors)
  :short "Test that a given setting of the don't-care bits of an STV are indeed
don't-cares under the given input alist."

  ((pstv        processed-stv-p
                "The symbolic test vector to run.")

   (input-alist "An alist that should typically bind at least some of the input
                 simulation variables to natural numbers, or to the symbol X.
                 Any inputs that aren't mentioned are implicitly bound to X.")
   &key
   (skip        "Advanced option to avoid computing certain outputs; see below.")

   (quiet       "Suppress debugging output.  By default, @('stv-run') will print
                 certain debugging information.  This is generally convenient in
                 @(see def-gl-thm) forms involving an @('stv-run'), and will allow
                 you to see nicely-formatted debugging info when counter-examples
                 are found.  But you can use @(':quiet t') to suppress it."))

  :returns (out-alist "Alist binding user-level STV outputs to either natural
                       numbers or X.")

  :long "<p>NOTE: This function is not always executable; read on for details.</p>

<p>This function evaluates an STV under the input alist, like @(see stv-run).
However, @(see stv-run) effectively binds to X all input and initial state
variables not set by the input alist (the don't-cares).  Thus, for each output,
@(see stv-run) produces either</p>

<ul>
<li>an integer giving the value of that output, signifying that the don't-cares
do not effect that output</li>
<li>an X, signifying that for some bit of that output, either the don't-cares
may effect the value, or the value is X independent of the don't-cares.</li>
</ul>

<p>This function instead produces:</p>
<ul>
<li>an integer giving the value of that output, signifying that the don't-cares
do not effect that output <em>as long as they are Boolean-valued</em></li>
<li>an X, signifying that for some bit of that output, either the don't-cares
may effect the value <em>even when they are restricted to Boolean values</em>,
or the value is X independent of the don't-cares.</li>
</ul>

<p>This function cannot always be straightforwardly computed: it may sometimes
require solving a SAT problem to show that all possible assignments of Boolean
values to the don't-care bits produce the same value of the outputs.  Rather
than calling a SAT solver in the midst of computing this function, we instead
compute the result when it is straightforward, and produce an error (by calling
a non-executable function) when it isn't.</p>

<p>Even when this function does not execute, it may be possible to prove that
its result (say) matches a spec function, by doing the following:</p>

<ul>
<li>Prove that the desired property holds of @(see stv-run-squash-dontcares)</li>
<li>Prove that @(see stv-run-check-dontcares) holds of the inputs to this
function, for all don't-care alists.</li>
</ul>
"


  (time$
   (b* (((mv sigs out-usersyms)
         (stv-run-collect-eval-signals pstv skip))

        (- (or quiet
               (cw "STV Raw Inputs: ~x0.~%" input-alist)))

        (ev-alist (stv-run-make-eval-env pstv input-alist))
        ((with-fast ev-alist))

        ;; Evaluate the non-skipped signals.
        (evaled-out-bits
         (time$ (make-fast-alist (4v-sexpr-boolconst-eval-alist sigs ev-alist))
                :mintime 1/2
                :msg "; stv-run out-bits: ~st sec, ~sa bytes.~%"))

        (- (fast-alist-free ev-alist))

        ;; Assemble the non-skipped outputs.
        (assembled-outs
         (time$ (stv-assemble-output-alist evaled-out-bits out-usersyms)
                :mintime 1/2
                :msg "; stv-run outs: ~st sec, ~sa bytes.~%"))

        (- (fast-alist-free evaled-out-bits))

        ;; Debugging Support
        (- (or quiet
               (progn$ (cw "~%STV Inputs:~%")
                       (stv-print-alist input-alist)
                       (cw "~%STV Outputs:~%")
                       (stv-print-alist assembled-outs)
                       (cw "~%")))))

     assembled-outs)
   :msg "; stv-run-for-all-dontcares: ~st sec, ~sa bytes.~%"
   :mintime 1)
  ///
  (defthm stv-run-for-all-dontcares-when-independent
    (implies (stv-run-independent-of-dontcares pstv input-alist skip)
             (equal (stv-run-for-all-dontcares pstv input-alist :skip skip :quiet quiet)
                    (stv-run-squash-dontcares pstv input-alist :skip skip :quiet quiet)))
    :hints(("Goal" :in-theory (e/d (stv-run-for-all-dontcares
                                    stv-run-squash-dontcares
                                    stv-run-check-dontcares)
                                   (stv-run-independent-of-dontcares-necc
                                    4v-sexpr-boolconst-eval-alist-when-independent))
            :use ((:instance stv-run-independent-of-dontcares-necc
                   (dontcare-env (4v-sexpr-boolconst-eval-alist-find-env-for-diff
                                  (mv-nth 0 (stv-run-collect-eval-signals pstv skip))
                                  (stv-run-make-eval-env pstv input-alist))))
                  (:instance 4v-sexpr-boolconst-eval-alist-when-independent
                   (x (mv-nth 0 (stv-run-collect-eval-signals pstv skip)))
                   (env (stv-run-make-eval-env pstv input-alist))))))))
