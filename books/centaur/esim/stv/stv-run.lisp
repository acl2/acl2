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


; stv-run.lisp -- main functions for running processed STVs
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "str/hexify" :dir :system)
(include-book "centaur/misc/vecs-ints" :dir :system)
(include-book "centaur/vl/util/defs" :dir :system)
(include-book "centaur/4v-sexpr/bitspecs" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-rewrites" :dir :system)
(include-book "centaur/gl/gl-util" :dir :system)
(local (include-book "centaur/vl/util/arithmetic" :dir :system))


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
                    (repeat *4vx* nvars))
                   ((and (natp val)
                         (< val (ash 1 nvars)))
                    (bool-to-4v-lst (int-to-v val nvars)))
                   (t
                    (progn$
                     (raise "Value ~x0 given for ~x1, but this value is not X ~
                             or in range for a ~x2-bit unsigned number."
                            val name nvars)
                     (repeat *4vx* nvars))))))

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
       (vals      (vl::look-up-each-fast bits bit-out-alist))
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
   (b* (((processed-stv pstv) pstv)
        ((compiled-stv cstv) pstv.compiled-stv)

        (- (or quiet
               (cw "STV Raw Inputs: ~x0.~%" input-alist)))

        (out-usersyms cstv.out-usersyms)
        (in-usersyms
         ;; These should already be a fast alist, but in case the object was
         ;; serialized and reloaded or something, we'll go ahead and try to
         ;; make them fast again.
         (make-fast-alist cstv.in-usersyms))

        ;; Start with all of the signals that we have in our STV.  These have
        ;; the expressions for the bits of the output simulation variables.
        (sigs        pstv.relevant-signals)

        ;; Prune away any signals that the user says he wants to skip.
        ((mv sigs out-usersyms)
         (time$ (b* (((unless skip)
                      (mv sigs out-usersyms))

                     ;; As a sanity check, complain if there are any bits
                     ;; that are being skipped that don't actually exist.
                     (skip     (sets::mergesort skip))
                     (outnames (sets::mergesort (alist-keys out-usersyms)))
                     ((unless (sets::subset skip outnames))
                      (b* ((bad  (sets::difference skip outnames))
                           ;; Don't use - or implicit progn$ on these, we want to make sure
                           ;; these get evaluated during GL runs.
                           (?msg (cw "Invalid skip!  Not outputs: ~&0." bad))
                           (?err (er hard? 'stv-run-fn "Invalid skip!  Not outputs: ~&0." bad)))
                        (mv sigs out-usersyms)))

                     ;; Filter the out-usersyms down to just those that we want.
                     (keep         (sets::difference outnames skip))
                     (out-usersyms (b* ((tmp (make-fal out-usersyms nil))
                                        (ret (fal-extract keep tmp)))
                                     (fast-alist-free tmp)
                                     ret))

                     ;; Also filter the sigs down to just the bits we need.
                     (keep-bits (vl::append-domains out-usersyms))
                     (sigs      (b* ((tmp (make-fal sigs nil))
                                     (ret (fal-extract keep-bits tmp)))
                                  (fast-alist-free tmp)
                                  ret)))

                  (mv sigs out-usersyms))
                :mintime 1/2
                :msg "; stv-run skips: ~st sec, ~sa bytes."))

        ;; Construct the alist to evaluate with
        (ev-alist
         (time$ (make-fast-alist
                 (stv-simvar-inputs-to-bits input-alist in-usersyms))
                :mintime 1/2
                :msg "; stv-run ev-alist: ~st sec, ~sa bytes.~%"))

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


