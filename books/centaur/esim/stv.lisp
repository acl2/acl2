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


; stv.lisp -- symbolic test vectors for esim
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-compile")
(include-book "esim-vcd")
(include-book "steps")
(include-book "centaur/misc/date" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "centaur/4v-sexpr/bitspecs" :dir :system)
(include-book "centaur/gl/gl-util" :dir :system)
(local (include-book "centaur/vl/util/arithmetic" :dir :system))

(defxdoc symbolic-test-vectors
  :parents (esim)
  :short "A concise way to describe, evaluate, and debug symbolic simulations
of E modules."

  :long "<p>A symbolic test vector is a description of a multi-phase @(see
esim) simulation.  It lets you say how the inputs should be set as the
simulation proceeds, and say when you would like the outputs and internal
signals to be sampled.</p>

<p>As a user, the main steps for using symbolic test vectors are:</p>

<ul>

<li>Use @(see defstv) to introduce the STV you want to run.  You basically
explain when you want to send in your inputs and when you want to sample the
outputs.</li>

<li>Use @(see stv-run) to run the STV on some particular inputs.  This is
intended to be compatible with @(see GL) proofs and can also be used in a
stand-alone way to get the outputs of the circuit.</li>

<li>Alternately, use @(see stv-debug) to run the STV on particular inputs and
also produce a waveform that can be inspected in a waveform viewer.  This is
intended for debugging only and cannot be embedded in proofs due to subtle
memoization issues.</li>

</ul>

<p>This interface is hopefully sufficient for most users.  But if you want to
understand more about how we process STVs, you can see @(see
stv-implementation-details).</p>")



(defxdoc symbolic-test-vector-format
  :parents (symbolic-test-vectors)
  :short "How to write a symbolic test vector."

  :long "<h3>Example Test Vector</h3>

<code>
 ;; phases:                0      1     2     3     4          5        6  ...
 ;; ---------------------------------------------------------------------------

 ((:inputs
   (\"clock\"               0      ~)
   (\"ibus[13:10]\"     #b101  #b101     _)
   (\"ibus[9:0]\"          op     op     _)
   (\"fwd\"                16     16     _)
   (\"a_bus\"               _      _    a1    a1    a2         a2        _)
   (\"b_bus\"               _      _     b     b     b          b        _)
   (\"reset\"               0)
   (\"fuse[0]\"             X))

  (:outputs
   (\"result_bus\"          _      _     _     _     _       res1     res2)
   (\"result_bus[63:32]\"   _      _     _     _     _    res-hi1  res-hi2)
   (\"result_bus[31:0]\"    _      _     _     _     _    res-lo1  res-lo2)
   )

  (:internals
   (\"queue0.mgr.fail\"     _      _     qf1   qf2   _))
  )
 ;; ---------------------------------------------------------------------------
</code>

<p>The <tt>:inputs</tt> section controls how the module's inputs will be set
over the course of the simulation.  For the above simulation,</p>

<ul>

<li><tt>clock</tt> starts low and then toggles throughout the simulation,</li>

<li><tt>ibus[13:10]</tt> is held to 5 (#b101) during the first full cycle, but
is not constrained afterward,</li>

<li><tt>ibus[9:0]</tt> is held to a certain value (call it <tt>op</tt>) during
the first full cycle, and is not constrained afterward,</li>

<li><tt>fwd</tt> is held constant at 16 during the first full cycle, but is
unconstrained afterward,</li>

<li><tt>a_bus</tt> is held at some particular value during the second full
cycle (call it <tt>a1</tt>), and at a (possibly different) value, <tt>a2</tt>
during the third cycle, but is unconstrained otherwise</li>

<li><tt>b_bus</tt> is held at the same value, call it <tt>b</tt>, for the full
second and third cycle, but is unconstrained otherwise,</li>

<li><tt>reset</tt> is kept off for the entire simulation,</li>

<li><tt>fuse[0]</tt> is explicitly set to <tt>X</tt> for the whole simulation.
This is similar to setting it to <tt>_</tt>, but is likely (1) more efficient
and (2) more likely to lead to false Xes in the outputs.</li>

<li>Any inputs to the module besides those specified above are implicitly
unconstrained (i.e., they are implicitly _) for the whole simulation.</li>

</ul>

<p>The <tt>:outputs</tt> section controls when the outputs should be sampled.
For this simulation:</p>

<ul>

<li>The full <tt>result_bus</tt> will be sampled twice.  Its results from
phases 5 and 6 will be called <tt>res1</tt> and <tt>res2</tt>,
respectively.</li>

<li>The high and low parts of the <tt>result_bus</tt> will also be sampled
during these cycles.  This probably seems redundant, but it can be useful in
cases where there is an X in only one side of the result bus.  This probably
won't make much sense until we talk about how to run symbolic test vectors,
below.</li>

</ul>

<p>The <tt>:internals</tt> section is similar to the outputs section, but it
allows you to pull out the values of internal signals in the module.</p>


<h3>Input Line Format</h3>

<p>Each line in the <tt>:inputs</tt> section explains how a certain input
should be driven over time.  Each line has the form:</p>

<code>
 (input-name     value1    value2   ...   valueN)
</code>

<p>The valid input names are:</p>

<ul>

<li>A string that names a particular input bus,</li>

<li>A string that is a Veriog-style bit- or part-select from a particular input
bus,</li>

<li>(Advanced) an explicit list of E input bits (which should usually be in
LSB-first order).  This isn't shown above, and is mainly intended for cases
where you are writing code to generate symbolic test vectors.</li>

</ul>

<p>The values explain how to set the bits of this input during the phases of
the simulation.  As a convenience, the last value on an input line is
implicitly repeated for the rest of the simulation.  What are the legal
values?</p>

<ul>

<li>A natural number can be used to set the input to a fixed value during this
particular phase.  The number supplied must be within <tt>[0, 2^n)</tt>, where
<tt>n</tt> is the size of the input, or an error will be caused.</li>

<li>The special <tt>~</tt> value is intended to support clock inputs, and
basically means <i>invert the previous value of this signal</i>.  Note that
this is only legitimate for one-bit inputs, and only when the previous value
expanded to <tt>0</tt> or <tt>1</tt>.  (In practice, this means the only things
that can occur before a <tt>~</tt> are <tt>0</tt>, <tt>1</tt>, or another
<tt>~</tt>.)</li>

<li>The special <tt>_</tt> value represents an unconstrained, four-valued
variable.  In general, you should use <tt>_</tt> during any phase where you
don't care about the value on this input.  There is no relationship between
separate underscores, e.g., in the example above, separate variables are used
for <tt>a_bus</tt> during the first and second phases.</li>

<li>The special <tt>:ONES</tt> value sets an input bus to all 1's, no matter
what its size.</li>

<li>Besides <tt>x</tt>, any other non-keyword symbols (like <tt>op</tt>,
<tt>a1</tt>, <tt>a2</tt>, and <tt>b</tt> above) are called <b>simulation
variables</b>.  A simulation variable lets you supply a particular value for
the input at this phase when you evaluate the symbolic test vector.</li>

<li>(Advanced) the special <tt>X</tt> value allows you to say that an input
should be explicitly set to X values.  It is similar to using <tt>_</tt>, but
supplies an explicit X value instead of fresh variables.  The advantage of this
is that it can be very efficient: X values often remain as X as they propagate
through gates, whereas free variables generally become larger expressions.  So,
using explicit Xes may lead to more efficient simulations by avoiding the
construction of lots of irrelevant expressions.  However, using explicit X
values can also lead to false Xes, e.g., whereas <tt>(AND A (NOT A))</tt> is
obviously 0, <tt>(AND X (NOT X))</tt> is <tt>X</tt>.  So, using Xes can lead to
overly conservative results.</li>

</ul>


<h3>Output Line Format</h3>

<p>Each line in the <tt>:outputs</tt> section controls when to sample certain
output signals.  The format is:</p>

<code>
 (output-name     value1    value2   ...   valueN)
</code>

<p>As with input-names, the output-names can be either (1) a string that names
a particular output bus, (2) a Verilog-style bit- or part-select, or (3) a list
of E output bits in LSB-first order.</p>

<p>But here the only legal values are:</p>

<ul>

<li><tt>_</tt>, which means don't sample the output at this time, or</li>

<li>a symbol, like <tt>res1</tt> or <tt>res2</tt> above, which gives a name to
the output at this time.  These names have to be unique, since outputs can vary
over time.</li>

</ul>

<p>To avoid any confusion between input and output lines, we don't allow you to
use <tt>~</tt>, <tt>X</tt>, or keyword symbols in output lines.</p>


<h3>Internals Line Format</h3>

<p>Except for their names, the lines in the <tt>:internals</tt> section are
essentially the same as lines in the <tt>:outputs</tt> section.  Generally
speaking we try to make the differences between outputs and internal signals as
invisible as possible.  For instance, it doesn't matter during @(see stv-run)
whether a signal is an internal or output signal.</p>

<p>The names on internal lines must be strings that are Verilog-style plain or
hierarchical identifiers using periods as separators.  They may optionally
include a Verilog-style bit- or part-select.</p>")




(defsection stv-implementation-details
  :parents (symbolic-test-vectors)
  :short "Overview of the basic flow for processing and running STVs."

  :long "<p>Here is a high-level overview of how we compile, process, and
evaluate STVs.  A picture of the flow is:</p>

<code>
 User-Level STV              ESIM Module
      |                           |
      |   ,-----------------------+
      |   |                       |
      v   v                       v
 Compiled STV            Fully General Sexprs
      |                           |
      |   ,-----------------------'
      |   |
      v   v
  Processed STV         Simulation Input Alist
      |                         |
      |   ,---------------------'
      |   |
      v   v
   stv-run/debug
        |    |
        |    +-------&gt; Waveform (VCD Dump)
        |    |
        v    v
  Simulation Output Alist
</code>


<p>Here, the user provides:</p>

<ul>

<li>The <b>User-Level STV</b>, which is a symbolic test vector written in the
@(see symbolic-test-vector-format),</li>

<li>The <b>ESIM Module</b> to simulate, which is generally produce by VL.</li>

<li>The <b>Simulation Input Alist</b>, which is an alist that should bind the
simulation variables of the symbolic test vector to concrete, natural-numbered
values.</li>

</ul>

<p>As a first step, we compile the STV; see @(see stv-compile).  This step
involves basic sanity checking and the computation of mappings that record what
inputs to provide to ESIM at each step of the simulation, what outputs to
extract after each phase, and how to translate between Esim bits and the
user-level input and output alists.  This compilation should generally be quite
fast (it's mostly involving the STV instead of the module), and it only needs
to be done once per STV.</p>

<p>Separately, we do a fully general symbolic simulation of the @(see esim)
module for as many phases are necessary to evaluate this STV; see @(see
stv-fully-general-simulation-run).  Symbolically simulating a module for many
steps can be very expensive.  On the other hand, this cost can be shared across
all STVs that target the same module, and it can even be at least partly shared
when the STV's require different numbers of phases.</p>

<p>Next, we create a Processed STV; see @(see stv-process).  This involves
pulling out the fully-general expressions for the signals we actually care
about (cheap) and specializing these expressions using the bindings from the
compiled STV (slightly expensive; basically @(see 4v-sexpr-restrict-with-rw) for
each signal in the user-outs).</p>

<p>We generally expect the Processed STV to be saved as a constant, via @(see
defconsts) since our use of @(see defattach) in @(see esim) prevents the sound
use of @(see defconst).  This will allow the same STV to be saved in a book and
reused for all evaluations of the STV.  In other words, we really expect to
only have to pay the price of processing an STV once.</p>

<p>Once the STV has been processed, we can run it with concrete values for the
input simulation variables; see @(see stv-run).  To do this, we basically need
to (1) translate the input numbers into bit-level bindings, (2) use @(see
sexpr-eval) to reduce the sexprs that are found in the Processed STV with the
bindings for their inputs, and (3) translate back from the resulting output-bit
bindings into numbers (or Xes) for the output alist.  This is about as cheap as
we know how to make it.</p>

<p>Of course, we may alternately want to run the STV and generate a waveform
for debugging; see @(see stv-debug).  But now there's a slight problem.  When
we compute the fully general sexprs, we omit internal signals because it gives
us a speed boost.  So, the processed STV doesn't contain the information we
would need to generate a waveform.</p>

<p>Well, basically we just do a new @(see esim) simulation that does include
the internal variables, and then run through the rest of the process again.  We
memoize things so that even though your first call of @(see stv-debug) is
expensive, subsequent calls will not need to redo the simulation or
specialization steps.</p>")



; -----------------------------------------------------------------------------
;
;                         FULLY GENERAL SIMULATIONS
;
; -----------------------------------------------------------------------------

(defsection stv-fully-general-st-alist
  :parents (stv-process)
  :short "@(call stv-fully-general-st-alist) generates a single alist that will
provide the values for the initial state of <tt>mod</tt> for a fully general
simulation."

  :long "<p>We basically just bind every state bit <tt>|foo|</tt> to
<tt>|foo.INIT|</tt>.  These names can't clash with each other, or with those
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
                (stv-suffix-symbols flat-sts ".INIT"))))

  (memoize 'stv-fully-general-st-alist))



(defsection stv-fully-general-in-alists
  :parents (stv-process)
  :short "@(call stv-fully-general-in-alists) generates <tt>n</tt> alists which
we will use as the inputs to <tt>mod</tt> to do an <tt>n</tt>-phase, fully
general simulation."

  :long "<p>This is basically name mangling.  For instance, at phase 5 the
input <tt>|foo[3]|</tt> will be represented by the variable
<tt>|foo[3].P5|</tt>.  There can't be any name clashes since we're adding a
such a suffix to every signal.</p>

<p>We memoize this to ensure that we'll get the same fully general alist across
different STVs that target the same module for the same numbers of steps.</p>"

  (defund stv-fully-general-in-alist-n (n flat-ins)
    (declare (xargs :guard (and (symbol-listp flat-ins)
                                (natp n))))
    (pairlis$ flat-ins
              (stv-suffix-symbols flat-ins (str::cat ".P" (str::natstr n)))))

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



(local
 (defsection basic-esim-lemmas

   (defthm true-list-listp-4v-sexpr-restrict-with-rw-alists
     (true-list-listp (4v-sexpr-restrict-with-rw-alists x al)))

   (defthm cons-listp-4v-sexpr-restrict-with-rw-alist
     (vl::cons-listp (4v-sexpr-restrict-with-rw-alist x al)))

   (defthm cons-list-listp-of-4v-sexpr-restrict-with-rw-alists
     (vl::cons-list-listp (4v-sexpr-restrict-with-rw-alists x al)))

   (defthm len-of-4v-sexpr-restrict-with-rw-alists
     (equal (len (4v-sexpr-restrict-with-rw-alists x al))
            (len x)))

   (local (in-theory (enable esim-sexpr-simp-new-probe-steps)))

   (defthm len-of-esim-sexpr-simp-new-probe-steps-0
     (equal (len (mv-nth 0 (esim-sexpr-simp-new-probe-steps mod ins st)))
            (len ins)))

   (defthm len-of-esim-sexpr-simp-new-probe-steps-1
     (equal (len (mv-nth 1 (esim-sexpr-simp-new-probe-steps mod ins st)))
            (len ins)))

   (defthm len-of-esim-sexpr-simp-new-probe-steps-2
     (equal (len (mv-nth 2 (esim-sexpr-simp-new-probe-steps mod ins st)))
            (len ins)))

   (defthm cons-listp-4v-sexpr-compose-with-rw-alist
     (vl::cons-listp (4v-sexpr-compose-with-rw-alist x al)))

   (defthm cons-listp-of-esim-sexpr-simp-nst
     (vl::cons-listp (esim-sexpr-simp-nst mod ins st))
     :hints(("Goal" :in-theory (enable esim-sexpr-simp-nst))))

   (defthm cons-listp-of-esim-sexpr-simp-out
     (vl::cons-listp (esim-sexpr-simp-out mod ins st))
     :hints(("Goal" :in-theory (enable esim-sexpr-simp-out))))

   (defthm cons-listp-of-esim-sexpr-simp-int
     (vl::cons-listp (esim-sexpr-simp-int mod ins st))
     :hints(("Goal" :in-theory (enable esim-sexpr-simp-int))))

   (defthm cons-listp-of-esim-sexpr-simp-new-probe-steps-0
     (vl::cons-list-listp (mv-nth 0 (esim-sexpr-simp-new-probe-steps mod ins st))))

   (defthm cons-listp-of-esim-sexpr-simp-new-probe-steps-1
     (vl::cons-list-listp (mv-nth 1 (esim-sexpr-simp-new-probe-steps mod ins st))))

   (defthm cons-listp-of-esim-sexpr-simp-new-probe-steps-2
     (vl::cons-list-listp (mv-nth 2 (esim-sexpr-simp-new-probe-steps mod ins st))))))



(defsection stv-fully-general-simulation-run
  :parents (stv-process)
  :short "Run an <tt>n</tt> step, fully general simulation of <tt>mod</tt>."

  :long "<p><b>Signature:</b> @(call stv-fully-general-simulation-run) returns
<tt>(mv init-st in-alists nst-alists out-alists NIL)</tt>.</p>

<p>The <tt>init-st</tt> and <tt>in-alists</tt> are just generated by @(see
stv-fully-general-st-alist) and @(see stv-fully-general-in-alists),
respectively, and are probably not very interesting.</p>

<p>The <tt>nst-alists</tt> and <tt>out-alists</tt> are each lists of <tt>n</tt>
alists, representing the fully-general next states and outputs after each
phase.  These alists bind signal names to @(see 4v-sexprs) that do not have any
assumptions about the values given to the module at each phase.</p>

<p>See also @(see stv-fully-general-simulation-debug), which produces the same
alists and also produces a list of fully general alists for the internal wires
of the modules.  The extra <tt>nil</tt> we return is for signature
compatibility with the <tt>-debug</tt> version.</p>

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



(defsection stv-fully-general-simulation-debug
  :parents (stv-debug)
  :short "Run an <tt>n</tt> step, fully general simulation of <tt>mod</tt> just
like @(see stv-fully-general-simulation-run), but also gather the fully general
expressions for internal signals."

  :long "<p><b>Signature:</b> @(call stv-fully-general-simulation-debug)
returns <tt>(mv init-st in-alists nst-alists out-alists int-alists)</tt>.</p>

<p>This is practically identical to @(see stv-fully-general-simulation-run),
except that it also gathers up and returns a list of <tt>int-alists</tt> which
contain the expressions for the internal signals of the module.</p>

<p>These expressions are useful for generating waveforms for debugging
simulations.  We could have just had @(see stv-fully-general-simulation-run)
always compute them, but computing the internal signals can be expensive so we
want to avoid it unless we're actually doing debugging.</p>

<p>Due to the structure of esim, we get a lot of memoized sharing between the
<tt>-run</tt> and <tt>-debug</tt> functions.  This works out very nicely, so
that it's not much more expensive to do a <tt>-debug</tt> after first doing a
<tt>-run</tt> than it is to just do a <tt>-debug</tt> from the beginning.</p>

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






; -----------------------------------------------------------------------------
;
;                        PROCESSING COMPILED STVS
;
; -----------------------------------------------------------------------------

(cutil::defaggregate processed-stv
  (mod                ;; module
   user-stv           ;; pre-compilation stv
   compiled-stv       ;; post-compilation stv
   relevant-signals   ;; (out/int sim var bit -> sexpr) alist
   )
  :tag :processed-stv
  :parents (stv-process)
  :short "Representation of a processed STV."
  :long "<p>You should probably read @(see stv-implementation-details) to
understand these fields.</p>

<ul>

<li>The <tt>mod</tt> is the @(see esim) module for this STV.  We save this in
the processed STV so that we re-simulate it later, if necessary, for @(see
stv-debug).</li>

<li>The <tt>user-stv</tt> is the user-level, pre-compiled STV.  We don't have
any particular need to keep this, but think it might possibly be useful in the
future.  For instance, Jared imagines eventually making a pretty-printer for
STVs so that they can be nicely referred to in documentation.</li>

<li>The <tt>compiled-stv</tt> is a @(see compiled-stv-p) and should be the
compiled version of the user's STV; see @(see stv-compile).</li>

<li>The <tt>relevant-signals</tt> is an alist computed by @(see stv-process)
that maps each the bits for each internal/output simulation variable to
already-restricted @(see 4v-sexprs).  That is, these s-expressions are
generally in terms of the input simulation variable bits, and ready to be
evaluated by @(see stv-run).</li>

</ul>"

; Historically we could optionally pre-compute snapshots for debugging, but we
; took that out because it could make stv-run a lot slower during GL proofs,
; because the snapshots were huge, and GL has to make sure the whole STV is
; free of special GL keywords with its gl-concrete-lite check.

  :require ((compiled-stv-p-of-processed-stv->compiled-stv
             (compiled-stv-p compiled-stv))))



(defsection stv-extract-relevant-signals
  :parents (stv-process)
  :short "Pull out the fully general expressions for the signals that we care
about, and bind them to the bit names of the simulation variables."

  :long "<p>@(call stv-extract-relevant-signals) is given:</p>

<ul>

<li><tt>extract-alists</tt>, the @(see stv-extraction-alists) we obtained from
@(see stv-compile),</li>

<li><tt>out-alists</tt>, the list of output alists we got from the fully general
simulation (e.g., from @(see stv-fully-general-simulation-run)), and</li>

<li><tt>acc</tt>, an accumulator to extend which should initially be nil.</li>

</ul>

<p>We walk down the <tt>extract-alists</tt> and <tt>out-alists</tt> together,
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

<p>The <tt>stv</tt> should be a valid symbolic test vector, written in the
@(see symbolic-test-vector-format).</p>

<p>The <tt>mod</tt> is the @(see esim) module that the <tt>stv</tt> is being
written for.</p>

<p>An STV must be processed before it can be run with @(see stv-run).  This
processing can be expensive and involves several steps.  The <tt>stv</tt>
itself is checked for well-formedness and is syntactically simplified.  The
<tt>mod</tt> is symbolically simulated using a fully-general multi-phase @(see
esim) simulation.  The relevant outputs are then extracted from this simulation
and specialized as suggested by this particular <tt>stv</tt>.  These restricted
outputs and other information is then saved into a @(see processed-stv-p)
object that can be given to @(see stv-run) or @(see stv-debug).</p>

<p>Note that there are many chances for memoization, e.g., if you have a lot of
different symbolic test vectors that all target the same module, they can reuse
the same @(see esim) simulation, so processing the first STV may be very
expensive but processing subsequent STVs can be much cheaper.</p>

<p>Since processing STVs is expensive, we generally recommend saving the result
of processing the STV using @(see defconsts).  You can't use an ordinary
<tt>defconst</tt> because of subtle issues having to do with memoization and
@(see defattach).</p>"

  (defund stv-process-fn (stv mod)
    (declare (xargs :guard (good-esim-modulep mod)))
    (b* ((cstv (time$ (stv-compile stv mod)
                      :msg "; stv-process compilation: ~st sec, ~sa bytes~%"
                      :mintime 1/2))

         ((unless cstv)
          ;; We shouldn't really hit this case because stv-compile should cause
          ;; an ER on any failure.  But, logically we'll say that if
          ;; stv-compile fails, we just fail, too.
          (er hard? 'stv-process "STV Compilation Failed!"))

         ((compiled-stv cstv) cstv)

         (nphases (nfix cstv.nphases))
         ((unless (posp nphases))
          (er hard? 'stv-process "STV has no phases?"))

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
              (time$ (stv-fully-general-simulation-debug nphases mod)
                     :msg "; stv-process debug simulation: ~st sec, ~sa bytes.~%"
                     :mintime 1/2)
            (time$ (stv-fully-general-simulation-run nphases mod)
                   :msg "; stv-process simulation: ~st sec, ~sa bytes.~%"
                   :mintime 1/2)))


         (relevant-signals-general
          ;; The out-alists-general and int-alists-general bind names to sexprs
          ;; based on the fully general inputs.  But we probably don't care
          ;; about the vast majority of these names -- we usually only care
          ;; about a few outputs at certain stages!  So, now pull out only the
          ;; signals we actually care about.  This seems like a good place to
          ;; stop distinguishing between internal and output signals.  From the
          ;; perspective of the STV user, the simulation vars can be treated
          ;; the same.
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

  (defmacro stv-process (stv mod)
    `(stv-process-fn ,stv ,mod))

  (local (in-theory (enable stv-process-fn)))

  (defthm processed-stv-p-of-stv-process
    (equal (processed-stv-p (stv-process-fn stv mod))
           (if (stv-process-fn stv mod)
               t
             nil))))


(defsection stv-make-snapshots

  (defund stv-combine-into-snapshots (in-alists out-alists int-alists)
    (declare (xargs :guard (and (vl::same-lengthp in-alists out-alists)
                                (vl::same-lengthp in-alists int-alists)
                                (true-list-listp in-alists)
                                (true-list-listp out-alists)
                                (true-list-listp int-alists))))
    (if (atom in-alists)
        nil
      (let ((snapshot1 (append (car in-alists)
                               (car out-alists)
                               (car int-alists))))
        (cons snapshot1 (stv-combine-into-snapshots (cdr in-alists)
                                                    (cdr out-alists)
                                                    (cdr int-alists))))))

  (local (defthm c0
           (implies (and (vl::cons-list-listp in-alists)
                         (vl::cons-list-listp out-alists)
                         (vl::cons-list-listp int-alists))
                    (vl::cons-list-listp
                     (stv-combine-into-snapshots in-alists out-alists int-alists)))
           :hints(("Goal" :in-theory (enable stv-combine-into-snapshots)))))

  (defund stv-make-snapshots (pstv)
    (declare (xargs :guard (processed-stv-p pstv)))
    (b* (((processed-stv pstv) pstv)

         ((compiled-stv cstv) pstv.compiled-stv)
         (nphases (nfix cstv.nphases))
         ((unless (posp nphases))
          (er hard? 'stv-process "STV has no phases?"))

         ((mv ?init-st-general
              in-alists-general
              ?nst-alists-general
              out-alists-general
              int-alists-general)
          (time$ (stv-fully-general-simulation-debug nphases pstv.mod)
                 :msg "; stv debug simulation: ~st sec, ~sa bytes.~%"
                 :mintime 1/2))

         (snapshots
          (time$ (stv-combine-into-snapshots
                  (4v-sexpr-restrict-with-rw-alists in-alists-general cstv.restrict-alist)
                  (4v-sexpr-restrict-with-rw-alists out-alists-general cstv.restrict-alist)
                  (4v-sexpr-restrict-with-rw-alists int-alists-general cstv.restrict-alist))
                 :msg "; stv-debug general snapshots: ~st sec, ~sa bytes.~%"
                 :mintime 1/2)))
      snapshots))

  (memoize 'stv-make-snapshots :aokp t)

  (defthm cons-list-listp-of-stv-make-snapshots
    (vl::cons-list-listp (stv-make-snapshots pstv))
    :hints(("Goal" :in-theory (enable stv-make-snapshots)))))




; -----------------------------------------------------------------------------
;
;                           RUNNING PROCESSED STVS
;
; -----------------------------------------------------------------------------

(defsection stv-simvar-inputs-to-bits
  :parents (stv-run)
  :short "Convert the user-level input alist (which binds simulation variables
to naturals) into a bit-level alist for @(see 4v-sexpr-eval)."

  :long "<p>@(call stv-simvar-inputs-to-bits) is given:</p>

<ul>

<li><tt>user-alist</tt>, the alist provided by the user that gives values to
the input simulation variables.  Each value should be a natural number that is
in the range for that simulation variable.</li>

<li><tt>in-usersyms</tt>, a fast alist that binds each input simulation
variable for the STV with a list of variables that represent its bits; see
@(see stv-compile), but in particular see the <tt>usersyms</tt> output of @(see
stv-expand-input-entry).</li>

</ul>

<p>We try to translate every user-level binding, like <tt>(opcode . 7)</tt>,
into a set of bit-level bindings, say something like:</p>

<code>
  ((opcode[0] . *4vt*)
   (opcode[1] . *4vt*)
   (opcode[2] . *4vt*)
   (opcode[3] . *4vf*)
   ...)
</code>

<p>For each input simulation variable bound in the user-level alist, we
basically just need to look up the names of its bits in the
<tt>in-usersyms</tt> alist, explode the value into @(see 4vp) bits, and then
pairing up the bit names with the values.  In the process, we do some basic
sanity checking to make sure that the names being bound exist and that the
provided values are in range.</p>

<p>The net result is a new alist that is suitable for @(see 4v-sexpr-eval) that
we can use to evaluate output expressions.</p>

<p>We don't check for duplicates in the user-alist, and if there are duplicates
it could lead to duplicate bindings in our resulting bit-level alist.  However,
the alist semantics are preserved because shadowed bindings are still shadowed
in the bit-level alist.</p>"

  (defund stv-simvar-inputs-to-bits (user-alist in-usersyms)
    (declare (xargs :guard t))
    (b* (((when (atom user-alist))
          nil)

         (rest  (stv-simvar-inputs-to-bits (cdr user-alist) in-usersyms))

         ((when (atom (car user-alist)))
          ;; Bad alist convention
          (cw "stv-simvar-inputs-to-bits: skipping malformed alist entry
               ~x0.~%" (car user-alist))
          rest)

         (name (caar user-alist))
         (val  (cdar user-alist))
         (look (hons-get name in-usersyms))

         ((unless look)
          (er hard? 'stv-simvar-inputs-to-bits
              "Value given for ~x0, but this is not a simulation variable."
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
                       (er hard? 'stv-simvar-inputs-to-bits
                           "Value ~x0 given for ~x1, but this value is not X ~
                           or in range for a ~x2-bit unsigned number."
                           val name nvars)
                       (repeat *4vx* nvars))))))

      (safe-pairlis-onto-acc vars vals rest))))



(defsection stv-assemble-output-alist
  :parents (stv-run)
  :short "Convert the bit-level bindings from after @(see 4v-sexpr-eval) into
user-level bindings of the output simulation variables to naturals or X."

  :long "<p>@(call stv-assemble-output-alist) is given:</p>

<ul>

<li><tt>bit-out-alist</tt>, a fast alist that binds the output simulation
variable bit names to their @(see 4vp) constants.  This alist should have been
produced by calling @(see 4v-sexpr-eval) on the <tt>relevant-signals</tt>
s-expressions of a @(see processed-stv-p).</li>

<li><tt>out-usersyms</tt>, an alist that binds each output simulation variable
for the STV with a list of variables that represent its bits; see @(see
stv-compile), but in particular see the <tt>usersyms</tt> output of @(see
stv-expand-output-entry).</li>

</ul>

<p>We recur down <tt>out-usersyms</tt>.  For each output variable, we look up
the values of its bits in <tt>bit-out-alist</tt>, and then try to combine these
bits into a single integer value.  If any bit is X, we just say the whole
output is X.</p>"

  (defund stv-assemble-output-alist (bit-out-alist out-usersyms)
    (declare (xargs :guard t))
    (b* (((when (atom out-usersyms))
          nil)
         (rest (stv-assemble-output-alist bit-out-alist (cdr out-usersyms)))
         ((when (atom (car out-usersyms)))
          (er hard? 'stv-assemble-output-alist "out-usersyms should be an alist.")
          rest)
         ((cons user-name bits) (car out-usersyms))
         (vals      (vl::look-up-each-fast bits bit-out-alist))
         (true-val  (4v-to-nat vals)))
      (cons (cons user-name true-val) rest))))





(defun insert-underscores (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         x)
        ((equal (mod (len x) 4) 0)
         (list* #\_ (car x) (insert-underscores (cdr x))))
        (t
         (list* (car x) (insert-underscores (cdr x))))))

(defthm character-listp-of-insert-underscores
  (implies (force (character-listp x))
           (character-listp (insert-underscores x))))

(defun hexify (x)
  ;; Dumb printing utility.  X can be a natural number or the symbol 'X.  We
  ;; turn it into a hexadecimal string.  Such a string can be printed with ~s0
  ;; or similar in calls of cw.
  (declare (xargs :guard t
                  :guard-debug t))
  (cond ((natp x)
         (b* ((chars (explode-atom x 16)) ;; looks like #xBEEF...
              ((unless (and (equal (take 2 chars) '(#\# #\x))
                            (characterp (third chars))))
               (er hard? 'hexify "explode-atom is broken"))
              (nice-chars (list* #\# #\x (third chars)
                                 (insert-underscores (nthcdr 3 chars)))))
           (coerce nice-chars 'string)))
        ((equal x 'x)
         "X")
        ((not x)
         ;; Jared: extending this to allow NIL since it's just a printing
         ;; utility and this is convenient sometimes in the IU stuff, where
         ;; a particular signal might not be bound in an input alist.
         "NIL")
        (t
         (prog2$ (er hard? 'hexify "Unexpected argument ~x0.~%" x)
                 ""))))

(defun stv-print-alist (x)
  ;; Dumb printing utility.  X is expected to be an alist binding symbols to
  ;; values.  We print them out hexified and indented in a nice way.
  (declare (xargs :guard t))
  (b* (((when (atom x))
        nil)
       ((unless (consp (car x)))
        (er hard? 'stv-print-alist
            "Malformed alist: Entry ~x0 is not a (key . val) pair.~%"
            (car x)))
       ((cons key val) (car x))
       ((unless (symbolp key))
        (er hard? 'stv-print-alist
            "Malformed alist: name is not a symbolp.~%"
            (car x)))
       (- (cw "  ~s0:~t1~s2~%" key 20 (hexify val))))
    (stv-print-alist (cdr x))))



(defsection stv-run
  :parents (symbolic-test-vectors)
  :short "Evaluate a symbolic test vector at particular, concrete inputs."

  :long "<p><b>Signature:</b> @(call stv-run) returns an alist that binds
user-level outputs to natural numbers or X.</p>

<p>The basic form of <tt>stv-run</tt> only requires two inputs:</p>

<ul>

<li>The <tt>pstv</tt> is an @(see processed-stv-p) that should have been
produced by @(see stv-process).</li>

<li>The <tt>input-alist</tt> is an alist that should bind some of the input
simulation variables to natural numbers, or to the symbol X.  Any inputs that
aren't mentioned are implicitly bound to X.</li>

</ul>

<p>And in this case, the evaluation basically involves three steps:</p>

<ol>

<li>We translate the <tt>input-alist</tt> into bit-level bindings; see @(see
stv-simvar-inputs-to-bits).</li>

<li>We evaluate the relevant output bits from the processed STV, using these
bit-level bindings, basically by calling @(see 4v-sexpr-eval) on each output
bit.</li>

<li>We take the evaluated output bits and merge them back into an alist that
binds the output simulation variables to natural numbers or Xes; see @(see
stv-assemble-output-alist).</li>

</ol>

<p>The optional <tt>skip</tt> argument may allow you to optimize this process,
especially in the context of @(see GL) proofs, when you don't care about the
values of certain output simulation variables.  For instance, suppose you have
a module that emits several flags in addition to its result, but you don't care
about the flags for some instructions.  Then, you can tell <tt>stv-run</tt> to
skip computing the flags as you verify these instructions, which may lead to a
big savings when BDDs are involved.</p>

<p>By default, <tt>stv-run</tt> will print certain debugging information.  This
is generally convenient in @(see def-gl-thm) forms involving an
<tt>stv-run</tt>, and will allow you to see nicely-formatted debugging info
when counter-examples are found.  You can suppress this output with <tt>:quiet
nil</tt>.</p>"

  (defund stv-run-fn (pstv input-alist skip quiet)
    (declare (xargs :guard (processed-stv-p pstv)))
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
           (time$ (make-fast-alist (4v-sexpr-eval-alist sigs ev-alist))
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

  (defmacro stv-run (pstv input-alist &key skip quiet)
    `(stv-run-fn ,pstv ,input-alist ,skip ,quiet)))




; -----------------------------------------------------------------------------
;
;                         DEBUGGING PROCESSED STVS
;
; -----------------------------------------------------------------------------

(defttag writes-okp)
(remove-untouchable acl2::writes-okp nil)


(defsection stv-debug
  :parents (symbolic-test-vectors)
  :short "Evaluate a symbolic test vector at particular, concrete inputs, and
generate a waveform."

  :long "<p>This macro is an extended version of @(see stv-run).  In addition
to building an alist of the output simulation variables, it also writes out a
waveform that can be viewed in a VCD viewer.  Note that debugging can be slow,
especially the first time before things are memoized.</p>"

  (defun stv-debug-fn (pstv input-alist filename viewer state)
    "Returns (MV OUT-ALIST STATE)"
    (declare (xargs :guard (processed-stv-p pstv)
                    :stobjs state
                    :mode :program))
    (time$
     (b* (((processed-stv pstv) pstv)
          ((compiled-stv cstv) pstv.compiled-stv)

          (snapshots
           (time$ (stv-make-snapshots pstv)
                  :mintime 1/2
                  :msg "; stv-debug snapshots: ~st sec, ~sa bytes.~%"))

          (in-usersyms
           ;; These should already be a fast alist, but in case the object was
           ;; serialized and reloaded or something, we'll go ahead and try to
           ;; make them fast again.
           (make-fast-alist cstv.in-usersyms))

          (ev-alist
           (time$ (make-fast-alist
                   (stv-simvar-inputs-to-bits input-alist in-usersyms))
                  :mintime 1/2
                  :msg "; stv-debug ev-alist: ~st sec, ~sa bytes.~%"))

          (evaled-out-bits
           (time$ (make-fast-alist
                   (4v-sexpr-eval-alist pstv.relevant-signals ev-alist))
                  :mintime 1/2
                  :msg "; stv-debug evaluating sexprs: ~st sec, ~sa bytes.~%"))

          (evaled-snapshots
           (time$ (4v-sexpr-eval-alists snapshots ev-alist)
                  :mintime 1/2
                  :msg "; stv-debug evaluating snapshots: ~st sec, ~sa bytes.~%"))

          (- (fast-alist-free ev-alist))

          (assembled-outs
           (time$ (stv-assemble-output-alist evaled-out-bits cstv.out-usersyms)
                  :mintime 1/2
                  :msg "; stv-debug assembling outs: ~st sec, ~sa bytes.~%"))

          (- (fast-alist-free evaled-out-bits))

          ;; Actual VCD generation
          ((mv date state) (acl2::date state))
          (dump (vl::vcd-dump-main pstv.mod evaled-snapshots date))

          ((mv & & state) (assign acl2::writes-okp t))
          (state (time$ (vl::with-ps-file filename
                           (vl::vl-ps-update-rchars dump))
                        :mintime 1/2
                        :msg "; vcd-dump file generation: ~st seconds, ~sa bytes.~%"))

          ;; Maybe launch a VCD viewer, but not if we're certifying books
          (certifying-book-p (acl2::f-get-global 'acl2::certify-book-info state))

          ;; BOZO we aren't really escaping filenames right or anything like that
          (- (if (and viewer (not certifying-book-p))
                 (b* ((cmd (str::cat viewer " " filename)))
                   (cw "; vcd-dump launching \"~s0\".~%" cmd)
                   (acl2::tshell-ensure)
                   (acl2::tshell-run-background cmd))
               nil)))

       (mv assembled-outs state))
     :msg "; stv-debug: ~st sec, ~sa bytes.~%"
     :mintime 1))

  (defmacro stv-debug (pstv input-alist
                            &key
                            (filename '"stv.debug")
                            (viewer   '"gtkwave"))
    `(stv-debug-fn ,pstv ,input-alist ,filename ,viewer state)))




; -----------------------------------------------------------------------------
;
;                         DOCUMENTATION GENERATION
;
; -----------------------------------------------------------------------------

(defund stv-name-bits-to-xml (bits col acc)
  (declare (xargs :guard (and (symbol-listp bits)
                              (natp col))))
  (b* (((when (atom bits))
        acc)
       ;; Print the name of this bit
       (name1 (symbol-name (car bits)))
       ((mv col acc)
        (vl::vl-html-encode-string-aux name1 0 (length name1) col 8 acc))
       ;; Print ", " if there are more bits.
       ((mv col acc)
        (if (atom (cdr bits))
            (mv col acc)
          (mv (+ col 2) (list* #\Space #\, acc)))))
    ;; Print the rest of the bit names.
    (stv-name-bits-to-xml (cdr bits) col acc)))

(defthm character-listp-of-stv-name-bits-to-xml
  (implies (and (character-listp acc)
                (symbol-listp bits)
                (natp col))
           (character-listp (stv-name-bits-to-xml bits col acc)))
  :hints(("Goal" :in-theory (enable stv-name-bits-to-xml))))

(defund stv-name-to-xml (name acc)
  (declare (xargs :guard t))
  (cond ((stringp name)
         ;; It already looks like a Verilog name, so this is easy enough.
         (b* (((mv ?col acc)
               (vl::vl-html-encode-string-aux name 0 (length name) 0 8 acc)))
           acc))
        ((symbol-listp name)
         (b* ((acc (cons #\{ acc))
              (acc (stv-name-bits-to-xml name 1 acc))
              (acc (cons #\} acc)))
           acc))
        (t
         (er hard? 'stv-name-to-xml "Bad name for stv line: ~x0." name))))

(defthm character-listp-of-stv-name-to-xml
  (implies (character-listp acc)
           (character-listp (stv-name-to-xml name acc)))
  :hints(("Goal" :in-theory (enable stv-name-to-xml))))

(defund stv-entry-to-xml (entry expansion acc)
  (declare (xargs :guard t))
  (cond ((natp entry)
         (if (< entry 10)
             ;; As a special nicety, write values under 10 without any
             ;; leading prefixes.
             (revappend (str::natchars entry) acc)
           ;; For any larger constants, write them in hex.  I'll use a 0x
           ;; prefix instead of a #x prefix, since it's probably more widely
           ;; understood.
           (let* ((pound-x-hex-digits (explode-atom entry 16))              ;; #x1000
                  (zero-x-hex-digits  (cons #\0 (cdr pound-x-hex-digits)))) ;; 0x1000
             (revappend zero-x-hex-digits acc))))

        ((eq entry 'x)
         (cons #\X acc))

        ((eq entry :ones)
         ;; BOZO maybe want to take the width and expand this out into the
         ;; actual constant we're using?
         (str::revappend-chars "<i>ones</i>" acc))

        ((eq entry '~)
         (cond ((equal expansion (list *4vt-sexpr*))
                (cons #\1 acc))
               ((equal expansion (list *4vf-sexpr*))
                (cons #\0 acc))
               (t
                (progn$ (er hard? 'stv-entry-to-xml "Expansion of ~ should be 1 or 0.")
                        acc))))

        ((eq entry '_)
         ;; Just skipping these seems nicest.
         acc)

        ((symbolp entry)
         (b* ((acc (str::revappend-chars "<b>" acc))
              ((mv ?col acc)
               (vl::vl-html-encode-string-aux (symbol-name entry) 0
                                              (length (symbol-name entry))
                                              0 8 acc))
              (acc (str::revappend-chars "</b>" acc)))
           acc))

        (t
         (er hard? 'stv-entry-to-xml
             "Bad entry in stv line: ~x0." entry))))

(defthm character-listp-of-stv-entry-to-xml
  (implies (character-listp acc)
           (character-listp (stv-entry-to-xml entry expansion acc)))
  :hints(("Goal" :in-theory (enable stv-entry-to-xml))))

(defund stv-entries-to-xml (entries expansions acc)
  (declare (xargs :guard (true-listp expansions)))
  (b* (((when (atom entries))
        acc)
       (acc (str::revappend-chars "<stv_entry>" acc))
       (acc (stv-entry-to-xml (car entries) (car expansions) acc))
       (acc (str::revappend-chars "</stv_entry>" acc)))
    (stv-entries-to-xml (cdr entries) (cdr expansions) acc)))

(defthm character-listp-of-stv-entries-to-xml
  (implies (character-listp acc)
           (character-listp (stv-entries-to-xml entries expansions acc)))
  :hints(("Goal" :in-theory (enable stv-entries-to-xml))))

(defund stv-line-to-xml (line expansion acc)
  (declare (xargs :guard (and (true-listp line)
                              (true-listp expansion))))
  (b* ((acc (str::revappend-chars "<stv_line>" acc))
       (acc (str::revappend-chars "<stv_name>" acc))
       (acc (stv-name-to-xml (car line) acc))
       (acc (str::revappend-chars "</stv_name>" acc))
       (acc (stv-entries-to-xml (cdr line) (cdr expansion) acc))
       (acc (str::revappend-chars "</stv_line>" acc))
       (acc (cons #\Newline acc)))
    acc))

(defthm character-listp-of-stv-line-to-xml
  (implies (character-listp acc)
           (character-listp (stv-line-to-xml line expansion acc)))
  :hints(("Goal" :in-theory (enable stv-line-to-xml))))

(defund stv-lines-to-xml (lines expansions acc)
  (declare (xargs :guard (and (true-list-listp lines)
                              (true-list-listp expansions))))
  (b* (((when (atom lines))
        acc)
       (acc (stv-line-to-xml (car lines) (car expansions) acc)))
    (stv-lines-to-xml (cdr lines) (cdr expansions) acc)))

(defthm character-listp-of-stv-lines-to-xml
  (implies (character-listp acc)
           (character-listp (stv-lines-to-xml lines expansions acc)))
  :hints(("Goal" :in-theory (enable stv-lines-to-xml))))


(defund stv-labels-to-xml (labels acc)
  (declare (xargs :guard (symbol-listp labels)))
  (b* (((when (atom labels))
        acc)
       (acc (str::revappend-chars "<stv_label>" acc))
       (acc (if (car labels)
                (str::revappend-chars (symbol-name (car labels)) acc)
              acc))
       (acc (str::revappend-chars "</stv_label>" acc)))
    (stv-labels-to-xml (cdr labels) acc)))

(defthm character-listp-of-stv-labels-to-xml
  (implies (character-listp acc)
           (character-listp (stv-labels-to-xml labels acc)))
  :hints(("Goal" :in-theory (enable stv-labels-to-xml))))


(defund stv-to-xml (stv cstv labels)
  (declare (xargs :guard t
                  :guard-hints(("Goal" :in-theory (enable basic-stv-p
                                                          stv-widen)))))
  (b* (((unless (basic-stv-p stv))
        (er hard? 'stv-to-xml "stv does not even satisfy basic-stv-p."))
       ((unless (compiled-stv-p cstv))
        (er hard? 'stv-to-xml "compiled stv does not even satisfy compiled-stv-p."))
       ((unless (symbol-listp labels))
        (er hard? 'stv-to-xml "labels are not a symbol-listp."))

       ;; Widen all the lines so the table will be filled.
       (stv        (stv-widen stv))
       (inputs     (cdr (hons-assoc-equal :inputs stv)))
       (outputs    (cdr (hons-assoc-equal :outputs stv)))
       (internals  (cdr (hons-assoc-equal :internals stv)))

       ;; Expand the input lines to resolve ~s.  We don't need to expand the
       ;; output or internal lines.
       (ex-ins    (compiled-stv->expanded-ins cstv))
       ((unless (true-list-listp ex-ins))
        (er hard? 'stv-to-xml "Expanded inputs aren't a true-list-listp?"))

       (acc nil)
       (acc (str::revappend-chars "<stv>" acc))
       (acc (if labels
                (b* ((acc (str::revappend-chars "<stv_labels>" acc))
                     ;; Initial empty label for above the signals list.
                     (acc (str::revappend-chars "<stv_label></stv_label>" acc))
                     (acc (stv-labels-to-xml labels acc))
                     (acc (str::revappend-chars "</stv_labels>" acc)))
                  acc)
              acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "<stv_inputs>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml inputs ex-ins acc))
       (acc (str::revappend-chars "</stv_inputs>" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "<stv_outputs>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml outputs nil acc))
       (acc (stv-lines-to-xml internals nil acc))
       (acc (str::revappend-chars "</stv_outputs>" acc))
       (acc (cons #\Newline acc))
       (acc (str::revappend-chars "</stv>" acc)))
    (reverse (coerce acc 'string))))

(defthm stringp-of-stv-to-xml
  (or (stringp (stv-to-xml stv expansion labels))
      (not (stv-to-xml stv expansion labels)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable stv-to-xml))))




; -----------------------------------------------------------------------------
;
;                                 DEFSTV
;
; -----------------------------------------------------------------------------

(defsection defstv
  :parents (symbolic-test-vectors)
  :short "Introduce a symbolic test vector as a constant."
  :long "<p>Example:</p>

<code>
 (defstv *foo*
   :mod *my-module*
   :inputs '((\"opcode\" _ _ op _)
             ...)
   :outputs '((\"result\" _ _ _ _ res _)
              ...)
   :debug t
   :labels '(A nil B nil C nil)
   :parents ...
1   :short ...
   :long ...)
</code>

<p>The <tt>defstv</tt> command is a high-level interface that allows you to
introduce a symbolic test vector for a module as a constant.  It sets up the
vector for use with @(see stv-run) or @(see stv-debug), and also (optionally)
generates @(see xdoc) documentation with a pretty table describing the
simulation.</p>

<h4>Required Arguments</h4>

<ul>

<li><tt>:mod</tt> should be the @(see esim) module you want to simulate.</li>

<li><tt>:inputs</tt> and <tt>:outputs</tt> control how the module will be
simulated; see @(see symbolic-test-vector-format) to understand how to write
them.</li>

</ul>

<h4>Optional Arguments</h4>

<ul>

<li><tt>:parents</tt>, <tt>:short</tt>, and <tt>:long</tt> are as in @(see
defxdoc).  If any of these options is given, documentation will be generated,
including a fancy table that shows the simulation.</li>

<li><tt>:labels</tt> are only used for documentation, and if provided must be a
symbol list.  These symbols will only be used to label the stages of the
simulation, with <tt>nil</tt> leaving a blank.  This can be useful to make the
documentation reflect the names of pipe stages, etc.</li>

</ul>

<p>Note that <tt>defstv</tt> isn't very elaborate, and if you don't want to
define a constant for each STV you are using, you might use @(see stv-process)
directly, instead.</p>"

;; <li><tt>:debug t</tt> says to pre-generate debugging information.  This will
;; make the <tt>defstv</tt> command slower, but will speed up the first subsequent
;; use of @(see stv-debug).</li>

  (defun defstv-fn (name mod-const-name ;; e.g., *mmx*
                         mod            ;; e.g., the value of *mmx*
                         inputs outputs internals labels parents short long)
    (declare (xargs :guard (and (symbolp name)
                                (symbolp mod-const-name)
                                (good-esim-modulep mod))))
    (b* ((mod         (or mod (er hard? 'defstv "No :mod was specified.")))
         (stv         (list (cons :inputs inputs)
                            (cons :outputs outputs)
                            (cons :internals internals)
                            ))
         (want-xdoc-p (or parents short long))
         (short       (cond ((stringp short)
                             short)
                            ((not short)
                             "")
                            (t
                             (progn$
                              (er hard? 'defstv ":short must be a string.")
                              ""))))
         (long        (cond ((stringp long)
                             long)
                            ((not long)
                             "")
                            (t
                             (progn$
                              (er hard? 'defstv ":long must be a string.")
                              ""))))


         (main (stv-process stv mod))
         ((unless main)
          ;; this shouldn't happen...
          (er hard? 'defstv-fn "stv-process failed?"))

; This is a trick to avoid re-serializing MOD in the certificate.  We remove
; the :mod from MAIN, and then save the stv without its module in the cert.
; Then, we re-attach the mod using a defconst.

         (main (change-processed-stv main :mod nil))

         (name-without-mod (intern-in-package-of-symbol
                            (concatenate 'string "*" (symbol-name name) "-WITHOUT-MOD*")
                            name))

         (cmds `((defconst ,name-without-mod ',main)
                 (defconst ,name (change-processed-stv ,name-without-mod
                                                       :mod ,mod-const-name)))))
      (if want-xdoc-p
          `(progn
             (defxdoc ,name
               :parents ,parents
               :short ,short
               :long ,long)
             ,@cmds
             ;; I use xdoc-extend here instead of directly catting the string
             ;; onto :long, so that the stv-process command gets run first.  This
             ;; way, the user gets good error reporting, whereas stv-to-xml does
             ;; not provide very nice error-reporting.
             (make-event
              (b* ((name ',name)
                   (stv  ',stv)
                   (mod  ',mod)
                   (labels ',labels)
                   (cstv (stv-compile stv mod))
                   (str  (str::cat "<h3>Simulation Diagram</h3>

<p>This is a <see topic='@(url
acl2::symbolic-test-vectors)'>symbolic test vector</see> defined with @(see
acl2::defstv).</p>" (stv-to-xml stv cstv labels))))
                `(xdoc-extend ,name ,str))))
        `(progn . ,cmds))))


  (defmacro defstv (name &key
                         mod
                         inputs
                         outputs
                         internals
                         labels
                         parents
                         short
                         long)
    `(make-event
      (let ((event (defstv-fn ',name ',mod ,mod ,inputs ,outputs ,internals ,labels ',parents ,short ,long)))
        event))))




(defsection stv->ins
  :parents (symbolic-test-vectors)
  :short "Get a list of the input simulation variables for an STV."

  :long "<p>@(call stv->ins) returns the user-level symbolic variables from the
input lines of a symbolic test vector.  For instance, if you have an input line
like:</p>

<code>
 (\"a-bus\"  _ _ _ a1 _ a2 _ _)
</code>

<p>Then the returned list will include <tt>a1</tt> and <tt>a2</tt>.</p>"

  (defund stv->ins (x)
    (declare (xargs :guard (processed-stv-p x)))
    (b* (((processed-stv x) x)
         ((compiled-stv cstv) x.compiled-stv))
      (alist-keys cstv.in-usersyms))))

(defsection stv->outs
  :parents (symbolic-test-vectors)
  :short "Get a list of the output simulation variables for an STV."

  :long "<p>@(call stv->outs) returns the user-level symbolic variables from
the output and internals lines of a symbolic test vector.  For instance, if you
have an output line like:</p>

<code>
 (\"main-result\"  _ _ _ res1 _ res2 _ _)
</code>

<p>Then the returned list will include <tt>res1</tt> and <tt>res2</tt>.</p>"

  (defund stv->outs (x)
    (declare (xargs :guard (processed-stv-p x)))
    (b* (((processed-stv x) x)
         ((compiled-stv cstv) x.compiled-stv))
      (alist-keys cstv.out-usersyms))))

(defsection stv->vars
  :parents (symbolic-test-vectors)
  :short "Get the list of all input and output simulation variables for an STV."
  :long "<p>See @(see stv->ins) and @(see stv->outs).</p>"

  (defund stv->vars (x)
    (declare (xargs :guard (processed-stv-p x)))
    (append (stv->ins x)
            (stv->outs x))))


;; For efficient execution of stv-run in GL, we want to our clause processors to
;; be able to natively execute these functions.
(gl::add-clause-proc-exec-fns '(4v-sexpr-restrict-with-rw-alist
                                vl::append-domains
                                sets::mergesort
                                sets::subset
                                sets::union
                                sets::difference))