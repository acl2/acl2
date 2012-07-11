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


; stv-top.lisp -- symbolic test vectors for esim
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-sim")
(include-book "stv-compile")
(include-book "stv-expand")
(include-book "stv-widen")
(include-book "stv-doc")
(include-book "stv-run")
(include-book "centaur/gl/auto-bindings" :dir :system)

;; I no longer include stv-debug here because
;;   (1) it has a big dependency set and ends up being the critical path, and
;;   (2) it has more ttags than anything else, and it's nice to think that
;;       these can be omitted unless desired.
;; (include-book "stv-debug")


(defxdoc symbolic-test-vectors
  :parents (esim)
  :short "A concise way to describe, evaluate, and debug symbolic simulations
of E modules."

  :long "<p>A symbolic test vector is a description of a multi-phase @(see
esim) simulation.  It lets you say how the state bits should be initialized,
how the inputs should be set as the simulation proceeds, and when you would
like the outputs and internal signals to be sampled.</p>

<p>As a user, the main steps for using symbolic test vectors are:</p>

<ul>

<li>Use @(see defstv) to introduce the STV you want to run.  You basically
explain when you want to send into the module, and which outputs you want to
extract at what times.</li>

<li>Use @(see stv-run) to run the STV on some particular inputs.  This is
intended to be compatible with @(see GL) proofs, and can also be used in a
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
 ((:initial
   (\"foo.statemachine.busy\"  0)
   (\"foo.prevStutter\"        stutter))

 ;; phases:                0      1     2     3     4          5        6  ...
 ;; ---------------------------------------------------------------------------

  (:inputs
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

<h3>High-Level Overview<h3>

<p>The <tt>:initial</tt> section controls the initial values of state bits.
For the above vector, <tt>foo.statemachine.busy</tt> will be initialized to
zero and <tt>foo.prevStutter</tt> will be some particular value,
<tt>stutter</tt>, that can be specified at @(see stv-run) time.</p>

<p>The <tt>:inputs</tt> section controls how the module's inputs will be set
over the course of the simulation.  For the above vector,</p>

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
during these cycles.  This might seem redundant, but it can be useful in cases
where there is an X in only one side of the result bus.</li>

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

<li>(Advanced) an explicit list of E input bits, in LSB-first order.  We don't
show this above, and it's not something you probably want to use.  But it may
be useful to know about this; generally all of the Verilog-level stuff is just
layered on top of lists of E bits, using a preprocessor, and the STV compiler
only ever sees with these bit lists.</li>

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
basically means <i>invert the previous value of this signal</i>.  This is only
legal for one-bit inputs whose previous value expanded to <tt>0</tt> or
<tt>1</tt>.  In practice, this means the only things that can occur before a
<tt>~</tt> are <tt>0</tt>, <tt>1</tt>, or another <tt>~</tt>.</li>

<li>The special <tt>_</tt> value represents an unconstrained, four-valued
variable.  As a rule, use <tt>_</tt> during any phase where you don't care
about the value on this input.  There is no relationship between separate
underscores, e.g., in the example above, separate variables are used for
<tt>a_bus</tt> during the first and second phases.</li>

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

<p>The names on internal lines may be strings that are Verilog-style plain or
hierarchical identifiers using periods as separators, which may optionally
include a Verilog-style bit- or part-select at the end.  It is also possible to
use explicit lsb-first ordered lists of ESIM paths.</p>


<h3>Initial Line Format</h3>

<p>Each line in the <tt>:initial</tt> section explains how to initialize some
state bits.  Unlike input lines, each initial line has only a single value,
namely its value at the start of the simulation.  This is because the value the
register stores during the subsequent phases of the simulation is determined by
the circuit.  Each initial line has the following format:</p>

<code>
 (name value)
</code>

<p>The names in initial lines may be strings that are Verilog-style plain or
hierarchical identifiers using periods as separators, which may optionally
include a Verilog-style bit- or part-select at the end.  It is also possible to
use explicit lsb-first ordered lists of ESIM paths.</p>

<p>STVs are slightly clever in how they interpret these names.  In short, you
don't have to write down the whole path to a Verilog <tt>reg</tt> or anything
like that, because the STV compiler will automatically walk backwards from
whatever paths you give it.  As long as this walk takes it to a flop or latch,
it will know which state bit to initialize.  In practice, you can give paths
that are separated from their Verilog <tt>reg</tt>s through any number of
assignments, inverters, and buffers.</p>

<p>The <tt>value</tt>s here are like those of input lines, except that you
can't use <tt>~</tt> since there isn't any previous value to invert.</p>")



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

<p>As a first step, we preprocess and compile the STV; see @(see stv-compile).
This step involves basic sanity checking and the computation of mappings that
record what inputs to provide to ESIM at each step of the simulation, what
outputs to extract after each phase, and how to translate between Esim bits and
the user-level input and output alists.  This compilation should generally be
quite fast (it's mostly involving the STV instead of the module), and it only
needs to be done once per STV.</p>

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

(defsection stv-autohyps

  (defund stv-autohyps-aux (ins stv)
    (declare (xargs :guard (and (symbol-listp ins)
                                (processed-stv-p stv))))
    (if (atom ins)
        nil
      ;; Could have used unsigned-byte-p instead, but that gets us into trouble
      ;; with :expand hints when recursive definitions of unsigned-byte-p are
      ;; installed, so just use explicit bounds instead.
      (list* `(natp ,(car ins))
             `(< ,(car ins) (expt 2 ,(stv-in->width (car ins) stv)))
            (stv-autohyps-aux (cdr ins) stv))))

  (defund stv-autohyps (stv)
    (declare (xargs :guard (processed-stv-p stv)))
    (b* ((ins (stv->ins stv))
         ((unless (symbol-listp ins))
          (er hard? 'stv-autohyps "Non-symbol inputs?")))
      `(and . ,(stv-autohyps-aux ins stv)))))


(defsection stv-autobinds

  (defund stv-autobinds-aux (ins stv)
    (declare (xargs :guard (and (symbol-listp ins)
                                (processed-stv-p stv))))
    (if (atom ins)
        nil
      (cons `(:nat ,(car ins) ,(stv-in->width (car ins) stv))
            (stv-autobinds-aux (cdr ins) stv))))

  (defund stv-autobinds (stv)
    (declare (xargs :guard (processed-stv-p stv)))
    (b* ((ins (stv->ins stv))
         ((unless (symbol-listp ins))
          (er hard? 'stv-autobinds "Non-symbol inputs?")))
      `(gl::auto-bindings . ,(stv-autobinds-aux ins stv)))))


(defsection stv-autoins

  (defund stv-autoins-aux (ins)
    (declare (xargs :guard t))
    (if (atom ins)
        nil
      (cons `(cons ',(car ins) ,(car ins))
            (stv-autoins-aux (cdr ins)))))

  (defund stv-autoins (stv)
    (declare (xargs :guard (processed-stv-p stv)))
    `(list . ,(stv-autoins-aux (stv->ins stv)))))


(defsection defstv
  :parents (symbolic-test-vectors)
  :short "Introduce a symbolic test vector as a constant."
  :long "<p>Example:</p>

<code>
 (defstv my-run
   :mod *my-mod*
   :initial   '((\"foo.bar.myreg\" mr)       ...)
   :inputs    '((\"opcode\" _ _ op _)        ...)
   :outputs   '((\"result\" _ _ _ _ res _)   ...)
   :internals '((\"foo.bar.mybus\" _ _ mb _) ...)
   :labels '(A nil B nil C nil)]
   :parents ...
   :short ...
   :long ...)
</code>

<p>The <tt>defstv</tt> command is the main interface for defining symbolic test
vectors.  It compiles the STV, does the necessary ESIM simulations, and gets
everything ready for @(see stv-run) and @(see stv-debug).  It generates
convenient macros for use in @(see def-gl-thm) commands, and can also produce
@(see xdoc) documentation.</p>

<h4>Required Arguments</h4>

<ul>

<li><tt>:mod</tt> should be the @(see esim) module you want to simulate, and
<b>must</b> be the name of a non-local @(see defconst).  This unusual
requirement lets us avoid writing the module into the certificate, which can
significantly improve performance when including books with STVs.</li>

<li>The <tt>:initial</tt>, <tt>:inputs</tt>, <tt>:outputs</tt>, and
<tt>:internals</tt> control how to simulate the module.  For the syntax and
meaning of these lines, see @(see symbolic-test-vector-format).</li>

</ul>

<h4>Optional Arguments</h4>

<ul>

<li><tt>:parents</tt>, <tt>:short</tt>, and <tt>:long</tt> are as in @(see
defxdoc).  If any of these options is given, documentation will be generated
for the STV.  This documentation includes a fancy table that shows the
simulation.</li>

<li><tt>:labels</tt> are only used for documentation.  If they are provided,
they must be a symbol list.  These symbols will only be used to label the
stages of the simulation, with <tt>nil</tt> leaving a blank.  (Having the pipe
stage names in the diagram is really nice).</li>

</ul>

<h4>Resulting Functions and Macros</h4>

<dl>

<dt><tt>(my-run)</tt></dt>

<dd>This is a disabled 0-ary function (i.e., a constant) that is a @(see
processed-stv-p).  You should generally only interact with this object using
interfacing functions like @(see stv->vars), @(see stv-out->width), etc., and
not directly use the <tt>processed-stv-p</tt> accessors (in case we change the
format).</dd>


<dt><tt>(my-run-autohyps)</tt></dt>

<dd>This is a macro that expands to something like:

<code>
 (and (unsigned-byte-p 4 opcode)
      (unsigned-byte-p 64 abus)
      (unsigned-byte-p 64 bbus)
      ...)

</code>

That is, it says each input simulation variable is a natural number of the
proper width.  This is generally useful in the <tt>:hyp</tt> of a @(see
def-gl-thm) about your STV.</dd>

<dt><tt>(my-run-autoins)</tt></dt>

<dd>This is a macro that expands to something like:

<code>
 (list (cons 'opcode opcode)
       (cons 'abus abus)
       (cons 'bbus bbus)
       ...)
</code>

That is, it constructs an alist that binds the name of each simulation variable
to the corresponding ACL2 symbol.  This is generally useful in the
<tt>:concl</tt> of a @(see def-gl-thm) about your STV, i.e., your conclusion
might be something like:

<code>
 (b* ((out-alist (stv-run (my-run) (my-run-autoins))))
   (outputs-valid-p out-alist))
</code>

</dd>

<dt><tt>(my-run-autobinds)</tt></dt>

<dd>This is a macro that expands to something like:

<code>
 (gl::auto-bindings (:nat opcode 4)
                    (:nat abus 64)
                    (:nat bbus 64)
                    ...)
</code>

See @(see gl::auto-bindings) for some details.  This is generally meant to be
used in the <tt>:g-bindings</tt> of a @(see def-gl-thm) about your STV.</dd>

<dd>These bindings are <b>probably quite lousy</b>.  For instance, if this is
some kind of ALU then we probably want to <tt>:mix</tt> the <tt>abus</tt> and
<tt>bbus</tt>.  But the generated bindings just use whatever variable order is
suggested by the initial and input lines, and doesn't smartly mix together
signals.</dd>

<dd>If your module is small or you're using @(see gl-aig-mode), then this may
be fine and very convenient.  For more complex modules, you'll probably want to
write your own binding macros.  See @(see stv-easy-bindings) for a high-level
way to describe most kind of bindings.</dd>

</dl>"

  (local (in-theory (disable good-esim-modulep)))

  (defund defstv-fn (name mod-const-name ;; e.g., *mmx*
                          mod            ;; e.g., the value of *mmx*
                          initial inputs outputs internals
                          labels parents short long)
    (declare (xargs :guard (and (symbolp name)
                                (symbolp mod-const-name)
                                (good-esim-modulep mod))))
    (b* ((mod         (or mod (er hard? 'defstv "No :mod was specified.")))

         (initial     (if (true-list-listp initial)
                          initial
                        (er hard? 'defstv ":initial is not even a true-list-listp?")))
         (inputs      (if (true-list-listp inputs)
                          inputs
                        (er hard? 'defstv ":inputs are not even a true-list-listp?")))
         (outputs     (if (true-list-listp outputs)
                          outputs
                        (er hard? 'defstv ":outputs are not even a true-list-listp?")))
         (internals   (if (true-list-listp internals)
                          internals
                        (er hard? 'defstv ":internals are not even a true-list-listp?")))
         (labels      (if (symbol-listp labels)
                          labels
                        (er hard? 'defstv ":labels need to be a symbol-listp.")))

         (stv         (make-stvdata :initial initial
                                    :inputs inputs
                                    :outputs outputs
                                    :internals internals))

         (want-xdoc-p (or parents short long))
         (short       (cond ((stringp short) short)
                            ((not short)     "")
                            (t               (progn$ (er hard? 'defstv ":short must be a string.")
                                                     ""))))
         (long        (cond ((stringp long) long)
                            ((not long)     "")
                            (t              (progn$ (er hard? 'defstv ":long must be a string.")
                                                    ""))))

         (preprocessed-stv
          (time$ (let* ((stv (stv-widen stv))
                        (stv (stv-expand stv mod)))
                   stv)
                 :msg "; stv preprocessing: ~st sec, ~sa bytes~%"
                 :mintime 1/2))

         (compiled-stv
          (time$ (stv-compile preprocessed-stv mod)
                 :msg "; stv compilation: ~st sec, ~sa bytes~%"
                 :mintime 1/2))

         ((unless compiled-stv)
          ;; this shouldn't happen... it should throw an error instead
          (er hard? 'defstv-fn "stv-compile failed?"))


         (processed-stv
          (time$ (stv-process stv compiled-stv mod)
                 :msg "; stv processing: ~st sec, ~sa bytes~%"
                 :mintime 1/2))

         ((unless processed-stv)
          ;; this shouldn't happen... it should throw an error instead
          (er hard? 'defstv-fn "stv-process failed?"))


         ;; Only now, after we've already compiled and processed the STV, do we
         ;; bother to generate the documentation.  We want to make sure it
         ;; stays in this order, because stv-to-xml doesn't have good error
         ;; reporting.
         (long (if (not want-xdoc-p)
                   long
                 (str::cat "<h3>Simulation Diagram</h3>

<p>This is a <see topic='@(url
acl2::symbolic-test-vectors)'>symbolic test vector</see> defined with @(see
acl2::defstv).</p>"
                           (or (stv-to-xml stv compiled-stv labels)
                               "Error generating diagram"))))


         ;; Stupid trick to avoid saving the module in the .cert file
         (stvconst-without-mod (intern-in-package-of-symbol
                                (str::cat "*" (symbol-name name) "-WITHOUT-MOD*")
                                name))
         (stvconst-with-mod    (intern-in-package-of-symbol
                                (str::cat "*" (symbol-name name) "*")
                                name))
         (name-autohyps        (intern-in-package-of-symbol
                                (str::cat (symbol-name name) "-AUTOHYPS")
                                name))
         (name-autoins         (intern-in-package-of-symbol
                                (str::cat (symbol-name name) "-AUTOINS")
                                name))
         (name-autobinds       (intern-in-package-of-symbol
                                (str::cat (symbol-name name) "-AUTOBINDS")
                                name))

         (cmds `((defconst ,stvconst-without-mod
                   ;; Remove :mod from the quoted constant we save
                   ',(change-processed-stv processed-stv :mod nil))

                 (defconst ,stvconst-with-mod
                   ;; Now restore it with a separate defconst, which gets evaluated
                   ;; at include-book time
                   (change-processed-stv ,stvconst-without-mod
                                         :mod ,mod-const-name))

                 (defund ,name ()
                   ;; Using a 0-ary function instead of a constant is nice when
                   ;; we want to look at DEF-GL-THMs with :PR, etc.
                   (declare (xargs :guard t))
                   ,stvconst-with-mod)

                 (defmacro ,name-autohyps ()
                   ',(stv-autohyps processed-stv))

                 (defmacro ,name-autoins ()
                   ',(stv-autoins processed-stv))

                 (defmacro ,name-autobinds ()
                    ',(stv-autobinds processed-stv))

                 ))

         (cmds (if (not want-xdoc-p)
                   cmds
                 (cons `(defxdoc ,name
                          :parents ,parents
                          :short ,short
                          :long ,long)
                       cmds))))

      `(progn . ,cmds)))

  (defmacro defstv (name &key
                         mod
                         initial inputs outputs internals
                         labels parents short long)
    `(make-event
      (let ((event (defstv-fn ',name
                     ',mod ,mod
                     ,initial ,inputs ,outputs ,internals
                     ,labels ',parents ,short ,long)))
        event))))


(defsection stv-easy-bindings
  :parents (symbolic-test-vectors)
  :short "Generating G-bindings from an STV in a particular way."

  :long "<p>@(call stv-easy-bindings) returns a list of G-bindings.  That is,
you can write something like:</p>

<code>
 (def-gl-thm foo
    ...
    :g-bindings
    (stv-easy-bindings (my-stv) '(opcode size special (:mix a b) c)))
</code>

<p>The format of <tt>x</tt> is simple: you can list out STV inputs and also use
<tt>(:mix a b c ...)</tt> where <tt>a</tt>, <tt>b</tt>, <tt>c</tt>, ... are all
STV inputs.</p>

<p>Bindings will be generated in the order specified, e.g., in the above
example the <tt>opcode</tt> will have the smallest indices, then <tt>size</tt>
next, etc.</p>

<p>You do <b>not</b> have to mention all of the STV variables.  All unmentioned
variables will be assigned indices after mentioned variables.</p>

<p>An especially nice feature of easy-bindings is that they automatically
adjust when inputs to the STV are resized, when new inputs are added, and when
irrelevant inputs are removed.</p>"

  (defund stv-easy-bindings-inside-mix (x stv)
    (declare (xargs :guard (processed-stv-p stv)))
    (cond ((atom x)
           nil)
          ((symbolp (car x))
           ;; Should be an STV input.
           (cons `(:nat ,(car x) ,(stv-in->width (car x) stv))
                 (stv-easy-bindings-inside-mix (cdr x) stv)))
          (t
           ;; Anything else is illegal inside mix.
           (er hard? 'stv-easy-bindings-inside-mix
               "Inside a :mix you can only have symbols (the names of stv
              inputs), ~ so ~x0 is illegal." (car x)))))

  (defund stv-easy-bindings-main (x stv)
    (declare (xargs :guard (processed-stv-p stv)))
    (cond ((atom x)
           nil)
          ((symbolp (car x))
           ;; Should be an STV input.
           (cons `(:nat ,(car x) ,(stv-in->width (car x) stv))
                 (stv-easy-bindings-main (cdr x) stv)))
          ((and (consp (car x))
                (equal (caar x) :mix))
           (let ((things-to-mix (cdar x)))
             (if (consp things-to-mix)
                 (cons `(:mix . ,(stv-easy-bindings-inside-mix things-to-mix stv))
                       (stv-easy-bindings-main (cdr x) stv))
               (er hard? 'stv-easy-bindings-main
                   ":MIX with no arguments? ~x0" (car x)))))
          (t
           (er hard? 'stv-easy-bindings-main
               "Arguments to stv-easy-bindings should be input names or ~
              (:mix input-name-list), so ~x0 is illegal." (car x)))))

  (defun stv-easy-bindings (stv x)
    (declare (xargs :guard (processed-stv-p stv)
                    :mode :program))
    (b* ((binds   (stv-easy-bindings-main x stv))
         (unbound (set-difference-equal (stv->ins stv)
                                        (pat-flatten1 binds))))
      (gl::auto-bindings-fn
       (append binds
               ;; bozo ugly, but workable enough...
               (stv-easy-bindings-inside-mix unbound stv))))))

