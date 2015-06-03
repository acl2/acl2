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

(defpointer stv symbolic-test-vectors)

(defxdoc symbolic-test-vector-format
  :parents (symbolic-test-vectors)
  :short "How to write a symbolic test vector."

  :long "<h3>Example Test Vector</h3>

@({
 (
 ;; phases:                0      1     2     3     4      5        6  ...
 ;; ---------------------------------------------------------------------------

  (:inputs ;; for supplying values to input wires
   (\"clock\"               0      ~)
   (\"ibus[13:10]\"     #b101  #b101     _)
   (\"ibus[9:0]\"          op     op     _)
   (\"fwd\"                16     16     _)
   (\"a_bus\"               _      _    a1    a1    a2         a2        _)
   (\"b_bus\"               _      _     b     b     b          b        _)
   (\"reset\"               0)
   (\"fuse[0]\"             X))

  (:outputs ;; for extracting values on output wires
   (\"result_bus\"          _      _     _     _     _       res1     res2)
   (\"result_bus[63:32]\"   _      _     _     _     _    res-hi1  res-hi2)
   (\"result_bus[31:0]\"    _      _     _     _     _    res-lo1  res-lo2)
   )

  (:internals ;; for extracting values on internal wires
   (\"queue0.mgr.fail\"     _      _     qf1   qf2   _))

 ;; advanced features:

  (:overrides ;; for forcibly overriding values on wires

   ;; abstract away product wire, replacing it with variables
   (\"foo.prod\"           _      _   prod    _     _      _        _ )

   ;; force fast mode to true after phase 1, no matter what its real value is
   (\"foo.fastmode\"       _      _     1     1     1      1        1 ))

  )
})

<h3>High-Level Overview</h3>

<p>The @(':inputs') section controls how the module's inputs will be set over
the course of the simulation.  For the above vector,</p>

<ul>

<li>@('clock') starts low and then toggles throughout the simulation,</li>

<li>@('ibus[13:10]') is held to 5 (#b101) during the first full cycle, but is
not constrained afterward,</li>

<li>@('ibus[9:0]') is held to a certain value (call it @('op')) during the
first full cycle, and is not constrained afterward,</li>

<li>@('fwd') is held constant at 16 during the first full cycle, but is
unconstrained afterward,</li>

<li>@('a_bus') is held at some particular value during the second full
cycle (call it @('a1')), and at a (possibly different) value, @('a2') during
the third cycle, but is unconstrained otherwise</li>

<li>@('b_bus') is held at the same value, call it @('b'), for the full second
and third cycle, but is unconstrained otherwise,</li>

<li>@('reset') is kept off for the entire simulation,</li>

<li>@('fuse[0]') is explicitly set to @('X') for the whole simulation.  This is
similar to setting it to @('_'), but is likely (1) more efficient and (2) more
likely to lead to false Xes in the outputs.</li>

<li>Any inputs to the module besides those specified above are implicitly
unconstrained (i.e., they are implicitly _) for the whole simulation.</li>

</ul>

<p>The @(':outputs') section controls when the outputs should be sampled.  For
this simulation:</p>

<ul>

<li>The full @('result_bus') will be sampled twice.  Its results from phases 5
and 6 will be called @('res1') and @('res2'), respectively.</li>

<li>The high and low parts of the @('result_bus') will also be sampled during
these cycles.  This might seem redundant, but it can be useful in cases where
there is an X in only one side of the result bus.</li>

</ul>

<p>The @(':internals') section is similar to the outputs section, but it allows
you to pull out the values of internal signals in the module.</p>


<p>The @(':overrides') section is similar to the inputs section, but it allows
you to forcibly install new values onto wires, regardless of how they are
actually driven by the circuit.</p>


<h3>Input Line Format</h3>

<p>Each line in the @(':inputs') section explains how a certain input should be
driven over time.  Each line has the form:</p>

@({
 (input-name     value1    value2   ...   valueN)
})

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
particular phase.  The number supplied must be within @('[0, 2^n)'), where
@('n') is the size of the input, or an error will be caused.</li>

<li>The special @('~') value is intended to support clock inputs, and basically
means <i>invert the previous value of this signal</i>.  This is only legal for
one-bit inputs whose previous value expanded to @('0') or @('1').  In practice,
this means the only things that can occur before a @('~') are @('0'), @('1'),
or another @('~').</li>

<li>The special @('_') value represents an unconstrained, four-valued variable.
As a rule, use @('_') during any phase where you don't care about the value on
this input.  There is no relationship between separate underscores, e.g., in
the example above, separate variables are used for @('a_bus') during the first
and second phases.</li>

<li>The special @(':ONES') value sets an input bus to all 1's, no matter what
its size.</li>

<li>Besides @('x'), any other non-keyword symbols (like @('op'), @('a1'),
@('a2'), and @('b') above) are called <b>simulation variables</b>.  A
simulation variable lets you supply a particular value for the input at this
phase when you evaluate the symbolic test vector.</li>

<li>(Advanced) the special @('X') value allows you to say that an input should
be explicitly set to X values.  It is similar to using @('_'), but supplies an
explicit X value instead of fresh variables.  The advantage of this is that it
can be very efficient: X values often remain as X as they propagate through
gates, whereas free variables generally become larger expressions.  So, using
explicit Xes may lead to more efficient simulations by avoiding the
construction of lots of irrelevant expressions.  However, using explicit X
values can also lead to false Xes, e.g., whereas @('(AND A (NOT A))') is
obviously 0, @('(AND X (NOT X))') is @('X').  So, using Xes can lead to overly
conservative results.</li>

</ul>


<h3>Output Line Format</h3>

<p>Each line in the @(':outputs') section controls when to sample certain
output signals.  The format is:</p>

@({
 (output-name     value1    value2   ...   valueN)
})

<p>As with input-names, the output-names can be either (1) a string that names
a particular output bus, (2) a Verilog-style bit- or part-select, or (3) a list
of E output bits in LSB-first order.</p>

<p>But here the only legal values are:</p>

<ul>

<li>@('_'), which means don't sample the output at this time, or</li>

<li>a symbol, like @('res1') or @('res2') above, which gives a name to the
output at this time.  These names have to be unique, since outputs can vary
over time.</li>

</ul>

<p>To avoid any confusion between input and output lines, we don't allow you to
use @('~'), @('X'), or keyword symbols in output lines.</p>


<h3>Internals Line Format</h3>

<p>Except for their names, the lines in the @(':internals') section are
essentially the same as lines in the @(':outputs') section.  Generally speaking
we try to make the differences between outputs and internal signals as
invisible as possible.  For instance, it doesn't matter during @(see stv-run)
whether a signal is an internal or output signal.</p>

<p>The names on internal lines may be strings that are Verilog-style plain or
hierarchical identifiers using periods as separators, which may optionally
include a Verilog-style bit- or part-select at the end.  It is also possible to
use explicit lsb-first ordered lists of ESIM paths.</p>


<h3>Override Line Format</h3>

<p>Each line in the @(':override') section explains how to override some
internal wire.</p>

<p>The names in override lines may be strings that are Verilog-style plain or
hierarchical identifiers using periods as separators, which may optionally
include a Verilog-style bit- or part-select at the end.  It is also possible to
use explicit lsb-first ordered lists of ESIM paths.</p>

<p>The @('value')s here are similar to those of input lines, except that:</p>

<ul>

<li>@('~') is not allowed, because it would be somewhat confusing.</li>

<li>@('_') means \"don't override the wire during this phase\".</li>

</ul>

<p>Every variable used in an override line becomes both an input and an output
variable of the STV.  For instance, in the example above, we had the following
override line:</p>

@({
   (\"foo.prod\"           _      _   prod    _     _      _        _ )
})

<p>Here, as an input to the STV, @('prod') allows us to forcibly set the value
of the wire @('foo.prod').  As an output, @('prod') gives us the <b>original,
un-overridden</b> expression for @('prod').  (Well, that's probably mostly
true.  If @('prod') depends on other overridden values, or is involved in some
combinational loop so that it affects itself, then this may not be quite
right.)</p>")



(defsection stv-implementation-details
  :parents (symbolic-test-vectors)
  :short "Overview of the basic flow for processing and running STVs."

  :long "<p>Here is a high-level overview of how we compile, process, and
evaluate STVs.  A picture of the flow is:</p>

@({
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
        |    +-------> Waveform (VCD Dump)
        |    |
        v    v
  Simulation Output Alist
})


<p>Here, the user provides:</p>

<ul>

<li>The <b>User-Level STV</b>, which is a symbolic test vector written in the
@(see symbolic-test-vector-format),</li>

<li>The <b>ESIM Module</b> to simulate, which is generally produced by VL.</li>

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
module for as many phases as are necessary to evaluate this STV; see @(see
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
4v-sexpr-eval) to reduce the sexprs that are found in the Processed STV with the
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
@(see memoize) things so that even though your first call of @(see stv-debug)
is expensive, subsequent calls will not need to redo the simulation or
specialization steps.</p>")

(define stv-autohyps-aux ((ins symbol-listp)
                          (stv processed-stv-p))
  :parents (stv-autohyps)
  :long "<p>We could have used @(see unsigned-byte-p) instead, but that gets us
into trouble with :expand hints when recursive definitions of unsigned-byte-p
are installed, so just use explicit bounds instead.</p>"
  (if (atom ins)
      nil
    (list* `(natp ,(car ins))
           `(< ,(car ins) (expt 2 ,(stv-in->width (car ins) stv)))
           (stv-autohyps-aux (cdr ins) stv))))

(define stv-autohyps ((stv processed-stv-p))
  :parents (defstv)
  :short "Generate the body for an STV's autohyps macro."
  (b* ((ins (stv->ins stv))
       ((unless (symbol-listp ins))
        (raise "Non-symbol inputs?")))
    `(and . ,(stv-autohyps-aux ins stv))))

(define stv-autobinds-aux ((ins symbol-listp)
                           (stv processed-stv-p))
  :parents (stv-autobinds)
  (if (atom ins)
      nil
    (cons `(:nat ,(car ins) ,(stv-in->width (car ins) stv))
          (stv-autobinds-aux (cdr ins) stv))))

(define stv-autobinds ((stv processed-stv-p))
  :parents (defstv)
  :short "Generate the body for an STV's autobinds macro."
  (b* ((ins (stv->ins stv))
       ((unless (symbol-listp ins))
        (raise "Non-symbol inputs?")))
    `(gl::auto-bindings . ,(stv-autobinds-aux ins stv))))

(define stv-autoins-aux (ins)
  :parents (stv-autoins)
  (if (atom ins)
      nil
    (cons `(cons ',(car ins) ,(car ins))
          (stv-autoins-aux (cdr ins)))))

(define stv-autoins ((stv processed-stv-p))
  :parents (defstv)
  :short "Generate the body for an STV's autoins macro."
  `(list . ,(stv-autoins-aux (stv->ins stv))))



(local (in-theory (disable good-esim-modulep)))

(define defstv-main
  :parents (defstv)
  :short "Main error checking and processing of an STV."

  (&key (mod good-esim-modulep)
        (name symbolp)
        inputs outputs internals overrides)

  :returns (pstv (equal (processed-stv-p pstv)
                        (if pstv t nil))
                 :hyp (force (symbolp name)))

  :long "<p>This is the main part of @(see defstv).</p>

<p>We split this out into its own function for advanced users who need a
non-event based way to introduce symbolic test vectors.</p>

<p>This does only the STV processing.  We don't deal here with generating
documentation, creating autohyps macros, etc.</p>"

  (b* ((mod         (or mod
                        ;; Blah, silly, (good-esim-modulep nil) is true, so
                        ;; explicitly check for this.
                        (raise "No :mod was specified.")))

       (-
        ;; Horribly primitive sanity check, but in practice even this
        ;; may be helpful for avoiding gross errors.
        (or (and (gpl :n mod)
                 (symbolp (gpl :n mod)))
            (raise "Alleged module doesn't have a non-nil symbol :n field?  ~
                    Is this a proper ESIM module?")))

       (inputs      (if (true-list-listp inputs)
                        inputs
                      (raise ":inputs are not even a true-list-listp")))
       (outputs     (if (true-list-listp outputs)
                        outputs
                      (raise ":outputs are not even a true-list-listp")))
       (internals   (if (true-list-listp internals)
                        internals
                      (raise ":internals are not even a true-list-listp")))
       (overrides   (if (true-list-listp overrides)
                        overrides
                      (raise ":overrides are not even a true-list-listp")))

       (stv         (make-stvdata :overrides overrides
                                  :inputs    inputs
                                  :outputs   outputs
                                  :internals internals))

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
        (raise "stv-compile failed?"))

       (mod (stv-cut-module
             (compiled-stv->override-paths compiled-stv) mod))

       (processed-stv
        (time$ (stv-process name stv compiled-stv mod)
               :msg "; stv processing: ~st sec, ~sa bytes~%"
               :mintime 1/2))

       ((unless processed-stv)
        ;; this shouldn't happen... it should throw an error instead
        (raise "stv-process failed?")))

    processed-stv))


(define defstv-fn
  :parents (defstv)
  :short "Implementation of @(see defstv)."

  ((name            symbolp "E.g., mmx-run")
   (mod-const-name  symbolp "E.g., the symbol *mmx*")
   (mod             good-esim-modulep "E.g., the actual E module for *mmx*")
   ;; Arguments from the user...
   inputs outputs internals overrides
   labels parents short long)

  (b* ((labels      (if (symbol-listp labels)
                        labels
                      (raise ":labels need to be a symbol-listp.")))

       (want-xdoc-p (or parents short long))
       (short       (cond ((stringp short) short)
                          ((not short)     "")
                          (t               (progn$ (raise ":short must be a string.")
                                                   ""))))
       (long        (cond ((stringp long) long)
                          ((not long)     "")
                          (t              (progn$ (raise ":long must be a string.")
                                                  ""))))

       (processed-stv (defstv-main :mod       mod
                                   :name      name
                                   :overrides overrides
                                   :inputs    inputs
                                   :outputs   outputs
                                   :internals internals))
       ((unless processed-stv)
        ;; In practice we should have already thrown an error, so we should
        ;; never hit this.
        (raise "Failed to process STV."))

       (compiled-stv (processed-stv->compiled-stv processed-stv))
       (stv          (processed-stv->user-stv processed-stv))

       ((unless (stvdata-p stv))
        ;; Stupidity to satisfy guards of stv-to-xml call, below; this should
        ;; be impossible to hit, I just don't want to prove it.
        (raise "stv processing didn't produce good stvdata?"))

       ;; Only now, after we've already compiled and processed the STV, do we
       ;; bother to generate the documentation.  We want to make sure it stays
       ;; in this order, because stv-to-xml doesn't have good error reporting.
       (long (if (not want-xdoc-p)
                 long
               (str::cat "<h3>Simulation Diagram</h3>

<p>This is a <see topic='@(url
acl2::symbolic-test-vectors)'>symbolic test vector</see> defined with @(see
acl2::defstv).</p>"
                         (or (stv-to-xml stv compiled-stv labels)
                             "Error generating diagram")
                         long)))


         ;; Stupid trick to avoid saving the module in the .cert file
         (stvconst             (intern-in-package-of-symbol
                                (str::cat "*" (symbol-name name) "*")
                                name))
         (modconst             (intern-in-package-of-symbol
                                (str::cat "*" (symbol-name name) "-MOD*")
                                name))
         (name-mod             (intern-in-package-of-symbol
                                (str::cat (symbol-name name) "-MOD")
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

         (cmds `((defconst ,stvconst ',processed-stv)

                 (defconst ,modconst
                   (stv-cut-module (compiled-stv->override-paths
                                    (processed-stv->compiled-stv ,stvconst))
                                   ,mod-const-name))

                 (defund ,name ()
                   ;; Using a 0-ary function instead of a constant is nice when
                   ;; we want to look at DEF-GL-THMs with :PR, etc.
                   (declare (xargs :guard t))
                   ,stvconst)

                 (defthm ,(intern-in-package-of-symbol
                           (str::cat "PROCESSED-STV-P-OF-" (symbol-name name))
                           name)
                   (processed-stv-p (,name)))

                 ;; We now also disable the executable-counterpart, as
                 ;; suggested by David Rager (acl2-books Issue 114).
                 (in-theory (disable (:executable-counterpart ,name)))

                 (defund ,name-mod ()
                   (declare (xargs :guard t))
                   ,modconst)

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

      `(with-output :off (event)
         (progn . ,cmds))))


(defsection defstv
  :parents (symbolic-test-vectors)
  :short "Introduce a symbolic test vector as a constant."
  :long "<p>Example:</p>

@({
 (defstv my-run
   :mod       *my-mod*
   :inputs    '((\"opcode\" _ _ op _)        ...)
   :outputs   '((\"result\" _ _ _ _ res _)   ...)
   :internals '((\"foo.bar.mybus\" _ _ mb _) ...)
   :overrides '((\"foo.bar.mywire\" _ mw _ _) ...)
   :labels    '(A nil B nil C nil)]
   :parents   ...
   :short     ...
   :long      ...)
})

<p>The @('defstv') command is the main interface for defining symbolic test
vectors.  It compiles the STV, does the necessary ESIM simulations, and gets
everything ready for @(see stv-run) and @(see stv-debug).  It generates
convenient macros for use in @(see def-gl-thm) commands, and can also produce
@(see xdoc) documentation.</p>

<h4>Required Arguments</h4>

<ul>

<li>@(':mod') should be the @(see esim) module you want to simulate, and
<b>must</b> be the name of a non-local @(see defconst).  This unusual
requirement lets us avoid writing the module into the certificate, which can
significantly improve performance when including books with STVs.</li>

<li>The @(':inputs'), @(':outputs'), @(':internals'), and @(':overrides')
control how to simulate the module.  For the syntax and meaning of these lines,
see @(see symbolic-test-vector-format).</li>

</ul>

<h4>Optional Arguments</h4>

<ul>

<li>@(':parents'), @(':short'), and @(':long') are as in @(see defxdoc).  If
any of these options is given, documentation will be generated for the STV.
This documentation includes a fancy table that shows the simulation.</li>

<li>@(':labels') are only used for documentation.  If they are provided, they
must be a symbol list.  These symbols will only be used to label the stages of
the simulation, with @('nil') leaving a blank.  (Having the pipe stage names in
the diagram is really nice).</li>

</ul>

<h4>Resulting Functions and Macros</h4>

<dl>

<dt>@('(my-run)')</dt>

<dd>This is a disabled 0-ary function (i.e., a constant) that is a @(see
processed-stv-p).  You should generally only interact with this object using
interfacing functions like @(see stv->vars), @(see stv-out->width), etc., and
not directly use the @('processed-stv-p') accessors (in case we change the
format).</dd>

<dt>@('(my-run-autohyps)')</dt>

<dd>This is a macro that expands to something like:

@({
 (and (unsigned-byte-p 4 opcode)
      (unsigned-byte-p 64 abus)
      (unsigned-byte-p 64 bbus)
      ...)

})

That is, it says each input simulation variable is a natural number of the
proper width.  This is generally useful in the @(':hyp') of a @(see def-gl-thm)
about your STV.</dd>

<dt>@('(my-run-autoins)')</dt>

<dd>This is a macro that expands to something like:

@({
 (list (cons 'opcode opcode)
       (cons 'abus abus)
       (cons 'bbus bbus)
       ...)
})

That is, it constructs an alist that binds the name of each simulation variable
to the corresponding ACL2 symbol.  This is generally useful in the @(':concl')
of a @(see def-gl-thm) about your STV, i.e., your conclusion might be something
like:

@({
 (b* ((out-alist (stv-run (my-run) (my-run-autoins))))
   (outputs-valid-p out-alist))
})

</dd>

<dt>@('(my-run-autobinds)')</dt>

<dd>This is a macro that expands to something like:

@({
 (gl::auto-bindings (:nat opcode 4)
                    (:nat abus 64)
                    (:nat bbus 64)
                    ...)
})

See @(see gl::auto-bindings) for some details.  This is generally meant to be
used in the @(':g-bindings') of a @(see def-gl-thm) about your STV.</dd>

<dd>These bindings are <b>probably quite lousy</b>.  For instance, if this is
some kind of ALU then we probably want to @(':mix') the @('abus') and
@('bbus').  But the generated bindings just use whatever variable order is
suggested by the initial and input lines, and doesn't smartly mix together
signals.</dd>

<dd>If your module is small or you're using @(see gl::gl-satlink-mode), then
this may be fine and very convenient.  For more complex modules, you'll
probably want to write your own binding macros.  See @(see stv-easy-bindings)
for a high-level way to describe most kind of bindings.</dd>

<dt>@('(my-run-mod)')</dt>

<dd>This is a disabled 0-ary function (i.e., a constant) that either returns
@('*mod*') or, when @(':overrides') are used, some modified version of
@('*mod*') where the overridden wires have been cut.  There is ordinarily no
reason to need this, but certain functions like @('stv-debug') make use of
it.</dd>

</dl>"

  (defmacro defstv (name &key
                         mod
                         inputs outputs internals overrides
                         labels parents short long)
    `(make-event
      (let ((event (defstv-fn ',name
                     ',mod ,mod
                     ,inputs ,outputs ,internals ,overrides
                     ,labels ',parents ,short ,long)))
        event))))




(define stv-easy-bindings-inside-mix ((x "Some arguments inside of a :mix")
                                      (stv processed-stv-p))
  :parents (stv-easy-bindings)
  (cond ((atom x)
         nil)
        ((symbolp (car x))
         ;; Should be an STV input.
         (cons `(:nat ,(car x) ,(stv-in->width (car x) stv))
               (stv-easy-bindings-inside-mix (cdr x) stv)))
        (t
         ;; Anything else is illegal inside mix.
         (raise "Inside a :mix you can only have symbols (the names of stv ~
                 inputs), so ~x0 is illegal." (car x)))))

(define stv-easy-bindings-main ((x   "Some arguments to easy-bindings")
                                (stv processed-stv-p))
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
             (raise ":MIX with no arguments? ~x0" (car x)))))
        (t
         (raise "Arguments to stv-easy-bindings should be input names or ~
                 (:mix input-name-list), so ~x0 is illegal." (car x)))))

(program)

(define stv-easy-bindings
  :parents (symbolic-test-vectors)
  :short "Generating G-bindings from an STV in a particular way."

  ((stv   "The STV you are dealing with."
          processed-stv-p)
   (order "The variable order you want to use."))

  :long "<p>@(call stv-easy-bindings) is a macro for proving theorems about
@(see symbolic-test-vectors) using @(see gl).  It returns a list of G-bindings
for use with @(see def-gl-thm).  That is, you can write something like:</p>

@({
 (def-gl-thm foo
    ...
    :g-bindings
    (stv-easy-bindings (my-stv) '(opcode size special (:mix a b) c)))
})

<p>This is probably only useful when:</p>

<ul>

<li>You are using GL in BDD mode, not some AIG or SAT based mode.</li>

<li>You are running into performance problems when using the default
@('-autobinds') from the @(see defstv).</li>

<li>You want to see if a different variable order performs better.</li>

</ul>

<p>To use @('stv-easy-bindings'), you just list (a subset of) the STV inputs in
priority order.  For instance, in the above example, the @('opcode') will get
the smallest indices, then @('size') next, etc.  You do <b>not</b> have to list
all of the STV variables.  Any unmentioned variables will be assigned indices
after mentioned variables.</p>

<p>As in @(see gl::auto-bindings), you can also use @('(:mix a b c ...)') to
interleave the bits of @('a'), @('b'), @('c'), ...; note that for this to work
these variables must all share the same width.  This is generally useful for
data buses that are going to be combined together.</p>

<p>An especially nice feature of easy-bindings is that they automatically
adjust when inputs to the STV are resized, when new inputs are added, and when
irrelevant inputs are removed.</p>"

  (b* ((binds   (stv-easy-bindings-main order stv))
       (unbound (set-difference-equal (stv->ins stv)
                                      (pat-flatten1 binds))))
    (gl::auto-bindings-fn
     (append binds
             ;; bozo ugly, but workable enough...
             (stv-easy-bindings-inside-mix unbound stv)))))


(defxdoc symbolic-test-vector-composition
  :parents (symbolic-test-vectors)
  :short "Strategy for performing compositional proofs involving stv's"

  :long "<p>It is common to use @(see gl) to perform proofs about small and
  moderately-sized circuits.  However, performing proofs about large circuits
  typically involves first breaking the circuit into smaller parts, and then
  showing that the sum of the parts is equivalent to the original whole
  circuit.  We call this proof a <it>compositional equivalence proof.</it></p>

  <p>Currently the most thorough example of such a proof can be found in the
  book @('centaur/esim/tutorial/boothmul.lisp').  This example highlights two
  ways of performing a compositional equivalence proof:</p>

  <ol>
    <li>By using @(see gl)</li>
    <li>By using rewriting</li>
  </ol>

  <p>The advantage of using @(see gl) is that it is automatic.  The
  disadvantage is that once one is working on very large circuits, the
  underlying BDDs or SAT solvers are unlikely to complete.  This is because the
  compositional proof relies upon the fact that every relevant intermediate
  value should be a @(see natp) (as opposed to @('X').  This turns out to be a
  very time-consuming proof obligation!</p>

  <p>An alternative to GL that uses rewriting has been developed.  It involves
  using book @('centaur/esim/stv/stv-decomp-proofs').  We recommend looking at
  the boothmul example mentioned above but offer additional points of
  clarification for anyone striving to use this book:</p>

  <ul>

    <li><p>You will need to enable the @('stv-decomp-theory').  Thus, the
    user's hints for the composition proof will look something like:</p>

@({
 :use ((:instance phase-1-types)
       (:instance phase-2-types))
 :in-theory (stv-decomp-theory)
})

    </li>

    <li><p>At one point the book only worked when the stv's used their autoins
    macro (see @(see defstv)) for finding the inputs.  We think this is no
    longer the case, but it is something to keep in mind when debugging the
    failures of your proofs.</p></li>

    <li><p>The user absolutely must prove and @(':use') a lemma that says the
    relevant intermediate values are @('natp')s.  If the user fails to do this,
    they will likely get an error message that looks like the following.  Note
    that the user can still obtain a \"not equivalent\" error for other
    reasons, which must be debugged by the user.</p>

@({
 HARD ACL2 ERROR in STV-DECOMP-4V-ENV-EQUIV-META:  Not equivalent

 A-alist:
 ((WIRENAME[0] CAR (IF (EQUAL (4V-TO-NAT #) 'X) '(X X X X X ...) (IF (IF # #
 #) (BOOL-TO-4V-LST #) '#))) (WIRENAME[10] CAR (CDR (CDR (CDR
 #)))) (WIRENAME[11] CAR (CDR (CDR (CDR #)))) (WIRENAME[12] CAR (CDR (CDR (CDR
 #)))) (WIRENAME[13] CAR (CDR (CDR (CDR #)))) ...)
 B-alist:
 ((WIRENAME[0] BOOL-TO-4V (LOGBITP '0 WIRENAME)) (WIRENAME[10] BOOL-TO-4V
 (LOGBITP '10 WIRENAME)) (WIRENAME[11] BOOL-TO-4V (LOGBITP '11 WIRENAME))
 (WIRENAME[12] BOOL-TO-4V (LOGBITP '12 WIRENAME)) (WIRENAME[13] BOOL-TO-4V
 (LOGBITP '13 WIRENAME)) ...)
})
    </li>
  </ul>

  <p>The stv-decomp-proofs book is experimental and not as robust as many of
  the other features provided in the ACL2 books.  Please send inquiries to the
  acl2-books project.</p>
")
