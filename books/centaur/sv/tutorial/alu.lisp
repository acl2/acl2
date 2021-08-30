; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2012-2015 Centaur Technology
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
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>


; This is the first example in the tutorial.  We are going to try to verify a
; basic 16-bit ALU module that implements 8 opcodes.  We will discover that
; there is a bug in its COUNT operation.

(in-package "SV")

; -----------------------------------------------------------------------------
;
;                            PRELIMINARY SETUP
;
; -----------------------------------------------------------------------------

; These include-books load all the libraries we're going to use.  This takes
; quite awhile.  In practice, we often build an ACL2 image that has these
; libraries pre-loaded, and use that image to carry out our proofs; see :DOC
; SAVE-EXEC for more information about how to save images.

(include-book "../top")
(include-book "centaur/vl/loader/top" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/aig/g-aig-eval" :dir :system)
(include-book "tools/plev-ccl" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(include-book "support")
(include-book "oslib/ls" :dir :system)

; cert_param: (uses-glucose)
; cert_param: (non-cmucl)

(gl::def-gl-clause-processor sv-tutorial-glcp)

(make-event

; Disabling waterfall parallelism.

 (if (f-get-global 'acl2::parallel-execution-enabled state)
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))




; The PLEV (print level) tool lets you control how much output ACL2 prints when
; it tries to print an object.  It is very important to be able to control the
; print level when you want to inspect things like translations, hardware
; modules, symbolic test vectors, etc.  Without (plev) ACL2 can end up just
; printing millions of lines of output at you.  See :XDOC PLEV for more
; information.
(make-event (b* (((er &) (acl2::plev)))
              (value '(value-triple :plev))))

; Debugger configuration.  These are optional commands that we generally use to
; enable the interactive debugger.  It's often very useful to get backtraces
; with :b when you interrupt.  On the other hand, this configuration can be
; very irritating when you are doing ordinary ACL2 proofs, especially the
; break-on-error command!
(set-slow-alist-action :break)
(make-event (b* ((state (set-debugger-enable t)))
              (value '(value-triple :set-debugger-enable))))

; Memory configuration.  The set-max-mem command sort of gives the Lisp a soft
; hint as to when to GC.  For this example we don't need very much memory, so
; lets set up a 3 GB threshold.  Putting this in a value-triple makes it an
; embeddable event.
(value-triple (acl2::set-max-mem (* 3 (expt 2 30))))




; -----------------------------------------------------------------------------
;
;                        LOADING THE ALU16 MODULE
;
; -----------------------------------------------------------------------------

; The file alu16.v contains a very simple ALU module that we will verify.  You
; should probably look at it now, and then come back.


; First, we read that module into a VL design.  This form does that.
(def-saved-event alu-design-form
  (defconsts (*alu-vl-design* state)
    (b* (((mv loadresult state)
          (vl::vl-load (vl::make-vl-loadconfig
                        :start-files '("alu16.v")
                        :search-path '("lib")))))
      (mv (vl::vl-loadresult->design loadresult) state))))

(def-saved-nonevent alu-print-reportcard
  (vl::cw-unformatted
   (vl::vl-reportcard-to-string (vl::vl-design-reportcard *alu-vl-design*))))

(def-saved-event alu->svex-form
  (defconsts (*alu-svex-design*
              *alu-simplified-good*
              *alu-simplified-bad*)
    (b* (((mv errmsg svex-design good bad)
          (vl::vl-design->sv-design "alu16" *alu-vl-design* (vl::make-vl-simpconfig))))
      (and errmsg
           (raise "~@0~%" errmsg))
      (mv svex-design good bad))))

(def-saved-nonevent alu-print-bad
  (vl::cw-unformatted
   (vl::vl-pps-modulelist (vl::vl-design->mods *alu-simplified-bad*))))

(def-saved-nonevent alu-print-good
  (vl::cw-unformatted
   (vl::vl-pps-modulelist (vl::vl-design->mods *alu-simplified-good*))))

(def-saved-nonevent alu-print-good-reportcard
  (vl::cw-unformatted
   (vl::vl-reportcard-to-string (vl::vl-design-reportcard *alu-simplified-good*))))

(deftutorial translating-verilog-to-svex
  :parents (sv-tutorial)
  :short "How to parse Verilog files and translate them into an svex design"
  :long "
<p>The first step in analyzing a design is to read it in.</p>

<p>The basic function to read and parse a Verilog design is @(see vl::vl-load).
The following form shows how to read our ALU design from the file
\"alu.v\".</p>

@(`(:code ($ alu-design-form))`)

<p>To specify what file(s) to load, we build a @(see vl::vl-loadconfig) object.
Here we have provided a starting file to read as well as a search path, from
which we need to load the @('flop') module.  @(csee vl::vl-load) produces a @(see
vl::vl-loadresult) structure, one field of which is the representation of the
design, which is the part we're interested in.</p>

<p>Before we go on and translate this into an svex design, we might want to see
whether there were any errors in parsing:</p>

@(`(:code ($ alu-print-reportcard))`)

<p>This prints the design's \"reportcard\", the list of warnings about each
module.  At this point, because our ALU module is well-formed and VL has no
trouble parsing it, this doesn't print anything.</p>

<p>The @('*alu-vl-design*') is basically a Verilog parse tree; we want to translate
this into an svex module hierarchy.  We can do this using @(see
vl::vl-design->sv-design):</p>

@(`(:code ($ alu->svex-form))`)

<p>This runs a series of Verilog to Verilog transforms on the parse tree to
simplify it, and finally transforms the simplified hierarchy into an svex
design.  It returns the resulting svex design, an object of type @(see
sv::design), as well as two additional Verilog designs: the portion of the
original design that survived the simplification process, and the portion that
failed for one reason or another.  You can view pretty-printed versions of
these:</p>

@(`(:code ($ alu-print-bad))`)

<p>doesn't print anything because our module was OK, whereas</p>

@(`(:code ($ alu-print-good))`)

<p>prints out a module similar to the original alu16 module.  You can also
print its warnings:</p>

@(`(:code ($ alu-print-good-reportcard))`)

<p>The svex design @('*alu-svex-design*') is an object of type @(see
sv::design), and this is a small enough design that you can print it in
full:</p>

@({(without-evisc *alu-svex-design*)})

<p>To continue the ALU example, next see @(see stvs-and-testing).</p>")


; -----------------------------------------------------------------------------
;
;                         RUNNING THE ALU16 MODULE
;
; -----------------------------------------------------------------------------



; There are many ways to run an svex design.  One of the nicest ways is to use
; a Symbolic Test Vector (STV).  STVs allow you to work at the Verilog level,
; i.e., provide inputs for whole busses rather than single bits, describe
; multi-phase simulations, and generate debugging waveforms.  They also hide
; pretty much all of the details of how SVEX works.

; STVs were originally an interface to the ESIM hardware verification package.
; For backward compatibility, svex's STV functions are therefore named slightly
; differently, and there are two ways to refer to most of them: in the ACL2
; package, using "svtv" instead of "stv", or in the SVEX package, using either
; "svtv" or "stv".  Since we're in the SVEX package in this book, we could use
; them interchangeably, but instead we'll stick with "svtv" to reduce
; confusion.

; The ALU16 module is a simply clocked pipeline.  Inputs go in one cycle; the
; result is computed using an opcode that is provided the next cycle, and the
; result is output the following cycle.
(def-saved-event alu-stv
  (defsvtv alu-test-vector        ;; name for this test vector
    :mod *alu-svex-design*    ;; the svex design to simulate

    :parents (stvs-and-testing)
    :short "A simple test of the alu16 module."
    :labels  '(dat1  dat2  op1   op2   out1  out2)

    :inputs
      ;; verilog name --> sequence of inputs to supply
    '(("clk"    1     0     1     0     1     0)
      ("opcode" _     _     _     op    _)
      ("abus"   _     a     _)
      ("bbus"   _     b     _))

    :outputs                  ;; verilog name --> variable names we will use
    '(("out"    _     _     _     _     _    res))))





; This DEFSTV command introduces several things, but among them is a 0-ary
; function, (alu-test-vector), that is a "processed STV" object.


; With this STV defined, we can try running it on concrete inputs.  But we will
; need to supply the right opcodes.
;
; If this was not just a tutorial but were instead a serious ALU that we cared
; about and that logic designers were updating, we could extract the `defines
; from the Verilog automatically.  The loadresult object obtained from VL-LOAD
; records the defines that were encountered; see also :XDOC VL::VL-DEFINES-P.
;
; But let's keep things easy and just manually recreate the opcode list,
; instead.

(def-saved-event alu-opcodes
  (progn
    (defconst *op-plus*    0)
    (defconst *op-minus*   1)
    (defconst *op-bitand*  2)
    (defconst *op-bitor*   3)
    (defconst *op-bitxor*  4)
    (defconst *op-min*     5)
    (defconst *op-count*   6)
    (defconst *op-mult*    7)))

; We can use STV-RUN to run the test vector on particular input alists.  The
; input alists need to give values for the input variables of the vector, i.e.,
; OP, A, and B.

(def-saved-nonevent alu-example-1
  (svtv-run (alu-test-vector)
            `((op . ,*op-plus*)
              (a  . 5)
              (b  . 3))))

; As you can see, the output is provided as an ALIST of values for the STV's
; output variables.  In this case we see that RES has value 8, so the circuit
; added 5 and 3 correctly.
;
; By default STV-RUN prints lots of debugging info.  We'll see below that this
; is very useful in theorems.  But when we're just doing concrete runs, this
; output can be irritating.  You can turn it off by adding :quiet t, like this:

(def-saved-nonevent alu-example-2
  (svtv-run (alu-test-vector)
            `((op . ,*op-mult*)
              (a  . 5)
              (b  . 3))
            :quiet t))

(defttag write-ok)

(local (acl2::remove-untouchable acl2::writes-okp nil))


; Now, you can also generate a waveform.  This dumps a VCD file, which you can
; view with gtkwave or any of several other waveform viewers.

(local
 (def-saved-nonevent alu-debug
   (svtv-debug (alu-test-vector)
               `((op . ,*op-mult*)
                 (a  . 5)
                 (b  . 3))
               :filename "alu-min-debug.vcd")
   :return state
   :writep t))

(def-saved-nonevent alu-function-examine
  (svtv->outexprs (alu-test-vector)))

(def-saved-nonevent alu-function-examine-rw
  (svex-alist-rewrite-fixpoint (svtv->outexprs (alu-test-vector))))

(def-saved-nonevent alu-x-input
  (svtv-run (alu-test-vector)
            `((op . ,*op-plus*)
              (a  . ,(4vec-x))
              (b  . 3))))

(def-saved-nonevent alu-zx-input
  (svtv-run (alu-test-vector)
            `((op . ,*op-bitand*)
              (a  . ,(4vec #xfca0 #x0cfa))
              (b  . ,#xffff))))



(deftutorial stvs-and-testing
  :parents (sv-tutorial)
  :short "Defining a simulation pattern (STV) and using it to run tests."
  :long "

<p>Part of the @(see sv-tutorial). Previous section: @(see
translating-verilog-to-svex).</p>

<h4>Defining a simulation pattern</h4> <p>To run a test of our SVEX design,
we'll first write a form that describes how to stimulate the module and grab
its output.  Looking at the ALU design, we have inputs coming into flip-flops.
The outputs of these flops are combined with the opcode input and used to
compute @('ans').  This goes to another flop, the result of which is output.
So we need to provide the @('a') and @('b') inputs one cycle, @('opcode') the
next, and read the output the cycle after that.  The following form defines a
@(see symbolic-test-vector) that describes this simulation pattern:</p>

@(`(:code ($ alu-stv))`)

<p>The semantically significant fields here are @(':inputs') and @(':outputs')
-- in particular, @(':parents'), @(':short'), @(':labels'), and @(':long') (not
provided here) are just for documentation.  You can see the documentation
generated for this STV <see topic='@(url alu-test-vector)'>here</see>.</p>

<p>The first column of @(':inputs') gives the Verilog signal names of
inputs we wish to set.  The first column after that describes what happens in
the first phase of simulation: we set the clock to 1.  All the other signals
have an underscore, meaning we don't set them.  The phase after that, we set
the clock to 0 and set the @('abus') and @('bbus') inputs to variables @('a')
and @('b').</p>

<blockquote>Aside: Why do this on the clock-low phase rather than the
clock-high phase?  For @('posedge') flipflops, the updated value depends on the
input to the flop during the previous clock-low phase; nothing much of
consequence happens during the clock-high phase.</blockquote>

<p>The next phase, the clock is set to 1; the next one, back to 0 and the
opcode is set to variable @('op'), and after that we toggle the clock twice
more and are done.</p>

<p>The outputs have a similar format to the inputs, except that instead of
naming input variables we're naming output names.  So our output line says that
we record the value of signal @('out') in variable @('res') at phase 6 of our
simulation (one cycle after the opcode goes in).</p>

<p>The main effect of this @(see defsvtv) form is to create a
constant (accessed via a 0-ary function, @('(alu-test-vector)') that encapsulates
the given simulation pattern in a set of svex expressions, one for each output
variable, expressed in terms of the input variables.  So the resulting
@('(alu-test-vector)') from the @('defsvtv') above contains an svex expression for
@('res') as a combinational function in terms of @('a'), @('b'), and @('op').
You can examine this function by looking at the @('outexprs') field of the SVTV
structure:</p>

@(`(:code ($ alu-function-examine))`)

<p>Warning: This  prints a  lot of  output --  around 11,000  lines.  We  get a
somewhat nicer result if we  apply some @(see rewriting) before displaying
it:</p>

@(`(:code ($ alu-function-examine-rw))`)

<p>This is small enough to fit on two screens, and its meaning can be teased
out with some patience and reference to the @(see svex) @(see functions).</p>

<h4>Running tests using the simulation pattern</h4>

<p>The basic way to run tests using the simulation pattern we've defined is
with @(see svtv-run):</p>

@(`(:code ($ alu-example-1))`)

<p>This takes as input an alist binding the STV input variables to integers.
Note that we don't have to do anything for the clock; its behavior was defined
by the @('defsvtv') form, and it has no input variable.  The output from
@('svtv-run') is just another alist binding the output variable(s) to their
values -- here, our ALU has added 3 and 5 and returned 8.</p>

<p>Sometimes you may need to drive a wire to X, Z, or some combination of X/Z
with good Boolean values.  The biggest difference in usage between svex's STV
functions and esim's is the notation used for this.  Svex constants, including
those in @('defsvtv') forms and in the inputs and outputs of @('svtv-run'), are
always expressed as @(see 4vec) objects.  Essentially, if your input or output
value is an all-Boolean vector, then you can just represent it as a single
integer.  If not, it is then a pair of integers; see @(see 4vec) for more
details. Examples:</p>

@(`(:code ($ alu-x-input))`)
@(`(:code ($ alu-zx-input))`)

<p>When we do an @('svtv-run'), we are essentially applying @(see svex-eval) to
interpret the output expressions examined above.</p>

<h4>Viewing Simulation Waveforms</h4>

<p>To debug these simulations in more depth, we can use @('svtv-debug'), which
produces a VCD waveform that can be examined in a waveform viewer such as
gtkwave:</p>

@(`(:code ($ alu-debug))`)

<p>To continue, next see @(see proofs-with-stvs).</p>")


#||
; Note that you can also supply X values, and that X values can propagate
; through the circuit.  See 4vec for how Xes are represented; this produces a
; result that is all Xes.

(svtv-run (alu-test-vector)
         `((op . ,*op-plus*)
           (a  . ,(4vec-x))
           (b  . 3)))

; But an X doesn't always flow through the circuit.  For instance, the COUNT
; operation pays no attention to its B bus, so you can send an X in, and still
; it will count the 8 bits of A:

(svtv-run (alu-test-vector)
         `((op . ,*op-count*)
           (a  . #xFF00)
           (b  . ,(4vec-x))))

; Leaving out an input is equivalent to setting it to X:

(svtv-run (alu-test-vector)
         `((op . ,*op-count*)
           (a  . #xFF00)))
||#


; -----------------------------------------------------------------------------
;
;                     PROVING SOME CORRECTNESS PROPERTIES
;
; -----------------------------------------------------------------------------

(def-saved-event alu-simple-proof
  (gl::def-gl-thm alu16-adds
    :hyp (and (alu-test-vector-autohyps)
              (equal op *op-plus*))
    :concl (equal (cdr (assoc 'res (svtv-run (alu-test-vector)
                                             (alu-test-vector-autoins))))
                  (loghead 16 (+ a b)))
    :g-bindings (alu-test-vector-autobinds)))

(def-saved-event alu-simple-proof-opt
  (gl::def-gl-thm alu16-adds-opt
    :hyp (and (alu-test-vector-autohyps)
              (equal op *op-plus*))
    :concl (equal (cdr (assoc 'res (svtv-run (alu-test-vector)
                                             (alu-test-vector-autoins))))
                  (loghead 16 (+ a b)))
    :g-bindings (gl::auto-bindings (:nat op 3)
                                   (:mix
                                    (:nat a 16)
                                    (:nat b 16)))))

(local
 (make-event
  (b* ((event-form '(gl::def-gl-thm alu16-counts
                      :hyp (and (alu-test-vector-autohyps)
                                (equal op *op-count*))
                      :concl (equal (cdr (assoc 'res (svtv-run (alu-test-vector)
                                                               (alu-test-vector-autoins))))
                                    (logcount a))
                      :g-bindings (alu-test-vector-autobinds)))
       ((mv er & state)
        (make-event event-form)))
    (value (and er
                `(progn (table saved-forms-table 'alu-count-ctrex ',event-form)
                        (value-triple :ok)))))))

(local
 (def-saved-nonevent alu-debug-ctrex
   (svtv-debug (alu-test-vector)
               `((a . #xb7b3)
                 (op . ,*op-count*))
               :filename "alu-ctrex.vcd")
   :return state
   :writep t))

(def-saved-event satlink-include
  (include-book "centaur/gl/bfr-satlink" :dir :system))

(def-saved-event satlink-configure
  (local (progn (defun my-satlink-config ()
                  (declare (Xargs :guard t))
                  (satlink::make-config
                   :cmdline "glucose -model"
                   :verbose t
                   :mintime 1))
                (defattach gl::gl-satlink-config my-satlink-config))))

(def-saved-event gl-use-satlink
  (local (gl::gl-satlink-mode)))

(def-saved-event tshell
  (value-triple (acl2::tshell-start)))

(def-saved-event alu-simple-proof-sat
  (gl::def-gl-thm alu16-counts-sat
    :hyp (and (alu-test-vector-autohyps)
              (equal op *op-plus*))
    :concl (equal (cdr (assoc 'res (svtv-run (alu-test-vector)
                                             (alu-test-vector-autoins))))
                  (loghead 16 (+ a b)))
    :g-bindings (alu-test-vector-autobinds)))

(def-saved-event bdd-mode
  (local (gl::gl-bdd-mode)))






(deftutorial proofs-with-stvs
  :parents (sv-tutorial)
  :short "How to do proofs about hardware models using STVs and GL."
  :long "

<p>Part of the @(see sv-tutorial). Previous section: @(see
stvs-and-testing).</p>

<h4>Simple STV Proofs</h4>

<p>Now that we've set up a symbolic test vector (in the previous section), we
can try some proofs about it.  Here is a simple example:</p>

@(`(:code ($ alu-simple-proof))`)

<p>In addition to defining the STV @('(alu-test-vector)') itself, the @('defsvtv')
form from the previous section also defines  the following macros/functions:</p>

<ul>
<li>@('(alu-test-vector-autohyps)') expands to a function that checks type hypotheses for the input variables -- in this case,</li>
@({
 (and (unsigned-byte-p 16 b)
      (unsigned-byte-p 16 a)
      (unsigned-byte-p 3 op))
 })
<li>@('(alu-test-vector-autoins)') expands to a function that takes the input variables as inputs and outputs an alist binding the variable symbols to their corresponding values, i.e.,</li>
@({
 (list (cons 'A a)
       (cons 'B b)
       (cons 'OP op))
 })

<li>@('(alu-test-vector-autobinds)') expands to a form that creates a set of
appropriate GL bindings for the input variables; in this case,</li>
@({
  (gl::auto-bindings (:nat b 16)
                     (:nat a 16)
                     (:nat op 3))
 })

<li>@('(alu-test-vector-alist-autohyps x)'), like @('(alu-test-vector-autohyps)'),
checks the type of the inputs, but instead of taking the input variables, it
takes an alist @('x') that binds the variable symbols to their values.</li>

<li>@('(alu-test-vector-alist-autoins x)'), like @('(alu-test-vector-autoins)'), checks
the type of the inputs, but instead of taking the input variables, it takes an
alist @('x') that binds the variable symbols to their values.  (Why would you
want to do this?  It can be useful in decomposition proofs, which we'll get to
later in the tutorial.)</li>

</ul>

<p>So the @('def-gl-thm') form above is checking that when the inputs @('a'),
@('b') are appropriately-sized integers and @('op') is set to the addition
opcode, the @('res') computed by the STV is (the low 16 bits of) the sum of
@('a') and @('b').</p>

<h4>Optimizing BDD Order</h4>

<p>The automatically-generated GL bindings don't always produce a good BDD
order (in fact, they don't really try to).  So in order to improve performance
when doing BDD-based proofs (which is the default), you may make your own @(see
gl::auto-bindings) form, or even create a hand-optimized variable ordering.
For example, the following version of the same theorem proves more quickly
because it uses a good interleaving of the variables of the @('a') and @('b')
inputs:</p>

@(`(:code ($ alu-simple-proof-opt))`)

<p>In addition to proving properties, it's also important to be able to debug
properties that don't prove.  For example, the @('COUNT') opcode has a bug in
our design.  Attempting the following proof exposes the bug:</p>

@(`(:code ($ alu-count-ctrex))`)

<p>Instead of completing the proof, this prints out some counterexamples.  It
can then be useful to plug one of these into @('svtv-debug') in order to get a
waveform:</p>

@(`(:code ($ alu-debug-ctrex))`)

<h4>Using SAT rather than BDDs</h4>

<p>If you have a SAT solver such as Glucose installed and set up in your path,
you may set up GL to use AIG/SAT based reasoning rather than BDDs, as
follows:</p>
@(`(:code ($ satlink-include))`)
@(`(:code ($ satlink-configure))`)
@(`(:code ($ gl-use-satlink))`)
@(`(:code ($ tshell))`)

<p>First, we need to include an additional book to get the SAT machinery.
Next, we create a satlink configuration that says how to run our SAT solver of
choice -- here, we use Glucose with its \"-model\" option so that it outputs a
satisfying assignment we can use -- and attach the function specifying that
configuration to GL's satlink-config stub, @('gl::gl-satlink-config').
@('Gl-satlink-mode') puts GL in a mode that uses AIGs to express Boolean
functions and SAT to solve them, and finally we need to start a tshell (see
@(see acl2::tshell)) to allow the SAT solver to be executed (the
@('value-triple') just makes it an event form that can be in a certifiable
book).  After this setup, any GL theorem we submit will be attempted using this
AIG/SAT strategy.  One advantage to this approach is that BDD ordering doesn't
matter, so using the automatically generated GL bindings is generally OK.</p>

<p>To go back to BDD mode, you just need to do:</p>

@(`(:code ($ bdd-mode))`)

<p>To continue, next see @(see decomposition-proofs).</p>")

(make-event
 (cons 'progn (recreate-saved-forms-table (table-alist 'saved-forms-table (w state)))))
