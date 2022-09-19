; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "xdoc/top" :dir :system)

(defxdoc svtv-data
  :parents (svex-stvs)
  :short "A stobj encapsulating an SVTV and the steps used in creating it, from
the initial SV design to (potentially) a pipelined symbolic run."
  :long "

<p>An svtv-data stobj holds an SV design and several other pieces of data, such
as finite-state machine and symbolic pipeline objects, tied to that design.
These data objects are constrained by the abstract stobj invariant to have
certain relationships among each other and to the design.  For example, one
invariant states that if the @('phase-fsm-validp') field is true, then the
@('phase-fsm') object is equivalent to the composition of the normalized signal
assignments from the @('flatten') field, which in turn (if @('flatten-validp')
is true) is a certain function of the original design.  Similarly, the
@('cycle-fsm') and @('pipeline') fields are known to equivalent to certain
functions of the other fields.  These relations are designed so that, for
example, a pipeline can be used to prove a lemma about a cycle FSM to aid in a
larger proof.</p>

<h3>Beta Warning</h3>

<p>This is relatively new and the structure/interface of the stobj may still
change in backward-incompatible ways.  Howeer, at least the high-level tools
@('defsvtv$') and @('defcycle') should retain their same interfaces.</p>


<h3>Steps</h3>

<p>The stobj contains data members that trace the following steps:</p>

<ul>

<li>The initial SV design is <em>flattened</em>, producing the @('flatten')
field, a product of type @('flatten-res') containing signal assignments, fixup
assignments, constraints, and a variable declaration map.</li>

<li>The flattened design is <em>normalized</em>, producing the @('flatnorm')
field, a product of type @('flatnorm-res') containing finalized signal
assignments and constraints and a signal delay map.</li>

<li>The flattened, normalized design is composed into a finite state machine
representation and stored in the @('phase-fsm') field.  This contains the
nextstate functions and the values for each signal in terms of previous states
and primary input.</li>

<li>The user may attach names to certain signals, which are processed into a
@('namemap').</li>

<li>The user may define a <em>cycle</em> as a composition of one or
more (usually two) phases of the phase FSM into a new FSM.</li>

<li>The user may define a <em>pipeline</em> as a run of several cycles of the
cycle FSM in which certain inputs are given symbolic or concrete values at
particular times and certain outputs are read at particular times.</li>

</ul>

<h3>High-level tools</h3>

<p>@('defsvtv$') provides a drop-in replacement for the old @(see defsvtv) and
@(see defsvtv-phasewise) utilities. However, it drops support for the
@(':state-machine'), @(':keep-final-states'), and @(':keep-all-states') options
because these are geared toward using a pipeline-style SVTV as a cycle FSM,
which is now deprecated since we have such FSMs as separate structures. The
primary function for running concrete simulations of an SVTV and reasoning
about SVTVs is still @(see svtv-run).</p>

<p>@('defcycle') produces a cycle FSM from a design, given a name mapping and
phase specification.  This is intended to replace the use of @('defsvtv') with
the @(':state-machine') option.</p>

<p>A nice thing about these two tools is that they don't need to repeat work
whose results have already been stored in the svtv-data stobj.  For example, to
create two SVTV objects representing pipelines built on the same module with
the same clock cycle phases, only the pipeline composition needs to be
repeated, not the flattening, phase-FSM composition, or clock-cycle
composition.</p>

<h3>Lower-level tools</h3>

<p>The fields of the @('svtv-data') stobj may be updated directly, but there
are stringent guard requirements to prevent the invariants from being broken.
Because these guard obligations can be somewhat baroque, we define several
helper utilities that are lower level than @('defsvtv$') and @('defcycle')
but with easier guard requirements than the core updaters.  To ease these guard
requirements, these functions invalidate any fields that might violate
invariants.</p>

<p>@('svtv-data-set-design') initializes the design of the @('svtv-data')
object to the given design.  If this differs from the current design, it
invalidates the @('flatten') and @('namemap') fields.</p>

<p>@('svtv-data-maybe-compute-flatten') computes the @('flatten') field from
the current design, unless that field is already valid.  It invalidates
all the other derived fields since they all depend on the flatten field.</p>

<p>@('svtv-data-maybe-compute-flatnorm') computes the @('flatnorm') field,
requiring that @('flatten') is valid.</p>

<p>@('svtv-data-maybe-compute-namemap') computes the namemap from the given
user namemap, requiring that @('flatten') is valid and invalidating the
@('pipeline') since it is derived from the namemap.</p>

<p>@('svtv-data-maybe-compute-phase-fsm') computes the @('phase-fsm') field,
requiring that @('flatnorm') is valid.  It invalidates the @('cycle-fsm').</p>

<p>@('svtv-data-maybe-compute-cycle-fsm') computes the @('cycle-fsm') field
given a list of phase specifications, requiring that the @('phase-fsm') is
valid.  It invalidates the @('pipeline').</p>

<p>@('svtv-data-maybe-compute-pipeline') computes the @('pipeline') given a
@('pipeline-setup') object.  It requires that the @('phase-fsm') and
@('cycle-fsm') fields are valid.</p>

<p>The following functions apply SVEX @('rewriting') to various fields:</p>
<ul>
<li>svtv-data-rewrite-phase-fsm</li>
<li>svtv-data-rewrite-cycle-fsm</li>
<li>svtv-data-rewrite-pipeline</li>
</ul>

<h3>Export and Import</h3>

<p>The svtv-data stobj is not saved by certify-book.  If you want to create an
svtv-data object in one book and include it elsewhere, we provide the utility
@('def-svtv-data-export/import').  This saves (almost all) the current contents
of the svtv-data stobj (or some congruent stobj) as a constant function, with
theorems stating that this function satisfies the svtv-data invariant.  It also
produces a function which imports that object back into an svtv-data object,
recomputing the parts (the @('moddb') and @('aliases') sub-stobjs) that
couldn't be saved.</p>

<h3>Debugging and VCD dumping</h3>

<p>Various utilities are provided for dumping VCD files showing runs of the
design.  There are three families of such utilities:</p>

<ul>
<li>@('Debug') functions dump a VCD waveform file for a given concrete simulation</li>
<li>@('Chase') functions enter a read-eval-print loop with commands to navigate through the drivers of signals under a given concrete simulation in order to trace root causes of a signal's value</li>
<li>@('Run') functions run a concrete simulation and returns the values of certain signals at certain times.</li>
</ul>

<p>We'll describe the functions of the @('debug') family.  The @('chase') and
@('run') families have basically analogous functions, which we list after that.</p>

<ul>

<li>@('svtv-debug$') takes an SVTV object created by @(see defsvtv$), recreates
the svtv-data stobj for that SVTV to the extent necessary up to the phase-fsm
stage, and dumps a VCD showing the run of the pipeline given the assignments
for the pipeline variables.</li>

<li>@('svtv-data-debug-defsvtv$') takes a @(see defsvtv$) form and dumps a VCD
given the assignments for the pipeline variables.  An advantage of this utility
is that you don't need to run the full @('defsvtv$') (in particular, compose
the pipeline) first, cutting down on a sometimes significant part of the debug
loop when fine-tuning the signals to set and extract.</li>

<li>@('svtv-data-debug-pipeline') operates on an existing svtv-data stobj,
dumping a VCD to a file given assignments for the pipeline variable.</li>

<li>@('svtv-data-debug-cycle-fsm') dumps a VCD showing a cycle FSM run, given
an initial state environment and a list of input environments for the cycles to
be run.</li>

<li>@('svtv-data-debug-phase-fsm') dumps a VCD showing a phase FSM run, given
an initial state environment and a list of input environments for the phases to
be run.</li>

</ul>

<p>The corresponding functions for the @('chase') family:</p>

<ul>
<li>@('svtv-chase$')</li>
<li>@('svtv-data-chase-defsvtv$')</li>
<li>@('svtv-data-chase-pipeline')</li>
<li>@('svtv-data-chase-cycle-fsm')</li>
<li>@('svtv-data-chase-phase-fsm')</li>
</ul>

<p>And the corresponding functions for the @('run') family:</p>

<ul>
<li>@('svtv-run$') (though @('svtv-run') is almost always a better choice)</li>
<li>@('svtv-data-run-defsvtv$')</li>
<li>@('svtv-data-run-pipeline')</li>
<li>@('svtv-data-run-cycle-fsm')</li>
<li>@('svtv-data-run-phase-fsm')</li>
</ul>

<p>Note: These functions don't replace @(see svtv-run) for reasoning purposes;
@('svtv-run$') should always produce the same result as @('svtv-run') but is in
program mode and is likely slower.</p>


")



(defxdoc defsvtv$
  :parents (svex-stvs svtv-data)
  :short "Create an SVTV structure for some simulation pattern of a hardware design."
  :long "
<p>See the @(see sv-tutorial) and the parent topic @(see svex-stvs) for
higher-level discussion; here, we provide a reference for the arguments.</p>

<ul>

<li>@(':design') or @(':mod') provides the SVEX @(see design) object containing
the hierarchical hardware model.  One or the other of @(':design') or @(':mod')
should be given, but not both; they mean exactly the same thing.</li>

<li>@(':phases') describes what happens at each phase, or each clock cycle if
the @(':cycle-phases') argument (below) is used: what inputs and overrides are
set and what outputs are sampled.  Additionally, each phase may be given a
label for documentation purposes.  As an alternative to @(':phases'), arguments
@(':inputs'), @(':overrides'), and @(':outputs') may be provided at the top
level with a timing diagram format, described below; this is the same format as
was used in the previous version @('defsvtv') and ESIM's @('defstv'), but using
@(':phases') is recommended since it tends to be easier to edit.  The format of
the @(':phases') argument is described in its own section below.</li>

<li>@(':cycle-phases') optionally describes a clock cycle. Its value must be a
list of @('svtv-cyclephase') objects.  A typical clock cycle has two phases
where the clock is low in one and high in the other, and input signals are
provided and outputs read in the clock-low phase (this is appropriate for
typical positive-edge-triggered flip-flops):

@({
 :cycle-phases
 (list (make-svtv-cyclephase :constants '((\"clock\" . 0))
                             :inputs-free t
                             :outputs-captured t)
       (make-svtv-cyclephase :constants '((\"clock\" . 1))))
 })

In this case, the phases of the provided timing diagram refer to the clock
cycles of the design rather than individual clock phases.
@({})
The default, when the @(':cycle-phases') argument is not provided, is for
all clock phases to be explicitly represented in the timing diagram; this
corresponds to the following cycle-phases value:
@({
 :cycle-phases
 (list (make-svtv-cyclephase :constants nil
                             :inputs-free t
                             :outputs-captured t))
 })
</li>

<li>@(':parents'), @(':short'), @(':long'), and @(':labels') pertain to
documentation; if any of @(':parents'), @(':short'), or @(':long') are given
then additional xdoc will also be generated to show a timing diagram.
@(':labels') may only be used without @(':phases') (alongside @(':inputs'),
@(':outputs') and @(':overrides')), which has its own syntax for providing
phase labels; if provided, these label the phases in that timing diagram.</li>

<li>@(':monotonify') is T by default; it says whether to rewrite certain SVEX
constructs that are not bitwise monotonic with respect to Xes into monotonic
ones.  Generally this is desirable; this monotonicity is used when generalizing
SVTV theorems for use in proof decomposition; see @(see decomposition-proofs).</li>

<li>@(':simplify') is T by default; it can be set to NIL to avoid rewriting the
output svex expressions after composing the pipeline.</li>

<li>@(':pre-simplify') is T by default, and controls rewriting the svex
expressions at earlier stages -- after flattening, phase FSM composition, and
cycle FSM composition.</li>

<li>@(':pipe-simp') is NIL by default and must be a @(see svex-simpconfig-p)
object.  It determines the level of SVEX simplification used on-the-fly when
composing cycle formulas together to compute the pipeline formulas.</li>

<li>@(':cycle-simp') is NIL by default and must be a @(see svex-simpconfig-p)
object.  It determines the level of SVEX simplification used on-the-fly when
composing phase formulas together to compute the clock cycle formula, when
using the @(':cycle-phases') feature.</li>

<li>@(':define-macros') is T by default; it controls whether macros
@('<svtv>-autoins'), @('<svtv>-autohyps'), etc. are created</li>

<li>@(':define-mod') is NIL by default; it controls whether a 0-ary function
@('<svtv>-mod') is defined, returning the SV design for the SVTV.  This is used
by some legacy utilities such as @(see svtv-debug) and @(see svtv-chase), but
these are deprecated in favor of @(see svtv-debug$) and @(see
svtv-chase$).</li>

<li>@(':phase-config') is the config object for the phase FSM
computation. Currently it is mainly an advanced feature useful for tweaking
which signals are conditionally overridden in the phase and cycle FSMs.  By
default all internally driven signals are conditionally overridden; this makes
it so that it is fast to recompute the pipeline when changing the phases, even
if overrides are modified.  But there may be some cases where it is better to
allow either only a few specific signals to be overridden, or else disallow a
few particular signals from being overridden.</li>

<li>@(':clocks') may be set to a list of clock input variable names (often just
a singleton). If this is provided, then an analysis will be done before
computing the phase FSM to determine what other signals are derived clocks, and
avoid providing conditional overrides on these derived clock signals.  It may
be important to avoid building conditional overrides on such signals because
they can prevent important simplifications that reduce the size of the
expressions produced.  Additionally, if these clock signals are set in the
@(':phases') argument and not in the @(':cycle-phases'), their assignments in
each phase will initially be used to simplify the nextstate before composing
the pipeline.</li>

<li>@(':phase-scc-limit') affects the phase FSM constructed in cases where
there is an apparent combinational loop at the bit level.  An apparent
combinational loop is equivalent to a strongly connected component in the
signal dependency graph; when such an SCC exists, self-composing those signals'
assignments N times where N is the size of the SCC is guaranteed to reach a
fixed point if all expressions are X-monotonic.  However, in practice this can
result in very large expressions, and in practice a few such self-composition
iterations is all that is necessary.  Setting the phase-scc-limit to a natural
number (instead of the default, NIL, meaning no limit) restricts the number of
self-composition steps to that limit.  Warning: If you build an SVTV with a
current phase-scc-limit, then change the phase-scc-limit and try to build it
again, that won't be sufficient to force the phase FSM to be recomputed.  You
can force this with
 @({(update-svtv-data->phase-fsm-validp nil svtv-data).})</li>

</ul>

<h3>@(':phases') argument format</h3>

<p>The following example shows the main features of the @(':phases') argument
format:</p>

@({
   :phases
   (;; Phase 0:
    (:label p
     :inputs ((\"clk\" 0 :toggle 1)  ;; will toggle each phase until end or until reassigned
              (\"start\" 1)))

    ;; Phase 4:
    (:delay 4 ;; number of phases since last one listed
     :label q
     :inputs ((\"cntl\" cntl4 :hold t)) ;; will hold this value until end or until reassigned
     :overrides ((\"inst.subinst.internalsig\" internal4)
                 ;; syntax for combined conditional override/output
                 (\"inst.subinst.decompsig\" decompsig :cond decompsig-ovr :output decompsig)
                 ;; old syntax for conditional override
                 (\"inst.subinst.decompsig\" (testsig testsig-ovr))))
 
    ;; Phase 6:
    (:delay 2
     :label r
     :inputs ((\"late\" late6))
     :outputs ((\"early\" early6)))
 
    ;; Phase 8:
    (:delay 2
     :label s
     :inputs ((\"cntl\" _)) ;; release previous held value
     :outputs ((\"inst.subinst.interesting\" interesting8))))
 })

<p>The format of this argument is a list of individual phases, which are
keyword-value lists with the following keywords recognized:</p>


<ul>

<li>@(':delay'): Number of phases since the previous one in the list,
defaulting to 1.  Must be positive.  (Note: If the first phase in the list has
a delay of 1, its assignments occur on the first phase that is to be simulated.
Phase 0 is skipped, in some sense.)</li>

<li>@(':label'): Optional name of the phase, for documentation purposes.</li>

<li>@(':inputs'): Input signals to be assigned a value at that phase.  Entries are described below.</li>

<li>@(':overrides'): Internal signals to be overridden to some value at that phase.  Entries are described below.</li>

<li>@(':outputs'): Signals to be read and their values stored in variables at that phase.</li>

</ul>

<p>The format for @(':outputs') is simply a list of entries of the form</p>
@({
  (signal-name variable-name)
 })
<p>where signal-name is a string giving the real hierarchical name in the
design and variable-name is a symbol.</p>

<p>The format for @(':inputs') is a list of entries of the form:</p>
@({
 (signal-name setting [ :hold t-or-nil | :toggle nphases ])
 })
<p>Setting can be one of:</p>
<ul>
<li>a 4vec constant, that is, an integer or a pair @('(upper . lower)'), both integers</li>
<li>a don\'t-care indicator, which is a symbol whose name is \"_\", \"-\", or \"\&amp;\" in any package</li>
<li>a variable, i.e. any other non-Boolean, non-keyword symbol.</li>
</ul>

<p>The @(':hold') keyword, if set to t, indicates that this assignment is
valid for all subsequent phases until the same signal is set again.</p>

<p>The @(':toggle') keyword, if set to t or a positive integer @('nphases'),
indicates that the signal will be held and toggled every @('nphases') phases,
where @('t') is the same as 1.  It is only valid (for now) if the setting is a
constant.</p>

<p>Note: Don\'t use the special symbol @('~'), which is what you'd use for
@(':toggle') in the original @('defsvtv').</p>

<p>The format for @(':overrides') is similar to that of inputs, but adds two
additional keyword variables:</p>

<ul>
<li>@(':cond'), if specified, gives an override condition value (a variable or
4vec constant), making this a conditional override.  This means bits of the
signal corresponding to 1-bits of the override condition are overridden and
take the value of the corresponding bits of the override value (@('setting')
field).</li>
<li>@(':output'), if specified, gives an output variable for the same signal.
This output will be assigned the non-overridden value of the signal.</li>
</ul>

<p>The @('setting') field can also take one additional form @('(value test)'),
which is another way of specifying a conditional override (this may not be used
along with the @(':cond') keyword).  Here @('test') is the override condition
and @('value') is the override value.</p>

<p>The @(':toggle') and @(':hold') keywords still apply to overrides and
conditional overrides: @(':hold') means that test and value both apply to
subsequent phases, and @(':toggle') means that test applies to subsequent
phases and value is toggled.</p>

<h3>Legacy stimulus/sampling specification format</h3>

<p>Previous versions of this utility -- @('defsvtv') and ESIM's
@('acl2::defstv') -- used another format for specifying stimulus and output
sampling.  Instead of a @(':phases') argument, these utilities took
@(':inputs'), @(':outputs'), @(':overrides'), and @(':labels').  The format of
the first three is described in @(see svtv-stimulus-format). The @(':labels')
argument is a list of symbols giving names to each phase for documentation
purposes.  Note that when using the @(':cycle-phases') argument, each phase
listed in @(':labels') or in an @(':inputs'), @(':outputs'), or @(':overrides')
entry actually refers to a clock cycle.</p>


")


(defxdoc defsvtv$-phasewise
  :parents (svex-stvs svtv-data)
  :short "(Deprecated) Create an SVTV using the @(see defsvtv-phasewise) syntax, storing and
          possibly using intermediate results from the @('svtv-data') stobj."
  :long "<p>The formerly different syntax of @('defsvtv$-phasewise') is now
allowed in @(see defsvtv$), and so @('defsvtv$-phasewise') is now just an alias
for @('defsvtv$').</p>")



(defxdoc defcycle
  :parents (svtv-data)
  :short "Create a FSM from a design and a clock cycle specification, along with a signal name list."
  :long "<p>Here is an example invocation of @('defcycle'):</p>

@({
 (defcycle my-clock-cycle
    :design *my-sv-design*
    :phases 
    (list (make-svtv-cyclephase :constants '((\"my-clock\" . 0))
                                :inputs-free t
                                :outputs-captured t)
          (make-svtv-cyclephase :constants '((\"my-clock\" . 1))))
    :names
     '((input0       . \"my-input\")
       (internal-val . \"my-modinst[3].my_internal_signal\")
       (output       . \"my-output\"))
    :rewrite-phases t
    :rewrite-cycle t
    :cycle-simp t
    :stobj svtv-data)
 })

<p>This form creates a clock cycle FSM for the given design, setting the signal
@('\"my-clock\"') to 0 in the first phase (at which time input signals are
provided and outputs captured) and 1 in the second phase.  It also provides
short names @('input0'), @('internal-val'), and @('output') for some signals
that are given as hierarchical Verilog names.  The rest of the arguments shown
are shown as their default values:</p>

<ul>

<li>@(':rewrite-phases') if @('t') applies SVEX @(see rewriting) to the
composed single phase FSM </li>

<li>@(':rewrite-cycle') if @('t') applies SVEX rewriting to the composed cycle
FSM</li>

<li>@(':cycle-simp') should be a @('svex-simpconfig') object, that is, @('t'),
@('nil'), or a natural number, controlling simplification that is applied while
composing the cycle. Here @('nil') signifies that no simplification is
performed, @('t') signifies that constants are propagated and cheap
simplifications applied to concatenation, select, and shift operations, and a
natural number says that full rewriting will be applied during composition with
that number as the iteration limit (the @('clk') argument of
@('svex-rewrite-fncall')).</li>

<li> @(':stobj') allows the event to use another stobj congruent to
@('svtv-data') rather than @('svtv-data') itself.</li>
</ul>
")
