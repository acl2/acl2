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
  :parents (svtv)
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

<p>@('defsvtv$') provides a drop-in replacement for the old @(see defsvtv)
utility. However, it drops support for the @(':state-machine'),
@(':keep-final-states'), and @(':keep-all-states') options because these are
geared toward using a pipeline-style SVTV as a cycle FSM, which is now
deprecated since we have such FSMs as separate structures.  Similarly,
@('defsvtv$-phasewise') is a drop-in replacement for @(see defsvtv-phasewise),
also producing an SVTV structure but using a different user input syntax to
supply the pipeline steps.</p>

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

<p>Various utilities are provided for dumping VCD files showing runs of the design:</p>

<ul>

<li>@('svtv-data-debug-pipeline') dumps a VCD showing the run of the
pipeline, given the assignments for the pipeline variables.</li>

<li>@('svtv-data-debug-cycle-fsm') dumps a VCD showing a cycle FSM run, given
an initial state environment and a list of input environments for the cycles to
be run.</li>

<li>@('svtv-data-debug-phase-fsm') dumps a VCD showing a phase FSM run, given
an initial state environment and a list of input environments for the phases to
be run.</li>

<li>@('fsm-debug') dumps a VCD from a @('base-fsm') data structure; it is used
as a helper function for the above.</li>

</ul>

<p>Additionally, the @(see svtv-chase) read-eval-print loop can be initialized
using the following entry points:</p>

<ul>

<li>@('svtv-data-chase-pipeline') sets up the chase environment to reflect a
run of the pipeline, given the assignments for the pipeline variables</li>

<li>@('svtv-data-chase-cycle-fsm') sets up the chase REPL for a cycle FSM run, given
an initial state environment and a list of input environments for the cycles to
be run.</li>

<li>@('svtv-data-chase-phase-fsm') sets up the chase REPL for a phase FSM run,
given an initial state environment and a list of input environments for the
phases to be run.</li>

</ul>

<p>Note that for now, the moddb and aliases sub-stobjs must be recreated in
order to run these.  However, this only needs to be done once; if the correct
moddb and aliases have already been computed, the argument @(':skip-flatten t')
may be given, saving this step, which might take several seconds otherwise.</p>

<p>A common debug loop to be stuck in is finding the right set of signals to
set in order to get a hardware module to produce a desired result.  In each
iteration, we find a signal that wasn't previously driven (by examining a VCD,
say), then add the signal to the pipeline and try again.  To support fast
iteration on this debug loop, we have three utilities based on the svtv-data
stobj.  These will set up the svtv-data stobj with a cycle FSM if it is not
already loaded.  They each take as input a @('defsvtv$') or
@('defsvtv$-phasewise') form or some form that macroexpands to one:</p>

<ul>

<li>@('svtv-data-debug-defsvtv$') performs a concrete run of the given
pipeline, producing an output environment; it takes a @('defsvtv$') or
@('defsvtv$-phasewise') form and keyword arguments @(':env') (an environment
binding the input variables of the SVTV) and @(':svtv-data') (to optionally
provide a congruent stobj to use in place of @('svtv-data')).</li>

<li>@('svtv-data-debug-defsvtv$') dumps a VCD for the pipeline; it takes a
@('defsvtv$') or @('defsvtv$-phasewise') form and keyword arguments
@(':env') (an environment binding the input variables of the SVTV),
@(':filename') (for the VCD file), @(':skip-flatten'), and the stobjs
@('svtv-data'), @('moddb'), @('aliases'), @('vcd-wiremap'), and
@('vcd-vals').  (The stobjs do not need to be initialized.)</li>

<li>@('svtv-data-chase-defsvtv$') sets up a @(see svtv-chase) REPL for a run of
the pipeline; it takes a @('defsvtv$') or @('defsvtv$-phasewise') form and
keyword arguments @(':env') (an environment binding the input variables of the
SVTV), @(':skip-flatten'), and the stobjs @('svtv-data'), @('moddb'),
@('aliases'), and @('svtv-chase-data'). (The stobjs do not need to be
initialized.)</li>
         
</ul>

")



(defxdoc defsvtv$
  :parents (svex-stvs svtv-data)
  :short "Create an SVTV, storing and possibly using intermediate results from
          the @('svtv-data') stobj."
  :long "<p>@('Defsvtv$') is a drop-in replacement for @(see defsvtv), with a
few differences.</p>

<p>The implementation is different in that it operates on the @(see svtv-data)
stobj, storing intermediate results such as the flattening and phase
composition in the stobj.  Subsequent invocations of @('defsvtv') may reuse
these results without recomputing them if they use the same design.</p>

<p>A few features are removed, namely those that overload the SVTV to represent
a state machine rather than just a pipeline.  We removed these because the new
preferred way to deal with FSMs is with a @('base-fsm') or @('svtv-fsm') object
rather than an @('svtv') object.</p>

<p>One added feature is the ability to define a clock cycle separately from the
pipeline timing diagram.  The clock cycle is given by the @(':cycle-phases')
keyword argument, which must be a list of @('svtv-cyclephase') objects.  A
typical clock cycle has two phases where the clock is low in one and high in
the other, and input signals are provided and outputs read in the clock-low
phase:</p>

@({
 :cycle-phases
 (list (make-svtv-cyclephase :constants '((\"clock\" . 0))
                             :inputs-free t
                             :outputs-captured t)
       (make-svtv-cyclephase :constants '((\"clock\" . 1))))
 })

<p>In this case, the phases of the provided timing diagram refer to the clock
cycles of the design rather than individual clock phases.</p>

<p>The default, when the @(':cycle-phases') argument is not provided, is for
all clock phases to be explicitly represented in the timing diagram; this
corresponds to the following cycle-phases value:</p>
@({
 :cycle-phases
 (list (make-svtv-cyclephase :constants nil
                             :inputs-free t
                             :outputs-captured t))
 })

")


(defxdoc defsvtv$-phasewise
  :parents (svex-stvs svtv-data)
  :short "Create an SVTV using the @(see defsvtv-phasewise) syntax, storing and
          possibly using intermediate results from the @('svtv-data') stobj."
  :long "<p>@('Defsvtv$-phasewise') is a drop-in replacement for @(see
defsvtv-phasewise).  It differs from @('defsvtv-phasewise') analogously to how
@('defsvtv$') differs from @('defsvtv'); see @(see defsvtv$).</p>
")



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
