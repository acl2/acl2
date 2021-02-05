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
geared toward using a pipeline-style SVTV as a cycle FSM which is now
deprecated.</p>

<p>@('defcycle') produces a cycle FSM from a design, given a name mapping and
phase specification.  This is intended to replace the use of @('defsvtv') with
the @(':state-machine') option.</p>

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
all the other derived fields since.</p>

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

<h3>VCD dumping</h3>

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

<p>Note that for now, the moddb and aliases sub-stobjs must be recreated in
order to run these, but this may be fixed soon.</p>

")
