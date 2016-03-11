; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")
(include-book "aig-cnf")
(include-book "aiger")
(include-book "aignet-absstobj")
(include-book "aig-sim")
(include-book "arrays")
(include-book "bit-lemmas")
(include-book "cnf")
(include-book "construction")
(include-book "copying")
(include-book "eval")
(include-book "from-hons-aig-fast")
(include-book "from-hons-aig")
(include-book "litp")
(include-book "portcullis")
(include-book "prune")
(include-book "refcounts")
(include-book "semantics")
(include-book "snodes")
(include-book "to-hons-aig")
(include-book "types")
(include-book "vecsim")

(xdoc::add-resource-directory "aignet" "images")

(defxdoc aignet
  :parents (acl2::boolean-reasoning)
  :short "An efficient, @(see stobj)-based And-Inverter Graph (AIG)
representation for Boolean functions and finite-state machines."

  :long "<h3>Background</h3>

<p>At its most basic, an AIG is a DAG whose nodes are either AND gates,
outputs, or inputs.  Outputs have 1 descendant (fanin), ANDs have 2, and inputs
have none.  An edge may point to an AND or an input, but not an output.  Each
edge has a Boolean attribute signifying whether it is negated or not.  Such an
AIG is <b>combinational</b>: it represents a stateless circuit that produces
outputs that are Boolean functions of its inputs.</p>

<p>A <b>sequential</b> AIG extends this to directly model circuits with
internal state that responds to inputs that are changing over time.  Here the
input and outputs to the AIG are divided into two categories, <i>register</i>
and <i>primary</i>.  The sequential semantics for an AIG depend on an initial
state and a series of inputs:</p>

<ul>

<li>Initially, assign initial values to the register output nodes.</li>

<li>Every cycle:

   <ul>
    <li>copy values from register outputs to corresponding register inputs</li>
    <li>assign values to the primary inputs</li>
    <li>compute values of AND gates in topological order</li>
    <li>compute values of primary outputs and register inputs.</li>
   </ul></li>

</ul>

<p>A sequential AIG can be viewed as a combinational AIG by ignoring the
distinctions between its register and primary nodes.  But confusingly:</p>

<ul>
<li><color rgb='#0000ff'>Combinational inputs</color> = primary inputs + register <b>outputs</b></li>
<li><color rgb='#ff0000'>Combinational outputs</color> = primary outputs + register <b>inputs</b></li>
</ul>

<p>To see this visually:</p>

<img src='res/aignet/combinational.png'/>

<p>That is: from the perspective of the combinational logic for the current
cycle, the register outputs (the current values in the registers) are consumed
just like the primary inputs.  Similarly, the register inputs (the values the
registers will become in the next cycle) are emitted just like primary
outputs.</p>



<h3>The Aignet Library</h3>

<p>The Aignet library, found in @('centaur/aignet'), is intended to provide an
<b>efficient</b> implementation of sequential AIGs.</p>

<p>We represent an AIG network as an @(see abstract-stobj).  This means that
the Common Lisp implementation and its logical story are substantially
different.  This is true of concrete stobjs as well, where access/update
functions are logically defined in terms of @(see nth) and @(see update-nth)
but implemented as array accesses.  But it is especially true for Aignet!</p>

<ul>

<li>Logically&mdash;for reasoning about the AIG network and proving AIG
algorithms are correct&mdash;the AIG network is viewed as just a list of
<i>nodes</i>.  Understanding these definitions is a first step toward
successfully using Aignet; see @(see representation).</li>

<li>For execution, the AIG is actually represented with various @(see stobj)
arrays, largely styled after the <a
href='http://www.eecs.berkeley.edu/~alanmi/abc/'>ABC</a> package.  Since the
implementation is kept hidden, most users can feel free to skim or entirely
skip the details in @(see aignet-impl).</li>

</ul>

<p>The low-level @(see base-api) connects these logical and executable
definitions together, and provides the most basic operations for initializing
the network, adding nodes to it, inspecting the contents of the nodes, and so
on.  The rest of Aignet is built on top of this API.  Generally speaking,
accesses are implemented as constant-time, and updates as amortized
constant-time (since there may be array resizes).</p>



<p>BOZO describe the rest of the library</p>


<h3>Comparison with Hons-AIGs</h3>

<p>Our focus on efficiency makes Aignet more difficult to work with and reason
about than the simpler <see topic='@(url aig)'>Hons-AIG library</see>.  On the
other hand, Aignet can sometimes be much faster than Hons-AIGs.  For a good
introduction with a more detailed comparison of Hons-AIGs and Aignet, see:</p>

<ul>

<li>Jared Davis and Sol Swords.  <a
href='http://dx.doi.org/10.4204/EPTCS.114.8'>Verified AIG Algorithms in
ACL2</a>.  ACL2 Workshop 2013.  May, 2013.  EPTCS 114.  Pages 95-110.</li>

</ul>")

(xdoc::order-subtopics aignet
                       (representation base-api semantics))


(defxdoc representation
  :parents (aignet)
  :short "Logical representation of the AIG network."

  :long "<p>We now describe the logical view of the @('aignet') stobj.  This
representation serves as the foundation for reasoning about AIG algorithms and
provides the logical basis for the @(see base-api).</p>

<p>Note that these definitions are used for reasoning but typically do not get
run.  For details about the executable representation, see @(see aignet-impl)
instead, but most users should not need to think about those details.</p>


<h3>The AIG Network</h3>

<p>Logically, @('aignet') is simply a list of @(see node)s, where a node is of one of
five types distinguished by a particular symbol in its CAR, called its @(see
sequential-type) or <b>stype</b>.  Depending on its stype, a node contains 0 or
more fields that encode the and-inverter graph.  We will discuss the meanings
of these fields later:</p>

<table>
<tr><th>    Node Kind        </th><th>    Representation              </th></tr>

<tr><td>    Primary input    </td><td>    @('(:pi)')                  </td></tr>
<tr><td>    Register         </td><td>    @('(:reg)')                 </td></tr>
<tr><td>    AND gate         </td><td>    @('(:gate fanin0 fanin1)')  </td></tr>
<tr><td>    Next state       </td><td>    @('(:nxst fanin regid)')    </td></tr>
<tr><td>    Primary output   </td><td>    @('(:po fanin)')            </td></tr>
</table>

<p>There is one other stype, @(':const'), but generally no node in the list
actually has constant type; instead, the end of the list implicitly contains a
constant node.  Thus, the number of nodes in the aignet is @('(+ 1 (len
aignet))').  However, we use a different function, @(see node-count), for this
purpose so that we can feel free to use rules that would be expensive to
generally apply to @('len').</p>

<p>Logically, an @('aignet') is constructed by simply consing new nodes onto
it.  A newly-created or cleared @('aignet') is just @('nil'), and contains only
the implicit constant node.</p>


<h3>Node IDs and Node Lookups</h3>

<p>Access to @('aignet') nodes is primarily by ID, which is simply the number
of nodes that were in the @('aignet') when the node was added.  The implicit
constant node has ID 0, the first node added to an empty aignet has ID 1, and
so on.  Thus, the ID of a node in an aignet is the length (node-count) of the
suffix of the aignet beginning at that node.</p>

<p>To look up a node by ID, we use the function @(see lookup-id), which returns
the unique <b>suffix</b> of length ID, or the final cdr of the aignet if the ID
is out of bounds:</p>

@(def lookup-id)

<p>Note that although this looks like a quadratic algorithm, it doesn't matter
because this is never actually executed.  Real ID lookups are carried out by
array accesses.</p>


<h3>Node Operations, Fanins, Register IDs</h3>

<p>Gate, next state, and primary output nodes have some fields:</p>

<ul>
<li>A gate has two fanins (representing the inputs to the AND gate),</li>
<li>A primary output or next-state has one fanin (the function of the output or next-state), and</li>
<li>A next-state also contains an ID that should point to a register node.</li>
</ul>

<p>The fanins are @(see literal)s, which combine a node ID with a negation flag
as a single natural number: @('(+ (* 2 id) neg)'), where neg is 1 or 0.</p>

<p>There are many functions for constructing and accessing the various kinds of
nodes.  See @(see logical-node) for a reference.  Note that these node-related
functions are not meant to be executed; they exist only for reasoning.</p>


<h3>IO Numbers and IO Lookups</h3>

<p>Input, output, and register nodes also have an IO number distinct from their
ID.  This is their index among nodes of their type, so, e.g., the first primary
input node added has input number 0, etc.</p>

<p>The IO number of a node can be determined by @(see stype-count), which
counts the number of nodes of some type:</p>

@(def stype-count)

<p>Typically @('stype-count') is called by @(see lookup-stype), which looks up
the @('n')th input/output/register node by its IO number, by searching for the
unique node of the given type with the given IO number:</p>

@(def lookup-stype)

<p>Again these functions look terribly inefficient, but are implemented as
array accesses.</p>

<p>An final type of lookup operation allows us to find the next-state node
for a given register ID:</p>

@(def lookup-reg->nxst)


<h3>Lowest-Level API</h3>

<p>The functions described above&mdash;@('node-count'), @('lookup-id'),
@('stype-count'), @('lookup-stype') and @('lookup-reg->nxst')&mdash;and
the other functions for operating on logical nodes, e.g., the functions
described under @(see logical-node) and 

provide the
logical basis for reasoning about most kinds of access to the aignet.</p>

<p>However, note that these functions are typically not used directly.
Instead, see the wrappers that implement Aignet's @(see base-api).</p>")


(defsection aignet-impl
  :parents (representation)
  :short "Implementation details of Aignet's representation for execution.
Since these details are hidden, most users can safely skip this section."

  :long "<p>For background see @(see aignet) and @(see representation).</p>

<p>We now describe the actual implementation of the @('aignet') stobj for
execution. Our use of @(see abstract-stobj)s means that these details are
completely hidden from reasoning about @('aignet') and have nothing at all to
do with the logical view of an @('aignet') as a list of logical nodes.  You
should not need to know these details when writing new Aignet algorithms or
when understanding existing Aignet code!</p>


<h3>Node Array</h3>

<p>The Aignet network consists mainly of an array of nodes representing a
topologically sorted DAG.</p>

<p>Each node in the graph has an ID, which is a natural number that can be used
to look up that node in the array.  However, often our functions take arguments
that may be a node or its negation; we encode this as a @(see literal), as
2*ID+NEG, where NEG is 1 signifying negated or 0 signifying not negated.</p>

<p>One arbitrary well-formedness condition that we impose on all Aignet
networks is that it must have a unique constant-false node with index 0.
Therefore, the literal 0 is constant-false (the constant-false node, not
negated), and the literal 1 is constant-true (the constant-false node,
negated).</p>

<p>Information about each node is stored in the node array as two consecutive
32-bit numbers, and the node ID corresponds to its position in the array.  That
is, the two array indices of a node are 2*ID and 2*ID+1.</p>


<h3>Node Encoding</h3>

<p>The two 32-bit values contained at these locations are broken down into two
30-bit data slots and four extra bits.  Three of the four extra bits encode the
<b>type</b> of the node, and the last extra bit encodes the <b>phase</b> of the
node, which is its value when all inputs/registers are 0.  The meaning of the
30-bit data slots depends on the type of node; in some cases it stores a
literal.</p>

<p>The encoding is broken down, least-significant bits first, as follows:</p>

<table>
<tr><th>  Size  </th><th>   Contents             </th></tr>
<tr><td>  2     </td><td>   Combinational type   </td></tr>
<tr><td>  30    </td><td>   Data slot 0          </td></tr>
<tr><td>  1     </td><td>   Register flag        </td></tr>
<tr><td>  1     </td><td>   Phase                </td></tr>
<tr><td>  30    </td><td>   Data slot 1          </td></tr>
</table>

<p>The combinational types are encoded as follows:</p>

<table>
<tr><th>  Encoding  </th><th>   Meaning          </th></tr>
<tr><td>  0         </td><td>   Constant false   </td></tr>
<tr><td>  1         </td><td>   And gate         </td></tr>
<tr><td>  2         </td><td>   Input            </td></tr>
<tr><td>  3         </td><td>   Output           </td></tr>
</table>

<p>The register flag only applies to combinational inputs/outputs; it should be
0 for constants/gates (but should also be ignored in those cases).  Note that
the polarity here can be very <b>confusing</b>:</p>

<ul>
<li>An input with the register flag set is a register output,</li>
<li>An output with the register flag set is a register input.</li>
</ul>

<p>The reason for this is described in @(see aignet): the output of a register
is an input to the combinational logic, and the input to a register is an
output from the combinational logic.</p>

<p>So there are, in total, six types of objects, encoded as follows:</p>

<table>
<tr><th>   Name             </th><th>  Combinational Type  </th><th>   Register Flag   </th></tr>
<tr><td>   Constant         </td><td>        0             </td><td>        -          </td></tr>
<tr><td>   And gate         </td><td>        1             </td><td>        -          </td></tr>
<tr><td>   Primary Input    </td><td>        2             </td><td>        0          </td></tr>
<tr><td>   Register Output  </td><td>        2             </td><td>        1          </td></tr>
<tr><td>   Primary Output   </td><td>        3             </td><td>        0          </td></tr>
<tr><td>   Register Input   </td><td>        3             </td><td>        1          </td></tr>
</table>


<h3>Restrictions and Interpretation</h3>

<p>Only objects with combinational types 0, 1, and 2&mdash;constants, gates,
and combinational inputs&mdash;may be fanins (descendants) of AND or
combinational output objects; combinational outputs (type 3) may not.</p>

<p>The meanings of the two 30-bit data slots vary based on the type:</p>

<ul>

<li><b>Constants</b>.  Both data 0 slots are meaningless; they should be set to
0 and ignored.</li>

<li><b>AND gates</b>.  Data 0 and 1 are literals encoding the fanins to the
gate.  To ensure an obvious topological ordering, the ID part of each literal
must be less than the gate ID.</li>

<li><b>Combinational inputs</b>.  Data 0 is ignored and should be 0.  Fanin 1
gives the PI or register number, sequentially assigned and unique among
PI/registers.</li>

<li><b>Primary outputs</b>.  Data 0 is the fanin (literal) of the output, whose
ID must (for topological ordering) be less than the output node ID.  Data 1 is
the output number.</li>

<li><b>Register inputs</b>.  Data 0 is the fanin (literal) of the register,
whose ID must (for topological ordering) be less than this node's ID.  Fanin 1
is the ID of the corresponding register output, which must also be less than
this node's ID.  (The register number of the RI is the register number of the
corresponding RO.)</li>

</ul>


<h3>Register Considerations</h3>

<p>Having separate register input and output objects is somewhat awkward in
terms of saying when a network is well-formed.  In some sense, it's not
well-formed unless every RO has a corresponding RI.  But the RIs can't be added
until their input cones are built, and we'd like to be able to say the network
is well-formed in some sense while it is being built.  So while an RO has no
corresponding RI, we will say it is simply not updated: its value under
sequential evalutation remains the same at each frame.  A separate predicate
can check that this isn't the case, but we won't generally require this for
guards etc.</p>

<p>Furthermore, for convenience, we also allow RIs with fanin 1 set to 0.  In
this case they are not proper RIs because they do not connect to an RO, and
they have no register number.  They are also basically irrelevant to any
sequential computation, because no RI gets updated with their previous
value.</p>

<p>We require that each RI object occur later (have a larger ID) than its
corresponding RO object.  This allows a couple of conveniences:</p>

<ul>

<li>There is a function for adding an RO and another function for adding an RI
which connects it to an existing RO.  If we allowed RIs to occur first, then
we'd need an additional pair of functions, for adding an unconnected RI and for
adding an RO connected to an RI.  Maybe we could avoid this by separately
allowing RO/RIs to be connected, but this seems knotty in terms of
well-formedness.</li>

<li>When doing a sequential simulation or similar operation that involves
repeated sweeps across the AIG nodes, an RO node will be reached before the
corresponding RI's previous value is overwritten.  So we don't need an
addtional step of copying RI to RO values between frames.</li>

</ul>

<p>Also, a strategy that might alleviate any inconvenience due to needing to
add the RO before the RI: at the point of adding the RI, check whether the
RO already exists and add it first if not.</p>


<h3>Other Arrays</h3>

<p>An Aignet network is designed to have objects added one at a time without
later modification.  That is, new objects may be added, but existing objects
are not changed.  The object array itself (along with its size) contains enough
information to fully replicate the network; in this sense, all other
information recorded is auxiliary.</p>

<p>For efficient lookups, we do also keep arrays of inputs, outputs, and
registers.</p>

<p>The input and output arrays simply hold the IDs of inputs/outputs in the
order that they were added (as described above, each input/output object
records its input/output numbers, i.e. the index in the input/output array that
points back to it).</p>

<p>The register array is a bit more complicated, because there are typically
two nodes (register input and register output) associated with each register.
Each entry in the register array contains the ID of either a register input or
output.  If it is a register input, then the register is incomplete, i.e. its
output hasn't been added yet.  If it is a register output, then we have a
complete register: the register array points to the register output node, which
points to the register input node, which has the index in the register
array.</p>


<h3>Source Code</h3>

<p>For the full details, see the source code in @('aignet-exec.lisp') or
@('aignet-exec-thms.lisp').</p>")


(defsection semantics
  :parents (aignet)
  :short "The precise combinational and sequential semantics of Aignet
networks, and also definitions of certain kinds of AIG network equivalence."

  :long "<p>The combinational semantics of aignets is given by the function
ID-EVAL.  This takes an aignet, a node ID, and assignments to the primary
inputs and registers, and produces the value of that ID under those
assignments.</p>

<p>The sequential semantics of aignets is given by the function LIT-EVAL-SEQ.
This takes an aignet, a time frame number, a literal, a 2D bit array assigning
values to the primary inputs on each frame, and an initial assignment to the
registers.  It produces the value of that literal under those sequential
assignments.</p>

<p>The following theorem describes @('lit-eval-seq') in terms of combinational
evaluation:</p>

 @(thm lit-eval-seq-in-terms-of-lit-eval)

<p>Here, @('frame-regvals') is a function that creates a register value array
from the previous frame's sequential evaluations of the next-state nodes
corresponding to each register.  That is, to get the value of a literal at a
particular timeframe, first evaluate the register next-states at the previous
timeframe, then combinationally evaluate the literal with the resulting
register values and the current frame's input values.</p>

")





#||

(ld
 "top.lisp")

(include-book
 "xdoc/save" :dir :system)

(defsection acl2::boolean-reasoning
  :parents (acl2::top)
  :short "placeholder")

(xdoc::save "./my-manual" :redef-okp t :zip-p nil)

||#
