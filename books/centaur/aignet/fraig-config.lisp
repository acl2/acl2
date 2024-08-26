; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2017 Centaur Technology
; Copyright 2024 Intel Corp.
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

(include-book "gatesimp")
(include-book "centaur/fty/deftypes" :dir :System)

(local (xdoc::set-default-parents fraig))


(fty::deftagsum fraig-output-type
  :parents (fraig)
  :short "Object describing how the @(see fraig) transform should treat a range of output nodes"
  :long "<p>Certain ways of configuring the fraig transform need user input in
the form of a list of nodes/literals to be treated specially:</p>

<ul>

<li>We can narrow down the allowed equivalences to be examined by providing a
set of pairs of literals as the initial equivalence candidates.</li>

<li> We can specify nodes that we don't want to simplify</li>

<li>We can specify nodes for which we don't want to simplify any nodes that
depend on them.</li>

</ul>
<p>Perhaps we can add more such behaviors in the future.</p>

<p>A @('fraig-output-type') object describes how to treat some range of outputs.</p>

<ul>

<li>@('(fraig-output-type-simplify)') is the default sort of output, which is
simplified unless other output map entries or configurations say not to.  That
is, all nodes in the fanin cone of such an output are simplified unless they
are required not to be simplified by a do-not-simplify-fanouts marker (see
below).</li>

<li>@('(fraig-output-type-ignore)') means we don't specifically simplify these
outputs.  The fanin cone of such an output may be simplified anyway, to the
extent that it intersects the fanin cones of outputs to be simplified.</li>

<li>@('(fraig-output-type-do-not-simplify-fanouts)') signifies that the outputs
in the given range are nodes that should be avoided by the fraig transform --
that is, their fanin cones may be simplified but they and their fanout cones
will not be.</li>

<li>@('(fraig-output-type-initial-equiv-classes)') signifies that instead of
starting with all nodes in one equivalence class as usual, we instead start
with equivalence classes formed by joining corresponding pairs of the outputs
in this range (which should be an even number count). That is, if this range of
outputs starts at @('k') and has count @('2i'), then nodes will only be
considered perhaps equivalent if there is a path from one to the other in the
undirected graph whose edges are given by pairs of outputs @('(j+k, j+i+k)')
for @('0 <= j < i').  This is useful in cases where we know what nodes are
likely to be equivalent to each other, and we don't want to waste time trying
to prove equivalences that aren't among these candidates.</li>

</ul>


"
  (:simplify ;; ((count natp :rule-classes :type-prescription))
   nil)
  (:ignore nil)
  (:do-not-simplify-fanouts ;; ((count natp :rule-classes :type-prescription))
   nil)
  (:initial-equiv-classes ;; ((count natp :rule-classes :type-prescription))
   nil))

(fty::defalist fraig-output-type-map :key-type symbolp :val-type fraig-output-type :true-listp t)


(fty::defprod fraig-config
  ((initial-sim-words posp "Number of 32-bit simulation words per node for initial simulation" :default 4)
   (initial-sim-rounds posp "Number of times to simulate initially" :default 10)
   (sim-words posp "Number of 32-bit simulation words per node for simulation during fraiging" :default 1)
   (ipasir-limit acl2::maybe-natp "Ipasir effort limit" :default 8)
   (ipasir-recycle-count acl2::maybe-natp "Number of callbacks after which to recycle the solver" :default 1000)
   (ctrex-queue-limit acl2::maybe-natp "Limit to number of counterexamples that may be queued before resimulation" :default 16)
   (ctrex-force-resim booleanp "Force resimulation of a counterexample before checking another node in the same equivalence class" :default t)
   (final-force-resim booleanp
                      "Force resimulation of any pending counterexamples at the
end of the sweep. Useful when a subsequent FRAIG transform will use (with the
output-types option) this transform's resulting equivalence classes (stored
with the save-candidate-equivs-as option) (see @(see fraig))."
                      :default nil)
   (random-seed-name symbolp "Name to use for seed-random, or NIL to not reseed the random number generator")
   (outs-only booleanp "Only check the combinational outputs of the network" :default nil)
   (miters-only booleanp
                "Instead of starting with all nodes in a single equivalence
class and refining them with random simulation, start with equivalence classes
consisting of the mitered outputs of the network. That is, whenever an output contains
an XOR under a top-level conjunction, put the inputs of that XOR into an
equivalence class.  This is useful for checking equivalences when you know
exactly which nodes in a network are supposed to be equivalent, because it
avoids checking false equivalences."
                :default nil)
   (delete-class-on-fail
    natp :default 0
    "If set greater than 0, then if a SAT check fails, don't try to prove any
     of the other equivalences in that node's equiv class (delete the class), unless
     it was the constant class.  If set greater than 1, delete the class even if
     it's the constant class (drastic!).")
   (gatesimp gatesimp-p :default (default-gatesimp)
             "Gate simplification parameters.  Warning: This transform will do
              nothing good if hashing is turned off.")
   (level-limit natp :default 0
                "If set greater than 0, we'll only try to check the current
node's candidatae equivalence if its level (see @(see aignet-record-levels)) is
less than or equal to the level limit.")

;;    (n-outputs-are-initial-equiv-classes
;;     acl2::maybe-natp
;;     :default nil
;;     "If set to a natural number N, then the initial equiv classes will be built
;; by joining pairs of outputs @('(i, i+N)'). The range of @('i') depends on the
;; setting of initial-equiv-classes-last.  If nonnil, then @('i') ranges from
;; @('numOuts-2N') to @('numOuts-N-1'); if nil, then it ranges from @('0') to
;; @('N-1').  Larger equivalence classes may be built by pairing the same node
;; more than once.  Combinational equivalence is preserved for all outputs.  Not
;; compatible with @(':miters-only') or @('output-map').")
;;    (initial-equiv-classes-last booleanp :default nil
;;                                "See the n-outputs-are-initial-equiv-classes option.")
   (output-types fraig-output-type-map :default nil ;;`((:fraig-remaining-equiv-classes . ,(fraig-output-type-initial-equiv-classes)))
               "If this is empty, then all outputs are treated as nodes to
simplify.  Otherwise, it gives a mapping from output range names (see @(see
aignet-output-ranges)) to @(see fraig-output-type) objects, determining how to
treat the named ranges of objects. (This depends on the output-types argument
to the transform, which determines which range of outputs corresponds to each
output range name.) The default output type is
@('(fraig-output-type-simplify)').")

   (save-candidate-equivs-as symbolp :default nil ;; :fraig-remaining-equiv-classes
                          "If this is a nonnil symbol and this transform is
called with strict-count nonnil (i.e. only preserving a fixed number of primary
outputs, not full combinational equivalence), then at the end of the SAT sweep,
a new output range (see @(see aignet-output-ranges)) of the given name is added
to the resulting AIG, encoding the remaining equivalence classes that were
neither proved nor disproved. If an output range of that name already exists,
then it is replaced.  This can be consumed in a subsequent FRAIG transform by
mapping this symbol to @('(fraig-output-type-initial-equiv-classes)') in the
output-types map. This can speed up that subsequent FRAIG transform since it
doesn't need to re-disprove candidate equivalences for which we have already
found counterexamples.")

   (remove-candidate-equivs symbolp :default nil
                            "If this is a nonnil symbol and this transform is
called with strict-count nonnil (i.e. only preserving a fixed number of primary
outputs, not full combinational equivalence), then at the end of the SAT sweep,
the given output range will be deleted. This is intended to be used to remove a
set of candidate equivalences that is no longer useful (e.g. because this is
the last FRAIG transform in the sequence), but it will in fact remove any
output range."))

  :parents (fraig comb-transform)
  :short "Configuration object for the @(see fraig) aignet transform."
  :tag :fraig-config)

(defconst *fraig-default-config* (make-fraig-config))
