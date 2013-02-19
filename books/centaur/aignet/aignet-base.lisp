; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")
(include-book "idp")
(include-book "litp")
(include-book "cutil/defmvtypes" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)
(include-book "str/natstr" :dir :system)
(include-book "tools/defmacfun" :dir :system)
(include-book "tools/stobj-frame" :dir :system)
(include-book "tools/clone-stobj" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "add-ons/hash-stobjs" :dir :system)
(include-book "std/ks/two-nats-measure" :dir :system)
(include-book "centaur/misc/2d-arr" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "centaur/misc/arrays" :dir :system)
(include-book "centaur/misc/bitarr" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "centaur/misc/iter" :dir :system)
(include-book "centaur/misc/natarr" :dir :system)
(include-book "centaur/misc/nth-equiv" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)
(include-book "centaur/misc/stobj-swap" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "clause-processors/instantiate" :dir :system)
(include-book "clause-processors/stobj-preservation" :dir :system)
(include-book "clause-processors/generalize" :dir :system)
(include-book "clause-processors/find-subterms" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable sets::double-containment)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           sets::double-containment
                           sets::sets-are-true-lists
                           make-list-ac)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index)))

(local (defthmd equal-1-to-bitp
         (implies (and (not (equal x 0))
                       (bitp x))
                  (equal (equal x 1) t))
         :hints(("Goal" :in-theory (enable bitp)))))

;; sigh
(defmacro mksym (pkg &rest concats)
  `(intern-in-package-of-symbol
    (concatenate 'string . ,concats)
    ,pkg))

(defthmd redundant-update-nth
  (implies (and (< (nfix n) (len x))
                (equal v (nth n x)))
           (equal (update-nth n v x)
                  x))
  :hints(("Goal" :in-theory (enable nth update-nth))))

(defmacro const-type () 0)
(defmacro gate-type () 1)
(defmacro in-type () 2)
(defmacro out-type () 3)

(defxdoc aignet
  :short "AIGNET is an and-inverter graph implementation: a representation for
both Boolean functions and finite-state machines."
  :long
  "<p>An and-inverter graph (AIG) at its most basic is a DAG whose nodes are either
AND gates, outputs, or inputs.  Outputs have 1 descendant, ANDs have 2, and
inputs have none.  An edge may point to an AND or an input, but not an output.
Each edge has a Boolean attribute signifying whether it is negated or not.</p>

<p>We call this a combinational AIG.  AIGNET, following packages like ABC,
implements a sequential AIG, by dividing the inputs and outputs into two
categories, \"register\" and \"primary\".  A sequential AIG can be seen as a
combinational AIG by just ignoring these distinctions; when we wish to ignore
the register/primary distinctions we refer to <i> combinational inputs </i>
and <i> combinational outputs </i>.  Confusingly, combinational inputs of
the register type are called <i>register outputs</i> -- it is an output
from a register, but are read (like inputs) by the combinational logic -- and
combinational outputs of the register type are called <i>register
inputs</i> -- they are inputs to registers, but are written (like outputs)
by the combinational logic.  Register inputs, like primary outputs, have one
descendant and may not be the descendant of another node; register outputs,
like primary inputs, have no descendants and may be the descendant of another
node.</p>

<p>Sequential semantics for an AIG network can be summarized as follows:<br/>
 Initially, assign initial values to the register output nodes.<br/>
 Every cycle,<br/>
  <ul><li>assign values to the primary inputs</li>
      <li>copy values from register outputs to corresponding register inputs</li>
      <li>compute values of AND gates in topological order</li>
      <li>compute values of primary outputs and register inputs.</li></ul></p>

<p>During the period of computing values for ANDs/primary outputs/register inputs,
the circuit is basically treated as combinational -- register outputs and
primary inputs are treated identically, as are primary outputs and register
inputs.</p>

<p>Usage and implementation are discussed in the subtopics.</p>")

(defsection aignet-impl
  :parents (aignet)
  :short "Implementation details of AIGNET"
  :long
  "<p>The AIGNET network consists mainly of an array of nodes representing a
topologically sorted DAG described in @(see aignet).  This uses a stobj called
@('AIGNET').</p>

<p>Each node in the graph has an ID, a natural number that can be used to look
up that node in the array.  However, often our functions take arguments that
may be a node or its negation; we encode this as a <i>literal</i>, as 2*ID+NEG,
where NEG is 1 signifying negated or 0 signifying not negated.</p>

<p>One arbitrary well-formedness condition that we impose on all AIGNET
networks is that it must have a unique constant-false node with index 0.
Therefore, the literal 0 is constant-false (the constant-false node, not
negated), and the literal 1 is constant-true (the constant-false node,
negated).</p>

<p>Information about each node is stored in the node array as two consecutive
32-bit numbers, and the node ID corresponds to its position: the two array
indices of a node are 2*ID and 2*ID+1.  The two 32-bit values contained at
these locations are broken down into two 30-bit data slots and four extra bits.
Three of the four extra bits encode the type of the node, and the last extra
bit encodes the phase of the node, which is its value when all inputs/registers
are 0.  The meaning of the 30-bit data slots depends on the type of node; in
some cases it stores a literal.</p>

<p>The encoding is broken down, least-significant bits first, as:</p>
<ul>
<li>2 bits:   combinational type</li>
<li>30 bits:  data slot 0</li>
<li>1 bit:    register flag</li>
<li>1 bit:    phase</li>
<li>30 bits:  data slot 1.</li></ul>

<p>The combinational types are:</p>
<ul>
<li>0:   constant false</li>
<li>1:   gate</li>
<li>2:   input</li>
<li>3:   output</li></ul>

<p>The register flag only applies to combinational inputs/outputs; it should be
0 for constants/gates (but should also be ignored in those cases).  An input
with the register flag set is a register output, and an output with the
register flag set is a register input.  (Remember that the output of a register
is an input to the combinational logic, and the input to a register is an
output from the combinational logic.)</p>

<p>So there are, in total, six types of object, encoded as follows:
<code>
Name               Type encoding          Register flag
Constant                 0                    -
AND gate                 1                    -
Primary input            2                    0
Register output          2                    1
Primary output           3                    0
Register input           3                    1.
</code></p>

<p>Only objects with type 0, 1, 2 -- constants, gates, and combinational inputs
-- may be fanins (descendents) of AND or combinational output objects;
combinational outputs (type 3) may not.</p>

<p>The meanings of the two 30-bit data slots vary based on the type:</p>

<p>Constant: both data 0 and 1 are meaningless, and should be set to 0 but
ignored</p>

<p>AND gates: data 0 and 1 are literals encoding the fanins to the gate.  The
ID part of each literal must be less than the gate ID.</p>

<p>Combinational inputs: data 0 is ignored and should be 0, and fanin 1 gives
the PI or register number, sequentially assigned and unique among
PI/registers.</p>

<p>Primary outputs: data 0 is the fanin (literal) of the output, whose ID must
be less than the output node ID.  Data 1 is the output number.</p>

<p>Register inputs: data 0 is the fanin (literal) of the register, whose ID
must be less than this node's ID.  Fanin 1 is the ID of the corresponding
register output, which must also be less than this node's ID.  (The register
number of the RI is the register number of the corresponding RO.)</p>

<p>Having separate register input and output objects is somewhat awkward in
terms of saying when a network is well-formed.  In some sense, it's not
well-formed unless every RO has a corresponding RI.  But the RIs can't be
added until their input cones are built, and we'd like to be able to say
the network is well-formed in some sense while it is being built.  So when
an RO has no corresponding RI, we will say it is simply not updated -- its
value under sequential evalutation remains the same at each frame.  A
separate predicate can check that this isn't the case, but we won't
generally require this for guards etc.  Furthermore, for convenience we
also allow RIs with fanin 1 set to 0 -- in this case, they are not proper
RIs because they do not connect to an RO, and they have no register
number.  They are also basically irrelevant to any sequential computation,
because no RI gets updated with their previous value.</p>

<p>We require that each RI object occur later (have a larger ID) than its
corresponding RO object.  This allows a couple of conveniences:</p>
<ul>
<li>there is a function for adding an RO and another function for adding an
  RI which connects it to an existing RO.  If we allowed RIs to occur first,
  then we'd need an additional pair of functions, for adding an unconnected
  RI and for adding an RO connected to an RI.  Maybe we could avoid this by
  separately allowing RO/RIs to be connected, but this seems knotty in terms
  of well-formednes.</li>
<li>When doing a sequential simulation or similar operation that involves
  repeated sweeps across the AIG nodes, an RO node will be reached before
  the corresponding RI's previous value is overwritten.  So we don't need an
  addtional step of copying RI-&gt;RO values between frames.</li></ul>
<p>Also, a strategy that might alleviate any inconvenience due to needing to
add the RO before the RI: at the point of adding the RI, check whether the
RO already exists and add it first if not.</p>

<p>An AIGNET network is designed to have objects added one at a time without
later modification.  That is, new objects may be added, but existing
objects are not changed.  The object array itself (along with its size)
contains enough information to fully replicate the network; in this sense,
all other information recorded is auxiliary.  But we do also keep arrays
of inputs, outputs, and registers.  The input and output arrays simply
hold the IDs of inputs/outputs in the order that they were added (as
described below, each input/output object records its input/output
numbers, i.e. the index in the input/output array that points back to
it).  The register array is a bit more complicated, because there are
typically two nodes (register input and register output) associated with
each register.  Each entry in the register array contains the ID of either
a register input or output.  If it is a register input, then the register
is incomplete, i.e. its output hasn't been added yet.  If it is a register
output, then we have a complete register: the register array points to the
register output node, which points to the register input node, which has
the index in the register array.</p>")

(defsection aignet-case
  (defmacro aignet-case (type &key const gate in out)
    `(case ,type
       (1 ,gate)
       (2 ,in)
       (3 ,out)
       (otherwise ,const)))

  (defmacro aignet-seq-case (type regp &rest keys)
    ;; we can't use keyword args because "pi" can't be used as a formal
    ;; const gate
    ;; (pi 'nil pi-p)
    ;; (ro 'nil ro-p)
    ;; (ri 'nil ri-p)
    ;; (po 'nil po-p)
    ;; (ci 'nil ci-p)
    ;; (co 'nil co-p))
    (declare (xargs :guard (and (keyword-value-listp keys)
                                (not (and (assoc-keyword :ci keys)
                                          (or (assoc-keyword :pi keys)
                                              (assoc-keyword :ro keys))))
                                (not (and (assoc-keyword :co keys)
                                          (or (assoc-keyword :po keys)
                                              (assoc-keyword :ri keys)))))))
    `(case ,type
       (1 ,(cadr (assoc-keyword :gate keys)))
       ,(if (assoc-keyword :ci keys)
            `(2 ,(cadr (assoc-keyword :ci keys)))
          `(2 (if (int= 1 ,regp)
                  ,(cadr (assoc-keyword :ro keys))
                ,(cadr (assoc-keyword :pi keys)))))
       ,(if (assoc-keyword :co keys)
            `(3 ,(cadr (assoc-keyword :co keys)))
          `(3 (if (int= 1 ,regp)
                  ,(cadr (assoc-keyword :ri keys))
                ,(cadr (assoc-keyword :po keys)))))
       (otherwise ,(cadr (assoc-keyword :const keys))))))

;; (local (defthmd bitp-by-range
;;          (implies (natp x)
;;                   (equal (< 1 x)
;;                          (not (bitp x))))
;;          :hints(("Goal" :in-theory (enable bitp)))))

;; (local (defthm bitp-by-range-limit
;;          (implies (natp x)
;;                   (equal (< 1 x)
;;                          (not (bitp x))))
;;          :hints(("Goal" :in-theory (enable bitp)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local (defthm equal-1-to-bitp
;;          (implies (not (equal x 0))
;;                   (equal (equal x 1)
;;                          (bitp x)))
;;          :hints(("Goal" :in-theory (enable bitp)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))




(defsection aignet

  (defstobj aignet

    (num-ins     :type (integer 0 *) :initially 0)
    (num-outs    :type (integer 0 *) :initially 0)
    (num-regs    :type (integer 0 *) :initially 0)
    (num-gates   :type (integer 0 *) :initially 0)
    (num-regins  :type (integer 0 *) :initially 0)
    ;; num-nodes = the sum of the above + 1 (const)
    (num-nodes    :type (integer 0 *) :initially 1)

; For space efficiency we tell the Lisp to use unsigned-byte 32's here, which
; in CCL at least will result in a very compact representation of these arrays.
; We might change this in the future if we ever need more space.  We try not to
; let this affect our logical story to the degree possible.
;
; The sizes of these arrays could also complicate our logical story, but we try
; to avoid thinking about their sizes at all.  Instead, we normally think of
; these as having unbounded length.  In the implementation we generally expect
; that:
;
;    num-nodes <= |gates|
;    num-outs    <= |outs|
;    num-regs    <= |regs|
;
; But if these don't hold we'll generally just cause an error, and logically we
; just act like the arrays are unbounded.

    (nodes       :type (array (unsigned-byte 32) (1))
                :initially 0
                :resizable t)
    (ins        :type (array (and (unsigned-byte 32) (satisfies idp)) (0))
                :initially 0
                :resizable t)
    (outs       :type (array (and (unsigned-byte 32) (satisfies idp)) (0))
                :initially 0
                :resizable t)
    (regs       :type (array (and (unsigned-byte 32) (satisfies idp)) (0))
                :initially 0
                :resizable t)

    :inline t
    ;; BOZO do we want to add some notion of the initial state of the
    ;; registers, or the current state, or anything like that?  And if
    ;; so, what do we want to allow it to be?  Or can we deal with that
    ;; separately on a per-algorithm basis?
    )

  (defun id32-listp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (equal x nil)
      (and (unsigned-byte-p 32 (car x))
           (idp (car x))
           (id32-listp (cdr x)))))

  (defun 32bit-listp (x)
    (declare (xargs :guard t))
    (if (atom x)
        (equal x nil)
      (and (unsigned-byte-p 32 (car x))
           (32bit-listp (cdr x)))))

  (defthmd nth-in-32bit-listp
    (implies (and (32bit-listp gates)
                  (natp idx)
                  (< idx (len gates)))
             (natp (nth idx gates)))
    :hints(("Goal" :in-theory (enable nth))))

  (defthm nodesp-is-32bit-listp
    (equal (nodesp x)
           (32bit-listp x)))

  (defthm insp-is-32bit-listp
    (equal (insp x)
           (id32-listp x)))

  (defthm outsp-is-32bit-listp
    (equal (outsp x)
           (id32-listp x)))

  (defthm regsp-is-32bit-listp
    (equal (regsp x)
           (id32-listp x)))

  (defstobj-clone aignet2 aignet :suffix "2")
  (acl2::def-stobj-swap aignet aignet2))

(defun aignet-sizes-ok (aignet)
  (declare (xargs :stobjs aignet))
  (and (<= (lnfix (num-ins aignet))
           (ins-length aignet))
       (<= (lnfix (num-outs aignet))
           (outs-length aignet))
       (<= (lnfix (num-regs aignet))
           (regs-length aignet))
       (<= (* 2 (lnfix (num-nodes aignet)))
           (nodes-length aignet))))



(defsection node-equiv
  (defund nodep (x)
    (declare (xargs :guard t))
    (and (true-listp x)
         (equal (len x) 2)
         (natp (car x))
         (natp (cadr x))))

  (local (in-theory (enable nodep)))

  (defund node-fix (x)
    (mbe :logic (non-exec (mv (nfix (mv-nth 0 x))
                              (nfix (mv-nth 1 x))))
         :exec (mv (nfix (car x))
                   (nfix (cadr x)))))

  (local (in-theory (enable node-fix)))

  (defthm nodep-of-node-fix
    (nodep (node-fix x)))

  (local (defthm len-zero
           (equal (equal (len x) 0)
                  (not (consp x)))))

  (defthm node-fix-when-nodep
    (implies (nodep x)
             (equal (node-fix x) x)))

  (defun-nx node-equiv (x y)
    (equal (node-fix x) (node-fix y)))

  (defequiv node-equiv)

  (defthm node-equiv-of-node-fix
    (node-equiv (node-fix x) x)))

;; Low-level access to the node array.
(defsection node-accessors

  (local (in-theory (enable nth-in-32bit-listp
                            nodep)))

  ;; The normal form for rewriting will be in terms of nth-node and
  ;; node-type, node-fanin0, etc.
  (defund-nx nth-node (id nodes)
    (mv (nfix (nth (* 2 (id-val id)) nodes))
        (nfix (nth (+ 1 (* 2 (id-val id))) nodes))))

  (defmvtypes nth-node (natp natp))
  (defcong id-equiv equal (nth-node id nodes) 1
    :hints(("Goal" :in-theory (enable nth-node))))



  ;; Field access.  These take the particular "node", i.e. the value of
  ;; nth-node, which is (logically) a list containing the two slot values.
  (defund node->type (node)
    (declare (xargs :guard (nodep node)))
    (logand 3 (nfix (mbe :logic (non-exec (mv-nth 0 node))
                         :exec (car node)))))

  (defund node->phase (node)
    (declare (xargs :guard (nodep node)))
    (logand 1 (ash (nfix (mbe :logic (non-exec (mv-nth 1 node))
                              :exec (cadr node))) -1)))

  (defund node->fanin0 (node)
    (declare (xargs :guard (nodep node)))
    (ash (nfix (mbe :logic (non-exec (mv-nth 0 node))
                    :exec (car node)))
         -2))

  (defund node->regp (node)
    (declare (xargs :guard (nodep node)))
    (logand 1 (nfix (mbe :logic (non-exec (mv-nth 1 node))
                         :exec (cadr node)))))

  (defund node->fanin1 (node)
    (declare (xargs :guard (nodep node)))
    (ash (nfix (mbe :logic (non-exec (mv-nth 1 node))
                    :exec (cadr node))) -2))

  (defthm nodep-nth-node
    (nodep (nth-node id nodes))
    :hints(("Goal" :in-theory (enable nodep nth-node))))

  (local (in-theory (enable nth-node
                            node->type
                            node->regp
                            node->phase
                            node->fanin0
                            node->fanin1
                            node-fix)))

  (defcong node-equiv equal (node->type x) 1)
  (defcong node-equiv equal (node->regp x) 1)
  (defcong node-equiv equal (node->phase x) 1)
  (defcong node-equiv equal (node->fanin0 x) 1)
  (defcong node-equiv equal (node->fanin1 x) 1)




  (defthm node->regp-bound
    (<= (node->regp x) 1)
    :hints(("Goal" :in-theory (disable acl2::logand-with-bitmask)))
    :rule-classes :linear)

  (defthm node->phase-bound
    (<= (node->phase x) 1)
    :hints(("Goal" :in-theory (disable acl2::logand-with-bitmask)))
    :rule-classes :linear)

  (defthm node->type-bound
    (<= (node->type x) 3)
    :hints(("Goal" :in-theory (disable acl2::logand-with-bitmask)))
    :rule-classes :linear)


  ;; replace the type prescriptions with stronger ones
  (defthm natp-node->type
    (natp (node->type node))
    :rule-classes :type-prescription)
  (in-theory (disable (:type-prescription node->type)))

  (defthm natp-node->regp
    (natp (node->regp node))
    :rule-classes :type-prescription)
  (in-theory (disable (:type-prescription node->regp)))

  (defthm natp-node->phase
    (natp (node->phase node))
    :rule-classes :type-prescription)
  (in-theory (disable (:type-prescription node->phase)))

  (defthm natp-node->fanin0
    (natp (node->fanin0 node))
    :rule-classes :type-prescription)
  (in-theory (disable (:type-prescription node->fanin0)))

  (defthm natp-node->fanin1
    (natp (node->fanin1 node))
    :rule-classes :type-prescription)
  (in-theory (disable (:type-prescription node->fanin1)))

  (defthm bitp-node->phase
    (bitp (node->phase x))
    :hints(("Goal" :in-theory (e/d (bitp)
                                   (acl2::logand-with-bitmask)))))

  (defthm bitp-node->regp
    (bitp (node->regp x))
    :hints(("Goal" :in-theory (e/d (bitp)
                                   (acl2::logand-with-bitmask)))))


  ;; The normal form for rewriting will be in terms of update-nth-node and
  ;; update-node-type, update-node-fanin0, etc.
  (defund-nx update-nth-node (id node nodes)
    (update-nth (* 2 (id-val id)) (mv-nth 0 node)
                (update-nth (+ 1 (* 2 (id-val id)))
                            (mv-nth 1 node)
                            nodes)))

  (local (in-theory (enable update-nth-node)))

  (defcong id-equiv equal (update-nth-node n val nodes) 1)

  (defthm nth-node-of-update-nth-node-same
    (equal (nth-node n (update-nth-node n val nodes))
           (node-fix val))
    :hints(("Goal" :in-theory (enable nth-node node-fix))))

  (defthm nth-node-of-update-nth-node-diff
    (implies (not (equal (id-val n) (id-val m)))
             (equal (nth-node n (update-nth-node m val nodes))
                    (nth-node n nodes)))
    :hints(("Goal" :in-theory (enable nth-node))))

  (defthmd nth-node-of-update-nth-node-split
    (equal (nth-node n (update-nth-node m val nodes))
           (if (equal (id-val n) (id-val m))
               (node-fix val)
             (nth-node n nodes)))
    :hints(("Goal" :in-theory (enable nth-node node-fix))))

  (defthm len-of-update-nth-node
    (equal (len (update-nth-node n node lst))
           (max (+ 2 (* 2 (id-val n))) (len lst))))


  (definlined mk-node (type regp phase fanin0 fanin1)
    (declare (type (integer 0 *) fanin0)
             (type (integer 0 *) fanin1)
             (type (integer 0 3) type)
             (type bit regp)
             (type bit phase))
    (mv (logior (ash (lnfix fanin0) 2)
                (logand 3 type))
        (logior (acl2::lbfix regp)
                (ash (acl2::lbfix phase) 1)
                (ash (lnfix fanin1) 2))))

  (defmvtypes mk-node$inline (natp natp))

  (local (in-theory (enable mk-node)))

  (defcong acl2::int-equiv equal (mk-node type regp phase fanin0 fanin1) 1)
  (defcong bit-equiv equal (mk-node type regp phase fanin0 fanin1) 2)
  (defcong bit-equiv equal (mk-node type regp phase fanin0 fanin1) 3)
  (defcong nat-equiv equal (mk-node type regp phase fanin0 fanin1) 4)
  (defcong nat-equiv equal (mk-node type regp phase fanin0 fanin1) 5)


  (defthm node->type-of-mk-node
    (equal (node->type (mk-node type regp phase fanin0 fanin1))
           (logand 3 type))
    :hints(("Goal" :in-theory (enable node->type))))

  (defthm node->fanin0-of-mk-node
    (equal (node->fanin0 (mk-node type regp phase fanin0 fanin1))
           (nfix fanin0))
    :hints(("Goal" :in-theory (enable node->fanin0))))

  (local (defun count2-ind (a b)
           (if (zp a)
               b
             (count2-ind (1- a) (1- b)))))

  (local (defthm loghead-of-ash
           (implies (<= (nfix a) (ifix b))
                    (equal (acl2::loghead a (ash n b)) 0))
           :hints(("Goal"
                   :induct (count2-ind a b)
                   :expand ((:free (b) (acl2::loghead a b))
                            (:free (n) (ash n b)))))))

  (defthm node->regp-of-mk-node
    (equal (node->regp (mk-node type regp phase fanin0 fanin1))
           (acl2::bfix regp))
    :hints(("Goal" :in-theory (enable node->regp))))

  (defthm node->phase-of-mk-node
    (equal (node->phase (mk-node type regp phase fanin0 fanin1))
           (acl2::bfix phase))
    :hints(("Goal" :in-theory (enable node->phase))))

  (defthm node->fanin1-of-mk-node
    (equal (node->fanin1 (mk-node type regp phase fanin0 fanin1))
           (nfix fanin1))
    :hints(("Goal" :in-theory (enable node->fanin1))))


  (defthm nodep-mk-node
    (nodep (mk-node type regp phase f0 f1))
    :hints(("Goal" :in-theory (enable mk-node len nodep)))))

(defsection typed-accessors

  ;; Now specialize these to the various types of node.
  (defund io-node->regp (x)
    (declare (xargs :guard (and (nodep x)
                                (or (int= (node->type x) (in-type))
                                    (int= (node->type x) (out-type))))))
    (node->regp x))

  (local (in-theory (enable io-node->regp)))

  (defthm bitp-of-io-node->regp
    (bitp (io-node->regp x)))

  (defthm io-node->regp-bound
    (<= (io-node->regp x) 1)
    :rule-classes :linear)

  (defund io-node->ionum (x)
    (declare (xargs :guard (and (nodep x)
                                (or (int= (node->type x) (in-type))
                                    (and (int= (node->type x) (out-type))
                                         (int= (io-node->regp x) 0))))))
    (node->fanin1 x))

  ;; (defund reg-node->ri (x)
  ;;   (declare (xargs :guard (and (nodep x)
  ;;                               (int= (node->type x) (in-type))
  ;;                               (int= (io-node->regp x) 1))))
  ;;   (to-id (node->fanin0 x)))

  (defund gate-node->fanin0 (x)
    (declare (xargs :guard (and (nodep x)
                                (int= (node->type x) (gate-type)))))
    (to-lit (node->fanin0 x)))

  (defund gate-node->fanin1 (x)
    (declare (xargs :guard (and (nodep x)
                                (int= (node->type x) (gate-type)))))
    (to-lit (node->fanin1 x)))

  (defund co-node->fanin (x)
    (declare (xargs :guard (and (nodep x)
                                (int= (node->type x) (out-type)))))
    (to-lit (node->fanin0 x)))

  (defund regin-node->ro (x)
    (declare (xargs :guard (and (nodep x)
                                (int= (node->type x) (out-type))
                                (int= (io-node->regp x) 1))))
    (to-id (node->fanin1 x)))

  (local (in-theory (enable io-node->regp
                            io-node->ionum
                            ;; reg-node->ri
                            gate-node->fanin0
                            gate-node->fanin1
                            co-node->fanin
                            regin-node->ro)))

  (local (in-theory (disable node-equiv)))

  (defcong node-equiv equal (io-node->regp x) 1)
  (defcong node-equiv equal (io-node->ionum x) 1)
  ;; (defcong node-equiv equal (reg-node->ri x) 1)
  (defcong node-equiv equal (gate-node->fanin0 x) 1)
  (defcong node-equiv equal (gate-node->fanin1 x) 1)
  (defcong node-equiv equal (co-node->fanin x) 1)
  (defcong node-equiv equal (regin-node->ro x) 1)

  (definlined mk-in-node (innum)
    (declare (type (integer 0 *) innum))
    (mk-node (in-type) 0 0 0 innum))

  (defmvtypes mk-in-node$inline (natp natp))

  (local (in-theory (enable mk-in-node)))

  (defthm nodep-of-mk-in-node
    (nodep (mk-in-node innum)))

  (defcong nat-equiv equal (mk-in-node innum) 1)

  (defthm node->type-of-mk-in-node
    (equal (node->type (mk-in-node innum)) (in-type)))

  (defthm io-node->regp-of-mk-in-node
    (equal (io-node->regp (mk-in-node innum)) 0))

  (defthm io-node->ionum-of-mk-in-node
    (equal (io-node->ionum (mk-in-node innum))
           (nfix innum)))

  (defthm node->phase-of-mk-in-node
    (equal (node->phase (mk-in-node innum)) 0))



  (definlined mk-reg-node (regnum)
    (declare (type (integer 0 *) regnum))
    (mk-node (in-type) 1 0 0 regnum))

  (defmvtypes mk-reg-node$inline (natp natp))

  (local (in-theory (enable mk-reg-node)))

  (defthm nodep-of-mk-reg-node
    (nodep (mk-reg-node regnum)))

  (defcong nat-equiv equal (mk-reg-node regnum) 1)

  (defthm node->type-of-mk-reg-node
    (equal (node->type (mk-reg-node regnum)) (in-type)))

  (defthm io-node->regp-of-mk-reg-node
    (equal (io-node->regp (mk-reg-node regnum)) 1))

  (defthm io-node->ionum-of-mk-reg-node
    (equal (io-node->ionum (mk-reg-node regnum))
           (nfix regnum)))

  (defthm node->phase-of-mk-reg-node
    (equal (node->phase (mk-reg-node regnum)) 0))



  (definlined mk-gate-node (f0 f1 phase)
    (Declare (type (integer 0 *) f0)
             (type (integer 0 *) f1)
             (type bit phase)
             (xargs :guard (and (litp f0)
                                (litp f1))))
    (mk-node (gate-type) 0 phase (lit-val f0) (lit-val f1)))

  (defmvtypes mk-gate-node$inline (natp natp))

  (local (in-theory (enable mk-gate-node)))

  (defthm nodep-of-mk-gate-node
    (nodep (mk-gate-node f0 f1 phase)))

  (defcong lit-equiv equal (mk-gate-node f0 f1 phase) 1)
  (defcong lit-equiv equal (mk-gate-node f0 f1 phase) 2)
  (defcong bit-equiv equal (mk-gate-node f0 f1 phase) 3)

  (defthm node->type-of-mk-gate-node
    (equal (node->type (mk-gate-node f0 f1 phase)) (gate-type)))

  (defthm gate-node->fanin0-of-mk-gate-node
    (equal (gate-node->fanin0 (mk-gate-node f0 f1 phase))
           (lit-fix f0)))

  (defthm litp-of-gate-node->fanin0
    (litp (gate-node->fanin0 x)))

  (defthm gate-node->fanin1-of-mk-gate-node
    (equal (gate-node->fanin1 (mk-gate-node f0 f1 phase))
           (lit-fix f1)))

  (defthm litp-of-gate-node->fanin1
    (litp (gate-node->fanin1 x)))

  (defthm node->phase-of-mk-gate-node
    (equal (node->phase (mk-gate-node f0 f1 phase))
           (acl2::bfix phase)))


  (definlined mk-out-node (fanin outnum phase)
    (declare (type (integer 0 *) fanin)
             (type (integer 0 *) outnum)
             (type bit phase)
             (xargs :guard (litp fanin)))
    (mk-node (out-type) 0 phase (lit-val fanin) outnum))

  (defmvtypes mk-out-node$inline (natp natp))

  (local (in-theory (enable mk-out-node)))

  (defthm nodep-of-mk-out-node
    (nodep (mk-out-node fanin outnum phase)))

  (defcong lit-equiv equal (mk-out-node fanin outnum phase) 1)
  (defcong nat-equiv equal (mk-out-node fanin outnum phase) 2)
  (defcong bit-equiv equal (mk-out-node fanin outnum phase) 3)

  (defthm node->type-of-mk-out-node
    (equal (node->type (mk-out-node fanin outnum phase)) (out-type)))

  (defthm io-node->regp-of-mk-out-node
    (equal (io-node->regp (mk-out-node fanin outnum phase)) 0))

  (defthm io-node->ionum-of-mk-out-node
    (equal (io-node->ionum (mk-out-node fanin outnum phase))
           (nfix outnum)))

  (defthm co-node->fanin-of-mk-out-node
    (equal (co-node->fanin (mk-out-node fanin outnum phase))
           (lit-fix fanin)))

  (defthm litp-of-co-node->fanin
    (litp (co-node->fanin x)))

  (defthm node->phase-of-mk-out-node
    (equal (node->phase (mk-out-node fanin outnum phase))
           (acl2::bfix phase)))


  (definlined mk-regin-node (fanin ro phase)
    (declare (type (integer 0 *) fanin)
             (type (integer 0 *) ro)
             (type bit phase)
             (xargs :guard (and (litp fanin)
                                (idp ro))))
    (mk-node (out-type) 1 phase (lit-val fanin) (id-val ro)))

  (defmvtypes mk-regin-node$inline (natp natp))

  (local (in-theory (enable mk-regin-node)))

  (defthm nodep-of-mk-regin-node
    (nodep (mk-regin-node fanin ro phase)))

  (defcong lit-equiv equal (mk-regin-node fanin ro phase) 1)
  (defcong id-equiv equal (mk-regin-node fanin ro phase) 2)
  (defcong bit-equiv equal (mk-regin-node fanin ro phase) 3)

  (defthm node->type-of-mk-regin-node
    (equal (node->type (mk-regin-node fanin ro phase)) (out-type)))

  (defthm io-node->regp-of-mk-regin-node
    (equal (io-node->regp (mk-regin-node fanin ro phase)) 1))

  (defthm regin-node->ro-of-mk-regin-node
    (equal (regin-node->ro (mk-regin-node fanin ro phase))
           (id-fix ro)))

  (defthm idp-of-regin-node->ro
    (idp (regin-node->ro x)))

  (defthm co-node->fanin-of-mk-regin-node
    (equal (co-node->fanin (mk-regin-node fanin ro phase))
           (lit-fix fanin)))

  (defthm node->phase-of-mk-regin-node
    (equal (node->phase (mk-regin-node fanin ro phase))
           (acl2::bfix phase)))



  (definlined mk-const-node ()
    (declare (xargs :guard t))
    (mk-node (const-type) 0 0 0 0))

  (defmvtypes mk-const-node$inline (natp natp))

  (local (in-theory (enable mk-const-node)))

  (defthm nodep-of-mk-const-node
    (nodep (mk-const-node)))

  (defthm node->type-of-mk-const-node
    (equal (node->type (mk-const-node)) (const-type)))


  ;; (definlined update-reg->ri (ri x)
  ;;   (declare (type (integer 0 *) ri)
  ;;            (xargs :guard (and (nodep x)
  ;;                               (equal (node->type x) (in-type))
  ;;                               (equal (io-node->regp x) 1)
  ;;                               (idp ri))))
  ;;   (update-node->fanin0 (id-val ri) x))

  ;; (local (in-theory (enable update-reg->ri)))

  ;; (defthm node->type-of-update-reg->ri
  ;;   (equal (node->type (update-reg->ri ri x))
  ;;          (node->type x)))

  ;; (defthm node->phase-of-update-reg->ri
  ;;   (equal (node->phase (update-reg->ri ri x))
  ;;          (node->phase x)))

  ;; (defthm io-node->regp-of-update-reg->ri
  ;;   (equal (io-node->regp (update-reg->ri ri x))
  ;;          (io-node->regp x)))

  ;; (defthm io-node->ionum-of-update-reg->ri
  ;;   (equal (io-node->ionum (update-reg->ri ri x))
  ;;          (io-node->ionum x)))

  ;; (defthm reg-node->ri-of-update-reg->ri
  ;;   (equal (reg-node->ri (update-reg->ri ri x))
  ;;          (id-fix ri)))

  ;; (defthm nodep-of-update-reg->ri
  ;;   (implies (nodep x)
  ;;            (nodep (update-reg->ri ri x))))
  )

(def-ruleset! aignet-frame-thms nil)

(defmacro def-aignet-frame (fn &key hints)
  `(encapsulate nil
    (local (in-theory (enable* aignet-frame-thms)))
    (acl2::def-stobj-frame ,fn aignet :ruleset aignet-frame-thms
                           ,@(and hints `(:hints ,hints)))))

(defmacro def-aignet2-frame (fn &key hints)
  `(encapsulate nil
    (local (in-theory (enable* aignet-frame-thms)))
    (acl2::def-stobj-frame ,fn aignet2 :ruleset aignet-frame-thms
                           ,@(and hints `(:hints ,hints)))))

(defsection aignet-idp

  (local (in-theory (enable acl2::aignetp)))

  (defund aignet-idp (n aignet)
    (declare (xargs :stobjs aignet))
    (and (idp n)
         (< (id-val n) (lnfix (num-nodes aignet)))))

  (def-aignet-frame aignet-idp)

  (local (in-theory (enable aignet-idp)))

  (defthm aignet-idp-of-id-fix
    (implies (aignet-idp n aignet)
             (aignet-idp (to-id (id-val n)) aignet)))

  (defcong nth-equiv equal (aignet-idp n aignet) 2)

  (defthm aignet-idp-implies-idp
    (implies (aignet-idp n aignet)
             (idp n))
    :rule-classes :forward-chaining)

  (defthm aignet-idp-of-to-id
    (implies (< (nfix n) (nfix (num-nodes aignet)))
             (aignet-idp (to-id n) aignet)))

  (defthm aignet-idp-linear
    (implies (aignet-idp n aignet)
             (and (< (id-val n) (nfix (nth *num-nodes* aignet)))
                  (implies (natp (nth *num-nodes* aignet))
                           (< (id-val n) (nth *num-nodes* aignet)))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-idp-forward
    (implies (and (aignet-idp n aignet)
                  (syntaxp (not (and (consp n)
                                     (eq (car n) 'to-id)))))
             (and (< (id-val n) (nfix (nth *num-nodes* aignet)))
                  (implies (natp (nth *num-nodes* aignet))
                           (< (id-val n) (nth *num-nodes* aignet)))))
    :rule-classes :forward-chaining)

  (defthm aignet-idp-to-id-forward
    (implies (and (aignet-idp (to-id n) aignet)
                  (integerp n))
             (and (< n (nfix (nth *num-nodes* aignet)))
                  (implies (natp (nth *num-nodes* aignet))
                           (< n (nth *num-nodes* aignet)))))
    :rule-classes :forward-chaining))

(defsection executable-node-accessors

  ;; Executable accessors.  These come in various levels of granularity for
  ;; convenience.

  (local (in-theory (enable nth-node aignet-idp
                            nth-in-32bit-listp)))

  ;; get one of the two slots of an node by ID
  (definline get-node-slot (id slot aignet)
    (declare (type (integer 0 *) id)
             (type bit slot)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet))))
    (mbe :logic (non-exec (mv-nth slot (nth-node id (nth *nodesi* aignet))))
         :exec (nodesi (+ slot (* 2 (id-val id))) aignet)))

  ;; get both slots of the node by ID
  (definline get-node (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet))))
    (mbe :logic (nth-node id (non-exec (nth *nodesi* aignet)))
         :exec
         (let ((idx (* 2 (id-val id))))
           (mv (nodesi idx aignet)
               (nodesi (+ 1 idx) aignet)))))

  (local (in-theory (disable nth-node)))


  ;; ;; get all fields of the node by ID
  ;; (definline get-node-info (id aignet)
  ;;   (declare (type (integer 0 *) id)
  ;;            (xargs :stobjs aignet
  ;;                   :guard (and (aignet-sizes-ok aignet)
  ;;                               (< id (lnfix (num-nodes aignet))))))
  ;;   (mbe :logic (let ((node (nth-node id (non-exec (nth *nodesi* aignet)))))
  ;;                 (mv (node-type node)
  ;;                     (node-regp node)
  ;;                     (node-phase node)
  ;;                     (node-fanin0 node)
  ;;                     (node-fanin1 node)))
  ;;        :exec (b* (((mv s0 s1) (get-node id aignet))
  ;;                   (type (logand 3 s0))
  ;;                   (regp (logand 1 s1))
  ;;                   (phase (logand 1 (ash s1 -1)))
  ;;                   (f0 (ash s0 -2))
  ;;                   (f1 (ash s1 -2)))
  ;;                (mv type regp phase f0 f1))))

  ;; get a single field from a particular slot. Some of these are not strictly
  ;; guarded because the slot doesn't contain all the type information, but the
  ;; corresponding rewrite rules won't fire unless it is established, so the
  ;; error should show up fairly quickly.
  (definlined snode->type (slot0)
    (declare (type (integer 0 *) slot0))
    (logand 3 (lnfix slot0)))

  (defthm snode->type-rw
    (equal (snode->type (mv-nth 0 node))
           (node->type node))
    :hints(("Goal" :in-theory (enable snode->type node->type))))

  (definlined snode->phase (slot1)
    (declare (type (integer 0 *) slot1))
    (logand 1 (ash (lnfix slot1) -1)))

  (defthm snode->phase-rw
    (equal (snode->phase (mv-nth 1 node))
           (node->phase node))
    :hints(("Goal" :in-theory (enable snode->phase node->phase))))


  (definlined snode-io->regp (slot1)
    (declare (type (integer 0 *) slot1))
    (logand 1 (lnfix slot1)))

  (defthm snode-io->regp-ci-rw
    (implies (equal (node->type node) (in-type))
             (equal (snode-io->regp (mv-nth 1 node))
                    (io-node->regp node)))
    :hints(("Goal" :in-theory (enable snode-io->regp
                                      node->regp
                                      io-node->regp))))

  (defthm snode-io->regp-co-rw
    (implies (equal (node->type node) (out-type))
             (equal (snode-io->regp (mv-nth 1 node))
                    (io-node->regp node)))
    :hints(("Goal" :in-theory (enable snode-io->regp
                                      node->regp
                                      io-node->regp))))

  (definlined snode-gate->fanin0 (slot0)
    (declare (type (integer 0 *) slot0)
             (xargs :guard (int= (snode->type slot0) (gate-type))))
    (to-lit (ash (lnfix slot0) -2)))

  (defthm snode-gate->fanin0-rw
    (implies (equal (node->type node) (gate-type))
             (equal (snode-gate->fanin0 (mv-nth 0 node))
                    (gate-node->fanin0 node)))
    :hints(("Goal" :in-theory (enable snode-gate->fanin0
                                      node->fanin0
                                      gate-node->fanin0))))

  (definlined snode-co->fanin (slot0)
    (declare (type (integer 0 *) slot0)
             (xargs :guard (int= (snode->type slot0) (out-type))))
    (to-lit (ash (lnfix slot0) -2)))

  (defthm snode-co->fanin-rw
    (implies (equal (node->type node) (out-type))
             (equal (snode-co->fanin (mv-nth 0 node))
                    (co-node->fanin node)))
    :hints(("Goal" :in-theory (enable snode-co->fanin
                                      node->fanin0
                                      co-node->fanin))))

  ;; (definlined snode-reg->ri (slot0)
  ;;   (declare (type (integer 0 *) slot0)
  ;;            (xargs :guard (int= (snode->type slot0) (in-type))))
  ;;   (to-id (ash (lnfix slot0) -2)))

  ;; (defthm snode-reg->ri-rw
  ;;   (implies (and (equal (node->type node) (in-type))
  ;;                 (equal (io-node->regp node) 1))
  ;;            (equal (snode-reg->ri (mv-nth 0 node))
  ;;                   (reg-node->ri node)))
  ;;   :hints(("Goal" :in-theory (enable snode-reg->ri
  ;;                                     node->fanin0
  ;;                                     reg-node->ri))))


  ;; not strictly guarded
  (definlined snode-gate->fanin1 (slot1)
    (declare (type (integer 0 *) slot1))
    (to-lit (ash (lnfix slot1) -2)))

  (defthm snode-gate->fanin1-rw
    (implies (equal (node->type node) (gate-type))
             (equal (snode-gate->fanin1 (mv-nth 1 node))
                    (gate-node->fanin1 node)))
    :hints(("Goal" :in-theory (enable snode-gate->fanin1
                                      node->fanin1
                                      gate-node->fanin1))))

  (definlined snode-io->ionum (slot1)
    (declare (type (integer 0 *) slot1))
    (ash (lnfix slot1) -2))

  (defthm snode-io->ionum-in-rw
    (implies (equal (node->type node) (in-type))
             (equal (snode-io->ionum (mv-nth 1 node))
                    (io-node->ionum node)))
    :hints(("Goal" :in-theory (enable snode-io->ionum
                                      node->fanin1
                                      io-node->ionum))))

  (defthm snode-io->ionum-out-rw
    (implies (and (equal (node->type node) (out-type))
                  (equal (io-node->regp node) 0))
             (equal (snode-io->ionum (mv-nth 1 node))
                    (io-node->ionum node)))
    :hints(("Goal" :in-theory (enable snode-io->ionum
                                      node->fanin1
                                      io-node->ionum))))

  (definlined snode-regin->ro (slot1)
    (declare (type (integer 0 *) slot1)
             (xargs :guard (int= (snode-io->regp slot1) 1)))
    (to-id (ash (lnfix slot1) -2)))

  (defthm snode-regin->ro-rw
    (implies (and (equal (node->type node) (out-type))
                  (equal (io-node->regp node) 1))
             (equal (snode-regin->ro (mv-nth 1 node))
                    (regin-node->ro node)))
    :hints(("Goal" :in-theory (enable snode-regin->ro
                                      node->fanin1
                                      regin-node->ro))))


  ;; get a particular field by ID
  (definline id->type (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet))))
    (mbe :logic (node->type (nth-node id (non-exec (nth *nodesi* aignet))))
         :exec (snode->type (get-node-slot id 0 aignet))))

  (definline id->phase (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet))))
    (mbe :logic (node->phase (nth-node id (non-exec (nth *nodesi* aignet))))
         :exec (snode->phase (get-node-slot id 1 aignet))))

  (definline io-id->regp (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (or (equal (id->type id aignet) (in-type))
                                    (equal (id->type id aignet) (out-type))))))
    (mbe :logic (io-node->regp (nth-node id (non-exec (nth *nodesi* aignet))))
         :exec (snode-io->regp (get-node-slot id 1 aignet))))

  (definline io-id->ionum (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (or (equal (id->type id aignet) (in-type))
                                    (and (equal (id->type id aignet) (out-type))
                                         (equal (io-id->regp id aignet) 0))))))
    (mbe :logic (io-node->ionum (nth-node id (non-exec (nth *nodesi* aignet))))
         :exec (snode-io->ionum (get-node-slot id 1 aignet))))

  (definline gate-id->fanin0 (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (equal (id->type id aignet) (gate-type)))))
    (mbe :logic (gate-node->fanin0 (nth-node id (non-exec (nth *nodesi* aignet))))
         :exec (snode-gate->fanin0 (get-node-slot id 0 aignet))))

  (definline gate-id->fanin1 (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (equal (id->type id aignet) (gate-type)))))
    (mbe :logic (gate-node->fanin1 (nth-node id (non-exec (nth *nodesi* aignet))))
         :exec (snode-gate->fanin1 (get-node-slot id 1 aignet))))

  (definline co-id->fanin (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (equal (id->type id aignet) (out-type)))))
    (mbe :logic (co-node->fanin (nth-node id (non-exec (nth *nodesi* aignet))))
         :exec (snode-co->fanin (get-node-slot id 0 aignet))))

  ;; (definline reg-id->ri (id aignet)
  ;;   (declare (type (integer 0 *) id)
  ;;            (xargs :stobjs aignet
  ;;                   :guard (and (aignet-sizes-ok aignet)
  ;;                               (idp id)
  ;;                               (< (id-val id) (lnfix (num-nodes aignet)))
  ;;                               (equal (id->type id aignet) (in-type))
  ;;                               (equal (io-id->regp id aignet) 1))))
  ;;   (mbe :logic (reg-node->ri (nth-node id (non-exec (nth *nodesi* aignet))))
  ;;        :exec (snode-reg->ri (get-node-slot id 0 aignet))))

  (definline regin-id->ro (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (equal (id->type id aignet) (out-type))
                                (equal (io-id->regp id aignet) 1))))
    (mbe :logic (regin-node->ro (nth-node id (non-exec (nth *nodesi* aignet))))
         :exec (snode-regin->ro (get-node-slot id 1 aignet))))




  (definline update-node-slot (id slot val aignet)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) val)
             (type bit slot)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet))))
    (mbe :logic (update-nodesi (+ slot (* 2 (id-val id)))
                              (nfix val) aignet)
         :exec (if (< val (expt 2 32))
                   (update-nodesi (+ slot (* 2 (id-val id))) val aignet)
                 (ec-call (update-nodesi (+ slot (* 2 (id-val id))) val aignet)))))


  (local (in-theory (enable update-nth-node)))


  ;; Executable -- so far, just need a way to set a whole node,
  ;; and a way to update fanin0.
  (definline set-in-node (id innum aignet)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) innum)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet))))
    (mbe :logic (non-exec
                 (update-nth
                  *nodesi*
                  (update-nth-node id (mk-in-node innum)
                                  (nth *nodesi* aignet))
                  aignet))
         :exec (b* (((mv slot0 slot1) (mk-in-node innum))
                    (aignet (update-node-slot id 0 slot0 aignet)))
                 (update-node-slot id 1 slot1 aignet))))

  (definline set-reg-node (id regnum aignet)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) regnum)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet))))
    (mbe :logic (non-exec
                 (update-nth
                  *nodesi*
                  (update-nth-node id (mk-reg-node regnum)
                                  (nth *nodesi* aignet))
                  aignet))
         :exec (b* (((mv slot0 slot1) (mk-reg-node regnum))
                    (aignet (update-node-slot id 0 slot0 aignet)))
                 (update-node-slot id 1 slot1 aignet))))

  (definline set-gate-node (id f0 f1 phase aignet)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) f0)
             (type (integer 0 *) f1)
             (type bit phase)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (litp f0) (litp f1))))
    (mbe :logic (non-exec
                 (update-nth
                  *nodesi*
                  (update-nth-node id (mk-gate-node f0 f1 phase)
                                  (nth *nodesi* aignet))
                  aignet))
         :exec (b* (((mv slot0 slot1) (mk-gate-node f0 f1 phase))
                    (aignet (update-node-slot id 0 slot0 aignet)))
                 (update-node-slot id 1 slot1 aignet))))

  (definline set-out-node (id fanin outnum phase aignet)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) fanin)
             (type (integer 0 *) outnum)
             (type bit phase)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (litp fanin))))
    (mbe :logic (non-exec
                 (update-nth
                  *nodesi*
                  (update-nth-node id (mk-out-node fanin outnum phase)
                                  (nth *nodesi* aignet))
                  aignet))
         :exec (b* (((mv slot0 slot1) (mk-out-node fanin outnum phase))
                    (aignet (update-node-slot id 0 slot0 aignet)))
                 (update-node-slot id 1 slot1 aignet))))

  (definline set-regin-node (id fanin ro phase aignet)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) fanin)
             (type (integer 0 *) ro)
             (type bit phase)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet)
                                (litp fanin) (idp ro))))
    (mbe :logic (non-exec
                 (update-nth
                  *nodesi*
                  (update-nth-node id (mk-regin-node fanin ro phase)
                                  (nth *nodesi* aignet))
                  aignet))
         :exec (b* (((mv slot0 slot1) (mk-regin-node fanin ro phase))
                    (aignet (update-node-slot id 0 slot0 aignet)))
                 (update-node-slot id 1 slot1 aignet))))

  ;; ID should only be 0...
  (definline set-const-node (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp id aignet))))
    (mbe :logic (non-exec
                 (update-nth
                  *nodesi*
                  (update-nth-node id (mk-const-node)
                                  (nth *nodesi* aignet))
                  aignet))
         :exec (b* (((mv slot0 slot1) (mk-const-node))
                    (aignet (update-node-slot id 0 slot0 aignet)))
                 (update-node-slot id 1 slot1 aignet))))

  ;; (local (in-theory (enable update-reg->ri
  ;;                           update-node->fanin0
  ;;                           nth-node
  ;;                           redundant-update-nth)))

  ;; (definline set-reg-node->ri (id ri aignet)
  ;;   (declare (type (integer 0 *) id)
  ;;            (type (integer 0 *) ri)
  ;;            (xargs :stobjs aignet
  ;;                   :guard (and (aignet-sizes-ok aignet)
  ;;                               (idp id) (idp ri)
  ;;                               (< (id-val id) (num-nodes aignet))
  ;;                               (int= (id->type id aignet) (in-type))
  ;;                               (int= (io-id->regp id aignet) 1)
  ;;                               (< (id-val id) (id-val ri)))))
  ;;   (mbe :logic (non-exec
  ;;                (let ((nodes (nth *nodesi* aignet)))
  ;;                  (update-nth
  ;;                   *nodesi*
  ;;                   (update-nth-node
  ;;                    id (update-reg->ri ri (nth-node id nodes))
  ;;                    nodes)
  ;;                   aignet)))
  ;;        :exec (b* ((slot0 (get-node-slot id 0 aignet))
  ;;                   (slot0 (logior (ash (id-val ri) 2) (logand 3 slot0))))
  ;;                (update-node-slot id 0 slot0 aignet))))
  )

(defsection nth-id

  (defund nth-id (n x)
    (id-fix (nth n x)))

  (local (in-theory (enable nth-id)))

  (defcong nat-equiv equal (nth-id n x) 1)

  (defthm idp-of-nth-id
    (idp (nth-id n x)))

  (defund update-nth-id (n v x)
    (update-nth n (id-fix v) x))

  (defthm nth-id-of-resize-list
    (implies (<= (len lst) (nfix m))
             (equal (nth-id n (resize-list lst m 0))
                    (nth-id n lst)))
    :hints(("Goal" :in-theory (enable nth-node
                                      acl2::nth-with-large-index
                                      acl2::nth-of-resize-list-split))))

  (local (in-theory (enable update-nth-id)))

  (defcong nat-equiv equal (update-nth-id n v x) 1)
  (defcong id-equiv equal (update-nth-id n v x) 2)

  (defthm nth-id-of-update-nth-id-same
    (equal (nth-id n (update-nth-id n v x))
           (id-fix v)))

  (defthm nth-id-of-update-nth-id-diff
    (implies (not (equal (nfix n) (nfix m)))
             (equal (nth-id m (update-nth-id n v x))
                    (nth-id m x))))

  (defthm nth-id-of-update-nth-id-split
    (equal (nth-id m (update-nth-id n v x))
           (if (equal (nfix n) (nfix m))
               (id-fix v)
             (nth-id m x))))

  (defthm len-update-nth-id-not-smaller
    (<= (len x) (len (update-nth-id n v x)))
    :rule-classes (:rewrite :linear))

  (defthm len-update-nth-id-at-least-n
    (<= (nfix n) (len (update-nth-id n v x)))
    :rule-classes (:rewrite :linear))

  (defthm update-nth-id-same
    (equal (update-nth-id n v1 (update-nth-id n v2 arr))
           (update-nth-id n v1 arr)))

  (defthmd update-nth-id-switch
    (implies (not (equal (nfix n1) (nfix n2)))
             (equal (update-nth-id n2 v2 (update-nth-id n1 v1 l))
                    (update-nth-id n1 v1 (update-nth-id n2 v2 l))))
    :rule-classes ((:rewrite :loop-stopper ((n2 n1))))))

(defsection nth-lit

  (defund nth-lit (n x)
    (lit-fix (nth n x)))

  (local (in-theory (enable nth-lit)))

  (defcong nat-equiv equal (nth-lit n x) 1)

  (defthm litp-of-nth-lit
    (litp (nth-lit n x)))

  (defthm nth-lit-of-resize-list
    (implies (<= (len lst) (nfix m))
             (equal (nth-lit n (resize-list lst m 0))
                    (nth-lit n lst)))
    :hints(("Goal" :in-theory (enable nth-node
                                      acl2::nth-with-large-index
                                      acl2::nth-of-resize-list-split))))

  (defund update-nth-lit (n v x)
    (update-nth n (lit-fix v) x))
  (local (in-theory (enable update-nth-lit)))

  (defcong nat-equiv equal (update-nth-lit n v x) 1)
  (defcong lit-equiv equal (update-nth-lit n v x) 2)

  (defthm nth-lit-of-update-nth-lit-same
    (equal (nth-lit n (update-nth-lit n v x))
           (lit-fix v)))

  (defthm nth-lit-of-update-nth-lit-diff
    (implies (not (equal (nfix n) (nfix m)))
             (equal (nth-lit m (update-nth-lit n v x))
                    (nth-lit m x))))

  (defthm nth-lit-of-update-nth-lit-split
    (equal (nth-lit m (update-nth-lit n v x))
           (if (equal (nfix n) (nfix m))
               (lit-fix v)
             (nth-lit m x))))

  (defthm len-update-nth-lit-not-smaller
    (<= (len x) (len (update-nth-lit n v x)))
    :rule-classes (:rewrite :linear))

  (defthm len-update-nth-lit-at-least-n+1
    (<= (+ 1 (nfix n)) (len (update-nth-lit n v x)))
    :rule-classes ((:linear :trigger-terms ((len (update-nth-lit n v x))))))

  (defthm update-nth-lit-same
    (equal (update-nth-lit n v1 (update-nth-lit n v2 arr))
           (update-nth-lit n v1 arr)))

  (defthmd update-nth-lit-switch
    (implies (not (equal (nfix n1) (nfix n2)))
             (equal (update-nth-lit n2 v2 (update-nth-lit n1 v1 l))
                    (update-nth-lit n1 v1 (update-nth-lit n2 v2 l))))
    :rule-classes ((:rewrite :loop-stopper ((n2 n1))))))

(defsection indices-in-bounds
  ;; predicate for saying that a memo table is large enough for an aignet
  ;; Each type of memo table will have a different executable predicate, but
  ;; they all rewrite to this one, which the in-bounds rewrite rule triggers on.
  (defund-nx memo-tablep (arr aignet)
    (<= (nfix (num-nodes aignet)) (len arr)))

  (local (in-theory (enable memo-tablep)))

  (defund-nx id-in-bounds (n arr)
    (< (id-val n) (len arr)))

  (defund-nx iterator-in-bounds (n arr)
    (<= (nfix n) (len arr)))

  (local (in-theory (enable id-in-bounds
                            iterator-in-bounds)))

  (defcong id-equiv equal (id-in-bounds n arr) 1)
  (defcong nat-equiv equal (iterator-in-bounds n arr) 1)

  (defthm less-than-len-when-id-in-bounds
    (implies (double-rewrite (id-in-bounds n arr))
             (< (id-val n) (len arr)))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm id-in-bounds-when-memo-tablep
    (implies (and (memo-tablep arr aignet)
                  (double-rewrite (aignet-idp n aignet)))
             (id-in-bounds n arr)))

  (defthm iterator-in-bounds-when-memo-tablep
    (implies (and (memo-tablep arr aignet)
                  (<= (nfix n) (nfix (nth *num-nodes* aignet))))
             (iterator-in-bounds n arr)))

  (defthm id-in-bounds-of-update
    (implies (id-in-bounds n arr)
             (id-in-bounds n (update-nth m v arr))))

  (defthm id-in-bounds-of-update-nth-id
    (implies (id-in-bounds n arr)
             (id-in-bounds n (update-nth-id m v arr)))
    :hints(("Goal" :in-theory (enable update-nth-id))))

  (defthm id-in-bounds-of-update-nth-lit
    (implies (id-in-bounds n arr)
             (id-in-bounds n (update-nth-lit m v arr)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defthm memo-tablep-when-big-enough
    (implies (<= (nfix (num-nodes aignet)) (len arr))
             (memo-tablep arr aignet)))

  (defthm memo-tablep-of-update-nth
    (implies (memo-tablep arr aignet)
             (memo-tablep (update-nth n v arr) aignet)))

  (defthm memo-tablep-of-update-nth-id
    (implies (memo-tablep arr aignet)
             (memo-tablep (update-nth-id n v arr) aignet))
    :hints(("Goal" :in-theory (enable update-nth-id))))

  (defthm memo-tablep-of-update-nth-lit
    (implies (memo-tablep arr aignet)
             (memo-tablep (update-nth-lit n v arr) aignet))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defthm iterator-in-bounds-of-update
    (implies (iterator-in-bounds n arr)
             (iterator-in-bounds n (update-nth m v arr))))

  (defthm iterator-in-bounds-of-update-nth-id
    (implies (iterator-in-bounds n arr)
             (iterator-in-bounds n (update-nth-id m v arr)))
    :hints(("Goal" :in-theory (enable update-nth-id))))

  (defthm iterator-in-bounds-of-update-nth-lit
    (implies (iterator-in-bounds n arr)
             (iterator-in-bounds n (update-nth-lit m v arr)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defthm big-enough-when-memo-tablep
    (implies (and (memo-tablep arr aignet)
                  (integerp (nth *num-nodes* aignet)))
             (<= (nth *num-nodes* aignet) (len arr)))
    :rule-classes (:rewrite :forward-chaining))

  (defthm id-in-bounds-when-iterator-in-bounds-and-less
    (implies (and (iterator-in-bounds n arr)
                  (not (equal (nfix n) (len arr))))
             (id-in-bounds (to-id n) arr)))

  (defthm id-in-bounds-of-one-less
    (implies (and (iterator-in-bounds n arr)
                  (not (zp n)))
             (id-in-bounds (to-id (+ -1 n)) arr)))

  (defthm iterator-in-bounds-of-incr
    (implies (and (iterator-in-bounds n arr)
                  (not (equal (nfix n) (len arr))))
             (iterator-in-bounds (+ 1 (nfix n)) arr)))

  (defthm iterator-in-bounds-of-incr-nat
    (implies (and (iterator-in-bounds n arr)
                  (natp n)
                  (not (equal n (len arr))))
             (iterator-in-bounds (+ 1 n) arr)))

  (defthm iterator-in-bounds-of-decr
    (implies (and (iterator-in-bounds n arr)
                  (not (zp n)))
             (iterator-in-bounds (+ -1 n) arr))))

(defsection io-accessors/updaters

  (local (defthm nth-in-id32-listp
           (implies (and (id32-listp x)
                         (< (nfix n) (len x)))
                    (and (idp (nth n x))
                         (integerp (nth n x))
                         (<= 0 (nth n x))))
           :hints(("Goal" :in-theory (enable nth)))
           :rule-classes (:rewrite :type-prescription)))

  (local (in-theory (enable nth-id update-nth-id)))

  (definline innum->id (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-ins aignet)))))
    (mbe :logic (nth-id n (non-exec (nth *insi* aignet)))
         :exec (insi n aignet)))

  (definline set-innum->id (n id aignet)
    (declare (type (integer 0 *) n)
             (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (idp id)
                                (< n (num-ins aignet)))))
    (mbe :logic (non-exec
                 (update-nth *insi*
                             (update-nth-id n id (nth *insi* aignet))
                             aignet))
         :exec (if (< id (expt 2 32))
                   (update-insi n id aignet)
                 (ec-call (update-insi n id aignet)))))

  (definline regnum->id (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-regs aignet)))))
    (mbe :logic (nth-id n (non-exec (nth *regsi* aignet)))
         :exec (regsi n aignet)))

  (definline set-regnum->id (n id aignet)
    (declare (type (integer 0 *) n)
             (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (idp id)
                                (< n (num-regs aignet)))))
    (mbe :logic (non-exec
                 (update-nth *regsi*
                             (update-nth-id n id (nth *regsi* aignet))
                             aignet))
         :exec (if (< id (expt 2 32))
                   (update-regsi n id aignet)
                 (ec-call (update-regsi n id aignet)))))

  (definline outnum->id (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-outs aignet)))))
    (mbe :logic (nth-id n (non-exec (nth *outsi* aignet)))
         :exec (outsi n aignet)))

  (definline set-outnum->id (n id aignet)
    (declare (type (integer 0 *) n)
             (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (idp id)
                                (< n (num-outs aignet)))))
    (mbe :logic (non-exec
                 (update-nth *outsi*
                             (update-nth-id n id (nth *outsi* aignet))
                             aignet))
         :exec (if (< id (expt 2 32))
                   (update-outsi n id aignet)
                 (ec-call (update-outsi n id aignet))))))

(defsection aignet-litp

  (local (in-theory (enable aignet-idp)))

  (defund aignet-litp (n aignet)
    (declare (xargs :stobjs aignet
                    :guard (aignet-sizes-ok aignet)))
    (and (litp n)
         (let ((id (lit-id n)))
           (and (aignet-idp id aignet)
                (not (equal (id->type id aignet) (out-type)))))))

  (def-aignet-frame aignet-litp)

  (local (in-theory (enable aignet-litp)))

  (defcong nth-equiv equal (aignet-litp n aignet) 2)

  (defthm aignet-litp-of-to-lit-lit-val
    (implies (aignet-litp n aignet)
             (aignet-litp (to-lit (lit-val n)) aignet)))

  (defthm aignet-litp-of-lit-fix
    (implies (aignet-litp n aignet)
             (aignet-litp (lit-fix n) aignet)))

  (defthm aignet-litp-of-lit-negate
    (equal (aignet-litp (lit-negate n) aignet)
           (aignet-litp (lit-fix n) aignet)))

  (defthm aignet-litp-of-lit-negate-cond
    (equal (aignet-litp (lit-negate-cond n b) aignet)
           (aignet-litp (lit-fix n) aignet)))

  (defthm aignet-litp-implies-litp
    (implies (aignet-litp n aignet)
             (litp n))
    :rule-classes :forward-chaining)

  ;; The converse of this theorem doesn't hold because an ID is good if it's a
  ;; CO, whereas a lit isn't.
  (defthm aignet-idp-of-lit-id
    (implies (aignet-litp n aignet)
             (aignet-idp (lit-id n) aignet)))

  (defthm aignet-litp-of-mk-lit
    (implies (aignet-litp lit aignet)
             (aignet-litp (mk-lit (lit-id lit) neg) aignet)))

  (defthm aignet-litp-of-mk-lit-of-aignet-idp
    (implies (and (aignet-idp id aignet)
                  (not (equal (id->type id aignet) (out-type))))
             (aignet-litp (mk-lit id neg) aignet)))

  (defun aignet-lit-listp (x aignet)
    (declare (xargs :stobjs aignet
                    :guard (aignet-sizes-ok aignet)))
    (if (atom x)
        (eq x nil)
      (and (aignet-litp (car x) aignet)
           (aignet-lit-listp (cdr x) aignet))))

  (defun aignet-lit-alistp (x aignet)
    (declare (xargs :stobjs aignet
                    :guard (aignet-sizes-ok aignet)))
    (if (atom x)
        (eq x nil)
      (and (consp (car x))
           (aignet-litp (cdar x) aignet)
           (aignet-lit-alistp (cdr x) aignet)))))

;; Allow lookup of a literal's phase for convenience
(definline lit->phase (lit aignet)
  (declare (type (integer 0 *) lit)
           (xargs :stobjs aignet
                  :guard (and (aignet-sizes-ok aignet)
                              (aignet-litp lit aignet))))
  (b-xor (id->phase (lit-id lit) aignet)
               (lit-neg lit)))

(defsection aignet-iterator-p
  (defund aignet-iterator-p (n aignet)
    (declare (xargs :stobjs aignet
                    :guard (natp n)))
    (<= (lnfix n) (lnfix (num-nodes aignet))))

  (local (in-theory (enable aignet-iterator-p)))

  (defthm aignet-idp-when-iterator-and-less
    (implies (and (aignet-iterator-p n aignet)
                  (not (equal (nfix n) (nfix (num-nodes aignet)))))
             (aignet-idp (to-id n) aignet)))

  (defthm aignet-idp-of-one-less
    (implies (and (aignet-iterator-p n aignet)
                  (not (zp n)))
             (aignet-idp (to-id (+ -1 n)) aignet)))

  (defthm aignet-iterator-p-of-zero
    (aignet-iterator-p 0 aignet))

  (defthm aignet-iterator-p-of-num-nodes
    (aignet-iterator-p (nth *num-nodes* aignet) aignet))

  (defthm aignet-iterator-p-of-incr
    (implies (and (aignet-iterator-p n aignet)
                  (not (equal (nfix n) (nfix (nth *num-nodes* aignet)))))
             (aignet-iterator-p (+ 1 (nfix n)) aignet)))

  (defthm aignet-iterator-p-of-incr-nat
    (implies (and (aignet-iterator-p n aignet)
                  (natp n)
                  (not (equal n (nfix (nth *num-nodes* aignet)))))
             (aignet-iterator-p (+ 1 n) aignet)))

  (defthm aignet-iterator-p-of-decr
    (implies (and (aignet-iterator-p n aignet)
                  (not (zp n)))
             (aignet-iterator-p (+ -1 n) aignet)))

  (defthm aignet-iterator-p-implies-less
    (implies (and (aignet-iterator-p n aignet)
                  (integerp n)
                  (natp (nth *num-nodes* aignet))
                  (not (equal n (nth *num-nodes* aignet))))
             (< n (nth *num-nodes* aignet))))

  (defthmd aignet-iterator-p-when-lte
    (implies (and (<= x (nth *num-nodes* aignet))
                  (integerp x)
                  (natp (nth *num-nodes* aignet)))
             (aignet-iterator-p x aignet))
    :hints(("Goal" :in-theory (enable aignet-iterator-p)))))

(defsection aignet-untranslate
  (defun untranslate-preproc-node-types (term wrld)
    (declare (ignore wrld))
    (case-match term
      (('equal ('node->type ('nth-node id ('nth ''6 aignet))) ('quote typenum))
       (case typenum
         (0 `(equal (id->type ,id ,aignet) (const-type)))
         (1 `(equal (id->type ,id ,aignet) (gate-type)))
         (2 `(equal (id->type ,id ,aignet) (in-type)))
         (3 `(equal (id->type ,id ,aignet) (out-type)))
         (otherwise term)))
      (& term)))

  (defmacro use-aignet-untrans ()
    '(local
      (table acl2::user-defined-functions-table 'acl2::untranslate-preprocess
             'untranslate-preproc-node-types))))

(use-aignet-untrans)

(in-theory (disable acl2::aignetp))

(defsection well-formedness

  (local (in-theory (disable acl2::nth-with-large-index)))

  (local (in-theory (enable acl2::aignetp)))

;   (local (in-theory (enable aignet-idp)))

  (definlined aignet-gate-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp n aignet)
                                (int= (id->type n aignet) (gate-type)))
                    :guard-debug t))
    (b* (((mv slot0 slot1) (get-node n aignet))
         (f0 (snode-gate->fanin0 slot0))
         (f1 (snode-gate->fanin1 slot1))
         (phase (snode->phase slot1))
; ((mv & regp phase f0 f1) (get-node-info n aignet))
         (fid0 (lit-id f0))
         (fid1 (lit-id f1)))
      (and ;; ordered
       (< (id-val fid0) (id-val n))
       (< (id-val fid1) (id-val n))
       ;; ;; good literals, i.e. not COs
       (aignet-litp f0 aignet)
       (aignet-litp f1 aignet)
       ;; phase ok
       (int= phase (b-and (lit->phase f0 aignet)
                                (lit->phase f1 aignet))))))

  (defcong id-equiv equal (aignet-gate-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-gate-ok))))
  (defcong nth-equiv equal (aignet-gate-ok n aignet) 2
    :hints(("Goal" :in-theory (enable aignet-gate-ok))))

  (def-aignet-frame aignet-gate-ok)

  (defthm aignet-gate-ok-implies-rw
    (implies (and (aignet-gate-ok n aignet)
                  (equal (id->type n aignet) (gate-type)))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (f0 (gate-node->fanin0 node))
                    (fnode0 (nth-node (lit-id f0) nodes))
                    (f1 (gate-node->fanin1 node))
                    (fnode1 (nth-node (lit-id f1) nodes)))
               (and
                (aignet-litp f0 aignet)
                (aignet-litp f1 aignet)
                (equal (node->phase node)
                       (b-and
                        (b-xor (node->phase fnode0)
                                     (lit-neg f0))
                        (b-xor (node->phase fnode1)
                                     (lit-neg f1)))))))
    :hints(("Goal" :in-theory (enable aignet-gate-ok))))

  (defthm aignet-gate-ok-implies-linear
    (implies (and (aignet-gate-ok n aignet)
                  (equal (id->type n aignet) (gate-type)))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (and
                (< (id-val (lit-id (gate-node->fanin0 node))) (id-val n))
                (< (id-val (lit-id (gate-node->fanin1 node))) (id-val n)))))
    :hints(("Goal" :in-theory (enable aignet-gate-ok)))
    :rule-classes (:rewrite :linear))

  (definlined aignet-reg-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp n aignet)
                                (int= (id->type n aignet) (in-type))
                                (int= (io-id->regp n aignet) 1))))
    (b* ((slot1 (get-node-slot n 1 aignet))
         (regnum (snode-io->ionum slot1))
         (phase (snode->phase slot1)))
      (and (int= phase 0)
           (< regnum (lnfix (num-regs aignet)))
           (b* ((ri (regnum->id regnum aignet)))
             (and (aignet-idp ri aignet)
                  (or
                   ;; incomplete reg: regnum points back to self
                   (int= (id-val ri) (id-val n))
                   ;; complete reg: regnum points to RI which points to self
                   (and (< (id-val n) (id-val ri))
                        (int= (id->type ri aignet) (out-type))
                        (int= (io-id->regp ri aignet) 1)
                        (int= (id-val (regin-id->ro ri aignet)) (id-val n)))))))))

  (defcong id-equiv equal (aignet-reg-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-reg-ok))))
  (defcong nth-equiv equal (aignet-reg-ok n aignet) 2
    :hints(("Goal" :in-theory (enable aignet-reg-ok))))

  (def-aignet-frame aignet-reg-ok)

  (defthm aignet-reg-ok-implies-rw
    (implies (and (aignet-reg-ok n aignet)
                  (equal (id->type n aignet) (in-type))
                  (equal (io-id->regp n aignet) 1))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (regnum (io-node->ionum node))
                    (ri (nth-id regnum (nth *regsi* aignet))))
               (and
                (equal (node->phase node) 0)
                (implies (not (equal (id-val ri) (id-val n)))
                         (let* ((fnode0 (nth-node ri nodes)))
                           (and (aignet-idp ri aignet)
                                (equal (node->type fnode0) (out-type))
                                (equal (io-node->regp fnode0) 1)
                                (equal (regin-node->ro fnode0) (id-fix n))))))))
    :hints(("Goal" :in-theory (enable aignet-reg-ok))))

  (defthm aignet-reg-ok-implies-linear
    (implies (and (aignet-reg-ok n aignet)
                  (equal (id->type n aignet) (in-type))
                  (equal (io-id->regp n aignet) 1))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (regnum (io-node->ionum node))
                    (ri (nth-id regnum (nth *regsi* aignet))))
               (and
                (< (io-node->ionum node) (nfix (nth *num-regs* aignet)))
                (implies (natp (nth *num-regs* aignet))
                         (< (io-node->ionum node) (nth *num-regs* aignet)))
                (implies (not (equal (id-val ri) (id-val n)))
                         (< (id-val n) (id-val ri))))))
    :hints(("Goal" :in-theory (enable aignet-reg-ok)))
    :rule-classes (:rewrite :linear))

  (definlined aignet-in-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp n aignet)
                                (int= (id->type n aignet) (in-type))
                                (int= (io-id->regp n aignet) 0))))
    (b* ((slot1 (get-node-slot n 1 aignet))
         (innum (snode-io->ionum slot1))
         (phase (snode->phase slot1)))
      (and (int= phase 0)
           (< innum (lnfix (num-ins aignet)))
           (int= (id-val (innum->id innum aignet)) (id-val n)))))

  (defcong id-equiv equal (aignet-in-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-in-ok))))
  (defcong nth-equiv equal (aignet-in-ok n aignet) 2
    :hints(("Goal" :in-theory (enable aignet-in-ok))))

  (def-aignet-frame aignet-in-ok)

  (defthm aignet-in-ok-implies-rw
    (implies (and (aignet-in-ok n aignet)
                  (int= (id->type n aignet) (in-type))
                  (int= (io-id->regp n aignet) 0))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (and
                (equal (node->phase node) 0)
                (equal (nth-id (io-node->ionum node) (nth *insi* aignet))
                       (id-fix n)))))
    :hints(("Goal" :in-theory (enable aignet-in-ok))))

  (defthm aignet-in-ok-implies-linear
    (implies (and (aignet-in-ok n aignet)
                  (int= (id->type n aignet) (in-type))
                  (int= (io-id->regp n aignet) 0))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (and (< (io-node->ionum node) (nfix (nth *num-ins* aignet)))
                    (implies (natp (nth *num-ins* aignet))
                             (< (io-node->ionum node) (nth *num-ins* aignet))))))
    :hints(("Goal" :in-theory (enable aignet-in-ok)))
    :rule-classes (:rewrite :linear))

  (definlined aignet-out-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp n aignet)
                                (int= (id->type n aignet) (out-type))
                                (int= (io-id->regp n aignet) 0))))
    (b* (((mv slot0 slot1) (get-node n aignet))
         (f (snode-co->fanin slot0))
         (outnum (snode-io->ionum slot1))
         (phase (snode->phase slot1)))
      (and ;; fanin ok
       (< (id-val (lit-id f)) (id-val n))
       (aignet-litp f aignet)
       ;; phase ok
       (int= phase (lit->phase f aignet))
       ;; outnum ok
       (< outnum (lnfix (num-outs aignet)))
       (int= (id-val (outnum->id outnum aignet))
             (id-val n)))))

  (defcong id-equiv equal (aignet-out-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-out-ok))))
  (defcong nth-equiv equal (aignet-out-ok n aignet) 2
    :hints(("Goal" :in-theory (enable aignet-out-ok))))

  (def-aignet-frame aignet-out-ok)

  (defthm aignet-out-ok-implies-rw
    (implies (and (aignet-out-ok n aignet)
                  (int= (id->type n aignet) (out-type))
                  (int= (io-id->regp n aignet) 0))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (f (co-node->fanin node))
                    (fnode (nth-node (lit-id f) nodes)))
               (and
                (aignet-litp f aignet)
                (equal (node->phase node)
                       (b-xor (node->phase fnode)
                                    (lit-neg f)))
                (equal (nth-id (io-node->ionum node) (nth *outsi* aignet))
                       (id-fix n)))))
    :hints(("Goal" :in-theory (enable aignet-out-ok))))

  (defthm aignet-out-ok-implies-linear
    (implies (and (aignet-out-ok n aignet)
                  (int= (id->type n aignet) (out-type))
                  (int= (io-id->regp n aignet) 0))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (and
                (< (id-val (lit-id (co-node->fanin node))) (id-val n))
                (< (io-node->ionum node) (nfix (nth *num-outs* aignet)))
                (implies (natp (nth *num-outs* aignet))
                         (< (io-node->ionum node) (nth *num-outs* aignet))))))
    :hints(("Goal" :in-theory (enable aignet-out-ok)))
    :rule-classes (:rewrite :linear))

  (definlined aignet-regin-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp n aignet)
                                (int= (id->type n aignet) (out-type))
                                (int= (io-id->regp n aignet) 1))))
    (b* (((mv slot0 slot1) (get-node n aignet))
         (f (snode-co->fanin slot0))
         (ro (snode-regin->ro slot1))
         (phase (snode->phase slot1))
         (fid (lit-id f)))
      (and
       ;; fanin ok
       (< (id-val fid) (id-val n))
       (aignet-litp f aignet)
       ;; phase ok
       (int= phase (lit->phase f aignet))
       ;; RO pointer ok
       (< (id-val ro) (id-val n))
       (aignet-idp ro aignet)
       (or (int= (id-val ro) 0)
           (and (int= (id->type ro aignet) (in-type))
                (int= (io-id->regp ro aignet) 1)
                ;; will be a redundant check for aignet-well-formedp
                ;; but needed for guard at the moment
                (< (io-id->ionum ro aignet) (lnfix (num-regs aignet)))

                (int= (id-val (regnum->id (io-id->ionum ro aignet) aignet))
                      (id-val n)))))))

  (defcong id-equiv equal (aignet-regin-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-regin-ok))))
  (defcong nth-equiv equal (aignet-regin-ok n aignet) 2
    :hints(("Goal" :in-theory (enable aignet-regin-ok))))

  (def-aignet-frame aignet-regin-ok)

  (defthm aignet-regin-ok-implies-rw
    (implies (and (aignet-regin-ok n aignet)
                  (int= (id->type n aignet) (out-type))
                  (int= (io-id->regp n aignet) 1))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (f (co-node->fanin node))
                    (fnode (nth-node (lit-id f) nodes))
                    (ro (regin-node->ro node))
                    (ronode (nth-node ro nodes)))
               (and
                (aignet-litp f aignet)
                (equal (node->phase node)
                       (b-xor (node->phase fnode)
                                    (lit-neg f)))
                (aignet-idp ro aignet)
                (implies (not (equal (id-val ro) 0))
                         (and (equal (node->type ronode) (in-type))
                              (equal (io-node->regp ronode) 1)
                              (equal (nth-id (io-node->ionum ronode)
                                             (nth *regsi* aignet))
                                     (id-fix n)))))))
    :hints(("Goal" :in-theory (enable aignet-regin-ok))))

  (defthm aignet-regin-ok-implies-linear
    (implies (and (aignet-regin-ok n aignet)
                  (int= (id->type n aignet) (out-type))
                  (int= (io-id->regp n aignet) 1))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (and
                (< (id-val (lit-id (co-node->fanin node))) (id-val n))
                (< (id-val (regin-node->ro node)) (id-val n)))))
    :hints(("Goal" :in-theory (enable aignet-regin-ok)))
    :rule-classes :linear)

  ;; (definlined aignet-const-ok (n aignet)
  ;;   (declare (type (integer 0 *) n)
  ;;            (xargs :stobjs aignet
  ;;                   :guard (and (aignet-sizes-ok aignet)
  ;;                               (< n (num-nodes aignet))
  ;;                               (int= (id->type n aignet) (const-type)))))
  ;;   (b* ((n (lnfix n))
  ;;        ((mv slot0 slot1) (get-node n aignet)))
  ;;     (and (int= slot0 0)
  ;;          (int= slot1 0))))

  ;; (defthm aignet-const-ok-implies-rw
  ;;   (implies (aignet-const-ok n aignet)
  ;;            (equal (nth-node n (nth *nodesi* aignet))
  ;;                   (mv 0 0)))
  ;;   :hints(("Goal" :in-theory (enable aignet-const-ok nth-node))))

  (defund aignet-node-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp n aignet))))
    (b* ((type (id->type n aignet)))
      (if (int= (id-val n) 0)
          (int= type (const-type))
        (aignet-seq-case
         type (io-id->regp n aignet)
         :gate (aignet-gate-ok n aignet)
         :pi (aignet-in-ok n aignet)
         :ro (aignet-reg-ok n aignet)
         :ri (aignet-regin-ok n aignet)
         :po (aignet-out-ok n aignet)
         :const nil))))

  (defcong id-equiv equal (aignet-node-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-node-ok))))
  (defcong nth-equiv equal (aignet-node-ok n aignet) 2
    :hints(("Goal" :in-theory (enable aignet-node-ok))))

  (def-aignet-frame aignet-node-ok)

  (defun aignet-nodes-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard-debug t
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-iterator-p n aignet))
                    :measure (nfix (- (nfix (num-nodes aignet))
                                      (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet))
                                   (nfix n)))
                     :exec (int= n (num-nodes aignet))))
          t))
      (and (aignet-node-ok (to-id n) aignet)
           (aignet-nodes-ok (1+ (lnfix n)) aignet))))

  (defcong nat-equiv equal (aignet-nodes-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-nodes-ok))))
  (defcong nth-equiv equal (aignet-nodes-ok n aignet) 2
    :hints(("Goal" :in-theory (enable aignet-nodes-ok))))

  (def-aignet-frame aignet-nodes-ok)

  (defthm aignet-nodes-ok-implies-0-const
    (implies (and (aignet-nodes-ok 0 aignet)
                  (< 0 (nfix (num-nodes aignet))))
             (equal (node->type (nth-node 0 (nth *nodesi* aignet)))
                    (const-type)))
    :hints (("goal" :expand ((aignet-nodes-ok 0 aignet)
                             (aignet-node-ok 0 aignet)))))

  (defthm aignet-nodes-ok-implies
    (implies (and (aignet-nodes-ok m aignet)
                  (<= (nfix m) (id-val n))
                  (aignet-idp n aignet))
             (aignet-node-ok n aignet))
    :hints(("Goal" :in-theory (e/d (aignet-idp)
                                   (aignet-node-ok)))))

  (defthm aignet-node-ok-implies
    (implies (aignet-node-ok n aignet)
             (let* ((node (nth-node n (nth *nodesi* aignet))))
               (and (equal (equal (node->type node) (const-type))
                           (equal (id-val n) 0))
                    (implies (equal (node->type node) (gate-type))
                             (aignet-gate-ok n aignet))
                    (implies (and (equal (node->type node) (in-type))
                                  (equal (io-node->regp node) 0))
                             (aignet-in-ok n aignet))
                    (implies (and (equal (node->type node) (in-type))
                                  (equal (io-node->regp node) 1))
                             (aignet-reg-ok n aignet))
                    (implies (and (equal (node->type node) (out-type))
                                  (equal (io-node->regp node) 0))
                             (aignet-out-ok n aignet))
                    (implies (and (equal (node->type node) (out-type))
                                  (equal (io-node->regp node) 1))
                             (aignet-regin-ok n aignet)))))
    :hints(("Goal" :in-theory (enable aignet-node-ok))))

  (definlined aignet-innum-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-ins aignet)))))
    (b* ((id (innum->id n aignet)))
      (and (aignet-idp id aignet)
           (int= (id->type id aignet) (in-type))
           (int= (io-id->regp id aignet) 0)
           (int= (io-id->ionum id aignet) (lnfix n)))))

  (defcong nat-equiv equal (aignet-innum-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-innum-ok))))

  (def-aignet-frame aignet-innum-ok)

  (defthm aignet-innum-ok-implies
    (implies (aignet-innum-ok n aignet)
             (let* ((id (nth-id n (nth *insi* aignet)))
                    (node (nth-node id (nth *nodesi* aignet))))
               (and (aignet-idp id aignet)
                    (equal (node->type node) (in-type))
                    (equal (io-node->regp node) 0)
                    (equal (io-node->ionum node) (nfix n)))))
    :hints(("Goal" :in-theory (enable aignet-innum-ok))))

  (defun aignet-ins-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (<= n (num-ins aignet)))
                    :measure (nfix (- (nfix (num-ins aignet))
                                      (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-ins aignet))
                                   (nfix n)))
                     :exec (int= (num-ins aignet) n)))
          t))
      (and (aignet-innum-ok n aignet)
           (aignet-ins-ok (+ 1 (lnfix n)) aignet))))

  (def-aignet-frame aignet-ins-ok)

  (defthm aignet-ins-ok-implies
    (implies (and (aignet-ins-ok m aignet)
                  (<= (nfix m) (nfix n))
                  (< (nfix n) (nfix (num-ins aignet))))
             (aignet-innum-ok n aignet)))

  (definlined aignet-regnum-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-regs aignet)))
                    :guard-debug t))
    (b* ((id (regnum->id n aignet)))
      (and (aignet-idp id aignet)
           (if (int= (id->type id aignet) (in-type))
               (and (int= (io-id->regp id aignet) 1)
                    (int= (io-id->ionum id aignet) (lnfix n)))
             (and (int= (id->type id aignet) (out-type))
                  (int= (io-id->regp id aignet) 1)
                  (aignet-idp (regin-id->ro id aignet) aignet)
                  (not (equal (id-val (regin-id->ro id aignet)) 0))
                  (equal (id->type (regin-id->ro id aignet) aignet) (in-type))
                  (equal (io-id->regp (regin-id->ro id aignet) aignet) 1)
                  (int= (io-id->ionum (regin-id->ro id aignet) aignet)
                        (lnfix n)))))))

  (defcong nat-equiv equal (aignet-regnum-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-regnum-ok))))

  (def-aignet-frame aignet-regnum-ok)

  (defthm aignet-regnum-ok-implies
    (implies (aignet-regnum-ok n aignet)
             (let* ((id (nth-id n (nth *regsi* aignet)))
                    (node (nth-node id (nth *nodesi* aignet))))
               (and (aignet-idp id aignet)
                    (implies (not (equal (node->type node) (in-type)))
                             (equal (node->type node) (out-type)))
                    (implies (not (equal (node->type node) (out-type)))
                             (equal (node->type node) (in-type)))
                    (not (equal (node->type node) (gate-type)))
                    (not (equal (node->type node) (const-type)))
                    (equal (io-node->regp node) 1)
                    (implies (equal (node->type node) (in-type))
                             (equal (io-node->ionum node) (nfix n)))
                    (implies (equal (node->type node) (out-type))
                             (let* ((ro-node (nth-node (regin-node->ro node)
                                                     (nth *nodesi* aignet))))
                               (and (not (equal (id-val (regin-node->ro node)) 0))
                                    (equal (io-node->ionum ro-node)
                                           (nfix n))))))))
    :hints(("Goal" :in-theory (enable aignet-regnum-ok))))

  (defun aignet-regs-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (<= n (num-regs aignet)))
                    :measure (nfix (- (nfix (num-regs aignet))
                                      (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet))
                                   (nfix n)))
                     :exec (int= (num-regs aignet) n)))
          t))
      (and (aignet-regnum-ok n aignet)
           (aignet-regs-ok (+ 1 (lnfix n)) aignet))))

  (def-aignet-frame aignet-regs-ok)

  (defthm aignet-regs-ok-implies
    (implies (and (aignet-regs-ok m aignet)
                  (<= (nfix m) (nfix n))
                  (< (nfix n) (nfix (num-regs aignet))))
             (aignet-regnum-ok n aignet)))

  (definlined aignet-outnum-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (< n (num-outs aignet)))))
    (b* ((id (outnum->id n aignet)))
      (and (aignet-idp id aignet)
           (int= (id->type id aignet) (out-type))
           (int= (io-id->regp id aignet) 0)
           (int= (io-id->ionum id aignet) (lnfix n)))))

  (defcong nat-equiv equal (aignet-outnum-ok n aignet) 1
    :hints(("Goal" :in-theory (enable aignet-outnum-ok))))

  (def-aignet-frame aignet-outnum-ok)

  (defthm aignet-outnum-ok-implies
    (implies (aignet-outnum-ok n aignet)
             (let* ((id (nth-id n (nth *outsi* aignet)))
                    (node (nth-node id (nth *nodesi* aignet))))
               (and (aignet-idp id aignet)
                    (equal (node->type node) (out-type))
                    (equal (io-node->regp node) 0)
                    (equal (io-node->ionum node) (nfix n)))))
    :hints(("Goal" :in-theory (enable aignet-outnum-ok))))

  (defun aignet-outs-ok (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (<= n (num-outs aignet)))
                    :measure (nfix (- (nfix (num-outs aignet))
                                      (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-outs aignet))
                                   (nfix n)))
                     :exec (int= (num-outs aignet) n)))
          t))
      (and (aignet-outnum-ok n aignet)
           (aignet-outs-ok (+ 1 (lnfix n)) aignet))))

  (def-aignet-frame aignet-outs-ok)

  (defthm aignet-outs-ok-implies
    (implies (and (aignet-outs-ok m aignet)
                  (<= (nfix m) (nfix n))
                  (< (nfix n) (nfix (num-outs aignet))))
             (aignet-outnum-ok n aignet)))


  (defun aignet-well-formedp (aignet)
    (declare (xargs :stobjs aignet))
    (and (aignet-sizes-ok aignet)
         (< 0 (lnfix (num-nodes aignet))) ;; must at least have the constant 0 node
         (aignet-nodes-ok 0 aignet)
         (aignet-ins-ok 0 aignet)
         (aignet-regs-ok 0 aignet)
         (aignet-outs-ok 0 aignet)
         (natp (num-regs aignet))
         (natp (num-ins aignet))
         (natp (num-outs aignet))
         (natp (num-gates aignet))
         (natp (num-regins aignet))))

  (local (in-theory (disable aignet-outs-ok
                             aignet-regs-ok
                             aignet-ins-ok
                             aignet-nodes-ok)))

  (defthm aignet-well-formedp-num-nodes-natp
    (implies (aignet-well-formedp aignet)
             (posp (nth *num-nodes* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-well-formedp-num-ins-natp
    (implies (aignet-well-formedp aignet)
             (natp (nth *num-ins* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-well-formedp-num-regs-natp
    (implies (aignet-well-formedp aignet)
             (natp (nth *num-regs* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-well-formedp-num-outs-natp
    (implies (aignet-well-formedp aignet)
             (natp (nth *num-outs* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-well-formedp-num-gates-natp
    (implies (aignet-well-formedp aignet)
             (natp (nth *num-gates* aignet)))
    :rule-classes :type-prescription)

  (defthm aignet-well-formedp-num-regins-natp
    (implies (aignet-well-formedp aignet)
             (natp (nth *num-regins* aignet)))
    :rule-classes :type-prescription)

  ;; ;; nothing should be proved here
  ;; (def-aignet-frame aignet-well-formedp)

  (local (in-theory (disable aignet-sizes-ok
                             aignet-nodes-ok
                             aignet-ins-ok
                             aignet-regs-ok
                             aignet-outs-ok)))

  (defthm aignet-well-formedp-gate-rw
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (gate-type)))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (f0 (gate-node->fanin0 node))
                    (fnode0 (nth-node (lit-id f0) nodes))
                    (f1 (gate-node->fanin1 node))
                    (fnode1 (nth-node (lit-id f1) nodes)))
               (and
                (aignet-litp f0 aignet)
                (aignet-litp f1 aignet)
                (equal (node->phase node)
                       (b-and
                        (b-xor (node->phase fnode0)
                                     (lit-neg f0))
                        (b-xor (node->phase fnode1)
                                     (lit-neg f1))))))))

  (defthm aignet-well-formedp-gate-linear
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (gate-type)))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (and
                (< (id-val (lit-id (gate-node->fanin0 node))) (id-val n))
                (< (id-val (lit-id (gate-node->fanin1 node))) (id-val n)))))
    :rule-classes (:rewrite :linear))


  (defthm aignet-well-formedp-reg-rw
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (in-type))
                  (equal (io-id->regp n aignet) 1))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (regnum (io-node->ionum node))
                    (ri (nth-id regnum (nth *regsi* aignet)))
                    (ri-node (nth-node ri (nth *nodesi* aignet))))
               (and
                (equal (node->phase node) 0)
                (aignet-idp ri aignet)
                (implies (not (equal (id-val ri) (id-val n)))
                         (and (equal (node->type ri-node) (out-type))
                              (equal (io-node->regp ri-node) 1)
                              (equal (regin-node->ro ri-node) (id-fix n))))))))

  (defun equiv-search-type-alist (type-alist goaltype equiv lhs rhs unify-subst wrld)
    (declare (xargs :mode :program))
    (b*  (((when (endp type-alist))
           (mv nil nil))
          ((list* term type ?ttree) (car type-alist))
          ((unless
               (and (acl2::ts-subsetp type goaltype)
                    (consp term)
                    (symbolp (car term))
                    (member equiv
                            (fgetprop (car term) 'acl2::coarsenings
                                      nil wrld))))
           (equiv-search-type-alist (cdr type-alist) goaltype equiv lhs rhs unify-subst
                                    wrld))
          ((mv ans new-unify-subst)
           (acl2::one-way-unify1 lhs (cadr term) unify-subst))
          ((mv ans new-unify-subst)
           (if ans
               (acl2::one-way-unify1 rhs (caddr term) new-unify-subst)
             (mv nil nil)))
          ((when ans) (mv t new-unify-subst))
          ;; try (equiv rhs lhs)
          ((mv ans new-unify-subst)
           (acl2::one-way-unify1 lhs (caddr term) unify-subst))
          ((mv ans new-unify-subst)
           (if ans
               (acl2::one-way-unify1 rhs (cadr term) new-unify-subst)
             (mv nil nil)))
          ((when ans) (mv t new-unify-subst)))
      (equiv-search-type-alist (cdr type-alist) goaltype equiv lhs rhs unify-subst
                               wrld)))

  ;; Term has at least one variable not bound in unify-subst.  Search
  ;; type-alist for term matching (equiv1 lhs rhs) or (equiv1 rhs lhs)
  ;; and return the matching free variables.
  (defun match-equiv-or-refinement (equiv var binding-term mfc state)
    (declare (xargs :mode :program :stobjs state))
    (b* (; (*mfc* mfc)
         (unify-subst (acl2::mfc-unify-subst mfc))
         ((mv erp tbind)
          (acl2::translate-cmp binding-term t t nil 'match-equiv-or-refinement (w state)
                               (acl2::default-state-vars t)))
         ((when erp)
          (er hard? erp "~@0" tbind))
         (type-alist (acl2::mfc-type-alist mfc))
         ;; Does the var unify with the binding-term already?
         ((mv ok new-unify-subst)
          (acl2::one-way-unify1 tbind (cdr (assoc var unify-subst)) unify-subst))
         ((when ok)
          (butlast new-unify-subst (length unify-subst)))
         ((mv ok new-unify-subst)
          (equiv-search-type-alist type-alist acl2::*ts-non-nil* equiv var tbind unify-subst
                                   (w state)))
         ((unless ok) nil))
      (butlast new-unify-subst (length unify-subst))))

  (defthmd aignet-well-formedp-reg-rw-regnum
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'nat-equiv 'regnum '(io-node->ionum (nth-node n (nth *nodesi* aignet)))
                    mfc state)
                   (n))
                  (nat-equiv regnum (io-node->ionum (nth-node n (nth *nodesi* aignet))))
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (in-type))
                  (equal (io-id->regp n aignet) 1))
             (let* ((ri (nth-id regnum (nth *regsi* aignet)))
                    (ri-node (nth-node ri (nth *nodesi* aignet))))
               (implies (not (equal (id-val ri) (id-val n)))
                        (and (equal (node->type ri-node) (out-type))
                             (equal (io-node->regp ri-node) 1)
                             (equal (regin-node->ro ri-node) (id-fix n))))))
    :hints (("goal" :use aignet-well-formedp-reg-rw
             :in-theory (disable aignet-well-formedp-reg-rw))))

  (def-ruleset! aignet-well-formedp-strong-rules nil)
  (add-to-ruleset aignet-well-formedp-strong-rules aignet-well-formedp-reg-rw-regnum)

  (defthm aignet-well-formedp-reg-linear
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (in-type))
                  (equal (io-id->regp n aignet) 1))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (regnum (io-node->ionum node))
                    (ri (nth-id regnum (nth *regsi* aignet))))
               (and (implies (not (equal (id-val ri) (id-val n)))
                             (< (id-val n) (id-val ri)))
                    (< regnum (nth *num-regs* aignet)))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-well-formedp-in-rw
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (in-type))
                  (equal (io-id->regp n aignet) 0))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (and
                (equal (node->phase node) 0)
                (equal (nth-id (io-node->ionum node) (nth *insi* aignet))
                       n)))))

  (defthmd aignet-well-formedp-in-rw-innum
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'nat-equiv 'innum '(io-node->ionum (nth-node n (nth *nodesi* aignet)))
                    mfc state)
                   (n))
                  (nat-equiv innum (io-node->ionum (nth-node n (nth *nodesi* aignet))))
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (in-type))
                  (equal (io-id->regp n aignet) 0))
             (equal (nth-id innum (nth *insi* aignet))
                    n))
    :hints (("goal" :use aignet-well-formedp-in-rw
             :in-theory (disable aignet-well-formedp-in-rw))))

  (add-to-ruleset aignet-well-formedp-strong-rules aignet-well-formedp-in-rw-innum)

  (defthm aignet-well-formedp-in-linear
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (in-type))
                  (equal (io-id->regp n aignet) 0))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (< (io-node->ionum node) (nth *num-ins* aignet))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-well-formedp-out-rw
    ;; see also combout
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type))
                  (equal (io-id->regp n aignet) 0))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (equal (nth-id (io-node->ionum node) (nth *outsi* aignet))
                      n))))

  (defthmd aignet-well-formedp-out-rw-outnum
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'nat-equiv 'outnum '(io-node->ionum (nth-node n (nth *nodesi* aignet)))
                    mfc state)
                   (n))
                  (nat-equiv outnum (io-node->ionum (nth-node n (nth *nodesi* aignet))))
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type))
                  (equal (io-id->regp n aignet) 0))
             (equal (nth-id outnum (nth *outsi* aignet))
                    n))
    :hints (("goal" :use aignet-well-formedp-out-rw
             :in-theory (disable aignet-well-formedp-out-rw))))

  (add-to-ruleset aignet-well-formedp-strong-rules aignet-well-formedp-out-rw-outnum)

  (defthm aignet-well-formedp-out-linear
    ;; see also combout
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type))
                  (equal (io-id->regp n aignet) 0))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (< (io-node->ionum node) (nth *num-outs* aignet))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-well-formedp-regin-rw
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type))
                  (equal (io-id->regp n aignet) 1))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (ro (regin-node->ro node))
                    (ronode (nth-node ro nodes)))
               (and (aignet-idp ro aignet)
                    (implies (not (equal (id-val ro) 0))
                             (and
                              (equal (node->type ronode) (in-type))
                              (equal (io-node->regp ronode) 1)
                              (equal (nth-id (io-node->ionum ronode)
                                             (nth *regsi* aignet))
                                     n)))))))

  (defthmd aignet-well-formedp-regin-rw-ro
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'id-equiv 'ro '(regin-node->ro (nth-node n (nth *nodesi* aignet)))
                    mfc state)
                   (n))
                  (id-equiv ro (regin-node->ro (nth-node n (nth *nodesi* aignet))))
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type))
                  (equal (io-id->regp n aignet) 1))
             (let* ((ronode (nth-node ro (nth *nodesi* aignet))))
               (implies (not (equal (id-val ro) 0))
                        (and
                         (equal (node->type ronode) (in-type))
                         (equal (io-node->regp ronode) 1)
                         (equal (nth-id (io-node->ionum ronode)
                                        (nth *regsi* aignet))
                                n)))))
    :hints (("goal" :use aignet-well-formedp-regin-rw
             :in-theory (disable aignet-well-formedp-regin-rw
                                 aignet-well-formedp))))

  (add-to-ruleset aignet-well-formedp-strong-rules aignet-well-formedp-regin-rw-ro)

  (defthm aignet-well-formedp-regin-linear
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type))
                  (equal (io-id->regp n aignet) 1))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (< (id-val (regin-node->ro node)) (id-val n))))
    :rule-classes (:rewrite :linear))

  ;; These are true of both regins and outs
  (defthm aignet-well-formedp-combout-rw
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type)))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes))
                    (f (co-node->fanin node))
                    (fnode (nth-node (lit-id f) nodes)))
               (and
                (aignet-litp f aignet)
                (equal (node->phase node)
                       (b-xor (node->phase fnode)
                                    (lit-neg f))))))
    :hints (("goal" :cases ((equal (io-id->regp n aignet) 1)
                            (equal (io-id->regp n aignet) 0)))))

  (defthm aignet-well-formedp-combout-linear
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type)))
             (let* ((nodes (nth *nodesi* aignet))
                    (node (nth-node n nodes)))
               (< (id-val (lit-id (co-node->fanin node))) (id-val n))))
    :hints (("goal" :cases ((equal (io-id->regp n aignet) 1)
                            (equal (io-id->regp n aignet) 0))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-well-formedp-const
    (implies (aignet-well-formedp aignet)
             (equal (node->type (nth-node 0 (nth *nodesi* aignet)))
                    (const-type))))

  (defthm aignet-well-formedp-innum
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (nfix (num-ins aignet))))
             (let* ((id (nth-id n (nth *insi* aignet)))
                    (node (nth-node id (nth *nodesi* aignet))))
               (and (aignet-idp id aignet)
                    (equal (node->type node) (in-type))
                    (equal (io-node->regp node) 0)
                    (equal (io-node->ionum node) (nfix n))))))

  (defthmd aignet-well-formedp-innum-id
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'id-equiv 'id '(nth-id n (nth *insi* aignet))
                    mfc state)
                   (n))
                  (id-equiv id (nth-id n (nth *insi* aignet)))
                  (< (nfix n) (nfix (num-ins aignet))))
             (let* ((node (nth-node id (nth *nodesi* aignet))))
               (and (equal (node->type node) (in-type))
                    (equal (io-node->regp node) 0)
                    (equal (io-node->ionum node) (nfix n)))))
    :hints (("goal" :use aignet-well-formedp-innum
             :in-theory (disable aignet-well-formedp-innum
                                 aignet-well-formedp))))

  (add-to-ruleset aignet-well-formedp-strong-rules aignet-well-formedp-innum-id)

  (defthm aignet-well-formedp-regnum
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (nfix (num-regs aignet))))
             (let* ((id (nth-id n (nth *regsi* aignet)))
                    (node (nth-node id (nth *nodesi* aignet))))
               (and (aignet-idp id aignet)
                    (implies (not (equal (node->type node) (in-type)))
                             (equal (node->type node) (out-type)))
                    (implies (not (equal (node->type node) (out-type)))
                             (equal (node->type node) (in-type)))
                    (equal (equal (node->type node) (in-type))
                           (not (equal (node->type node) (out-type))))
                    (not (equal (node->type node) (gate-type)))
                    (not (equal (node->type node) (const-type)))
                    (equal (io-node->regp node) 1)
                    (implies (equal (node->type node) (in-type))
                             (equal (io-node->ionum node) (nfix n)))
                    (implies (equal (node->type node) (out-type))
                             (let* ((ro-node (nth-node (regin-node->ro node)
                                                     (nth *nodesi* aignet))))
                               (and (not (equal (id-val (regin-node->ro node)) 0))
                                    (equal (io-node->ionum ro-node) (nfix n))))))))
    :hints(("Goal" :in-theory (enable aignet-regnum-ok))))

  (defthmd aignet-well-formedp-regnum-id
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'id-equiv 'id '(nth-id n (nth *regsi* aignet))
                    mfc state)
                   (n))
                  (id-equiv id (nth-id n (nth *regsi* aignet)))
                  (< (nfix n) (nfix (num-regs aignet))))
             (let* ((node (nth-node id (nth *nodesi* aignet))))
               (and (implies (not (equal (node->type node) (in-type)))
                             (equal (node->type node) (out-type)))
                    (implies (not (equal (node->type node) (out-type)))
                             (equal (node->type node) (in-type)))
                    (equal (equal (node->type node) (in-type))
                           (not (equal (node->type node) (out-type))))
                    (not (equal (node->type node) (gate-type)))
                    (not (equal (node->type node) (const-type)))
                    (equal (io-node->regp node) 1)
                    (implies (equal (node->type node) (in-type))
                             (equal (io-node->ionum node) (nfix n)))
                    (implies (equal (node->type node) (out-type))
                             (let* ((ro-node (nth-node (regin-node->ro node)
                                                     (nth *nodesi* aignet))))
                               (and (not (equal (id-val (regin-node->ro node)) 0))
                                    (equal (io-node->ionum ro-node) (nfix n))))))))
    :hints (("goal" :use aignet-well-formedp-regnum
             :in-theory (disable aignet-well-formedp-regnum
                                 aignet-well-formedp))))

  (add-to-ruleset aignet-well-formedp-strong-rules aignet-well-formedp-regnum-id)

  (defthm aignet-well-formedp-outnum
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (nfix (num-outs aignet))))
             (let* ((id (nth-id n (nth *outsi* aignet)))
                    (node (nth-node id (nth *nodesi* aignet))))
               (and (aignet-idp id aignet)
                    (equal (node->type node) (out-type))
                    (equal (io-node->regp node) 0)
                    (equal (io-node->ionum node) (nfix n)))))
    :hints(("Goal" :in-theory (enable aignet-outnum-ok))))

  (defthmd aignet-well-formedp-outnum-id
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'id-equiv 'id '(nth-id n (nth *outsi* aignet))
                    mfc state)
                   (n))
                  (id-equiv id (nth-id n (nth *outsi* aignet)))
                  (< (nfix n) (nfix (num-outs aignet))))
             (let* ((node (nth-node id (nth *nodesi* aignet))))
               (and (equal (node->type node) (out-type))
                    (equal (io-node->regp node) 0)
                    (equal (io-node->ionum node) (nfix n)))))
    :hints (("goal" :use aignet-well-formedp-outnum
             :in-theory (disable aignet-well-formedp-outnum
                                 aignet-well-formedp))))

  (add-to-ruleset aignet-well-formedp-strong-rules aignet-well-formedp-outnum-id)

  (defthm aignet-well-formedp-const-node-is-0
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet))
             (equal (equal (node->type (nth-node n (nth *nodesi* aignet)))
                           (const-type))
                    (equal (id-val n) 0)))
    :hints(("Goal" :in-theory (enable aignet-well-formedp))))

  (defthm aignet-well-formedp-not-zero-when-non-const
    (implies (and (equal (node->type (nth-node n (nth *nodesi* aignet))) type)
                  (aignet-well-formedp aignet)
                  (not (equal type (const-type))))
             (posp (id-val n)))
; :hints(("Goal" :in-theory (enable aignet-well-formedp)))
    :rule-classes :forward-chaining)

  (defthm aignet-well-formedp-not-zero-when-non-const-nfix
    (implies (and (equal (node->type (nth-node (to-id n) (nth *nodesi* aignet))) type)
                  (aignet-well-formedp aignet)
                  (not (equal type (const-type))))
             (posp n))
; :hints(("Goal" :in-theory (enable aignet-well-formedp)))
    :rule-classes :forward-chaining)


  (defthm aignet-well-formedp-sizes-ok
    (implies (aignet-well-formedp aignet)
             (aignet-sizes-ok aignet))
    :hints(("Goal" :in-theory (enable aignet-well-formedp))))

  (defthm aignet-well-formedp-sizes-ok-linear
    (implies (aignet-well-formedp aignet)
             (and (<= (nth *num-ins* aignet)
                      (len (nth *insi* aignet)))
                  (<= (nth *num-outs* aignet)
                      (len (nth *outsi* aignet)))
                  (<= (nth *num-regs* aignet)
                      (len (nth *regsi* aignet)))
                  (<= (* 2 (nth *num-nodes* aignet))
                      (len (nth *nodesi* aignet)))
                  (< 0 (nth *num-nodes* aignet))))
    :hints(("Goal" :in-theory (enable aignet-well-formedp
                                      aignet-sizes-ok)))
    :rule-classes (:rewrite :linear))

  (defthm aignet-idp-0
    (implies (aignet-well-formedp aignet)
             (aignet-idp 0 aignet))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-litp-0-and-1
    (implies (aignet-well-formedp aignet)
             (and (aignet-litp 0 aignet)
                  (aignet-litp 1 aignet)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-litp-0
    (implies (aignet-well-formedp aignet)
             (aignet-litp 0 aignet))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (in-theory (disable aignet-well-formedp
                      aignet-gate-ok-implies-linear
                      aignet-gate-ok-implies-rw
                      aignet-in-ok-implies-linear
                      aignet-in-ok-implies-rw
                      aignet-reg-ok-implies-linear
                      aignet-reg-ok-implies-rw
                      aignet-out-ok-implies-linear
                      aignet-out-ok-implies-rw
                      aignet-regin-ok-implies-linear
                      aignet-regin-ok-implies-rw
                      aignet-nodes-ok-implies-0-const
                      aignet-innum-ok-implies
                      aignet-regnum-ok-implies
                      aignet-outnum-ok-implies
                      (:type-prescription aignet-well-formedp))))

(defsection regnum->ro


  (defthm equal-of-id-vals-when-idp
    (implies (and (idp a) (idp b))
             (equal (equal (id-val a) (id-val b))
                    (equal a b)))
    :hints (("goal" :use ((:instance id-fix-of-id (x a))
                          (:instance id-fix-of-id (x b))
                          (:instance id-equiv-implies-equal-id-fix-1
                           (x a) (x-equiv b)))
             :in-theory (disable id-fix-of-id
                                 equal-of-id-fix-backchain
                                 id-equiv-implies-equal-id-fix-1)))
    :otf-flg t)


  (definlined regnum->ro (n aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (< n (num-regs aignet)))))
    (b* ((id (regnum->id n aignet)))
      (if (int= (id->type id aignet) (in-type))
          id
        (regin-id->ro id aignet))))

  (local (in-theory (enable regnum->ro)))

  (def-aignet-frame regnum->ro)

  (defcong nat-equiv equal (regnum->ro n aignet) 1)

  (defthm idp-of-regnum->ro
    (idp (regnum->ro n aignet))
    :rule-classes (:rewrite :type-prescription))

  (defthm aignet-well-formedp-regnum->ro
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (num-regs aignet)))
             (and (equal (node->type (nth-node (regnum->ro n aignet)
                                               (nth *nodesi* aignet)))
                         (in-type))
                  (equal (io-node->regp (nth-node (regnum->ro n aignet)
                                                  (nth *nodesi* aignet)))
                         1)
                  (aignet-idp (regnum->ro n aignet) aignet)
                  (equal (io-node->ionum (nth-node (regnum->ro n aignet)
                                                   (nth *nodesi* aignet)))
                         (nfix n))))
    :hints (("goal" :in-theory (disable aignet-well-formedp-regnum)
             :use ((:instance aignet-well-formedp-regnum
                    (n n))))))

  (defthmd aignet-well-formedp-regnum->ro-id
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'id-equiv 'id '(regnum->ro n aignet)
                    mfc state)
                   (n))
                  (id-equiv id (regnum->ro n aignet))
                  (< (nfix n) (num-regs aignet)))
             (and (equal (node->type (nth-node id
                                               (nth *nodesi* aignet)))
                         (in-type))
                  (equal (io-node->regp (nth-node id
                                                  (nth *nodesi* aignet)))
                         1)
             (equal (io-node->ionum (nth-node id
                                              (nth *nodesi* aignet)))
                    (nfix n))))
    :hints (("goal" :in-theory (disable aignet-well-formedp-regnum->ro)
             :use ((:instance aignet-well-formedp-regnum->ro
                    (n n))))))

  (add-to-ruleset aignet-well-formedp-strong-rules
                  aignet-well-formedp-regnum->ro-id)


  (definline ro-id->regin (id aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-idp id aignet)
                                (equal (id->type id aignet) (in-type))
                                (equal (io-id->regp id aignet) 1))))
    (regnum->id (io-id->ionum id aignet) aignet))


  (defthm regin-id->ro-of-regnum-id
    (implies (equal (id->type (regnum->id n aignet) aignet) (out-type))
             (equal (regnum->ro n aignet)
                    (regin-node->ro (nth-node
                                     (nth-id n (nth *regsi* aignet))
                                     (nth *nodesi* aignet))))))

  (defthmd regnum->ro-is-regnum->id
    (implies (equal (id->type (regnum->id n aignet) aignet) (in-type))
             (equal (regnum->ro n aignet)
                    (regnum->id n aignet))))

  (defthm regnum->ro-of-ionum
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id aignet)
                  (equal (id->type id aignet) (in-type))
                  (equal (io-id->regp id aignet) 1))
             (equal (regnum->ro (io-node->ionum
                                 (nth-node id (nth *nodesi* aignet)))
                                aignet)
                    id))
    :hints(("Goal" :in-theory (e/d* (aignet-well-formedp-strong-rules)
                                    (aignet-well-formedp-reg-rw
                                     aignet-well-formedp-reg-rw-regnum))
            :use ((:instance aignet-well-formedp-reg-rw
                   (n id))))))

  (defthmd regnum->ro-of-ionum-rw-strong
    (implies (and (aignet-well-formedp aignet)
                  (bind-free
                   (match-equiv-or-refinement
                    'nat-equiv 'n '(io-node->ionum
                                    (nth-node id (nth *nodesi* aignet)))
                    mfc state)
                   (id))
                  (nat-equiv n (io-node->ionum
                                (nth-node id (nth *nodesi* aignet))))
                  (aignet-idp id aignet)
                  (equal (id->type id aignet) (in-type))
                  (equal (io-id->regp id aignet) 1))
             (equal (regnum->ro n aignet)
                    id))
    :hints(("Goal" :in-theory (e/d* (aignet-well-formedp-strong-rules)
                                    (aignet-well-formedp-reg-rw
                                     aignet-well-formedp-reg-rw-regnum))
            :use ((:instance aignet-well-formedp-reg-rw
                   (n id))))))

  (add-to-ruleset aignet-well-formedp-strong-rules regnum->ro-of-ionum-rw-strong))

(defsection ionum-uniqueness
  (defthm in-node-ionums-unique
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id1 aignet)
                  (aignet-idp id2 aignet)
                  (equal (id->type id1 aignet) (in-type))
                  (equal (io-id->regp id1 aignet) 0)
                  (equal (id->type id2 aignet) (in-type))
                  (equal (io-id->regp id2 aignet) 0))
             (equal (equal (io-node->ionum (nth-node id1 (nth *nodesi* aignet)))
                           (io-node->ionum (nth-node id2 (nth *nodesi* aignet))))
                    (id-equiv id1 id2)))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-in-rw
                          (n id1))
                         (:instance aignet-well-formedp-in-rw
                          (n id2)))
                   :in-theory (disable aignet-well-formedp-in-rw)))))

  (defthm innum-ids-unique
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n1) (num-ins aignet))
                  (< (nfix n2) (num-ins aignet)))
             (equal (equal (nth-id n1 (nth *insi* aignet))
                           (nth-id n2 (nth *insi* aignet)))
                    (nat-equiv n1 n2)))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-innum
                          (n n1))
                         (:instance aignet-well-formedp-innum
                          (n n2)))
                   :in-theory (disable aignet-well-formedp-innum)))))

  (defthm out-node-ionums-unique
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id1 aignet)
                  (aignet-idp id2 aignet)
                  (equal (id->type id1 aignet) (out-type))
                  (equal (io-id->regp id1 aignet) 0)
                  (equal (id->type id2 aignet) (out-type))
                  (equal (io-id->regp id2 aignet) 0))
             (equal (equal (io-node->ionum (nth-node id1 (nth *nodesi* aignet)))
                           (io-node->ionum (nth-node id2 (nth *nodesi* aignet))))
                    (id-equiv id1 id2)))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-out-rw
                          (n id1))
                         (:instance aignet-well-formedp-out-rw
                          (n id2)))
                   :in-theory (disable aignet-well-formedp-out-rw)))))

  (defthm outnum-ids-unique
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n1) (num-outs aignet))
                  (< (nfix n2) (num-outs aignet)))
             (equal (equal (nth-id n1 (nth *outsi* aignet))
                           (nth-id n2 (nth *outsi* aignet)))
                    (nat-equiv n1 n2)))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-outnum
                          (n n1))
                         (:instance aignet-well-formedp-outnum
                          (n n2)))
                   :in-theory (disable aignet-well-formedp-outnum))))
    :otf-flg t)


  (defthm ro-node-ionums-unique
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id1 aignet)
                  (aignet-idp id2 aignet)
                  (equal (id->type id1 aignet) (in-type))
                  (equal (io-id->regp id1 aignet) 1)
                  (equal (id->type id2 aignet) (in-type))
                  (equal (io-id->regp id2 aignet) 1))
             (equal (equal (io-node->ionum (nth-node id1 (nth *nodesi* aignet)))
                           (io-node->ionum (nth-node id2 (nth *nodesi* aignet))))
                    (id-equiv id1 id2)))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-reg-rw
                          (n id1))
                         (:instance aignet-well-formedp-reg-rw
                          (n id2))
                         (:instance aignet-well-formedp-regin-rw
                          (n (regnum->id (io-id->ionum id1 aignet) aignet)))
                         (:instance aignet-well-formedp-regin-rw
                          (n (regnum->id (io-id->ionum id1 aignet) aignet))))
                   :in-theory (disable aignet-well-formedp-reg-rw
                                       aignet-well-formedp-regin-rw)))))

  (defthm ri-node-ros-unique
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id1 aignet)
                  (aignet-idp id2 aignet)
                  (equal (id->type id1 aignet) (out-type))
                  (equal (io-id->regp id1 aignet) 1)
                  (equal (id->type id2 aignet) (out-type))
                  (equal (io-id->regp id2 aignet) 1)
                  (not (equal (id-val (regin-id->ro id1 aignet)) 0)))
             (equal (equal (regin-node->ro
                            (nth-node id1 (nth *nodesi* aignet)))
                           (regin-node->ro
                            (nth-node id2 (nth *nodesi* aignet))))
                    (id-equiv id1 id2)))
    :hints ((and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-regin-rw
                          (n id1))
                         (:instance aignet-well-formedp-regin-rw
                          (n id2))
                         (:instance aignet-well-formedp-reg-rw
                          (n (regin-id->ro id1 aignet)))
                         (:instance aignet-well-formedp-reg-rw
                          (n (regin-id->ro id2 aignet))))
                   :in-theory (disable aignet-well-formedp-reg-rw
                                       aignet-well-formedp-regin-rw)))))

  (defthm ri-node-ionums-unique
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id1 aignet)
                  (aignet-idp id2 aignet)
                  (equal (id->type id1 aignet) (out-type))
                  (equal (io-id->regp id1 aignet) 1)
                  (equal (id->type id2 aignet) (out-type))
                  (equal (io-id->regp id2 aignet) 1)
                  (not (equal (id-val (regin-id->ro id1 aignet)) 0))
                  (not (equal (id-val (regin-id->ro id2 aignet)) 0)))
             (equal (equal (io-node->ionum
                            (nth-node
                             (regin-node->ro
                              (nth-node id1 (nth *nodesi* aignet)))
                             (nth *nodesi* aignet)))
                           (io-node->ionum
                            (nth-node
                             (regin-node->ro
                              (nth-node id2 (nth *nodesi* aignet)))
                             (nth *nodesi* aignet))))
                    (id-equiv id1 id2))))

  (defthm regnum->ro-unique
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n1) (num-regs aignet))
                  (< (nfix n2) (num-regs aignet)))
             (equal (equal (regnum->ro n1 aignet)
                           (regnum->ro n2 aignet))
                    (nat-equiv n1 n2)))
    :hints (("goal" :use ((:instance aignet-well-formedp-regnum->ro
                           (n n1))
                          (:instance aignet-well-formedp-regnum->ro
                           (n n2)))
             :in-theory (disable aignet-well-formedp-regnum->ro))))

  (defthm regnum->id-unique
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n1) (num-regs aignet))
                  (< (nfix n2) (num-regs aignet)))
             (equal (equal (regnum->id n1 aignet)
                           (regnum->id n2 aignet))
                    (nat-equiv n1 n2)))
    :hints (("goal" :use ((:instance aignet-well-formedp-regnum
                           (n n1))
                          (:instance aignet-well-formedp-regnum
                           (n n2)))
             :in-theory (disable aignet-well-formedp-regnum)))))

(defsection aignet-extension-p
  :short "Predicate that says that one aignet is the result of building some new
nodes onto another aignet"
  :long "<p>Pretty much every aignet-modifying function produces an extension of
its input.  Net-extension-p is a transitive, reflexive relation that implies a
whole slew of useful things.  The most basic is that any ID of the original
aignet is an ID of the new aignet, and the node of that ID is the same in both aignets
-- this is just a reading of the definition.  But this implies, for example,
that the evaluations of nodes existing in the first are the same as their
evaluations in the second.</p>

<p>Rewrite rules using aignet-extension-p are a little odd.  For example, suppose we
want a rewrite rule just based on the definition, e.g.,
<code>
 (implies (and (aignet-extension-p new-aignet orig-aignet)
               (aignet-idp id orig-aignet))
          (equal (nth-node id new-aignet)
                 (nth-node id orig-aignet)))
</code>
This isn't a very good rewrite rule because it has to match the free variable
orig-aignet.  However, we can make it much better with a bind-free strategy.
We'll check the syntax of new-aignet to see if it is a call of a
aignet-updating function.  Then, we'll use the aignet input of that function as the
binding for orig-aignet.</p>
"

  (defun-sk aignet-extension-p (new-aignet orig-aignet)
    (forall id
            (implies (aignet-idp id orig-aignet)
                     (and (aignet-idp id new-aignet)
                          (equal (nth-node id (nth *nodesi* new-aignet))
                                 (nth-node id (nth *nodesi* orig-aignet))))))
    :rewrite :direct)

  ;; (defthmd aignet-extension-p-transitive
  ;;   (implies (and (aignet-extension-p aignet2 aignet1)
  ;;                 (aignet-extension-p aignet3 aignet2))
  ;;            (aignet-extension-p aignet3 aignet1)))

  (defun simple-search-type-alist (term typ type-alist unify-subst)
    (declare (xargs :mode :program))
    (cond ((endp type-alist)
           (mv nil unify-subst))
          ((acl2::ts-subsetp (cadr (car type-alist)) typ)
           (mv-let (ans unify-subst)
             (acl2::one-way-unify1 term (car (car type-alist)) unify-subst)
             (if ans
                 (mv t unify-subst)
               ;; note: one-way-unify1 is a no-change-loser so unify-subst is
               ;; unchanged below
               (simple-search-type-alist term typ (cdr type-alist)
                                         unify-subst))))
          (t (simple-search-type-alist term typ (cdr type-alist) unify-subst))))


  ;; Additional possible strategic thing: keep aignet-modifying functions that
  ;; don't produce an extension in a table and don't bind their inputs.
  (defun find-prev-stobj-binding (new-term state)
    (declare (xargs :guard (pseudo-termp new-term)
                    :stobjs state
                    :mode :program))
    (b* (((mv valnum function args)
          (case-match new-term
            (('mv-nth ('quote valnum) (function . args) . &)
             (mv (and (symbolp function) valnum) function args))
            ((function . args)
             (mv (and (symbolp function) 0) function args))
            (& (mv nil nil nil))))
         ((unless valnum) (mv nil nil))
         (w (w state))
         (stobjs-out (acl2::stobjs-out function w))
         (formals (acl2::formals function w))
         (stobj-out (nth valnum stobjs-out))
         ((unless stobj-out) (mv nil nil))
         (pos (position stobj-out formals))
         ((unless pos) (mv nil nil)))
      (mv t (nth pos args))))

  (defun iterate-prev-stobj-binding (n new-term state)
    (declare (xargs :guard (and (pseudo-termp new-term)
                                (natp n))
                    :stobjs state
                    :mode :program))
    (if (zp n)
        new-term
      (mv-let (ok next-term)
        (find-prev-stobj-binding new-term state)
        (if ok
            (iterate-prev-stobj-binding (1- n) next-term state)
          new-term))))

  (defun prev-stobj-binding (new-term prev-var iters mfc state)
    (declare (xargs :guard (and (pseudo-termp new-term)
                                (symbolp prev-var))
                    :stobjs state
                    :mode :program)
             (ignore mfc))
    (let ((prev-term (iterate-prev-stobj-binding iters new-term state)))
      (if (equal new-term prev-term)
          `((do-not-use-this-long-horrible-variable . 'nil))
        `((,prev-var . ,prev-term)))))

  (defmacro aignet-extension-binding (&key (new-aignet 'new-aignet)
                                           (orig-aignet 'orig-aignet)
                                           (fall-through 't)
                                           (iters '1))
    `(bind-free (prev-stobj-binding ,new-aignet ',orig-aignet ',iters mfc state)
                . ,(if fall-through nil `((,orig-aignet)))))

  ;; expands aignet-extension-p if it appears as a positive literal
  (defthmd prove-aignet-extension-p
    (implies (acl2::rewriting-positive-literal `(aignet-extension-p ,new-aignet ,orig-aignet))
             (equal (aignet-extension-p new-aignet orig-aignet)
                    (let ((id (acl2::aignet-extension-p-witness new-aignet orig-aignet)))
                      (implies (aignet-idp id orig-aignet)
                               (and (aignet-idp id new-aignet)
                                    (equal (nth-node id (nth *nodesi* new-aignet))
                                           (nth-node id (nth *nodesi* orig-aignet)))))))))

  (defthm aignet-extension-p-transitive
    (implies (and (aignet-extension-binding :new-aignet aignet3 :orig-aignet aignet2)
                  (aignet-extension-p aignet3 aignet2)
                  (aignet-extension-p aignet2 aignet1))
             (aignet-extension-p aignet3 aignet1))
    :hints(("Goal" :in-theory (disable aignet-extension-p)
            :expand ((aignet-extension-p aignet3 aignet1))
            :use ((:instance acl2::aignet-extension-p-necc
                   (new-aignet aignet2) (orig-aignet aignet1)
                   (id (acl2::aignet-extension-p-witness aignet3 aignet1)))
                  (:instance acl2::aignet-extension-p-necc
                   (new-aignet aignet3) (orig-aignet aignet2)
                   (id (acl2::aignet-extension-p-witness aignet3 aignet1))))))
    :rule-classes ((:rewrite :match-free :all)))

  (defthmd aignet-extension-p-transitive-match-free
    (implies (and (aignet-extension-p aignet3 aignet2)
                  (aignet-extension-p aignet2 aignet1))
             (aignet-extension-p aignet3 aignet1))
    :hints (("goal" :use aignet-extension-p-transitive
             :in-theory (disable aignet-extension-p-transitive)))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm aignet-extension-p-reflexive
    (aignet-extension-p aignet aignet))

  (in-theory (disable aignet-extension-p))

  (defthm aignet-extension-simplify-nth-node
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-idp id orig-aignet))
             (equal (nth-node id (nth *nodesi* new-aignet))
                    (nth-node id (nth *nodesi* orig-aignet)))))

  (defthm aignet-extension-simplify-aignet-idp
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-idp id orig-aignet))
             (aignet-idp id new-aignet)))

  (in-theory (disable acl2::aignet-extension-p-necc))

  (defthm aignet-extension-simplify-aignet-litp
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-litp lit orig-aignet))
             (aignet-litp lit new-aignet))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-extension-num-nodes-linear-nfix
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet))
             (<= (nfix (nth *num-nodes* orig-aignet))
                 (nfix (nth *num-nodes* new-aignet))))
    :hints (("goal" :use ((:instance acl2::aignet-extension-p-necc
                           (id (to-id (1- (nfix (nth *num-nodes* orig-aignet)))))))
             :in-theory (e/d (aignet-idp)
                             (aignet-extension-simplify-aignet-idp))))
    :rule-classes ((:linear :trigger-terms ((nfix (nth *num-nodes* new-aignet))))))

  (defthm aignet-extension-num-nodes-linear
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (natp (nth *num-nodes* new-aignet)))
             (<= (nfix (nth *num-nodes* orig-aignet))
                 (nth *num-nodes* new-aignet)))
    :hints (("goal" :use ((:instance acl2::aignet-extension-p-necc
                           (id (to-id (1- (nfix (nth *num-nodes* orig-aignet)))))))
             :in-theory (e/d (aignet-idp)
                             (aignet-extension-simplify-aignet-idp))))
    :rule-classes ((:linear :trigger-terms ((nth *num-nodes* new-aignet)))))

  (defthm aignet-extension-implies-aignet-lit-listp
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-lit-listp lits orig-aignet))
             (aignet-lit-listp lits new-aignet)))

  (defthm aignet-extension-implies-aignet-lit-alistp
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-lit-alistp lital orig-aignet))
             (aignet-lit-alistp lital new-aignet)))


  (defthm aignet-extension-implies-num-ins-incr
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet))
             (<= (nth *num-ins* orig-aignet)
                 (nth *num-ins* new-aignet)))
    :hints (("goal" :use ((:instance aignet-well-formedp-in-linear
                           (n (innum->id (1- (nth *num-ins* orig-aignet)) orig-aignet))
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-in-rw)))
    :rule-classes ((:linear :trigger-terms ((nth *num-ins* new-aignet)))))

  (defthm aignet-extension-implies-num-outs-incr
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet))
             (<= (nth *num-outs* orig-aignet)
                 (nth *num-outs* new-aignet)))
    :hints (("goal" :use ((:instance aignet-well-formedp-out-linear
                           (n (outnum->id (1- (nth *num-outs* orig-aignet)) orig-aignet))
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-out-rw)))
    :rule-classes ((:linear :trigger-terms ((nth *num-outs* new-aignet)))))

  (defthm aignet-extension-implies-num-regs-incr
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet))
             (<= (nth *num-regs* orig-aignet)
                 (nth *num-regs* new-aignet)))
    :hints (("goal" :use ((:instance aignet-well-formedp-reg-linear
                           (n (let ((id (regnum->id (1- (nth *num-regs*
                                                             orig-aignet))
                                                    orig-aignet)))
                                (if (equal (id->type id orig-aignet) (in-type))
                                    id
                                  (regin-id->ro id orig-aignet))))
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-reg-linear)))
    :rule-classes ((:linear :trigger-terms ((nth *num-regs* new-aignet)))))

  (defthm aignet-extension-preserves-innum->id
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (< (nfix n) (num-ins orig-aignet)))
             (equal (nth-id n (nth *insi* new-aignet))
                    (nth-id n (nth *insi* orig-aignet))))
    :hints (("goal" :use ((:instance aignet-well-formedp-in-rw
                           (n (nth-id n (nth *insi* new-aignet)))
                           (aignet new-aignet))
                          (:instance aignet-well-formedp-in-rw
                           (n (nth-id n (nth *insi* orig-aignet)))
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-in-rw))))

  (defthm aignet-extension-new-in
    (implies (and (syntaxp (not (equal new-aignet orig-aignet)))
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (< (nfix n) (num-ins new-aignet))
                  (<= (num-ins orig-aignet) (nfix n)))
             (not (aignet-idp (nth-id n (nth *insi* new-aignet)) orig-aignet)))
    :hints (("goal" :use ((:instance aignet-well-formedp-innum
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-innum))))

  (defthm aignet-extension-preserves-outnum->id
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (< (nfix n) (num-outs orig-aignet)))
             (equal (nth-id n (nth *outsi* new-aignet))
                    (nth-id n (nth *outsi* orig-aignet))))
    :hints (("goal" :use ((:instance aignet-well-formedp-out-rw
                           (n (nth-id n (nth *outsi* new-aignet)))
                           (aignet new-aignet))
                          (:instance aignet-well-formedp-out-rw
                           (n (nth-id n (nth *outsi* orig-aignet)))
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-out-rw))))

  (defthm aignet-extension-new-out
    (implies (and (syntaxp (not (equal new-aignet orig-aignet)))
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (< (nfix n) (num-outs new-aignet))
                  (<= (num-outs orig-aignet) (nfix n)))
             (not (aignet-idp (nth-id n (nth *outsi* new-aignet)) orig-aignet)))
    :hints (("goal" :use ((:instance aignet-well-formedp-outnum
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-outnum))))


  (defthm regnum->ro-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (aignet-well-formedp orig-aignet)
                  (< (nfix n) (num-regs orig-aignet)))
             (equal (regnum->ro n new-aignet)
                    (regnum->ro n orig-aignet)))
    :hints (("goal" :use ((:instance aignet-well-formedp-reg-rw
                           (n (regnum->ro n new-aignet))
                           (aignet new-aignet))
                          (:instance aignet-well-formedp-reg-rw
                           (n (regnum->ro n orig-aignet))
                           (aignet new-aignet)))
             :in-theory (e/d ()
                             (aignet-well-formedp-reg-rw)))))

  (defthm regnum->id-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (aignet-well-formedp orig-aignet)
                  (< (nfix n) (num-regs orig-aignet))
                  (equal (id->type (regnum->id n orig-aignet) orig-aignet) (out-type)))
             (equal (nth-id n (nth *regsi* new-aignet))
                    (nth-id n (nth *regsi* orig-aignet))))
    :hints (("goal" :cases
             ((equal (id->type (regnum->id n new-aignet) new-aignet)
                     (out-type))))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-regin-rw
                          (n (regnum->id n new-aignet))
                          (aignet new-aignet))
                         (:instance aignet-well-formedp-regin-rw
                          (n (regnum->id n orig-aignet))
                          (aignet new-aignet))
                         regnum->ro-of-extension)
                   :expand ((regnum->ro n orig-aignet))
                   :in-theory (e/d ()
                                   (aignet-well-formedp-regin-rw
                                    regnum->ro-of-extension))))))

  (defthm aignet-extension-new-reg
    (implies (and (syntaxp (not (equal new-aignet orig-aignet)))
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (< (nfix n) (num-regs new-aignet))
                  (<= (num-regs orig-aignet) (nfix n)))
             (not (aignet-idp (nth-id n (nth *regsi* new-aignet)) orig-aignet)))
    :hints (("goal" :use ((:instance aignet-well-formedp-regnum
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-regnum))))

  (defthm aignet-extension-new-reg->ro
    (implies (and (syntaxp (not (equal new-aignet orig-aignet)))
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-well-formedp orig-aignet)
                  (aignet-well-formedp new-aignet)
                  (< (nfix n) (num-regs new-aignet))
                  (<= (num-regs orig-aignet) (nfix n)))
             (not (aignet-idp (regnum->ro n new-aignet) orig-aignet)))
    :hints (("goal" :use ((:instance aignet-well-formedp-regnum->ro
                           (aignet new-aignet)))
             :in-theory (disable aignet-well-formedp-regnum->ro)))))

(defsection preservation-thms
  (acl2::def-stobj-preservation-macros
    :name aignet
    :default-stobjname aignet
    :templates aignet-preservation-templates
    :history aignet-preservation-history)

  (add-aignet-preservation-thm
   aignet-extension-p
   :body `(aignet-extension-p ,new-stobj ,orig-stobj)
   :hints `(,@expand/induct-hints
            (and stable-under-simplificationp
                 '(:in-theory (enable prove-aignet-extension-p)))
            (and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp)))))

  ;; ;; obsoleted by aignet-extension-p
  ;; (add-aignet-preservation-thm
  ;;  aignet-litp-preserved
  ;;  :vars (lit)
  ;;  :body
  ;;  `(implies (aignet-litp lit ,orig-stobj)
  ;;            (aignet-litp lit ,new-stobj))
  ;;  :hints `(,@expand/induct-hints
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable aignet-litp)))
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable aignet-idp)))))

  ;; ;; obsoleted by aignet-extension-p
  ;; (add-aignet-preservation-thm
  ;;  aignet-idp-preserved
  ;;  :vars (id)
  ;;  :body `(implies (aignet-idp id ,orig-stobj)
  ;;                  (aignet-idp id ,new-stobj))
  ;;  :hints `(,@expand/induct-hints
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable aignet-idp)))))

  ;; not yet:
  ;; (add-aignet-preservation-thm
  ;;  aignet-well-formedp
  ;;  :body `(implies (aignet-well-formedp ,orig-stobj)
  ;;                  (aignet-well-formedp ,new-stobj))
  ;;  :hints expand-induct-hints)

  ;; ;; obsoleted by aignet-extension-p
  ;; (add-aignet-preservation-thm
  ;;  nth-node-preserved
  ;;  :vars (id)
  ;;  :body `(implies (aignet-idp id ,orig-stobj)
  ;;                  (equal (nth-node id (nth ',*nodesi* ,new-stobj))
  ;;                         (nth-node id (nth ',*nodesi* ,orig-stobj))))
  ;;  :hints `(,@expand/induct-hints
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable aignet-idp)))))

  ;; ;; obsoleted by aignet-extension-p
  ;; (add-aignet-preservation-thm
  ;;  aignet-lit-listp-preserved
  ;;  :vars (lits)
  ;;  :body `(implies (aignet-lit-listp lits ,orig-stobj)
  ;;                  (aignet-lit-listp lits ,new-stobj))
  ;;  :hints `(("goal" :induct (aignet-lit-listp lits ,orig-stobj)
  ;;            :in-theory (e/d (aignet-lit-listp) (,fn$)))))

  ;; ;; obsoleted by aignet-extension-p
  ;; (add-aignet-preservation-thm
  ;;  aignet-lit-alistp-preserved
  ;;  :vars (lital)
  ;;  :body `(implies (aignet-lit-alistp lital ,orig-stobj)
  ;;                  (aignet-lit-alistp lital ,new-stobj))
  ;;  :hints `(("goal" :induct (aignet-lit-alistp lital ,orig-stobj)
  ;;            :in-theory (e/d (aignet-lit-alistp) (,fn$)))))

  (add-aignet-preservation-thm
   num-nodes-natp
   :body `(implies (natp (nth *num-nodes* ,orig-stobj))
                   (natp (nth *num-nodes* ,new-stobj)))
   :hints `(,@expand/induct-hints)
   :rule-classes '(:rewrite :type-prescription))

  ;; ;; obsoleted by aignet-extension-p
  ;; (add-aignet-preservation-thm
  ;;  num-nodes-increasing-nfix
  ;;  :body `(<= (nfix (nth *num-nodes* ,orig-stobj))
  ;;            (nfix (nth *num-nodes* ,new-stobj)))
  ;;  :hints `(,@expand/induct-hints)
  ;;  :rule-classes '(:rewrite :linear))

  ;; ;; obsoleted by aignet-extension-p
  ;; (add-aignet-preservation-thm
  ;;  num-nodes-increasing
  ;;  :body `(implies (natp (nth *num-nodes* ,new-stobj))
  ;;                  (<= (nfix (nth *num-nodes* ,orig-stobj))
  ;;                      (nth *num-nodes* ,new-stobj)))
  ;;  :hints `(,@expand/induct-hints)
  ;;  :rule-classes '(:rewrite :linear))
  )

(defsection maybe-grow-arrays

  (local (in-theory (enable acl2::nth-of-resize-list-split)))
  (local (in-theory (enable acl2::aignetp)))

  (defthm nth-node-of-resize-list
    (implies (<= (len lst) (nfix m))
             (equal (nth-node n (resize-list lst m 0))
                    (nth-node n lst)))
    :hints(("Goal" :in-theory (enable nth-node
                                      acl2::nth-with-large-index))))

  ;; Reallocate the array if there isn't room to add an node.
  (definlined maybe-grow-nodes (aignet)
    (declare (xargs :stobjs aignet))
    (let ((target (+ 2 (* 2 (lnfix (num-nodes aignet))))))
      (if (< (nodes-length aignet) target)
          (resize-nodes (max 16 (* 2 target)) aignet)
        aignet)))

  (local (in-theory (enable maybe-grow-nodes)))

  (def-aignet-frame maybe-grow-nodes)
  (def-aignet-preservation-thms maybe-grow-nodes)

  (defthm nth-node-of-maybe-grow-nodes
    (equal (nth-node id (nth *nodesi* (maybe-grow-nodes aignet)))
           (nth-node id (nth *nodesi* aignet))))

  (defthm len-nodes-of-maybe-grow-nodes
    (<= (+ 2 (* 2 (nfix (nth *num-nodes* aignet))))
        (len (nth *nodesi* (maybe-grow-nodes aignet))))
    :rule-classes ((:linear :trigger-terms
                    ((len (nth *nodesi* (maybe-grow-nodes aignet)))))))

  (defthm aignet-sizes-ok-of-maybe-grow-nodes
    (implies (aignet-sizes-ok aignet)
             (aignet-sizes-ok (maybe-grow-nodes aignet))))

  (defthm len-of-maybe-grow-nodes
    (<= (len aignet) (len (maybe-grow-nodes aignet)))
    :rule-classes :linear)


  (definlined maybe-grow-ins (aignet)
    (declare (xargs :stobjs aignet))
    (let ((target (+ 1 (lnfix (num-ins aignet)))))
      (if (< (ins-length aignet) target)
          (resize-ins (max 16 (* 2 target)) aignet)
        aignet)))

  (def-aignet-frame maybe-grow-ins)
  (def-aignet-preservation-thms maybe-grow-ins)

  (local (in-theory (enable maybe-grow-ins)))

  (defthm nth-in-of-maybe-grow-ins
    (id-equiv (nth-id n (nth *insi* (maybe-grow-ins aignet)))
              (nth-id n (nth *insi* aignet)))
    :hints(("Goal" :in-theory (enable nth-id acl2::nth-with-large-index))))

  (defthm len-ins-of-maybe-grow-ins
    (<= (+ 1 (nfix (nth *num-ins* aignet)))
        (len (nth *insi* (maybe-grow-ins aignet))))
    :rule-classes ((:linear :trigger-terms
                    ((len (nth *insi* (maybe-grow-ins aignet)))))))

  (defthm aignet-sizes-ok-of-maybe-grow-ins
    (implies (aignet-sizes-ok aignet)
             (aignet-sizes-ok (maybe-grow-ins aignet))))

  (defthm len-of-maybe-grow-ins
    (<= (len aignet) (len (maybe-grow-ins aignet)))
    :rule-classes :linear)


  (definlined maybe-grow-regs (aignet)
    (declare (xargs :stobjs aignet))
    (let ((target (+ 1 (lnfix (num-regs aignet)))))
      (if (< (regs-length aignet) target)
          (resize-regs (max 16 (* 2 target)) aignet)
        aignet)))

  (def-aignet-frame maybe-grow-regs)
  (def-aignet-preservation-thms maybe-grow-regs)

  (local (in-theory (enable maybe-grow-regs)))

  (defthm nth-reg-of-maybe-grow-regs
    (id-equiv (nth-id n (nth *regsi* (maybe-grow-regs aignet)))
              (nth-id n (nth *regsi* aignet)))
    :hints(("Goal" :in-theory (enable acl2::nth-with-large-index nth-id))))

  (defthm len-regs-of-maybe-grow-regs
    (<= (+ 1 (nfix (nth *num-regs* aignet)))
        (len (nth *regsi* (maybe-grow-regs aignet))))
    :rule-classes ((:linear :trigger-terms
                    ((len (nth *regsi* (maybe-grow-regs aignet)))))))

  (defthm aignet-sizes-ok-of-maybe-grow-regs
    (implies (aignet-sizes-ok aignet)
             (aignet-sizes-ok (maybe-grow-regs aignet))))

  (defthm len-of-maybe-grow-regs
    (<= (len aignet) (len (maybe-grow-regs aignet)))
    :rule-classes :linear)

  (definlined maybe-grow-outs (aignet)
    (declare (xargs :stobjs aignet))
    (let ((target (+ 1 (lnfix (num-outs aignet)))))
      (if (< (outs-length aignet) target)
          (resize-outs (max 16 (* 2 target)) aignet)
        aignet)))

  (def-aignet-frame maybe-grow-outs)
  (def-aignet-preservation-thms maybe-grow-outs)

  (local (in-theory (enable maybe-grow-outs)))

  (defthm nth-out-of-maybe-grow-outs
    (id-equiv (nth-id n (nth *outsi* (maybe-grow-outs aignet)))
              (nth-id n (nth *outsi* aignet)))
    :hints(("Goal" :in-theory (enable acl2::nth-with-large-index nth-id))))

  (defthm len-outs-of-maybe-grow-outs
    (<= (+ 1 (nfix (nth *num-outs* aignet)))
        (len (nth *outsi* (maybe-grow-outs aignet))))
    :rule-classes ((:linear :trigger-terms
                    ((len (nth *outsi* (maybe-grow-outs aignet)))))))

  (defthm aignet-sizes-ok-of-maybe-grow-outs
    (implies (aignet-sizes-ok aignet)
             (aignet-sizes-ok (maybe-grow-outs aignet))))

  (defthm len-of-maybe-grow-outs
    (<= (len aignet) (len (maybe-grow-outs aignet)))
    :rule-classes :linear))

(defsection aignet-lit-fix

  (local (in-theory (enable aignet-litp)))

  (definlined aignet-lit-fix (x aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp x aignet))))
    (mbe :logic
         (b* ((x (lit-fix x))
              ((when (aignet-litp x aignet)) x)
              (id (lit-id x))
              ((unless (aignet-idp id aignet))
               (mk-lit 0 (lit-neg x))))
           ;; id is valid but of output type
           (lit-negate-cond (co-id->fanin id aignet) (lit-neg x)))
         :exec x))

  (local (in-theory (e/d (aignet-lit-fix))))

  (defcong lit-equiv equal (aignet-lit-fix x aignet) 1)

  (defthm aignet-lit-fix-when-aignet-litp
    (implies (aignet-litp x aignet)
             (equal (aignet-lit-fix x aignet) x)))

  (defthm aignet-litp-of-aignet-lit-fix
    (implies (aignet-well-formedp aignet)
             (aignet-litp (aignet-lit-fix x aignet) aignet))))

(defsection aignet-unconnected-reg-fix

  (definlined aignet-unconnected-reg-p (x aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-idp x aignet))))
    (and (int= (id->type x aignet) (in-type))
         (int= (io-id->regp x aignet) 1)
         (id-equiv (regnum->id
                    (io-id->ionum x aignet) aignet)
                   x)))

  (local (in-theory (enable aignet-unconnected-reg-p)))

  (defcong id-equiv equal (aignet-unconnected-reg-p x aignet) 1)

  (local (defthm equal-when-to-id-of-id-val-equal
           (implies (and (equal (to-id (id-val x))
                                (to-id (id-val y)))
                         (idp x)
                         (idp y))
                    (equal (equal x y) t))))

  (definlined aignet-unconnected-reg-fixup (x aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-idp x aignet)
                                (or (int= 0 (id-val x))
                                    (aignet-unconnected-reg-p x aignet)))))
    (mbe :logic (let ((x (id-fix x)))
                  (if (and (aignet-idp x aignet)
                           (aignet-unconnected-reg-p x aignet))
                      x
                    0))
         :exec x))

  (local (in-theory (e/d (aignet-unconnected-reg-fixup))))

  (defcong id-equiv equal (aignet-unconnected-reg-fixup x aignet) 1)

  (defthm aignet-unconnected-reg-fix-of-unconnected-reg
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp x aignet)
                  (or (int= 0 (id-val x))
                      (aignet-unconnected-reg-p x aignet)))
             (equal (aignet-unconnected-reg-fixup x aignet) x))
    :hints(("Goal" :in-theory (disable (to-id)))))

  (defthm aignet-idp-of-aignet-unconnected-reg-fixup
    (implies (aignet-well-formedp aignet)
             (aignet-idp (aignet-unconnected-reg-fixup x aignet) aignet)))

  (defthm aignet-unconnected-reg-p-of-aignet-unconnected-reg-fixup
    (implies (and (aignet-well-formedp aignet)
                  (not (equal 0 (id-val (aignet-unconnected-reg-fixup x aignet)))))
             (aignet-unconnected-reg-p (aignet-unconnected-reg-fixup x aignet) aignet)))

  ;; Silly hack.  Add a placeholder for the aignet-well-formedp preservation
  ;; thm here.
  (table aignet-preservation-templates 'aignet-well-formedp nil)

  (add-aignet-preservation-thm
   aignet-unconnected-reg-p-preserved
   :vars (id)
   :body `(implies (and (aignet-well-formedp ,orig-stobj)
                        (aignet-unconnected-reg-p id ,orig-stobj)
                        (aignet-idp id ,orig-stobj))
                   (aignet-unconnected-reg-p id ,new-stobj))
   :hints `(,@expand/induct-hints
            (and stable-under-simplificationp
                 '(:in-theory (e/d (aignet-unconnected-reg-p)
                                   (,fn$)))))))

(defsection add-nodes

  (local (in-theory (enable nth-node-of-update-nth-node-split)))
  (local (in-theory (enable* aignet-frame-thms)))
  (add-default-hints '((and stable-under-simplificationp
                            '(:in-theory (enable aignet-litp)))
                       (and stable-under-simplificationp
                            '(:in-theory (enable aignet-idp)))))

  ;; To make these similar to the eventual aignet-add-simp-gate, which needs to return
  ;; a literal because simplification might reduce the gate to something
  ;; negated (e.g., 1 & ~a), we return the literal from each of these, even
  ;; though it is easily determined from the aignet.
  (definlined aignet-add-in (aignet)
    (declare (xargs :stobjs aignet
                    :guard (aignet-well-formedp aignet)))
    (b* ((aignet (maybe-grow-nodes aignet))
         (aignet (maybe-grow-ins aignet))
         (id  (to-id (num-nodes aignet)))
         (lit (mk-lit id 0))
         (pi-num  (lnfix (num-ins aignet)))
         (aignet (update-num-ins (+ 1 pi-num) aignet))
         (aignet (update-num-nodes (+ 1 (id-val id)) aignet))
         (aignet (set-innum->id pi-num id aignet))
         (aignet (set-in-node id pi-num aignet)))
      (mv lit aignet)))

  (local (in-theory (enable aignet-add-in)))

  (def-aignet-frame aignet-add-in)
  (def-aignet-preservation-thms aignet-add-in)

  (defthm aignet-add-in-new-lit
    (equal (mv-nth 0 (aignet-add-in aignet))
           (mk-lit (to-id (num-nodes aignet)) 0)))

  (defthm aignet-add-in-num-nodes
    (equal (nth *num-nodes* (mv-nth 1 (aignet-add-in aignet)))
           (+ 1 (nfix (num-nodes aignet)))))

  (defthm aignet-add-in-aignet-litp
    (b* (((mv lit aignet) (aignet-add-in aignet)))
      (implies (equal lit lit2)
               (aignet-litp lit2 aignet)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-add-in-new-node
    (b* (((mv lit aignet2) (aignet-add-in aignet))
         (node (nth-node id (nth *nodesi* aignet2))))
      (implies (equal (id-fix id) (lit-id lit))
               (equal node
                      (mk-in-node (num-ins aignet))))))

  (defthm aignet-add-in-num-ins
    (equal (nth *num-ins* (mv-nth 1 (aignet-add-in aignet)))
           (+ 1 (nfix (num-ins aignet)))))

  (local (in-theory (disable aignet-add-in)))

  (definlined aignet-add-reg (aignet)
    (declare (xargs :stobjs aignet
                    :guard (aignet-well-formedp aignet)))
    (b* ((aignet (maybe-grow-nodes aignet))
         (aignet (maybe-grow-regs aignet))
         (id  (to-id (num-nodes aignet)))
         (lit (mk-lit id 0))
         (reg-num (lnfix (num-regs aignet)))
         (aignet (update-num-regs (+ 1 reg-num) aignet))
         (aignet (update-num-nodes (+ 1 (id-val id)) aignet))
         (aignet (set-regnum->id reg-num id aignet))
         (aignet (set-reg-node id reg-num aignet)))
      (mv lit aignet)))

  (def-aignet-frame aignet-add-reg)
  (def-aignet-preservation-thms aignet-add-reg)

  (local (in-theory (enable aignet-add-reg)))

  (defthm aignet-add-reg-new-lit
    (equal (mv-nth 0 (aignet-add-reg aignet))
           (mk-lit (to-id (num-nodes aignet)) 0)))

  (defthm aignet-add-reg-num-nodes
    (equal (nth *num-nodes* (mv-nth 1 (aignet-add-reg aignet)))
           (+ 1 (nfix (num-nodes aignet)))))

  (defthm aignet-add-reg-aignet-litp
    (b* (((mv lit aignet) (aignet-add-reg aignet)))
      (implies (equal lit lit2)
               (aignet-litp lit2 aignet)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-add-reg-new-node
    (b* (((mv lit aignet2) (aignet-add-reg aignet))
         (node (nth-node id (nth *nodesi* aignet2))))
      (implies (equal (id-fix id) (lit-id lit))
               (equal node
                      (mk-reg-node (num-regs aignet))))))

  (defthm aignet-add-reg-num-regs
    (equal (nth *num-regs* (mv-nth 1 (aignet-add-reg aignet)))
           (+ 1 (nfix (num-regs aignet)))))

  (local (in-theory (disable aignet-add-reg)))

  (definlined aignet-add-gate1 (f0 f1 aignet)
    (declare (type (integer 0 *) f0)
             (type (integer 0 *) f1)
             (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp f0 aignet)
                                (aignet-litp f1 aignet))
                    :guard-hints (("goal" :in-theory (enable aignet-litp)))))
    (b* ((aignet (maybe-grow-nodes aignet))
         (id  (to-id (num-nodes aignet)))
         (lit (mk-lit id 0))
         (aignet (update-num-gates (+ 1 (lnfix (num-gates aignet))) aignet))
         (aignet (update-num-nodes (+ 1 (id-val id)) aignet))
         (phase (b-and (lit->phase f0 aignet)
                             (lit->phase f1 aignet)))
         (aignet (set-gate-node id f0 f1 phase aignet)))
      (mv lit aignet)))

  (def-aignet-frame aignet-add-gate1)
  (def-aignet-preservation-thms aignet-add-gate1)

  (local (in-theory (enable aignet-add-gate1)))

  (defcong lit-equiv equal (aignet-add-gate1 lit1 lit2 aignet) 1)
  (defcong lit-equiv equal (aignet-add-gate1 lit1 lit2 aignet) 2)

  (defthm aignet-add-gate1-new-lit
    (equal (mv-nth 0 (aignet-add-gate1 f0 f1 aignet))
           (mk-lit (to-id (num-nodes aignet)) 0)))

  (defthm aignet-add-gate1-num-nodes
    (equal (nth *num-nodes* (mv-nth 1 (aignet-add-gate1 f0 f1 aignet)))
           (+ 1 (nfix (num-nodes aignet)))))

  (defthm aignet-add-gate1-aignet-litp
    (b* (((mv lit aignet) (aignet-add-gate1 f0 f1 aignet)))
      (implies (equal lit lit2)
               (aignet-litp lit2 aignet)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-add-gate1-new-node
    (b* (((mv lit aignet2) (aignet-add-gate1 f0 f1 aignet))
         (node (nth-node id (nth *nodesi* aignet2))))
      (implies (equal (id-fix id) (lit-id lit))
               (equal node
                      (mk-gate-node f0 f1
                                   (b-and (lit->phase f0 aignet)
                                                (lit->phase f1 aignet)))))))

  (defthm aignet-add-gate1-new-node-rw
    (b* (((mv & aignet2) (aignet-add-gate1 f0 f1 aignet))
         (node (nth-node (to-id (nth *num-nodes* aignet)) (nth *nodesi* aignet2))))
      (equal node
             (mk-gate-node f0 f1
                          (b-and (lit->phase f0 aignet)
                                       (lit->phase f1 aignet))))))

  (defthm aignet-add-gate1-num-gates
    (equal (nth *num-gates* (mv-nth 1 (aignet-add-gate1 f0 f1 aignet)))
           (+ 1 (nfix (num-gates aignet)))))

  (local (in-theory (disable aignet-add-gate1)))

  (definlined aignet-add-gate (f0 f1 aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp f0 aignet)
                                (aignet-litp f1 aignet))))
    (aignet-add-gate1 (aignet-lit-fix f0 aignet)
                   (aignet-lit-fix f1 aignet)
                   aignet))

  (def-aignet-frame aignet-add-gate)
  (def-aignet-preservation-thms aignet-add-gate)

  (local (in-theory (enable aignet-add-gate)))

  (defcong lit-equiv equal (aignet-add-gate lit1 lit2 aignet) 1)
  (defcong lit-equiv equal (aignet-add-gate lit1 lit2 aignet) 2)

  (defthm aignet-add-gate-new-lit
    (equal (mv-nth 0 (aignet-add-gate f0 f1 aignet))
           (mk-lit (to-id (num-nodes aignet)) 0)))

  (defthm aignet-add-gate-num-nodes
    (equal (nth *num-nodes* (mv-nth 1 (aignet-add-gate f0 f1 aignet)))
           (+ 1 (nfix (num-nodes aignet)))))

  (defthm aignet-add-gate-aignet-litp
    (b* (((mv lit aignet) (aignet-add-gate f0 f1 aignet)))
      (implies (equal lit lit2)
               (aignet-litp lit2 aignet)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-add-gate-new-node
    (b* (((mv lit aignet2) (aignet-add-gate f0 f1 aignet))
         (node (nth-node id (nth *nodesi* aignet2))))
      (implies (equal (id-fix id) (lit-id lit))
               (equal node
                      (let ((f0 (aignet-lit-fix f0 aignet))
                            (f1 (aignet-lit-fix f1 aignet)))
                        (mk-gate-node f0 f1
                                     (b-and (lit->phase f0 aignet)
                                                  (lit->phase f1 aignet))))))))

  (defthm aignet-add-gate-new-node-rw
    (b* (((mv & aignet2) (aignet-add-gate f0 f1 aignet))
         (node (nth-node (to-id (nth *num-nodes* aignet)) (nth *nodesi* aignet2))))
      (equal node
             (let ((f0 (aignet-lit-fix f0 aignet))
                   (f1 (aignet-lit-fix f1 aignet)))
               (mk-gate-node f0 f1
                            (b-and (lit->phase f0 aignet)
                                         (lit->phase f1 aignet)))))))

  (defthm aignet-add-gate-num-gates
    (equal (nth *num-gates* (mv-nth 1 (aignet-add-gate f0 f1 aignet)))
           (+ 1 (nfix (num-gates aignet)))))

  (local (in-theory (disable aignet-add-gate)))


  ;; These don't return a literal because they shouldn't be fanins.
  (definlined aignet-add-out1 (fanin-lit aignet)
    (declare (type (integer 0 *) fanin-lit)
             (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp fanin-lit aignet))))
    (b* ((aignet (maybe-grow-nodes aignet))
         (aignet (maybe-grow-outs aignet))
         (id  (to-id (num-nodes aignet)))
         (out-num (lnfix (num-outs aignet)))
         (aignet (update-num-outs (+ 1 out-num) aignet))
         (aignet (update-num-nodes (+ 1 (id-val id)) aignet))
         (phase (lit->phase fanin-lit aignet))
         (aignet (set-outnum->id out-num id aignet)))
      (set-out-node id fanin-lit out-num phase aignet)))

  (def-aignet-frame aignet-add-out1)
  (def-aignet-preservation-thms aignet-add-out1)

  (local (in-theory (enable aignet-add-out1)))

  (defcong lit-equiv equal (aignet-add-out1 lit aignet) 1)

  (defthm aignet-add-out1-aignet-idp
    (b* ((aignet2 (aignet-add-out1 f aignet)))
      (aignet-idp (to-id (nth *num-nodes* aignet)) aignet2))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-add-out1-new-node
    (b* ((aignet2 (aignet-add-out1 f aignet))
         (node (nth-node id (nth *nodesi* aignet2))))
      (implies (equal (id-val id) (nfix (num-nodes aignet)))
               (equal node
                      (mk-out-node f (num-outs aignet)
                                  (lit->phase f aignet))))))

  (defthm aignet-add-out1-num-nodes
    (equal (nth *num-nodes* (aignet-add-out1 f aignet))
           (+ 1 (nfix (num-nodes aignet)))))

  (defthm aignet-add-out1-num-outs
    (equal (nth *num-outs* (aignet-add-out1 f aignet))
           (+ 1 (nfix (num-outs aignet)))))

  (local (in-theory (disable aignet-add-out1)))

  (definlined aignet-add-out (fanin-lit aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp fanin-lit aignet))))
    (aignet-add-out1 (aignet-lit-fix fanin-lit aignet) aignet))

  (def-aignet-frame aignet-add-out)
  (def-aignet-preservation-thms aignet-add-out)

  (local (in-theory (enable aignet-add-out)))

  (defcong lit-equiv equal (aignet-add-out lit aignet) 1)

  (defthm aignet-add-out-aignet-idp
    (b* ((aignet2 (aignet-add-out f aignet)))
      (aignet-idp (to-id (nth *num-nodes* aignet)) aignet2))
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-add-out-new-node
    (b* ((aignet2 (aignet-add-out f aignet))
         (node (nth-node id (nth *nodesi* aignet2))))
      (implies (equal (id-val id) (nfix (num-nodes aignet)))
               (equal node
                      (let ((f (aignet-lit-fix f aignet)))
                        (mk-out-node f (num-outs aignet)
                                    (lit->phase f aignet)))))))

  (defthm aignet-add-out-num-nodes
    (equal (nth *num-nodes* (aignet-add-out f aignet))
           (+ 1 (nfix (num-nodes aignet)))))

  (defthm aignet-add-out-num-outs
    (equal (nth *num-outs* (aignet-add-out f aignet))
           (+ 1 (nfix (num-outs aignet)))))

  (local (in-theory (disable aignet-add-out)))


  (definlined aignet-add-regin1 (fanin-lit reg-id aignet)
    (declare (type (integer 0 *) fanin-lit)
             (type (integer 0 *) reg-id)
             (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp fanin-lit aignet)
                                (aignet-idp reg-id aignet)
                                (or (int= 0 (id-val reg-id))
                                    (aignet-unconnected-reg-p reg-id aignet)))
                    :guard-hints (("goal" :in-theory (enable aignet-unconnected-reg-p)))))
    (b* ((aignet (maybe-grow-nodes aignet))
         (id  (to-id (num-nodes aignet)))
         (aignet (update-num-regins (+ 1 (lnfix (num-regins aignet))) aignet))
         (aignet (update-num-nodes (+ 1 (id-val id)) aignet))
         (phase (lit->phase fanin-lit aignet))
         (aignet (set-regin-node id fanin-lit reg-id phase aignet))
         ((when (int= 0 (id-val reg-id)))
          aignet)
         (regnum (io-id->ionum reg-id aignet)))
      (set-regnum->id regnum id aignet)))

  (def-aignet-frame aignet-add-regin1)
  (def-aignet-preservation-thms aignet-add-regin1
    :omit (aignet-unconnected-reg-p-preserved))

  (local (in-theory (enable aignet-add-regin1)))

  (defcong lit-equiv equal (aignet-add-regin1 lit ro aignet) 1)
  (defcong id-equiv equal (aignet-add-regin1 lit ro aignet) 2)

  (defthm aignet-add-regin1-new-node
    (b* ((aignet2 (aignet-add-regin1 f ro aignet))
         (node (nth-node id (nth *nodesi* aignet2))))
      (implies (equal (id-val id) (nfix (num-nodes aignet)))
               (equal node
                      (mk-regin-node f ro (lit->phase f aignet))))))

  (defthm aignet-add-regin1-num-nodes
    (equal (nth *num-nodes* (aignet-add-regin1 f ro aignet))
           (+ 1 (nfix (num-nodes aignet)))))

  (defthm aignet-add-regin1-num-regins
    (equal (nth *num-regins* (aignet-add-regin1 f ro aignet))
           (+ 1 (nfix (num-regins aignet)))))

  (defthm aignet-add-regin1-other-regs-unconnected
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-reg-p reg aignet)
                  (aignet-idp reg aignet)
                  (aignet-idp ro aignet)
                  (or (aignet-unconnected-reg-p ro aignet)
                      (equal (id-val ro) 0))
                  (not (equal (id-val reg) (id-val ro))))
             (aignet-unconnected-reg-p reg (aignet-add-regin1 f ro aignet)))
    :hints(("Goal" :in-theory (enable aignet-unconnected-reg-p))
           (and stable-under-simplificationp
                '(:in-theory (disable aignet-well-formedp-reg-rw)
                  :use ((:instance aignet-well-formedp-reg-rw
                         (n reg))
                        (:instance aignet-well-formedp-reg-rw
                         (n ro)))))))

  (local (in-theory (disable aignet-add-regin1)))

  (definlined aignet-add-regin (fanin-lit reg-id aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp fanin-lit aignet)
                                (aignet-idp reg-id aignet)
                                (or (int= 0 (id-val reg-id))
                                    (aignet-unconnected-reg-p reg-id aignet)))))
    (aignet-add-regin1 (aignet-lit-fix fanin-lit aignet)
                    (aignet-unconnected-reg-fixup reg-id aignet)
                    aignet))

  (def-aignet-frame aignet-add-regin)
  (def-aignet-preservation-thms aignet-add-regin
    :omit (aignet-unconnected-reg-p-preserved))

  (local (in-theory (enable aignet-add-regin)))

  (defcong lit-equiv equal (aignet-add-regin lit ro aignet) 1)
  (defcong id-equiv equal (aignet-add-regin lit ro aignet) 2)

  (defthm aignet-add-regin-new-node
    (b* ((aignet2 (aignet-add-regin f ro aignet))
         (node (nth-node id (nth *nodesi* aignet2))))
      (implies (equal (id-val id) (nfix (num-nodes aignet)))
               (equal node
                      (let ((f (aignet-lit-fix f aignet))
                            (ro (aignet-unconnected-reg-fixup ro aignet)))
                        (mk-regin-node f ro (lit->phase f aignet)))))))

  (defthm aignet-add-regin-num-nodes
    (equal (nth *num-nodes* (aignet-add-regin f ro aignet))
           (+ 1 (nfix (num-nodes aignet)))))

  (defthm aignet-add-regin-num-regins
    (equal (nth *num-regins* (aignet-add-regin f ro aignet))
           (+ 1 (nfix (num-regins aignet)))))

  (defthm aignet-add-regin-other-regs-unconnected
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-reg-p reg aignet)
                  (aignet-idp reg aignet)
                  (not (equal (id-val reg)
                              (id-val (aignet-unconnected-reg-fixup ro aignet)))))
             (aignet-unconnected-reg-p reg (aignet-add-regin f ro aignet)))
    :hints (("goal" :use ((:instance
                           aignet-add-regin1-other-regs-unconnected
                           (f (aignet-lit-fix f aignet))
                           (ro (aignet-unconnected-reg-fixup ro aignet))))
             :in-theory (disable aignet-add-regin1-other-regs-unconnected)))))

(defthm fix-nfix
  (equal (fix (nfix x))
         (nfix x)))

(local
 (defsection aignet-node-ok-preserved
   (local (in-theory (disable acl2::nth-with-large-index
                              resize-list len
                              aignet-well-formedp-in-rw
                              aignet-well-formedp-gate-rw
                              aignet-well-formedp-reg-rw
                              aignet-well-formedp-reg-linear
                              aignet-well-formedp-combout-rw
                              aignet-well-formedp-regin-linear
                              aignet-well-formedp-out-linear
                              aignet-well-formedp-in-linear
                              aignet-well-formedp-sizes-ok-linear
                              aignet-well-formedp-regin-rw
                              aignet-well-formedp-const
                              aignet-well-formedp-gate-linear
                              acl2::nfix-when-not-natp
                              aignet-well-formedp-num-nodes-natp)))

   (local (in-theory (enable aignet-add-in
                             aignet-add-reg
                             aignet-add-gate1
                             aignet-add-out1
                             aignet-add-regin1)))

   (defthm aignet-node-ok-of-add-new-node2
     (implies (and (aignet-idp n aignet)
                   (equal (id-val nodenum) (nfix (nth *num-nodes* aignet))))
              (equal (aignet-node-ok n (update-nth *nodesi*
                                               (update-nth-node
                                                nodenum
                                                new-node
                                                nodes)
                                               aignet))
                     (aignet-node-ok n (update-nth *nodesi* nodes aignet))))
     :hints(("Goal"
             :expand ((:free (aignet) (aignet-node-ok n aignet)))
             :in-theory (e/d (aignet-idp aignet-litp)
                             (aignet-well-formedp-num-nodes-natp)))
            (and stable-under-simplificationp
                 '(:expand ((:free (aignet) (aignet-in-ok n aignet))
                            (:free (aignet) (aignet-reg-ok n aignet))
                            (:free (aignet) (aignet-gate-ok n aignet))
                            (:free (aignet) (aignet-out-ok n aignet))
                            (:free (aignet) (aignet-regin-ok n aignet)))))))

   (defthm aignet-node-ok-of-add-new-node
     (implies (and (aignet-idp n aignet)
                   (equal (id-val nodenum) (nfix (nth *num-nodes* aignet)))
                   (equal nodes (nth *nodesi* aignet)))
              (equal (aignet-node-ok n (update-nth *nodesi*
                                               (update-nth-node
                                                nodenum
                                                new-node
                                                nodes)
                                               aignet))
                     (aignet-node-ok n aignet))))

   (defthm aignet-node-ok-of-add-new-in
     (implies (and (equal (nfix innum) (nfix (nth *num-ins* aignet)))
                   (equal ins (nth *insi* aignet)))
              (equal (aignet-node-ok n (update-nth *insi*
                                               (update-nth-id
                                                innum
                                                new-in ins)
                                               aignet))
                     (aignet-node-ok n aignet)))
     :hints(("Goal"
             :in-theory (e/d* (aignet-frame-thms)
                              (aignet-node-ok-implies
                               (:type-prescription aignet-well-formedp)))
             :expand ((:free (aignet) (aignet-node-ok n aignet))))
            (and stable-under-simplificationp
                 '(:expand ((:free (aignet) (aignet-in-ok n aignet))
                            (:free (aignet) (aignet-reg-ok n aignet))
                            (:free (aignet) (aignet-gate-ok n aignet))
                            (:free (aignet) (aignet-out-ok n aignet))
                            (:free (aignet) (aignet-regin-ok n aignet)))))))

   (defthm aignet-node-ok-of-add-new-out
     (implies (and (equal (nfix outnum) (nfix (nth *num-outs* aignet)))
                   (equal outs (nth *outsi* aignet)))
              (equal (aignet-node-ok n (update-nth *outsi*
                                               (update-nth-id
                                                outnum
                                                new-out
                                                outs)
                                               aignet))
                     (aignet-node-ok n aignet)))
     :hints(("Goal"
             :in-theory (e/d* (aignet-frame-thms)
                              (aignet-node-ok-implies
                               (:type-prescription aignet-well-formedp)))
             :expand ((:free (aignet) (aignet-node-ok n aignet))))
            (and stable-under-simplificationp
                 '(:expand ((:free (aignet) (aignet-in-ok n aignet))
                            (:free (aignet) (aignet-reg-ok n aignet))
                            (:free (aignet) (aignet-gate-ok n aignet))
                            (:free (aignet) (aignet-out-ok n aignet))
                            (:free (aignet) (aignet-regin-ok n aignet)))))))

   (defthm aignet-node-ok-of-add-new-reg
     (implies (and (equal (nfix regnum) (nfix (nth *num-regs* aignet)))
                   (equal regs (nth *regsi* aignet)))
              (equal (aignet-node-ok n (update-nth *regsi*
                                               (update-nth-id
                                                regnum
                                                new-reg
                                                regs)
                                               aignet))
                     (aignet-node-ok n aignet)))
     :hints(("Goal"
             :in-theory (e/d* (aignet-frame-thms)
                              (aignet-node-ok-implies
                               (:type-prescription aignet-well-formedp)))
             :expand ((:free (aignet) (aignet-node-ok n aignet))))
            (and stable-under-simplificationp
                 '(:expand ((:free (aignet) (aignet-in-ok n aignet))
                            (:free (aignet) (aignet-reg-ok n aignet))
                            (:free (aignet) (aignet-gate-ok n aignet))
                            (:free (aignet) (aignet-out-ok n aignet))
                            (:free (aignet) (aignet-regin-ok n aignet)))))))

   (local (in-theory (e/d* (aignet-node-ok
                            aignet-in-ok
                            aignet-reg-ok
                            aignet-gate-ok
                            aignet-out-ok
                            aignet-regin-ok
                            aignet-frame-thms)
                           (aignet-node-ok-implies
                            (:type-prescription
                             aignet-well-formedp)))))

   (defthm aignet-node-ok-of-increase-num-regs
     (implies (and (<= (nfix (num-regs aignet)) (nfix nregs))
                   (aignet-node-ok n aignet))
              (aignet-node-ok n (update-nth *num-regs* nregs aignet))))

   (defthm aignet-node-ok-of-increase-num-ins
     (implies (and (<= (nfix (num-ins aignet)) (nfix nins))
                   (aignet-node-ok n aignet))
              (aignet-node-ok n (update-nth *num-ins* nins aignet))))

   (defthm aignet-node-ok-of-increase-num-outs
     (implies (and (<= (nfix (num-outs aignet)) (nfix nouts))
                   (aignet-node-ok n aignet))
              (aignet-node-ok n (update-nth *num-outs* nouts aignet))))

   (defthm aignet-node-ok-of-increase-num-regins
     (implies (and (<= (nfix (num-regins aignet)) (nfix nregins))
                   (aignet-node-ok n aignet))
              (aignet-node-ok n (update-nth *num-regins* nregins aignet))))

   (defthm aignet-node-ok-of-increase-num-nodes
     (implies (and (<= (nfix (num-nodes aignet)) (nfix nnodes))
                   (aignet-node-ok n aignet))
              (aignet-node-ok n (update-nth *num-nodes* nnodes aignet)))
     :hints(("Goal" :in-theory (enable aignet-idp aignet-litp))))

   (defthm aignet-node-ok-of-maybe-grow-ins
     (equal (aignet-node-ok n (maybe-grow-ins aignet))
            (aignet-node-ok n aignet))
     :hints(("Goal" :in-theory (enable* aignet-frame-thms aignet-idp aignet-litp))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::nth-with-large-index)))))

   (defthm aignet-node-ok-of-maybe-grow-regs
     (equal (aignet-node-ok n (maybe-grow-regs aignet))
            (aignet-node-ok n aignet))
     :hints(("Goal" :in-theory (enable* aignet-frame-thms aignet-idp aignet-litp))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::nth-with-large-index)))))

   (defthm aignet-node-ok-of-maybe-grow-outs
     (equal (aignet-node-ok n (maybe-grow-outs aignet))
            (aignet-node-ok n aignet))
     :hints(("Goal" :in-theory (enable* aignet-frame-thms aignet-idp aignet-litp))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::nth-with-large-index)))))

   (defthm aignet-node-ok-of-maybe-grow-nodes
     (equal (aignet-node-ok n (maybe-grow-nodes aignet))
            (aignet-node-ok n aignet))
     :hints(("Goal" :in-theory (enable* aignet-frame-thms aignet-idp aignet-litp))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::nth-with-large-index)))))

   ;; (defthm aignet-node-ok-of-update-fanin0
   ;;   (implies (and (aignet-node-ok n (update-nth *nodesi* nodes aignet))
   ;;                 (equal (id->type m aignet) (in-type))
   ;;                 (equal (io-id->regp m aignet) 1)
   ;;                 (< (nfix newf0) (nfix (num-nodes aignet)))
   ;;                 (< (nfix m) (nfix newf0))
   ;;                 (equal (id->type newf0 aignet) (out-type))
   ;;                 (equal (io-id->regp newf0 aignet) 1)
   ;;                 (equal (id-fanin1 newf0 aignet) (nfix m))
   ;;                 (equal (id-fanin0 m aignet) 0)
   ;;                 (equal nodes (nth *nodesi* aignet))
   ;;                 (equal node (nth-node m nodes)))
   ;;            (aignet-node-ok n (update-nth
   ;;                       co    *nodesi*
   ;;                           (update-nth-node
   ;;                            m (update-node-fanin0 newf0 node)
   ;;                            nodes)
   ;;                           aignet)))
   ;;   :hints(("Goal" :in-theory (enable aignet-node-ok
   ;;                                     nth-node-of-update-nth-node-split))))



   (local (in-theory (disable aignet-reg-ok aignet-out-ok aignet-gate-ok aignet-regin-ok aignet-in-ok)))

   (local (in-theory (enable* aignet-frame-thms)))

   (defthm aignet-node-ok-of-add-in-prev
     (implies (and (aignet-node-ok n aignet)
                   (aignet-idp n aignet))
              (aignet-node-ok n (mv-nth 1 (aignet-add-in aignet))))
     :hints (("goal" :do-not-induct t))
     :otf-flg t)

   (defthm aignet-node-ok-of-add-in-new
     (implies (and (< 0 (nfix (num-nodes aignet)))
                   (equal (id-val n) (nth *num-nodes* aignet)))
              (aignet-node-ok n (mv-nth 1 (aignet-add-in aignet))))
     :hints (("goal" :do-not-induct t
              :in-theory (enable aignet-in-ok)))
     :otf-flg t)

   (defthm aignet-nodes-ok-of-add-in
     (implies (and (aignet-nodes-ok n aignet)
                   (< 0 (nfix (num-nodes aignet))))
              (aignet-nodes-ok n (mv-nth 1 (aignet-add-in aignet))))
     :hints(("Goal" :induct t :in-theory (e/d (aignet-idp)
                                              (aignet-node-ok aignet-add-in)))
            '(:cases ((aignet-idp (to-id n) aignet)))))

   (defthm aignet-node-ok-of-add-reg-prev
     (implies (and (aignet-node-ok n aignet)
                   (aignet-idp n aignet))
              (aignet-node-ok n (mv-nth 1 (aignet-add-reg aignet))))
     :hints (("goal" :do-not-induct t))
     :otf-flg t)

   (defthm aignet-node-ok-of-add-reg-new
     (implies (and (< 0 (nfix (num-nodes aignet)))
                   (equal (id-val n) (nth *num-nodes* aignet)))
              (aignet-node-ok n (mv-nth 1 (aignet-add-reg aignet))))
     :hints (("goal" :do-not-induct t
              :in-theory (enable aignet-reg-ok))
             (and stable-under-simplificationp
                  '(:in-theory (enable aignet-idp))))
     :otf-flg t)

   (defthm aignet-nodes-ok-of-add-reg
     (implies (and (aignet-nodes-ok n aignet)
                   (< 0 (nfix (num-nodes aignet))))
              (aignet-nodes-ok n (mv-nth 1 (aignet-add-reg aignet))))
     :hints(("Goal" :induct t :in-theory (e/d (aignet-idp)
                                              (aignet-node-ok aignet-add-reg)))
            '(:cases ((aignet-idp (to-id n) aignet)))))

   (defthm aignet-node-ok-of-add-gate-prev
     (implies (and (aignet-node-ok n aignet)
                   (aignet-idp n aignet))
              (aignet-node-ok n (mv-nth 1 (aignet-add-gate1 f0 f1 aignet))))
     :hints (("goal" :do-not-induct t))
     :otf-flg t)

   (defthm aignet-node-ok-of-add-gate-new
     (implies (and (< 0 (nfix (num-nodes aignet)))
                   (equal (id-val n) (nth *num-nodes* aignet))
                   (aignet-litp f0 aignet)
                   (aignet-litp f1 aignet))
              (aignet-node-ok n (mv-nth 1 (aignet-add-gate1 f0 f1 aignet))))
     :hints (("goal" :do-not-induct t
              :in-theory (enable aignet-gate-ok aignet-litp aignet-idp)))
     :otf-flg t)

   (defthm aignet-nodes-ok-of-add-gate
     (implies (and (aignet-nodes-ok n aignet)
                   (< 0 (nfix (num-nodes aignet)))
                   (aignet-litp f0 aignet)
                   (aignet-litp f1 aignet))
              (aignet-nodes-ok n (mv-nth 1 (aignet-add-gate1 f0 f1 aignet))))
     :hints(("Goal" :induct t :in-theory (e/d (aignet-idp)
                                              (aignet-node-ok aignet-add-gate1)))
            '(:cases ((aignet-idp (to-id n) aignet)))))

   (defthm aignet-node-ok-of-add-out-prev
     (implies (and (aignet-node-ok n aignet)
                   (aignet-idp n aignet))
              (aignet-node-ok n (aignet-add-out1 f aignet)))
     :hints (("goal" :do-not-induct t))
     :otf-flg t)

   (defthm aignet-node-ok-of-add-out-new
     (implies (and (< 0 (nfix (num-nodes aignet)))
                   (equal (id-val n) (nth *num-nodes* aignet))
                   (aignet-litp f aignet))
              (aignet-node-ok n (aignet-add-out1 f aignet)))
     :hints (("goal" :do-not-induct t
              :in-theory (enable aignet-out-ok aignet-idp aignet-litp)))
     :otf-flg t)

   (defthm aignet-nodes-ok-of-add-out
     (implies (and (aignet-nodes-ok n aignet)
                   (< 0 (nfix (num-nodes aignet)))
                   (aignet-litp f aignet))
              (aignet-nodes-ok n (aignet-add-out1 f aignet)))
     :hints(("Goal" :induct t :in-theory (e/d (aignet-idp)
                                              (aignet-node-ok aignet-add-out1)))
            '(:cases ((aignet-idp (to-id n) aignet)))))

   (local (in-theory (disable aignet-well-formedp-num-regs-natp
                              aignet-add-regin1-new-node
                              aignet-idp-of-to-id)))

   (defthm aignet-node-ok-of-add-regin-prev
     (implies (and (aignet-node-ok n aignet)
                   (aignet-idp n aignet)
                   (aignet-idp reg-id aignet)
                   (or (equal (id-val reg-id) 0)
                       (and (equal (id->type reg-id aignet) (in-type))
                            (equal (io-id->regp reg-id aignet) 1)
                            (equal (id-val (regnum->id (io-id->ionum reg-id aignet) aignet))
                                   (id-val reg-id)))))
              (aignet-node-ok n (aignet-add-regin1 f0 reg-id aignet)))
     :hints (("goal"
              :in-theory (e/d ()
                              (aignet-add-regin1)))
             ;; (and stable-under-simplificationp
             ;;      '(:in-theory (e/d (aignet-idp aignet-litp) (aignet-add-regin1))))
             (and stable-under-simplificationp
                  '(:expand ((:free (aignet) (aignet-node-ok n aignet))
                             (:free (aignet) (aignet-in-ok n aignet))
                             (:free (aignet) (aignet-reg-ok n aignet))
                             (:free (aignet) (aignet-gate-ok n aignet))
                             (:free (aignet) (aignet-out-ok n aignet))
                             (:free (aignet) (aignet-regin-ok n aignet)))
                    :do-not-induct t))
             (and stable-under-simplificationp
                  '(:in-theory (enable aignet-add-regin1 aignet-idp aignet-litp))))
     :otf-flg t)

   (local (in-theory (enable aignet-well-formedp-num-regs-natp
                             aignet-add-regin1-new-node
                             aignet-idp-of-to-id)))


   (defthm aignet-node-ok-of-add-regin-new
     (implies (and (< 0 (nfix (num-nodes aignet)))
                   (equal (id-val n) (num-nodes aignet))
                   (aignet-litp f0 aignet)
                   (aignet-idp reg-id aignet)
                   (or (equal (id-val reg-id) 0)
                       (and (equal (id->type reg-id aignet) (in-type))
                            (equal (io-id->regp reg-id aignet) 1)
                            (< (io-id->ionum reg-id aignet) (nfix (num-regs aignet)))
                            (equal (id-val (regnum->id (io-id->ionum reg-id aignet) aignet))
                                   (id-val reg-id)))))
              (aignet-node-ok n (aignet-add-regin1 f0 reg-id aignet)))
     :hints (("goal"
              :in-theory (e/d (aignet-regin-ok aignet-idp aignet-litp
                                            nth-node-of-update-nth-node-split))
              :do-not-induct t))
     :otf-flg t)

   (defthm aignet-nodes-ok-of-add-regin
     (implies (and (aignet-nodes-ok n aignet)
                   (< 0 (nfix (num-nodes aignet)))
                   (aignet-litp f0 aignet)
                   (aignet-idp reg-id aignet)
                   (or (equal (id-val reg-id) 0)
                       (and (equal (id->type reg-id aignet) (in-type))
                            (equal (io-id->regp reg-id aignet) 1)
                            (< (io-id->ionum reg-id aignet) (nfix (num-regs aignet)))
                            (equal (id-val (regnum->id (io-id->ionum reg-id aignet) aignet))
                                   (id-val reg-id)))))
              (aignet-nodes-ok n (aignet-add-regin1 f0 reg-id aignet)))
     :hints(("Goal" :induct t :in-theory (e/d (aignet-idp)
                                              (aignet-node-ok aignet-add-regin1)))
            '(:cases ((aignet-idp (to-id n) aignet)))))))

(defsection well-formedness-of-add-nodes
  (local (in-theory (e/d* (aignet-frame-thms)
                          (aignet-well-formedp-num-nodes-natp
                           aignet-well-formedp-num-regs-natp
                           aignet-well-formedp-num-ins-natp
                           aignet-well-formedp-num-outs-natp
                           acl2::nfix-when-not-natp
                           acl2::natp-when-gte-0
                           acl2::zp-when-gt-0
                           acl2::natp-when-integerp))))
  ;; (defthm aignet-regs-ok-of-update-irrelevant
  ;;   (implies (and (aignet-regs-ok n aignet)
  ;;                 (not (member (nfix k)
  ;;                              (list *num-regs*
  ;;                                    *regsi*
  ;;                                    *num-nodes*
  ;;                                    *nodesi*))))
  ;;            (aignet-regs-ok n (update-nth k val aignet)))
  ;;   :hints(("Goal" :in-theory (enable aignet-regnum-ok))))

  (local (in-theory (disable acl2::nth-with-large-index)))

  (local (in-theory (enable aignet-add-in
                            aignet-add-reg
                            aignet-add-gate1
                            aignet-add-out1
                            aignet-add-regin1)))

  (local (in-theory (enable nth-node-of-update-nth-node-split)))
  (local (in-theory (disable acl2::nfix-equal-to-nonzero)))

  (local
   (progn
     (defthm aignet-regs-ok-of-add-in
       (implies (aignet-regs-ok n aignet)
                (aignet-regs-ok n (mv-nth 1 (aignet-add-in aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-regnum-ok aignet-idp)
                                      ((:definition aignet-regs-ok)))
               :induct (aignet-regs-ok n aignet)
               :expand ((:free (aignet) (aignet-regs-ok n aignet))))))

     (defthm aignet-regs-ok-of-add-reg
       (implies (aignet-regs-ok n aignet)
                (aignet-regs-ok n (mv-nth 1 (aignet-add-reg aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-regnum-ok aignet-idp)
                                      ((:definition aignet-regs-ok)))
               :induct (aignet-regs-ok n aignet)
               :expand ((:free (aignet) (aignet-regs-ok n aignet))))
              (and stable-under-simplificationp
                   '(:expand ((:free (aignet) (aignet-regs-ok (+ 1 (nfix n)) aignet)))))))

     (defthm aignet-regs-ok-of-add-gate
       (implies (aignet-regs-ok n aignet)
                (aignet-regs-ok n (mv-nth 1 (aignet-add-gate1 f0 f1 aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-regnum-ok aignet-idp)
                                      ((:definition aignet-regs-ok)))
               :induct (aignet-regs-ok n aignet)
               :expand ((:free (aignet) (aignet-regs-ok n aignet))))))

     (defthm aignet-regs-ok-of-add-out
       (implies (aignet-regs-ok n aignet)
                (aignet-regs-ok n (aignet-add-out1 f0 aignet)))
       :hints(("Goal" :in-theory (e/d (aignet-regnum-ok aignet-idp)
                                      ((:definition aignet-regs-ok)))
               :induct (aignet-regs-ok n aignet)
               :expand ((:free (aignet) (aignet-regs-ok n aignet))))))

     (defthm aignet-regs-ok-of-add-regin
       (implies (and (aignet-regs-ok n aignet)
                     (aignet-idp reg-id aignet)
                     (or (equal (id-val reg-id) 0)
                         (and (equal (id->type reg-id aignet) (in-type))
                              (equal (io-id->regp reg-id aignet) 1)
                              (< (io-id->ionum reg-id aignet) (nfix (num-regs aignet)))
                              (equal (id-val (regnum->id (io-id->ionum reg-id aignet) aignet))
                                     (id-val reg-id)))))
                (aignet-regs-ok n (aignet-add-regin1 f0 reg-id aignet)))
       :hints(("Goal" :in-theory (e/d (nth-node-of-update-nth-node-split
                                       aignet-regnum-ok aignet-idp)
                                      ((:definition aignet-regs-ok)))
               :induct (aignet-regs-ok n aignet)
               :expand ((:free (aignet) (aignet-regs-ok n aignet))))))

     (defthm aignet-ins-ok-of-add-in
       (implies (aignet-ins-ok n aignet)
                (aignet-ins-ok n (mv-nth 1 (aignet-add-in aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-innum-ok aignet-idp)
                                      ((:definition aignet-ins-ok)))
               :induct (aignet-ins-ok n aignet)
               :expand ((:free (aignet) (aignet-ins-ok n aignet))))
              (and stable-under-simplificationp
                   '(:expand ((:free (aignet) (aignet-ins-ok (+ 1 (nfix n)) aignet)))))))

     (defthm aignet-ins-ok-of-add-reg
       (implies (aignet-ins-ok n aignet)
                (aignet-ins-ok n (mv-nth 1 (aignet-add-reg aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-innum-ok aignet-idp)
                                      ((:definition aignet-ins-ok)))
               :induct (aignet-ins-ok n aignet)
               :expand ((:free (aignet) (aignet-ins-ok n aignet))))))

     (defthm aignet-ins-ok-of-add-gate
       (implies (aignet-ins-ok n aignet)
                (aignet-ins-ok n (mv-nth 1 (aignet-add-gate1 f0 f1 aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-innum-ok aignet-idp)
                                      ((:definition aignet-ins-ok)))
               :induct (aignet-ins-ok n aignet)
               :expand ((:free (aignet) (aignet-ins-ok n aignet))))))

     (defthm aignet-ins-ok-of-add-out
       (implies (aignet-ins-ok n aignet)
                (aignet-ins-ok n (aignet-add-out1 f0 aignet)))
       :hints(("Goal" :in-theory (e/d (aignet-innum-ok aignet-idp)
                                      ((:definition aignet-ins-ok)))
               :induct (aignet-ins-ok n aignet)
               :expand ((:free (aignet) (aignet-ins-ok n aignet))))))

     (defthm aignet-ins-ok-of-add-regin
       (implies (aignet-ins-ok n aignet)
                (aignet-ins-ok n (aignet-add-regin1 f0 regnum aignet)))
       :hints(("Goal" :in-theory (e/d (aignet-innum-ok aignet-idp)
                                      ((:definition aignet-ins-ok)))
               :induct (aignet-ins-ok n aignet)
               :expand ((:free (aignet) (aignet-ins-ok n aignet))))))

     (defthm aignet-outs-ok-of-add-in
       (implies (aignet-outs-ok n aignet)
                (aignet-outs-ok n (mv-nth 1 (aignet-add-in aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-outnum-ok aignet-idp)
                                      ((:definition aignet-outs-ok)))
               :induct (aignet-outs-ok n aignet)
               :expand ((:free (aignet) (aignet-outs-ok n aignet))))))

     (defthm aignet-outs-ok-of-add-reg
       (implies (aignet-outs-ok n aignet)
                (aignet-outs-ok n (mv-nth 1 (aignet-add-reg aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-outnum-ok aignet-idp)
                                      ((:definition aignet-outs-ok)))
               :induct (aignet-outs-ok n aignet)
               :expand ((:free (aignet) (aignet-outs-ok n aignet))))))

     (defthm aignet-outs-ok-of-add-gate
       (implies (aignet-outs-ok n aignet)
                (aignet-outs-ok n (mv-nth 1 (aignet-add-gate1 f0 f1 aignet))))
       :hints(("Goal" :in-theory (e/d (aignet-outnum-ok aignet-idp)
                                      ((:definition aignet-outs-ok)))
               :induct (aignet-outs-ok n aignet)
               :expand ((:free (aignet) (aignet-outs-ok n aignet))))))

     (defthm aignet-outs-ok-of-add-out
       (implies (aignet-outs-ok n aignet)
                (aignet-outs-ok n (aignet-add-out1 f0 aignet)))
       :hints(("Goal" :in-theory (e/d (aignet-outnum-ok aignet-idp)
                                      ((:definition aignet-outs-ok)))
               :induct (aignet-outs-ok n aignet)
               :expand ((:free (aignet) (aignet-outs-ok n aignet))))
              (and stable-under-simplificationp
                   '(:expand ((:free (aignet) (aignet-outs-ok (+ 1 (nfix n)) aignet)))))))

     (defthm aignet-outs-ok-of-add-regin
       (implies (aignet-outs-ok n aignet)
                (aignet-outs-ok n (aignet-add-regin1 f0 regnum aignet)))
       :hints(("Goal" :in-theory (e/d (aignet-outnum-ok aignet-idp)
                                      ((:definition aignet-outs-ok)))
               :induct (aignet-outs-ok n aignet)
               :expand ((:free (aignet) (aignet-outs-ok n aignet))))))

     (defthm aignet-sizes-ok-of-add-in
       (implies (aignet-sizes-ok aignet)
                (aignet-sizes-ok (mv-nth 1 (aignet-add-in aignet))))
       :hints(("Goal" :in-theory (enable aignet-sizes-ok))))

     (defthm aignet-sizes-ok-of-add-reg
       (implies (aignet-sizes-ok aignet)
                (aignet-sizes-ok (mv-nth 1 (aignet-add-reg aignet))))
       :hints(("Goal" :in-theory (enable aignet-sizes-ok))))

     (defthm aignet-sizes-ok-of-add-gate
       (implies (aignet-sizes-ok aignet)
                (aignet-sizes-ok (mv-nth 1 (aignet-add-gate1 f0 f1 aignet))))
       :hints(("Goal" :in-theory (enable aignet-sizes-ok))))

     (defthm aignet-sizes-ok-of-add-out
       (implies (aignet-sizes-ok aignet)
                (aignet-sizes-ok (aignet-add-out1 f0 aignet)))
       :hints(("Goal" :in-theory (enable aignet-sizes-ok))))

     (defthm aignet-sizes-ok-of-add-regin
       (implies (aignet-sizes-ok aignet)
                (aignet-sizes-ok (aignet-add-regin1 f0 regnum aignet)))
       :hints(("Goal" :in-theory (enable aignet-sizes-ok
                                         nth-node-of-update-nth-node-split))))))


   (defthm aignet-well-formedp-of-add-in
     (implies (aignet-well-formedp aignet)
              (aignet-well-formedp (mv-nth 1 (aignet-add-in aignet))))
     :hints(("Goal" :in-theory (e/d (aignet-well-formedp)
                                    (aignet-add-in
                                     aignet-outs-ok
                                     aignet-regs-ok
                                     aignet-ins-ok
                                     aignet-nodes-ok
                                     aignet-sizes-ok)))))

   (defthm aignet-well-formedp-of-add-reg
     (implies (aignet-well-formedp aignet)
              (aignet-well-formedp (mv-nth 1 (aignet-add-reg aignet))))
     :hints(("Goal" :in-theory (e/d (aignet-well-formedp)
                                    (aignet-add-reg
                                     aignet-outs-ok
                                     aignet-regs-ok
                                     aignet-ins-ok
                                     aignet-nodes-ok
                                     aignet-sizes-ok)))))

   (local (defthm aignet-well-formedp-of-add-gate1
            (implies (and (aignet-well-formedp aignet)
                          (aignet-litp f0 aignet)
                          (aignet-litp f1 aignet))
                     (aignet-well-formedp (mv-nth 1 (aignet-add-gate1 f0 f1 aignet))))
            :hints(("Goal" :in-theory (e/d (aignet-well-formedp)
                                           (aignet-add-gate1
                                            aignet-outs-ok
                                            aignet-regs-ok
                                            aignet-ins-ok
                                            aignet-nodes-ok
                                            aignet-sizes-ok))))))

   (defthm aignet-well-formedp-of-add-gate
     (implies (aignet-well-formedp aignet)
              (aignet-well-formedp (mv-nth 1 (aignet-add-gate f0 f1 aignet))))
     :hints(("Goal" :in-theory (e/d (aignet-add-gate)
                                    (aignet-add-gate1)))))

   (local (defthm aignet-well-formedp-of-add-out1
            (implies (and (aignet-well-formedp aignet)
                          (aignet-litp f0 aignet))
                     (aignet-well-formedp (aignet-add-out1 f0 aignet)))
            :hints(("Goal" :in-theory (e/d (aignet-well-formedp)
                                           (aignet-add-out1
                                            aignet-outs-ok
                                            aignet-regs-ok
                                            aignet-ins-ok
                                            aignet-nodes-ok
                                            aignet-sizes-ok))))))

   (defthm aignet-well-formedp-of-add-out
     (implies (aignet-well-formedp aignet)
              (aignet-well-formedp (aignet-add-out f0 aignet)))
     :hints(("Goal" :in-theory (e/d (aignet-add-out)
                                    (aignet-add-out1)))))

   (local (defthm aignet-well-formedp-of-add-regin1
            (implies (and (aignet-well-formedp aignet)
                          (aignet-litp f0 aignet)
                          (aignet-idp reg-id aignet)
                          (or (equal (id-val reg-id) 0)
                              (aignet-unconnected-reg-p reg-id aignet)))
                     (aignet-well-formedp (aignet-add-regin1 f0 reg-id aignet)))
            :hints(("Goal" :in-theory (e/d (aignet-well-formedp
                                            aignet-regnum-ok-implies
                                            aignet-unconnected-reg-p)
                                           (aignet-add-regin1
                                            aignet-outs-ok
                                            aignet-regs-ok
                                            aignet-ins-ok
                                            aignet-nodes-ok
                                            aignet-sizes-ok))))))

   (defthm aignet-well-formedp-of-add-regin
     (implies (aignet-well-formedp aignet)
              (aignet-well-formedp (aignet-add-regin f0 reg-id aignet)))
     :hints(("Goal" :in-theory (e/d (aignet-add-regin)
                                    (aignet-add-regin1)))))

   (add-aignet-preservation-thm
    aignet-well-formedp
    :body `(implies (aignet-well-formedp ,orig-stobj)
                    (aignet-well-formedp ,new-stobj))
    :hints expand/induct-hints))

(defsection aignet-init

  (local (in-theory (disable acl2::nth-with-large-index
                             aignet-nodes-ok)))

  (local (in-theory (enable aignet-idp)))

  ;; Clears the aignet without resizing, unless the node array is size 0.
  (defund aignet-clear (aignet)
    (declare (xargs :stobjs aignet
                    :guard-debug t))
    (b* ((aignet (update-num-ins 0 aignet))
         (aignet (update-num-regs 0 aignet))
         (aignet (update-num-gates 0 aignet))
         (aignet (update-num-regins 0 aignet))
         (aignet (update-num-outs 0 aignet))
         (aignet (update-num-nodes 1 aignet))
         (aignet (if (< 1 (nodes-length aignet))
                  aignet
                ;; arbitrary
                (resize-nodes 10 aignet)))
         ;; set up the constant node
         (aignet (set-const-node 0 aignet)))
      aignet))

  (defthm aignet-well-formedp-of-aignet-clear
    (aignet-well-formedp (aignet-clear aignet))
    :hints(("Goal" :in-theory (enable aignet-node-ok
                                      aignet-ins-ok
                                      aignet-outs-ok
                                      aignet-regs-ok
                                      aignet-sizes-ok)
            :expand ((aignet-well-formedp (aignet-clear aignet))))
           '(:expand ((aignet-clear aignet)
                      (:free (aignet) (aignet-nodes-ok 0 aignet))
                      (:free (aignet) (aignet-nodes-ok 1 aignet))))))

  (defun aignet-init (max-outs max-regs max-ins max-nodes aignet)
    (declare (type (integer 0 *) max-outs max-regs max-ins)
             (type (integer 1 *) max-nodes)
             (xargs :stobjs aignet))
    (b* ((max-nodes (mbe :logic (if (< 0 (nfix max-nodes))
                                   max-nodes
                                 1)
                        :exec max-nodes))
         (aignet (resize-nodes (* 2 max-nodes) aignet))
         (aignet (resize-ins (lnfix max-ins) aignet))
         (aignet (resize-outs (lnfix max-outs) aignet))
         (aignet (resize-regs (lnfix max-regs) aignet)))
      (aignet-clear aignet)))

  ;; Note: We could first resize each array to 0, then to the appropriate
  ;; size.  This might be nice logically because it throws out all the data and
  ;; returns everything to default values; the aignet input is then logically
  ;; irrelevant to the result.  But it shouldn't matter because we set the
  ;; gate/reg/out numbers to 0; the array contents should thus be irrelevant.
  (defthm aignet-well-formedp-of-aignet-init
    (aignet-well-formedp (aignet-init nouts nregs nins nnodes aignet))
    :hints(("Goal" :in-theory (e/d ()
                                   (aignet-clear)))))

  (local (in-theory (enable aignet-clear)))

  (defthm zero-counts-of-aignet-clear
    (implies (<= (nfix n) *num-regins*)
             (equal (nth n (aignet-clear aignet)) 0)))

  (defthm zero-counts-of-aignet-init
    (implies (<= (nfix n) *num-regins*)
             (equal (nth n (aignet-init max-outs max-regs max-ins max-nodes aignet)) 0))
    :hints(("Goal" :in-theory (disable aignet-clear))))

  (defthm num-nodes-of-aignet-clear
    (equal (nth *num-nodes* (aignet-clear aignet)) 1))

  (defthm aignet-idp-of-aignet-clear
    (implies (idp n)
             (equal (aignet-idp n (aignet-clear aignet))
                    (equal (id-val n) 0))))

  (defthm aignet-litp-of-aignet-clear
    (implies (litp n)
             (equal (aignet-litp n (aignet-clear aignet))
                    (equal (id-val (lit-id n)) 0)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm num-nodes-of-aignet-init
    (equal (nth *num-nodes* (aignet-init max-outs max-regs max-ins max-nodes aignet))
           1))

  (defthm aignet-idp-of-aignet-init
    (implies (idp n)
             (equal (aignet-idp n (aignet-init max-outs max-regs max-ins max-nodes aignet))
                    (equal (id-val n) 0))))

  (defthm aignet-litp-of-aignet-init
    (implies (litp n)
             (equal (aignet-litp n (aignet-init max-outs max-regs max-ins max-nodes aignet))
                    (equal (id-val (lit-id n)) 0)))
    :hints(("Goal" :in-theory (enable aignet-litp))))


  (in-theory (disable aignet-clear aignet-init)))

(defsection bitarr
  (local (in-theory (enable acl2::aignetp)))
  ;; bug workaround
  ;; (in-theory (disable (acl2::bitarrp)))
  (defun bitarr-sizedp (bitarr aignet)
    (declare (xargs :stobjs (bitarr aignet)
                    :guard-hints ('(:in-theory (e/d (memo-tablep))))))
    (mbe :logic (non-exec (memo-tablep bitarr aignet))
         :exec (<= (num-nodes aignet) (bits-length bitarr))))

  (defun bitarr-id-in-bounds (id bitarr)
    (declare (xargs :guard (idp id)
                    :stobjs bitarr
                    :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
    (mbe :logic (non-exec (id-in-bounds id bitarr))
         :exec (< (id-val id) (bits-length bitarr))))

  (defun bitarr-iterator-in-bounds (n bitarr)
    (declare (xargs :guard (natp n)
                    :stobjs bitarr
                    :guard-hints (("goal" :in-theory (e/d (iterator-in-bounds))))))
    (mbe :logic (non-exec (iterator-in-bounds n bitarr))
         :exec (<= (nfix n) (bits-length bitarr))))

  (definline get-id->bit (id bitarr)
    (declare (type (integer 0 *) id)
             (xargs :stobjs bitarr
                    :guard (and (idp id)
                                (bitarr-id-in-bounds id bitarr))))
    (get-bit (id-val id) bitarr))

  (definline set-id->bit (id v bitarr)
    (declare (type (integer 0 *) id)
             (xargs :stobjs bitarr
                    :guard (and (idp id)
                                (bitp v)
                                (bitarr-id-in-bounds id bitarr))))
    (set-bit (id-val id) v bitarr))

  (local (in-theory (enable resize-list)))

  (definline bitarr-clear (bitarr)
    (declare (xargs :stobjs bitarr
                    :guard-hints ('(:expand ((len bitarr)
                                             (len (cdr bitarr)))
                                    :in-theory (e/d (nth update-nth))))))
    (mbe :logic (non-exec nil)
         :exec (resize-bits 0 bitarr))))

(defsection semantics

  (defund gate-orderedp (n aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp n aignet)
                                (int= (id->type n aignet) (gate-type)))))
    (and (< (id-val (lit-id (gate-id->fanin0 n aignet))) (id-val n))
         (< (id-val (lit-id (gate-id->fanin1 n aignet))) (id-val n))))

  (local (in-theory (enable gate-orderedp)))

  (defthm gate-orderedp-when-aignet-well-formed
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (gate-type)))
             (gate-orderedp n aignet)))

  (defund co-orderedp (n aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-sizes-ok aignet)
                                (aignet-idp n aignet)
                                (int= (id->type n aignet) (out-type)))))
    (< (id-val (lit-id (co-id->fanin n aignet))) (id-val n)))

  (local (in-theory (enable co-orderedp)))

  (defthm co-orderedp-when-aignet-well-formed
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp n aignet)
                  (equal (id->type n aignet) (out-type)))
             (co-orderedp n aignet)))

  (mutual-recursion
   (defun lit-eval (lit in-vals reg-vals aignet)
     (declare (xargs :stobjs aignet
                     :guard (and (aignet-well-formedp aignet)
                                 (aignet-litp lit aignet)
                                 (true-listp in-vals)
                                 (true-listp reg-vals))
                     :measure (+ 1 (* 2 (id-val (lit-id lit))))
                     :verify-guards nil))
     (b-xor (id-eval (lit-id lit) in-vals reg-vals aignet)
            (lit-neg lit)))

   (defun id-eval (id in-vals reg-vals aignet)
     (declare (xargs :stobjs aignet
                     :guard (and (aignet-well-formedp aignet)
                                 (aignet-idp id aignet)
                                 (true-listp in-vals)
                                 (true-listp reg-vals))
                     :measure (* 2 (id-val id))))
     (b* (((unless (mbt (aignet-idp (id-fix id) aignet)))
           ;; out-of-bounds IDs are false
           0)
          (type (id->type id aignet)))
       (aignet-case
        type
        :gate (b* ((f0 (gate-id->fanin0 id aignet))
                   (f1 (gate-id->fanin1 id aignet)))
                (mbe :logic (if (gate-orderedp id aignet)
                                (b-and (lit-eval f0 in-vals reg-vals aignet)
                                             (lit-eval f1 in-vals reg-vals aignet))
                              0)
                     :exec (b-and (lit-eval f0 in-vals reg-vals aignet)
                                        (lit-eval f1 in-vals reg-vals aignet))))
        :in    (if (int= (io-id->regp id aignet) 1)
                   (bfix (nth (io-id->ionum id aignet) reg-vals))
                 (bfix (nth (io-id->ionum id aignet) in-vals)))
        :out (b* ((f (co-id->fanin id aignet)))
               (mbe :logic (if (co-orderedp id aignet)
                               (lit-eval f in-vals reg-vals aignet)
                             0)
                    :exec (lit-eval f in-vals reg-vals aignet)))
        :const 0))))

  (defun-nx id-eval-ind (id in-vals reg-vals aignet)
    (declare (xargs :measure (id-val id)))
    (b* (((unless (mbt (aignet-idp (id-fix id) aignet)))
          ;; out-of-bounds IDs are false
          0)
         (type (id->type id aignet)))
      (aignet-case
       type
       :gate (b* ((f0 (gate-id->fanin0 id aignet))
                  (f1 (gate-id->fanin1 id aignet)))
               (if (gate-orderedp id aignet)
                   (list (id-eval-ind (lit-id f0) in-vals reg-vals aignet)
                         (id-eval-ind (lit-id f1) in-vals reg-vals aignet))
                 0))
       :in    (list in-vals reg-vals)
       :out (b* ((f (co-id->fanin id aignet)))
              (if (co-orderedp id aignet)
                  (id-eval-ind (lit-id f) in-vals reg-vals aignet)
                0))
       :const 0)))

  (defcong id-equiv equal (id-eval id in-vals reg-vals aignet) 1
    :hints (("goal" :expand ((id-eval id in-vals reg-vals aignet)
                             (id-eval id-equiv in-vals reg-vals aignet)))))

  (defcong bits-equiv equal (id-eval id in-vals reg-vals aignet) 2
    :hints (("goal" :induct (id-eval-ind id in-vals reg-vals aignet)
             :expand ((:free (in-vals reg-vals)
                       (id-eval id in-vals reg-vals aignet))))))

  (defcong bits-equiv equal (id-eval id in-vals reg-vals aignet) 3
    :hints (("goal" :induct (id-eval-ind id in-vals reg-vals aignet)
             :expand ((:free (in-vals reg-vals)
                       (id-eval id in-vals reg-vals aignet))))))

  (defcong lit-equiv equal (lit-eval lit in-vals reg-vals aignet) 1
    :hints (("goal" :expand ((lit-eval lit in-vals reg-vals aignet)
                             (lit-eval lit-equiv in-vals reg-vals aignet)))))

  (flag::make-flag lit/id-eval-flag lit-eval
                   :flag-mapping ((lit-eval . lit)
                                  (id-eval . id)))

  (defthm bitp-of-lit-eval
    (bitp (lit-eval lit in-vals reg-vals aignet))
    :hints (("goal" :expand (lit-eval lit in-vals reg-vals aignet))))

  (defthm bitp-of-id-eval
    (bitp (id-eval id in-vals reg-vals aignet))
    :hints (("goal" :expand (id-eval id in-vals reg-vals aignet))))

  (verify-guards lit-eval)

  (defthm-lit/id-eval-flag
    (defthm nth-equiv-congruence-of-lit-eval-ins
      (implies (nth-equiv in-vals in-vals1)
               (equal (lit-eval lit in-vals reg-vals aignet)
                      (lit-eval lit in-vals1 reg-vals aignet)))
      :rule-classes :congruence
      :flag lit)
    (defthm nth-equiv-congruence-of-id-eval-ins
      (implies (nth-equiv in-vals in-vals1)
               (equal (id-eval id in-vals reg-vals aignet)
                      (id-eval id in-vals1 reg-vals aignet)))
      :rule-classes :congruence
      :flag id))

  (defthm-lit/id-eval-flag
    (defthm nth-equiv-congruence-of-lit-eval-regs
      (implies (nth-equiv reg-vals reg-vals1)
               (equal (lit-eval lit in-vals reg-vals aignet)
                      (lit-eval lit in-vals reg-vals1 aignet)))
      :rule-classes :congruence
      :flag lit)
    (defthm nth-equiv-congruence-of-id-eval-regs
      (implies (nth-equiv reg-vals reg-vals1)
               (equal (id-eval id in-vals reg-vals aignet)
                      (id-eval id in-vals reg-vals1 aignet)))
      :rule-classes :congruence
      :flag id))

  (defthm-lit/id-eval-flag
    (defthm nth-equiv-congruence-of-lit-eval-aignet
      (implies (nth-equiv aignet aignet1)
               (equal (lit-eval lit in-vals reg-vals aignet)
                      (lit-eval lit in-vals reg-vals aignet1)))
      :rule-classes :congruence
      :flag lit)
    (defthm nth-equiv-congruence-of-id-eval-aignet
      (implies (nth-equiv aignet aignet1)
               (equal (id-eval id in-vals reg-vals aignet)
                      (id-eval id in-vals reg-vals aignet1)))
      :rule-classes :congruence
      :flag id))

  (defthm-lit/id-eval-flag
    (defthm id-eval-preserved-by-extension
      (implies (and (aignet-extension-binding :orig-aignet aignet)
                    (aignet-extension-p new-aignet aignet)
                    (aignet-idp id aignet))
               (equal (id-eval id in-vals reg-vals new-aignet)
                      (id-eval id in-vals reg-vals aignet)))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable aignet-litp aignet-idp))))
      :flag id)
    (defthm lit-eval-preserved-by-extension
      (implies (and (aignet-extension-binding :orig-aignet aignet)
                    (aignet-extension-p new-aignet aignet)
                    (aignet-idp (lit-id lit) aignet))
               (equal (lit-eval lit in-vals reg-vals new-aignet)
                      (lit-eval lit in-vals reg-vals aignet)))
      :flag lit))


  (defthm id-eval-of-aignet-lit-fix
    (implies (aignet-well-formedp aignet)
             (equal (id-eval (lit-id (aignet-lit-fix x aignet)) in-vals reg-vals aignet)
                    (b-xor (id-eval (lit-id x) in-vals reg-vals aignet)
                                 (b-xor (lit-neg x)
                                              (lit-neg (aignet-lit-fix x aignet))))))
    :hints(("Goal" :in-theory (e/d (aignet-lit-fix aignet-litp aignet-idp)
                                   (id-eval))
            :expand ((id-eval (lit-id x) in-vals reg-vals aignet)
                     (id-eval 0 in-vals reg-vals aignet)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (b-xor lit-eval
                                               equal-1-to-bitp))))))

  (defthm lit-eval-of-aignet-lit-fix
    (implies (aignet-well-formedp aignet)
             (equal (lit-eval (aignet-lit-fix x aignet) in-vals reg-vals aignet)
                    (lit-eval x in-vals reg-vals aignet)))
    :hints(("Goal" :in-theory (e/d (lit-eval b-xor
                                             b-not
                                             equal-1-to-bitp))
            :expand ((lit-eval (aignet-lit-fix x aignet) in-vals reg-vals aignet)
                     (lit-eval x in-vals reg-vals aignet)))))


  (defund eval-and-of-lits (lit1 lit2 in-vals reg-vals aignet)
    (declare (xargs :stobjs (aignet)
                    :verify-guards nil))
    (b-and (lit-eval lit1 in-vals reg-vals aignet)
                 (lit-eval lit2 in-vals reg-vals aignet)))
  (local (in-theory (enable eval-and-of-lits)))
  (defcong lit-equiv equal (lit-eval lit in-vals reg-vals aignet) 1
    :hints(("Goal" :in-theory (enable lit-eval))))
  (defcong lit-equiv equal (eval-and-of-lits lit1 lit2 in-vals reg-vals aignet) 1
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))
  (defcong lit-equiv equal (eval-and-of-lits lit1 lit2 in-vals reg-vals aignet) 2
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defun lit-eval-list (x in-vals reg-vals aignet)
    (declare (xargs :stobjs (aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-lit-listp x aignet)
                                (true-listp in-vals)
                                (true-listp reg-vals))))
    (if (atom x)
        nil
      (cons (lit-eval (car x) in-vals reg-vals aignet)
            (lit-eval-list (cdr x) in-vals reg-vals aignet))))

  (defthm lit-eval-list-preserved-by-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-lit-listp lits orig-aignet))
             (equal (lit-eval-list lits in-vals reg-vals new-aignet)
                    (lit-eval-list lits in-vals reg-vals orig-aignet))))


  (defmvtypes acl2::aignet-add-gate$inline (natp nil))

  (defthm num-gates-of-aignet-add-gate
    (equal (nth *num-gates* (mv-nth 1 (aignet-add-gate lit1 lit2 aignet)))
           (+ 1 (nfix (num-gates aignet)))))

  (defthm id-eval-of-aignet-add-gate-new
    (implies (aignet-well-formedp aignet)
             (b* ((new-id (to-id (nth *num-nodes* aignet)))
                  (aignet1 (mv-nth 1 (aignet-add-gate lit1 lit2 aignet))))
               (equal (id-eval new-id in-vals reg-vals aignet1)
                      (b-and (lit-eval lit1 in-vals reg-vals aignet)
                                   (lit-eval lit2 in-vals reg-vals aignet)))))
    :hints(("Goal" :expand ((:free (name type aignet1)
                             (id-eval (to-id (nth *num-nodes* aignet)) in-vals reg-vals aignet1)))
            :in-theory (e/d (gate-orderedp) (aignet-add-gate))))))

(defsection aignet-evaluation
 :parents (aignet)
  :short "Evaluation semantics of AIGNET networks"
  :autodoc nil
  :long "
<p>The (combinational) semantics of an AIGNET network is given by the function
@({'(lit-eval lit aignet-vals aignet)').})
Net-eval is simply an array of bits holding a value for each node in the
network.  However, lit-eval only uses the values that are stored for primary
input and register output nodes to compute evaluations.   Furthermore, lit-eval
does no memoization, so it is not intended to be used in execution.  Rather, it
is a simple specification for the semantics of nodes.</p>

<p>To actually execute evaluations of nodes, use the functions
@({(aignet-eval n aignet-vals aignet)})
and
@({(aignet-eval-frame n k aignet-vals aignet-frames aignet)})
both of which return <tt>aignet-vals</tt>.  Instead of giving the evaluation of
one literal, these record the evaluations of every node (starting at
<tt>n</tt>) in the <tt>aignet-vals</tt> table. Then,
@({(get-id->bit id aignet-vals)})
or
@({(aignet-eval-lit lit aignet-vals)})
may be used to retrieve them.  These values are then provably equal to,
respectively,
@({(lit-eval (mk-lit id 0) aignet-vals aignet)})
and
@({(lit-eval lit aignet-vals aignet),})
by the following theorem:
@(thm aignet-eval-lit-of-aignet-eval)</p>

<p>The difference between @('aignet-eval') and @('aignet-eval-frame') is that
aignet-eval-frame is designed to be used as part of a sequential simulation.
Therefore, it looks up input nodes in a separate structure
<tt>aignet-frames</tt> which gives a value for each input at each frame.  It
assigns values to register output nodes by checking the value stored for its
corresponding register input in the <tt>aignet-vals</tt> structure.  For both
of these node types, @('aignet-eval') assumes that they are already set to the
desired values, and skips them.  The final result is equivalent to the result
of @('aignet-vals') after first copying the RI values to the corresponding ROs
and the inputs from the appropriate frame:
@(thm aignet-eval-frame-rw)</p>

<p>For higher-level functions for simulation, see the book \"aignet-sim.lisp\".</p>
"
  (local (in-theory (disable acl2::bfix-when-not-1
                             acl2::nfix-when-not-natp)))


  (defstobj-clone aignet-vals bitarr :strsubst (("BIT" . "AIGNET-VAL")))

  (local (in-theory (disable acl2::nth-with-large-index)))

  (definline aignet-eval-lit (lit aignet-vals)
    (declare (type (integer 0 *) lit)
             (xargs :stobjs aignet-vals
                    :guard (and (litp lit)
                                (bitarr-id-in-bounds (lit-id lit) aignet-vals))))
    (b-xor (lit-neg lit)
                 (get-id->bit (lit-id lit) aignet-vals)))

  ;; (local (in-theory (enable nth-in-aignet-valsp-bound
  ;;                           nth-in-aignet-valsp-type)))

  (local (in-theory (disable acl2::logxor-equal-0)))


  (defiteration
    aignet-eval (aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet))))
    (b* ((n (lnfix n))
         (nid (to-id n))
         (slot0 (get-node-slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate  (b* ((f0 (snode-gate->fanin0 slot0))
                   (f1 (gate-id->fanin1 nid aignet))
                   (v0 (aignet-eval-lit f0 aignet-vals))
                   (v1 (aignet-eval-lit f1 aignet-vals))
                   (val (mbe :logic (if (gate-orderedp nid aignet)
                                        (b-and v0 v1)
                                      0)
                             :exec (b-and v0 v1))))
                (set-id->bit nid val aignet-vals))
       :out   (b* ((f0 (snode-co->fanin slot0))
                   (v0 (aignet-eval-lit f0 aignet-vals))
                   (val (mbe :logic (if (co-orderedp nid aignet)
                                        v0
                                      0)
                             :exec v0)))
                (set-id->bit nid val aignet-vals))
       :const (set-id->bit nid 0 aignet-vals)
       :in    aignet-vals))
    :index n
    :returns aignet-vals
    :last (num-nodes aignet)
    :package aignet::foo)

  (local (in-theory (enable (:induction aignet-eval-iter))))


  (defthm aignet-eval-well-sizedp-after-aignet-eval
    (implies (memo-tablep aignet-vals aignet)
             (memo-tablep (aignet-eval-iter n aignet-vals aignet)
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n aignet-vals aignet))))


  (defiteration aignet-vals-in-vals (in-vals aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (true-listp in-vals))))
    (b* ((id (innum->id n aignet))
         (val (get-id->bit id aignet-vals)))
      (update-nth n val in-vals))
    :returns in-vals
    :index n
    :last (num-ins aignet))

  (in-theory (enable (:induction aignet-vals-in-vals-iter)))

  (defthm nth-of-aignet-vals-in-vals
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (nfix m))
                  (<= (nfix m) (num-ins aignet)))
             (bit-equiv
              (nth n (aignet-vals-in-vals-iter m in-vals aignet-vals aignet))
              (nth (id-val (innum->id n aignet))
                   aignet-vals)))
    :hints ((acl2::just-induct-and-expand (aignet-vals-in-vals-iter m in-vals aignet-vals aignet))))

  (defiteration aignet-vals-reg-vals (reg-vals aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (true-listp reg-vals))))
    (b* ((id (regnum->ro n aignet))
         (val (get-id->bit id aignet-vals)))
      (update-nth n val reg-vals))
    :returns reg-vals
    :index n
    :last (num-regs aignet))

  (in-theory (enable (:induction aignet-vals-reg-vals-iter)))

  (defthm nth-of-aignet-vals-reg-vals
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (nfix m))
                  (<= (nfix m) (num-regs aignet)))
             (bit-equiv
              (nth n (aignet-vals-reg-vals-iter m reg-vals aignet-vals aignet))
              (nth (id-val (regnum->ro n aignet))
                   aignet-vals)))
    :hints ((acl2::just-induct-and-expand (aignet-vals-reg-vals-iter m reg-vals aignet-vals aignet))))

  (defthm aignet-eval-preserves-ci-val
    (implies (equal (id->type (to-id id) aignet) (in-type))
             (equal (nth id (aignet-eval-iter n aignet-vals
                                                           aignet))
                    (nth id aignet-vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n aignet-vals aignet))))

  (defthm aignet-eval-preserves-in-vals
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-ins aignet)))
             (equal (aignet-vals-in-vals-iter n in-vals
                                              (aignet-eval-iter m aignet-vals aignet)
                                              aignet)
                    (aignet-vals-in-vals-iter n in-vals aignet-vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-in-vals-iter n in-vals aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-in-vals-iter n in-vals aignet-vals aignet))))
            (and stable-under-simplificationp
                 '(:in-theory (enable* aignet-well-formedp-strong-rules)))))

  (defthm aignet-eval-preserves-reg-vals
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-regs aignet)))
             (equal (aignet-vals-reg-vals-iter n reg-vals
                                               (aignet-eval-iter m aignet-vals aignet)
                                               aignet)
                    (aignet-vals-reg-vals-iter n reg-vals aignet-vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-reg-vals-iter n reg-vals aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-reg-vals-iter n reg-vals aignet-vals aignet))))
            (and stable-under-simplificationp
                 '(:in-theory (enable* aignet-well-formedp-strong-rules)))))


  (defthmd nth-in-aignet-eval-iter-preserved
    (implies (and (< (nfix m) (nfix n))
                  (equal nm (1+ (nfix m)))
                  (syntaxp (not (equal n nm))))
             (equal (nth m (aignet-eval-iter n aignet-vals
                                                          aignet))
                    (nth m (aignet-eval-iter nm aignet-vals
                                                          aignet))))
    :hints ((acl2::just-induct-and-expand (aignet-eval-iter n aignet-vals aignet))
            '(:in-theory (disable b-xor b-and
                                  aignet-eval-lit
                                  (:definition aignet-eval-iter)
                                  co-orderedp
                                  gate-orderedp))
            (and stable-under-simplificationp
                 '(:expand ((aignet-eval-iter (+ 1 (nfix m)) aignet-vals
                                              aignet))))))


  (defthm aignet-eval-nth-previous
    (implies (<= (nfix n) (nfix m))
             (equal (nth m (aignet-eval-iter n aignet-vals aignet))
                    (nth m aignet-vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n aignet-vals aignet))
            '(:in-theory (disable nth-in-aignet-eval-iter-preserved
                                  aignet-eval-iter))))

  (in-theory (disable id-eval lit-eval))

  (defthm aignet-eval-records-id-evals-lemma
    (implies (and (aignet-well-formedp aignet)
                  (< (id-val id) (nfix n))
                  (idp id)
                  (<= (nfix n) (nfix (num-nodes aignet))))
             (bit-equiv (nth (id-val id)
                                   (aignet-eval-iter n aignet-vals
                                                                  aignet))
                              (id-eval id
                                       (aignet-vals-in-vals nil aignet-vals aignet)
                                       (aignet-vals-reg-vals nil aignet-vals aignet)
                                       aignet)))
    :hints ((acl2::just-induct-and-expand
             (id-eval-ind id (aignet-vals-in-vals nil aignet-vals aignet)
                          (aignet-vals-reg-vals nil aignet-vals aignet)
                          aignet)
             :expand-others
             ((id-eval id (aignet-vals-in-vals nil aignet-vals aignet)
                       (aignet-vals-reg-vals nil aignet-vals aignet)
                       aignet)))
            '(:in-theory (enable* lit-eval
                                  nth-in-aignet-eval-iter-preserved
                                 aignet-idp aignet-litp
                                 gate-orderedp co-orderedp
                                 aignet-well-formedp-strong-rules)
              :expand ((aignet-eval-iter
                        (+ 1 (id-val id)) aignet-vals aignet))))
    :rule-classes nil)

  (defthm aignet-eval-records-id-evals
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix id) (nfix n))
                  (<= (nfix n) (num-nodes aignet)))
             (bit-equiv (nth id
                                   (aignet-eval-iter n aignet-vals
                                                                  aignet))
                              (id-eval (to-id id)
                                       (aignet-vals-in-vals nil aignet-vals aignet)
                                       (aignet-vals-reg-vals nil aignet-vals aignet)
                                       aignet)))
    :hints (("goal" :use ((:instance aignet-eval-records-id-evals-lemma
                           (id (to-id id)))))))

  (defthm aignet-eval-lit-of-aignet-eval
    (implies (and (aignet-well-formedp aignet)
                  (aignet-litp lit aignet))
             (equal (aignet-eval-lit lit (aignet-eval-iter
                                          (nth *num-nodes* aignet)
                                          aignet-vals aignet))
                    (lit-eval lit
                              (aignet-vals-in-vals nil aignet-vals aignet)
                              (aignet-vals-reg-vals nil aignet-vals aignet)
                              aignet)))
    :hints(("Goal" :in-theory (e/d (lit-eval aignet-litp aignet-idp)))))


  (defthm aignet-eval-iter-of-update-greater
    (implies (<= (nfix n) (nfix m))
             (equal (aignet-eval-iter
                     n (update-nth m val aignet-vals)
                     aignet)
                    (let ((aignet-vals (aignet-eval-iter
                                        n aignet-vals aignet)))
                      (update-nth m val                                                                  aignet-vals))))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-iter n aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-eval-iter n aignet-vals aignet))))
            '(:in-theory (e/d (co-orderedp gate-orderedp)
                              (nth-in-aignet-eval-iter-preserved
                               aignet-eval-iter))))))

(defsection simplify-gate

;  (local (include-book "bit-lemmas"))

  (local (in-theory (disable acl2::bfix-when-not-1
                             acl2::bfix-when-not-bitp
                             id-eval
                             equal-of-to-lit-backchain
                             o<)))

  (defsection two-id-measure

    (local (in-theory (enable natp)))

    (defund two-id-measure (x y)
      (declare (xargs :guard (and (idp x) (idp y))))
      (let ((x (id-val x))
            (y (id-val y)))
        (acl2::two-nats-measure
         (+ 1 (max x y))
         (+ 1 (min x y)))))

    (local (in-theory (enable two-id-measure)))

    (defthm two-id-measure-symm
      (equal (two-id-measure id1 id2)
             (two-id-measure id2 id1)))

    (defthm o-p-of-two-id-measure
      (o-p (two-id-measure x y)))

    (local (in-theory (enable aignet-idp)))

    (defthm two-id-measure-of-gate
      (implies (and (aignet-well-formedp aignet)
                    (equal (id->type id1 aignet) (gate-type))
                    (aignet-idp id1 aignet))
               (b* ((node (nth-node id1 (nth *nodesi* aignet)))
                    (ch1 (gate-node->fanin0 node))
                    (ch2 (gate-node->fanin1 node)))
                 (and (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id1 id2))
                      (o< (two-id-measure id2 (lit-id ch2))
                          (two-id-measure id1 id2))
                      (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id2 id1))
                      (o< (two-id-measure id2 (lit-id ch2))
                          (two-id-measure id2 id1))))))

    (defthm two-id-measure-of-out
      (implies (and (aignet-well-formedp aignet)
                    (equal (id->type id1 aignet) (out-type))
                    (aignet-idp id1 aignet))
               (b* ((node (nth-node id1 (nth *nodesi* aignet)))
                    (ch1 (co-node->fanin node)))
                 (and (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id1 id2))
                      (o< (two-id-measure id2 (lit-id ch1))
                          (two-id-measure id2 id1)))))))

  (defsection aignet-gate-simp-order
    (defund aignet-gate-simp-order (lit1 lit2 aignet)
      (declare (type (integer 0 *) lit1)
               (type (integer 0 *) lit2)
               (xargs :stobjs aignet
                      :guard (and (aignet-well-formedp aignet)
                                  (aignet-litp lit1 aignet)
                                  (aignet-litp lit2 aignet))))
      (b* ((lit1 (lit-fix lit1))
           (lit2 (lit-fix lit2))
           (id1 (lit-id lit1))
           (id2 (lit-id lit2))
           (gatep1 (int= (id->type id1 aignet) (gate-type)))
           (gatep2 (int= (id->type id2 aignet) (gate-type)))
           ((mv lit1 lit2 both neither)
            (if gatep1
                (if gatep2
                    (mv lit1 lit2 t nil)
                  (mv lit1 lit2 nil nil))
              (if gatep2
                  (mv lit2 lit1 nil nil)
                (mv lit1 lit2 nil t))))
           ((when neither)
            (mv lit1 lit2 both neither))
           ((mv lit1 lit2)
            (if (and both (< lit1 lit2))
                (mv lit2 lit1)
              (mv lit1 lit2))))
        (mv lit1 lit2 both neither)))

    (local (in-theory (enable aignet-gate-simp-order)))

    (defcong lit-equiv equal (aignet-gate-simp-order lit1 lit2 aignet) 1)
    (defcong lit-equiv equal (aignet-gate-simp-order lit1 lit2 aignet) 2)

    (defthm aignet-gate-simp-order-flags1
      (b* (((mv ?nlit1 ?nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (equal neither
               (not (equal (id->type (lit-id nlit1) aignet) (gate-type))))))

    (defthm aignet-gate-simp-order-flags2
      (b* (((mv ?nlit1 ?nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (equal both
               (equal (id->type (lit-id nlit2) aignet) (gate-type)))))

    (defthm aignet-gate-simp-order-flags3
      (b* (((mv ?nlit1 ?nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (implies (not (equal (id->type (lit-id nlit1) aignet) (gate-type)))
                 (not (equal (id->type (lit-id nlit2) aignet) (gate-type))))))

    (defthm two-id-measure-of-aignet-gate-simp-order
      (b* (((mv nlit1 nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (and (equal (two-id-measure (lit-id nlit1) (lit-id nlit2))
                    (two-id-measure (lit-id lit1) (lit-id lit2)))
             (equal (two-id-measure (lit-id nlit2) (lit-id nlit1))
                    (two-id-measure (lit-id lit1) (lit-id lit2)))))
      :hints(("Goal" :in-theory (enable two-id-measure))))

    (defmvtypes aignet-gate-simp-order (natp natp))

    (defthm fanin-precedes-gate-of-aignet-gate-simp-order
      (implies (and (< (id-val (lit-id lit1)) ngates)
                    (< (id-val (lit-id lit2)) ngates)
                    (natp ngates))
               (b* (((mv nlit1 nlit2 ?both ?neither)
                     (aignet-gate-simp-order lit1 lit2 aignet)))
                 (and (< (id-val (lit-id nlit1)) ngates)
                      (< (id-val (lit-id nlit2)) ngates))))
      :rule-classes (:rewrite :linear))

    (defthm eval-and-of-lits-of-aignet-gate-simp-order
      (b* (((mv nlit1 nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (equal (eval-and-of-lits nlit1 nlit2 in-vals reg-vals aignet)
               (eval-and-of-lits lit1 lit2 in-vals reg-vals aignet)))
      :hints(("Goal" :in-theory (enable eval-and-of-lits))))

    (def-aignet-frame aignet-gate-simp-order)

    ;; (defthmd aignet-gate-simp-order-frame
    ;;   (implies
    ;;    (and (not (equal (nfix n) *num-nodes*))
    ;;         (not (equal (nfix n) *nodesi*)))
    ;;    (equal (let ((aignet (update-nth n v aignet)))
    ;;             (aignet-gate-simp-order lit1 lit2 aignet))
    ;;           (aignet-gate-simp-order lit1 lit2 aignet))))
    ;; (acl2::add-to-ruleset aignet-frame-thms aignet-gate-simp-order-frame)


    ;; (defthm faninp-of-aignet-gate-simp-order
    ;;   (b* (((mv nlit1 nlit2 ?both ?neither)
    ;;         (aignet-gate-simp-order lit1 lit2 aignet)))
    ;;     (implies (and (not (equal (id->type (lit-id lit1) aignet) (out-type)))
    ;;                   (not (equal (id->type (lit-id lit2) aignet) (out-type))))
    ;;              (let ((nodes (nth *nodesi* aignet)))
    ;;                (and (not (equal (node->type (nth-node (lit-id nlit1) nodes)) (out-type)))
    ;;                     (not (equal (node->type (nth-node (lit-id nlit2) nodes))
    ;;                                 (out-type))))))))

    (defthm aignet-litp-of-aignet-gate-simp-order
      (implies (and (aignet-litp lit1 aignet)
                    (aignet-litp lit2 aignet))
               (b* (((mv nlit1 nlit2 ?both ?neither)
                     (aignet-gate-simp-order lit1 lit2 aignet)))
                 (and (aignet-litp nlit1 aignet)
                      (aignet-litp nlit2 aignet)))))

    (defthm litp-of-aignet-gate-simp-order
      (b* (((mv nlit1 nlit2 ?both ?neither)
            (aignet-gate-simp-order lit1 lit2 aignet)))
        (and (litp nlit1)
             (litp nlit2)))))



  ;; takes arguments lit1, lit2, and returns:
  ;; (mv exists flg nlit1 nlit2).
  ;;  - if exists is nonnil, it is an in-bounds literal equivalent to lit1 & lit2
  ;;  - otherwise if flg is t, then nlit1, nlit2 are in-bounds and
  ;;       nlit1 & nlit2 === lit1 & lit2
  ;;  - otherwise no simplification was found.
  (acl2::deffunmac
   def-gate-simp (name body
                       &key extra-args
                       (guard 't)
                       (reqs 'nil)
                       (eval-hints 'nil)
                       (fanin-hints 'nil)
; (bounds-hints 'nil)
                       (guard-hints 'nil)
                       (measure-hints 'nil)
                       (skip-measure 'nil)
                       (frame-hints 'nil)
                       (aignet-litp-hints 'nil)
                       (lit-cong1-hints 'nil)
                       (lit-cong2-hints 'nil)
; (nth-cong-hints 'nil)
                       (xargs 'nil))
   `(defsection ,name
      (defund ,name (lit1 lit2 ,@extra-args aignet)
        (declare (type (integer 0 *) lit1)
                 (type (integer 0 *) lit2)
                 (xargs :stobjs aignet
                        :guard (and (aignet-well-formedp aignet)
                                    (aignet-litp lit1 aignet)
                                    (aignet-litp lit2 aignet)
                                    ,guard)
                        :guard-hints ,guard-hints)
                 (xargs . ,xargs))
        ,body)

      (local (in-theory (enable ,name)))

      (defmvtypes ,name (nil nil natp natp))

      (defthm ,(mksym name (symbol-name name) "-TYPE")
        (or (not (mv-nth 0 (,name lit1 lit2 ,@extra-args aignet)))
            (natp (mv-nth 0 (,name lit1 lit2 ,@extra-args aignet))))
        :rule-classes :type-prescription)

      (def-aignet-frame ,name
        ,@(and frame-hints `(:hints ,frame-hints)))

      ;; (defthmd ,(mksym name (symbol-name name) "-FRAME")
      ;;   (implies
      ;;    (and (not (equal (nfix n) *num-nodes*))
      ;;         (not (equal (nfix n) *nodesi*)))
      ;;    (equal (let ((aignet (update-nth n v aignet)))
      ;;             (,name lit1 lit2 ,@extra-args aignet))
      ;;           (,name lit1 lit2 ,@extra-args aignet)))
      ;;   :hints ,(or frame-hints
      ;;               '(("Goal" :in-theory (enable* aignet-frame-thms)))))

      ;; (add-to-ruleset aignet-frame-thms
      ;;                 ,(mksym name (symbol-name name) "-FRAME"))

      (defcong lit-equiv equal (,name lit1 lit2 ,@extra-args aignet) 1
        :hints ,lit-cong1-hints)
      (defcong lit-equiv equal (,name lit1 lit2 ,@extra-args aignet) 2
        :hints ,lit-cong2-hints)
      ;; (defcong nth-equiv equal
      ;;            (,name lit1 lit2 ,@extra-args aignet)
      ;;            ,(+ 3 (- (len extra-args)
      ;;                     (len (member 'aignet extra-args))))
      ;;            :hints ,nth-cong-hints)

      (defthm ,(mksym name "FANIN-PRECEDES-GATE-OF-" (symbol-name name))
        (implies (and (< (id-val (lit-id lit1)) gate)
                      (< (id-val (lit-id lit2)) gate)
                      (aignet-litp lit1 aignet)
                      (aignet-litp lit2 aignet)
                      (natp gate)
                      ;; (<= gate (nfix (nth *num-nodes* aignet)))
                      (aignet-well-formedp aignet)
                      . ,reqs)
                 (b* (((mv extra ?flg nlit1 nlit2)
                       (,name lit1 lit2 ,@extra-args aignet)))
                   (and (implies extra
                                 (< (id-val (lit-id extra)) gate))
                        (< (id-val (lit-id nlit1)) gate)
                        (< (id-val (lit-id nlit2)) gate))))
        :hints ,fanin-hints
        :rule-classes (:rewrite ;; :linear
                       ))

      ,@(and
         (not skip-measure)
         `((defthm ,(mksym name "TWO-ID-MEASURE-OF-" (symbol-name name))
             (implies (and (aignet-litp lit1 aignet)
                           (aignet-litp lit2 aignet)
                           (aignet-well-formedp aignet)
                           . ,reqs)
                      (b* (((mv ?extra flg nlit1 nlit2)
                            (,name lit1 lit2 ,@extra-args aignet)))
                        (implies flg
                                 (o< (two-id-measure (lit-id nlit1)
                                                     (lit-id nlit2))
                                     (two-id-measure (lit-id lit1)
                                                     (lit-id lit2))))))
             :hints ,measure-hints)))

      (defthm ,(mksym name "AIGNET-LITP-OF-" (symbol-name name))
        (b* (((mv extra ?flg nlit1 nlit2)
              (,name lit1 lit2 ,@extra-args aignet)))
          (implies (and (aignet-well-formedp aignet)
                        (aignet-litp lit1 aignet)
                        (aignet-litp lit2 aignet)
                        . ,reqs)
                   (and (implies extra
                                 (aignet-litp extra aignet))
                        (aignet-litp nlit1 aignet)
                        (aignet-litp nlit2 aignet))))
        :hints ,aignet-litp-hints)


      (defthm ,(mksym name "ID-EVAL-OF-" (symbol-name name))
        (b* (((mv extra ?flg nlit1 nlit2)
              (,name lit1 lit2 ,@extra-args aignet)))
          (implies (and (aignet-well-formedp aignet)
                        (aignet-litp lit1 aignet)
                        (aignet-litp lit2 aignet)
                        . ,reqs)
                   (and (implies extra
                                 (equal (lit-eval extra in-vals reg-vals aignet)
                                        (eval-and-of-lits lit1 lit2 in-vals reg-vals
                                                                       aignet)))
                        (equal (eval-and-of-lits nlit1 nlit2 in-vals reg-vals aignet)
                               (eval-and-of-lits lit1 lit2 in-vals reg-vals aignet)))))
        :hints ,eval-hints)

      (defthm ,(mksym name "LITP-OF-" (symbol-name name))
        (b* (((mv extra ?flg nlit1 nlit2)
              (,name lit1 lit2 ,@extra-args aignet)))
          (and (implies extra
                        (litp extra))
               (litp nlit1)
               (litp nlit2))))))


  (local (in-theory (disable len
                             acl2::nth-with-large-index)))

  ;; (defthmd bits-equal-of-logxor
  ;;   (implies (and (bitp c)
  ;;                 (bitp b)
  ;;                 (bitp a))
  ;;            (equal (equal c (logxor a b))
  ;;                   (equal (equal c 1) (xor (equal a 1) (equal b 1)))))
  ;;   :hints(("Goal" :in-theory (enable bitp))))

  ;; (defthmd bits-equal-of-logand
  ;;   (implies (and (bitp c)
  ;;                 (bitp b)
  ;;                 (bitp a))
  ;;            (equal (equal c (logand a b))
  ;;                   (equal (equal c 1) (and (equal a 1) (equal b 1)))))
  ;;   :hints(("Goal" :in-theory (enable bitp))))

  ;; (defthm logand-of-same
  ;;   (equal (logand a a)
  ;;          (ifix a))
  ;;   :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
  ;;                                      acl2::ihsext-recursive-redefs))))

  ;; (defthm lognot-lognot
  ;;   (equal (lognot (lognot x))
  ;;          (ifix x))
  ;;   :hints(("Goal" :in-theory (enable lognot))))

  ;; (defthm logxor-of-a-a-b
  ;;   (equal (logxor a a b)
  ;;          (ifix b))
  ;;   :hints(("Goal" :in-theory (e/d* (acl2::ihsext-inductions
  ;;                                    acl2::ihsext-recursive-redefs)
  ;;                                   (acl2::logcdr-natp
  ;;                                    logxor-of-naturals)))))

  ;; (defthm bit-logand-1
  ;;   (implies (bitp a)
  ;;            (equal (logand 1 a)
  ;;                   a))
  ;;   :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
  ;;                                      acl2::ihsext-recursive-redefs))))

  (defthm b-xor-a-a-b
    (equal (b-xor a (b-xor a b))
           (acl2::bfix b))
    :hints(("Goal" :in-theory (enable b-xor acl2::bfix))))

  (defthm b-and-of-xor-not
    (equal (b-and (b-xor (b-not a) b)
                        (b-xor a b))
           0)
    :hints(("Goal" :in-theory (enable b-and b-xor b-not))))

  (def-gate-simp aignet-gate-simp-level1
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((when (int= (id->type (lit-id lit1) aignet) (const-type)))
          (mv (if (int= (lit-neg lit1) 1)
                  lit2    ;; neutrality
                0)
              nil lit1 lit2))       ;; boundedness
         ((when (int= (id->type (lit-id lit2) aignet) (const-type)))
          (mv (if (int= (lit-neg lit2) 1)
                  lit1    ;; neutrality
                0)
              nil lit1 lit2))       ;; boundedness
         ((when (= lit1 lit2))
          (mv lit1 nil lit1 lit2))       ;; idempotence
         ((when (= lit1 (lit-negate lit2)))
          (mv 0 nil lit1 lit2)))         ;; contradiction
      (mv nil nil lit1 lit2))
    :eval-hints (("Goal" :in-theory (e/d* (eval-and-of-lits
                                           id-eval lit-eval
                                           equal-of-mk-lit
                                           acl2::arith-equiv-forwarding)))
                 ;; (and stable-under-simplificationp
                 ;;      '(:in-theory (e/d (bits-equal-of-logxor
                 ;;                         bits-equal-of-logand)
                 ;;                        (acl2::logand-with-bitmask))))
                 ))


  (defund aignet-gate-simp-l2-step1-cond (a b c)
    (or (= a c) (= b c)))




  (defthm id-eval-0-when-aignet-well-formedp
    (implies (aignet-well-formedp aignet)
             (equal (id-eval 0 in-vals reg-vals aignet)
                    0))
    :hints(("Goal" :in-theory (enable id-eval))))

  (defthm lit-eval-of-constants
    (implies (aignet-well-formedp aignet)
             (and (equal (lit-eval 0 in-vals reg-vals aignet)
                         0)
                  (equal (lit-eval 1 in-vals reg-vals aignet)
                         1)))
    :hints(("Goal" :in-theory (enable lit-eval))))

  ;; (local (Defthm lit-eval-of-mk-lit
  ;;          (equal (lit-eval (mk-lit (lit-id lit) neg) in-vals reg-vals aignet)
  ;;                 (b-xor (b-xor neg (lit-neg lit))
  ;;                        (lit-eval lit in-vals reg-vals aignet)))
  ;;          :hints(("Goal" :in-theory (enable lit-eval)))))

  (def-gate-simp aignet-gate-simp-l2-step1
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (id1 (lit-id lit1))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (lit2b (lit-negate lit2))
         (res (or (and (mbe :logic (aignet-gate-simp-l2-step1-cond a b lit2b)
                            :exec (or (= a lit2b)
                                      (= b lit2b)))
                       (if (int= (lit-neg lit1) 1)
                           lit2 ;; subsumption1
                         0))    ;; contradiction1
                  (and (int= (lit-neg lit1) 0)
                       (mbe :logic (aignet-gate-simp-l2-step1-cond a b lit2)
                            :exec (or (= a lit2) (= b lit2)))
                       lit1))))  ;; idempotence1
      (mv res nil lit1 lit2))
    :guard (int= (id->type (lit-id lit1) aignet) (gate-type))
    ;; (and (< (id-val (lit-id lit1)) (nfix (num-nodes aignet)))
    ;;      (< (id-val (lit-id lit2)) (nfix (num-nodes aignet)))
    ;;      (lit-gatep lit1))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-l2-step1-cond)))
    :eval-hints (("goal" :in-theory (e/d (eval-and-of-lits lit-eval
                                          equal-of-mk-lit)))
                 (and stable-under-simplificationp
                      '(:expand ((id-eval (lit-id lit1) in-vals reg-vals aignet)
                                 (:free (a b c) (aignet-gate-simp-l2-step1-cond a b
                                                                             c)))))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor b-and b-not
                                                     equal-1-to-bitp))))))

  (defund aignet-gate-simp-l2-step2-cond (a b cb db)
    (or (= a cb)
        (= a db)
        (= b cb)
        (= b db)))


  (local (defthmd lit-eval-open
           (equal (lit-eval lit in-vals reg-vals aignet)
                  (b-xor (lit-neg lit)
                         (id-eval (lit-id lit) in-vals reg-vals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))


  (local (defthmd equal-0-of-lit-neg
           (equal (equal (lit-neg x) 0)
                  (not (equal (lit-neg x) 1)))))

  (local (defthmd equal-0-of-lit-neg-2
           (equal (equal 0 (lit-neg x))
                  (not (equal (lit-neg x) 1)))))

  (local (defun rewriting-negative-literal-equiv (equiv x y mfc state)
           (declare (xargs :mode :program :stobjs state))
           (or (acl2::rewriting-negative-literal-fn `(,equiv ,x ,y) mfc state)
               (acl2::rewriting-negative-literal-fn `(,equiv ,y ,x) mfc state))))

  (local (defthmd equal-of-mk-lit-neg
           (implies (syntaxp
                     (rewriting-negative-literal-equiv
                      'equal x `(mk-lit$inline ,id ,neg) mfc state))
                    (equal (equal x (mk-lit id neg))
                           (and (litp x)
                                (equal (lit-id x) (id-fix id))
                                (equal (lit-neg x) (bfix neg)))))
           :hints(("Goal" :in-theory (enable equal-of-mk-lit)))))

  (local (defthm bfix-of-lit-neg
           (Equal (bfix (lit-neg x)) (lit-neg x))))

  ;; (defund and* (x y) (and x y))
  ;; (defthmd equal-of-mk-lit-abbrev
  ;;   (equal (equal a (mk-lit id neg))
  ;;          (and* (litp a)
  ;;                (and* (equal (id-val (lit-id a)) (id-val id))
  ;;                      (equal (lit-neg a) (bfix neg)))))
  ;;   :hints(("Goal" :in-theory (enable equal-of-mk-lit and*))))

  ;; (defthm bitp-norm-equal-to-1
  ;;   (implies (bitp x)
  ;;            (equal (equal x 0)
  ;;                   (equal (b-not x) 1)))
  ;;   :hints(("Goal" :in-theory (enable bitp b-not))))

  (def-gate-simp aignet-gate-simp-l2-step2
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (id1 (lit-id lit1))
         (id2 (lit-id lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         (negp1 (int= (lit-neg lit1) 1))
         (negp2 (int= (lit-neg lit2) 1))
         (cb (lit-negate c))
         (db (lit-negate d))
         (res (and (int= 0 (b-and (lit-neg lit1) (lit-neg lit2)))
                   (mbe :logic (aignet-gate-simp-l2-step2-cond a b cb db)
                        :exec (or (= a cb)
                                  (= a db)
                                  (= b cb)
                                  (= b db)))
                   (cond (negp1 lit2)   ;; subsumption2
                         (negp2 lit1)   ;; subsumption2
                         (t     0)))))  ;; contradiction2
      (mv res nil lit1 lit2))
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-l2-step2-cond)))
    :fanin-hints (("goal" :in-theory nil)
                  (and stable-under-simplificationp
                       '(:in-theory (enable))))
    :eval-hints (("goal" :in-theory nil)
                 ;; (and stable-under-simplificationp
                 ;;      '(:in-theory (e/d (eval-and-of-lits
                 ;;                         equal-of-mk-lit))))
                 (and stable-under-simplificationp
                      '(:expand (;; (lit-eval lit1 in-vals reg-vals aignet)
                                 ;; (lit-eval lit2 in-vals reg-vals aignet)
                                 (id-eval (lit-id lit1) in-vals reg-vals aignet)
                                 (id-eval (lit-id lit2) in-vals reg-vals aignet)
                                 (:free (a b cb db)
                                  (aignet-gate-simp-l2-step2-cond a b cb
                                                                  db)))
                        :in-theory (e/d (lit-eval-open
                                         eval-and-of-lits
                                         equal-of-mk-lit-neg
                                         )
                                        (id-eval))))
                 ;; (and stable-under-simplificationp
                 ;;      '(:in-theory (e/d (equal-of-mk-lit)
                 ;;                        (id-eval))))
                 ;; (and stable-under-simplificationp
                 ;;      '(:by nil))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor
                                         b-and
                                         b-not
                                         equal-0-of-lit-neg-2
                                         equal-0-of-lit-neg
                                         ))
                        :bdd (:vars nil)))))

  (defund aignet-gate-simp-l2-step3-cond (a b c d cb db)
    (or (and (= a d) (= b cb))
        (and (= a c) (= b db))))


  (def-gate-simp aignet-gate-simp-l2-step3
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((unless (int= 1 (b-and (lit-neg lit1)
                                 (lit-neg lit2))))
          (mv nil nil lit1 lit2))
         (id1 (lit-id lit1))
         (id2 (lit-id lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         (cb (lit-negate c))
         (db (lit-negate d))
         ((when (mbe :logic (aignet-gate-simp-l2-step3-cond a b c d cb db)
                     :exec (or (and (= a d) (= b cb))
                               (and (= a c) (= b db)))))
          (mv (lit-negate a) nil lit1 lit2))
         ((when (mbe :logic (aignet-gate-simp-l2-step3-cond b a c d cb db)
                     :exec (or (and (= b d) (= a cb))
                               (and (= b c) (= a db)))))
          (mv (lit-negate b) nil lit1 lit2)))
      (mv nil nil lit1 lit2))
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-l2-step3-cond)))
    :eval-hints (;; ("goal" :in-theory (e/d (eval-and-of-lits
                 ;;                           equal-of-mk-lit-neg)
                 ;;                         (id-eval)))
                 (and stable-under-simplificationp
                      '(:expand (;; (lit-eval lit1 in-vals reg-vals aignet)
                                 ;; (lit-eval lit2 in-vals reg-vals aignet)
                                 (id-eval (lit-id lit1) in-vals reg-vals aignet)
                                 (id-eval (lit-id lit2) in-vals reg-vals aignet)
                                 (:free (a b c d cb db)
                                  (aignet-gate-simp-l2-step3-cond a b c d cb
                                                                  db)))
                        :in-theory (e/d (lit-eval-open
                                         eval-and-of-lits
                                         equal-of-mk-lit-neg)
                                        (id-eval))))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor
                                         b-and
                                         b-not
                                         acl2::bfix
                                         equal-0-of-lit-neg
                                         equal-0-of-lit-neg-2)
                                        (id-eval))
                        :bdd (:vars nil)))))

  (def-gate-simp aignet-gate-simp-level2
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((mv extra & & &)
          (aignet-gate-simp-l2-step1 lit1 lit2 aignet))
         ((when extra) (mv extra nil lit1 lit2))
         ((when (not both)) (mv nil nil lit1 lit2))
         ((mv extra & & &)
          (aignet-gate-simp-l2-step2 lit1 lit2 aignet))
         ((when extra) (mv extra nil lit1 lit2))
         ((mv extra & & &)
          (aignet-gate-simp-l2-step3 lit1 lit2 aignet))
         ((when extra) (mv extra nil lit1 lit2)))
      (mv nil nil lit1 lit2))
    :extra-args (both)
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (implies both
                         (int= (id->type (lit-id lit2) aignet) (gate-type))))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (implies both
                    (int= (id->type (lit-id lit2) aignet) (gate-type)))))

  (defund aignet-gate-simp-level3-cond1.1 (ab c d)
    (or (= ab c) (= ab d)))

  (defund aignet-gate-simp-level3-cond1 (ab c d lit2 negp2 both)
    (or (= ab lit2)                                     ;; substitution1
        (and both (not negp2)
             (aignet-gate-simp-level3-cond1.1 ab c d))))

  (defund aignet-gate-simp-level3-cond2 (a b cd)
    (or (= cd b) (= cd a)))

  (defthm lit-eval-of-mk-lit-opposite
    (implies (equal b (b-not (lit-neg lit)))
             (equal (lit-eval (mk-lit (lit-id lit) b) in-vals reg-vals aignet)
                    (b-not (lit-eval lit in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (enable b-not b-xor lit-eval
                                      equal-1-to-bitp))))

(def-gate-simp aignet-gate-simp-level3
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (id1 (lit-id lit1))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         ((mv c d) (if both
                       (let ((id2 (lit-id lit2)))
                         (mv (gate-id->fanin0 id2 aignet)
                             (gate-id->fanin1 id2 aignet)))
                     (mv nil nil)))
         (negp1 (int= (lit-neg lit1) 1))
         (negp2 (int= (lit-neg lit2) 1))

         ((when (and negp1
                     (mbe :logic (aignet-gate-simp-level3-cond1 b c d lit2 negp2 both)
                          :exec
                          (or (= b lit2)                                      ;; substitution1
                              (and both (not negp2) (or (= b c) (= b d))))))) ;; substitution2
          (mv nil t (lit-negate a) lit2))
         ((when (and negp1
                     (mbe :logic (aignet-gate-simp-level3-cond1 a c d lit2 negp2 both)
                          :exec
                          (or (= a lit2)                                      ;; substitution1
                              (and both (not negp2) (or (= a c) (= a d))))))) ;; substitution2
          (mv nil t (lit-negate b) lit2))
         ((when (and both (int= 1 (b-and (lit-neg lit2) (b-not (lit-neg lit1))))
                     (mbe :logic (aignet-gate-simp-level3-cond2 a b c)
                          :exec (or (= c b) (= c a))))) ;; substitution2
          (mv nil t (lit-negate d) lit1))
         ((when  (and both (int= 1 (b-and (lit-neg lit2) (b-not (lit-neg lit1))))
                      (mbe :logic (aignet-gate-simp-level3-cond2 a b d)
                           :exec (or (= d b) (= d a))))) ;; substitution2
          (mv nil t (lit-negate c) lit1)))
      (mv nil nil lit1 lit2))
    :extra-args (both)
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (implies both
                         (int= (id->type (lit-id lit2) aignet) (gate-type))))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (implies both
                    (int= (id->type (lit-id lit2) aignet) (gate-type))))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-level3-cond1
                                             aignet-gate-simp-level3-cond1.1
                                             aignet-gate-simp-level3-cond2)))
    :eval-hints (;; ("goal" :in-theory (e/d (eval-and-of-lits
                 ;;                          equal-of-mk-lit)))
                 (and stable-under-simplificationp
                      '(:expand ((lit-eval lit1 in-vals reg-vals aignet)
                                 (lit-eval lit2 in-vals reg-vals aignet)
                                 (id-eval (lit-id lit1) in-vals reg-vals aignet)
                                 (id-eval (lit-id lit2) in-vals reg-vals aignet))
                        :in-theory (enable aignet-gate-simp-level3-cond1
                                           aignet-gate-simp-level3-cond1.1
                                           aignet-gate-simp-level3-cond2
                                           equal-of-mk-lit-neg
                                           eval-and-of-lits)))

                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor b-and b-not
                                                     equal-1-to-bitp
                                                     equal-0-of-lit-neg
                                                     equal-0-of-lit-neg-2)
                                        (id-eval))
                        :bdd (:vars nil)))))

  (defund aignet-gate-simp-level4-cond (ab c d)
    (or (= ab c) (= ab d)))

  (def-gate-simp aignet-gate-simp-level4
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((when (or (int= (lit-neg lit1) 1)
                    (int= (lit-neg lit2) 1)))
          (mv nil nil lit1 lit2))
         (id1 (lit-id lit1))
         (id2 (lit-id lit2))
         (a (gate-id->fanin0 id1 aignet))
         (b (gate-id->fanin1 id1 aignet))
         (c (gate-id->fanin0 id2 aignet))
         (d (gate-id->fanin1 id2 aignet))
         ;; For each equality, we could either reduce the left or right gate.
         ;; Maybe experiment with this.  Atm. we'll prefer to reduce the
         ;; higher-numbered gate, lit1.
         ((when (mbe :logic (aignet-gate-simp-level4-cond a c d)
                     :exec (or (= a c) (= a d))))
          (mv nil t b lit2))
         ((when (mbe :logic (aignet-gate-simp-level4-cond b c d)
                     :exec (or (= b c) (= b d))))
          (mv nil t a lit2)))
      (mv nil nil lit1 lit2))
    :guard (and (int= (id->type (lit-id lit1) aignet) (gate-type))
                (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :reqs ((int= (id->type (lit-id lit1) aignet) (gate-type))
           (int= (id->type (lit-id lit2) aignet) (gate-type)))
    :guard-hints (("goal" :in-theory (enable aignet-gate-simp-level4-cond)))
    :eval-hints (("goal" :in-theory (e/d (eval-and-of-lits
                                          equal-of-mk-lit)))
                 (and stable-under-simplificationp
                      '(:expand ((lit-eval lit1 in-vals reg-vals aignet)
                                 (lit-eval lit2 in-vals reg-vals aignet)
                                 (id-eval (lit-id lit1) in-vals reg-vals aignet)
                                 (id-eval (lit-id lit2) in-vals reg-vals aignet))
                        :in-theory (enable aignet-gate-simp-level4-cond)))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (b-xor b-and b-not
                                                     equal-1-to-bitp)
                                        (id-eval))))))

  (def-gate-simp aignet-gate-simp-pass
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         (level (lnfix level))
         ((when (< level 1))
          (mv nil nil lit1 lit2))

         ((mv level1-result & & &) (aignet-gate-simp-level1 lit1 lit2 aignet))
         ((when level1-result)
          (mv level1-result nil lit1 lit2))

         ((mv lit1 lit2 both neither)
          (aignet-gate-simp-order lit1 lit2 aignet))

         ((when (or (< level 2) neither))
          (mv nil nil lit1 lit2))

         ;; O2.
         ;; Only one direction possible since lit2 < lit1.
         ((mv level2-result & & &) (aignet-gate-simp-level2 lit1 lit2 both aignet))
         ((when level2-result)
          (mv level2-result nil lit1 lit2))

         ((when (< level 3))
          (mv nil nil lit1 lit2))


         ;; O3.
         ((mv & succ nlit1 nlit2)
          (aignet-gate-simp-level3 lit1 lit2 both aignet))
         ((when succ)
          (mv nil succ nlit1 nlit2))

         ((when (or (< level 4) (not both)))
          (mv nil nil lit1 lit2))

         ;; O4.
         ((mv & succ nlit1 nlit2)
          (aignet-gate-simp-level4 lit1 lit2 aignet))
         ((when succ)
          (mv nil succ nlit1 nlit2)))

      (mv nil nil lit1 lit2))

    :extra-args (level)
    :guard (natp level)
    :fanin-hints (("goal" :cases ((mv-nth 2 (aignet-gate-simp-order lit1 lit2 aignet)))))
    :measure-hints (("goal" :use ((:instance
                                   two-id-measure-of-aignet-gate-simp-order))
                     :in-theory (disable
                                 two-id-measure-of-aignet-gate-simp-order))))

  (local
   (set-default-hints
    '((and (equal id (acl2::parse-clause-id "goal"))
           '(:induct (aignet-gate-simp lit1 lit2 level aignet)
             :do-not-induct t
             :in-theory (disable (:definition aignet-gate-simp))
             :expand ((:free (lit2) (aignet-gate-simp lit1 lit2 level aignet))
                      (:free (lit1) (aignet-gate-simp lit1 lit2 level aignet))))))))

  (def-gate-simp aignet-gate-simp
    (b* ((lit1 (lit-fix lit1))
         (lit2 (lit-fix lit2))
         ((mv exists reduced nlit1 nlit2)
          (aignet-gate-simp-pass lit1 lit2 level aignet))
         ((when exists)
          (mv exists nil nlit1 nlit2))
         ((unless reduced)
          (mv nil nil nlit1 nlit2))
         ;; check measure
         ((unless (mbt (o< (two-id-measure (lit-id nlit1) (lit-id nlit2))
                           (two-id-measure (lit-id lit1) (lit-id lit2)))))
          (mv nil nil nlit1 nlit2)))
      (aignet-gate-simp nlit1 nlit2 level aignet))

    :extra-args (level)
    :guard (natp level)
    :xargs (:measure (two-id-measure (lit-id lit1) (lit-id lit2))
            :hints (("goal" :in-theory (enable two-id-measure)))
            :guard-hints (("goal" :no-thanks t)))
    :frame-hints (("goal" :induct (aignet-gate-simp lit1 lit2 level aignet)
                   :in-theory (disable (:definition aignet-gate-simp))
                   :do-not-induct t
                   :expand ((:free (lit2) (aignet-gate-simp lit1 lit2 level aignet))
                            (:free (lit1) (aignet-gate-simp lit1 lit2 level aignet)))))
    :skip-measure t))

(defsection aignet-addr-combine
  ;; Combining two integers into one (generally fixnum) key for hashing:
  ;; This is the same as hl-addr-combine (in books/system/hl-addr-combine.lisp)
  ;; but we don't need to prove anything about it here beyond verifying
  ;; guards (which are simpler here because we don't need the MBE).

  #!ACL2
  (local (defthm +-of-logcons-with-cin
           (implies (bitp cin)
                    (equal (+ cin
                              (logcons b1 r1)
                              (logcons b2 r2))
                           (logcons (b-xor cin (b-xor b1 b2))
                                    (+ (b-ior (b-and cin b1)
                                              (b-ior (b-and cin b2)
                                                     (b-and b1 b2)))
                                       (ifix r1)
                                       (ifix r2)))))
           :hints(("Goal" :in-theory (enable logcons b-ior b-and b-xor b-not)))))
  (local
   (defthm logior-to-plus
     (implies (and (natp a)
                   (integerp b)
                   (natp n)
                   (< a (ash 1 n)))
              (equal (logior a (ash b n))
                     (+ a (ash b n))))
     :hints(("Goal" :in-theory (e/d* (acl2::ihsext-inductions)
; (acl2::ash-1-removal)
                                     )
             :induct (logbitp n a)
             :expand ((:free (b) (ash b n))
                      (:free (b) (logior a b))))
            (and stable-under-simplificationp
                 '(:use ((:instance acl2::+-of-logcons-with-cin
                          (acl2::b1 (acl2::logcar a))
                          (acl2::r1 (acl2::logcdr a))
                          (acl2::b2 0)
                          (acl2::r2 (ash b (+ -1 n)))
                          (acl2::cin 0))))))))

  (local (defthm floor-of-1
           (implies (natp n)
                    (equal (floor n 1) n))
           :hints(("Goal" :in-theory (enable floor)))))

  (defund aignet-addr-combine (a b)
    (declare (xargs :guard (and (natp a) (natp b))
                    :verify-guards nil))
    (if (and (< a 1073741824)
             (< b 1073741824))
        ;; Optimized version of the small case
        (the (signed-byte 61)
          (- (the (signed-byte 61)
               (logior (the (signed-byte 61)
                         (ash (the (signed-byte 31) a) 30))
                       (the (signed-byte 31) b)))))
      ;; Large case.
      (- (+ (let* ((a+b   (+ a b))
                   (a+b+1 (+ 1 a+b)))
              (if (= (logand a+b 1) 0)
                  (* (ash a+b -1) a+b+1)
                (* a+b (ash a+b+1 -1))))
            b)
         576460752840294399)))

  (local (in-theory (enable aignet-addr-combine)))

  (verify-guards aignet-addr-combine
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable ash))))
    :otf-flg t))

(defsection strash
  (defstobj strash
    (strashtab :type (hash-table eql))
    :inline t)

  ;; returns (mv exists key id).
  ;; exists implies that id is a gate with the two specified fanins.
  (definlined strash-lookup (lit1 lit2 strash aignet)
    (declare (xargs :stobjs (aignet strash)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp lit1 aignet)
                                (aignet-litp lit2 aignet))))
    (b* ((key (aignet-addr-combine (lit-val lit1) (lit-val lit2)))
         (id (strashtab-get key strash))
         ((unless (and id
                       (aignet-idp id aignet)
                       (int= (id->type id aignet) (gate-type))
                       (int= (gate-id->fanin0 id aignet) lit1)
                       (int= (gate-id->fanin1 id aignet) lit2)))
          (mv nil key 0)))
      (mv t key id)))

  (local (in-theory (enable strash-lookup)))

  (defthm strash-lookup-correct
    (b* (((mv found & id) (strash-lookup lit1 lit2 strash aignet)))
      (implies found
               (and (aignet-idp id aignet)
                    (let ((node (nth-node id (nth *nodesi* aignet))))
                      (and (equal (node->type node) (gate-type))
                           (equal (gate-node->fanin0 node) lit1)
                           (equal (gate-node->fanin1 node) lit2)))))))

  (defthm strash-lookup-id-type
    (idp (mv-nth 2 (strash-lookup lit1 lit2 strash aignet)))
    :rule-classes (:rewrite :type-prescription))

  (defthm strash-lookup-key-type
    (acl2-numberp (mv-nth 1 (strash-lookup lit1 lit2 strash aignet)))
    :rule-classes :type-prescription))

(defsection aignet-add-simp-gate

  (defsection gatesimp
    (local (in-theory (disable len-update-nth)))
    (local (in-theory (enable* acl2::ihsext-recursive-redefs
                               acl2::ihsext-bounds-thms
                               nfix natp)))

    (definlined gatesimp-level (gatesimp)
      (declare (Xargs :guard (natp gatesimp)))
      (ash (lnfix gatesimp) -1))

    (defthm natp-gatesimp-level
      (natp (gatesimp-level gatesimp))
      :hints(("Goal" :in-theory (enable gatesimp-level)))
      :rule-classes :type-prescription)

    (definlined gatesimp-hashp (gatesimp)
      (declare (Xargs :guard (natp gatesimp)))
      (logbitp 0 gatesimp))

    (definlined mk-gatesimp (level hashp)
      (declare (xargs :guard (natp level)))
      (logior (ash (lnfix level) 1) (if hashp 1 0)))

    (defthm gatesimp-level-of-mk-gatesimp
      (equal (gatesimp-level (mk-gatesimp level hashp))
             (nfix level))
      :hints(("Goal" :in-theory (enable gatesimp-level mk-gatesimp))))

    (defthm gatesimp-hashp-of-mk-gatesimp
      (equal (gatesimp-hashp (mk-gatesimp level hashp))
             (if hashp
                 t
               nil))
      :hints(("Goal" :in-theory (enable gatesimp-hashp mk-gatesimp))))

    (defthm natp-mk-gatesimp
      (natp (mk-gatesimp level hashp))
      :hints(("Goal" :in-theory (enable mk-gatesimp)))
      :rule-classes :type-prescription))




  (defund aignet-add-simp-gate (lit1 lit2 strash gatesimp aignet)
    (declare (type (integer 0 *) lit1)
             (type (integer 0 *) lit2)
             (type (integer 0 *) gatesimp)
             (xargs :stobjs (aignet strash)
                    :guard-debug t
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp lit1 aignet)
                                (aignet-litp lit2 aignet))))
    (b* ((lit1 (aignet-lit-fix lit1 aignet))
         (lit2 (aignet-lit-fix lit2 aignet))
         (gatesimp (lnfix gatesimp))
         ((mv existing & lit1 lit2)
          (aignet-gate-simp lit1 lit2 (gatesimp-level gatesimp) aignet))
         ((when existing)
          (mv existing strash aignet))
         ((when (not (gatesimp-hashp gatesimp)))
          (b* (((mv lit aignet)
                (aignet-add-gate lit1 lit2 aignet)))
            (mv lit strash aignet)))
         ((mv found key id) (strash-lookup lit1 lit2 strash aignet))
         ((when found)
          (mv (mk-lit id 0) strash aignet))
         ((mv lit aignet)
          (aignet-add-gate lit1 lit2 aignet))
         (strash (strashtab-put key (lit-id lit) strash)))
      (mv lit strash aignet)))


  (local (in-theory (enable aignet-add-simp-gate)))

  (defthm litp-of-aignet-add-simp-gate
    (litp (mv-nth 0 (aignet-add-simp-gate lit1 lit2 strash gatesimp aignet))))

  (defmvtypes aignet-add-simp-gate (natp nil nil))

  (defcong lit-equiv equal (aignet-add-simp-gate lit1 lit2 strash gatesimp aignet) 1)
  (defcong lit-equiv equal (aignet-add-simp-gate lit1 lit2 strash gatesimp aignet) 2)

  (def-aignet-frame aignet-add-simp-gate)
  (def-aignet-preservation-thms aignet-add-simp-gate)

  ;; (defthm aignet-add-simp-gate-of-aignet-fix
  ;;   (equal (aignet-add-simp-gate lit1 lit2 strash gatesimp (aignet-fix aignet))
  ;;          (aignet-add-simp-gate lit1 lit2 strash gatesimp aignet)))

  (local (in-theory (disable aignet-add-gate)))

  (defthm num-nodes-of-aignet-add-simp-gate-nfix
    (<= (nfix (nth *num-nodes* aignet))
        (nfix (nth *num-nodes* (mv-nth 2 (aignet-add-simp-gate lit1 lit2 strash
                                                           gatesimp aignet)))))
    :rule-classes :linear)

  ;; (defthm lit-id-in-bounds-of-aignet-add-simp-gate
  ;;   (implies (and (aignet-well-formedp aignet)
  ;;                 (strash-ok strash aignet)
  ;;                 (aignet-litp lit1 aignet)
  ;;                 (aignet-litp lit2 aignet))
  ;;            (b* (((mv lit & aignet)
  ;;                  (aignet-add-simp-gate lit1 lit2 strash gatesimp aignet)))
  ;;              (< (id-val (lit-id lit)) (nfix (nth *num-nodes* aignet)))))
  ;;   :rule-classes (:rewrite
  ;;                  (:linear :trigger-terms
  ;;                   ((id-val (lit-id (mv-nth 0 (aignet-add-simp-gate lit1 lit2 strash
  ;;                                                                 gatesimp
  ;;                                                                 aignet))))))))

  (defthm aignet-litp-of-aignet-add-simp-gate
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet)
                   (aignet-add-simp-gate lit1 lit2 strash gatesimp aignet)))
               (aignet-litp lit aignet)))
    :hints(("Goal" :in-theory (disable aignet-add-gate-new-lit))))


  (local (defthmd equal-1-to-bitp
           (implies (and (not (equal x 0))
                         (bitp x))
                    (equal (equal x 1) t))
           :hints(("Goal" :in-theory (enable bitp)))))

  (local (defthm lit-eval-of-mk-lit-split
           (equal (lit-eval (mk-lit (lit-id lit) neg) in-vals reg-vals aignet)
                  (b-xor (b-xor neg (lit-neg lit))
                               (lit-eval lit in-vals reg-vals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval b-xor)))))

  (local (defthm lit-eval-of-mk-lit-consts
           (and (equal (lit-eval (mk-lit id 0) in-vals reg-vals aignet)
                       (id-eval id in-vals reg-vals aignet))
                (equal (lit-eval (mk-lit id 1) in-vals reg-vals aignet)
                       (b-not (id-eval id in-vals reg-vals aignet))))
           :hints(("Goal" :in-theory (enable lit-eval b-xor b-not)))))
  (defthm id-eval-of-strash-lookup
    (b* (((mv ok & id)
          (strash-lookup lit1 lit2 strash aignet)))
      (implies (and ok (aignet-well-formedp aignet))
               (equal (id-eval id in-vals reg-vals aignet)
                      (eval-and-of-lits lit1 lit2 in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (enable eval-and-of-lits id-eval))))


  (defthm lit-eval-of-aignet-add-simp-gate
    (b* (((mv res & newaignet)
          (aignet-add-simp-gate lit1 lit2 strash gatesimp aignet)))
      (implies (aignet-well-formedp aignet)
               (equal (lit-eval res in-vals reg-vals newaignet)
                      (eval-and-of-lits
                       lit1 lit2 in-vals reg-vals aignet))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (; id-eval
                                    eval-and-of-lits)
                                   (id-eval-of-aignet-gate-simp))
                   :use ((:instance id-eval-of-aignet-gate-simp
                          (level (gatesimp-level (nfix gatesimp)))
                          (lit1 (aignet-lit-fix lit1 aignet))
                          (lit2 (aignet-lit-fix lit2 aignet))))))
            (and stable-under-simplificationp
                 '(:expand ((:free (x y)
                             (id-eval (cdr (hons-assoc-equal x y)) in-vals reg-vals
                                      aignet))
                            (:free (aignet)
                             (id-eval (to-id (nth *num-nodes* aignet)) in-vals reg-vals
                                      aignet)))))))

  (defthm aignet-add-simp-gate-num-nodes-increases
    (<= (nfix (nth *num-nodes* aignet))
        (nfix (nth *num-nodes* (mv-nth 2 (aignet-add-simp-gate
                                         lit1 lit2 strash gatesimp aignet)))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-add-simp-gate-num-nodes-increases-natp
    (implies (natp (nth *num-nodes* aignet))
             (<= (nth *num-nodes* aignet)
                 (nth *num-nodes* (mv-nth 2 (aignet-add-simp-gate
                                            lit1 lit2 strash gatesimp aignet)))))
    :rule-classes (:rewrite :linear))

  (defthm aignet-add-simp-gate-num-nodes-natp
    (implies (natp (nth *num-nodes* aignet))
             (natp (nth *num-nodes* (mv-nth 2 (aignet-add-simp-gate
                                              lit1 lit2 strash gatesimp aignet)))))
    :rule-classes (:rewrite :type-prescription))


  (defund aignet-add-simp-gate-nohash (lit1 lit2 level aignet)
    (declare (type (integer 0 *) lit1)
             (type (integer 0 *) lit2)
             (type (integer 0 *) level)
             (xargs :guard (and (aignet-well-formedp aignet)
                                (aignet-litp lit1 aignet)
                                (aignet-litp lit2 aignet))
                    :stobjs (aignet)))
    (b* ((lit1 (aignet-lit-fix lit1 aignet))
         (lit2 (aignet-lit-fix lit2 aignet))
         (level (lnfix level))
         ((mv existing & lit1 lit2)
          (aignet-gate-simp lit1 lit2 level aignet))
         ((when existing)
          (mv existing aignet)))
      (aignet-add-gate lit1 lit2 aignet)))

  (defthm aignet-add-simp-gate-nohash-is-aignet-add-simp-gate
    (equal (aignet-add-simp-gate-nohash lit1 lit2 level aignet)
           (b* (((mv lit & aignet)
                 (aignet-add-simp-gate lit1 lit2 nil (mk-gatesimp level nil) aignet)))
             (mv lit aignet)))
    :hints(("Goal" :in-theory (enable aignet-add-simp-gate-nohash
                                      aignet-add-gate
                                      aignet-add-gate1)))))

(defsection litarr
  (acl2::def-1d-arr :arrname litarr
                    :slotname lit
                    :pred litp
                    :fix lit-fix$inline
                    :type-decl (unsigned-byte 32)
                    :default-val 0
                    :rename ((get-lit . get-lit_)
                             (set-lit . set-lit_)))

  (definline get-lit (n litarr)
    (declare (xargs :stobjs litarr
                    :guard (and (natp n)
                                (< n (lits-length litarr)))
                    :guard-hints ('(:in-theory (enable nth-lit)))))
    (mbe :logic (non-exec (nth-lit n litarr))
         :exec (get-lit_ n litarr)))

  (definline set-lit (n v litarr)
    (declare (xargs :stobjs litarr
                    :guard (and (natp n)
                                (< n (lits-length litarr))
                                (litp v))
                    :guard-hints ('(:in-theory (enable update-nth-lit)))))
    (mbe :logic (non-exec (update-nth-lit n (lit-fix v) litarr))
         :exec (if (< (the (integer 0 *) v) (expt 2 32))
                   (set-lit_ n v litarr)
                 (ec-call (set-lit_ n v litarr)))))

  (local (in-theory (enable acl2::aignetp)))

  (defun litarr-sizedp (litarr aignet)
    (declare (xargs :stobjs (litarr aignet)
                    :guard-hints ('(:in-theory (enable memo-tablep)))))
    (mbe :logic (non-exec (memo-tablep litarr aignet))
         :exec (<= (num-nodes aignet) (lits-length litarr))))

  (defun litarr-id-in-bounds (id litarr)
    (declare (xargs :guard (idp id)
                    :stobjs litarr
                    :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
    (mbe :logic (non-exec (id-in-bounds id litarr))
         :exec (< (id-val id) (lits-length litarr))))

  (defun litarr-iterator-in-bounds (n litarr)
    (declare (xargs :guard (natp n)
                    :stobjs litarr
                    :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
    (mbe :logic (non-exec (iterator-in-bounds n litarr))
         :exec (<= (nfix n) (lits-length litarr))))


  (local (in-theory (enable nth-lit update-nth-lit)))

  (local (in-theory (enable nth-lit nth-id
                            update-nth-lit update-nth-id
                            id-in-bounds)))

  ;; using a litarr as various types of mapping
  (definline get-id->lit (id litarr)
    (declare (type (integer 0 *) id)
             (xargs :stobjs litarr
                    :guard (and (idp id)
                                (litarr-id-in-bounds id litarr))))
    (get-lit (id-val id) litarr))

  (definline set-id->lit (id lit litarr)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) lit)
             (xargs :stobjs litarr
                    :guard (and (idp id) (litp lit)
                                (litarr-id-in-bounds id litarr))))
    (set-lit (id-val id) lit litarr))

  (local (in-theory (enable resize-list)))

  (definline litarr-clear (litarr)
    (declare (xargs :stobjs litarr
                    :guard-hints ('(:expand ((len litarr)
                                             (len (cdr litarr)))
                                    :in-theory (enable nth update-nth)))))
    (mbe :logic (non-exec nil)
         :exec (resize-lits 0 litarr)))

  (acl2::def-universal-equiv
   lits-equiv
   :qvars (i)
   :equiv-terms ((lit-equiv (nth i x))))

  (defcong lits-equiv lit-equiv (nth i x) 2
    :hints ('(:use ((:instance lits-equiv-necc
                     (acl2::y x-equiv))))))
  (defcong lits-equiv lits-equiv (update-nth i v x) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable lits-equiv-necc)))))
  (defcong lit-equiv lits-equiv (update-nth i v x) 2
        :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable lits-equiv-necc)))))

  (local (in-theory (enable nth-lit update-nth-lit)))

  (defcong lits-equiv lit-equiv (nth-lit i x) 2)
  (defcong lits-equiv lits-equiv (update-nth-lit i v x) 3)
  (defcong lit-equiv lits-equiv (update-nth-lit i v x) 2))

(defsection idarr
  (acl2::def-1d-arr :arrname idarr
                    :slotname id
                    :pred idp
                    :fix id-fix$inline
                    :type-decl (unsigned-byte 32)
                    :default-val 0
                    :rename ((get-id . get-id_)
                             (set-id . set-id_)))

  (definline get-id (n idarr)
    (declare (xargs :stobjs idarr
                    :guard (and (natp n)
                                (< n (ids-length idarr)))
                    :guard-hints ('(:in-theory (enable nth-id)))))
    (mbe :logic (non-exec (nth-id n idarr))
         :exec (get-id_ n idarr)))

  (definline set-id (n v idarr)
    (declare (xargs :stobjs idarr
                    :guard (and (natp n)
                                (< n (ids-length idarr))
                                (idp v))
                    :guard-hints ('(:in-theory (enable update-nth-id)))))
    (mbe :logic (non-exec (update-nth-id n (id-fix v) idarr))
         :exec (if (< (the (integer 0 *) v) (expt 2 32))
                   (set-id_ n v idarr)
                 (ec-call (set-id_ n v idarr)))))

  (local (in-theory (enable acl2::aignetp)))

  (defun idarr-sizedp (idarr aignet)
    (declare (xargs :stobjs (idarr aignet)
                    :guard-hints ('(:in-theory (enable memo-tablep)))))
    (mbe :logic (non-exec (memo-tablep idarr aignet))
         :exec (<= (num-nodes aignet) (ids-length idarr))))

  (defun idarr-id-in-bounds (id idarr)
    (declare (xargs :guard (idp id)
                    :stobjs idarr
                    :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
    (mbe :logic (non-exec (id-in-bounds id idarr))
         :exec (< (id-val id) (ids-length idarr))))

  (defun idarr-iterator-in-bounds (n idarr)
    (declare (xargs :guard (natp n)
                    :stobjs idarr
                    :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
    (mbe :logic (non-exec (iterator-in-bounds n idarr))
         :exec (<= (nfix n) (ids-length idarr))))

  (local (in-theory (enable nth-id update-nth-id)))

  ;; (defthm idp-nth-in-idsp
  ;;   (implies (and (idsp arr)
  ;;                 (< (nfix n) (len arr)))
  ;;            (idp (nth n arr)))
  ;;   :hints(("Goal" :in-theory (enable nth))))

  ;; (definline get-id (n idarr)
  ;;   (declare (type (integer 0 *) n)
  ;;            (xargs :stobjs idarr
  ;;                   :guard (< n (ids-length idarr))))
  ;;   (mbe :logic (non-exec (nth-id n idarr))
  ;;        :exec (idsi n idarr)))

  ;; (definline set-id (n v idarr)
  ;;   (declare (type (integer 0 *) n)
  ;;            (type (integer 0 *) v)
  ;;            (xargs :stobjs idarr
  ;;                   :guard (and (< n (ids-length idarr))
  ;;                               (idp v))))
  ;;   (mbe :logic (non-exec   ;;                                     (update-nth-id
  ;;                                      n (id-fix v)
  ;;                                      (nth *idsi* idarr))
  ;;                                     idarr))
  ;;        :exec (if (< v (expt 2 32))
  ;;                  (update-idsi n v idarr)
  ;;                (ec-call (update-idsi n v idarr)))))

  (local (in-theory (enable nth-id nth-id
                            update-nth-id update-nth-id
                            id-in-bounds)))
  ;; using a idarr as various types of mapping
  (definline get-id->id (id idarr)
    (declare (type (integer 0 *) id)
             (xargs :stobjs idarr
                    :guard (and (idp id)
                                (idarr-id-in-bounds id idarr))))
    (get-id (id-val id) idarr))

  (definline set-id->id (id idv idarr)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) id)
             (xargs :stobjs idarr
                    :guard (and (idp id) (idp idv)
                                (idarr-id-in-bounds id idarr))))
    (set-id (id-val id) idv idarr))

  (acl2::def-universal-equiv
   ids-equiv
   :qvars (i)
   :equiv-terms ((id-equiv (nth i x))))

  (defcong ids-equiv id-equiv (nth i x) 2
    :hints ('(:use ((:instance ids-equiv-necc
                     (acl2::y x-equiv))))))
  (defcong ids-equiv ids-equiv (update-nth i v x) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable ids-equiv-necc)))))
  (defcong id-equiv ids-equiv (update-nth i v x) 2
        :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable ids-equiv-necc)))))

  (local (in-theory (enable nth-id update-nth-id)))

  (defcong ids-equiv id-equiv (nth-id i x) 2)
  (defcong ids-equiv ids-equiv (update-nth-id i v x) 3)
  (defcong id-equiv ids-equiv (update-nth-id i v x) 2))

(defsection u32arr

  (acl2::def-1d-arr :arrname u32arr
                    :slotname u32
                    :pred natp
                    :fix nfix
                    :type-decl (unsigned-byte 32)
                    :default-val 0
                    :rename ((set-u32 . set-u32_)
                             (u32s-length . u32-length)
                             (resize-u32s . resize-u32)))

  (definline set-u32 (n v u32arr)
    (declare (xargs :stobjs u32arr
                    :guard (and (natp n)
                                (< n (u32-length u32arr))
                                (natp v))))
    (mbe :logic (set-u32_ n (nfix v) u32arr)
         :exec (if (< (the (integer 0 *) v) (expt 2 32))
                   (set-u32_ n v u32arr)
                 (ec-call (set-u32_ n v u32arr)))))

  (local (in-theory (enable acl2::aignetp)))

  (defun u32arr-sizedp (u32arr aignet)
    (declare (xargs :stobjs (u32arr aignet)
                    :guard-hints ('(:in-theory (enable memo-tablep)))))
    (mbe :logic (non-exec (memo-tablep u32arr aignet))
         :exec (<= (num-nodes aignet) (u32-length u32arr))))

  (defun u32arr-id-in-bounds (id u32arr)
    (declare (xargs :guard (idp id)
                    :stobjs u32arr
                    :guard-hints (("goal" :in-theory (enable id-in-bounds)))))
    (mbe :logic (non-exec (id-in-bounds id u32arr))
         :exec (< (id-val id) (u32-length u32arr))))

  (defun u32arr-iterator-in-bounds (n u32arr)
    (declare (xargs :guard (natp n)
                    :stobjs u32arr
                    :guard-hints (("goal" :in-theory (enable iterator-in-bounds)))))
    (mbe :logic (non-exec (iterator-in-bounds n u32arr))
         :exec (<= (nfix n) (u32-length u32arr))))

  ;; (defthm u32p-is-32bit-listp
  ;;   (equal (u32p x)
  ;;          (32bit-listp x)))

  (local (in-theory (enable nth-lit nth-id
                            update-nth-lit update-nth-id
                            id-in-bounds)))

  (definline get-id->nat (id u32arr)
    (declare (type (integer 0 *) id)
             (xargs :stobjs u32arr
                    :guard (and (idp id)
                                (u32arr-id-in-bounds id u32arr))))
    (lnfix (get-u32 (id-val id) u32arr)))

  (definline set-id->nat (id n u32arr)
    (declare (type (integer 0 *) id)
             (type (integer 0 *) n)
             (xargs :stobjs u32arr
                    :guard (and (idp id)
                                (u32arr-id-in-bounds id u32arr))))
    (set-u32 (id-val id) (lnfix n) u32arr)))

(defsection copying

  (local (include-book "bit-lemmas"))
  (local (in-theory (disable id-eval
                             32bit-listp
                             true-listp
                             sets::double-containment
                             acl2::nfix-when-not-natp
                             acl2::natp-when-integerp)))

  (defstobj-clone aignet-copy litarr :prefix "COPY")

  ;; Copies:

  (defun aignet-copies-ok (n aignet-copy aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs (aignet-copy aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (litarr-iterator-in-bounds n aignet-copy))
                    :guard-debug t))
    (if (zp n)
        t
      (and (aignet-litp (get-id->lit (to-id (1- n)) aignet-copy) aignet)
           (aignet-copies-ok (1- n) aignet-copy aignet))))

  (defthm aignet-copies-ok-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new-aignet orig-aignet)
                  (aignet-copies-ok n aignet-copy orig-aignet))
             (aignet-copies-ok n aignet-copy new-aignet)))

  (defcong nat-equiv equal (aignet-copies-ok n aignet-copy aignet) 1)
  (defcong nth-equiv equal (nth-lit i x) 2 :hints(("Goal" :in-theory (enable nth-lit))))
  (defcong nth-equiv equal (aignet-copies-ok n aignet-copy aignet) 2)
  (defcong nth-equiv equal (aignet-copies-ok n aignet-copy aignet) 3)

  (defthm aignet-copies-ok-of-aignet-add-simp-gate
    (implies (aignet-copies-ok n aignet-copy aignet)
             (aignet-copies-ok n aignet-copy
                               (mv-nth 2 (aignet-add-simp-gate
                                          lit1 lit2 gatesimp strash aignet)))))

  (defthm aignet-copies-ok-of-update
    (implies (and (aignet-copies-ok n aignet-copy aignet)
                  (aignet-litp v aignet))
             (aignet-copies-ok
              n
              (update-nth-lit m v aignet-copy)
              aignet))
    :hints (("goal" :induct
             (aignet-copies-ok n aignet-copy aignet))))

  (defthm aignet-copies-ok-implies
    (implies (and (aignet-copies-ok n aignet-copy aignet)
                  (< (nfix k) (nfix n)))
             (aignet-litp (nth-lit k aignet-copy) aignet))
    :hints (("goal" :induct (aignet-copies-ok n aignet-copy aignet))))

  (defthm aignet-copies-ok-implies-special
    (implies (and (aignet-copies-ok (nth *num-nodes* aignet1) aignet-copy aignet)
                  (aignet-idp (to-id k) aignet1))
             (aignet-litp (nth-lit k aignet-copy) aignet))
    :hints (("goal" :in-theory (enable aignet-idp))))

  (defmacro lit-copy (lit aignet-copyv)
    `(let ((lit-copy-lit ,lit))
       (lit-negate-cond (get-id->lit (lit-id lit-copy-lit) ,aignet-copyv)
                        (lit-neg lit-copy-lit))))

  (local (in-theory (disable aignet-add-simp-gate)))

  (defiteration aignet-copy-comb (aignet aignet-copy gatesimp strash aignet2)
    (declare (type (integer 0 *) gatesimp)
             (xargs :stobjs (aignet aignet-copy strash aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (litarr-sizedp aignet-copy aignet)
                                (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2))
                    :guard-hints (("goal" :do-not-induct t))))
    (b* ((n (lnfix n))
         (nid (to-id n))
         (slot0 (get-node-slot nid 0 aignet)))
      (aignet-case
       (snode->type slot0)
       :gate (b* ((lit0 (snode-gate->fanin0 slot0))
                  (lit1 (gate-id->fanin1 nid aignet))
                  ((mv lit strash aignet2)
                   (aignet-add-simp-gate
                    (lit-copy lit0 aignet-copy)
                    (lit-copy lit1 aignet-copy)
                    strash gatesimp aignet2))
                  (aignet-copy (set-id->lit nid lit aignet-copy)))
               (mv aignet-copy strash aignet2))
       :in ;; assume already set up
       (mv aignet-copy strash aignet2)
       :out ;; -- output -- update copy numbers as fanins but don't add nodes
       (b* ((lit0 (snode-co->fanin slot0))
            (aignet-copy (set-id->lit nid (lit-copy lit0 aignet-copy) aignet-copy)))
         (mv aignet-copy strash aignet2))
       :const (b* ((aignet-copy (set-id->lit nid (to-lit 0) aignet-copy)))
                (mv aignet-copy strash aignet2))))
    :returns (mv aignet-copy strash aignet2)
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (in-theory (enable (:induction aignet-copy-comb-iter)))

  (def-aignet-preservation-thms aignet-copy-comb-iter :stobjname aignet2)

  ;; (def-aignet-frame aignet-copy-comb-iter
  ;;   :hints (("goal" :induct (aignet-copy-comb-iter n aignet aignet-copy gatesimp strash aignet2)
  ;;            :expand ((:free (aignet2) (aignet-copy-comb-iter n aignet aignet-copy gatesimp
  ;;                                                 strash aignet2)))
  ;;            :in-theory (disable (:definition aignet-copy-comb-iter))
  ;;            :do-not-induct t))
  (defthm nth-aignet2-of-aignet-copy-comb-iter
    (implies (and (not (equal (nfix acl2::n) *nodesi*))
                  (not (equal (nfix acl2::n) *num-nodes*))
                  (not (equal (nfix acl2::n) *num-gates*)))
             (equal (nth acl2::n
                         (mv-nth
                          2 (aignet-copy-comb-iter n aignet aignet-copy gatesimp strash aignet2)))
                    (nth acl2::n aignet2)))
    :hints (("goal" :induct (aignet-copy-comb-iter n aignet aignet-copy gatesimp strash aignet2)
             :expand ((:free (aignet2) (aignet-copy-comb-iter n aignet aignet-copy gatesimp
                                                              strash aignet2)))
             :in-theory (e/d* (aignet-frame-thms)
                              ((:definition aignet-copy-comb-iter)))
             :do-not-induct t)))


  (defthmd nth-in-aignet-copy-comb-iter-preserved
    (implies (and (< (nfix m) (nfix n))
                  (equal nm (1+ (nfix m)))
                  (syntaxp (not (equal n nm))))
             (equal (nth-lit m (mv-nth 0 (aignet-copy-comb-iter
                                                       n aignet aignet-copy
                                                       gatesimp strash aignet2)))
                    (nth-lit m (mv-nth 0 (aignet-copy-comb-iter
                                                       nm aignet aignet-copy
                                                       gatesimp strash aignet2)))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet aignet-copy gatesimp strash
                                    aignet2))
            '(:in-theory (disable b-xor b-and
                                  (:definition aignet-copy-comb-iter)
                                  co-orderedp
                                  gate-orderedp))
            (and stable-under-simplificationp
                 '(:expand ((aignet-copy-comb-iter
                             (+ 1 (nfix m))
                             aignet aignet-copy gatesimp strash aignet2))))))


  (defthm aignet-copy-comb-nth-previous
    (implies (<= (nfix n) (nfix m))
             (equal (nth-lit m (mv-nth 0 (aignet-copy-comb-iter
                                                       n aignet aignet-copy
                                                       gatesimp strash aignet2)))
                    (nth-lit m aignet-copy)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet aignet-copy
                                    gatesimp strash aignet2))))


  (defthm aignet-copies-ok-of-aignet-copy-comb
    (b* (((mv aignet-copy1 & aignet21)
          (aignet-copy-comb-iter
           n aignet aignet-copy gatesimp strash aignet2)))
      (implies (and (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                    (aignet-well-formedp aignet2)
                    (aignet-well-formedp aignet)
                    (<= (nfix n) (num-nodes aignet)))
               (and (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy1
                                      aignet21)
                    (aignet-well-formedp aignet21))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet aignet-copy
                                    gatesimp strash aignet2))))

  (defthm aignet-copy-sized-of-aignet-copy-comb-iter
    (implies (litarr-sizedp aignet-copy aignet)
             (memo-tablep                                (mv-nth 0 (aignet-copy-comb-iter
                                          n aignet aignet-copy gatesimp strash
                                          aignet2))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet aignet-copy
                                    gatesimp strash aignet2))))

  (defthm aignet-copy-comb-inputs-preserved
    (b* (((mv aignet-copy1 & &)
          (aignet-copy-comb-iter
           n aignet aignet-copy gatesimp strash aignet2)))
      (implies (and (equal (id->type (to-id m) aignet) (in-type)))
               (equal (nth-lit m aignet-copy1)
                      (nth-lit m aignet-copy))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet aignet-copy
                                    gatesimp strash aignet2))))

  (defiteration aignet-copy-comb-in-vals (in-vals reg-vals aignet2 aignet-copy
                                                  aignet)
    (declare (xargs :stobjs (aignet2 aignet-copy aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (litarr-sizedp aignet-copy aignet)
                                (aignet-copies-ok (num-nodes aignet)
                                                  aignet-copy aignet2)
                                (true-listp reg-vals)
                                (true-listp in-vals))))
    (b* ((in-id (innum->id n aignet))
         (copy-lit (get-id->lit in-id aignet-copy))
         (copy-val (lit-eval copy-lit in-vals reg-vals aignet2)))
      (update-nth n copy-val vals))
    :returns vals
    :init-vals ((vals nil))
    :iter-guard (true-listp vals)
    :index n
    :last (num-ins aignet))

  (defiteration aignet-copy-comb-reg-vals (in-vals reg-vals aignet2 aignet-copy
                                                   aignet)
    (declare (xargs :stobjs (aignet2 aignet-copy aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (litarr-sizedp aignet-copy aignet)
                                (aignet-copies-ok (num-nodes aignet)
                                                  aignet-copy aignet2)
                                (true-listp reg-vals)
                                (true-listp in-vals))))
    (b* ((reg-id (regnum->ro n aignet))
         (copy-lit (get-id->lit reg-id aignet-copy))
         (copy-val (lit-eval copy-lit in-vals reg-vals aignet2)))
      (update-nth n copy-val vals))
    :returns vals
    :init-vals ((vals nil))
    :iter-guard (true-listp vals)
    :index n
    :last (num-regs aignet))

  (in-theory (enable (:induction aignet-copy-comb-in-vals-iter)
                     (:induction aignet-copy-comb-reg-vals-iter)))

  (defthm nth-of-aignet-copy-comb-in-vals-iter
    (implies (and (aignet-well-formedp aignet)
                  ; (<= (nfix n) (num-ins aignet))
                  (< (nfix m) (nfix n)))
             (equal (nth m (aignet-copy-comb-in-vals-iter
                            n vals in-vals reg-vals aignet2 aignet-copy
                            aignet))
                    (lit-eval (get-id->lit (innum->id m aignet) aignet-copy)
                              in-vals reg-vals aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-in-vals-iter
                            n vals in-vals reg-vals aignet2 aignet-copy
                            aignet))))

  (defthm nth-of-aignet-copy-comb-reg-vals-iter
    (implies (and (aignet-well-formedp aignet)
                  ; (<= (nfix n) (num-regs aignet))
                  (< (nfix m) (nfix n)))
             (equal (nth m (aignet-copy-comb-reg-vals-iter
                            n vals in-vals reg-vals aignet2 aignet-copy
                            aignet))
                    (lit-eval (get-id->lit (regnum->ro m aignet) aignet-copy)
                              in-vals reg-vals aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-reg-vals-iter
              n vals in-vals reg-vals aignet2 aignet-copy
              aignet))))

  (local
   (defun-sk eval-of-aignet-copy-comb-invariant
     (n in-vals reg-vals aignet-copy1 aignet21 aignet2 aignet-copy aignet)
     (forall m
             (implies (< (nfix m) (nfix n))
                      (equal (lit-eval (nth-lit m aignet-copy1)
                                       in-vals reg-vals aignet21)
                             (id-eval (to-id m)
                                      (aignet-copy-comb-in-vals
                                       in-vals reg-vals aignet2 aignet-copy aignet)
                                      (aignet-copy-comb-reg-vals
                                       in-vals reg-vals aignet2 aignet-copy aignet)
                                      aignet))))
     :rewrite :direct))

  (local (in-theory (disable eval-of-aignet-copy-comb-invariant)))

  (local (defthm lit-eval-of-mk-lit
           (equal (lit-eval (mk-lit (lit-id lit) neg) in-vals reg-vals aignet)
                  (b-xor (b-xor neg (lit-neg lit))
                         (lit-eval lit in-vals reg-vals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))


  (defthm aignet-idp-of-aignet-copy-comb-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (< (nfix m) (num-nodes aignet))
                  (<= (nfix n) (num-nodes aignet)))
             (b* (((mv aignet-copy & aignet2)
                   (aignet-copy-comb-iter
                    n aignet aignet-copy
                    gatesimp strash aignet2)))
               (aignet-litp (nth-lit m aignet-copy) aignet2)))
    :hints (("goal" :use ((:instance aignet-copies-ok-of-aignet-copy-comb))
             :in-theory (disable aignet-copies-ok-of-aignet-copy-comb))))

  (local
   (defthm eval-of-aignet-copy-comb-lemma
     (implies (and (aignet-well-formedp aignet)
                   (aignet-well-formedp aignet2)
                   (<= (nfix n) (num-nodes aignet))
                   (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2))
              (b* (((mv aignet-copy1 & aignet21)
                    (aignet-copy-comb-iter
                     n aignet aignet-copy gatesimp strash aignet2)))
                (eval-of-aignet-copy-comb-invariant
                 n in-vals reg-vals aignet-copy1 aignet21 aignet2 aignet-copy aignet)))
     :hints (("goal" :induct (aignet-copy-comb-iter
                              n aignet aignet-copy gatesimp strash aignet2)
              :expand ((aignet-copy-comb-iter
                        n aignet aignet-copy gatesimp strash aignet2)))
             (and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :in-theory (enable eval-and-of-lits)))
             (and stable-under-simplificationp
                  (let ((witness (acl2::find-call-lst
                                  'eval-of-aignet-copy-comb-invariant-witness
                                  clause)))
                    `(:clause-processor
                      (acl2::simple-generalize-cp
                       clause '((,witness . witness))))))
             (and stable-under-simplificationp
                  '(:cases ((< (nfix witness) (nfix (+ -1 n))))))
             (and stable-under-simplificationp
                  '(:expand ((:free (in-vals reg-vals)
                              (id-eval (to-id (+ -1 n)) in-vals reg-vals
                                       aignet)))
                    :in-theory (enable lit-eval))))))

  (defthm eval-of-aignet-copy-comb
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (<= (nfix n) (num-nodes aignet))
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (< (nfix m) (nfix n)))
             (b* (((mv aignet-copy1 & aignet21)
                   (aignet-copy-comb-iter
                    n aignet aignet-copy gatesimp strash aignet2)))
               (equal (lit-eval (nth-lit m aignet-copy1)
                                in-vals reg-vals aignet21)
                      (id-eval (to-id m)
                               (aignet-copy-comb-in-vals
                                in-vals reg-vals aignet2 aignet-copy aignet)
                               (aignet-copy-comb-reg-vals
                                in-vals reg-vals aignet2 aignet-copy aignet)
                               aignet))))
    :hints (("goal" :use ((:instance eval-of-aignet-copy-comb-lemma))
             :in-theory (disable eval-of-aignet-copy-comb-lemma))))


  (defthm aignet-copy-in-vals-of-extension
    (implies (and (aignet-extension-binding :new-aignet new-aignet2
                                            :orig-aignet aignet2)
                  (aignet-extension-p new-aignet2 aignet2)
                  (aignet-copies-ok (num-nodes aignet)
                                    aignet-copy aignet2)
                  (aignet-well-formedp aignet)
                  (<= (nfix n) (num-ins aignet)))
             (equal (aignet-copy-comb-in-vals-iter
                     n vals in-vals reg-vals new-aignet2 aignet-copy aignet)
                    (aignet-copy-comb-in-vals-iter
                     n vals in-vals reg-vals aignet2 aignet-copy aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-in-vals-iter
              n vals in-vals reg-vals new-aignet2
              aignet-copy aignet)
             :expand-others
             ((aignet-copy-comb-in-vals-iter
               n vals in-vals reg-vals aignet2
               aignet-copy
               aignet)))))

  (defthm aignet-copy-reg-vals-of-extension
    (implies (and (aignet-extension-binding :new-aignet new-aignet2
                                            :orig-aignet aignet2)
                  (aignet-extension-p new-aignet2 aignet2)
                  (aignet-copies-ok (num-nodes aignet)
                                    aignet-copy aignet2)
                  (aignet-well-formedp aignet)
                  (<= (nfix n) (num-regs aignet)))
             (equal (aignet-copy-comb-reg-vals-iter
                     n vals in-vals reg-vals new-aignet2 aignet-copy aignet)
                    (aignet-copy-comb-reg-vals-iter
                     n vals in-vals reg-vals aignet2 aignet-copy aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-reg-vals-iter
              n vals in-vals reg-vals new-aignet2
              aignet-copy aignet)
             :expand-others
             ((aignet-copy-comb-reg-vals-iter
               n vals in-vals reg-vals aignet2
               aignet-copy
               aignet)))))


  ;; These two hold because aignet-copy-comb doesn't touch the copy pointers of
  ;; CI nodes
  (defthm aignet-copy-in-vals-after-copy-comb-copy
    (b* (((mv aignet-copy2 & &)
          (aignet-copy-comb-iter
           m aignet aignet-copy gatesimp strash aignet2)))
      (implies (and (aignet-well-formedp aignet)
                    (<= (nfix n) (num-ins aignet)))
               (equal (aignet-copy-comb-in-vals-iter
                       n vals in-vals reg-vals aignet22 aignet-copy2 aignet)
                      (aignet-copy-comb-in-vals-iter
                       n vals in-vals reg-vals aignet22 aignet-copy aignet))))
    :hints (("goal" :induct
             (aignet-copy-comb-in-vals-iter
              n vals in-vals reg-vals
              aignet22
              (mv-nth 0 (aignet-copy-comb-iter
                         m aignet aignet-copy gatesimp strash aignet2))
              aignet)
             :in-theory (disable (:induction aignet-copy-comb-iter)))
            '(:expand
              ((:free (aignet-copy)
                (aignet-copy-comb-in-vals-iter
                 n vals in-vals reg-vals aignet22 aignet-copy
                 aignet))))))

  (defthm aignet-copy-reg-vals-after-copy-comb-copy
    (b* (((mv aignet-copy2 & &)
          (aignet-copy-comb-iter
           m aignet aignet-copy gatesimp strash aignet2)))
      (implies (and (aignet-well-formedp aignet)
                    (<= (nfix n) (num-regs aignet)))
               (equal (aignet-copy-comb-reg-vals-iter
                       n vals in-vals reg-vals aignet22 aignet-copy2 aignet)
                      (aignet-copy-comb-reg-vals-iter
                       n vals in-vals reg-vals aignet22 aignet-copy aignet))))
    :hints (("goal" :induct
             (aignet-copy-comb-reg-vals-iter
              n vals in-vals reg-vals
              aignet22
              (mv-nth 0 (aignet-copy-comb-iter
                         m aignet aignet-copy gatesimp strash aignet2))
              aignet)
             :in-theory (disable (:induction aignet-copy-comb-iter)))
            '(:expand
              ((:free (aignet-copy)
                (aignet-copy-comb-reg-vals-iter
                 n vals in-vals reg-vals aignet22 aignet-copy
                 aignet)))))))

(defsection aignet-copy-frame

  (defiteration aignet-copy-frame (aignet aignet-copy gatesimp strash aignet2)
    (declare (type (integer 0 *) gatesimp)
             (xargs :stobjs (aignet aignet-copy strash aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (litarr-sizedp aignet-copy aignet)
                                (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2))
                    :guard-hints (("goal" :do-not-induct t))))
    (b* ((n (lnfix n))
         (nid (to-id n))
         (slot0 (get-node-slot nid 0 aignet)))
      (aignet-seq-case
       (snode->type slot0) (io-id->regp nid aignet)
       :gate (b* ((lit0 (snode-gate->fanin0 slot0))
                  (lit1 (gate-id->fanin1 nid aignet))
                  ((mv lit strash aignet2)
                   (aignet-add-simp-gate
                    (lit-copy lit0 aignet-copy)
                    (lit-copy lit1 aignet-copy)
                    strash gatesimp aignet2))
                  (aignet-copy (set-id->lit nid lit aignet-copy)))
               (mv aignet-copy strash aignet2))
       :pi (mv aignet-copy strash aignet2)
       :ro (b* (;; the copy of the reg is the copy of the reg input
                (regin-id (regnum->id (io-id->ionum nid aignet) aignet))
                (aignet-copy (set-id->lit nid
                                          (get-id->lit regin-id aignet-copy)
                                          aignet-copy)))
             (mv aignet-copy strash aignet2))
       :co ;; update copy numbers as fanins but don't add nodes
       (b* ((lit0 (snode-co->fanin slot0))
            (aignet-copy (set-id->lit nid (lit-copy lit0 aignet-copy) aignet-copy)))
         (mv aignet-copy strash aignet2))
       :const (b* ((aignet-copy (set-id->lit nid (to-lit 0) aignet-copy)))
                (mv aignet-copy strash aignet2))))
    :returns (mv aignet-copy strash aignet2)
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (in-theory (enable (:induction aignet-copy-frame-iter)))

  (def-aignet-preservation-thms aignet-copy-frame-iter :stobjname aignet2)

  ;; (def-aignet-frame aignet-copy-frame-iter
  ;;   :hints (("goal" :induct (aignet-copy-frame-iter n aignet aignet-copy gatesimp strash aignet2)
  ;;            :expand ((:free (aignet2) (aignet-copy-frame-iter n aignet aignet-copy gatesimp
  ;;                                                 strash aignet2)))
  ;;            :in-theory (disable (:definition aignet-copy-frame-iter))
  ;;            :do-not-induct t)))

  (defthm nth-aignet2-of-aignet-copy-comb-iter
    (implies (and (not (equal (nfix acl2::n) *nodesi*))
                  (not (equal (nfix acl2::n) *num-nodes*))
                  (not (equal (nfix acl2::n) *num-gates*)))
     (equal (nth acl2::n
                 (mv-nth
                  2 (aignet-copy-comb-iter n aignet aignet-copy gatesimp strash aignet2)))
            (nth acl2::n aignet2)))
    :hints (("goal" :induct (aignet-copy-comb-iter n aignet aignet-copy gatesimp strash aignet2)
             :expand ((:free (aignet2) (aignet-copy-comb-iter n aignet aignet-copy gatesimp
                                                  strash aignet2)))
             :in-theory (e/d* (aignet-frame-thms)
                              ((:definition aignet-copy-comb-iter)))
             :do-not-induct t)))

  (defiteration aignet-copy-update-ri->ros (aignet-copy aignet)
    (declare (xargs :stobjs (aignet-copy aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (litarr-sizedp aignet-copy aignet))))
    (b* ((n (lnfix n))
         ((unless (and (int= (id->type (to-id n) aignet) (in-type))
                       (int= (io-id->regp (to-id n) aignet) 1)))
          aignet-copy)
         (ri (regnum->id (io-id->ionum (to-id n) aignet) aignet)))
      (set-id->lit (to-id n)
                   (get-id->lit ri aignet-copy)
                   aignet-copy))
    :returns aignet-copy
    :index n
    :last (num-nodes aignet))

  (in-theory (enable (:induction aignet-copy-update-ri->ros-iter)))

  (defthm nth-lit-greater-of-aignet-copy-update-ri->ros
    (implies (<= (nfix n) (nfix k))
             (equal (nth-lit k (aignet-copy-update-ri->ros-iter
                                             n aignet-copy aignet))
                    (nth-lit k aignet-copy)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-update-ri->ros-iter n aignet-copy aignet))))

  (defthm lookup-in-aignet-copy-update-ri->ros
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-nodes aignet)))
             (equal (nth-lit k (aignet-copy-update-ri->ros-iter n aignet-copy aignet))
                    (if (and (equal (id->type (to-id k) aignet) (in-type))
                             (equal (io-id->regp (to-id k) aignet) 1)
                             (< (nfix k) (nfix n)))
                        (nth-lit (id-val (regnum->id (io-id->ionum (to-id k) aignet) aignet)) aignet-copy)
                      (nth-lit k aignet-copy))))
    :hints (("goal" :induct (aignet-copy-update-ri->ros-iter n aignet-copy aignet)
             :expand ((aignet-copy-update-ri->ros-iter n aignet-copy aignet))
             :do-not-induct t
             :in-theory (enable* aignet-well-formedp-strong-rules))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-reg-rw
                          (n (to-id k))))
                   :in-theory (e/d (aignet-idp)
                                   (aignet-well-formedp-reg-rw))) )
            )
    :otf-flg t)

  (defcong lits-equiv lits-equiv (aignet-copy-update-ri->ros-iter n aignet-copy aignet) 2
    :hints (("goal" :induct (aignet-copy-update-ri->ros-iter n aignet-copy aignet)
             :expand ((:free (aignet-copy)
                       (aignet-copy-update-ri->ros-iter n aignet-copy aignet))))))


  (local (defthm mv-nth-when-list-equal
           (implies (equal x (list a b c))
                    (and (equal (mv-nth 0 x) a)
                         (equal (mv-nth 1 x) b)
                         (equal (mv-nth 2 x) c)))))

  (defthm aignet-copy-comb-iter-of-update-prev-copy
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (nfix m))
                  (<= (nfix n) (num-nodes aignet)))
             (equal (aignet-copy-comb-iter
                     n aignet (update-nth-lit m val aignet-copy)
                     gatesimp strash aignet2)
                    (b* (((mv aignet-copy strash aignet2)
                          (aignet-copy-comb-iter
                           n aignet aignet-copy gatesimp strash aignet2)))
                      (mv (update-nth-lit m val aignet-copy)
                          strash aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet (update-nth-lit m val aignet-copy)
              gatesimp strash aignet2)
             :expand-others
             ((:free (aignet-copy)
               (aignet-copy-comb-iter
                n aignet aignet-copy gatesimp strash aignet2))))
            '(:in-theory (enable update-nth-lit-switch
                                 aignet-idp))))

  (defthm nth-lit-past-of-aignet-copy-frame-iter
    (implies (<= (nfix n) (nfix m))
             (equal (nth-lit m (mv-nth 0 (aignet-copy-frame-iter
                                          n aignet aignet-copy gatesimp
                                          strash aignet2)))
                    (nth-lit m aignet-copy)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-frame-iter n aignet aignet-copy gatesimp
                                     strash aignet2))))

  (defthm aignet-copy-frame-iter-rw
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-nodes aignet)))
             (equal (aignet-copy-frame-iter n aignet aignet-copy gatesimp strash aignet2)
                    (aignet-copy-comb-iter
                     n aignet (aignet-copy-update-ri->ros-iter n aignet-copy aignet)
                     gatesimp strash aignet2)))
    :hints (("goal" :induct (aignet-copy-frame-iter n aignet aignet-copy gatesimp strash aignet2)
             :expand ((aignet-copy-frame-iter n aignet aignet-copy gatesimp strash aignet2)
                      (aignet-copy-update-ri->ros-iter n aignet-copy aignet)
                      (:free (aignet-copy)
                       (aignet-copy-comb-iter n aignet aignet-copy gatesimp strash aignet2)))
             :in-theory (disable (:definition aignet-copy-frame-iter)
                                 aignet-copy-update-ri->ros-iter
                                 aignet-copy-comb-iter)))))

;; (defsection regnum->fanin
;;   (definlined reg-id->fanin (n aignet)
;;     (declare (type (integer 0 *) n)
;;              (xargs :stobjs aignet
;;                     :guard (and (aignet-well-formedp aignet)
;;                                 (idp n)
;;                                 (< (id-val n) (num-nodes aignet))
;;                                 (equal (id->type n aignet) (in-type))
;;                                 (equal (io-id->regp n aignet) 1))))
;;     (b* ((ri (reg-id->ri n aignet)))
;;       (if (int= (id-val ri) 0) (to-lit 0) (co-id->fanin ri aignet))))

;;   (definlined regnum->fanin (n aignet)
;;     (declare (type (integer 0 *) n)
;;              (xargs :stobjs aignet
;;                     :guard (and (aignet-well-formedp aignet)
;;                                 (< n (num-regs aignet)))))
;;     (b* ((ro (regnum->id n aignet)))
;;       (reg-id->fanin ro aignet)))

;;   (local (in-theory (enable regnum->fanin
;;                             reg-id->fanin)))
;;   (defcong id-equiv equal (reg-id->fanin n aignet) 1)
;;   (defcong nth-equiv equal (reg-id->fanin n aignet) 2)

;;   (defcong nat-equiv equal (regnum->fanin n aignet) 1)
;;   (defcong nth-equiv equal (regnum->fanin n aignet) 2)

;;   (defthm reg-id->fanin-in-bounds
;;     (implies (and (aignet-well-formedp aignet)
;;                   (< (id-val n) (num-nodes aignet))
;;                   (equal (id->type n aignet) (in-type))
;;                   (equal (io-id->regp n aignet) 1))
;;              (< (id-val (lit-id (reg-id->fanin n aignet)))
;;                 (nth *num-nodes* aignet)))
;;     :rule-classes (:rewrite :linear))

;;   (defthm regnum->fanin-in-bounds
;;     (implies (and (aignet-well-formedp aignet)
;;                   (< (nfix n) (num-regs aignet)))
;;              (< (id-val (lit-id (regnum->fanin n aignet)))
;;                 (nth *num-nodes* aignet)))
;;     :rule-classes (:rewrite :linear))

;;   (defthm reg-id->fanin-is-fanin
;;     (implies (and (aignet-well-formedp aignet)
;;                   (< (id-val n) (num-nodes aignet))
;;                   (equal (id->type n aignet) (in-type))
;;                   (equal (io-id->regp n aignet) 1))
;;              (and (litp (reg-id->fanin n aignet))
;;                   (not (equal (node->type (nth-node (lit-id (reg-id->fanin n aignet))
;;                                                   (nth *nodesi* aignet)))
;;                               (out-type))))))

;;   (defthm regnum->fanin-is-fanin
;;     (implies (and (aignet-well-formedp aignet)
;;                   (< (nfix n) (num-regs aignet)))
;;              (and (litp (regnum->fanin n aignet))
;;                   (not (equal (node->type (nth-node (lit-id (regnum->fanin n aignet))
;;                                                   (nth *nodesi* aignet)))
;;                               (out-type)))))))

(defsection aignet-copy-utils

  (local (in-theory (disable acl2::nfix-when-not-natp
                             acl2::natp-when-integerp
                             (:type-prescription aignet-well-formedp))))
  ;; Utilities for copying IOs

  (defiteration
   aignet-copy-ins (aignet aignet-copy aignet2)
   (declare (xargs :stobjs (aignet aignet-copy aignet2)
                   :guard (and (aignet-well-formedp aignet)
                               (aignet-well-formedp aignet2)
                               (litarr-sizedp aignet-copy aignet))))
   (b* ((inid (innum->id n aignet))
        ((mv inlit aignet2) (aignet-add-in aignet2))
        (aignet-copy (set-id->lit inid inlit aignet-copy)))
     (mv aignet-copy aignet2))
   :returns (mv aignet-copy aignet2)
   :last (num-ins aignet)
   :index n
   :package aignet::bla)
  ;; ;; Adds a aignet2 PI for every PI of aignet, and sets the copy
  ;; (defund aignet-copy-ins (n aignet aignet-copy aignet2)
  ;;   (declare (type (integer 0 *) n)
  ;;            (xargs :stobjs (aignet aignet-copy aignet2)
  ;;                   :guard (and (aignet-well-formedp aignet)
  ;;                               (aignet-well-formedp aignet2)
  ;;                               (litarr-sizedp aignet-copy aignet)
  ;;                               (<= n (num-ins aignet)))
  ;;                   :measure (nfix (- (nfix (num-ins aignet))
  ;;                                     (nfix n)))))
  ;;   (b* (((when (mbe :logic (zp (- (nfix (num-ins aignet))
  ;;                                  (nfix n)))
  ;;                    :exec (int= n (num-ins aignet))))
  ;;         (mv aignet-copy aignet2))
  ;;        (inid (innum->id n aignet))
  ;;        ((mv inlit aignet2) (aignet-add-in aignet2))
  ;;        (aignet-copy (set-id->lit inid inlit aignet-copy)))
  ;;     (aignet-copy-ins (1+ (lnfix n)) aignet aignet-copy aignet2)))

  (local (in-theory (enable (:induction aignet-copy-ins-iter))))

  (def-aignet-preservation-thms aignet-copy-ins-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-ins-iter n aignet aignet-copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-ins-iter n aignet aignet-copy aignet2))
              (:free (aignet-copy) (aignet-copy-ins-iter n aignet aignet-copy aignet2))
              (:free (aignet2) (aignet-copy-ins-iter n aignet aignet-copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (def-aignet-frame aignet-copy-ins-iter)
  (def-aignet2-frame aignet-copy-ins-iter)

  (defthm aignet-copy-size-of-aignet-copy-ins
    (implies (and (aignet-well-formedp aignet)
                  (litarr-sizedp aignet-copy aignet))
             (memo-tablep (mv-nth 0 (aignet-copy-ins-iter
                                                  n aignet aignet-copy aignet2))
                          aignet)))

  (defthm aignet-copies-ok-of-aignet-copy-ins-iter
    (implies (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
             (mv-let (aignet-copy aignet2)
               (aignet-copy-ins-iter n aignet aignet-copy aignet2)
               (aignet-copies-ok
                (nth *num-nodes* aignet)
                aignet-copy aignet2))))

  (local (defthm nfix-diff-zero
           (implies (<= a b)
                    (equal (nfix (+ (- b) a))
                           0))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defthm num-ins-of-aignet-copy-ins-iter
    (implies (aignet-well-formedp aignet2)
             (equal (nth *num-ins* (mv-nth 1 (aignet-copy-ins-iter
                                              n aignet aignet-copy aignet2)))
                    (+ (nfix n)
                       (nth *num-ins* aignet2)))))

  ; (local (in-theory (enable* aignet-well-formedp-strong-rules)))
  (defthm lookup-copy-of-aignet-copy-ins-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-idp (to-id m) aignet)
                  (<= (nfix n) (num-ins aignet)))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-ins-iter n aignet aignet-copy aignet2)))
               (equal (nth-lit m aignet-copy-new)
                      (let ((id (to-id m)))
                        (if (or (not (equal (id->type id aignet) (in-type)))
                                (equal (io-id->regp id aignet) 1)
                                (<= (nfix n) (io-id->ionum id aignet)))
                            (get-id->lit id aignet-copy)
                          (mk-lit
                           (nth-id (+ (nfix (io-id->ionum id aignet))
                                      (num-ins aignet2))
                                   (nth *insi* aignet2-new))
                           0))))))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable* aignet-well-formedp-strong-rules
                                      aignet-add-in aignet-frame-thms)))))

  (local (set-default-hints nil))



  ;; Adds a aignet2 reg for every reg of aignet, and sets the copy
  (defiteration aignet-copy-regs (aignet aignet-copy aignet2)
    (declare (xargs :stobjs (aignet aignet-copy aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (litarr-sizedp aignet-copy aignet))))
    (b* ((ro (regnum->ro n aignet))
         ((mv reglit aignet2) (aignet-add-reg aignet2))
         (aignet-copy (set-id->lit ro reglit aignet-copy)))
      (mv aignet-copy aignet2))
    :returns (mv aignet-copy aignet2)
    :last (num-regs aignet)
    :index n
    :package aignet::bla)

  ;; (defun aignet-copy-regs (n aignet aignet-copy aignet2)
  ;;   (declare (type (integer 0 *) n)
  ;;            (xargs :stobjs (aignet aignet-copy aignet2)
  ;;                   :guard (and (aignet-well-formedp aignet)
  ;;                               (aignet-well-formedp aignet2)
  ;;                               (litarr-sizedp aignet-copy aignet)
  ;;                               (<= n (num-regs aignet)))
  ;;                   :measure (nfix (- (nfix (num-regs aignet))
  ;;                                     (nfix n)))))
  ;;   (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet))
  ;;                                  (nfix n)))
  ;;                    :exec (int= n (num-regs aignet))))
  ;;         (mv aignet-copy aignet2))
  ;;        (ro (regnum->ro n aignet))
  ;;        ((mv reglit aignet2) (aignet-add-reg aignet2))
  ;;        (aignet-copy (set-id->lit ro reglit aignet-copy)))
  ;;     (aignet-copy-regs (1+ (lnfix n)) aignet aignet-copy aignet2)))

  (local (in-theory (enable (:induction aignet-copy-regs-iter))))

  (def-aignet-preservation-thms aignet-copy-regs-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-regs-iter n aignet aignet-copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-regs-iter n aignet aignet-copy aignet2))
              (:free (aignet-copy) (aignet-copy-regs-iter n aignet aignet-copy aignet2))
              (:free (aignet2) (aignet-copy-regs-iter n aignet aignet-copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (def-aignet-frame aignet-copy-regs-iter)
  (def-aignet2-frame aignet-copy-regs-iter)

  (defthm aignet-copy-size-of-aignet-copy-regs-iter
    (implies (and (aignet-well-formedp aignet)
                  (litarr-sizedp aignet-copy aignet))
             (memo-tablep (mv-nth 0 (aignet-copy-regs-iter n aignet aignet-copy
                                                               aignet2))
                          aignet)))

  (defthm aignet-copies-ok-of-aignet-copy-regs-iter
    (implies (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
             (mv-let (aignet-copy aignet2)
               (aignet-copy-regs-iter n aignet aignet-copy aignet2)
               (aignet-copies-ok
                (nth *num-nodes* aignet)
                aignet-copy aignet2))))

  (local (set-default-hints nil))

  ;; Adds a aignet2 output for every output of aignet, using the stored copy
  ;; assumes the copy of each output ID is set to the fanin lit,
  ;; does not change this to the new node
  (defiteration aignet-copy-outs (aignet aignet-copy aignet2)
    (declare (xargs :stobjs (aignet aignet-copy aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (litarr-sizedp aignet-copy aignet)
                                (aignet-copies-ok (num-nodes aignet)
                                                  aignet-copy aignet2))))
    (b* ((outid (outnum->id n aignet))
         (fanin (get-id->lit outid aignet-copy))
         (aignet2 (aignet-add-out fanin aignet2)))
      aignet2)
    :returns aignet2
    :last (num-outs aignet)
    :index n
    :package aignet::bla)

  ;; (defun aignet-copy-outs (n aignet aignet-copy aignet2)
  ;;   (declare (type (integer 0 *) n)
  ;;            (xargs :stobjs (aignet aignet-copy aignet2)
  ;;                   :guard (and (aignet-well-formedp aignet)
  ;;                               (aignet-well-formedp aignet2)
  ;;                               (litarr-sizedp aignet-copy aignet)
  ;;                               (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
  ;;                               (<= n (num-outs aignet)))
  ;;                   :measure (nfix (- (nfix (num-outs aignet))
  ;;                                     (nfix n)))))
  ;;   (b* (((when (mbe :logic (zp (- (nfix (num-outs aignet))
  ;;                                  (nfix n)))
  ;;                    :exec (int= n (num-outs aignet))))
  ;;         aignet2)
  ;;        (outid (outnum->id n aignet))
  ;;        (fanin (get-id->lit outid aignet-copy))
  ;;        (aignet2 (aignet-add-out fanin aignet2)))
  ;;     (aignet-copy-outs (1+ (lnfix n)) aignet aignet-copy aignet2)))

  (local (in-theory (enable (:induction aignet-copy-outs-iter))))

  (def-aignet-preservation-thms aignet-copy-outs-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-outs-iter n aignet aignet-copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-outs-iter n aignet aignet-copy aignet2))
              (:free (aignet-copy) (aignet-copy-outs-iter n aignet aignet-copy aignet2))
              (:free (aignet2) (aignet-copy-outs-iter n aignet aignet-copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (def-aignet-frame aignet-copy-outs-iter)
  (def-aignet2-frame aignet-copy-outs-iter)

  (local (set-default-hints nil))

  (local (in-theory (enable* aignet-frame-thms)))

  ;; Adds a aignet2 regin for every register of aignet.
  ;; assumes the copy of each regin ID is set to the fanin lit,
  ;; does not change this to the new node.
  ;; Connects the regin to the corresponding reg in aignet2.  Therefore, we must
  ;; assume there are at least as many regs in aignet2 as in aignet.
  (defiteration aignet-copy-regins (aignet aignet-copy aignet2)
    (declare (xargs :stobjs (aignet aignet-copy aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (litarr-sizedp aignet-copy aignet)
                                (<= (num-regs aignet) (num-regs aignet2))
                                (aignet-copies-ok (num-nodes aignet)
                                                  aignet-copy aignet2))))
    (b* ((ri (regnum->id n aignet))
         ((when (int= (id->type ri aignet) (in-type)))
          ;; has no corresp regin, skip
          aignet2)
         (fanin-copy (get-id->lit ri aignet-copy))
         (ro-copy (regnum->id n aignet2))
         (ro-copy (if (int= (id->type ro-copy aignet2) (in-type))
                      ro-copy
                    (to-id 0)))
         (aignet2 (aignet-add-regin fanin-copy ro-copy aignet2)))
      aignet2)
    :returns aignet2
    :last (num-regs aignet)
    :index n
    :guard-hints ('(:in-theory (enable aignet-unconnected-reg-p)))
    :package aignet::bla)

  ;; (defun aignet-copy-regins (n aignet aignet-copy aignet2)
  ;;   (declare (type (integer 0 *) n)
  ;;            (xargs :stobjs (aignet aignet-copy aignet2)
  ;;                   :guard (and (aignet-well-formedp aignet)
  ;;                               (aignet-well-formedp aignet2)
  ;;                               (litarr-sizedp aignet-copy aignet)
  ;;                               (<= (num-regs aignet) (num-regs aignet2))
  ;;                               (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
  ;;                               (<= n (num-regs aignet)))
  ;;                   :guard-hints (("goal" :in-theory (enable aignet-unconnected-reg-p)))
  ;;                   :measure (nfix (- (nfix (num-regs aignet))
  ;;                                     (nfix n)))))
  ;;   (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet))
  ;;                                  (nfix n)))
  ;;                    :exec (int= n (num-regs aignet))))
  ;;         aignet2)
  ;;        (ri (regnum->id n aignet))
  ;;        ((when (int= (id->type ri aignet) (in-type)))
  ;;         ;; has no corresp regin, skip
  ;;         (aignet-copy-regins (1+ (lnfix n)) aignet aignet-copy aignet2))
  ;;        (fanin-copy (get-id->lit ri aignet-copy))
  ;;        (ro-copy (regnum->id n aignet2))
  ;;        (ro-copy (if (int= (id->type ro-copy aignet2) (in-type))
  ;;                     ro-copy
  ;;                   (to-id 0)))
  ;;        (aignet2 (aignet-add-regin fanin-copy ro-copy aignet2)))
  ;;     (aignet-copy-regins (1+ (lnfix n)) aignet aignet-copy aignet2)))

  (local (in-theory (enable (:induction aignet-copy-regins-iter))))

  (def-aignet-preservation-thms aignet-copy-regins-iter :stobjname aignet2
    :omit (aignet-unconnected-reg-p-preserved))

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-regins-iter n aignet aignet-copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-regins-iter n aignet aignet-copy aignet2))
              (:free (aignet-copy) (aignet-copy-regins-iter n aignet aignet-copy aignet2))
              (:free (aignet2) (aignet-copy-regins-iter n aignet aignet-copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (def-aignet-frame aignet-copy-regins-iter)
  (def-aignet2-frame aignet-copy-regins-iter))

(defsection aignet-print
  (local (in-theory (disable len acl2::aignetp)))
  (defund aignet-print-lit (lit aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp lit aignet))))
    (b* ((id (lit-id lit))
         (type (id->type id aignet))
         ((when (int= type (const-type)))
          (if (int= (lit-neg lit) 1) "1" "0")))
      (acl2::msg "~s0~s1~x2"
                 (if (int= (lit-neg lit) 1) "~" "")
                 (if (int= type (in-type))
                     (if (int= (io-id->regp id aignet) 1) "r" "i")
                   "g")
                 (if (int= type (in-type))
                     (io-id->ionum id aignet)
                   id))))

  (defund aignet-print-gate (n aignet)
    (declare (Xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-idp n aignet)
                                (int= (id->type n aignet) (gate-type)))))
    (b* ((f0 (gate-id->fanin0 n aignet))
         (f1 (gate-id->fanin1 n aignet)))
      (acl2::msg "g~x0 = ~@1 & ~@2"
                 n
                 (aignet-print-lit f0 aignet)
                 (aignet-print-lit f1 aignet))))


  (defund aignet-print-gates (n aignet)
    (declare (Xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (natp n)
                                (aignet-iterator-p n aignet))
                    :measure (nfix (- (nfix (num-nodes aignet)) (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet)) (nfix n)))
                     :exec (= (num-nodes aignet) n)))
          nil)
         ((unless (int= (id->type (to-id n) aignet) (gate-type)))
          (aignet-print-gates (1+ (lnfix n)) aignet))
         (- (cw "~@0~%" (aignet-print-gate (to-id n) aignet))))
      (aignet-print-gates (1+ (lnfix n)) aignet)))

  (defund aignet-print-outs (n aignet)
    (declare (Xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (natp n)
                                (<= n (num-outs aignet)))
                    :measure (nfix (- (nfix (num-outs aignet)) (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-outs aignet)) (nfix n)))
                     :exec (= (num-outs aignet) n)))
          nil)
         (- (cw "o~x0 = ~@1~%" n (aignet-print-lit
                                  (co-id->fanin (outnum->id n aignet) aignet)
                                  aignet))))
      (aignet-print-outs (1+ (lnfix n)) aignet)))

  (defund aignet-print-regs (n aignet)
    (declare (Xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (natp n)
                                (<= n (num-regs aignet)))
                    :measure (nfix (- (nfix (num-regs aignet)) (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet)) (nfix n)))
                     :exec (= (num-regs aignet) n)))
          nil)
         (ri (regnum->id n aignet))
         ((unless (int= (id->type ri aignet) (out-type)))
          (aignet-print-regs (1+ (lnfix n)) aignet))
         (- (cw "r~x0 = ~@1~%" n
                (aignet-print-lit (co-id->fanin ri aignet) aignet))))
      (aignet-print-regs (1+ (lnfix n)) aignet)))

  (defund aignet-print (aignet)
    (declare (xargs :stobjs aignet
                    :guard (aignet-well-formedp aignet)))
    (progn$ (aignet-print-gates 0 aignet)
            (aignet-print-outs 0 aignet)
            (aignet-print-regs 0 aignet))))

;; (defsection construct-gates

;;   ;; Adding various gates.  All return (mv new-lit strash aignet).

;;   ;; This is just an alias for aignet-add-simp-gate.
;; )

(defsection aignet-construction
  :parents (aignet)
  :short "How to construct an AIGNET network."
  :autodoc nil
  :long "
<p>An AIGNET network is constructed by adding nodes in topological
order: that is, an AND gate cannot be added until its two fanins are created,
and a combinational output cannot be added until its fanin exists.
Additionally, a register input cannot be added until its corresponding register
output exists.</p>

<p>First, because an AIGNET network is represented in a stobj, you must either
work on the \"live\" @('AIGNET') stobj or else create a local one using
@(see with-local-stobj).</p>

<p>Usually when constructing an AIG network one wants to structurally hash the
AND nodes, so as to avoid creating duplicate nodes with identical structure.
To do this, you additionally need a @('STRASH') stobj, which again may either
be the live one or one created locally.</p>

<p>To initialize a new network or clear an existing one, use:
@({ (aignet-clear aignet) })
or, to allocate a certain amount of space in order to avoid resizing arrays,
@({ (aignet-init output-cap reg-cap input-cap node-cap aignet). })</p>

<p>To initialize a strash object or clear an existing one, use:
@({ (strashtab-clear strash) })
or to allocate a certain amount of space to avoid resizing the hash table,
@({ (strashtab-init node-cap nil nil strash). })</p>

<h1>Aigaignet-construction functions</h1>
<p>@('(aignet-add-in aignet)') adds a new primary input node to the network and
returns <tt>(mv lit aignet)</tt>, where <tt>lit</tt> is the non-negated literal of
the new node.</p>

<p>@('(aignet-add-reg aignet)') adds a new register output node to the network and
returns <tt>(mv lit aignet)</tt>, where <tt>lit</tt> is the non-negated literal of
the new node.</p>

<p>@('(aignet-add-gate lit1 lit2 aignet)') adds to the network a new AND node
conjoining <tt>lit1</tt> and <tt>lit2</tt>, and returns <tt>(mv lit aignet)</tt>,
where <tt>lit</tt> is the non-negated literal of the new node.  <tt>lit1</tt>
and <tt>lit2</tt> must be literals of the network, satisfying
@('aignet-litp') (which is true of any literal returned by a node construction
function, or its negation).  Note: this function does not do structural
hashing -- for that, see below.</p>

<p>@('(aignet-add-out lit aignet)') adds to the network a new primary output with
fanin <tt>lit</tt>, and returns <tt>aignet</tt>.  (It does not return a literal
because a combinational output node is not allowed to be the fanin to another
node.)  <tt>lit</tt> must satisfy @('aignet-litp').</p>

<p>@('(aignet-add-regin lit ro aignet)') adds to the network a new register input
with fanin <tt>lit</tt>, and connects it to a register output node whose ID is
<tt>ro</tt>.  It returns <tt>aignet</tt>.  <tt>lit</tt> must satisfy @('aignet-litp')
and <tt>ro</tt> must be the ID of a register output node that is not yet
connected to a register input.</p>

<p>The following functions:
@({
    (aignet-hash-and f1 f2 strash gatesimp aignet)
    (aignet-hash-or  f1 f2 strash gatesimp aignet)
    (aignet-hash-xor f1 f2 strash gatesimp aignet)
    (aignet-hash-mux c tb fb strash gatesimp aignet) })

add nodes implementing the respective functions of input literals <tt>f1</tt>
and <tt>f2</tt> (for and/or/xor) and <tt>c</tt>, <tt>tb</tt>, and <tt>fb</tt>
for mux (signifying condition, true-branch, and false-branch), possibly with
structural hashing and lightweight simplification.  All return
<code>(mv lit strash aignet).</code>
Gatesimp is an object that specifies both whether to
structurally hash the nodes and what level of effort to use in Boolean
simplification, between 0 and 4.  The levels of simplification correspond to
the paper:

<blockquote>
R. Brummayer and A. Biere.  Local two-level And-Inverter Graph minimization
without blowup.  Proc. MEMCIS 6 (2006): 32-38,
</blockquote>

available <a
href=\"http://megaknowledge.info/cadathlon/2007/refs/p5-verification.pdf\">here</a>.
These simplifications look at most one level deep at the fanins of each AND,
that is, examining at most four fanin nodes.  Usually at least level 1 is
desirable; level 1 deals with ANDs of constants and identical and negated
nodes.  Practically, we think for most applications building the AIGs is not a
performance bottleneck and level 3 or 4 can be used with some potential benefit
and no noticeable slowdown.</p>

<p>To construct a gatesimp object, use @('(mk-gatesimp level hashp)'), where
level is from 0-4 as above and hashp is Boolean and causes structural hashing
to be done if non-<tt>NIL</tt>.</p>"

  (definlined aignet-hash-and (f0 f1 strash gatesimp aignet)
    (declare (xargs :stobjs (strash aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp f0 aignet)
                                (aignet-litp f1 aignet)
                                (natp gatesimp))))
    (aignet-add-simp-gate f0 f1 strash gatesimp aignet))
  (local (in-theory (enable aignet-hash-and)))

  (def-aignet-frame aignet-hash-and)

  (defthm litp-aignet-hash-and
    (litp (mv-nth 0 (aignet-hash-and lit1 lit2 strash gatesimp aignet))))

  (defthm aignet-litp-aignet-hash-and
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet)
                   (aignet-hash-and lit1 lit2 strash gatesimp aignet)))
               (aignet-litp lit aignet))))

  (definlined aignet-hash-or (f0 f1 strash gatesimp aignet)
    (declare (xargs :stobjs (strash aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp f0 aignet)
                                (aignet-litp f1 aignet)
                                (natp gatesimp))))
    (b* (((mv lit strash aignet)
          (aignet-hash-and (lit-negate f0) (lit-negate f1) strash gatesimp aignet)))
      (mv (lit-negate lit) strash aignet)))
  (local (in-theory (enable aignet-hash-or)))

  (def-aignet-frame aignet-hash-or)

  (defthm litp-aignet-hash-or
    (litp (mv-nth 0 (aignet-hash-or lit1 lit2 strash gatesimp aignet))))

  (defthm aignet-litp-aignet-hash-or
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet)
                   (aignet-hash-or lit1 lit2 strash gatesimp aignet)))
               (aignet-litp lit aignet))))

  (definlined aignet-hash-mux (c tb fb strash gatesimp aignet)
    (declare (xargs :stobjs (strash aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp c aignet)
                                (aignet-litp tb aignet)
                                (aignet-litp fb aignet)
                                (natp gatesimp))))
    (b* ((c (aignet-lit-fix c aignet))
         (tb (aignet-lit-fix tb aignet))
         (fb (aignet-lit-fix fb aignet))
         ((mv c-tb strash aignet)
          (aignet-hash-and c tb strash gatesimp aignet))
         ((mv nc-fb strash aignet)
          (aignet-hash-and (lit-negate c) fb strash gatesimp aignet)))
      (aignet-hash-or c-tb nc-fb strash gatesimp aignet)))

  (local (in-theory (enable aignet-hash-mux)))

  (def-aignet-frame aignet-hash-mux)

  (defthm litp-aignet-hash-mux
    (litp (mv-nth 0 (aignet-hash-mux c tb fb strash gatesimp aignet))))

  (defthm aignet-litp-aignet-hash-mux
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet)
                   (aignet-hash-mux c tb fb strash gatesimp aignet)))
               (aignet-litp lit aignet))))

  (definlined aignet-hash-xor (f0 f1 strash gatesimp aignet)
    (declare (xargs :stobjs (strash aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-litp f0 aignet)
                                (aignet-litp f1 aignet)
                                (natp gatesimp))))
    (aignet-hash-mux f0 (lit-negate f1) f1 strash gatesimp aignet))
  (local (in-theory (enable aignet-hash-xor)))

  (def-aignet-frame aignet-hash-xor)

  (defthm litp-aignet-hash-xor
    (litp (mv-nth 0 (aignet-hash-xor lit1 lit2 strash gatesimp aignet))))

  (defthm aignet-litp-aignet-hash-xor
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet)
                   (aignet-hash-xor lit1 lit2 strash gatesimp aignet)))
               (aignet-litp lit aignet)))
    :hints(("Goal" :in-theory (disable aignet-hash-mux))))

  (def-aignet-preservation-thms aignet-hash-and)
  (def-aignet-preservation-thms aignet-hash-or)
  (def-aignet-preservation-thms aignet-hash-mux)

  (defthm lit-eval-of-aignet-hash-and
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet1)
                   (aignet-hash-and lit1 lit2 strash gatesimp aignet)))
               (equal (lit-eval lit in-vals reg-vals aignet1)
                      (b-and (lit-eval lit1 in-vals reg-vals aignet)
                                   (lit-eval lit2 in-vals reg-vals aignet)))))
    :hints(("Goal" :in-theory (enable eval-and-of-lits))))

  (defthm lit-eval-of-aignet-hash-or
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet1)
                   (aignet-hash-or lit1 lit2 strash gatesimp aignet)))
               (equal (lit-eval lit in-vals reg-vals aignet1)
                      (b-ior (lit-eval lit1 in-vals reg-vals aignet)
                                   (lit-eval lit2 in-vals reg-vals aignet)))))
    :hints(("Goal" :in-theory (enable eval-and-of-lits
                                      b-ior b-and
                                      b-not))))

  (local (in-theory (disable aignet-hash-and aignet-hash-or)))

  (defthm lit-eval-of-aignet-hash-mux
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet1)
                   (aignet-hash-mux c tb fb strash gatesimp aignet)))
               (equal (lit-eval lit in-vals reg-vals aignet1)
                      (b-ior (b-and
                                    (lit-eval c in-vals reg-vals aignet)
                                    (lit-eval tb in-vals reg-vals aignet))
                                   (b-and
                                    (b-not
                                     (lit-eval c in-vals reg-vals aignet))
                                    (lit-eval fb in-vals reg-vals aignet)))))))

  (local (in-theory (disable aignet-hash-mux)))
  (def-aignet-preservation-thms aignet-hash-xor)

  (defthm lit-eval-of-aignet-hash-xor
    (implies (aignet-well-formedp aignet)
             (b* (((mv lit & aignet1)
                   (aignet-hash-xor lit1 lit2 strash gatesimp aignet)))
               (equal (lit-eval lit in-vals reg-vals aignet1)
                      (b-xor (lit-eval lit1 in-vals reg-vals aignet)
                                   (lit-eval lit2 in-vals reg-vals aignet)))))
    :hints(("Goal" :in-theory (enable b-xor
                                      b-ior b-and
                                      equal-1-to-bitp)))))

(defsection combinational-sim
  (defstobj-clone aignet-cis bitarr :strsubst (("BIT" . "AIGNET-CI")))
  (defstobj-clone aignet-cos bitarr :strsubst (("BIT" . "AIGNET-CO")))

  (local (in-theory (disable acl2::aignetp len true-listp)))

  (defiteration aignet-eval-comb-loop (aignet-cis aignet-cos aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet-cis aignet-cos aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (<= (+ (num-ins aignet) (num-regs aignet))
                                    (bits-length aignet-cis))
                                (<= (+ (num-outs aignet) (num-regs aignet))
                                    (bits-length aignet-cos)))))
    (b* ((n (lnfix n))
         (nid (to-id n))
         (slot0 (get-node-slot nid 0 aignet))
         (type (snode->type slot0))
         (aignet-vals
          (aignet-seq-case
           type (io-id->regp nid aignet)
           :gate  (b* ((f0 (snode-gate->fanin0 slot0))
                       (f1 (gate-id->fanin1 nid aignet))
                       (v0 (aignet-eval-lit f0 aignet-vals))
                       (v1 (aignet-eval-lit f1 aignet-vals))
                       (val (mbe :logic (if (gate-orderedp nid aignet)
                                            (b-and v0 v1)
                                          0)
                                 :exec (b-and v0 v1))))
                    (set-id->bit nid val aignet-vals))
           :pi    (b* ((innum (io-id->ionum nid aignet))
                       (val (get-bit innum aignet-cis)))
                    (set-id->bit nid val aignet-vals))
           :ro    (b* ((regnum (io-id->ionum nid aignet))
                       (val (get-bit (+ (num-ins aignet) regnum) aignet-cis)))
                    (set-id->bit nid val aignet-vals))
           :co    (b* ((f0 (snode-co->fanin slot0))
                       (v0 (aignet-eval-lit f0 aignet-vals))
                       (val (mbe :logic (if (co-orderedp nid aignet)
                                            v0
                                          0)
                                 :exec v0)))
                    (set-id->bit nid val aignet-vals))
           :const (set-id->bit nid 0 aignet-vals)))
         (aignet-cos
          (cond ((and (int= type (out-type))
                      (int= (io-id->regp nid aignet) 0))
                 (set-bit (io-id->ionum nid aignet)
                          (get-id->bit nid aignet-vals)
                          aignet-cos))
                ((and (int= type (out-type))
                      (int= (io-id->regp nid aignet) 1)
                      (not (int= (id-val (regin-id->ro nid aignet)) 0)))
                 (set-bit (+ (num-outs aignet)
                             (io-id->ionum (regin-id->ro nid aignet) aignet))
                          (get-id->bit nid aignet-vals)
                          aignet-cos))
                ((and (int= type (in-type))
                      (int= (io-id->regp nid aignet) 1)
                      (int= nid (regnum->id (io-id->ionum nid aignet) aignet)))
                 (set-bit (+ (num-outs aignet)
                             (io-id->ionum nid aignet))
                          (get-id->bit nid aignet-vals)
                          aignet-cos))
                (t aignet-cos))))
      (mv aignet-vals aignet-cos))
    :returns (mv aignet-vals aignet-cos)
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  ;; (defund aignet-eval-comb-iter (n aignet-cis aignet-cos aignet-vals aignet)
  ;;   (declare (type (integer 0 *) n)
  ;;            (xargs :stobjs (aignet-vals aignet-cis aignet-cos aignet)
  ;;                   :guard (and (aignet-well-formedp aignet)
  ;;                               (aignet-iterator-p n aignet)
  ;;                               (bitarr-sizedp aignet-vals aignet)
  ;;                               (<= (+ (num-ins aignet) (num-regs aignet))
  ;;                                   (bits-length aignet-cis))
  ;;                               (<= (+ (num-outs aignet) (num-regs aignet))
  ;;                                   (bits-length aignet-cos)))
  ;;                   :measure (nfix (- (nfix (num-nodes aignet))
  ;;                                     (nfix n)))))
  ;;   (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet))
  ;;                                  (nfix n)))
  ;;                    :exec (int= n (num-nodes aignet))))
  ;;         (mv aignet-vals aignet-cos))
  ;;        (n (lnfix n))
  ;;        (nid (to-id n))
  ;;        (slot0 (get-node-slot nid 0 aignet))
  ;;        (type (snode->type slot0))
  ;;        (aignet-vals
  ;;         (aignet-seq-case
  ;;          type (io-id->regp nid aignet)
  ;;          :gate  (b* ((f0 (snode-gate->fanin0 slot0))
  ;;                      (f1 (gate-id->fanin1 nid aignet))
  ;;                      (v0 (aignet-eval-lit f0 aignet-vals))
  ;;                      (v1 (aignet-eval-lit f1 aignet-vals))
  ;;                      (val (mbe :logic (if (gate-orderedp nid aignet)
  ;;                                           (b-and v0 v1)
  ;;                                         0)
  ;;                                :exec (b-and v0 v1))))
  ;;                   (set-id->bit nid val aignet-vals))
  ;;          :pi    (b* ((innum (io-id->ionum nid aignet))
  ;;                      (val (get-bit innum aignet-cis)))
  ;;                   (set-id->bit nid val aignet-vals))
  ;;          :ro    (b* ((regnum (io-id->ionum nid aignet))
  ;;                      (val (get-bit (+ (num-ins aignet) regnum) aignet-cis)))
  ;;                   (set-id->bit nid val aignet-vals))
  ;;          :co    (b* ((f0 (snode-co->fanin slot0))
  ;;                      (v0 (aignet-eval-lit f0 aignet-vals))
  ;;                      (val (mbe :logic (if (co-orderedp nid aignet)
  ;;                                           v0
  ;;                                         0)
  ;;                                :exec v0)))
  ;;                   (set-id->bit nid val aignet-vals))
  ;;          :const (set-id->bit nid 0 aignet-vals)))
  ;;        (aignet-cos
  ;;         (cond ((and (int= type (out-type))
  ;;                     (int= (io-id->regp nid aignet) 0))
  ;;                (set-bit (io-id->ionum nid aignet)
  ;;                         (get-id->bit nid aignet-vals)
  ;;                         aignet-cos))
  ;;               ((and (int= type (out-type))
  ;;                     (int= (io-id->regp nid aignet) 1)
  ;;                     (not (int= (id-val (regin-id->ro nid aignet)) 0)))
  ;;                (set-bit (+ (num-outs aignet)
  ;;                            (io-id->ionum (regin-id->ro nid aignet) aignet))
  ;;                         (get-id->bit nid aignet-vals)
  ;;                         aignet-cos))
  ;;               ((and (int= type (in-type))
  ;;                     (int= (io-id->regp nid aignet) 1)
  ;;                     (int= nid (regnum->id (io-id->ionum nid aignet) aignet)))
  ;;                (set-bit (+ (num-outs aignet)
  ;;                            (io-id->ionum nid aignet))
  ;;                         (get-id->bit nid aignet-vals)
  ;;                         aignet-cos))
  ;;               (t aignet-cos))))
  ;;     (aignet-eval-comb-iter (+ 1 (lnfix n)) aignet-cis aignet-cos
  ;;                       aignet-vals aignet)))

  (local (in-theory (enable (:induction aignet-eval-comb-loop-iter))))

  (defthm aignet-eval-well-sizedp-after-aignet-eval-comb-loop-iter
    (implies (memo-tablep aignet-vals aignet)
             (memo-tablep (mv-nth 0 (aignet-eval-comb-loop-iter
                                                  n aignet-cis aignet-cos
                                                  aignet-vals aignet))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-comb-loop-iter n aignet-cis aignet-cos aignet-vals aignet))))

  (defiteration aignet-vals-copy-in-comb (aignet-cis aignet-vals aignet)
    (declare (xargs :stobjs (aignet-cis aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (<= (+ (num-ins aignet) (num-regs aignet))
                                    (bits-length aignet-cis)))))
    (b* ((n (lnfix n))
         ((unless (int= (id->type (to-id n) aignet) (in-type)))
          aignet-vals)
         (regp (int= (io-id->regp (to-id n) aignet) 1))
         (ionum (io-id->ionum (to-id n) aignet))
         (aignet-vals (set-id->bit (to-id n)
                                   (get-bit (+ (if regp (num-ins aignet) 0) ionum)
                                            aignet-cis)
                                   aignet-vals)))
      aignet-vals)
    :returns aignet-vals
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (local (in-theory (enable (:induction aignet-vals-copy-in-comb-iter))))

  (defthm aignet-eval-well-sizedp-after-aignet-vals-copy-in-comb-iter
    (implies (memo-tablep aignet-vals aignet)
             (memo-tablep (aignet-vals-copy-in-comb-iter
                                        n aignet-cis aignet-vals aignet)
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet))))))


  (defthm lookup-in-aignet-vals-copy-in-comb-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp (to-id m) aignet))
             (equal (nth m (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet))
                    (if (and (equal (id->type (to-id m) aignet) (in-type))
                             (< (nfix m) (nfix n)))
                        (get-bit (+ (if (int= (io-id->regp (to-id m) aignet) 1)
                                        (num-ins aignet)
                                      0)
                                    (io-id->ionum (to-id m) aignet))
                                 aignet-cis)
                      (nth m aignet-vals))))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet)))))
    :otf-flg t)

  (defcong nth-equiv nth-equiv (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet) 3
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet))))))


  (defthm aignet-vals-copy-in-comb-iter-of-update-prev
    (implies (and (<= (nfix n) (nfix m))
                  (aignet-well-formedp aignet))
             (equal (aignet-vals-copy-in-comb-iter
                     n aignet-cis (update-nth m v aignet-vals)
                     aignet)
                    (let ((aignet-vals (aignet-vals-copy-in-comb-iter
                                        n aignet-cis aignet-vals aignet)))
                      (update-nth m v aignet-vals))))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals aignet))))))

  (local (in-theory (e/d ((:induction aignet-eval-iter))
                         ((:definition aignet-eval-iter)))))

  (defthm aignet-eval-comb-loop-iter-vals-rw
    (implies (aignet-well-formedp aignet)
             (equal (mv-nth 0 (aignet-eval-comb-loop-iter n aignet-cis
                                                 aignet-cos aignet-vals aignet))
                    (aignet-eval-iter n
                                      (aignet-vals-copy-in-comb-iter
                                       n aignet-cis aignet-vals aignet)
                                      aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-comb-loop-iter n aignet-cis aignet-cos aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-eval-iter n aignet-vals aignet))
              (:free (aignet-vals)
               (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals
                                          aignet))))))


  (defiteration aignet-vals-copy-out-comb (aignet-cos aignet-vals aignet)
    (declare (xargs :stobjs (aignet-cos aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (<= (+ (num-regs aignet)
                                       (num-outs aignet))
                                    (bits-length aignet-cos)))))
    (b* ((id (to-id n))
         ((when (and (int= (id->type id aignet) (out-type))
                     (int= (io-id->regp id aignet) 0)))
          (b* ((ionum (io-id->ionum id aignet))
               (aignet-cos (set-bit ionum (get-id->bit id aignet-vals)
                                    aignet-cos)))
            aignet-cos))
         ((when (and (int= (id->type id aignet) (out-type))
                     (int= (io-id->regp id aignet) 1)
                     (not (int= (id-val (regin-id->ro id aignet)) 0))))
          (b* ((ionum (io-id->ionum (regin-id->ro id aignet) aignet))
               (aignet-cos (set-bit (+ (num-outs aignet) ionum)
                                    (get-id->bit id aignet-vals)
                                    aignet-cos)))
            aignet-cos))
         ((when (and (int= (id->type id aignet) (in-type))
                     (int= (io-id->regp id aignet) 1)
                     (int= id (regnum->id (io-id->ionum id aignet) aignet))))
          (b* ((ionum (io-id->ionum id aignet))
               (aignet-cos (set-bit (+ (num-outs aignet) ionum)
                                    (get-id->bit id aignet-vals)
                                    aignet-cos)))
            aignet-cos)))
      aignet-cos)
    :returns aignet-cos
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)


  (local (in-theory (enable (:induction aignet-vals-copy-out-comb-iter))))

  (defthm aignet-vals-copy-out-comb-iter-of-update-greater
    (implies (<= (nfix n) (nfix m))
             (equal (aignet-vals-copy-out-comb-iter
                     n aignet-cos (update-nth m val aignet-vals)
                     aignet)
                    (aignet-vals-copy-out-comb-iter
                     n aignet-cos aignet-vals aignet)))
  :hints ((acl2::just-induct-and-expand
           (aignet-vals-copy-out-comb-iter n aignet-cos aignet-vals aignet)
           :expand-others
           ((:free (aignet-vals)
             (aignet-vals-copy-out-comb-iter n aignet-cos aignet-vals aignet))))))

  (defthm aignet-eval-comb-loop-iter-outs-rw
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-nodes aignet)))
             (equal (mv-nth 1 (aignet-eval-comb-loop-iter n aignet-cis
                                                 aignet-cos aignet-vals
                                                 aignet))
                    (aignet-vals-copy-out-comb-iter
                     n aignet-cos
                     (aignet-eval-iter n
                                  (aignet-vals-copy-in-comb-iter
                                   n aignet-cis aignet-vals aignet)
                                  aignet)
                     aignet)))

    :hints ((acl2::just-induct-and-expand
             (aignet-eval-comb-loop-iter n aignet-cis aignet-cos aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-eval-iter n aignet-vals aignet))
              (:free (aignet-vals)
               (aignet-vals-copy-out-comb-iter n aignet-cos aignet-vals
                                           aignet))
              (:free (aignet-vals)
               (aignet-vals-copy-in-comb-iter n aignet-cis aignet-vals
                                              aignet))))))

  (defund aignet-eval-comb (aignet-cis aignet-cos aignet)
    (declare (xargs :stobjs (aignet-cis aignet-cos aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (<= (+ (num-regs aignet) (num-ins aignet))
                                    (bits-length aignet-cis)))))
    (b* (((local-stobjs aignet-vals)
          (mv aignet-vals aignet-cos))
         (aignet-vals (resize-bits (num-nodes aignet) aignet-vals))
         (aignet-cos (bitarr-clear aignet-cos))
         (aignet-cos (resize-bits (+ (num-regs aignet) (num-outs aignet))
                                  aignet-cos)))
      (aignet-eval-comb-loop aignet-cis aignet-cos aignet-vals aignet)))


  (defthm aignet-eval-comb-normalize-cos
    (implies (syntaxp (not (equal aignet-cos ''nil)))
             (equal (aignet-eval-comb aignet-cis aignet-cos aignet)
                    (aignet-eval-comb aignet-cis nil aignet)))
    :hints(("Goal" :in-theory (e/d (aignet-eval-comb))))))

(defsection sequential-sim
  (local (in-theory (enable acl2::make-list-ac-redef)))
  (acl2::def2darr aignet-frames
                  :prefix frames
                  :elt-type bit
                  :elt-typep bitp
                  :default-elt 0
                  :elt-fix acl2::bfix
                  :elt-guard (bitp x))

  (defstobj-clone aignet-frames-out aignet-frames :strsubst (("FRAMES" . "FRAMES-OUT")))

  (defiteration aignet-eval-frame (k aignet-frames aignet-frames-out aignet-vals aignet)
    (declare (type (integer 0 *) k)
             (xargs :stobjs (aignet-vals aignet-frames aignet-frames-out aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (< k (frames-nrows aignet-frames))
                                (<= (num-ins aignet) (frames-ncols
                                                      aignet-frames))
                                (< k (frames-nrows aignet-frames-out))
                                (<= (num-outs aignet)
                                    (frames-ncols aignet-frames-out)))))
    (b* ((n (lnfix n))
         (nid (to-id n))
         (slot0 (get-node-slot nid 0 aignet))
         (type (snode->type slot0))
         (aignet-vals
          (aignet-seq-case
           type (io-id->regp nid aignet)
           :gate  (b* ((f0 (snode-gate->fanin0 slot0))
                       (f1 (gate-id->fanin1 nid aignet))
                       (v0 (aignet-eval-lit f0 aignet-vals))
                       (v1 (aignet-eval-lit f1 aignet-vals))
                       (val (mbe :logic (if (gate-orderedp nid aignet)
                                            (b-and v0 v1)
                                          0)
                                 :exec (b-and v0 v1))))
                    (set-id->bit nid val aignet-vals))
           :pi    (b* ((innum (io-id->ionum nid aignet))
                       (val (frames-get2 k innum aignet-frames)))
                    (set-id->bit nid val aignet-vals))
           :ro    (b* ((ri (regnum->id (io-id->ionum nid aignet) aignet))
                       (val (get-id->bit ri aignet-vals)))
                    (set-id->bit nid val aignet-vals))
           :co    (b* ((f0 (snode-co->fanin slot0))
                       (v0 (aignet-eval-lit f0 aignet-vals))
                       (val (mbe :logic (if (co-orderedp nid aignet)
                                            v0
                                          0)
                                 :exec v0)))
                    (set-id->bit nid val aignet-vals))
           :const (set-id->bit nid 0 aignet-vals)))
         (aignet-frames-out
          (if (and (int= type (out-type))
                   (int= (io-id->regp nid aignet) 0))
              (frames-set2 k (io-id->ionum nid aignet)
                              (get-id->bit nid aignet-vals)
                              aignet-frames-out)
            aignet-frames-out)))
      (mv aignet-vals aignet-frames-out))
    :returns (mv aignet-vals aignet-frames-out)
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (defiteration aignet-eval-frame1 (aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet))))
    (b* ((n (lnfix n))
         (nid (to-id n))
         (slot0 (get-node-slot nid 0 aignet))
         (type (snode->type slot0))
         (aignet-vals
          (aignet-seq-case
           type (io-id->regp nid aignet)
           :gate  (b* ((f0 (snode-gate->fanin0 slot0))
                       (f1 (gate-id->fanin1 nid aignet))
                       (v0 (aignet-eval-lit f0 aignet-vals))
                       (v1 (aignet-eval-lit f1 aignet-vals))
                       (val (mbe :logic (if (gate-orderedp nid aignet)
                                            (b-and v0 v1)
                                          0)
                                 :exec (b-and v0 v1))))
                    (set-id->bit nid val aignet-vals))
           :pi    aignet-vals
           :ro    (b* ((ri (regnum->id (io-id->ionum nid aignet) aignet))
                       (val (get-id->bit ri aignet-vals)))
                    (set-id->bit nid val aignet-vals))
           :co    (b* ((f0 (snode-co->fanin slot0))
                       (v0 (aignet-eval-lit f0 aignet-vals))
                       (val (mbe :logic (if (co-orderedp nid aignet)
                                            v0
                                          0)
                                 :exec v0)))
                    (set-id->bit nid val aignet-vals))
           :const (set-id->bit nid 0 aignet-vals))))
      aignet-vals)
      :returns aignet-vals
      :index n
      :last (num-nodes aignet)
      :package aignet::foo)


  (local (in-theory (enable (:induction aignet-eval-frame-iter)
                            (:induction aignet-eval-frame1-iter))))

  (defthm aignet-eval-well-sizedp-after-aignet-eval-frame-iter
    (implies (memo-tablep aignet-vals aignet)
             (memo-tablep (mv-nth 0 (aignet-eval-frame-iter
                                                  n k aignet-frames aignet-frames-out
                                                  aignet-vals aignet))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-frame-iter n k aignet-frames aignet-frames-out aignet-vals
                                aignet))))

  (defthm aignet-eval-well-sizedp-after-aignet-eval-frame1-iter
    (implies (memo-tablep aignet-vals aignet)
             (memo-tablep (aignet-eval-frame1-iter
                                        n aignet-vals aignet)
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-frame1-iter n aignet-vals aignet))))


  (defiteration aignet-vals-update-ri->ros (aignet-vals aignet)
    (declare (xargs :stobjs (aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet))))
    (b* ((n (lnfix n))
         ((unless (and (int= (id->type (to-id n) aignet) (in-type))
                       (int= (io-id->regp (to-id n) aignet) 1)))
          aignet-vals)
         (ri (regnum->id (io-id->ionum (to-id n) aignet) aignet))
         (aignet-vals (set-id->bit (to-id n)
                                (get-id->bit ri aignet-vals)
                                aignet-vals)))
      aignet-vals)
    :returns aignet-vals
    :index n
    :last (num-nodes aignet))

  (local (in-theory (enable (:induction aignet-vals-update-ri->ros-iter))))

  (defthm aignet-eval-well-sizedp-after-aignet-vals-update-ri->ros-iter
    (implies (memo-tablep aignet-vals aignet)
             (memo-tablep (aignet-vals-update-ri->ros-iter n
                                                                   aignet-vals
                                                                   aignet)
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-update-ri->ros-iter n aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-update-ri->ros-iter n aignet-vals aignet))))))

  (defthm reg-id-is-gte-reg-out
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id aignet)
                  (equal (id->type id aignet) (in-type))
                  (equal (io-id->regp id aignet) 1))
             (<= (id-val id)
                 (id-val (nth-id (io-node->ionum (nth-node id (nth *nodesi*
                                                                   aignet)))
                                 (nth *regsi* aignet)))))
    :rule-classes :linear)

  (defthm nth-of-update-ri->ros-greater
    (implies (<= (nfix n) (nfix m))
             (equal (nth m (aignet-vals-update-ri->ros-iter
                                         n aignet-vals aignet))
                    (nth m aignet-vals)))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-update-ri->ros-iter n aignet-vals aignet))))

  (defthm lookup-in-aignet-vals-update-ri->ros-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp (to-id k) aignet))
             (equal (nth k (aignet-vals-update-ri->ros-iter n aignet-vals aignet))
                    (if (and (equal (id->type (to-id k) aignet) (in-type))
                             (equal (io-id->regp (to-id k) aignet) 1)
                             (< (nfix k) (nfix n)))
                        (acl2::bfix
                         (nth (id-val (regnum->id (io-id->ionum (to-id k) aignet) aignet))
                              aignet-vals))
                      (nth k aignet-vals))))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-update-ri->ros-iter n aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-update-ri->ros-iter n aignet-vals aignet))))
            )
    :otf-flg t)

  ;; (local
  ;;  (defun-nx aignet-vals-update-ri->ros-iter-ind (n aignet-vals aignet-vals2 aignet)
  ;;    (declare (xargs :measure (nfix (- (nfix (num-nodes aignet))
  ;;                                      (nfix n)))))
  ;;    (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet))
  ;;                                   (nfix n)))
  ;;                     :exec (int= n (num-nodes aignet))))
  ;;          aignet-vals)
  ;;         (n (lnfix n))
  ;;         ((unless (and (int= (id->type (to-id n) aignet) (in-type))
  ;;                       (int= (io-id->regp (to-id n) aignet) 1)))
  ;;          (aignet-vals-update-ri->ros-iter-ind (1+ n) aignet-vals aignet-vals2 aignet))
  ;;         (ri (regnum->id (io-id->ionum (to-id n) aignet) aignet))
  ;;         (aignet-vals (set-id->bit (to-id n)
  ;;                                   (get-id->bit ri aignet-vals)
  ;;                                   aignet-vals))
  ;;         (aignet-vals2 (set-id->bit (to-id n)
  ;;                                    (get-id->bit ri aignet-vals)
  ;;                                    aignet-vals2)))
  ;;      (aignet-vals-update-ri->ros-iter-ind (1+ n) aignet-vals aignet-vals2 aignet))))

  (defcong nth-equiv nth-equiv (aignet-vals-update-ri->ros-iter n aignet-vals aignet) 2
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-update-ri->ros-iter n aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-update-ri->ros-iter n aignet-vals aignet))))))


;;   (defthm aignet-vals-update-ri->ros-iter-of-update-prev
;;     (implies (and (aignet-well-formedp aignet)
;;                   (<= (nfix n) (nfix m)))
;;              (equal (aignet-vals-update-ri->ros-iter
;;                      n (
;;                                    (update-nth m v aignet-vals)
;;                                    aignet-vals)
;;                      aignet)
;;                     (let ((aignet-vals (aignet-vals-update-ri->ros-iter
;;                                      n aignet-vals aignet)))
;;                       (update-nth *bitsi*
;;                                   (update-nth m v aignet-vals)
;;                                   aignet-vals))))
;;     :hints ((acl2::just-induct-and-expand
;;              (aignet-vals-update-ri->ros-iter n aignet-vals aignet)
;;              :expand-others
;;              ((:free (aignet-vals)
;;                (aignet-vals-update-ri->ros-iter n aignet-vals aignet))))))
;; )


  (defiteration aignet-vals-copy-in-frame (k aignet-frames aignet-vals aignet)
    (declare (type (integer 0 *) k)
             (xargs :stobjs (aignet-frames aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (< k (frames-nrows aignet-frames))
                                (<= (num-ins aignet) (frames-ncols aignet-frames)))))
    (b* ((n (lnfix n))
         ((unless (and (int= (id->type (to-id n) aignet) (in-type))
                       (int= (io-id->regp (to-id n) aignet) 0)))
          aignet-vals)
         (innum (io-id->ionum (to-id n) aignet))
         (aignet-vals (set-id->bit (to-id n)
                                   (frames-get2 k innum aignet-frames)
                                   aignet-vals)))
      aignet-vals)
    :returns aignet-vals
    :index n
    :last (num-nodes aignet))

  (local (in-theory (enable (:induction aignet-vals-copy-in-frame-iter))))

  (defthm aignet-eval-well-sizedp-after-aignet-vals-copy-in-frame-iter
    (implies (memo-tablep aignet-vals aignet)
             (memo-tablep (aignet-vals-copy-in-frame-iter
                                        n k aignet-frames aignet-vals aignet)
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet))))))


  (defthm lookup-in-aignet-vals-copy-in-frame-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp (to-id m) aignet))
             (equal (nth m (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet))
                    (if (and (equal (id->type (to-id m) aignet) (in-type))
                             (equal (io-id->regp (to-id m) aignet) 0)
                             (< (nfix m) (nfix n)))
                        (frames-get2 k (io-id->ionum (to-id m) aignet)
                                     aignet-frames)
                      (nth m aignet-vals))))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet))))
            ;; (and stable-under-simplificationp
            ;;      '(:use ((:instance aignet-well-formedp-in-rw
            ;;               (n (to-id m))))
            ;;        :in-theory (disable aignet-well-formedp-in-rw)))
            )
    :otf-flg t)

  ;; (local
  ;;  (defun-nx aignet-vals-copy-in-frame-iter-ind (n k aignet-frames aignet-vals aignet-vals2 aignet)
  ;;    (declare (xargs :measure (nfix (- (nfix (num-nodes aignet))
  ;;                                      (nfix n)))))
  ;;    (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet))
  ;;                                   (nfix n)))
  ;;                     :exec (int= n (num-nodes aignet))))
  ;;          aignet-vals)
  ;;         (n (lnfix n))
  ;;         ((unless (and (int= (id->type (to-id n) aignet) (in-type))
  ;;                       (int= (io-id->regp (to-id n) aignet) 0)))
  ;;          (aignet-vals-copy-in-frame-iter-ind (1+ n) k aignet-frames aignet-vals aignet-vals2 aignet))
  ;;         (innum (io-id->ionum (to-id n) aignet))
  ;;         (aignet-vals (set-id->bit (to-id n)
  ;;                                   (frames-get2 k innum aignet-frames)
  ;;                                   aignet-vals))
  ;;         (aignet-vals2 (set-id->bit (to-id n)
  ;;                                    (frames-get2 k innum aignet-frames)
  ;;                                    aignet-vals2)))
  ;;      (aignet-vals-copy-in-frame-iter-ind (1+ n) k aignet-frames aignet-vals aignet-vals2 aignet))))

  (defcong nth-equiv nth-equiv (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet) 4
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet))))))

  (defthm aignet-vals-copy-in-frame-iter-of-update-prev
    (implies (and (<= (nfix n) (nfix m))
                  (aignet-well-formedp aignet))
             (equal (aignet-vals-copy-in-frame-iter
                     n k aignet-frames
                     (update-nth m v aignet-vals)
                     aignet)
                    (let ((aignet-vals (aignet-vals-copy-in-frame-iter
                                        n k aignet-frames aignet-vals aignet)))
                      (update-nth m v aignet-vals))))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet))))))

  (local (in-theory (disable (:definition aignet-eval-iter))))

  (local (defthm aignet-eval-nth-previous-rw
           (implies (and (equal aignet-vals1 (aignet-eval-iter n aignet-vals aignet))
                         (<= (nfix n) (nfix m)))
                    (equal (nth m aignet-vals1)
                           (nth m aignet-vals)))))

  (defthm aignet-eval-frame-iter-vals-rw
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (nth *num-nodes* aignet)))
             (equal (mv-nth 0 (aignet-eval-frame-iter n k aignet-frames
                                                 aignet-frames-out aignet-vals aignet))
                    (aignet-eval-iter n
                                 (aignet-vals-copy-in-frame-iter
                                  n k aignet-frames
                                  (aignet-vals-update-ri->ros-iter
                                   n aignet-vals aignet)
                                  aignet)
                                 aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-frame-iter n k aignet-frames aignet-frames-out aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-eval-iter n aignet-vals aignet))
              (:free (aignet-vals)
               (aignet-vals-update-ri->ros-iter n aignet-vals aignet))
              (:free (aignet-vals)
               (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals
                                          aignet))))))

  (local (in-theory (enable (:induction aignet-eval-frame1-iter))))

  (defthm aignet-eval-frame1-iter-rw
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-nodes aignet)))
             (equal (aignet-eval-frame1-iter n aignet-vals aignet)
                    (aignet-eval-iter n
                                 (aignet-vals-update-ri->ros-iter
                                  n aignet-vals aignet)
                                 aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-eval-frame1-iter n aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-eval-iter n aignet-vals aignet))
              (:free (aignet-vals)
               (aignet-vals-update-ri->ros-iter n aignet-vals aignet))))))


  (defiteration aignet-vals-copy-out-frame (k aignet-frames-out aignet-vals aignet)
    (declare (type (integer 0 *) k)
             (xargs :stobjs (aignet-frames-out aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (< k (frames-nrows aignet-frames-out))
                                (<= (num-outs aignet) (frames-ncols aignet-frames-out)))))
    (b* ((id (to-id n))
         ((unless (and (int= (id->type id aignet) (out-type))
                       (int= (io-id->regp id aignet) 0)))
          aignet-frames-out)
         (aignet-frames-out (frames-set2 k (io-id->ionum id aignet)
                                         (get-id->bit id aignet-vals)
                                         aignet-frames-out)))
      aignet-frames-out)
    :returns aignet-frames-out
    :index n
    :last (num-nodes aignet))

  (local (in-theory (enable (:induction aignet-vals-copy-out-frame-iter))))

  (defthm aignet-vals-copy-out-frame-iter-of-update-prev
    (implies (<= (nfix n) (nfix m))
             (equal (aignet-vals-copy-out-frame-iter
                     n k aignet-frames-out (update-nth m v                                                               aignet-vals)
                     aignet)
                    (aignet-vals-copy-out-frame-iter
                     n k aignet-frames-out
                     aignet-vals aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-out-frame-iter
              n k aignet-frames-out
              aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-vals-copy-out-frame-iter
                n k aignet-frames-out
                aignet-vals aignet))))))

  (defthm aignet-eval-frame-iter-outs-rw
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-nodes aignet)))
             (equal (mv-nth 1 (aignet-eval-frame-iter n k aignet-frames
                                                 aignet-frames-out aignet-vals
                                                 aignet))
                    (aignet-vals-copy-out-frame-iter
                     n k aignet-frames-out
                     (aignet-eval-iter n
                                  (aignet-vals-copy-in-frame-iter
                                   n k aignet-frames
                                   (aignet-vals-update-ri->ros-iter
                                    n aignet-vals aignet)
                                   aignet)
                                  aignet)
                     aignet)))

    :hints ((acl2::just-induct-and-expand
             (aignet-eval-frame-iter n k aignet-frames aignet-frames-out aignet-vals aignet)
             :expand-others
             ((:free (aignet-vals)
               (aignet-eval-iter n aignet-vals aignet))
              (:free (aignet-vals)
               (aignet-vals-update-ri->ros-iter n aignet-vals aignet))
              (:free (aignet-vals)
               (aignet-vals-copy-out-frame-iter n k aignet-frames-out aignet-vals
                                           aignet))
              (:free (aignet-vals)
               (aignet-vals-copy-in-frame-iter n k aignet-frames aignet-vals aignet))))))

  (local (in-theory (enable (:induction aignet-vals-copy-out-frame-iter))))

  (defthm car-of-aignet-vals-copy-out-frame-iter
    (equal (car (aignet-vals-copy-out-frame-iter
                 n k aignet-frames-out aignet-vals aignet))
           (car aignet-frames-out))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-out-frame-iter
                 n k aignet-frames-out aignet-vals aignet))))

  (defthm len-cdr-of-aignet-vals-copy-out-frame-iter
    (implies (< (nfix k) (len (cdr aignet-frames-out)))
             (equal (len (cdr (aignet-vals-copy-out-frame-iter
                               n k aignet-frames-out aignet-vals aignet)))
                    (len (cdr aignet-frames-out))))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-copy-out-frame-iter
                 n k aignet-frames-out aignet-vals aignet))))



  (defiteration aignet-eval-seq-loop (aignet-frames aignet-frames-out aignet-vals aignet)
    (declare (xargs :stobjs (aignet-frames aignet-frames-out aignet-vals aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (bitarr-sizedp aignet-vals aignet)
                                (<= (num-ins aignet) (frames-ncols aignet-frames))
                                (int= (frames-nrows aignet-frames-out)
                                      (frames-nrows aignet-frames))
                                (<= (num-outs aignet) (frames-ncols
                                                       aignet-frames-out)))))
    (b* (((mv aignet-vals aignet-frames-out)
          (aignet-eval-frame k aignet-frames aignet-frames-out
                             aignet-vals aignet)))
      (mv aignet-vals aignet-frames-out))
    :index k
    :last (frames-nrows aignet-frames)
    :returns (mv aignet-vals aignet-frames-out))


  (defund aignet-eval-seq (aignet-frames aignet-frames-out aignet)
    (declare (xargs :stobjs (aignet-frames aignet-frames-out aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (<= (num-ins aignet) (frames-ncols
                                                      aignet-frames)))))
    (b* (((local-stobjs aignet-vals)
          (mv aignet-vals aignet-frames-out))
         (aignet-vals (resize-bits (num-nodes aignet) aignet-vals))
         (aignet-frames-out (frames-set-width (num-outs aignet)
                                              aignet-frames-out))
         (aignet-frames-out (frames-resize (frames-nrows aignet-frames)
                                           aignet-frames-out)))
      (aignet-eval-seq-loop aignet-frames aignet-frames-out aignet-vals aignet)))

  (local (in-theory (enable acl2::resize-list-when-empty)))
  (defthm aignet-eval-seq-normalize-frames-out
    (implies (syntaxp (not (equal aignet-frames-out ''nil)))
             (equal (aignet-eval-seq aignet-frames aignet-frames-out aignet)
                    (aignet-eval-seq aignet-frames nil aignet)))
    :hints(("Goal" :in-theory (e/d (aignet-eval-seq))))))






