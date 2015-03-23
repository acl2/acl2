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

(include-book "aignet-exec")

(include-book "aignet-logic-interface")

(include-book "centaur/misc/absstobjs" :dir :system)
(include-book "tools/clone-stobj" :dir :system)

(local (include-book "aignet-exec-thms"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "clause-processors/generalize" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable set::double-containment)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           set::double-containment
                           set::sets-are-true-lists
                           make-list-ac)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index)))




(local
 (progn


   (defun-sk innums-correct (aignetc aigneta)
     (forall n
             (implies (< (nfix n) (aignet$a::num-ins aigneta))
                      (nat-equiv (nth n (nth aignet$c::*insi* aignetc))
                                (node-count (lookup-stype n (pi-stype) aigneta)))))
     :rewrite :direct)

   (in-theory (disable innums-correct))

   (defun-sk outnums-correct (aignetc aigneta)
     (forall n
             (implies (< (nfix n) (aignet$a::num-outs aigneta))
                      (nat-equiv (nth n (nth aignet$c::*outsi* aignetc))
                                (node-count (lookup-stype n (po-stype) aigneta)))))
     :rewrite :direct)

   (in-theory (disable outnums-correct))

   (defun-sk regnums-correct (aignetc aigneta)
     (forall
      n
      (implies
       (< (nfix n) (aignet$a::num-regs aigneta))
       (nat-equiv (nth n (nth aignet$c::*regsi* aignetc))
                 (aignet$a::regnum->id n aigneta))))
     :rewrite :direct)

   (in-theory (disable regnums-correct))
   (in-theory (enable aignet$c::regnum->id))

   


   (defsection nodes-correct
     (defun-sk nodes-correct (aignetc aigneta)
       (forall
        id
        (implies
         (and (natp id)
              (case-split (< id (aignet$c::num-nodes aignetc))))
         (let ((slot0 (aignet$c::id->slot id 0 aignetc))
               (slot1 (aignet$c::id->slot id 1 aignetc)))
           (and (equal (aignet$c::snode->type slot0)
                       (node->type
                        (car (lookup-id id aigneta))))
                (equal slot0 (mv-nth 0 (id-slots id aigneta)))
                (equal slot1 (mv-nth 1 (id-slots id aigneta)))
                (implies (equal (aignet$a::id->type id aigneta)
                                (out-type))
                         (equal (aignet$c::snode->fanin slot0)
                                (aignet$a::co-id->fanin id aigneta)))
                (implies (and (equal (aignet$a::id->type id aigneta)
                                     (in-type))
                              (equal (aignet$a::io-id->regp id aigneta)
                                     1))
                         (equal (aignet$c::snode->regid slot0)
                                (aignet$a::reg-id->nxst id aigneta)))
                (implies (equal (aignet$a::id->type id aigneta)
                                (gate-type))
                         (equal (aignet$c::snode->fanin slot0)
                                (aignet$a::gate-id->fanin0 id aigneta)))
                (equal (aignet$c::snode->phase slot1)
                       (aignet$a::id->phase id aigneta))
                (implies (or (equal (aignet$a::id->type id aigneta)
                                    (in-type))
                             (equal (aignet$a::id->type id aigneta)
                                    (out-type)))
                         (equal (aignet$c::snode->regp slot1)
                                (aignet$a::io-id->regp id aigneta)))
                (implies (or (equal (aignet$a::id->type id aigneta)
                                    (in-type))
                             (and (equal (aignet$a::id->type id aigneta)
                                         (out-type))
                                  (equal (aignet$a::io-id->regp id aigneta)
                                         0)))
                         (equal (aignet$c::snode->ionum slot1)
                                (aignet$a::io-id->ionum id aigneta)))
                (implies (and (equal (aignet$a::id->type id aigneta)
                                     (out-type))
                              (equal (aignet$a::io-id->regp id aigneta)
                                     1))
                         (equal (aignet$c::snode->regid slot1)
                                (aignet$a::nxst-id->reg id aigneta)))
                (implies (equal (aignet$a::id->type id aigneta)
                                (gate-type))
                         (equal (aignet$c::snode->fanin slot1)
                                (aignet$a::gate-id->fanin1 id aigneta)))))))
       :rewrite :direct)

     (in-theory (disable nodes-correct)))

   (local (in-theory (enable aignet$a::io-id->regp
                             aignet$a::co-id->fanin
                             aignet$a::gate-id->fanin0
                             aignet$a::gate-id->fanin1
                             aignet$a::io-id->ionum)))

   (defthm id->type-of-empty
     (equal (aignet$a::id->type x nil) 0)
     :hints(("Goal" :in-theory (enable aignet$a::id->type))))

   (defthm id->phase-of-empty
     (equal (aignet$a::id->phase x nil) 0)
     :hints(("Goal" :in-theory (enable aignet$a::id->phase))))

   (defthm io-id->regp-of-empty
     (equal (aignet$a::io-id->regp x nil) 0)
     :hints(("Goal" :in-theory (enable aignet$a::io-id->regp))))

   ;; (defthm aignet-regs-in-bounds-impl-regs-in-bounds
   ;;   (implies (and (aignet$c::aignet-regs-in-bounds aignet)
   ;;                 (equal count (aignet$c::num-regs aignet)))
   ;;            (aignet$c::regs-in-bounds count aignet))
   ;;   :hints(("Goal" :in-theory (enable aignet$c::aignet-regs-in-bounds))))
   
   (local (in-theory (enable aignet$a::id->type)))

   (defsection aignet-count-equivs
     (defund-nx aignet-count-equivs (aignetc aigneta)
       (and (equal (nth aignet$c::*num-nodes* aignetc)
                   (aignet$a::num-nodes aigneta))
            (equal (nth aignet$c::*num-ins* aignetc)
                   (aignet$a::num-ins aigneta))
            (equal (nth aignet$c::*num-regs* aignetc)
                   (aignet$a::num-regs aigneta))
            (equal (nth aignet$c::*num-nxsts* aignetc)
                   (aignet$a::num-nxsts aigneta))
            (equal (nth aignet$c::*num-outs* aignetc)
                   (aignet$a::num-outs aigneta))
            (equal (nth aignet$c::*num-gates* aignetc)
                   (aignet$a::num-gates aigneta))))

     (local (in-theory (enable aignet-count-equivs)))
     (defthm aignet-count-equivs-implies
       (implies (aignet-count-equivs aignetc aigneta)
                (and (equal (nth aignet$c::*num-nodes* aignetc)
                            (aignet$a::num-nodes aigneta))
                     (equal (nth aignet$c::*num-ins* aignetc)
                            (aignet$a::num-ins aigneta))
                     (equal (nth aignet$c::*num-regs* aignetc)
                            (aignet$a::num-regs aigneta))
                     (equal (nth aignet$c::*num-nxsts* aignetc)
                            (aignet$a::num-nxsts aigneta))
                     (equal (nth aignet$c::*num-outs* aignetc)
                            (aignet$a::num-outs aigneta))
                     (equal (nth aignet$c::*num-gates* aignetc)
                            (aignet$a::num-gates aigneta)))))

     (defthm aignet-count-equivs-unhide
       (equal (hide (aignet-count-equivs aignetc aigneta))
              (and (equal (nth aignet$c::*num-nodes* aignetc)
                          (aignet$a::num-nodes aigneta))
                   (equal (nth aignet$c::*num-ins* aignetc)
                          (aignet$a::num-ins aigneta))
                   (equal (nth aignet$c::*num-regs* aignetc)
                          (aignet$a::num-regs aigneta))
                   (equal (nth aignet$c::*num-nxsts* aignetc)
                          (aignet$a::num-nxsts aigneta))
                   (equal (nth aignet$c::*num-outs* aignetc)
                          (aignet$a::num-outs aigneta))
                   (equal (nth aignet$c::*num-gates* aignetc)
                          (aignet$a::num-gates aigneta))))
       :hints (("goal" :Expand ((:free (x) (hide x)))))))


   (defsection aignet-corr
     (defun-nx aignet-corr (aignetc aigneta)
       (and (aignet$a::aignet-well-formedp aigneta)
            (aignet$c::aignet-sizes-ok aignetc)
            ;; (aignet$c::aignet-regs-in-bounds aignetc)
            (aignet-count-equivs aignetc aigneta)
            (innums-correct aignetc aigneta)
            (outnums-correct aignetc aigneta)
            (regnums-correct aignetc aigneta)
            (nodes-correct aignetc aigneta)))
     (defthm aignet-corr-in-hide
       (equal (hide (aignet-corr aignetc aigneta))
              (and (aignet$a::aignet-well-formedp aigneta)
                   (aignet$c::aignet-sizes-ok aignetc)
                   ;; (aignet$c::aignet-regs-in-bounds aignetc)
                   (aignet-count-equivs aignetc aigneta)
                   (innums-correct aignetc aigneta)
                   (outnums-correct aignetc aigneta)
                   (regnums-correct aignetc aigneta)
                   (nodes-correct aignetc aigneta)))
       :hints (("goal" :expand ((:free (x) (hide x)))))))


   (local (in-theory (enable aignet$a::innum->id
                             aignet$a::outnum->id
                             aignet$a::regnum->id)))

   (defthm nat-equiv-of-nth-in-empty-nodes
     (nat-equiv (nth n '(0 0))
                0)
     :hints(("Goal" :in-theory (enable nth))))


   ;; (defthm equal-plus-neg1
   ;;   (implies (and (integerp n) (integerp m))
   ;;            (equal (equal n (+ -1 m))
   ;;                   (equal (+ 1 n) m))))

   (set-default-hints
    '((and stable-under-simplificationp
           (let ((last (car (last clause))))
             (and (member (car last) '(innums-correct
                                       outnums-correct
                                       regnums-correct
                                       nodes-correct
                                       aignet-count-equivs))
                  `(:expand (,last)))))
      (and stable-under-simplificationp
           '(:expand ((:free (a b c stype)
                       (lookup-stype a stype (cons b c)))
                      (:free (a b c)
                       (lookup-reg->nxst a (cons b c)))
                      (:free (a b c)
                       (lookup-id a (cons b c)))
                      (:free (b)
                       (aignet$a::id->phase (+ 1 (node-count aignet)) b))
                      (:free (a b)
                       (aignet$a::lit->phase a b))
                      (:free (a b)
                       (aignet-litp a b))
                      (:free (id aignet)
                       (id-slots id aignet)))))
      (and stable-under-simplificationp
           (let ((last (car (last clause))))
             (and (member (car last) '(;; aignet$c::aignet-regs-in-bounds
                                       aignet$c::aignet-sizes-ok
                                       aignet-idp))
                  `(:expand (,last)))))
      (and stable-under-simplificationp
           (let ((witness (acl2::find-call-lst
                           'nodes-correct-witness
                           clause)))
             `(:clause-processor
               (acl2::simple-generalize-cp
                clause '((,witness . nid))))))
      (and stable-under-simplificationp
           '(:cases ((equal (nfix nid) (+ 1 (node-count aignet)))
                     (< (nfix nid) (+ 1 (node-count aignet))))))
      ;; (and stable-under-simplificationp
      ;;      '(:expand ((:free (a b)
      ;;                  (aignet$a::id->phase nid (cons a b))))))
      (and stable-under-simplificationp
           '(:in-theory (enable aignet-idp
                                typecodep)))

      (and stable-under-simplificationp
           '(:in-theory (enable aignet$c::id->slot)))
      ))

   ;; (local (in-theory (disable aignet$c::aignet-regs-in-bounds)))

   (local (in-theory (e/d* (aignet$c::aignet-frame-thms
                            aignet$a::id->type))))

   ;; (defthm <-0-of-to-id
   ;;   (equal (< 0 (to-id x))
   ;;          (< 0 (nfix x))))


   ;; (defthm equal-0-of-to-id
   ;;   (equal (equal 0 (to-id x))
   ;;          (equal 0 (nfix x)))
   ;;   :hints (("goal" :use ((:instance <-0-of-to-id))
   ;;            :in-theory (disable <-0-of-to-id))))


   (local (in-theory (enable bitops::ELIM-PLUS-ONE)))

   (defthm |(< (* 2 x) (+ 2 (* 2 y)))|
     (iff (< (* 2 x) (+ 2 (* 2 y)))
          (< x (+ 1 y))))

   (defthm even-is-not-odd
     (implies (and (integerp a) (integerp b))
              (not (equal (+ 1 (* 2 a)) (* 2 b))))
     :hints (("goal" :use ((:theorem
                            (implies
                             (and (integerp a)
                                  (integerp b))
                             (not (equal (acl2::logcar (+ 1 (* 2 a)))
                                         (acl2::logcar (* 2 b))))))))))

   (defthm even-is-not-odd-2
     (implies (and (integerp a) (integerp b))
              (not (equal (+ 1 (* 2 a)) (+ 2 (* 2 b)))))
     :hints (("goal" :use ((:instance even-is-not-odd
                            (b (+ 1 b)))))))

   (in-theory (disable (force)))


   (local (defthm stype-const-when-not-others
            (implies (and (not (equal (stype x) (gate-stype)))
                          (not (equal (ctype (stype x)) (in-ctype)))
                          (not (equal (ctype (stype x)) (out-ctype))))
                     (equal (stype x) (const-stype)))
            :hints(("Goal" :in-theory (enable stype stype-fix stypep)))))
   
   (local (defthm id->phase-when-const
            (implies (equal (stype (car (lookup-id id aignet))) (const-stype))
                     (equal (aignet$a::id->phase id aignet) 0))
            :hints(("Goal" :in-theory (enable aignet$a::id->phase)))))

   (local (defthm id->phase-when-in
            (implies (equal (ctype (stype (car (lookup-id id aignet)))) (in-ctype))
                     (equal (aignet$a::id->phase id aignet) 0))
            :hints(("Goal" :in-theory (enable aignet$a::id->phase)))))

   (local (defthm node-count-lookup-reg->nxst-out-of-bounds
            (implies (< (node-count aignet) (nfix id))
                     (equal (node-count (lookup-reg->nxst id aignet))
                            0))))))

(acl2::defabsstobj-events aignet
  :concrete aignet$c::aignet
  :corr-fn aignet-corr
  :recognizer (aignetp :logic aignet$a::aignet-well-formedp
                       :exec aignet$c::aignetp)
  :creator (acl2::create-aignet :logic aignet$a::create-aignet
                                :exec aignet$c::create-aignet)
  :exports ((num-nodes :logic aignet$a::num-nodes
                       :exec aignet$c::num-nodes)
            (num-ins :logic aignet$a::num-ins
                     :exec aignet$c::num-ins)
            (num-regs :logic aignet$a::num-regs
                      :exec aignet$c::num-regs)
            (num-outs :logic aignet$a::num-outs
                      :exec aignet$c::num-outs)
            (num-nxsts :logic aignet$a::num-nxsts
                        :exec aignet$c::num-nxsts)
            (num-gates :logic aignet$a::num-gates
                       :exec aignet$c::num-gates)
            
            (fanin-litp :logic aignet$a::fanin-litp
                         :exec aignet$c::fanin-litp$inline)
            (id-existsp :logic aignet$a::id-existsp
                        :exec aignet$c::id-existsp$inline)

            (innum->id :logic aignet$a::innum->id
                       :exec aignet$c::innum->id$inline)
            (outnum->id :logic aignet$a::outnum->id
                        :exec aignet$c::outnum->id$inline)
            (regnum->id :logic aignet$a::regnum->id
                        :exec aignet$c::regnum->id$inline)
            (id->type :logic aignet$a::id->type
                      :exec aignet$c::id->type$inline)
            (io-id->regp :logic aignet$a::io-id->regp
                         :exec aignet$c::id->regp$inline)
            (io-id->ionum :logic aignet$a::io-id->ionum
                          :exec aignet$c::id->ionum$inline)
            (co-id->fanin :logic aignet$a::co-id->fanin
                          :exec aignet$c::id->fanin0$inline)
            (gate-id->fanin0 :logic aignet$a::gate-id->fanin0
                             :exec aignet$c::id->fanin0$inline)
            (gate-id->fanin1 :logic aignet$a::gate-id->fanin1
                             :exec aignet$c::id->fanin1$inline)
            (reg-id->nxst :logic aignet$a::reg-id->nxst
                        :exec aignet$c::reg-id->nxst$inline)
            (nxst-id->reg :logic aignet$a::nxst-id->reg
                        :exec aignet$c::nxst-id->reg$inline)
            (id->phase :logic aignet$a::id->phase
                       :exec aignet$c::id->phase$inline)
            (id->slot :logic aignet$a::id->slot
                         :exec aignet$c::id->slot$inline)

            (aignet-add-in :logic aignet$a::aignet-add-in
                           :exec aignet$c::aignet-add-in
                           :protect t)
            (aignet-add-reg :logic aignet$a::aignet-add-reg
                            :exec aignet$c::aignet-add-reg
                            :protect t)
            (aignet-add-gate :logic aignet$a::aignet-add-gate
                             :exec aignet$c::aignet-add-gate
                             :protect t)
            (aignet-add-out :logic aignet$a::aignet-add-out
                            :exec aignet$c::aignet-add-out
                            :protect t)
            (aignet-set-nxst :logic aignet$a::aignet-set-nxst
                              :exec aignet$c::aignet-set-nxst
                              :protect t)

            (aignet-init :logic aignet$a::aignet-init
                         :exec aignet$c::aignet-init
                         :protect t)
            (aignet-clear :logic aignet$a::aignet-clear
                         :exec aignet$c::aignet-clear
                         :protect t)))

(defstobj-clone aignet2 aignet :suffix "2")


(defxdoc aignet
  :parents (acl2::boolean-reasoning)
  :short "An efficient, @(see acl2::stobj)-based And-Inverter Graph (AIG)
representation for Boolean functions and finite-state machines."
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


(defxdoc aignet-logic
  :parents (aignet)
  :short "The logical story of aignets"
  :long
"
<p> An aignet object is defined as an abstract stobj.  That means that its
implementation and its logical story are different: i.e., the code that
actually gets executed is not the same as the logical definitions of those
functions.  (This is true of concrete stobjs as well -- access/update functions
are defined in terms of NTH and UPDATE-NTH, but implemented as array accesses.)
</p>

<p> Since the implementation is kept hidden, we don't discuss it in depth here
except to say that among the basic APIs, accesses are implemented as
constant-time operations, and updates as amortized constant-time (since there
may be array resizes).  Implementation code is in aignet-exec.lisp or
aignet-exec-thms.lisp, and see @(see aignet-impl).  </p>

<p> Logically, an aignet is simply a list of nodes, where a node is of one of
five types distinguished by a particular symbol in its CAR, called its
<i>stype</i> (for \"sequential type\").  Depending on its stype, a node
contains 0 or more fields that encode the and-inverter graph.  We will discuss
the meanings of these fields later:</p>

<ul>
<li>Primary input --    @('(:pi)')</li>
<li>Register --         @('(:reg)')</li>
<li>AND gate --         @('(:gate fanin0 fanin1)')</li>
<li>Next state --       @('(:nxst fanin regid)')</li>
<li>Primary output --   @('(:po fanin)')</li>
</ul>

<p>There is one other stype, @(':const'), but generally no node in the list
actually has constant type; instead, the final CDR of the list implicitly
contains a constant node.  Thus, the number of nodes in the aignet is 
@('(+ 1 (len aignet))').  However, we use a different function,
@('node-count'), for this purpose so that we can feel free to use rules that
would be expensive to generally apply to @('len').  </p>

<p>An aignet is constructed by simply consing new nodes onto it.  A
newly-created or cleared aignet is just NIL, which contains only the implicit
constant node.</p>

<p>Access to aignet nodes is primarily by ID, which is simply the number of
nodes that were in the aignet when the node was added.  The implicit constant
node has ID 0, the first node added to an empty aignet has ID 1, and so on.
Thus, the ID of a node in an aignet is the length (node-count) of the suffix of
the aignet beginning at that node.  To look up a node by ID, we use the
function @('(lookup-id id aignet)'), which returns the unique suffix of length
ID, or the final cdr of the aignet if the ID is out of bounds:</p> @(def
lookup-id)

<p>Note: This is a quadratic algorithm!  But it doesn't matter, since real
executions of ID lookups do not use this function, but instead use array
accesses. </p>

<p>Input, output, and register nodes also have an IO number distinct from their
ID.  This is their index among nodes of their type, so, e.g., the first primary
input node added has input number 0, etc.  The IO number of a node can be
determined by counting the number of nodes of the same type in the suffix
beginnning after that node:
@(def stype-count)
Therefore, an input/output/register node can be looked up by IO number by
searching for the unique node of the given type with the given IO number:
@(def lookup-stype)
</p>

<p>Gate, next state, and primary output nodes all have fields: a gate has two
fanins (representing the inputs to the AND gate), a primary output or
next-state has one fanin (the function of the output or next-state), and a
next-state also contains an ID that should point to a register node.  The
fanins are <i>literals</i>, which combine a node ID with a negation flag
as a single natural number: @('(+ (* 2 id) neg)'), where neg is 1 or 0.</p>

<p>The four functions @('node-count'), @('lookup-id'), @('stype-count'), and
@('lookup-stype') provide the logical basis for most kinds of access to the
aignet.  One additional type of lookup is required, namely finding the
next-state node for a given register ID:</p> @(def lookup-reg->nxst)")


; [Jared] changed parents here; previously everything below had
; aignet-programming as another parent, but this topic was never defined.  it
; may have been intended to be aignet-impl, but I think it's reasonable to just
; not include it for now.

(defxdoc num-nodes
  :parents (aignet-logic)
  :short "Total number of nodes in an aignet"
  :long "
<p>Logically, @('(+ 1 (node-count aignet))'), (where @('node-count') is the
same as @('len')), since the empty aignet implicitly has a constant node.</p>")

(defxdoc num-ins
  :parents (aignet-logic)
  :short "Number of primary input nodes in an aignet"
  :long "
<p>
Logically, @('(stype-count :pi aignet)')</p> ")

(defxdoc num-regs
  :parents (aignet-logic)
  :short "Number of register nodes in an aignet"
  :long "
<p>
Logically, @('(stype-count :reg aignet)')</p> ")

(defxdoc num-outs
  :parents (aignet-logic)
  :short "Number of primary output nodes in an aignet"
  :long "
<p>
Logically, @('(stype-count :po aignet)')</p> ")

(defxdoc num-nxsts
  :parents (aignet-logic)
  :short "Number of next-state nodes in an aignet"
  :long "
<p>
Logically, @('(stype-count :nxst aignet)')</p> ")

(defxdoc num-gates
  :parents (aignet-logic)
  :short "Number of AND gate nodes in an aignet"
  :long "
<p>
Logically, @('(stype-count :gate aignet)')</p> "
  :short ""
  :long "")

(defxdoc fanin-litp
  :parents (aignet-logic)
  :short "Checks whether a literal is appropriate as a fanin to another node"
  :long "<p>AKA aignet-litp (but fanin-litp is the executable version).  True iff
the literal's ID is in bounds and belongs to a non-output, non-next-state node.</p>")

(defxdoc id-existsp
  :parents (aignet-logic)
  :short "Checks whether an ID is in bounds for an aignet"
  :long "<p>AKA aignet-idp.  True iff the ID is less than @('(num-nodes aignet)').</p>")

(defxdoc innum->id
  :parents (aignet-logic)
  :short "Gets the ID of the node with the given PI number"
  :long "<p>Logically, @('(node-count (lookup-stype n :pi aignet))')</p>")

(defxdoc outnum->id
  :parents (aignet-logic)
  :short "Gets the ID of the node with the given PO number"
  :long "<p>Logically, @('(node-count (lookup-stype n :po aignet))')</p>")

(defxdoc regnum->id
  :parents (aignet-logic)
  :short "Gets the ID of the node with the given register number"
  :long "<p>Logically, @('(node-count (lookup-stype n :reg aignet))')</p>")

(defxdoc id->type
  :parents (aignet-logic)
  :short "Gets the type code of the node with the given ID"
  :long "<p>Logically, @('(typecode (ctype (stype (car (lookup-id id aignet)))))').</p>")

(defxdoc io-id->regp
  :parents (aignet-logic)
  :short "Gets the register bit of the node with the given ID"
  :long "<p>Logically, @('(regp (stype (car (lookup-id id aignet))))')</p>")

(defxdoc io-id->ionum
  :parents (aignet-logic)
  :short "Gets the IO number of the node with the given ID"
  :long "<p>Logically,
@({
 (stype-count (stype (car (lookup-id id aignet)))
              (cdr (lookup-id id aignet)))})
but, per its guard, may only be called on the ID of a PI, PO, or register node.
This is because the aignet data structure only stores this information for PIs,
POs, and registers.
</p>")

(defxdoc co-id->fanin
  :parents (aignet-logic)
  :short "Gets the fanin of a next-state or primary output node"
  :long "<p>Logically,
 @({
 (aignet-lit-fix
   (co-node->fanin (car (lookup-id id aignet)))
   (cdr (lookup-id id aignet)))})
 The aignet-lit-fix ensures that the literal returned is a valid fanin,
 i.e. its ID is less than the ID of the CO node and is not a CO node
 itself.</p>")

(defxdoc gate-id->fanin0
  :parents (aignet-logic)
  :short "Gets the 0th fanin of an AND gate node"
  :long "<p>Logically,
 @({
 (aignet-lit-fix
   (gate-node->fanin0 (car (lookup-id id aignet)))
   (cdr (lookup-id id aignet)))})
 The aignet-lit-fix ensures that the literal returned is a valid fanin,
i.e. its ID is less than the ID of the gate node, and is not a combinational
output node.</p>")

(defxdoc gate-id->fanin1
  :parents (aignet-logic)
  :short "Gets the 1st fanin of an AND gate node"
  :long "<p>Logically,
 @({
 (aignet-lit-fix
   (gate-node->fanin1 (car (lookup-id id aignet)))
   (cdr (lookup-id id aignet)))})
 The aignet-lit-fix ensures that the literal returned is a valid fanin,
i.e. its ID is less than the ID of the gate node, and is not a combinational
output node.</p>")

(defxdoc reg-id->nxst
  :parents (aignet-logic)
  :short "Finds the next-state node associated with a register ID, if it exists"
  :long "<p>Logically, @('(node-count (lookup-reg->nxst id aignet))')</p>")

(defxdoc nxst-id->reg
  :parents (aignet-logic)
  :short "Gets the register ID associated with a next-state node"
  :long "<p>Logically,
@({
 (aignet-id-fix (nxst-node->reg (car (lookup-id id aignet)))
                (cdr (lookup-id id aignet)))})
The aignet-id-fix ensures that the ID exists and is less than that of the
next-state node.  However, there is no guarantee that it is the ID of a
register node!  Even if it is, it is possible that subsequent addition of
another next-state node for the same register superseded this one.  Typically,
one really wants to find the next-state node for a register (@(see
reg-id->nxst)) rather than the other way around.</p>")

(defxdoc id->phase
  :parents (aignet-logic)
  :short "Finds the value of the node under the all-0 simulation"
  :long "<p></p>")

(defxdoc aignet-add-in
  :parents (aignet-logic)
  :short "Adds a primary input node to the aignet"
  :long "<p>Logically, @('(cons (pi-node) aignet)').</p>")

(defxdoc aignet-add-reg
  :parents (aignet-logic)
  :short "Adds a register node to the aignet"
  :long "<p>Logically, @('(cons (reg-node) aignet)').</p>")

(defxdoc aignet-add-gate
  :parents (aignet-logic)
  :short "Adds an AND gate node to the aignet"
  :long "<p>Logically,
 @({
   (cons (gate-node (aignet-lit-fix f0 aignet)
                    (aignet-lit-fix f1 aignet))
         aignet)})
The aignet-lit-fixes ensure that well-formedness of the network is preserved
unconditionally.</p>")

(defxdoc aignet-add-out
  :parents (aignet-logic)
  :short "Adds a primary output node to the aignet"
  :long "<p>Logically,
 @({
   (cons (po-node (aignet-lit-fix f aignet))
         aignet)})
The aignet-lit-fix ensures that well-formedness of the network is preserved
unconditionally.</p>")

(defxdoc aignet-set-nxst
  :parents (aignet-logic)
  :short "Adds a next-state node to the aignet"
  :long "<p>Logically,
@({
   (cons (nxst-node (aignet-lit-fix f aignet)
                    (aignet-id-fix regid aignet))
         aignet)})
The aignet-lit-fix/aignet-id-fix together ensure that well-formedness of the
network is preserved unconditionally.</p>")

(defxdoc aignet-init
  :parents (aignet-logic)
  :short "Clears the aignet, ensuring minimum sizes for arrays"
  :long "<p>Logically, just returns NIL.  The resulting aignet contains only
the implicit constant-0 node.  The sizes given are used to adjust arrays in the
implementation.</p>")

(defxdoc aignet-clear
  :parents (aignet-logic)
  :short "Clears the aignet"
  :long "<p>Logically, just returns NIL.  The resulting aignet contains only the
implicit constant-0 node.</p>")
