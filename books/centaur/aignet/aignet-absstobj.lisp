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
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(local (include-book "aignet-exec-thms"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "clause-processors/generalize" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable set::double-containment
                           nth
                           update-nth
                           resize-list
                           acl2::nfix-when-not-natp
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           set::double-containment
                           set::sets-are-true-lists
                           make-list-ac
                           true-listp-update-nth
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



(defsection base-api
  :parents (aignet)
  :short "Lowest-level functions for working with the @('aignet') stobj."

  :long "<h3>Quick Guide</h3>

<h5>Initialization</h5>
<ul>
  <li>@(see aignet-clear) clears the network without resizing.</li>
  <li>@(see aignet-init) clears the network and resize arrays.</li>
</ul>

<h5>Network construction</h5>
<ul>
  <li>@(see aignet-add-in) adds a primary input</li>
  <li>@(see aignet-add-out) adds a primary output</li>
  <li>@(see aignet-add-gate) adds an and gate</li>
  <li>@(see aignet-add-reg) adds a new register node; its next-state
      should later be configured with @(see aignet-set-nxst)</li>
</ul>

<h5>Network size</h5>
<ul>
  <li>@(see num-nodes) returns the number of nodes in the network</li>
  <li>@(see num-ins) returns the number of primary inputs</li>
  <li>@(see num-outs) returns the number of primary outputs</li>
  <li>@(see num-gates) returns the number of and gates</li>
  <li>@(see num-regs) returns the number of register nodes</li>
  <li>@(see num-nxsts) returns the number of next-state nodes</li>
</ul>

<h5>General node queries</h5>
<ul>
 <li>@(see id-existsp) checks whether an ID is in bounds</li>
 <li>@(see id->type) looks up the type of some node</li>
 <li>@(see id->phase) gets the value of this node in the all-0 evaluation.</li>
 <li>@(see fanin-litp) checks whether an ID can be used as a fanin.</li>
</ul>

<h5>Name mappings</h5>
<ul>
 <li>@(see innum->id) looks up the node id for the @('n')th primary input</li>
 <li>@(see outnum->id) looks up the node id for the @('n')th primary output</li>
 <li>@(see regnum->id) looks up the node id for the @('n')th register</li>
 <li>@(see io-id->ionum) gets the IO number from an IO node's ID</li>
 <li>@(see reg-id->nxst) gets the next state node associated with a register ID, if one exists</li>
 <li>@(see nxst-id->reg) gets the register ID associated with a next-state node</li>
</ul>

<h5>Fanin lookup</h5>
<ul>
 <li>@(see gate-id->fanin0) gets the 0th fanin @(see literal) from an AND gate</li>
 <li>@(see gate-id->fanin1) gets the 1st fanin literal from an AND gate</li>
 <li>@(see co-id->fanin) gets the fanin literal from a next-state or primary output node</li>
</ul>

<h5>Misc</h5>

<ul>
 <li>@(see io-id->regp) gets the register bit for a node id</li>
</ul>")

(local (xdoc::set-default-parents base-api))

;; Initialization

(defxdoc aignet-clear
  :short "@(call aignet-clear) clears the aignet, essentially without resizing
  its arrays."

  :long "<p>Logically, just returns @('nil'), i.e., the resulting aignet
  contains only the implicit constant-0 node.</p>

  <p>In the execution we reset the counters associated with the Aignet, but the
  actual arrays are left unchanged (unless there are no nodes at all, in which
  case a very small node array is allocated.)</p>

  @(def aignet$a::aignet-clear)")

(defxdoc aignet-init
  :short "@(call aignet-init) clears the aignet, setting the arrays to the
  given sizes."

  :long "<p>Logically, just returns @('nil'), i.e., the resulting aignet
  contains only the implicit constant-0 node.</p>

  <p>In the execution, we reset the counters associated with the Aignet and
  also resize the stobj arrays to the indicated sizes.</p>

  <p>Note: the @('max-nodes') size indicates the number of logical nodes that
  the node array will be able to hold without resizing.  That is, since each
  node takes two 32-bit array slots, we resize the physical node array to @('2
  * max-nodes') elements, so that there are room for @('max-nodes') nodes.</p>

  @(def aignet$a::aignet-init)")


;; Network construction

(defxdoc aignet-add-in
  :short "@(call aignet-add-in) adds a new primary input node to the aignet."
  :long "<p>Logically this is just @('(cons (pi-node) aignet)').</p>
  <p>In the execution we update the necessary arrays, counts, etc.</p>
  @(def aignet$a::aignet-add-in)")

(defxdoc aignet-add-reg
  :short "@(call aignet-add-reg) adds a new register node to the aignet."
  :long "<p>Logically this is just @('(cons (reg-node) aignet)').</p>
  <p>In the execution we update the necessary arrays, counts, etc.</p>
  @(def aignet$a::aignet-add-reg)")

(defxdoc aignet-add-gate
  :short "@(call aignet-add-gate) adds an new AND gate node to the aignet with
  the given fanin @(see literal)s."

  :long "<p><b>Note</b>: this is a very low level function.  It is often better
  to use routines like @(see aignet-hash-and), @(see aignet-hash-or), etc.,
  which can do some simplifications to produce smaller aig networks.</p>

  <p>Logically this is just:</p>

  @({
      (cons (gate-node (aignet-lit-fix f0 aignet)
                       (aignet-lit-fix f1 aignet))
            aignet)
  })

  <p>The @(see aignet-lit-fix)es ensure that well-formedness of the network is
  preserved unconditionally.</p>

  <p>In the execution we update the necessary arrays, counts, etc.</p>

  @(def aignet$a::aignet-add-gate)")

(defxdoc aignet-add-out
  :short "@(call aignet-add-out) adds a primary output node to the aignet."

  :long "<p>Logically this is just:</p>

  @({
      (cons (po-node (aignet-lit-fix f aignet))
            aignet)
  })

  <p>The @(see aignet-lit-fix) ensures that well-formedness of the network is
  preserved unconditionally.</p>

  <p>In the execution we update the necessary arrays, counts, etc.</p>

  @(def aignet$a::aignet-add-out)")

(defxdoc aignet-set-nxst
  :short "@(call aignet-set-nxst) adds a next-state node to the aignet."

  :long "<p>Logically this is just:</p>

  @({
      (cons (nxst-node (aignet-lit-fix f aignet)
                       (aignet-id-fix regid aignet))
            aignet)
  })

  <p>The fixing here ensures that well-formedness of the network is preserved
  unconditionally.</p>

  <p>In the execution we update the necessary arrays, counts, etc.</p>

  @(def aignet$a::aignet-set-nxst)")


;; Network size

(defxdoc node-count
  :short "@(call node-count) is an alias for @(see len)."
  :long "<p>This is mainly of use in the logical definition of @(see
  num-nodes).  We use a different function than @(see len) only so that we can
  feel free to use rules that would be expensive to generally apply to
  @('len').</p>

  @(def node-count)")

(defxdoc num-nodes
  :short "@(call num-nodes) returns the total number of nodes in an aignet."
  :long "<p>Logically this is @('(+ 1 (node-count aignet))'), (where
  @('node-count') is the same as @('len')), since the empty aignet implicitly
  has a constant node.</p>

  <p>In the execution this is just a stobj field access.</p>

  @(def aignet$a::num-nodes)")

(defxdoc num-ins
  :short "@(call num-ins) returns the number of primary input nodes in an aignet."
  :long "<p>Logically this is just @('(stype-count :pi aignet)').</p>
  <p>In the execution this is just a stobj field access.</p>
  @(def aignet$a::num-ins)")

(defxdoc num-regs
  :short "@(call num-regs) returns the number of register nodes in an aignet."
  :long "<p>Logically this is just @('(stype-count :reg aignet)').</p>
  <p>In the execution this is just a stobj field access.</p>
  @(def aignet$a::num-regs)")

(defxdoc num-outs
  :short "@(call num-outs) returns the number of primary output nodes in an aignet."
  :long "<p>Logically this is just @('(stype-count :po aignet)').</p>
  <p>In the execution this is just a stobj field access.</p>
  @(def aignet$a::num-outs)")

(defxdoc num-nxsts
  :short "@(call num-nxsts) returns the number of next-state nodes in an aignet."
  :long "<p>Logically this is just @('(stype-count :nxst aignet)')</p>
  <p>In the execution this is just a stobj field access.</p>
  @(def aignet$a::num-nxsts)")

(defxdoc num-gates
  :short "@(call num-gates) returns the number of AND gate nodes in an aignet."
  :long "<p>Logically this is just @('(stype-count :gate aignet)')</p>
  <p>In the execution this is just a stobj field access.</p>
  @(def aignet$a::num-gates)")



;; General node queries

(defxdoc id-existsp
  :short "@(call id-existsp) checks whether an ID is in bounds for an aignet."
  :long "<p>Executable version of @('aignet-idp').  True iff the ID is less
  than @('(num-nodes aignet)').</p>

  @(def aignet$a::id-existsp)
  @(def aignet-idp)")

(defxdoc id->type
  :short "@(call id->type) gets the type code of the node with ID @('id')."
  :long "<p>Logically this is @('(node->type (car (lookup-id id aignet)))').</p>
  <p>In the execution this is mostly a stobj array lookup in the node array.</p>

  @(def aignet$a::id->type)")

(defxdoc id->phase
  :short "@(call id->phase) computes the value of the node under the all-0
  simulation."
  :long "<p>In the logic, we have to compute the value by recursively walking
  over the node array.  However, in the execution we keep these values
  pre-computed so this is mostly just a stobj array lookup in the node
  array.</p>

  @(def aignet$a::id->phase)
  @(def aignet$a::lit->phase)")

(defxdoc fanin-litp
  :short "@(call fanin-litp) checks whether a @(see literal) is appropriate as
  a fanin to another node."
  :long "<p>Executable version of @('aignet-litp').  True iff the literal's ID
  is in bounds and belongs to a non-output, non-next-state node.</p>

  @(def aignet$a::fanin-litp)
  @(def aignet-litp)")


;; Name mappings

(defxdoc innum->id
  :short "@(call innum->id) gets the ID of the node with primary input number @('n')."
  :long "<p>Logically this is @('(node-count (lookup-stype n :pi aignet))').</p>
  <p>In the execution this is a stobj array lookup in the inputs array.</p>

  @(def aignet$a::innum->id)")

(defxdoc outnum->id
  :short "@(call outnum->id) gets the ID of the node with primary output number @('n')."
  :long "<p>Logically this is @('(node-count (lookup-stype n :po aignet))').</p>
  <p>In the execution this is a stobj array lookup in the outputs array.</p>

  @(def aignet$a::outnum->id)")

(defxdoc regnum->id
  :short "@(call regnum->id) gets the ID of the node with register number @('n')."
  :long "<p>Logically this is @('(node-count (lookup-stype n :reg aignet))').</p>
  <p>In the execution this is a stobj array lookup in the registers array.</p>

  @(def aignet$a::regnum->id)")

(defxdoc io-id->ionum
  :short "@(call io-id->ionum) gets the IO number of the node whose ID is @('id')."
  :long "<p>Logically this is just</p>

  @({
      (stype-count (stype (car (lookup-id id aignet)))
                   (cdr (lookup-id id aignet)))
  })

  <p>However, its guard requires that it may only be called on the ID of a PI,
  PO, or register node.  This is because the aignet data structure only stores
  this information for PIs, POs, and registers.</p>

  <p>In the execution this is mostly a stobj array lookup in the node array.</p>

  @(def aignet$a::io-id->ionum)")

(defxdoc reg-id->nxst
  :short "@(call reg-id->nxst) finds the next-state node associated with the
  register whose ID is @('id'), if it exists."
  :long "<p>Logically this is just @('(node-count (lookup-reg->nxst id aignet))')</p>
  <p>In the execution this is mostly just a stobj array lookup in the node array.</p>
  @(def aignet$a::reg-id->nxst)")

(defxdoc nxst-id->reg
  :short "@(call nxst-id->reg) gets the register ID associated with a
  next-state node."
  :long "<p>Logically this is just</p>

  @({
      (aignet-id-fix (nxst-node->reg (car (lookup-id id aignet)))
                     (cdr (lookup-id id aignet)))
  })

  <p>The @(see aignet-id-fix) ensures that the ID exists and is less than that
  of the next-state node.  However, there is no guarantee that it is the ID of
  a register node!  Even if it is, it is possible that subsequent addition of
  another next-state node for the same register superseded this one.</p>

  <p>Typically, one really wants to find the next-state node for a
  register (@(see reg-id->nxst)) rather than the other way around.</p>

  <p>In the execution this is mostly just a stobj array lookup in the node
  array.</p>

  @(def aignet$a::nxst-id-reg)")


;; Fanin Lookup

(defxdoc gate-id->fanin0
  :short "@(call gate-id->fanin0) gets the 0th fanin @(see literal) of the AND
  gate node whose ID is @('id')."
  :long "<p>Logically this is just</p>

  @({
      (aignet-lit-fix (gate-node->fanin0 (car (lookup-id id aignet)))
                      (cdr (lookup-id id aignet)))
  })

  <p>The @(see aignet-lit-fix) ensures that the literal returned is a valid
  fanin, i.e. its ID is less than the ID of the gate node, and is not a
  combinational output node.</p>

  <p>In the execution this is mostly just a stobj array lookup in the node
  array.</p>

  @(def aignet$a::gate-id->fanin0)")

(defxdoc gate-id->fanin1
  :short "@(call gate-id->fanin1) gets the 1st fanin @(see literal) of the AND
  gate node whose ID is @('id')."
  :long "<p>Logically this is just</p>

  @({
      (aignet-lit-fix (gate-node->fanin1 (car (lookup-id id aignet)))
                      (cdr (lookup-id id aignet)))
  })

  <p>The @(see aignet-lit-fix) ensures that the literal returned is a valid
  fanin, i.e. its ID is less than the ID of the gate node, and is not a
  combinational output node.</p>

  <p>In the execution this is mostly just a stobj array lookup in the node
  array.</p>

  @(def aignet$a::gate-id->fanin1)")

(defxdoc co-id->fanin
  :short "@(call co-id->fanin) gets the fanin @(see literal) of the next-state or
  primary output node whose ID is @('id')."
  :long "<p>Logically this is just</p>

  @({
      (aignet-lit-fix (co-node->fanin (car (lookup-id id aignet)))
                      (cdr (lookup-id id aignet)))
  })

  <p>The @(see aignet-lit-fix) ensures that the literal returned is a valid
  fanin, i.e. its ID is less than the ID of the CO node and is not a CO node
  itself.</p>

  <p>In the execution this is mostly a stobj array lookup in the node
  array.</p>

  @(def aignet$a::co-id->fanin)")


;; Misc

(defxdoc io-id->regp
  :short "@(call io-id->regp) gets the register bit from the node with ID @('id')."
  :long "<p>Logically this is @('(regp (stype (car (lookup-id id aignet))))').</p>
  <p>In the execution this is mostly a stobj array lookup in the node array.</p>

  @(def aignet$a::io-id->regp)")



