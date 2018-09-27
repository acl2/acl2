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

(in-package "AIGNET$C")

(local (include-book "aignet-exec-thms"))

(include-book "std/util/defredundant" :dir :system)

(set-enforce-redundancy t)
; (include-book "centaur/aignet/idp" :dir :system)
(include-book "litp")
(include-book "snodes")
(include-book "std/util/define" :dir :system)

(std::defredundant
  :names
  (const-type
   gate-type
   in-type
   ;; out-type
   aignet
   aignet-sizes-ok
   id->slot id->slot0 id->slot1 id->slot$
   set-snode->fanin
   ;; id->type
   ;; id->phase
   ;; id->regp
   ;; id->ionum
   ;; id->fanin0
   ;; id->fanin1
   ;; reg-id->nxst
   ;; nxst-id->reg
   update-node-slot update-node-slot0 update-node-slot1 update-node-slot$
   maybe-grow-nodes maybe-grow-ins maybe-grow-regs maybe-grow-outs
   set-innum->id innum->id
   set-regnum->id regnum->id
   set-outnum->fanin outnum->fanin
   lit->phase
   ;; fanin-litp
   count-nodes
   ;; aignet-counts-accurate
   ;; aignet-nodes-nonconst-witness
   add-node add-in add-out add-reg
   aignet-add-in
   aignet-add-reg
   aignet-add-and
   aignet-add-xor
   aignet-add-out
   aignet-set-nxst
   ;; aignet-gates-onlyp
   ;; aignet-regs-constant
   ;; aignet-reg-ids-in-bounds
   aignet-rollback
   aignet-clear
   aignet-init
   id-existsp
   ;; regnum->nxst
   ))
