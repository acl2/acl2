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

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/ipasir/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)

(defconst *aignet-exports*
  '(aignet-well-formedp
    aignet-extension-p
    aignet
    aignet2
    def-aignet-preservation-thms
    add-aignet-preservation-thm
    aignet-add-in
    def-aignet-frame
    aignet-add-in
    aignet-add-reg
    aignet-add-gate
    aignet-add-out
    aignet-add-regin
    aignet-init
    aignet-clear
    aignet-eval
    aignet-eval-frame
    aignet-copy-comb
    aignet-copy-frame
    aignet-vals
    aignet-copy
    aignet-copy-ins
    aignet-copy-regs
    aignet-copy-outs
    aignet-copy-regins
    aignet-print
    aignet-hash-and
    aignet-hash-or
    aignet-hash-xor
    aignet-hash-mux
    swap-aignets
    aig-sat))

(defconst *aignet-imports*
  '(nat-listp
    defconsts
    definline
    definlined
    defxdoc
    define
    defsection
    defmvtypes
    std::defprojection
    std::deflist
    std::defval
    b*
    aig-eval
    aig-not
    aig-and
    aig-xor
    aig-xor-lists
    aig-cases
    aig-vars
    aig-vars-1pass
    aig-restrict
    aig-restrict-list
    aig-restrict-alist
    lnfix lifix
    zz-sat
    zz-batch-sat
    aiger-read
    unsigned-byte-p
    signed-byte-p
    make-fast-alist
    alist-keys
    alist-vals
    with-fast
    with-fast-alist
    with-fast-alists
    nat-equiv
    nth-equiv
    value
    def-ruleset
    def-ruleset!
    add-to-ruleset
    enable*
    disable*
    e/d*
    e/d**
    cwtime
    local-stobjs
    def-array-set
    def-slot-set
    defiteration
    def-list-constructor
    defstobj-clone
    x
    bitp bfix b-and b-xor b-ior b-not bit-equiv
    bitarr get-bit set-bit bits-length resize-bits bits-equiv
    tag
    list-equiv
    duplicity
    stobj
    abstract-stobj
    new old orig
    ))

(defpkg "AIGNET"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*
            *aignet-exports*
            *aignet-imports*
            satlink::*satlink-exports*
            std::*std-exports*
            *bitops-exports*
            *stobjs-exports*
            *ipasir-exports*))

(defpkg "AIGNET-GENSYMS" nil)

;; (defconst *aignet$a-exports*
;;   #!AIGNET
;;   '(const-type
;;     gate-type
;;     in-type
;;     out-type
;;     stype
;;     stype-fix
;;     stypep
;;     const-stype
;;     gate-stype
;;     pi-stype
;;     po-stype
;;     ri-stype
;;     ro-stype
;;     stype->type
;;     stype->regp
;;     gate-node
;;     gate-node-p
;;     gate-node->fanin0
;;     gate-node->fanin1
;;     po-node
;;     po-node-p
;;     po-node->fanin
;;     ri-node
;;     ri-node-p
;;     ri-node->fanin
;;     ri-node->reg
;;     io-node->ionum
;;     io-node->regp
;;     node->type
;;     node-p
;;     node-listp
;;     proper-node-listp
;;     tags
;;     suffixp
;;     suffixp-bind
;;     reg-count
;;     lookup-node
;;     lookup-pi
;;     lookup-ro
;;     lookup-po
;;     lookup-reg->ri
;;     pi->id
;;     po->id
;;     ro->id
;;     ri->id
;;     co-orderedp
;;     gate-orderedp
;;     aignet-litp
;;     aignet-idp
;;     aignet-nodes-ok
;;     aignet-well-formedp))

(defconst *aignet$c-imports*
  #!AIGNET '(idp
             litp
             id-val
             id-fix
             lit-id
             lit-neg
             mk-lit
             lit-negate
             lit-negate-cond
             to-lit
             to-id
             lit-fix
             lit-val
             id-equiv
             lit-equiv
             snode->type
             snode->phase
             snode->regp
             snode->fanin
             snode->ionum
             snode->regid
             mk-snode
             snode->type^
             snode->phase^
             snode->regp^
             snode->fanin^
             snode->ionum^
             snode->regid^
             mk-snode^
             ;; [Jared] added these for nicer aignet-base-api docs
             f f0 f1 n regid lit
             max-outs max-regs max-ins max-nodes
             new old orig
             ))

(defpkg "AIGNET$A"
  #!AIGNET '(
             ;; [Jared] added these for a nicer aignet-base-api docs
             f f0 f1 n regid lit
             max-outs max-regs max-ins max-nodes
             new old orig))

;; (defpkg "AIGNET$A"
;;   (union-eq *acl2-exports*
;;             *common-lisp-symbols-from-main-lisp-package*
;;             *aignet$a-exports*
;;             *aignet-imports*
;;             *aignet$a/c-imports*))

(defpkg "AIGNET$C"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*
            *aignet-imports*
            satlink::*satlink-exports*
            *aignet$c-imports*
            std::*std-exports*
            *stobjs-exports*))
