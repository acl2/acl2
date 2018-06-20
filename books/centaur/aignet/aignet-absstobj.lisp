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
(local (include-book "clause-processors/use-by-hint" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth
                           update-nth
                           resize-list
                           acl2::nfix-when-not-natp
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           ;; set::double-containment
                           ;; set::sets-are-true-lists
                           make-list-ac
                           true-listp-update-nth
                           acl2::nth-with-large-index
                           ;; (aignet$c::aignet-max-fanin-correct)
                           ;; (aignet$c::aignet-max-fanin-sufficient)
                           (aignet$c::aignet-nodes-nonconst))))
(local (std::add-default-post-define-hook :fix))

(local (defthm lookup-id-of-lookup-id
         (implies (and (<= m n)
                       (integerp n)
                       (<= n (node-count aignet))
                       ;; (not (equal (stype (car (lookup-id m aignet))) :const))
                       )
                  (equal (lookup-id m (lookup-id n aignet))
                         (lookup-id m aignet)))
         :hints ((and stable-under-simplificationp
                      '(:cases ((zp m))))
                 (and stable-under-simplificationp
                      '(:cases ((zp n)))))))


(local (defthm id->phase-of-extension-inverse
         (implies (and (aignet-extension-bind-inverse)
                       (<= (nfix id) (node-count orig)))
                  (equal (aignet$a::id->phase id orig)
                         (aignet$a::id->phase id new)))))

(local (defthm lookup-reg->nxst-of-extension-inverse-when-nxst-counts-equal
         (implies (and (aignet-extension-bind-inverse)
                       (equal (stype-count :nxst orig)
                              (stype-count :nxst new))
                       (equal (stype (car (lookup-id reg-id orig))) :reg))
                  (equal (lookup-reg->nxst reg-id orig)
                         (lookup-reg->nxst reg-id new)))
         :hints(("Goal" :in-theory (enable lookup-reg->nxst aignet-extension-p
                                           stype-count)))))

(local (defthm id->phase-of-cons
         (implies (equal (nfix n) (+ 1 (node-count aignet)))
                  (equal (aignet$a::id->phase n (cons node aignet))
                         (snode->phase (mv-nth 1 (id-slots n (cons node aignet))))))
         :hints(("Goal" :in-theory (enable id-slots))
                (and stable-under-simplificationp
                     '(:in-theory (enable aignet$a::id->phase))))))

(local (in-theory (disable id->phase-of-cons)))

(local (defthm id-slots-of-cons-and
         (implies (equal (nfix n) (+ 1 (node-count aignet)))
                  (equal (id-slots n (cons (and-node f0 f1) aignet))
                         (let ((f0 (aignet-lit-fix f0 aignet))
                               (f1 (aignet-lit-fix f1 aignet)))
                         (mk-snode (gate-type) 0
                                   (b-and (aignet$a::lit->phase f0 aignet)
                                          (aignet$a::lit->phase f1 aignet))
                                   f0 f1))))
         :hints(("Goal" :in-theory (enable id-slots aignet$a::id->phase)))))

(local (defthm id-slots-of-cons-xor
         (implies (equal (nfix n) (+ 1 (node-count aignet)))
                  (equal (id-slots n (cons (xor-node f0 f1) aignet))
                         (let ((f0 (aignet-lit-fix f0 aignet))
                               (f1 (aignet-lit-fix f1 aignet)))
                         (mk-snode (gate-type) 1
                                   (b-xor (aignet$a::lit->phase f0 aignet)
                                          (aignet$a::lit->phase f1 aignet))
                                   f0 f1))))
         :hints(("Goal" :in-theory (enable id-slots aignet$a::id->phase)))))

(local (defthm id-slots-of-cons-pi
         (implies (equal (nfix n) (+ 1 (node-count aignet)))
                  (equal (id-slots n (cons '(:pi) aignet))
                         (mk-snode (in-type) 0
                                   0 0
                                   (stype-count :pi aignet))))
         :hints(("Goal" :in-theory (enable id-slots aignet$a::id->phase)))))

(local (defthm id-slots-of-cons-reg
         (implies (equal (nfix n) (+ 1 (node-count aignet)))
                  (equal (id-slots n (cons '(:reg) aignet))
                         (mk-snode (in-type) 1
                                   0
                                   (+ 1 (node-count aignet))
                                   (stype-count :reg aignet))))
         :hints(("Goal" :in-theory (enable id-slots aignet$a::id->phase
                                           lookup-reg->nxst)))))

(local (defthm id-slots-of-cons-po
         (implies (equal (nfix n) (+ 1 (node-count aignet)))
                  (equal (id-slots n (cons (po-node f) aignet))
                         (let ((f (aignet-lit-fix f aignet)))
                         (mk-snode (out-type) 0
                                   (aignet$a::lit->phase f aignet)
                                   f (stype-count :po aignet)))))
         :hints(("Goal" :in-theory (enable id-slots aignet$a::id->phase)))))

(local (defthm id-slots-of-cons-nxst
         (implies (equal (nfix n) (+ 1 (node-count aignet)))
                  (equal (id-slots n (cons (nxst-node f regid) aignet))
                         (let ((f (aignet-lit-fix f aignet)))
                           (mk-snode (out-type) 1
                                     (aignet$a::lit->phase f aignet)
                                     f (aignet-id-fix regid aignet)))))
         :hints(("Goal" :in-theory (enable id-slots aignet$a::id->phase)))))

(local (defthm id-slots-of-cons-non-nxst
         (implies (and (not (eq (stype node) :nxst))
                       (<= (nfix n) (node-count aignet)))
                  (equal (id-slots n (cons node aignet))
                         (id-slots n aignet)))
         :hints(("Goal" :in-theory (enable id-slots)
                 :expand ((lookup-reg->nxst n (cons node aignet)))))))

(local (defthm id-slots-non-reg-node-of-cons-nxst
         (implies (and (<= (nfix n) (node-count aignet))
                       (not (equal (nfix n) (nfix regid))))
                  (equal (id-slots n (cons (nxst-node f regid) aignet))
                         (id-slots n aignet)))
         :hints(("Goal" :in-theory (enable id-slots)
                 :expand ((:free (node) (lookup-reg->nxst n (cons node aignet))))))))

(local (defthm id-slot-1-of-cons-node
         (implies (<= (nfix n) (node-count aignet))
                  (equal (mv-nth 1 (id-slots n (cons node aignet)))
                         (mv-nth 1 (id-slots n aignet))))
         :hints(("Goal" :in-theory (enable id-slots)))))

(local (defthm id-slot-0-of-cons-nxst
         (implies (And (<= (nfix n) (node-count aignet))
                       (equal (stype (car (lookup-id regid aignet))) :reg))
                  (equal (mv-nth 0 (id-slots regid (cons (nxst-node f regid) aignet)))
                         (aignet$c::set-snode->regid (+ 1 (node-count aignet))
                                                     (mv-nth 0 (id-slots regid aignet)))))
         :hints(("Goal" :in-theory (enable id-slots)
                 :expand ((lookup-reg->nxst regid (cons (nxst-node f regid) aignet)))))))

(local (defthm id-slots-of-aignet-extension-inverse
         (implies (and (aignet-extension-bind-inverse)
                       (<= (nfix m) (node-count orig))
                       (equal (stype-count :nxst orig)
                              (stype-count :nxst new)))
                  (equal (id-slots m orig)
                         (id-slots m new)))
         :hints(("Goal" :in-theory (e/d (id-slots)
                                        (lookup-reg->nxst-of-extension-inverse-when-nxst-counts-equal))
                 :use ((:instance lookup-reg->nxst-of-extension-inverse-when-nxst-counts-equal
                        (reg-id m)))))))

(local (in-theory (enable id->phase-of-cons)))

(local
 (progn

   

   #!aignet$c
   (defthm aignet-nodes-nonconst-when-empty
     (implies (equal (num-nodes aignet) 1)
              (aignet-nodes-nonconst aignet))
     :hints(("Goal" :in-theory (enable aignet-nodes-nonconst))))

   #!aignet$C
   (defthm aignet-find-max-fanin-when-empty
     (implies (equal (id->type 0 aignet) 0)
              (equal (aignet-find-max-fanin 0 aignet) 0))
     :hints(("Goal" :in-theory (enable aignet-find-max-fanin))))

   #!aignet$c
   (defthm aignet-counts-accurate-when-empty
     (implies (and (equal (num-nodes aignet) 1)
                   (equal (id->type 0 aignet) 0)
                   (equal (num-ins aignet) 0)
                   (equal (num-outs aignet) 0)
                   (equal (num-nxsts aignet) 0)
                   (equal (num-regs aignet) 0))
              (aignet-counts-accurate aignet))
     :hints(("Goal" :in-theory (enable aignet-counts-accurate
                                       count-nodes))))

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

   (in-theory (disable regnums-correct
                       lookup-stype-in-bounds))
   (in-theory (enable aignet$c::regnum->id))




   (defsection nodes-correct
     (defun-sk nodes-correct (aignetc aigneta)
       (forall
        id
        (implies
         ;; (and (natp id)
         ;;      (case-split (< id (aignet$c::num-nodes aignetc))))
         (case-split (< (nfix id) (nfix (aignet$c::num-nodes aignetc))))
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
                              (equal (aignet$a::id->regp id aigneta)
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
                                (aignet$a::id->regp id aigneta)))
                (implies (or (equal (aignet$a::id->type id aigneta)
                                    (in-type))
                             (and (equal (aignet$a::id->type id aigneta)
                                         (out-type))
                                  (equal (aignet$a::id->regp id aigneta)
                                         0)))
                         (equal (aignet$c::snode->ionum slot1)
                                (aignet$a::io-id->ionum id aigneta)))
                (implies (and (equal (aignet$a::id->type id aigneta)
                                     (out-type))
                              (equal (aignet$a::id->regp id aigneta)
                                     1))
                         (equal (aignet$c::snode->regid slot1)
                                (aignet$a::nxst-id->reg id aigneta)))
                (implies (equal (aignet$a::id->type id aigneta)
                                (gate-type))
                         (equal (aignet$c::snode->fanin slot1)
                                (aignet$a::gate-id->fanin1 id aigneta)))))))
       :rewrite :direct)

     (in-theory (disable nodes-correct)))

   (local (in-theory (enable aignet$a::id->regp
                             aignet$a::co-id->fanin
                             aignet$a::gate-id->fanin0
                             aignet$a::gate-id->fanin1
                             aignet$a::io-id->ionum
                             aignet$a::aignet-rollback)))

   (defthm id->type-of-empty
     (equal (aignet$a::id->type x nil) 0)
     :hints(("Goal" :in-theory (enable aignet$a::id->type))))

   (defthm id->phase-of-empty
     (equal (aignet$a::id->phase x nil) 0)
     :hints(("Goal" :in-theory (enable aignet$a::id->phase))))

   (defthm id->regp-of-empty
     (equal (aignet$a::id->regp x nil) 0)
     :hints(("Goal" :in-theory (enable aignet$a::id->regp))))

   ;; (defthm aignet-regs-in-bounds-impl-regs-in-bounds
   ;;   (implies (and (aignet$c::aignet-regs-in-bounds aignet)
   ;;                 (equal count (aignet$c::num-regs aignet)))
   ;;            (aignet$c::regs-in-bounds count aignet))
   ;;   :hints(("Goal" :in-theory (enable aignet$c::aignet-regs-in-bounds))))

   (local (in-theory (enable aignet$a::id->type)))

   (defsection aignet-count-equivs
     (defund-nx aignet-count-equivs (aignetc aigneta)
       (and (nat-equiv (nth aignet$c::*num-nodes* aignetc)
                       (aignet$a::num-nodes aigneta))
            (nat-equiv (nth aignet$c::*num-ins* aignetc)
                       (aignet$a::num-ins aigneta))
            (nat-equiv (nth aignet$c::*num-regs* aignetc)
                       (aignet$a::num-regs aigneta))
            (nat-equiv (nth aignet$c::*num-nxsts* aignetc)
                       (aignet$a::num-nxsts aigneta))
            (nat-equiv (nth aignet$c::*num-outs* aignetc)
                       (aignet$a::num-outs aigneta))
            (nat-equiv (nth aignet$c::*max-fanin* aignetc)
                       (aignet$a::max-fanin aigneta))))

     (local (in-theory (enable aignet-count-equivs)))
     (defthm aignet-count-equivs-implies
       (implies (aignet-count-equivs aignetc aigneta)
                (and (nat-equiv (nth aignet$c::*num-nodes* aignetc)
                                (aignet$a::num-nodes aigneta))
                     (nat-equiv (nth aignet$c::*num-ins* aignetc)
                                (aignet$a::num-ins aigneta))
                     (nat-equiv (nth aignet$c::*num-regs* aignetc)
                                (aignet$a::num-regs aigneta))
                     (nat-equiv (nth aignet$c::*num-nxsts* aignetc)
                                (aignet$a::num-nxsts aigneta))
                     (nat-equiv (nth aignet$c::*num-outs* aignetc)
                                (aignet$a::num-outs aigneta))
                     (nat-equiv (nth aignet$c::*max-fanin* aignetc)
                                (aignet$a::max-fanin aigneta))
                     (implies (natp (nth aignet$c::*num-nodes* aignetc))
                              (equal (nth aignet$c::*num-nodes* aignetc)
                                     (aignet$a::num-nodes aigneta)))
                     (implies (natp (nth aignet$c::*num-ins* aignetc))
                              (equal (nth aignet$c::*num-ins* aignetc)
                                     (aignet$a::num-ins aigneta)))
                     (implies (natp (nth aignet$c::*num-regs* aignetc))
                              (equal (nth aignet$c::*num-regs* aignetc)
                                     (aignet$a::num-regs aigneta)))
                     (implies (natp (nth aignet$c::*num-nxsts* aignetc))
                              (equal (nth aignet$c::*num-nxsts* aignetc)
                                     (aignet$a::num-nxsts aigneta)))
                     (implies (natp (nth aignet$c::*num-outs* aignetc))
                              (equal (nth aignet$c::*num-outs* aignetc)
                                     (aignet$a::num-outs aigneta)))
                     (implies (natp (nth aignet$c::*max-fanin* aignetc))
                              (equal (nth aignet$c::*max-fanin* aignetc)
                                     (aignet$a::max-fanin aigneta))))))

     (defthm aignet-count-equivs-unhide
       (equal (hide (aignet-count-equivs aignetc aigneta))
              (and (nat-equiv (nth aignet$c::*num-nodes* aignetc)
                              (aignet$a::num-nodes aigneta))
                   (nat-equiv (nth aignet$c::*num-ins* aignetc)
                              (aignet$a::num-ins aigneta))
                   (nat-equiv (nth aignet$c::*num-regs* aignetc)
                              (aignet$a::num-regs aigneta))
                   (nat-equiv (nth aignet$c::*num-nxsts* aignetc)
                              (aignet$a::num-nxsts aigneta))
                   (nat-equiv (nth aignet$c::*num-outs* aignetc)
                              (aignet$a::num-outs aigneta))
                   (nat-equiv (nth aignet$c::*max-fanin* aignetc)
                              (aignet$a::max-fanin aigneta))))
       :hints (("goal" :Expand ((:free (x) (hide x)))))))


   (defsection aignet-corr
     (defun-nx aignet-corr (aignetc aigneta)
       (and (aignet$a::aignet-well-formedp aigneta)
            (aignet$c::aignet-sizes-ok aignetc)
            (aignet$c::aignet-counts-accurate aignetc)
            (aignet$c::aignet-nodes-nonconst aignetc)
            (nat-equiv (aignet$c::max-fanin aignetc)
                       (aignet$c::aignet-find-max-fanin
                        (+ -1 (aignet$c::num-nodes aignetc))
                        aignetc))
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
                   (aignet$c::aignet-counts-accurate aignetc)
                   (aignet$c::aignet-nodes-nonconst aignetc)
                   ;; (aignet$c::aignet-max-fanin-correct aignetc)
                   (nat-equiv (nth aignet$c::*max-fanin* aignetc)
                              (aignet$c::aignet-find-max-fanin
                               (+ -1 (aignet$c::num-nodes aignetc))
                               aignetc))
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



   (local (defthm aignet-has-no-non-gate-when-counts-equal
            (implies (and (equal (stype-count :nxst aignet)
                                 (stype-count :nxst (lookup-id (1- n) aignet)))
                          (equal (stype-count :pi aignet)
                                 (stype-count :pi (lookup-id (1- n) aignet)))
                          (equal (stype-count :po aignet)
                                 (stype-count :po (lookup-id (1- n) aignet)))
                          (equal (stype-count :reg aignet)
                                 (stype-count :reg (lookup-id (1- n) aignet)))
                          (proper-node-listp aignet)
                          (posp n)
                          (<= n (nfix m))
                          (<= (nfix m) (node-count aignet)))
                     (equal (ctype (stype (car (lookup-id m aignet)))) :gate))
            :hints (("goal" :induct (proper-node-listp aignet)
                     :in-theory (e/d ((:i proper-node-listp))
                                     (lookup-id-in-extension-inverse))
                     :expand ((:free (x) (lookup-id x aignet))
                              (node-count aignet)
                              (proper-node-listp aignet)
                              (:free (type) (stype-count type aignet)))))
            :rule-classes nil))

   (local (defthm aignet-gates-onlyp-when-counts-equal
            (implies (and (nodes-correct aignet$c aignet)
                          (aignet-count-equivs aignet$c aignet)
                          (posp n)
                          (equal (stype-count :nxst aignet)
                                 (stype-count :nxst (lookup-id (1- n) aignet)))
                          (equal (stype-count :pi aignet)
                                 (stype-count :pi (lookup-id (1- n) aignet)))
                          (equal (stype-count :po aignet)
                                 (stype-count :po (lookup-id (1- n) aignet)))
                          (equal (stype-count :reg aignet)
                                 (stype-count :reg (lookup-id (1- n) aignet)))
                          (aignet-nodes-ok aignet)
                          (node-listp aignet))
                     (aignet$c::aignet-gates-onlyp n aignet$c))
            :hints (("goal" :use ((:instance aignet$c::not-aignet-gates-onlyp-implies-witness
                                   (n n) (aignet aignet$c))
                                  (:instance aignet-has-no-non-gate-when-counts-equal
                                   (m (aignet$c::aignet-nongate-witness n aignet$c))))))))


   (local (defthmd max-fanin-when-nodes-correct-lemma
            (implies (and (nodes-correct aignet$c aignet)
                          (equal (nfix (aignet$c::num-nodes aignet$c)) (+ 1 (node-count aignet)))
                          (aignet-extension-p aignet aignet-suff))
                     (equal (node-count (find-max-fanin aignet-suff))
                            (aignet$c::aignet-find-max-fanin (node-count aignet-suff) aignet$c)))
            :hints(("Goal" :in-theory (enable node-count find-max-fanin aignet$c::aignet-find-max-fanin)))))

   (local (defthm max-fanin-when-nodes-correct
            (implies (and (nodes-correct aignet$c aignet)
                          (equal (nfix (aignet$c::num-nodes aignet$c)) (+ 1 (node-count aignet))))
                     (equal (node-count (find-max-fanin aignet))
                            (aignet$c::aignet-find-max-fanin (node-count aignet) aignet$c)))
            :hints(("Goal" :in-theory (enable max-fanin-when-nodes-correct-lemma)))))

   (local (defthm find-max-fanin-of-lookup-id
            (implies (and (nodes-correct aignet$c aignet)
                          (equal (nfix (aignet$c::num-nodes aignet$c)) (+ 1 (node-count aignet)))
                          (<= (nfix n) (node-count aignet)))
                     (equal (node-count (find-max-fanin (lookup-id n aignet)))
                            (aignet$c::aignet-find-max-fanin n aignet$c)))
            :hints(("Goal" :in-theory (enable max-fanin-when-nodes-correct-lemma)))))

   (local (defthmd cdr-lookup-id-of-plus-1
            (implies (and (natp nn)
                          (< nn (node-count aignet)))
                     (equal (cdr (lookup-id (+ 1 nn) aignet))
                            (lookup-id nn aignet)))
            :hints (("goal" :in-theory (enable lookup-id)
                     :induct t)
                    (and stable-under-simplificationp
                         '(:expand ((lookup-id nn aignet)
                                    (lookup-id nn (cdr aignet)))
                           :in-theory (disable lookup-id-in-extension-inverse))))))

   (local (defthmd lookup-id-of-minus-1
            (implies (and (posp nn)
                          (<= nn (node-count aignet)))
                     (equal (lookup-id (+ -1 nn) aignet)
                            (cdr (lookup-id nn aignet))))
            :hints (("goal" :use ((:instance cdr-lookup-id-of-plus-1
                                   (nn (+ -1 nn))))))))

   (local (in-theory (disable acl2::nfix-equal-to-nonzero)))

   (local (defthmd stype-count-0-of-extension-inverse
            (implies (and (aignet-extension-bind-inverse)
                          (equal 0 (stype-count stype new)))
                     (equal (equal 0 (stype-count stype orig)) t))))

   (local (define type->stype-for-count (type regp)
            :verify-guards nil
            :returns (stype (iff (stypep stype) stype))
            (cond ((eql type (in-type)) (if (eql regp 1) :reg :pi))
                  ((eql type (out-type)) (if (eql regp 1) :nxst :po))
                  (t nil))))

   (local (defthm count-nodes-is-diff-of-stype-counts-pi
            (implies (and (syntaxp (and (quotep type)
                                        (quotep regp)))
                          (bitp regp)
                          (equal stype (type->stype-for-count type regp))
                          stype
                          ;; (aignet$c::aignetp aignet$c)
                          (nodes-correct aignet$c aignet)
                          (equal (nfix (aignet$c::num-nodes aignet$c)) (+ 1 (node-count aignet)))
                          (<= (nfix n) (+ 1 (node-count aignet))))
                     (equal (aignet$c::count-nodes n type regp aignet$c)
                            (- (stype-count stype aignet)
                               (stype-count stype (lookup-id (nfix (+ -1 (nfix n))) aignet)))))
            :hints(("Goal" :in-theory (enable aignet$c::count-nodes
                                              type->stype-for-count)
                    :induct t)
                   (and stable-under-simplificationp
                        '(:in-theory (e/d (lookup-id-of-minus-1
                                           stype-count-0-of-extension-inverse))
                          :cases ((equal (nfix n) (node-count aignet))
                                  (equal (nfix n) 0))
                          :expand ((:free (stype) (stype-count stype (lookup-id n aignet)))
                                   (:free (type regp) (aignet$c::count-nodes (nth 4 aignet$c) type regp aignet$c))
                                   (:free (type regp) (aignet$c::count-nodes (+ 1 (nfix n)) type regp aignet$c))
                                   ;; (stype-count :pi (cdr (lookup-id (+ 1 (nfix n)) aignet)))
                                   ))))))
   

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
           (let ((last (car (last clause))))
             (case-match last
               (('equal ('node-count ('lookup-stype . &)) ('node-count ('lookup-stype . &)))
                '(:in-theory (enable lookup-stype-in-bounds)))
               (& nil))))
      (and stable-under-simplificationp
           '(:expand ((:free (a b c stype)
                       (lookup-stype a stype (cons b c)))
                      (:free (a b c)
                       (lookup-reg->nxst a (cons b c)))
                      (:free (a b c)
                       (lookup-id a (cons b c)))
                      (:free (b)
                       (aignet$a::id->phase (+ 1 (node-count aignet)) b))
                      ;; (:free (b)
                      ;;  (aignet$a::id->phase nid b))
                      (:free (a b)
                       (aignet$a::lit->phase a b))
                      (:free (a b)
                       (aignet-litp a b))
                      ;; (:free (id aignet)
                      ;;  (id-slots id aignet))
                      )))
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
             (and witness
                  `(:computed-hint-replacement
                    ((and stable-under-simplificationp
                          '(:cases ((equal (nfix nid) (+ 1 (node-count aignet)))
                                    (< (nfix nid) (+ 1 (node-count aignet))))))
                     ;; (and stable-under-simplificationp
                     ;;      '(:expand ((:free (a b)
                     ;;                  (aignet$a::id->phase nid (cons a b)))
                     ;;                 (:free (a b)
                     ;;                  (aignet$a::lit->phase a b))
                     ;;                 (id-slots nid aignet))))
                     )
                    :clause-processor
                    (acl2::simple-generalize-cp
                     clause '((,witness . nid)))))))
      
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
            (implies (and (not (equal (ctype (stype x)) (gate-ctype)))
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

   (local (defthm id->phase-when-gate
            (implies (equal (ctype (stype (car (lookup-id id aignet)))) (gate-ctype))
                     (equal (aignet$a::id->phase id aignet)
                            (b* ((f0 (fanin :gate0 (lookup-id id aignet)))
                                 (f1 (fanin :gate1 (lookup-id id aignet))))
                              (if (eql 1 (regp (stype (car (lookup-id id aignet)))))
                                  (b-xor (b-xor (lit->neg f0)
                                                (aignet$a::id->phase (lit->var f0) aignet))
                                         (b-xor (lit->neg f1)
                                                (aignet$a::id->phase (lit->var f1) aignet)))
                                (b-and (b-xor (lit->neg f0)
                                                (aignet$a::id->phase (lit->var f0) aignet))
                                         (b-xor (lit->neg f1)
                                                (aignet$a::id->phase (lit->var f1) aignet)))))))
            :hints(("Goal" :in-theory (enable aignet$a::id->phase)))))

   (local (defthm node-count-lookup-reg->nxst-out-of-bounds
            (implies (< (node-count aignet) (nfix id))
                     (equal (node-count (lookup-reg->nxst id aignet))
                            0))))))



;; (local (defthm nth-under-nat-equiv
;;          (implies (and (syntaxp (and (quotep n)
;;                                      (member (unquote n)
;;                                              (list aignet$c::*num-outs*
;;                                                    aignet$c::*num-ins*
;;                                                    aignet$c::*num-regs* 
;;                                                    aignet$c::*num-nxsts*))))
;;                        (natp (nth n x))
;;                        (natp y))
;;                   (equal (equal (nth n x) y)
;;                          (nat-equiv (nth n x) y)))))

(local (std::add-default-post-define-hook :fix))


;; (local (defthm dumb
;;            (implies (equal (nfix n) (+ 1 m))
;;                     (equal (+ -1 (nfix n))
;;                            (fix m)))))

(local (in-theory (disable ACL2::INEQUALITY-WITH-NFIX-HYP-1
                           AIGNET$C::AIGNETP-IMPLIES-NUM-NODES
                           lookup-id-in-bounds-when-positive
                           lookup-id-out-of-bounds
                           stype-const-when-not-others
                           acl2::cancel_plus-equal-correct
                           node-count-of-atom
                           fanin-if-co-when-output
                           POSP-WHEN-CONSP-OF-LOOKUP-ID)))

(local (in-theory (enable aignet$c::lit->phase
                          aignet$c::aignet-init)))

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
            (max-fanin :logic aignet$a::max-fanin
                       :exec  aignet$c::max-fanin)

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
            (id->regp :logic aignet$a::id->regp
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
            
            (aignet-add-in^ :logic aignet$a::aignet-add-in^
                            :exec aignet$c::aignet-add-in
                            :protect t)
            (aignet-add-reg^ :logic aignet$a::aignet-add-reg^
                             :exec aignet$c::aignet-add-reg
                             :protect t)
            (aignet-add-and^ :logic aignet$a::aignet-add-and^
                              :exec aignet$c::aignet-add-and
                              :protect t)
            (aignet-add-xor^ :logic aignet$a::aignet-add-xor^
                              :exec aignet$c::aignet-add-xor
                              :protect t)
            (aignet-add-out^ :logic aignet$a::aignet-add-out^
                             :exec aignet$c::aignet-add-out
                             :protect t)
            (aignet-set-nxst^ :logic aignet$a::aignet-set-nxst^
                              :exec aignet$c::aignet-set-nxst
                              :protect t)
            (aignet-rollback :logic aignet$a::aignet-rollback
                             :exec aignet$c::aignet-rollback
                             :protect t)

            (aignet-init^ :logic aignet$a::aignet-init^
                          :exec aignet$c::aignet-init
                          :protect t)
            (aignet-clear :logic aignet$a::aignet-clear
                          :exec aignet$c::aignet-clear
                          :protect t)))


(fty::deffixtype aignet :pred node-listp :fix node-list-fix :equiv node-list-equiv)

(define aignet-add-in (aignet)
  :enabled t
  (mbe :logic (non-exec (cons (pi-node) (node-list-fix aignet)))
       :exec (if (< (the (unsigned-byte 29) (num-nodes aignet)) #x1fffffff)
                 (aignet-add-in^ aignet)
               (ec-call (aignet-add-in^ aignet)))))

(define aignet-add-reg (aignet)
  :enabled t
  (mbe :logic (non-exec (cons (reg-node) (node-list-fix aignet)))
       :exec (if (< (the (unsigned-byte 29) (num-nodes aignet)) #x1fffffff)
                 (aignet-add-reg^ aignet)
               (ec-call (aignet-add-reg^ aignet)))))

(define aignet-add-and ((f0 litp)
                         (f1 litp)
                         aignet)
  :guard (and (fanin-litp f0 aignet)
              (fanin-litp f1 aignet))
  :enabled t
  (mbe :logic (non-exec (cons (and-node (aignet-lit-fix f0 aignet)
                                         (aignet-lit-fix f1 aignet))
                              (node-list-fix aignet)))
       :exec (if (< (the (unsigned-byte 29) (num-nodes aignet)) #x1fffffff)
                 (aignet-add-and^ f0 f1 aignet)
               (ec-call (aignet-add-and^ f0 f1 aignet)))))

(define aignet-add-xor ((f0 litp)
                         (f1 litp)
                         aignet)
  :guard (and (fanin-litp f0 aignet)
              (fanin-litp f1 aignet))
  :enabled t
  (mbe :logic (non-exec (cons (xor-node (aignet-lit-fix f0 aignet)
                                         (aignet-lit-fix f1 aignet))
                              (node-list-fix aignet)))
       :exec (if (< (the (unsigned-byte 29) (num-nodes aignet)) #x1fffffff)
                 (aignet-add-xor^ f0 f1 aignet)
               (ec-call (aignet-add-xor^ f0 f1 aignet)))))

(define aignet-add-out ((f litp)
                         aignet)
  :guard (fanin-litp f aignet)
  :enabled t
  (mbe :logic (non-exec (cons (po-node (aignet-lit-fix f aignet))
                              (node-list-fix aignet)))
       :exec (if (< (the (unsigned-byte 29) (num-nodes aignet)) #x1fffffff)
                 (aignet-add-out^ f aignet)
               (ec-call (aignet-add-out^ f aignet)))))

(define aignet-set-nxst ((f litp)
                         (regid natp)
                         aignet)
  :guard (and (fanin-litp f aignet)
              (id-existsp regid aignet)
              (eql (id->type regid aignet) (in-type))
              (eql (id->regp regid aignet) 1))
  :enabled t
  (mbe :logic (non-exec (cons (nxst-node (aignet-lit-fix f aignet)
                                         (aignet-id-fix regid aignet))
                              (node-list-fix aignet)))
       :exec (if (< (the (unsigned-byte 29) (num-nodes aignet)) #x1fffffff)
                 (aignet-set-nxst^ f regid aignet)
               (ec-call (aignet-set-nxst^ f regid aignet)))))

(define aignet-init ((max-outs natp :type (integer 0 *))
                     (max-regs natp :type (integer 0 *))
                     (max-ins natp :type (integer 0 *))
                     (max-nodes posp :type (integer 1 *))
                     aignet)
  :enabled t
  (mbe :logic (non-exec nil)
       :exec (if (and (< (the (integer 0 *) max-outs) #x20000000)
                      (< (the (integer 0 *) max-regs) #x20000000)
                      (< (the (integer 0 *) max-ins) #x20000000)
                      (< (the (integer 0 *) max-nodes) #x20000000))
                 (aignet-init^ max-outs max-regs max-ins max-nodes aignet)
               (ec-call (aignet-init^ max-outs max-regs max-ins max-nodes aignet)))))


(defmacro aignet-fix (aignet)
  `(mbe :logic (non-exec (node-list-fix ,aignet))
        :exec ,aignet))


(defstobj-clone aignet2 aignet :suffix "2")


(define num-gates (aignet)
  :prepwork ((local (set-default-hints nil))
             (local (defthm gate-stype-count
                      (implies (aignet-nodes-ok aignet)
                               (equal (+ (stype-count :and aignet)
                                         (stype-count :xor aignet))
                                      (+ (node-count aignet)
                                         (- (stype-count :pi aignet))
                                         (- (stype-count :po aignet))
                                         (- (stype-count :reg aignet))
                                         (- (stype-count :nxst aignet)))))
                      :hints (("goal" :induct (node-count aignet)
                               :in-theory (enable (:i node-count))
                               :expand ((node-count aignet)
                                        (aignet-nodes-ok aignet)
                                        (:free (stype) (stype-count stype aignet))))))))
  :enabled t
  (mbe :logic (non-exec (+ (stype-count (and-stype) aignet)
                           (stype-count (xor-stype) aignet)))
       :exec (+ (num-nodes aignet)
                (- (+ 1  ;; constant
                      (num-ins aignet)
                      (num-regs aignet)
                      (num-outs aignet)
                      (num-nxsts aignet))))))
  
(define reg-id->nxst-lit ((id natp)
                          (aignet))
  :guard (and (id-existsp id aignet)
              (eql (id->type id aignet) (in-type))
              (eql (id->regp id aignet) 1))
  :returns (lit (and (litp lit)
                     (aignet-litp lit aignet))
                :hints((and stable-under-simplificationp
                            '(:in-theory (enable aignet-litp)))))
  :guard-hints (("goal" :in-theory (enable fanin-if-co
                                           lookup-id-in-bounds)))
  (b* ((nxst (reg-id->nxst id aignet)))
    (mbe :logic (non-exec (fanin-if-co (lookup-id nxst aignet)))
         :exec
         (if (int= (id->type nxst aignet) (out-type))
             (co-id->fanin nxst aignet)
           (mk-lit nxst 0))))
  ///
  (defthm reg-id->nxst-lit-id-lte-max-fanin
    (<= (lit-id (reg-id->nxst-lit id aignet))
        (node-count (find-max-fanin aignet)))
    :hints(("Goal" :in-theory (disable reg-id->nxst-lit
                                       aignet-litp-implies-id-lte-max-fanin)
            :use ((:instance aignet-litp-implies-id-lte-max-fanin
                   (lit (reg-id->nxst-lit id aignet))))))
    :rule-classes :linear))



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
  <li>@(see aignet-add-and) adds an and gate</li>
  <li>@(see aignet-add-xor) adds an xor gate</li>
  <li>@(see aignet-add-reg) adds a register</li>
  <li>@(see aignet-set-nxst) sets the next-state formula for a register.</li>
</ul>

<h5>Network size</h5>
<ul>
  <li>@(see num-nodes) returns the number of nodes in the network</li>
  <li>@(see num-ins) returns the number of primary inputs</li>
  <li>@(see num-outs) returns the number of primary outputs</li>
  <li>@(see num-gates) returns the number of gates</li>
  <li>@(see num-regs) returns the number of register nodes</li>
  <li>@(see num-nxsts) returns the number of next-state nodes</li>
  <li>@(see max-fanin) returns the index of the last fanin (non-output) node</li>
</ul>

<h5>General node queries</h5>
<ul>
 <li>@(see id-existsp) checks whether an ID is in bounds</li>
 <li>@(see id->type) looks up the type of some node -- constant (0), gate (1),
 input (2), or output (3)</li>
 <li>@(see id->regp) gets the register/xor bit for a node id, which
 distinguishes between types of gate (1 for XORs, 0 for ANDs), combinational
 input (1 for registers, 0 for primary inputs), and combinational output (1 for
 next-state, 0 for primary output).</li>
 <li>@(see id->phase) gets the value of this node in the all-0 evaluation.</li>
 <li>@(see fanin-litp) checks whether a literal can be used as a fanin.</li>
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
 <li>@(see gate-id->fanin0) gets the 0th fanin @(see literal) from an AND or XOR gate</li>
 <li>@(see gate-id->fanin1) gets the 1st fanin literal from an AND or XOR gate</li>
 <li>@(see co-id->fanin) gets the fanin literal from a next-state or primary output node</li>
</ul>

<h5>Misc</h5>

<ul>
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

  @(def aignet$a::aignet-init^)")


;; Network construction

(defxdoc aignet-add-in
  :short "@(call aignet-add-in) adds a new primary input node to the aignet."
  :long "<p>Logically this is just @('(cons (pi-node) aignet)').</p>
  <p>In the execution we update the necessary arrays, counts, etc.</p>
  @(def aignet$a::aignet-add-in^)")

(defxdoc aignet-add-reg
  :short "@(call aignet-add-reg) adds a new register node to the aignet."
  :long "<p>Logically this is just @('(cons (reg-node) aignet)').</p>
  <p>In the execution we update the necessary arrays, counts, etc.</p>
  @(def aignet$a::aignet-add-reg^)")

(defxdoc aignet-add-and
  :short "@(call aignet-add-and) adds an new AND gate node to the aignet with
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

  @(def aignet$a::aignet-add-and^)")

(defxdoc aignet-add-xor
  :short "@(call aignet-add-xor) adds an new XOR gate node to the aignet with
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

  @(def aignet$a::aignet-add-xor^)")

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

  @(def aignet$a::aignet-add-out^)")

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

  @(def aignet$a::aignet-set-nxst^)")

(defxdoc aignet-rollback
  :short "@(call aignet-rollback) rewinds the aignet so that node @('n') is the
          last node."
  :long "<p>Logically this is just:</p>
 @({
   (lookup-id n aignet)
  })

 <p>The guard requires that there are no next-state nodes that will be removed;
this is because the implementation of removing a next-state node is somewhat
more complicated than other kinds.</p>")


;; Network size

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

(defxdoc max-fanin
  :short "@(call max-fanin) returns the maximum index of a non-output/non-nextstate
          node in an aignet."
  :long "<p>Logically this is @('(node-count (find-max-fanin aignet))'), where
  @(see find-max-fanin) just finds the longest suffix whose first node is a fanin
  type.</p>
  <p>In the execution this is just a stobj field access.</p>
  @(def aignet$a::max-fanin)")



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

  @(def aignet$a::nxst-id->reg)")


(defxdoc gate-id->fanin0
  :short "@(call gate-id->fanin0) gets the 0th fanin @(see literal) of the AND
  gate node whose ID is @('id')."
  :long "<p>Logically this is just</p>

  @({
      (fanin :gate0 (lookup-id id aignet))
  })

  <p>The @(see fanin) function ensures that the literal returned is a valid
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
      (fanin :gate1 (lookup-id id aignet))
  })

  <p>The @(see fanin) function ensures that the literal returned is a valid
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
      (fanin :co (lookup-id id aignet))
  })

  <p>The @(see fanin) function ensures that the literal returned is a valid
  fanin, i.e. its ID is less than the ID of the CO node and is not a CO node
  itself.</p>

  <p>In the execution this is mostly a stobj array lookup in the node
  array.</p>

  @(def aignet$a::co-id->fanin)")


;; Misc

(defxdoc id->regp
  :short "@(call id->regp) gets the register bit from the node with ID @('id')."
  :long "<p>Logically this is @('(regp (stype (car (lookup-id id aignet))))').</p>
  <p>In the execution this is mostly a stobj array lookup in the node array.</p>

  @(def aignet$a::id->regp)")



(defxdoc literal
  :parents (base-api)
  :short "See @(see satlink::litp)."
  :long "<p>Aignet used to use a literal representation of its own, but now it
just borrows @(see satlink::satlink)'s.</p>")


(defxdoc utilities
  :parents (aignet)
  :short "Basic tools for using @(see aignet) networks.")


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
about than the simpler <see topic='@(url acl2::aig)'>Hons-AIG library</see>.
On the other hand, Aignet can sometimes be much faster than Hons-AIGs.  For a
good introduction with a more detailed comparison of Hons-AIGs and Aignet,
see:</p>

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
nodes.  See @(see node) for a reference.  Note that these node-related
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
@('stype-count'), @('lookup-stype') and @('lookup-reg->nxst')&mdash;and the
other functions for operating on logical nodes, e.g., the functions described
under @(see node), provide the logical basis for reasoning about most kinds of
access to the aignet.</p>

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

(xdoc::add-resource-directory "aignet" "images")

