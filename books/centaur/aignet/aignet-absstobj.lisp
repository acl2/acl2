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

(include-book "aignet-exec")
(local (include-book "aignet-exec-thms"))

(include-book "aignet-logic-interface")

(include-book "centaur/misc/absstobjs" :dir :system)
(include-book "tools/clone-stobj" ::dir :system)

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "clause-processors/generalize" :dir :system))
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


(local
 (progn
   (defun-sk innums-correct (aignetc aigneta)
     (forall n
             (implies (< (nfix n) (aignet$a::num-ins aigneta))
                      (id-equiv (nth n (nth aignet$c::*insi* aignetc))
                                (to-id (len (lookup-stype n (pi-stype) aigneta))))))
     :rewrite :direct)

   (in-theory (disable innums-correct))

   (defun-sk outnums-correct (aignetc aigneta)
     (forall n
             (implies (< (nfix n) (aignet$a::num-outs aigneta))
                      (id-equiv (nth n (nth aignet$c::*outsi* aignetc))
                                (to-id (len (lookup-stype n (po-stype) aigneta))))))
     :rewrite :direct)

   (in-theory (disable outnums-correct))

   (defun-sk regnums-correct (aignetc aigneta)
     (forall
      n
      (implies
       (< (nfix n) (aignet$a::num-regs aigneta))
       (id-equiv (nth n (nth aignet$c::*regsi* aignetc))
                 (aignet$a::regnum->id n aigneta))))
     :rewrite :direct)

   (in-theory (disable regnums-correct))
   (in-theory (enable aignet$c::regnum->id))


   (defsection nodes-correct
     (defun-sk nodes-correct (aignetc aigneta)
       (forall
        nid
        (implies
         (and (natp nid)
              (case-split (< nid (aignet$a::num-nodes aigneta))))
         (let ((slot0 (nth (* 2 nid)
                           (nth aignet$c::*nodesi* aignetc)))
               (slot1 (nth (+ 1 (* 2 nid))
                           (nth aignet$c::*nodesi* aignetc)))
               (id (to-id nid)))
           (and (equal (aignet$c::snode->type slot0)
                       (node->type
                        (car (lookup-id id aigneta))))
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
                (implies (equal (aignet$a::id->type id aigneta)
                                (out-type))
                         (equal (aignet$c::snode->fanin0 slot0)
                                (aignet$a::co-id->fanin id aigneta)))
                (implies (and (equal (aignet$a::id->type id aigneta)
                                     (in-type))
                              (equal (aignet$a::io-id->regp id aigneta)
                                     1))
                         (equal (aignet$c::snode->regid slot0)
                                (aignet$a::reg-id->nxst id aigneta)))
                (implies (and (equal (aignet$a::id->type id aigneta)
                                     (out-type))
                              (equal (aignet$a::io-id->regp id aigneta)
                                     1))
                         (equal (aignet$c::snode->regid slot1)
                                (aignet$a::nxst-id->reg id aigneta)))
                (implies (equal (aignet$a::id->type id aigneta)
                                (gate-type))
                         (and (equal (aignet$c::snode->fanin0 slot0)
                                     (aignet$a::gate-id->fanin0 id aigneta))
                              (equal (aignet$c::snode->fanin1 slot1)
                                     (aignet$a::gate-id->fanin1 id aigneta))))
                ))))
       :rewrite :direct)

     (in-theory (disable nodes-correct))


     ;;                     nodes-correct-necc))
     ;; (defun slot0-bind-free (idx mfc state)
     ;;   (declare (xargs :mode :program :stobjs state)
     ;;            (ignore state))
     ;;   (prog2$ (cw "bind-free idx: ~x0~%unify-subst: ~x1"
     ;;               idx (acl2::mfc-unify-subst mfc))
     ;;           (case-match idx
     ;;             (('binary-* ''2 x) `((nid . ,x)))
     ;;             (('binary-+ ''2 ('binary-* ''2 x)) `((nid . (binary-+ '1 ,x)))))))

     ;; (defthm nodes-correct-rw-slot0
     ;;   (implies
     ;;    (and (bind-free
     ;;          (case-match idx
     ;;             (('binary-* ''2 x) `((nid . ,x)))
     ;;             (('binary-+ ''2 ('binary-* ''2 x)) `((nid . (binary-+ '1 ,x)))))
     ;;          (nid))
     ;;         (nodes-correct aignetc aigneta)
     ;;         (equal idx (* 2 nid))
     ;;         (natp nid)
     ;;         (case-split (< nid (aignet$a::num-nodes aigneta))))
     ;;    (let ((slot0 (nth idx
     ;;                       (nth aignet$c::*nodesi* aignetc)))
     ;;          (id (to-id nid)))
     ;;      (and (equal (aignet$c::snode->type slot0)
     ;;                  (node->type
     ;;                   (car (lookup-id id aigneta))))
     ;;           (implies (equal (aignet$a::id->type id aigneta)
     ;;                           (out-type))
     ;;                    (equal (aignet$c::snode->fanin0 slot0)
     ;;                           (aignet$a::co-id->fanin id aigneta)))
     ;;           (implies (and (equal (aignet$a::id->type id aigneta)
     ;;                                (in-type))
     ;;                         (equal (aignet$a::io-id->regp id aigneta)
     ;;                                1))
     ;;                    (equal (aignet$c::snode->nxst slot0)
     ;;                           (aignet$a::regnum->nxst
     ;;                            (reg-count
     ;;                             (cdr (lookup-id id aigneta)))
     ;;                            aigneta)))
     ;;           (implies (equal (aignet$a::id->type id aigneta)
     ;;                           (gate-type))
     ;;                    (equal (aignet$c::snode->fanin0 slot0)
     ;;                           (aignet$a::gate-id->fanin0 id aigneta)))
     ;;           )))
     ;;   :hints (("Goal" :use nodes-correct-necc)))

     ;; (defthm nodes-correct-rw-slot2
     ;;    (implies
     ;;     (and (nodes-correct aignetc aigneta)
     ;;          (natp nid)
     ;;          (case-split (< nid (aignet$a::num-nodes aigneta))))
     ;;     (let ((slot1 (nth (+ 1 (* 2 nid))
     ;;                       (nth aignet$c::*nodesi* aignetc)))
     ;;           (id (to-id nid)))
     ;;       (and (equal (aignet$c::snode->phase slot1)
     ;;                   (aignet$a::id->phase id aigneta))
     ;;            (equal (aignet$c::snode->regp slot1)
     ;;                   (aignet$a::io-id->regp id aigneta))
     ;;            (implies (or (equal (aignet$a::id->type id aigneta)
     ;;                                (in-type))
     ;;                         (equal (aignet$a::id->type id aigneta)
     ;;                                (out-type)))
     ;;                     (equal (aignet$c::snode->ionum slot1)
     ;;                            (aignet$a::io-id->ionum id aigneta)))
     ;;            (implies (equal (aignet$a::id->type id aigneta)
     ;;                            (gate-type))
     ;;                     (equal (aignet$c::snode->fanin1 slot1)
     ;;                            (aignet$a::gate-id->fanin1 id aigneta)))
     ;;            )))
     ;;   :hints (("Goal" :use nodes-correct-necc)))
     )

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
                      (:free (a b)
                       (aignet$a::id->phase (to-id a) b))
                      (:free (a b)
                       (aignet$a::lit->phase a b))
                      (:free (a b)
                       (aignet-litp a b)))))
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
           '(:cases ((equal (nfix nid) (+ 1 (len aignet))))))))

   ;; (local (in-theory (disable aignet$c::aignet-regs-in-bounds)))

   (local (in-theory (e/d* (aignet$c::aignet-frame-thms
                            aignet$a::id->type))))

   (defthm <-0-of-to-id
     (equal (< 0 (to-id x))
            (< 0 (nfix x))))

   (defthm <-0-len-is-consp
     (equal (< 0 (len x))
            (consp x)))

   (defthm equal-0-of-to-id
     (equal (equal 0 (to-id x))
            (equal 0 (nfix x)))
     :hints (("goal" :use ((:instance <-0-of-to-id))
              :in-theory (disable <-0-of-to-id))))

   (defthm equal-0-of-len
     (equal (equal 0 (len x))
            (not (consp x))))


   (local (in-theory (enable ACL2::ELIM-PLUS-ONE)))

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

   (in-theory (disable (force)))))


(acl2::defabsstobj-events aignet
  :concrete aignet$c::aignet
  :recognizer (aignetp :logic aignet$a::aignet-well-formedp
                       :exec aignet$c::aignetp)
  :creator (acl2::create-aignet :logic aignet$a::create-aignet
                                :exec aignet$c::create-aignet)
  :corr-fn aignet-corr
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
            
            (fanout-litp :logic aignet$a::fanout-litp
                         :exec aignet$c::fanout-litp$inline)
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
