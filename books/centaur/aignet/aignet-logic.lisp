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

(in-package "AIGNET$A")
(include-book "idp")
(include-book "litp")
(include-book "cutil/defmvtypes" :dir :system)
(include-book "cutil/defprojection" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)
(include-book "std/lists/equiv" :dir :system)
(include-book "tools/defmacfun" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/define" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "std/ks/two-nats-measure" :dir :system)
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
                           make-list-ac
                           acl2::duplicity-when-non-member-equal)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index)))

(defmacro const-type () 0)
(defmacro gate-type () 1)
(defmacro in-type () 2)
(defmacro out-type () 3)

(defsection aignet-logic
  :short "The logical story of what an aignet is"
  :long
 "<p> An aignet object is a representation of a finite-state machine or a
combinational circuit.  It is, abstractly, a DAG containing various types of
nodes: outputs, register inputs, AND gates, register outputs, inputs, and a
unique constant node.  It is implemented as a stobj containing various arrays
so as to provide various constant-time functions for examining nodes; @(see
aignet-exec).  However, we hide the complexity of the implementation in an
abstract stobj.  Here we describe the logical representation of that abstract
stobj.</p>

<p>

</p>

")



;; (defun const-node ()
;;   (declare (xargs :guard t))
;;   '(:const))
;; (defun const-node-p (node)
;;   (declare (xargs :guard t))
;;   (equal node (const-node)))

(defun pi-node ()
  (declare (xargs :guard t))
  '(:pi))
(defun pi-node-p (node)
  (declare (xargs :guard t))
  (equal node (pi-node)))

(defun ro-node ()
  (declare (xargs :guard t))
 '(:ro))
(defun ro-node-p (node)
  (declare (xargs :guard t))
  (equal node (ro-node)))

(cutil::defaggregate gate-node
                     ((fanin0 litp)
                      (fanin1 litp))
                     :tag :gate)

(cutil::defaggregate po-node
                     ((fanin litp))
                     :tag :po)

(cutil::defaggregate ri-node
                     ((fanin litp)
                      (reg idp))
                     :tag :ri)

(define const-node-p (node)
  (eq node nil)
  ///
  (defthm tag-when-const-node-p
    (implies (const-node-p node)
             (equal (tag node) nil))))

(define node-p (x)
  (or (pi-node-p x)
      (ro-node-p x)
      (gate-node-p x)
      (po-node-p x)
      (ri-node-p x)
      (const-node-p x))
  ///
  (defthm tags-when-node-p
    (implies (node-p node)
             (and (equal (equal (tag node) :pi)
                         (pi-node-p node))
                  (equal (equal (tag node) :ro)
                         (ro-node-p node))
                  (equal (equal (tag node) :gate)
                         (gate-node-p node))
                  (equal (equal (tag node) :ri)
                         (ri-node-p node))
                  (equal (equal (tag node) :po)
                         (po-node-p node)))))

  (defthmd node-p-when-all-others-ruled-out
    (implies (not (member (tag node)
                          '(:pi :ro :gate :ri :po)))
             (equal (node-p node)
                    (const-node-p node)))))

(cutil::deflist node-listp (x)
                (node-p x)
                :true-listp t)

(define proper-node-p (x)
  (and (node-p x)
       (not (const-node-p x)))
  :enabled t)

(cutil::deflist proper-node-listp (x)
                (proper-node-p x)
                :true-listp t)

(defthmd proper-node-listp-implies-node-listp
  (implies (proper-node-listp x)
           (node-listp x))
  :hints(("Goal" :in-theory (enable proper-node-listp
                                    node-listp))))
  



;; (cutil::deflist id-listp (x)
;;                 (idp x)
;;                 :true-listp t)

;; (cutil::defaggregate aigneta
;;                      ((pis id-listp "PI ids")
;;                       (ros id-listp "RO ids")
;;                       (pos id-listp "PO ids")
;;                       (ris id-listp "RI ids")
;;                       (nodes node-listp))
;;                      :tag :aignet)



(defprojection tags (x)
  (tag x))

(local
 (defthm induct-by-list-equiv
   t
   :rule-classes ((:induction
                   :pattern (list-equiv x y)
                   :scheme (acl2::fast-list-equiv x y)))))
(local (in-theory (enable (:induction acl2::fast-list-equiv))))


(defcong list-equiv equal (tags x) 1
  :hints(("Goal" :in-theory (enable tags))))

(define suffixp (x y)
  (or (list-equiv x y)
      (and (consp y)
           (suffixp x (cdr y))))
  ///
  (defthm len-when-suffixp
    (implies (suffixp x y)
             (<= (len x) (len y)))
    :rule-classes (:rewrite :forward-chaining))
  (defthm duplicity-when-suffixp
    (implies (suffixp x y)
             (<= (duplicity k x)
                 (duplicity k y)))
    :rule-classes (:rewrite :linear))
  ;; Leave just the rewrite rules enabled
  (in-theory (disable (:forward-chaining len-when-suffixp)
                      (:linear duplicity-when-suffixp)))
  (defthm tags-suffixp-when-suffixp
    (implies (suffixp x y)
             (suffixp (tags x) (tags y))))
  (defcong list-equiv equal (suffixp x y) 1)
  (defcong list-equiv equal (suffixp x y) 2)
  (defthm cdr-suffixp
    (implies (suffixp x y)
             (suffixp (cdr x) y)))
  (defthm len-suffixp-of-cdr
    (implies (and (suffixp x (cdr y))
                  (consp y))
             (< (len x) (len y)))
    :hints (("goal" :induct (list-equiv x y))))
  (defthm len-suffixp-of-cdr-not-equal
    (implies (and (suffixp x (cdr y))
                  (consp y))
             (not (equal (len x) (len y))))
    :hints (("goal" :use len-suffixp-of-cdr
             :in-theory (disable len-suffixp-of-cdr))))
  (defthm duplicity-suffixp-of-cdr
    (implies (and (suffixp x (cdr y))
                  (consp y)
                  (equal (car y) k))
             (< (duplicity k x) (duplicity k y)))
    :hints (("goal" :induct (list-equiv x y))))
  (defthm duplicity-suffixp-of-cdr-not-equal
    (implies (and (suffixp x (cdr y))
                  (consp y)
                  (equal (car y) k))
             (not (equal (duplicity k x) (duplicity k y))))
    :hints (("goal" :use duplicity-suffixp-of-cdr
             :in-theory (disable duplicity-suffixp-of-cdr))))
  (defthm suffixp-self
    (suffixp x x)))

(defsection suffixp-binder
  (defun suffixp-bind (x)
    (declare (xargs :mode :program))
    (case-match x
      ((lookup-fn & y)
       (if (member lookup-fn
                   '(lookup-node
                     lookup-pi
                     lookup-po
                     lookup-ro
                     lookup-ri))
           `((y . ,y))
         '((try-again . try-again))))
      (& '((try-again . try-again)))))

  (defthm len-when-suffixp-bind
    (implies (and (bind-free (suffixp-bind x))
                  (suffixp x y))
             (<= (len x) (len y)))
    :rule-classes ((:linear :trigger-terms ((len x)))))

  (defthm duplicity-when-suffixp-bind
    (implies (and (bind-free (suffixp-bind x))
                  (suffixp x y))
             (<= (duplicity k x) (duplicity k y)))
    :rule-classes ((:linear :trigger-terms ((duplicity k x))))))





;; (define reg-count ((aignet node-listp))
;;   :short "The number of registers in the aignet"
;;   :long "
;; <p>Surprise! this one is different. reg-count is not just the number of
;; :ro nodes.  Here is how the number of registers develops over time:
;; <ul>
;; <li>An aignet starts out with 0 regs, unsurprisingly.</li>
;; <li>Each RO that is added is an additional register.</li>
;; <li>Each RI that is added when reg-count <= num-regins is an additional
;; register.</li>
;; </ul>
;; </p>

;; <p>Why? Registers are connected implicitly.  We generally expect a bunch of ROs
;; to be added initially, and then an equal number of RIs to be added after some
;; logic, so that the number of RIs is <= the number of ROs at any point.  When
;; this is the case, the Nth RI added is just connected to the Nth RO; until the
;; Nth RI is added, the Nth RO is unconnected.  Also, in this case reg-count is
;; just the number of RO nodes.  (num-regins is always the number of RI nodes.)
;; </p>

;; <p>What if this pattern isn't followed?
;; <ul>
;; <li> Adding an RO is simple: it is initially unconnected, its RO index is the
;; reg-count, and it increases the reg-count by 1.
;; </li>
;; <li> When reg-count > num-regins and an RI is added, that RI is connected to the
;; RO whose index is num-regins, its RI index is num-regins, num-regins is
;; incremented and reg-count remains the same.
;; </li>
;; <li>When reg-count <= num-regins and an RI is added, that RI is permanently
;; unconnected to any RO.  Its RI index is num-regins; there is then no RO whose
;; index is reg-count (we'll say the [reg-count]th RO is node 0), and reg-count and
;; num-regins are both incremented.  (This maintains an invariant that reg-count >=
;; num-regins, so this case actually occurs exactly when reg-count == num-regins.)
;; </li>
;; </ul>
;; </p>"
;;   (if (endp aignet)
;;       0
;;     (case (tag (car aignet))
;;       (:ro (+ 1 (reg-count (cdr aignet))))
;;       (:ri (let ((rest (reg-count (cdr aignet))))
;;              (if (< (duplicity :ri (tags (cdr aignet))) rest)
;;                  rest
;;                (+ 1 rest))))
;;       (t (reg-count (cdr aignet)))))
;;   ///
;;   (defthm reg-count-gte-num-regins
;;     (<= (duplicity :ri (tags aignet)) (reg-count aignet))
;;     :rule-classes :linear)
;;   (defcong list-equiv equal (reg-count x) 1)
;;   (defthm reg-count-when-suffixp
;;     (implies (suffixp x y)
;;              (<= (reg-count x) (reg-count y)))
;;     :hints(("Goal" :in-theory (enable suffixp))))
;;   (defthm reg-count-when-suffixp-bind
;;     (implies (and (bind-free (suffixp-bind x))
;;                   (suffixp x y))
;;              (<= (reg-count x) (reg-count y)))
;;     :rule-classes ((:linear :trigger-terms ((reg-count x)))))
;;   ;; (defthm reg-count-when-suffixp-of-cdr
;;   ;;   (implies (and (suffixp x (cdr y))
;;   ;;                 (consp y)
;;   ;;                 (equal (tag (car y)) :ro))
;;   ;;            (and (< (reg-count x) (reg-count y))
;;   ;;                 (not (equal (reg-count x) (reg-count y)))))
;;   ;;   :hints (("goal" :use ((:instance reg-count-when-suffixp
;;   ;;                          (y (cdr y))))
;;   ;;            :in-theory (disable reg-count-when-suffixp))))
;;   (defthm reg-count-cdr-of-suffixp
;;     (implies (and (bind-free (suffixp-bind x))
;;                   (suffixp x y)
;;                   (equal (tag (car x)) :ro))
;;              (< (reg-count (cdr x)) (reg-count y)))
;;     :hints (("goal" :use ((:instance reg-count-when-suffixp
;;                            (x x)))
;;              :in-theory (disable reg-count-when-suffixp
;;                                  duplicity-when-suffixp)))
;;     :rule-classes ((:linear :trigger-terms ((reg-count (cdr x))))))
;;   (defthm reg-count-not-equal-cdr-of-suffixp
;;     (implies (and (bind-free (suffixp-bind x))
;;                   (suffixp x y)
;;                   (consp x)
;;                   (equal (tag (car x)) :ro))
;;              (< (reg-count (cdr x)) (reg-count y)))
;;     :hints (("goal" :use ((:instance reg-count-when-suffixp
;;                            (x x)))
;;              :in-theory (disable reg-count-when-suffixp
;;                                  duplicity-when-suffixp)))
;;     :rule-classes ((:linear :trigger-terms ((reg-count (cdr x))))))
;;   (defthm reg-count-cdr-linear
;;     (implies (and (consp x)
;;                   (equal (tag (car x)) :ro))
;;              (< (reg-count (cdr x)) (reg-count x)))
;;     :rule-classes ((:linear :trigger-terms ((reg-count (cdr x))))))
;;   (defthm reg-count-of-cons-ro
;;     (implies (eq (tag x) :ro)
;;              (equal (reg-count (cons x y))
;;                     (+ 1 (reg-count y)))))
;;   (defthm reg-count-of-atom
;;     (implies (not (consp x))
;;              (equal (reg-count x) 0)))
;;   (defthm reg-count-of-cons-non-ri/ro
;;     (implies (and (not (eq (tag x) :ro))
;;                   (not (eq (tag x) :ri)))
;;              (equal (reg-count (cons x y))
;;                     (reg-count y)))))





(define lookup-node ((id idp)
                     (aignet node-listp))
  :returns (suffix node-listp :hyp (node-listp aignet))
  (cond ((endp aignet) nil)
        ((equal (len aignet) (id-val id))
         aignet)
        (t (lookup-node id (cdr aignet))))
  ///
  (defcong id-equiv equal (lookup-node id aignet) 1)
  (defthm len-of-lookup-node
    (implies (<= (id-val n) (len aignet))
             (equal (len (lookup-node n aignet))
                    (id-val n)))
    :hints(("Goal" :in-theory (enable lookup-node))))
  (defthm lookup-node-0
    (equal (lookup-node 0 aignet) nil))
  (defthm lookup-node-in-bounds
    (iff (lookup-node n aignet)
         (and (< 0 (id-val n))
              (<= (id-val n) (len aignet)))))
  (defthm lookup-node-suffixp
    (suffixp (lookup-node id aignet) aignet)
    :hints(("Goal" :in-theory (enable suffixp))))
  (defthm lookup-node-consp
    (iff (consp (lookup-node id aignet))
         (lookup-node id aignet)))
  (defcong list-equiv list-equiv (lookup-node id aignet) 2)
  (defthm lookup-node-in-suffix
    (implies (and (suffixp aignet aignet2)
                  (<= (id-val id) (len aignet)))
             (list-equiv (lookup-node id aignet2)
                         (lookup-node id aignet)))
    :hints(("Goal" :in-theory (enable suffixp)))))


(define lookup-pi ((n natp)
                   (aignet node-listp))
  :returns (suffix node-listp :hyp (node-listp aignet))
  (cond ((endp aignet) nil)
        ((and (eq (tag (car aignet)) :pi)
              (equal (duplicity :pi (tags (cdr aignet))) (lnfix n)))
         aignet)
        (t (lookup-pi n (cdr aignet))))
  ///
  (defcong nat-equiv equal (lookup-pi n aignet) 1)
  (defthm num-ins-of-lookup-pi
    (implies (< (nfix n) (duplicity :pi (tags aignet)))
             (equal (duplicity :pi (tags (cdr (lookup-pi n aignet))))
                    (nfix n))))
  (defthm car-of-lookup-pi
    (implies (< (nfix n) (duplicity :pi (tags aignet)))
             (equal (tag (car (lookup-pi n aignet)))
                    :pi)))
  (defthm lookup-pi-in-bounds
    (iff (lookup-pi n aignet)
         (< (nfix n) (duplicity :pi (tags aignet)))))
  (defthm lookup-pi-suffixp
    (suffixp (lookup-pi n aignet) aignet)
    :hints(("Goal" :in-theory (enable suffixp))))
  (defthm lookup-pi-consp
    (iff (consp (lookup-pi id aignet))
         (lookup-pi id aignet))))

(define lookup-ro ((n natp)
                   (aignet node-listp))
  :returns (suffix node-listp :hyp (node-listp aignet))
  (cond ((endp aignet) nil)
        ((and (eq (tag (car aignet)) :ro)
              (equal (duplicity :ro (tags (cdr aignet)))
                     (lnfix n)))
         aignet)
        (t (lookup-ro n (cdr aignet))))
  ///
  (defcong nat-equiv equal (lookup-ro n aignet) 1)
  (defthm num-regs-of-lookup-ro
    (implies (< (nfix n) (duplicity :ro (tags aignet)))
             (equal (duplicity :ro (tags (cdr (lookup-ro n aignet))))
                    (nfix n))))
  (defthm car-of-lookup-ro
    (implies (lookup-ro n aignet)
             (equal (tag (car (lookup-ro n aignet)))
                    :ro)))
  ;; unlike the others, no guarantee that lookup-ro exists even if n < reg-count
  (defthm lookup-ro-suffixp
    (suffixp (lookup-ro n aignet) aignet)
    :hints(("Goal" :in-theory (enable suffixp))))
  (defthm lookup-ro-consp
    (iff (consp (lookup-ro id aignet))
         (lookup-ro id aignet))))

(define lookup-po ((n natp)
                   (aignet node-listp))
  :returns (suffix node-listp :hyp (node-listp aignet))
  (cond ((endp aignet) nil)
        ((and (eq (tag (car aignet)) :po)
              (equal (duplicity :po (tags (cdr aignet))) (lnfix n)))
         aignet)
        (t (lookup-po n (cdr aignet))))
  ///
  (defcong nat-equiv equal (lookup-po n aignet) 1)
  (defthm num-outs-of-lookup-po
    (implies (< (nfix n) (duplicity :po (tags aignet)))
             (equal (duplicity :po (tags (cdr (lookup-po n aignet))))
                    (nfix n))))
  (defthm car-of-lookup-po
    (implies (< (nfix n) (duplicity :po (tags aignet)))
             (equal (tag (car (lookup-po n aignet)))
                    :po)))
  (defthm lookup-po-in-bounds
    (iff (lookup-po n aignet)
         (< (nfix n) (duplicity :po (tags aignet)))))
  (defthm lookup-po-suffixp
    (suffixp (lookup-po n aignet) aignet)
    :hints(("Goal" :in-theory (enable suffixp))))
  (defthm lookup-po-consp
    (iff (consp (lookup-po id aignet))
         (lookup-po id aignet))))


;; NOTE this is different from the other lookups: it's by ID of the
;; corresponding RO node, not IO number.  I think the asymmetry is worth it
;; though.
(define lookup-reg->ri ((reg-id idp)
                        (aignet node-listp))
  :returns (suffix node-listp :hyp (node-listp aignet))
  (cond ((endp aignet) nil)
        ((and (eq (tag (car aignet)) :ri)
              (b* ((ro (ri-node->reg (car aignet))))
                (id-equiv reg-id ro)))
         aignet)
        (t (lookup-reg->ri reg-id (cdr aignet))))
  ///
  (defcong id-equiv equal (lookup-reg->ri reg-id aignet) 1)
  (defthm car-of-lookup-reg->ri
    (implies (lookup-reg->ri reg-id aignet)
             (and (equal (tag (car (lookup-reg->ri reg-id aignet))) :ri)
                  (id-equiv (ri-node->reg (car (lookup-reg->ri reg-id aignet)))
                            reg-id))))
  (defthm suffixp-of-lookup-reg->ri
    (suffixp (lookup-reg->ri reg-id aignet) aignet)
    :hints(("Goal" :in-theory (enable suffixp)))))


;; (define lookup-ri ((n natp)
;;                    (aignet node-listp))
;;   :returns (suffix node-listp :hyp (node-listp aignet))
;;   (cond ((endp aignet) nil)
;;         ((and (eq (tag (car aignet)) :ri)
;;               (b* ((ro (ri-node->reg (car aignet)))
;;                    ((cons ro-node ro-tail)
;;                     (lookup-node ro aignet)))
;;                 (and (eq (tag ro-node) :ro)
;;                      (equal (lnfix n) (duplicity :ro (tags ro-tail))))))
;;          aignet)
;;         (t (lookup-ri n (cdr aignet))))
;;   ///
;;   (defcong nat-equiv equal (lookup-ri n aignet) 1)
;;   (defthm car-of-lookup-ri
;;     (implies (lookup-ri n aignet)
;;              (and (equal (tag (car (lookup-ri n aignet)))
;;                          :ri)
;;                   (equal (ri-node->regnum (car (lookup-ri n aignet)))
;;                          (nfix n)))))
;;   (defthm lookup-ri-suffixp
;;     (suffixp (lookup-ri n aignet) aignet)
;;     :hints(("Goal" :in-theory (enable suffixp))))
;;   (defthm lookup-ri-consp
;;     (iff (consp (lookup-ri id aignet))
;;          (lookup-ri id aignet))))


         




;; (defun num-nodes (aignet)
;;   (declare (xargs :guard (aigneta-p aignet)))
;;   (len (aigneta->nodes aignet)))

;; (defun num-ins (aignet)
;;   (declare (xargs :guard (aigneta-p aignet)))
;;   (len (aigneta->pis aignet)))

;; (defun num-outs (aignet)
;;   (declare (xargs :guard (aigneta-p aignet)))
;;   (len (aigneta->pos aignet)))

;; (defun num-regins (aignet)
;;   (declare (xargs :guard (aigneta-p aignet)))
;;   (len (aigneta->ris aignet)))

;; (defun reg-count (aignet)
;;   (declare (xargs :guard (aigneta-p aignet)))
;;   (len (aigneta->ros aignet)))

(local (defthm equal-len-0
         (equal (equal (len x) 0)
                (not (consp x)))))











(define node->type ((node node-p))
  :enabled t
  (case (tag node)
    ((:pi :ro) (in-type))
    ((:po :ri) (out-type))
    (:gate     (gate-type))
    (t         (const-type))))

(define io-node->regp ((node node-p))
  :guard (or (int= (node->type node) (in-type))
             (int= (node->type node) (out-type)))
  :enabled t
  (case (tag node)
    ((:ri :ro) 1)
    (t 0)))

(define co-node->fanin ((node node-p))
  :guard (equal (node->type node) (out-type))
  :returns (lit litp)
  (lit-fix (if (equal (io-node->regp node) 1)
               (ri-node->fanin node)
             (po-node->fanin node)))
  :prepwork ((local (in-theory (e/d (node->type
                                     io-node->regp)
                                    ((force))))))
  ///
  (defthm co-node->fanin-of-po-node
    (equal (co-node->fanin (po-node f))
           (lit-fix f)))
  (defthm co-node->fanin-of-ri-node
    (equal (co-node->fanin (ri-node f n))
           (lit-fix f))))












(define aignet-litp ((lit litp)
                     (aignet node-listp))
  (and (<= (id-val (lit-id lit))
           (len aignet))
       (not (equal (node->type (car (lookup-node (lit-id lit) aignet)))
                   (out-type))))
  ///
  (defthm lit-id-bound-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (<= (id-val (lit-id lit)) (len aignet)))
    :rule-classes ((:linear :trigger-terms ((id-val (lit-id lit))))))
  (local (defthm <=-when-<-+-1
           (implies (and (< x (+ 1 y))
                         (integerp x) (integerp y))
                    (<= x y))))
  (defthm aignet-litp-in-suffix
    (implies (and (aignet-litp lit aignet)
                  (suffixp aignet aignet2))
             (aignet-litp lit aignet2)))
  (defcong lit-equiv equal (aignet-litp lit aignet) 1)
  (defcong list-equiv equal (aignet-litp lit aignet) 2))

(define aignet-idp ((id idp) aignet)
  (<= (id-val id) (len aignet))
  ///
  (defthm id-val-bound-when-aignet-idp
    (implies (aignet-idp id aignet)
             (<= (id-val id) (len aignet))))
  (local (defthm <=-when-<-+-1
           (implies (and (< x (+ 1 y))
                         (integerp x) (integerp y))
                    (<= x y))))
  (defthm aignet-idp-in-suffix
    (implies (and (aignet-idp id aignet)
                  (suffixp aignet aignet2))
             (aignet-idp id aignet2)))
  (defcong id-equiv equal (aignet-idp id aignet) 1)
  (defcong list-equiv equal (aignet-idp id aignet) 2)
  (defthm aignet-idp-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (aignet-idp (lit-id lit) aignet))
    :hints(("Goal" :in-theory (enable aignet-litp)))))


(defsection aignet-case
  (defmacro aignet-case (type &key const gate in out)
    `(case ,type
       (,(gate-type)      ,gate)
       (,(in-type)        ,in)
       (,(out-type)       ,out)
       (otherwise         ,const)))

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
       (,(gate-type)    ,(cadr (assoc-keyword :gate keys)))
       (,(in-type)
                        ,(if (assoc-keyword :ci keys)
                             (cadr (assoc-keyword :ci keys))
                           `(if (int= 1 ,regp)
                                ,(cadr (assoc-keyword :ro keys))
                              ,(cadr (assoc-keyword :pi keys)))))
       (,(out-type)     ,(if (assoc-keyword :co keys)
                             (cadr (assoc-keyword :co keys))
                           `(if (int= 1 ,regp)
                                ,(cadr (assoc-keyword :ri keys))
                              ,(cadr (assoc-keyword :po keys)))))
       (otherwise       ,(cadr (assoc-keyword :const keys))))))

(define aignet-nodes-ok ((aignet node-listp))
  (if (endp aignet)
      t
    (and (aignet-seq-case
          (node->type (car aignet))
          (io-node->regp (car aignet))
          :ci   t
          :po   (aignet-litp (co-node->fanin (car aignet))
                             (cdr aignet))
          :ri   (and (aignet-litp (co-node->fanin (car aignet))
                                  (cdr aignet))
                     (aignet-idp (ri-node->reg (car aignet))
                                 (cdr aignet)))
          :gate (let ((f0 (gate-node->fanin0 (car aignet)))
                      (f1 (gate-node->fanin1 (car aignet))))
                  (and (aignet-litp f0 (cdr aignet))
                       (aignet-litp f1 (cdr aignet)))))
         (aignet-nodes-ok (cdr aignet))))
  ///
  (defthm proper-node-list-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (node-listp aignet))
             (proper-node-listp aignet)))
  (defthm co-fanin-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-node id aignet)))
                         (out-type)))
             (< (id-val (lit-id (co-node->fanin
                                 (car (lookup-node id aignet)))))
                (id-val id)))
    :hints (("goal" :induct (lookup-node id aignet)
             :in-theory (enable lookup-node))))
  (defthm ri-reg-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-node id aignet)))
                         (out-type))
                  (equal (io-node->regp (car (lookup-node id aignet)))
                         1))
             (<= (id-val (ri-node->reg (car (lookup-node id aignet))))
                 (len aignet)))
    :hints (("goal" :induct (lookup-node id aignet)
             :in-theory (e/d (lookup-node aignet-idp)
                             ((force))))))
  (defthm ri-reg-aignet-idp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-node id aignet)))
                         (out-type))
                  (equal (io-node->regp (car (lookup-node id aignet)))
                         1))
             (aignet-idp (ri-node->reg (car (lookup-node id aignet)))
                         (cdr (lookup-node id aignet))))
    :hints (("goal" :induct (lookup-node id aignet)
             :in-theory (e/d (lookup-node aignet-idp)
                             ((force))))))
  (defthm gate-fanin0-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-node id aignet)))
                         (gate-type)))
             (< (id-val (lit-id (gate-node->fanin0
                                 (car (lookup-node id aignet)))))
                (id-val id)))
    :hints (("goal" :induct (lookup-node id aignet)
             :in-theory (enable lookup-node))))
  (defthm gate-fanin1-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-node id aignet))) (gate-type)))
             (< (id-val (lit-id (gate-node->fanin1
                                 (car (lookup-node id aignet)))))
                (id-val id)))
    :hints (("goal" :induct (lookup-node id aignet)
             :in-theory (enable lookup-node))))

  (defthm co-fanin-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-node id aignet))) (out-type)))
             (aignet-litp (co-node->fanin
                           (car (lookup-node id aignet)))
                          aignet))
    :hints (("goal" :induct (lookup-node id aignet)
             :in-theory (enable lookup-node)
             :expand ((aignet-nodes-ok aignet)))))
  (defthm gate-fanin0-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-node id aignet))) (gate-type)))
             (aignet-litp (gate-node->fanin0
                           (car (lookup-node id aignet)))
                          aignet))
    :hints (("goal" :induct (lookup-node id aignet)
             :in-theory (enable lookup-node)
             :expand ((aignet-nodes-ok aignet)))))
  (defthm gate-fanin1-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-node id aignet))) (gate-type)))
             (aignet-litp (gate-node->fanin1
                           (car (lookup-node id aignet)))
                          aignet))
    :hints (("goal" :induct (lookup-node id aignet)
             :in-theory (enable lookup-node)
             :expand ((aignet-nodes-ok aignet)))))
  (defcong list-equiv equal (aignet-nodes-ok x) 1
    :hints (("goal" :induct (list-equiv x acl2::x-equiv)
             :in-theory (disable (force)))))
  (defthm aignet-nodes-ok-of-suffix
    (implies (and (bind-free (suffixp-bind x))
                  (suffixp x y)
                  (aignet-nodes-ok y))
             (aignet-nodes-ok x))
    :hints(("Goal" :in-theory (enable suffixp aignet-nodes-ok)
            :induct (aignet-nodes-ok y))))

  (defthm lookup-reg->ri-out-of-bounds
    (implies (and (aignet-nodes-ok aignet)
                  (< (len aignet) (id-val id)))
             (not (lookup-reg->ri id aignet)))
    :hints(("Goal" :in-theory (e/d (lookup-reg->ri
                                    node->type
                                    aignet-idp
                                    io-node->regp)
                                   (id-val-bound-when-aignet-idp
                                    tags-when-node-p))))))

(define io-node->ionum ((node node-p)
                        (rest node-listp))
  :guard (or (equal (node->type node) (in-type))
             (and (equal (node->type node) (out-type))
                  (equal (io-node->regp node) 0) ))
  :guard-hints (("goal" :in-theory (enable node->type)))
  (lnfix (case (tag node)
           (:pi (duplicity :pi (tags rest)))
           (:ro (duplicity :ro (tags rest)))
           (:po (duplicity :po (tags rest)))))
  ///
  (defthm io-node->ionum-of-pi
    (equal (io-node->ionum '(:pi) rest)
           (duplicity :pi (tags rest))))

  (defthm io-node->ionum-of-ro
    (equal (io-node->ionum '(:ro) rest)
           (duplicity :ro (tags rest))))

  (defthm io-node->ionum-of-po-node
    (equal (io-node->ionum (po-node f) rest)
           (duplicity :po (tags rest)))
    :hints(("Goal" :in-theory (enable io-node->ionum)))))


  

(define co-orderedp ((id idp)
                     (aignet node-listp))
  :guard (and (<= (id-val id) (len aignet))
              (int= (node->type (car (lookup-node id aignet))) (out-type)))
  (< (id-val (lit-id (co-node->fanin (car (lookup-node id aignet))))) (id-val id))
  ///
  (defthm co-orderedp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (<= (id-val id) (len aignet))
                  (int= (node->type (car (lookup-node id aignet))) (out-type)))
             (co-orderedp id aignet))))

(define gate-orderedp ((id idp)
                       (aignet node-listp))
  :guard (and (<= (id-val id) (len aignet))
              (int= (node->type (car (lookup-node id aignet))) (gate-type)))
  (and (< (id-val (lit-id (gate-node->fanin0 (car (lookup-node id aignet))))) (id-val id))
       (< (id-val (lit-id (gate-node->fanin1 (car (lookup-node id aignet))))) (id-val id)))
  ///
  (defthm gate-orderedp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (<= (id-val id) (len aignet))
                  (int= (node->type (car (lookup-node id aignet))) (gate-type)))
             (gate-orderedp id aignet))))

  
  




(define create-aignet ()
  nil)

                   

(defthm lookup-node-of-len-of-suffix
  (implies (suffixp x y)
           (list-equiv (lookup-node (to-id (len x)) y)
                       x))
  :hints(("Goal" :in-theory (enable lookup-node))))


;; (defsection lookup-ro-of-reg-count-suffix

;;   (defthm lookup-ro-implies-linear
;;     (implies (lookup-ro n x)
;;              (< (nfix n) (reg-count x)))
;;     :hints(("Goal" :in-theory (enable lookup-ro
;;                                       reg-count)))
;;     :rule-classes ((:linear :trigger-terms ((reg-count x)))))

;;   (defcong list-equiv list-equiv (lookup-ro n x) 2
;;     :hints(("Goal" :in-theory (enable lookup-ro))))

;;   (defthm lookup-ro-equal-when-suffixp
;;     (implies (and (suffixp x y)
;;                   (lookup-ro n x)
;;                   (lookup-ro n y))
;;              (list-equiv (lookup-ro n x) (lookup-ro n y)))
;;     :hints(("Goal" :in-theory (enable lookup-ro suffixp)
;;             :induct t)
;;            (and stable-under-simplificationp
;;                 '(:cases ((<= (reg-count x) (reg-count (cdr y))))))))

;;   (defthm suffixp-nil
;;     (suffixp nil x)
;;     :hints(("Goal" :in-theory (enable suffixp))))


;;   (defthm lookup-ro-of-reg-count-suffix
;;     (implies (and (suffixp x y)
;;                   (equal (node->type (car x)) (in-type))
;;                   (equal (io-node->regp (car x)) 1))
;;              (list-equiv (lookup-ro (reg-count (cdr x)) y)
;;                          x))
;;     :hints(("Goal" :in-theory (enable lookup-ro
;;                                       suffixp
;;                                       node->type io-node->regp)
;;             :induct t)
;;            (and stable-under-simplificationp
;;                 '(:use ((:instance lookup-ro-equal-when-suffixp
;;                          (n (reg-count (cdr x))))))))))



(defthm type-of-lookup-ro
  (and (equal (node->type (car (lookup-ro n aignet)))
              (if (lookup-ro n aignet)
                  (in-type)
                (const-type)))
       (equal (io-node->regp (car (lookup-ro n aignet)))
              (if (lookup-ro n aignet)
                  1
                0)))
  :hints(("Goal" :in-theory (enable node->type io-node->regp)
          :cases ((lookup-ro n aignet)))))

(defthm type-of-lookup-ri
  (and (equal (node->type (car (lookup-reg->ri n aignet)))
              (if (lookup-reg->ri n aignet)
                  (out-type)
                (const-type)))
       (equal (io-node->regp (car (lookup-reg->ri n aignet)))
              (if (lookup-reg->ri n aignet)
                  1 0)))
  :hints(("Goal" :in-theory (enable node->type io-node->regp)
          :cases ((lookup-reg->ri n aignet)))))




(defsection gate-node-misc
  (defthm node-p-of-gate-node
    (implies (and (litp f0) (litp f1))
             (node-p (gate-node f0 f1)))
    :hints(("Goal" :in-theory (enable node-p))))

  (defthm node->type-of-gate-node
    (equal (node->type (gate-node f0 f1))
           (gate-type))
    :hints(("Goal" :in-theory (enable node->type)))))

(defsection po-node-misc
  (defthm node-p-of-po-node
    (implies (litp f)
             (node-p (po-node f)))
    :hints(("Goal" :in-theory (enable node-p))))

  (defthm node->type-of-po-node
    (equal (node->type (po-node f))
           (out-type))
    :hints(("Goal" :in-theory (enable node->type))))

  (defthm io-node->regp-of-po-node
    (equal (io-node->regp (po-node f))
           0)
    :hints(("Goal" :in-theory (enable io-node->regp)))))

(defsection ri-node-misc
  (defthm node-p-of-ri-node
    (implies (and (litp f) (idp r))
             (node-p (ri-node f r)))
    :hints(("Goal" :in-theory (enable node-p))))

  (defthm node->type-of-ri-node
    (equal (node->type (ri-node f n))
           (out-type))
    :hints(("Goal" :in-theory (enable node->type))))

  (defthm io-node->regp-of-ri-node
    (equal (io-node->regp (ri-node f n))
           1)
    :hints(("Goal" :in-theory (enable io-node->regp)))))


;; (defthm reg-count-suffixp-by-node->type/regp
;;   (implies (and (bind-free (suffixp-bind x))
;;                 (suffixp x y)
;;                 (equal (node->type (car x)) (in-type))
;;                 (equal (io-node->regp (car x)) 1))
;;            (< (reg-count (cdr x)) (reg-count y)))
;;   :hints(("Goal" :in-theory (enable node->type
;;                                     io-node->regp)))
;;   :rule-classes ((:linear :trigger-terms
;;                   ((reg-count (cdr x))))))

(local (defthm len-cdr-when-consp
         (implies (consp x)
                  (< (len (cdr x)) (len x)))
         :rule-classes :linear))

(define aignet-lit-fix ((x litp)
                        (aignet node-listp))
  :verify-guards nil
  :measure (len aignet)
  :returns (fix)
  (b* ((id (lit-id x))
       (look (lookup-node id aignet))
       ((unless look)
        (mk-lit 0 (lit-neg x)))
       ((cons node rest) look)
       ((when (eql (node->type node) (out-type)))
        (lit-negate-cond
         (aignet-lit-fix (co-node->fanin node) rest)
         (lit-neg x))))
    (lit-fix x))
  ///
  (defthm litp-of-aignet-lit-fix
    (litp (aignet-lit-fix x aignet)))
  (verify-guards aignet-lit-fix)
  
  (local (defthm lookup-node-in-suffix-bind
           (implies (and (bind-free (suffixp-bind x))
                         (suffixp x y)
                         (< (id-val id) (len x)))
                    (list-equiv (lookup-node id (cdr x))
                                (lookup-node id y)))
           :hints(("Goal" :in-theory (enable suffixp lookup-node)))))

  (defthm aignet-litp-of-aignet-lit-fix
    (aignet-litp (aignet-lit-fix x aignet) aignet)
    :hints(("Goal" 
            :induct (aignet-lit-fix x aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable aignet-litp)))))

  (defthm aignet-lit-fix-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (equal (aignet-lit-fix lit aignet)
                    (lit-fix lit)))
    :hints(("Goal" :in-theory (enable aignet-litp
                                      aignet::equal-of-mk-lit)))))

(define aignet-id-fix ((x idp) aignet)
  (if (<= (id-val x) (len aignet))
      (id-fix x)
    (to-id 0))
  ///
  (defthm idp-of-aignet-id-fix
    (idp (aignet-id-fix x aignet)))
  (defthm aignet-idp-of-aignet-id-fix
    (aignet-idp (aignet-id-fix x aignet) aignet)
    :hints(("Goal" :in-theory (enable aignet-idp))))
  (defthm aignet-id-fix-when-aignet-idp
    (implies (aignet-idp id aignet)
             (equal (aignet-id-fix id aignet)
                    (id-fix id)))
    :hints(("Goal" :in-theory (enable aignet-idp)))))
             
