; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2020 Centaur Technology
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


; The observability transform in observability.lisp is important for certain
; problems where the top-level hypotheses must be assumed in order to find
; sufficiently many internal equivalences in the conclusion so as to quickly
; prove it.  That is, if there are pairs or sets of AIG nodes in the Boolean
; formula of the conclusion that are equivalent, but only under some
; assumptions implied by the hypotheses of the theorem, the observability
; transform helps to find them.

; We want to extend this by automatically finding important internal nodes for
; which some large subgraphs of the AIG have observable behavior only if some
; such node is active.  More precisely, we want to pick pairings of a literal
; to assume and a subgraph on which to assume it, such that all or most of the
; subgraph is unobservable when that literal is false.  Then we'll duplicate
; that subgraph with inputs mapped to muxes ( assum-lit ? input : assum_input )
; where assum-lit is true if all of the inputs are assigned their respective
; assum_inputs.


;      Recursive Application of Observability Conditions

; There need not be only one unique observability literal guarding a subtree.
; We can effectively make this a recursive algorithm by tracking

;   1) EXT-OBS, A conjunction of literals that must all be satisfied or the current
;   subtree won't be observable.
;   2) IN-SUBST, a vector of input substitution expressions such that
;          a) when EXT-OBJ is satisfied, the substitution
;             evaluates to the original inputs (correctness condition)
;          b) the outputs of the substitution always satisfy EXT-OBS
;             (usefulness condition).

; Whenever we choose an observability condition OBS to apply to some subtree,
; we conjoin it to EXT-OBS and update IN-SUBST to be, effectively, OBS ?
; in-subst : satisfying_assign, where satisfying_assign makes the conjunction
; of OBS and EXT-OBS true.


;    Choosing Observability Conditions

; If a node N has direct fanout nodes F1 ... Fn and is not connected to an
; output, then a literal D is an "observability dominator" of N if for all i in
; 1..n, it is also either an observability dominator of Fi, or Fi is an AND
; node where D is the sibling of node N and D is less than N according to some
; ranking of nodes.  This last condition is important for the following situation:
;  n0 = AND(n1,n2) ; n1 is unobservable if ~n2, n2 is unobservable if ~n1
;  n1 = AND(n3,n4) ;
;  n2 = AND(n3,n5)
;  n4 = XOR(n2,n0)
;  n3 = XOR(n1,n0)
;  Then when n1=n2=n0=0, n4 and n3 are both supposed to be unobservable.
;  However, if we toggle n0, then n5 is also toggled even though it's not 

; Without the ranking, n3 

; A combinational output has no observability dominators, therefore a node that
; has a combinational output as a direct fanout has no observability
; dominators.

; An observability dominator of node N is a literal L for which a toggle of the
; value of N cannot be observed in any output unless L is true.

(include-book "transform-utils")
(include-book "levels")

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth
                           update-nth
                           resize-list
                           make-list-ac
                           true-listp-update-nth
                           acl2::nfix-when-not-natp
                           ;; acl2::resize-list-when-empty
                           ;; acl2::make-list-ac-redef
                           ;; set::double-containment
                           ;; set::sets-are-true-lists
                           acl2::nth-when-zp
                           ;; acl2::nth-with-large-index
                           )))
(local (std::add-default-post-define-hook :fix))

(defines id-eval-toggle
  :prepwork ((local (in-theory (disable lookup-id-in-bounds-when-positive
                                        lookup-id-out-of-bounds))))
  :ruler-extenders :lambdas
  (define lit-eval-toggle ((lit litp) (toggle natp) invals regvals aignet)
    :guard (and (fanin-litp lit aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length regvals)))
    :measure (acl2::two-nats-measure (lit-id lit) 1)
    :verify-guards nil
    (b-xor (id-eval-toggle (lit-id lit) toggle invals regvals aignet)
           (lit-neg lit)))

  (define eval-and-of-lits-toggle ((lit1 litp)
                            (lit2 litp)
                            (toggle natp)
                            invals regvals aignet)
    :guard (and (fanin-litp lit1 aignet)
                (fanin-litp lit2 aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length
                                       regvals)))
    :measure (acl2::two-nats-measure
              (max (lit-id lit1)
                   (lit-id lit2))
              2)
    (b-and (lit-eval-toggle lit1 toggle invals regvals aignet)
           (lit-eval-toggle lit2 toggle invals regvals aignet)))

  (define eval-xor-of-lits-toggle ((lit1 litp)
                            (lit2 litp)
                            (toggle natp)
                            invals regvals aignet)
    :guard (and (fanin-litp lit1 aignet)
                (fanin-litp lit2 aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length
                                       regvals)))
    :measure (acl2::two-nats-measure
              (max (lit-id lit1)
                   (lit-id lit2))
              2)
    (b-xor (lit-eval-toggle lit1 toggle invals regvals aignet)
           (lit-eval-toggle lit2 toggle invals regvals aignet)))

  (define id-eval-toggle ((id natp) (toggle natp) invals regvals aignet)
    :guard (and (id-existsp id aignet)
                (<= (num-ins aignet) (bits-length invals))
                (<= (num-regs aignet) (bits-length regvals)))
    :measure (acl2::two-nats-measure id 0)
    :hints(("Goal" :in-theory (enable aignet-idp)))
    (let ((ans
           (b* (((unless (mbt (id-existsp id aignet)))
                 ;; out-of-bounds IDs are false
                 0)
                (type (id->type id aignet)))
             (aignet-case
               type
               :gate (b* ((f0 (gate-id->fanin0 id aignet))
                          (f1 (gate-id->fanin1 id aignet)))
                       (if (int= (id->regp id aignet) 1)
                           (eval-xor-of-lits-toggle
                            f0 f1 toggle invals regvals aignet)
                         (eval-and-of-lits-toggle
                          f0 f1 toggle invals regvals aignet)))
               :in    (if (int= (id->regp id aignet) 1)
                          (get-bit (ci-id->ionum id aignet) regvals)
                        (get-bit (ci-id->ionum id aignet) invals))
               :const 0))))
      (if (eql (lnfix id) (lnfix toggle))
          (b-not ans)
        ans)))
  ///
  (fty::deffixequiv-mutual id-eval-toggle)
  (verify-guards id-eval-toggle))



(define output-eval-toggle ((n natp) (toggle natp) invals regvals aignet)
  :guard (and (< n (num-outs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (lit-eval-toggle (outnum->fanin n aignet) toggle invals regvals aignet))

(define nxst-eval-toggle ((n natp) (toggle natp) invals regvals aignet)
  :guard (and (< n (num-regs aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  (lit-eval-toggle (regnum->nxst n aignet) toggle invals regvals aignet))



;; For each node starting at the outputs and working our way back, we need to
;; find the intersection of the observability dominators among all the fanouts,
;; with two exceptions: (1) a node connected to a CO has no observability
;; dominators and (2) a node whose only fanout is an AND gate additionally has its sibling
;; as an observability dominator.

;; To track this easily, we'll sweep first over the COs and then backwards over
;; the nodes.  At all times, each node tracks its observability info, which is either
;;   - T, meaning it hasn't been found to be observable yet
;;   - a list of literals, the possible observability dominators from the fanouts swept so far.


;; What invariant is maintained by this algorithm?  Once a node's observability
;; info has been completed, it suggests a set of conditions under which the
;; node is known not to be observable:
;;  - if not reached (T) , then it's never observable
;;  - if some dominator evaluates to 0, it's not observable.
;; This is formalized as obs-dom-info-observable-p.

;; When we're all done with a node, it'll be the case that when it is not
;; observable (under some inputs), it can be toggled without causing a change
;; in value in any node that is observable (under those inputs).  Call this
;; property OBSERVABILITY-DONE-INVARIANT.

;; But until we're done with a node, what does its observability info mean?
;; When we've swept some but not all of its fanouts, a toggle in that node
;; could still cause a change in some fanout that has been swept.  E.g. if node
;; A is a direct fanin of B, but also a fanin of C which is the other fanin of
;; B, and we have swept B but not C, then A's observability info might seem to
;; allow it to be toggled without affecting B, but in fact it could still
;; affect B through C.  Similarly, it could affect B through a longer chain.

;; So instead we'll state an invariant in terms of direct fanouts of A that
;; have been swept, and that is more explicitly in terms of the observability
;; structure.  When all direct fanouts of A have been swept, this will imply
;; OBSERVABILITY-DONE-INVARIANT.


(define obs-dom-info-p (x)
  (or (eq x t) (lit-listp x))
  ///
  (defthm lit-listp-when-obs-dom-info-p
    (implies (and (not (equal x t))
                  (obs-dom-info-p x))
             (lit-listp x)))
  (define obs-dom-info-fix ((x obs-dom-info-p))
    :returns (new-x obs-dom-info-p)
    :inline t
    (mbe :logic (if (eq x t) t (lit-list-fix x))
         :exec x)
    ///
    (defthm obs-dom-info-fix-when-obs-dom-info-p
      (implies (obs-dom-info-p x)
               (equal (obs-dom-info-fix x) x)))

    (fty::deffixtype obs-dom-info :pred obs-dom-info-p :fix obs-dom-info-fix
      :equiv obs-dom-info-equiv :define t :forward t)))

(define make-obs-dom-info-unreached ()
  :returns (info obs-dom-info-p)
  :inline t
  t)

(define make-obs-dom-info-reached ((doms lit-listp))
  :returns (info obs-dom-info-p
                 :hints (("goal" :in-theory (Enable obs-dom-info-p))))
  :inline t
  (lit-list-fix doms))

(define obs-dom-info->reached ((x obs-dom-info-p))
  :inline t
  :hooks nil
  (not (eq x t))
  ///
  (defthm obs-dom-info->reached-of-make-obs-dom-info-reached
    (obs-dom-info->reached (make-obs-dom-info-reached doms)))

  (fty::deffixequiv obs-dom-info->reached
    :hints (("goal" :in-theory (enable obs-dom-info-fix)))))


(define obs-dom-info->doms ((x obs-dom-info-p))
  :inline t
  ;; :guard (obs-dom-info->reached x)
  :returns (doms lit-listp)
  :guard-hints (("goal" :in-theory (enable obs-dom-info-p obs-dom-info->reached)))
  :hooks nil
  (if (eq x t) nil (lit-list-fix x))
  ///
  (defthm obs-dom-info->doms-of-make-obs-dom-info-reached
    (equal (obs-dom-info->doms (make-obs-dom-info-reached doms))
           (lit-list-fix doms))
    :hints (("goal" :in-theory (enable make-obs-dom-info-reached))))

  (fty::deffixequiv obs-dom-info->doms
    :hints (("goal" :in-theory (enable obs-dom-info-fix)))))


(acl2::def-b*-binder
  obs-dom-info
  :body (std::da-patbind-fn 'obs-dom-info
                            '((reached . obs-dom-info->reached)
                              (doms . obs-dom-info->doms))
                            args acl2::forms acl2::rest-expr))

;; (fty::defflexsum obs-dom-info
;;   :kind nil
;;   (:info
;;    :type-name obs-dom-info
;;    :cond t
;;    :fields ((reached :acc-body (eq x t) :type booleanp :rule-classes :type-prescription)
;;             (doms :acc-body (if (eq x t) nil x) :type lit-listp))
;;    :ctor-body 
   


;; (fty::defprod obs-dom-info
;;   ((reached booleanp "have any reachable fanouts been swept"
;;             :rule-classes :type-prescription)
;;    (doms    lit-listp   "intersection of fanout dominators, if reached"))
;;   :layout :list)

(define obs-dom-info-well-formedp ((info obs-dom-info-p) aignet)
  :returns wfp
  (b* (((obs-dom-info info)))
    (or (not info.reached)
        (aignet-lit-listp info.doms aignet)))
  ///
  (defret aignet-lit-listp-of-doms-when-<fn>
    (b* (((obs-dom-info info)))
      (implies wfp
               (aignet-lit-listp info.doms aignet)))
    :hints (("goal" :in-theory (enable obs-dom-info->reached obs-dom-info->doms)))))

(define obs-dom-info-eval ((info obs-dom-info-p)
                           invals regvals aignet)
  :guard (and (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (obs-dom-info-well-formedp info aignet))
  (b* (((obs-dom-info info)))
    (and info.reached
         (bit->bool (aignet-eval-conjunction info.doms invals regvals aignet)))))
 


(fty::deflist obs-dom-info-list :elt-type obs-dom-info :true-listp t)

(make-event
 `(acl2::def-1d-arr obs-dom-array
    :slotname dominfo
    :pred obs-dom-info-p
    :fix obs-dom-info-fix
    :default-val ,(make-obs-dom-info-unreached)
    :rename ((resize-dominfos . resize-dominfo)
             (dominfos-length . dominfo-length))))

(defthm obs-dom-array$ap-is-obs-dom-info-list-p
  (equal (obs-dom-array$ap x)
         (obs-dom-info-list-p x)))


(local (include-book "std/lists/sets" :dir :system))
(local
 #!satlink
 (fty::deflist lit-list :pred lit-listp :elt-type litp :true-listp t
  :parents (litp)
  :short "List of literals"))


(local (defthm eqlable-listp-when-lit-listp
         (implies (lit-listp x)
                  (eqlable-listp x))))


(define cube-contradictionp ((x lit-listp))
  :returns (contradictionp)
  (if (atom x)
      nil
    (if (member (lit-negate (car x)) (lit-list-fix (cdr x)))
        t
      (cube-contradictionp (cdr x))))
  ///
  (local (defthm aignet-eval-conjunction-when-member
           (implies (and (member x (lit-list-fix y))
                         (equal (lit-eval x invals regvals aignet) 0))
                    (equal (aignet-eval-conjunction y invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))
  
  (defret <fn>-correct
    (implies contradictionp
             (equal (aignet-eval-conjunction x invals regvals aignet)
                    0))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))

(define obs-dom-info-subsetp ((x obs-dom-info-p)
                              (y obs-dom-info-p))
  :returns (subsetp)
  (b* (((obs-dom-info x))
       ((obs-dom-info y)))
    (or (not y.reached)
        (cube-contradictionp y.doms)
        (and x.reached
             (subsetp x.doms y.doms))))
  ///
  (local (defthm aignet-eval-conjunction-when-member
           (implies (and (equal (lit-eval x invals regvals aignet) 0)
                         (member (lit-fix x) (lit-list-fix  y)))
                    (equal (aignet-eval-conjunction y invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))
  (local (defthm aignet-eval-conjunction-when-subsetp
           (implies (and (equal (aignet-eval-conjunction x invals regvals aignet) 0)
                         (subsetp (lit-list-fix x) (lit-list-fix y)))
                    (equal (aignet-eval-conjunction y invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction
                                             subsetp lit-list-fix)
                   :induct (lit-list-fix x)))))
  (defretd <fn>-implies
    (implies (and subsetp (obs-dom-info-eval y invals regvals aignet))
             (obs-dom-info-eval x invals regvals aignet))
    :hints(("Goal" :in-theory (enable obs-dom-info-eval)))))


(define obs-dom-info-intersect ((x obs-dom-info-p)
                                (y obs-dom-info-p))
  :returns (int obs-dom-info-p)
  (b* (((obs-dom-info x))
       ((obs-dom-info y)))
    (if (and (not x.reached) (not y.reached))
        (make-obs-dom-info-unreached)
      (make-obs-dom-info-reached (intersection$ x.doms y.doms))))
  ///

  (local (defthm aignet-eval-conjunction-when-member
           (implies (and (equal (lit-eval x invals regvals aignet) 0)
                         (member x y))
                    (equal (aignet-eval-conjunction y invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))
  
  (local (defthm aignet-eval-conjunction-of-intersection
           (implies (or (bit->bool (aignet-eval-conjunction x invals regvals aignet))
                        (bit->bool (aignet-eval-conjunction y invals regvals aignet)))
                    (equal (aignet-eval-conjunction (intersection-equal x y) invals regvals aignet) 1))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction)
                   :induct (intersection-equal x y)))))
  
  (defret eval-of-<fn>
    (implies (or (obs-dom-info-eval x invals regvals aignet)
                 (obs-dom-info-eval y invals regvals aignet))
             (obs-dom-info-eval int invals regvals aignet))
    :hints(("Goal" :in-theory (enable obs-dom-info-eval))))

  (local (defthm subsetp-of-intersect-1
           (subsetp (intersection$ x y) x)))
  (local (defthm subsetp-of-intersect-2
           (subsetp (intersection$ x y) y)))
  
  (defret obs-dom-info-subsetp-of-intersect-1
    (obs-dom-info-subsetp int x)
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp))))

  (defret obs-dom-info-subsetp-of-intersect-2
    (obs-dom-info-subsetp int y)
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp)))))

(define obs-dom-info-add ((lit litp) (x obs-dom-info-p))
  :returns (new obs-dom-info-p)
  (b* (((obs-dom-info x)))
    (if x.reached
        (make-obs-dom-info-reached (cons (lit-fix lit) x.doms))
      (make-obs-dom-info-unreached)))
  ///
  (defret eval-of-<fn>
    (equal (obs-dom-info-eval new invals regvals aignet)
           (and (bit->bool (lit-eval lit invals regvals aignet))
                (obs-dom-info-eval x invals regvals aignet)))
    :hints(("Goal" :in-theory (enable obs-dom-info-eval
                                      aignet-eval-conjunction)))))

(define node-level-rank< ((node1 natp)
                          (node2 natp)
                          levels)
  :guard (and (< node1 (le



(define obs-dom-info-for-child ((fanout-info obs-dom-info-p)
                                (fanout natp)
                                (fanin bitp)
                                aignet)
  :guard (and (id-existsp fanout aignet)
              (eql (id->type fanout aignet) (gate-type)))
  :returns (child-fanout-info obs-dom-info-p)
  (if (or (eql 1 (id->regp fanout aignet))
          (eql fanin 1))
      ;; xor
      (obs-dom-info-fix fanout-info)
    (obs-dom-info-add (snode->fanin (id->slot-fn fanout (b-not fanin) aignet)) fanout-info))
  ///
  (defret eval-of-<fn>
    (implies (not (obs-dom-info-eval fanout-info invals regvals aignet))
             (not (obs-dom-info-eval child-fanout-info invals regvals aignet))))

  (defret <fn>-when-xor
    (implies (equal (stype (car (lookup-id fanout aignet))) :xor)
             (equal child-fanout-info (obs-dom-info-fix fanout-info))))
  (defret <fn>-when-fanin1
    (implies (bit->bool fanin)
             (equal child-fanout-info (obs-dom-info-fix fanout-info))))
  (defret <fn>-when-and-fanin0
    (implies (and (equal (stype (car (lookup-id fanout aignet))) :and)
                  (not (bit->bool fanin)))
             (equal child-fanout-info
                    (obs-dom-info-add (fanin (if (equal fanin 1) :gate0 :gate1)
                                             (lookup-id fanout aignet))
                                      fanout-info)))))
                                


;; (define obs-dom-info-combine ((fanout-info obs-dom-info-p)
;;                               (fanin-info obs-dom-info-p)
;;                               (fanout-and-sibling
;;                                maybe-litp
;;                                "sibling of fanin if the fanout is an AND gate"))
;;   :returns (new-fanin-info obs-dom-info-p)
;;   (b* (((obs-dom-info fanout-info))
;;        ((unless fanout-info.reached) (obs-dom-info-fix fanin-info))
;;        ((obs-dom-info fanin-info))
;;        (fanout-and-sibling (maybe-lit-fix fanout-and-sibling))
;;        ((unless fanin-info.reached)
;;         (make-obs-dom-info-reached
;;          (if fanout-and-sibling
;;              (cons fanout-and-sibling fanout-info.doms)
;;            fanout-info.doms)))
;;        (doms1 (intersection$ fanin-info.doms fanout-info.doms))
;;        (doms (if (and fanout-and-sibling
;;                       (member fanout-and-sibling fanin-info.doms)
;;                       (not (member fanout-and-sibling doms1)))
;;                  (cons fanout-and-sibling doms1)
;;                doms1)))
;;     (make-obs-dom-info-reached doms)))

;; ;; check out define-sk?
;; (defun-sk obs-dom-info-sweep-invariant (node sweep-position aignet)
;;   (forall fanout
;;           (implies (<= (nfix sweep-position) (nfix fanout))
                   
;; (include-book "kestrel/utilities/define-sk" :dir :system)






(define obs-dom-info-normalize ((x obs-dom-info-p))
  :returns (new-x obs-dom-info-p)
  (b* (((obs-dom-info x)))
    (if x.reached
        (if (cube-contradictionp x.doms)
            (make-obs-dom-info-unreached)
          (make-obs-dom-info-reached x.doms))
      (make-obs-dom-info-unreached)))
  ///
  (defret eval-of-<fn>
    (equal (obs-dom-info-eval new-x invals regvals aignet)
           (obs-dom-info-eval x invals regvals aignet))
    :hints(("Goal" :in-theory (enable obs-dom-info-eval))))

  (local (defthm cube-contradictionp-by-member
           (implies (and (member x cube)
                         (member (lit-negate x) cube)
                         (lit-listp cube))
                    (cube-contradictionp cube))
           :hints(("Goal" :in-theory (enable cube-contradictionp)))))
  
  (local (defthm cube-contradictionp-when-subsetp
           (implies (and (subsetp x y)
                         (cube-contradictionp x)
                         (lit-listp y) (lit-listp x))
                    (cube-contradictionp y))
           :hints(("Goal" :in-theory (enable cube-contradictionp
                                             subsetp)))))
  
  (defret subsetp-of-<fn>-1
    (equal (obs-dom-info-subsetp new-x y)
           (obs-dom-info-subsetp x y))
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp))))

  (defret subsetp-of-<fn>-2
    (equal (obs-dom-info-subsetp y new-x)
           (obs-dom-info-subsetp y x))
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp)))))
    


(defsection invariants

  (defun-sk obs-dom-info-sweep-invariant (sweep-position obs-dom-array aignet)
    (forall (fanout)
            (implies (and (natp fanout)
                          (<= fanout (fanin-count aignet))
                          (<= (nfix sweep-position) fanout)
                          (equal (id->type fanout aignet) (gate-type)))
                     (and (obs-dom-info-subsetp
                           (nth (lit->var (fanin :gate0 (lookup-id fanout aignet))) obs-dom-array)
                           (obs-dom-info-for-child
                            (nth fanout obs-dom-array) fanout 0 aignet))
                          (obs-dom-info-subsetp
                           (nth (lit->var (fanin :gate1 (lookup-id fanout aignet))) obs-dom-array)
                           (obs-dom-info-for-child
                            (nth fanout obs-dom-array) fanout 1 aignet)))))
    :rewrite  :direct)

  (in-theory (disable obs-dom-info-sweep-invariant
                      obs-dom-info-sweep-invariant-necc))

  (defthm id-eval-toggle-when-less
    (implies (< (nfix x) (nfix toggle))
             (equal (id-eval-toggle x toggle invals regvals aignet)
                    (id-eval x invals regvals aignet)))
    :hints (("goal" :induct (id-eval-ind x aignet)
             :expand ((id-eval x invals regvals aignet)
                      (id-eval-toggle x toggle invals regvals aignet)
                      (:free (x) (lit-eval x invals regvals aignet))
                      (:free (x y) (lit-eval-toggle x y invals regvals aignet))
                      (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
                      (:free (x y) (eval-xor-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet))))))


  (defthm obs-dom-info-eval-of-xor-fanin0
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :xor)
                  (case-split (<= (nfix sweep-position) (lit->var (fanin :gate0 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet))
             (obs-dom-info-eval
              (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array)
              invals regvals aignet))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies)
             )))

  (defthm obs-dom-info-eval-of-xor-fanin1
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :xor)
                  (case-split (<= (nfix sweep-position) (lit->var (fanin :gate1 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet))
             (obs-dom-info-eval
              (nth (lit->var (fanin :gate1 (lookup-id node aignet))) obs-dom-array)
              invals regvals aignet))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies)
             )))

  (defthm obs-dom-info-eval-of-and-fanin0
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :and)
                  (case-split (<= (nfix sweep-position) (lit->var (fanin :gate0 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet)
                  (case-split (bit->bool (lit-eval (fanin :gate1 (lookup-id node aignet)) invals regvals aignet))))
             (obs-dom-info-eval
              (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array)
              invals regvals aignet))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node))
                          ;; (:instance obs-dom-info-subsetp-implies
                          ;;  (x (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array))
                          ;;  (y (obs-dom-info-add (fanin :gate1 (lookup-id node aignet))
                          ;;                       (nth node obs-dom-array))))
                          )
             :in-theory (enable obs-dom-info-subsetp-implies))))

  (defthm obs-dom-info-eval-of-and-fanin1
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :and)
                  (case-split (<= (nfix sweep-position) (lit->var (fanin :gate1 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet)
                  ;; (case-split (bit->bool (lit-eval (fanin :gate0 (lookup-id node aignet)) invals regvals aignet)))
                  )
             (obs-dom-info-eval
              (nth (lit->var (fanin :gate1 (lookup-id node aignet))) obs-dom-array)
              invals regvals aignet))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies)
             )))
             
  
  ;; When we're all done with a node, it'll be the case that when it is not
  ;; observable (under some inputs), it can be toggled without causing a change
  ;; in value in any node that is observable (under those inputs).  Call this
  ;; property OBSERVABILITY-DONE-INVARIANT.

  ;; If we don't have a ranking on the inputs to an AND, then this invariant
  ;; isn't inductive: if sink is an AND with both fanins (f0 and f1)
  ;; unobservable due to each other but both toggled when toggling source,
  ;; then this leads to an observable toggle of sink.  It seems that source should be
  ;; observable in this case: its path to f0 cannot have f0 as a dominator, and
  ;; its path to f1 cannot have f1 as a dominator, 
  (defthm observability-done-invariant
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix source))
                  (<= (nfix sweep-position) (nfix sink))
                  ;; source is known not observable under the inputs
                  (not (obs-dom-info-eval (nth source obs-dom-array) invals regvals aignet))
                  ;; sink is observable under the inputs
                  (obs-dom-info-eval (nth sink obs-dom-array) invals regvals aignet))
             (equal (id-eval sink invals regvals aignet)
                    (id-eval-toggle sink source invals regvals aignet)))
    :hints (("goal" :induct (id-eval-ind sink aignet)
             :expand ((id-eval sink invals regvals aignet)
                      (id-eval-toggle sink source invals regvals aignet)
                      (:free (x) (lit-eval x invals regvals aignet))
                      (:free (x y) (lit-eval-toggle x y invals regvals aignet))
                      (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
                      (:free (x y) (eval-xor-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet)))
             :do-not-induct t
             ;; :in-theory (disable ACL2::INEQUALITY-WITH-NFIX-HYP-1
             ;;                     ACL2::INEQUALITY-WITH-NFIX-HYP-2)
             )
            ;; (acl2::use-termhint
            ;;  (b* (((unless (equal (id->type node2 aignet) (gate-type)))
            ;;        nil)
            ;;       (xor (equal (id->regp node2 aignet) 1))
            ;;       (fan0 (lit->var (gate-id->fanin0 node2 aignet)))
            ;;       (fan1 (lit->var (gate-id->fanin1 node2 aignet)))
            ;;       ((unless ))
  
            )))






(define obs-dom-info-sweep-node ((n natp) obs-dom-array aignet)
  :guard (and (id-existsp n aignet)
              (< n (dominfo-length obs-dom-array)))
  :returns new-obs-dom-array
  (b* ((slot0 (id->slot n 0 aignet))
       (type (snode->type slot0))
       (node-info (obs-dom-info-normalize (get-dominfo n obs-dom-array)))
       (obs-dom-array (set-dominfo n node-info obs-dom-array)))
    (aignet-case
      type
      :gate
      (b* ((lit0 (snode->fanin slot0))
           (slot1 (id->slot n 1 aignet))
           (lit1 (snode->fanin slot1))
           (lit0-info (get-dominfo (lit->var lit0) obs-dom-array))
           (new-lit0-info (obs-dom-info-intersect
                           (obs-dom-info-for-child node-info n 0 aignet) lit0-info))
           (obs-dom-array (set-dominfo (lit->var lit0) new-lit0-info obs-dom-array))
           (lit1-info (get-dominfo (lit->var lit1) obs-dom-array))
           (new-lit1-info (obs-dom-info-intersect
                           (obs-dom-info-for-child node-info n 1 aignet) lit1-info)))
        (set-dominfo (lit->var lit1) new-lit1-info obs-dom-array))
      :otherwise obs-dom-array))
  ///
  (defret <fn>-length
    (implies (< n (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-correct
    ))



(define obs-dom-info-sweep-nodes ((n natp) obs-dom-array aignet)
  :guard (and (<= n (num-fanins aignet))
              (<= n (dominfo-length obs-dom-array)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns new-obs-dom-array
  (b* (((when (zp n))
        obs-dom-array)
       (obs-dom-array (obs-dom-info-sweep-node (1- n) obs-dom-array aignet)))
    (obs-dom-info-sweep-nodes (1- n) obs-dom-array aignet))
  ///
  (defret <fn>-length
    (implies (< n (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array)))))


    



             











;; - :none -- none of its fanouts have been swept
;; - :one-and -- exactly one fanout has been swept and it was an AND gate.
;;               This state additionally stores the fanout gate's dominators
;;               and the sibling literal.
;; - :multi   -- at least one fanout has been swept and either it wasn't an AND 












;; ; Dually, a node N is observable under condition 1 (const true) if it is
;; ; connected to that output.  It is observable under condition A & B if it has a
;; ; fanout AND node where its sibling is A and the AND node is observable under
;; ; condition B.  Its full observability condition is the OR of all the
;; ; observability conditions due to its fanouts.
