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
  :returns (contradictionp maybe-litp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (if (member (lit-negate (car x)) (lit-list-fix (cdr x)))
        (lit-fix (car x))
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
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

  (defret <fn>-membership
    (implies contradictionp
             (and (member-equal contradictionp (lit-list-fix x))
                  (member (lit-negate contradictionp) (lit-list-fix x)))))

  (defret <fn>-membership-no-fix
    (implies (and contradictionp (lit-listp x))
             (and (member-equal contradictionp x)
                  (member (lit-negate contradictionp) x)))))

(define obs-dom-info-subsetp ((x obs-dom-info-p)
                              (y obs-dom-info-p))
  :returns (subsetp)
  (b* (((obs-dom-info x))
       ((obs-dom-info y)))
    (or (not y.reached)
        ;; (cube-contradictionp y.doms)
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
    :hints(("Goal" :in-theory (enable obs-dom-info-eval))))

  (defretd <fn>-implies-reached
    (implies (and subsetp
                  (obs-dom-info->reached y)
                  ;; (not (cube-contradictionp (obs-dom-info->doms y)))
                  )
             (obs-dom-info->reached x))
    :hints(("Goal" :in-theory (enable obs-dom-info-eval))))

  (defretd <fn>-implies-member
    (implies (and subsetp
                  (obs-dom-info->reached y)
                  (not (member-equal lit (obs-dom-info->doms y))))
             (not (member lit (obs-dom-info->doms x))))))


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
                                      aignet-eval-conjunction))))

  (defret <fn>-when-unreached
    (implies (not (obs-dom-info->reached x))
             (equal new (make-obs-dom-info-unreached))))

  (defret <fn>-when-reached
    (implies (obs-dom-info->reached x)
             (obs-dom-info->reached new)))

  (defret member-of-<fn>
    (implies (obs-dom-info->reached x)
             (iff (member-equal dom (obs-dom-info->doms new))
                  (or (equal dom (lit-fix lit))
                      (member-equal dom (obs-dom-info->doms x)))))))

;; (define node-level-rank< ((node1 natp)
;;                           (node2 natp)
;;                           levels)
;;   :guard (and (< node1 (le



(define obs-dom-info-for-child ((fanout-info obs-dom-info-p)
                                (fanout natp)
                                (fanin bitp)
                                aignet)
  :guard (and (id-existsp fanout aignet)
              (eql (id->type fanout aignet) (gate-type)))
  :returns (child-fanout-info obs-dom-info-p)
  (b* ((fanin0 (gate-id->fanin0 fanout aignet))
       (fanin1 (gate-id->fanin1 fanout aignet))
       (xor (eql 1 (id->regp fanout aignet))))
    (if xor
        (if (or (eql fanin0 fanin1)
                (eql fanin0 (lit-negate fanin1)))
            (make-obs-dom-info-unreached)
          (obs-dom-info-fix fanout-info))
      (cond ((eql fanin0 fanin1) (obs-dom-info-fix fanout-info))
            ((eql fanin0 (lit-negate fanin1)) (make-obs-dom-info-unreached))
            (t
             (obs-dom-info-add (snode->fanin (id->slot-fn fanout (b-not fanin) aignet)) fanout-info)))))
  ///
  ;; (defret eval-of-<fn>
  ;;   (implies (not (obs-dom-info-eval fanout-info invals regvals aignet))
  ;;            (not (obs-dom-info-eval child-fanout-info invals regvals aignet))))

  (defret <fn>-when-xor
    (implies (equal (stype (car (lookup-id fanout aignet))) :xor)
             (equal child-fanout-info
                    (b* ((fanin0 (gate-id->fanin0 fanout aignet))
                         (fanin1 (gate-id->fanin1 fanout aignet)))
                      (if (or (eql fanin0 fanin1)
                              (eql fanin0 (lit-negate fanin1)))
                          (make-obs-dom-info-unreached)
                        (obs-dom-info-fix fanout-info))))))
  ;; (defret <fn>-when-fanin1
  ;;   (implies (bit->bool fanin)
  ;;            (equal child-fanout-info (obs-dom-info-fix fanout-info))))
  ;; (defret <fn>-when-and-fanin0
  ;;   (implies (and (equal (stype (car (lookup-id fanout aignet))) :and)
  ;;                 (not (bit->bool fanin)))
  ;;            (equal child-fanout-info
  ;;                   (obs-dom-info-add (fanin (if (equal fanin 1) :gate0 :gate1)
  ;;                                            (lookup-id fanout aignet))
  ;;                                     fanout-info))))
  (defret <fn>-when-and
    (implies (equal (stype (car (lookup-id fanout aignet))) :and)
             (equal child-fanout-info
                    (cond ((equal (gate-id->fanin0 fanout aignet)
                                  (gate-id->fanin1 fanout aignet))
                           (obs-dom-info-fix fanout-info))
                          ((equal (gate-id->fanin0 fanout aignet)
                                  (lit-negate (gate-id->fanin1 fanout aignet)))
                           (make-obs-dom-info-unreached))
                          (t (obs-dom-info-add (fanin (if (equal fanin 1) :gate0 :gate1)
                                                      (lookup-id fanout aignet))
                                               fanout-info)))))))
                                


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






;; (define obs-dom-info-normalize ((x obs-dom-info-p))
;;   :returns (new-x obs-dom-info-p)
;;   (b* (((obs-dom-info x)))
;;     (if x.reached
;;         (if (cube-contradictionp x.doms)
;;             (make-obs-dom-info-unreached)
;;           (make-obs-dom-info-reached x.doms))
;;       (make-obs-dom-info-unreached)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (obs-dom-info-eval new-x invals regvals aignet)
;;            (obs-dom-info-eval x invals regvals aignet))
;;     :hints(("Goal" :in-theory (enable obs-dom-info-eval))))

;;   (local (defthm cube-contradictionp-by-member
;;            (implies (and (member x cube)
;;                          (member (lit-negate x) cube)
;;                          (lit-listp cube))
;;                     (cube-contradictionp cube))
;;            :hints(("Goal" :in-theory (enable cube-contradictionp)))))
  
;;   (local (defthm cube-contradictionp-when-subsetp
;;            (implies (and (subsetp x y)
;;                          (cube-contradictionp x)
;;                          (lit-listp y) (lit-listp x))
;;                     (cube-contradictionp y))
;;            :hints(("Goal" :in-theory (enable cube-contradictionp
;;                                              subsetp)))))
  
;;   (defret subsetp-of-<fn>-1
;;     (equal (obs-dom-info-subsetp new-x y)
;;            (obs-dom-info-subsetp x y))
;;     :hints(("Goal" :in-theory (enable obs-dom-info-subsetp))))

;;   (defret subsetp-of-<fn>-2
;;     (equal (obs-dom-info-subsetp y new-x)
;;            (obs-dom-info-subsetp y x))
;;     :hints(("Goal" :in-theory (enable obs-dom-info-subsetp)))))
    


(defsection invariants

  (defun-sk obs-dom-info-sweep-invariant (sweep-position obs-dom-array aignet)
    (forall (fanout)
            (implies (and (natp fanout)
                          (<= fanout (fanin-count aignet))
                          (<= (nfix sweep-position) fanout)
                          (not (cube-contradictionp (obs-dom-info->doms (nth fanout obs-dom-array)))))
                     (and ;; (not (cube-contradictionp (obs-dom-info->doms (nth fanout obs-dom-array))))
                          (implies (equal (id->type fanout aignet) (gate-type))
                                   (and (obs-dom-info-subsetp
                                         (nth (lit->var (fanin :gate0 (lookup-id fanout aignet))) obs-dom-array)
                                         (obs-dom-info-for-child
                                          (nth fanout obs-dom-array) fanout 0 aignet))
                                        (obs-dom-info-subsetp
                                         (nth (lit->var (fanin :gate1 (lookup-id fanout aignet))) obs-dom-array)
                                         (obs-dom-info-for-child
                                          (nth fanout obs-dom-array) fanout 1 aignet))
                                        )))))
    :rewrite  :direct)

  (in-theory (disable obs-dom-info-sweep-invariant
                      obs-dom-info-sweep-invariant-necc))

  ;; (defthm obs-dom-info-sweep-invariant-implies-not-contradictionp
  ;;   (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
  ;;                 (<= (nfix fanout) (fanin-count aignet))
  ;;                 (<= (nfix sweep-position) (nfix fanout)))
  ;;            (not (cube-contradictionp (obs-dom-info->doms (nth fanout obs-dom-array)))))
  ;;   :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
  ;;                          (fanout (nfix fanout)))))))
  
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


  (local (defthm obs-dom-info-eval-when-contradictionp
           (implies (cube-contradictionp (obs-dom-info->doms x))
                    (not (obs-dom-info-eval x invals regvals aignet)))
           :hints(("Goal" :in-theory (enable obs-dom-info-eval)))))
  
  (defthm obs-dom-info-eval-of-xor-fanin0
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :xor)
                  ;; (case-split (<= (nfix sweep-position) (lit->var (fanin :gate0 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet)
                  (not (equal (fanin :gate0 (lookup-id node aignet))
                              (fanin :gate1 (lookup-id node aignet))))
                  (not (equal (fanin :gate0 (lookup-id node aignet))
                              (lit-negate (fanin :gate1 (lookup-id node aignet))))))
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
                  ;; (case-split (<= (nfix sweep-position) (lit->var (fanin :gate1 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet)
                  (not (equal (fanin :gate0 (lookup-id node aignet))
                              (fanin :gate1 (lookup-id node aignet))))
                  (not (equal (fanin :gate0 (lookup-id node aignet))
                              (lit-negate (fanin :gate1 (lookup-id node aignet))))))
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
                  ;; (case-split (<= (nfix sweep-position) (lit->var (fanin :gate0 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet)
                  (case-split (bit->bool (lit-eval (fanin :gate1 (lookup-id node aignet)) invals regvals aignet)))
                  ;; (not (equal (fanin :gate0 (lookup-id node aignet))
                  ;;             (fanin :gate1 (lookup-id node aignet))))
                  (not (equal (fanin :gate0 (lookup-id node aignet))
                              (lit-negate (fanin :gate1 (lookup-id node aignet))))))
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

  (defthm obs-dom-info-eval-of-and-fanin0-self
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :and)
                  ;; (case-split (<= (nfix sweep-position) (lit->var (fanin :gate0 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet)
                  (equal (fanin :gate0 (lookup-id node aignet))
                         (fanin :gate1 (lookup-id node aignet))))
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
                  ;; (case-split (<= (nfix sweep-position) (lit->var (fanin :gate1 (lookup-id node aignet)))))
                  (obs-dom-info-eval (nth node obs-dom-array) invals regvals aignet)
                  (case-split (bit->bool (lit-eval (fanin :gate0 (lookup-id node aignet)) invals regvals aignet)))
                  (not (equal (fanin :gate0 (lookup-id node aignet))
                              (lit-negate (fanin :gate1 (lookup-id node aignet)))))
                  )
             (obs-dom-info-eval
              (nth (lit->var (fanin :gate1 (lookup-id node aignet))) obs-dom-array)
              invals regvals aignet))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies)
             )))


  (defthm obs-dom-info-reached-of-xor-fanin0
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :xor)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array))))
                  (case-split
                    (not (equal (fanin :gate0 (lookup-id node aignet))
                                (fanin :gate1 (lookup-id node aignet)))))
                  (case-split (not (equal (fanin :gate0 (lookup-id node aignet))
                                          (lit-negate (fanin :gate1 (lookup-id node aignet))))))
                  ;; (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array))))
                  )
             (obs-dom-info->reached (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array)))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-reached))))

  (defthm obs-dom-info-reached-of-xor-fanin1
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :xor)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array))))
                  (case-split
                    (not (equal (fanin :gate0 (lookup-id node aignet))
                                (fanin :gate1 (lookup-id node aignet)))))
                  (case-split (not (equal (fanin :gate0 (lookup-id node aignet))
                                          (lit-negate (fanin :gate1 (lookup-id node aignet))))))
                  ;; (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array))))
                  )
             (obs-dom-info->reached (nth (lit->var (fanin :gate1 (lookup-id node aignet))) obs-dom-array)))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-reached))))

  (defthm obs-dom-info-reached-of-and-fanin0
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :and)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array))))
                  (case-split (not (equal (fanin :gate0 (lookup-id node aignet))
                                          (lit-negate (fanin :gate1 (lookup-id node aignet))))))
                  ;; (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array))))
                  )
             (obs-dom-info->reached (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array)))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-reached))))

  (defthm obs-dom-info-reached-of-and-fanin1
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :and)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array))))
                  (case-split (not (equal (fanin :gate0 (lookup-id node aignet))
                                          (lit-negate (fanin :gate1 (lookup-id node aignet))))))
                  ;; (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array))))
                  )
             (obs-dom-info->reached (nth (lit->var (fanin :gate1 (lookup-id node aignet))) obs-dom-array)))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-reached))))

  ;; (defthm obs-dom-info-reached-of-xor-fanin0
  ;;   (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
  ;;                 (<= (nfix sweep-position) (nfix node))
  ;;                 (equal (stype (car (lookup-id node aignet))) :xor)
  ;;                 (obs-dom-info->reached (nth node obs-dom-array))
  ;;                 (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array)))))
  ;;            (obs-dom-info->reached (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array)))
  ;;   :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
  ;;                          (fanout node)))
  ;;            :in-theory (enable obs-dom-info-subsetp-implies-reached))))

  ;; (defthm obs-dom-info-reached-of-xor-fanin1
  ;;   (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
  ;;                 (<= (nfix sweep-position) (nfix node))
  ;;                 (equal (stype (car (lookup-id node aignet))) :xor)
  ;;                 (obs-dom-info->reached (nth node obs-dom-array))
  ;;                 (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array)))))
  ;;            (obs-dom-info->reached (nth (lit->var (fanin :gate1 (lookup-id node aignet))) obs-dom-array)))
  ;;   :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
  ;;                          (fanout node)))
  ;;            :in-theory (enable obs-dom-info-subsetp-implies-reached))))
  
  ;; When we're all done with a node, it'll be the case that when it is not
  ;; observable (under some inputs), it can be toggled without causing a change
  ;; in value in any node that is observable (under those inputs).  Call this
  ;; property OBSERVABILITY-DONE-INVARIANT.

  ;; If we don't have a ranking on the inputs to an AND, then this invariant
  ;; isn't inductive: if sink is an AND with both fanins (f0 and f1)
  ;; unobservable due to each other but both toggled when toggling source,
  ;; then this leads to an observable toggle of sink.  It seems that source should be
  ;; observable in this case: its path to f0 cannot have f0 as a dominator, and
  ;; its path to f1 cannot have f1 as a dominator.  
  ;; (defthm observability-done-invariant
  ;;   (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
  ;;                 (<= (nfix sweep-position) (nfix source))
  ;;                 (<= (nfix sweep-position) (nfix sink))
  ;;                 ;; source is known not observable under the inputs
  ;;                 (not (obs-dom-info-eval (nth source obs-dom-array) invals regvals aignet))
  ;;                 ;; sink is observable under the inputs
  ;;                 (obs-dom-info-eval (nth sink obs-dom-array) invals regvals aignet))
  ;;            (equal (id-eval sink invals regvals aignet)
  ;;                   (id-eval-toggle sink source invals regvals aignet)))
  ;;   :hints (("goal" :induct (id-eval-ind sink aignet)
  ;;            :expand ((id-eval sink invals regvals aignet)
  ;;                     (id-eval-toggle sink source invals regvals aignet)
  ;;                     (:free (x) (lit-eval x invals regvals aignet))
  ;;                     (:free (x y) (lit-eval-toggle x y invals regvals aignet))
  ;;                     (:free (x y) (eval-and-of-lits x y invals regvals aignet))
  ;;                     (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
  ;;                     (:free (x y) (eval-xor-of-lits x y invals regvals aignet))
  ;;                     (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet)))
  ;;            :do-not-induct t
  ;;            ;; :in-theory (disable ACL2::INEQUALITY-WITH-NFIX-HYP-1
  ;;            ;;                     ACL2::INEQUALITY-WITH-NFIX-HYP-2)
  ;;            )
  ;;           ;; (acl2::use-termhint
  ;;           ;;  (b* (((unless (equal (id->type node2 aignet) (gate-type)))
  ;;           ;;        nil)
  ;;           ;;       (xor (equal (id->regp node2 aignet) 1))
  ;;           ;;       (fan0 (lit->var (gate-id->fanin0 node2 aignet)))
  ;;           ;;       (fan1 (lit->var (gate-id->fanin1 node2 aignet)))
  ;;           ;;       ((unless ))
  
  ;;           ))


  
  (defthm obs-dom-info-member-of-xor-fanin0
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :xor)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array))))
                  (case-split
                    (not (equal (fanin :gate0 (lookup-id node aignet))
                                (fanin :gate1 (lookup-id node aignet)))))
                  (case-split (not (equal (fanin :gate0 (lookup-id node aignet))
                                          (lit-negate (fanin :gate1 (lookup-id node aignet))))))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array)))))
             (not (member-equal dom (obs-dom-info->doms (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array)))))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-member))))

  (defthm obs-dom-info-member-of-xor-fanin1
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :xor)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array))))
                  (case-split
                    (not (equal (fanin :gate0 (lookup-id node aignet))
                                (fanin :gate1 (lookup-id node aignet)))))
                  (case-split (not (equal (fanin :gate0 (lookup-id node aignet))
                                          (lit-negate (fanin :gate1 (lookup-id node aignet))))))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array)))))
             (not (member-equal dom (obs-dom-info->doms (nth (lit->var (fanin :gate1 (lookup-id node aignet))) obs-dom-array)))))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-member))))

  (defthm obs-dom-info-member-of-and-fanin0
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :and)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array))))
                  (case-split (not (equal dom (fanin :gate1 (lookup-id node aignet)))))
                  (case-split (not (equal (fanin :gate0 (lookup-id node aignet))
                                          (lit-negate (fanin :gate1 (lookup-id node aignet))))))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array)))))
             (not (member-equal dom (obs-dom-info->doms (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array)))))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-member))))

  (defthm obs-dom-info-member-of-and-fanin0-same
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :and)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array))))
                  ;; (case-split (not (equal dom (fanin :gate1 (lookup-id node aignet)))))
                  (equal (fanin :gate0 (lookup-id node aignet))
                         (fanin :gate1 (lookup-id node aignet)))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array)))))
             (not (member-equal dom (obs-dom-info->doms (nth (lit->var (fanin :gate0 (lookup-id node aignet))) obs-dom-array)))))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-member))))

  (defthm obs-dom-info-member-of-and-fanin1
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix node))
                  (equal (stype (car (lookup-id node aignet))) :and)
                  (obs-dom-info->reached (nth node obs-dom-array))
                  (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array))))
                  (case-split (not (equal dom (fanin :gate0 (lookup-id node aignet)))))
                  (case-split (not (equal (fanin :gate0 (lookup-id node aignet))
                                          (lit-negate (fanin :gate1 (lookup-id node aignet))))))
                  (not (cube-contradictionp (obs-dom-info->doms (nth node obs-dom-array)))))
             (not (member-equal dom (obs-dom-info->doms (nth (lit->var (fanin :gate1 (lookup-id node aignet))) obs-dom-array)))))
    :hints (("goal" :use ((:instance obs-dom-info-sweep-invariant-necc
                           (fanout node)))
             :in-theory (enable obs-dom-info-subsetp-implies-member))))
  

  ;; If we DON'T treat nodes with contradictory observability dominators as
  ;; unreachable, we can prove (1) unreachable nodes only affect other
  ;; unreachable nodes, and (2) if a "source" node is unobservable under an
  ;; assignment, then toggling it may only affect the value of other "sink"
  ;; nodes that are unobservable. (Specifically, there is an observability
  ;; dominator of source that evaluates to false, if a sink node is reachable
  ;; and does not share that observability dominator, then it cannot be
  ;; affected by toggling the source.)


  ;; However, it would be nice to be able to treat nodes with contradictory
  ;; observability dominators as unreachable!  Not doing so might cause us to
  ;; miss otherwise useful observability dominators.  For example, if A has two
  ;; xor fanouts B and C, B has contradictory dominators D and ~D, and C has
  ;; dominator E, treating B as unreachable allows us to say A has dominator E,
  ;; whereas otherwise it has no dominators.  But doing so causes our proof
  ;; above to unravel (even if we record nodes with contradictory dominators
  ;; separately from unreachable nodes) because an "unreachable" node (one
  ;; which only reaches nodes with contradictory dominators) may affect nodes
  ;; with contradictory dominators, and nodes with contradictory dominators may
  ;; affect nodes without contradictory dominators, only under conditions where
  ;; they are unobservable.

  ;; We'd like to adapt our proof of theorem (2) above so that it works for
  ;; this method.  However, it isn't true anymore that if a source node has an
  ;; observability dominator that evaluates to false, it may only affect nodes
  ;; that share that observability dominator.  For example, if we have A, B, C,
  ;; D, E as in the paragraph above, and E evaluates to false, then A may still
  ;; affect B, which doesn't have E as a dominator.  We hope to instead say
  ;; that if a source node affects a sink node, the source node is
  ;; unobservable, and the sink node is reachable, we will find an
  ;; observability dominator of the sink node that is false.  For the ABCDE
  ;; example, we can choose between D and ~D, whichever is false.  However,
  ;; we'll run into trouble again on AND nodes where both the fanins are false
  ;; but are both affected by toggling the sink.  E.g., if sink = x & y, the
  ;; false dominator of x is y and the false dominator of y is x, neither of
  ;; these need be a dominator for sink.  We need some property of our badguy
  ;; function such that we know that badguy(x)=y and badguy(y)=x aren't both
  ;; true.

  ;; Intuitively, we are getting our badguy dominator literals from either (1)
  ;; the original sink's dominator list, or (2) one of the contradictory
  ;; literals from a node with contradictory dominators.  Let's focus on (2),
  ;; since once we solve the problems with those presumably we'll be able to
  ;; solve the problems with (1), perhaps needing a separate induction.

  ;; When a source has contradictory literals, one of them must be false.  A
  ;; parent node might:
  ;;  1. also have contradictory dominators, either the same or different
  ;;  2. have the false literal as a dominator also
  ;;  3. otherwise, it must be that the parent is an AND node and the sibling of
  ;; the source must be the dominator, in which case that parent node can't be
  ;; affected by the source.
  
  ;; An interesting property of 2. (that is, ~1 & 2) is that then the dominator
  ;; node is a descendant of the parent.  We use this to show that badguy for
  ;; a sink is either a descendant of the sink, or else its negation is also
  ;; a dominator of the sink.

  ;; When we have the annoying case where we have a sink that is an AND node
  ;; and both children dominate each other, we use this property to try and
  ;; untangle them.  Since they can't both be descendants of each other, we
  ;; basically have two cases (modulo symmetry):

  ;; 1) the left fanin is a descendant of the right fanin,
  ;;    ~right and right are dominators of left
  ;;    left is a dominator of right.

  ;; 2) ~right and right are dominators of left
  ;;    ~left and left are dominators of right

  ;; Common to both of these is:
  ;;   ~right and right are dominators of left
  ;;    left is a dominator of right.
  ;; I think this should be impossible.
  
  ;; If we look at the parent node, this means ~right is a dominator. With the
  ;; obs-parent invariant (if a node has a dominator, it must have a reachable
  ;; parent node) we can follow the ~right dominator up the chain to find
  ;; "origin", an AND with one fanin "anc" an ancestor of parent, left, and
  ;; right, and the other fanin ~right.  But now for left to be a dominator of
  ;; right, origin must have left as a dominator.  Again we can follow the left
  ;; dominator up the chain from origin to "origin2", an AND of "anc2" and left.

  ;; Generalizing slightly: if we have a node SINK with (proper) descendants A
  ;; and B, A is a dominator of B, B is a dominator of A, and A is a dominator
  ;; of SINK ==> contradiction.

  ;; Proof: Induct back up the parent chain of SINK. Since A is a dominator of
  ;; SINK, go back up the chain until we reach the AND node where A is a
  ;; dominator.  But since B is a dominator of A, it must be a dominator of
  ;; that AND node.  Now we have another instance of this with A and B
  ;; switched, which we assume true by induction.

  (define descendant-p ((sink natp) (source natp) aignet)
    :measure (nfix sink)
    :guard (and (id-existsp sink aignet)
                (id-existsp source aignet))
    (b* (((when (eql (nfix sink) (nfix source))) t)
         ((unless (eql (id->type sink aignet) (gate-type))) nil))
      (or (descendant-p (lit->var (gate-id->fanin0 sink aignet)) source aignet)
          (descendant-p (lit->var (gate-id->fanin1 sink aignet)) source aignet)))
    ///
    (defthm descendant-p-self
      (descendant-p x x aignet)) 
    (defthm descendant-p-of-fanin
      (implies (and (equal (ctype (stype (car (lookup-id sink aignet)))) :gate)
                    (not (descendant-p sink source aignet)))
               (and (not (descendant-p (lit->var (fanin :gate0 (lookup-id sink aignet)))
                                       source aignet))
                    (not (descendant-p (lit->var (fanin :gate1 (lookup-id sink aignet)))
                                       source aignet))))))
  )

(define obs-parent-p ((parent natp) (child natp) obs-dom-array aignet)
  :guard (and (id-existsp parent aignet)
              (<= (num-fanins aignet) (dominfo-length obs-dom-array)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* (((obs-dom-info inf) (get-dominfo parent obs-dom-array))
       (type (id->type parent aignet))
       (xor (eql 1 (id->regp parent aignet)))
       ((unless (and inf.reached
                     (not (cube-contradictionp inf.doms))
                     (eql type (gate-type))))
        nil)
       (fanin0 (gate-id->fanin0 parent aignet))
       (fanin1 (gate-id->fanin1 parent aignet)))
    (and (or (eql (lnfix child) (lit->var fanin0))
             (eql (lnfix child) (lit->var fanin1)))
         (if xor
             (and (not (eql fanin0 (lit-negate fanin1)))
                  (not (eql fanin0 fanin1)))
           (not (eql fanin0 (lit-negate fanin1))))))
  ///
  (defthm not-obs-parent-p-when-less
    (implies (<= (nfix parent) (nfix child))
             (not (obs-parent-p parent child obs-dom-array aignet))))

  (defthm not-obs-parent-p-when-out-of-bounds
    (implies (<= (num-fanins aignet) (nfix parent))
             (not (obs-parent-p parent child obs-dom-array aignet)))))

(define obs-parent-aux ((child natp) (next natp) obs-dom-array aignet)
  :guard (and (<= next (num-fanins aignet))
              (<= (num-fanins aignet) (dominfo-length obs-dom-array)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns (parent? acl2::maybe-natp :rule-classes :type-prescription)
  :measure (nfix (- (num-fanins aignet) (nfix next)))
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix next)))
                   :exec (eql next (num-fanins aignet))))
        nil)
       ((when (obs-parent-p next child obs-dom-array aignet))
        (lnfix next)))
    (obs-parent-aux child (1+ (lnfix next)) obs-dom-array aignet))
  ///
  (defret obs-parent-p-of-<fn>
    (implies parent?
             (obs-parent-p parent? child obs-dom-array aignet)))

  
  (defret not-obs-parent-p-when-not-<fn>
    (implies (and (not parent?)
                  (<= (nfix next) (nfix other)))
             (not (obs-parent-p other child obs-dom-array aignet)))))


(define obs-parent ((child natp) obs-dom-array aignet)
  :guard (<= (num-fanins aignet) (dominfo-length obs-dom-array))
  :returns (parent? acl2::maybe-natp :rule-classes :type-prescription)
  (and (< (lnfix child) (num-fanins aignet))
       (obs-parent-aux child (1+ (lnfix child)) obs-dom-array aignet))
  ///
  (defret obs-parent-p-of-<fn>
    (implies parent?
             (obs-parent-p parent? child obs-dom-array aignet)))

  
  (defret not-obs-parent-p-when-not-<fn>
    (implies (not parent?)
             (not (obs-parent-p other child obs-dom-array aignet)))
    :hints (("goal" :use ((:instance not-obs-parent-p-when-less
                           (parent other))
                          (:instance not-obs-parent-p-when-out-of-bounds
                           (parent other)))
             :in-theory (disable not-obs-parent-p-when-out-of-bounds
                                 not-obs-parent-p-when-less))))

  (defret obs-parent-greater
    (implies parent?
             (< (nfix child) parent?))
    :hints(("Goal" :in-theory (disable <fn>
                                       obs-parent-p-of-<fn>)
            :use obs-parent-p-of-<fn>))
    :rule-classes :linear)

  (defret obs-parent-in-bounds
    (implies parent?
             (<= parent? (fanin-count aignet)))
    :hints(("Goal" :in-theory (disable <fn>
                                       obs-parent-p-of-<fn>)
            :use obs-parent-p-of-<fn>))
    :rule-classes :linear)

  (defret child-when-obs-parent
    (implies (and parent?
                  (not (equal (nfix child) (lit->var (fanin :gate0 (lookup-id parent? aignet))))))
             (equal (nfix child) (lit->var (fanin :gate1 (lookup-id parent? aignet)))))
    :hints(("Goal" :in-theory (e/d (obs-parent-p)
                                   (<fn>
                                    obs-parent-p-of-<fn>))
            :use obs-parent-p-of-<fn>))
    :rule-classes nil))


(defsection obs-parent-invar
  (defun-sk obs-parent-invar (obs-dom-array aignet)
    (forall child
            (implies (obs-dom-info->doms (nth child obs-dom-array))
                     (obs-parent child obs-dom-array aignet)))
    :rewrite :direct)

  (in-theory (disable obs-parent-invar))

  (defthm obs-parent-invar-corrollary
    (implies (and (obs-parent-invar obs-dom-array aignet)
                  (not (obs-parent child obs-dom-array aignet)))
             (not (obs-dom-info->doms (nth child obs-dom-array)))))
  
  (defun-nx obs-parent-induct (node obs-dom-array aignet)
    (declare (xargs :measure (nfix (- (num-fanins aignet) (nfix node)))))
    (let ((parent (obs-parent node obs-dom-array aignet)))
      (if parent
          (obs-parent-induct parent obs-dom-array aignet)
        node)))

  
  (defthm descendant-p-of-obs-parent
    (implies (and (descendant-p b a aignet)
                  (obs-parent b obs-dom-array aignet))
             (descendant-p (obs-parent b obs-dom-array aignet) a aignet))
    :hints (("goal" :use ((:instance obs-parent-p-of-obs-parent
                           (child b)))
             :in-theory (e/d (obs-parent-p) (obs-parent-p-of-obs-parent))
             :expand ((descendant-p (obs-parent b obs-dom-array aignet) a aignet)))))

  (defthm descendant-p-implies-lte-natp1
    (implies (and (descendant-p b a aignet)
                  (natp a))
             (<= a (nfix b)))
    :hints (("goal" :in-theory (enable descendant-p)))
    :rule-classes :forward-chaining)

  (defthm descendant-p-implies-lte-lit->var
    (implies (descendant-p b (lit->var a) aignet)
             (<= (lit->var a) (nfix b)))
    :hints (("goal" :use ((:instance descendant-p-implies-lte-natp1
                           (a (lit->var a))))))
    :rule-classes :forward-chaining)

  
  (defthm obs-dom-info-member-of-xor-fanin0-parent
    (let ((node (obs-parent fanin obs-dom-array aignet)))
      (implies (and node
                    (equal (nfix fanin) (lit->var (fanin :gate0 (lookup-id node aignet))))
                    (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                    (<= (nfix sweep-position) (nfix node))
                    (equal (stype (car (lookup-id node aignet))) :xor)
                    (obs-dom-info->reached (nth node obs-dom-array))
                    (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array)))))
               (not (member-equal dom (obs-dom-info->doms (nth fanin obs-dom-array))))))
    :hints (("goal" :use ((:instance obs-dom-info-member-of-xor-fanin0
                           (node (obs-parent fanin obs-dom-array aignet)))
                          (:instance obs-parent-p-of-obs-parent
                           (child fanin)))
             :in-theory (e/d (obs-parent-p)
                             (obs-dom-info-member-of-xor-fanin0
                              obs-parent-p-of-obs-parent)))))

  (defthm obs-dom-info-member-of-xor-fanin1-parent
    (let ((node (obs-parent fanin obs-dom-array aignet)))
      (implies (and node
                    (equal (nfix fanin) (lit->var (fanin :gate1 (lookup-id node aignet))))
                    (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                    (<= (nfix sweep-position) (nfix node))
                    (equal (stype (car (lookup-id node aignet))) :xor)
                    (obs-dom-info->reached (nth node obs-dom-array))
                    (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array)))))
               (not (member-equal dom (obs-dom-info->doms (nth fanin obs-dom-array))))))
    :hints (("goal" :use ((:instance obs-dom-info-member-of-xor-fanin1
                           (node (obs-parent fanin obs-dom-array aignet)))
                          (:instance obs-parent-p-of-obs-parent
                           (child fanin)))
             :in-theory (e/d (obs-parent-p)
                             (obs-dom-info-member-of-xor-fanin1
                              obs-parent-p-of-obs-parent)))))

  (defthm obs-dom-info-member-of-and-fanin0-parent
    (let ((node (obs-parent fanin obs-dom-array aignet)))
      (implies (and node
                    (equal (nfix fanin) (lit->var (fanin :gate0 (lookup-id node aignet))))
                    (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                    (<= (nfix sweep-position) (nfix node))
                    (equal (stype (car (lookup-id node aignet))) :and)
                    (obs-dom-info->reached (nth node obs-dom-array))
                    (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array))))
                    (case-split (not (equal dom (fanin :gate1 (lookup-id node aignet))))))
               (not (member-equal dom (obs-dom-info->doms (nth fanin obs-dom-array))))))
    :hints (("goal" :use ((:instance obs-dom-info-member-of-and-fanin0
                           (node (obs-parent fanin obs-dom-array aignet)))
                          (:instance obs-parent-p-of-obs-parent
                           (child fanin)))
             :in-theory (e/d (obs-parent-p)
                             (obs-dom-info-member-of-and-fanin0
                              obs-parent-p-of-obs-parent)))))

  (defthm obs-dom-info-member-of-and-fanin1-parent
    (let ((node (obs-parent fanin obs-dom-array aignet)))
      (implies (and node
                    (equal (nfix fanin) (lit->var (fanin :gate1 (lookup-id node aignet))))
                    (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                    (<= (nfix sweep-position) (nfix node))
                    (equal (stype (car (lookup-id node aignet))) :and)
                    (obs-dom-info->reached (nth node obs-dom-array))
                    (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array))))
                    (case-split (not (equal dom (fanin :gate0 (lookup-id node aignet))))))
               (not (member-equal dom (obs-dom-info->doms (nth fanin obs-dom-array))))))
    :hints (("goal" :use ((:instance obs-dom-info-member-of-and-fanin1
                           (node (obs-parent fanin obs-dom-array aignet)))
                          (:instance obs-parent-p-of-obs-parent
                           (child fanin)))
             :in-theory (e/d (obs-parent-p)
                             (obs-dom-info-member-of-and-fanin1
                              obs-parent-p-of-obs-parent)))))

  (defthm obs-dom-info-member-of-and-fanin0-same-parent
    (let ((node (obs-parent fanin obs-dom-array aignet)))
      (implies (and node
                    (equal (nfix fanin) (lit->var (fanin :gate1 (lookup-id node aignet))))
                    (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                    (<= (nfix sweep-position) (nfix node))
                    (equal (stype (car (lookup-id node aignet))) :and)
                    (obs-dom-info->reached (nth node obs-dom-array))
                    (not (member-equal dom (obs-dom-info->doms (nth node obs-dom-array))))
                    (case-split (equal (fanin :gate0 (lookup-id node aignet))
                                       (fanin :gate1 (lookup-id node aignet)))))
               (not (member-equal dom (obs-dom-info->doms (nth fanin obs-dom-array))))))
    :hints (("goal" :use ((:instance obs-dom-info-member-of-and-fanin0-same
                           (node (obs-parent fanin obs-dom-array aignet)))
                          (:instance obs-parent-p-of-obs-parent
                           (child fanin)))
             :in-theory (e/d (obs-parent-p)
                             (obs-dom-info-member-of-and-fanin0-same
                              obs-parent-p-of-obs-parent)))))


  
  
  (defthm no-self-domination-lemma
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (obs-parent-invar obs-dom-array aignet)
                  (member a (obs-dom-info->doms (nth b obs-dom-array)))
                  (descendant-p b (lit->var a) aignet)
                  (<= (nfix sweep-position) (lit->var a)))
             (not (member a (obs-dom-info->doms (nth (lit->var a) obs-dom-array)))))
    :hints (("goal" :induct (obs-parent-induct b obs-dom-array aignet))
            (and stable-under-simplificationp
                 '(:use ((:instance obs-parent-p-of-obs-parent
                          (child b)))
                   :in-theory (e/d (obs-parent-p )
                                   (obs-parent-p-of-obs-parent))))
            (and stable-under-simplificationp
                 '(:cases ((equal (stype (car (lookup-id (obs-parent b obs-dom-array aignet) aignet)))
                                  :and))))
            )
    :rule-classes nil)

  (local (defthmd equal-of-lit->var
           (equal (equal (lit->var a) (lit->var b))
                  (or (equal (lit-fix a) (lit-fix b))
                      (equal (lit-fix a) (lit-negate b))))
           :hints(("Goal" :in-theory (e/d (lit-negate b-not
                                                      satlink::equal-of-make-lit))))))

  (defthm no-self-domination
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (obs-parent-invar obs-dom-array aignet)
                  (<= (nfix sweep-position) (lit->var a)))
             (not (member a (obs-dom-info->doms (nth (lit->var a) obs-dom-array)))))
    :hints (("goal" :use ((:instance no-self-domination-lemma
                           (b (obs-parent (lit->var a) obs-dom-array aignet)))))
            (and stable-under-simplificationp
                 '(:use ((:instance obs-parent-p-of-obs-parent
                          (child (lit->var a))))
                   :in-theory (e/d (obs-parent-p)
                                   (obs-parent-p-of-obs-parent))))
            (and stable-under-simplificationp
                 '(:cases ((equal (stype (car (lookup-id (obs-parent (lit->var a) obs-dom-array aignet) aignet)))
                                  :and)))))
    :otf-flg t)

  (defun-nx no-mutual-domination-lemma-ind (sink a b obs-dom-array aignet)
    (declare (xargs :measure (nfix (- (num-fanins aignet) (nfix sink)))))
    (b* ((parent (obs-parent sink obs-dom-array aignet))
         ((unless parent) (list a b))
         (other
          (if (eql (lit->var (fanin :gate0 (lookup-id parent aignet))) (nfix sink))
              (fanin :gate1 (lookup-id parent aignet))
            (fanin :gate0 (lookup-id parent aignet))))
         ((when (and (eq (stype (car (lookup-id parent aignet))) :and)
                     (eql other (lit-fix a))))
          (no-mutual-domination-lemma-ind parent b a obs-dom-array aignet)))
      (no-mutual-domination-lemma-ind parent a b obs-dom-array aignet)))
  
  (defthm no-mutual-domination-lemma
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (obs-parent-invar obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix sink))
                  (descendant-p sink (lit->var a) aignet)
                  (descendant-p sink (lit->var b) aignet)
                  (not (equal (nfix sink) (lit->var a)))
                  (not (equal (nfix sink) (lit->var b)))
                  (member a (obs-dom-info->doms (nth (lit->var b) obs-dom-array)))
                  (member b (obs-dom-info->doms (nth (lit->var a) obs-dom-array))))
             (not (member a (obs-dom-info->doms (nth sink obs-dom-array)))))
    :hints (("goal" :induct (no-mutual-domination-lemma-ind sink a b obs-dom-array aignet))
            (and stable-under-simplificationp
                 '(:use ((:instance obs-parent-p-of-obs-parent
                          (child sink)))
                   :in-theory (e/d (obs-parent-p )
                                   (obs-parent-p-of-obs-parent))))
            (and stable-under-simplificationp
                 '(:cases ((equal (stype (car (lookup-id (obs-parent sink obs-dom-array aignet) aignet)))
                                  :and)))))
    :rule-classes nil))
    



(define contradictory-literal-badguy ((sink natp) (source natp)
                                      invals regvals aignet obs-dom-array)
  :measure (nfix sink)
  :returns (badguy maybe-litp)
  :guard (and (id-existsp sink aignet)
              (id-existsp source aignet)
              (<= (num-regs aignet) (bits-length regvals))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-fanins aignet) (dominfo-length obs-dom-array)))
  :verify-guards nil
  (b* ((dominfo (get-dominfo sink obs-dom-array))
       ((unless (obs-dom-info->reached dominfo)) nil)
       
       ((when (< (nfix sink) (nfix source))) nil)
       (contra (cube-contradictionp (obs-dom-info->doms dominfo)))
       ((when contra)
        (if (bit->bool (lit-eval contra invals regvals aignet))
            (lit-negate contra)
          contra))
       ((when (eql (nfix sink) (nfix source))) nil)
       ((unless (eql (id->type sink aignet) (gate-type))) nil)
       (fanin0  (gate-id->fanin0 sink aignet))
       (fanin1  (gate-id->fanin1 sink aignet))
       (xor (eql (id->regp sink aignet) 1))
       (badguy0 (contradictory-literal-badguy (lit->var fanin0)
                                              source invals regvals aignet obs-dom-array))
       ((when (eql fanin0 fanin1))
        (if (or xor (not (obs-dom-info->reached dominfo)))
            nil
          badguy0))
       ((when (eql fanin0 (lit-negate fanin1))) nil)
       (badguy1 (contradictory-literal-badguy (lit->var fanin1)
                                              source invals regvals aignet obs-dom-array))
       ((unless (obs-dom-info->reached dominfo)) nil)
       ((when (and badguy0 (or xor (not (eql badguy0 fanin1))))) badguy0)
       ((when (and badguy1 (or xor (not (eql badguy1 fanin0))))) badguy1))
    nil)
  ///
  (local (in-theory (disable (:d contradictory-literal-badguy))))
  (defret contradictory-literal-badguy-when-less
    (implies (< (nfix sink) (nfix source))
             (not badguy))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :do-not-induct t)))
  
  
  (defret contradictory-literal-badguy-member
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  badguy
                  (<= (nfix sweep-position) (nfix sink))
                  (<= (nfix sweep-position) (nfix source)))
             (member-equal badguy (obs-dom-info->doms (nth sink obs-dom-array))))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:cases ((equal (stype (car (lookup-id sink aignet))) :and))
                   :do-not-induct t))))

  ;; (local (defthm lit->var-when-lit-negate-equal
  ;;          (implies (equal (lit-negate x) y)
  ;;                   (equal (lit->var x) (lit->var y)))))

  
  (local (defthm lit-var-when-equal-lit-negate
           (implies (equal x (lit-negate y))
                    (and (equal (lit->neg x) (b-not (lit->neg y)))
                         (equal (lit->var x) (lit->var y))))
           ;; :rule-classes :forward-chaining
           ))

  (defret contradictory-literal-badguy-invar
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (or (not (obs-dom-info->reached (nth source obs-dom-array)))
                      (cube-contradictionp (obs-dom-info->doms (nth source obs-dom-array))))
                  badguy
                  (<= (nfix sweep-position) (nfix sink))
                  (<= (nfix sweep-position) (nfix source)))
             ;; (and (member-equal badguy (obs-dom-info->doms (nth sink obs-dom-array)))
             (or (member-equal (lit-negate badguy) (obs-dom-info->doms (nth sink obs-dom-array)))
                 (descendant-p sink (lit->var badguy) aignet)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((equal (stype (car (lookup-id sink aignet))) :and))))
            (and stable-under-simplificationp
                 '(:expand ((:free (bla) (descendant-p sink bla aignet)))))))
  
  (defthm descendants-antisymm
    (implies (and (descendant-p a b aignet)
                  (not (equal (nfix a) (nfix b))))
             (not (descendant-p b a aignet)))
    :hints (("goal" :use ((:instance descendant-p-implies-lte-natp1 (a (nfix a)) (b (nfix b)))
                          (:instance descendant-p-implies-lte-natp1 (b (nfix a)) (a (nfix b)))))))


  ;; (defthm cross-literal-badguys
  ;;   (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
  ;;                 (obs-parent-invar obs-dom-array aignet)
  ;;                 (or (not (obs-dom-info->reached (nth source obs-dom-array)))
  ;;                     (cube-contradictionp (obs-dom-info->doms (nth source obs-dom-array))))
  ;;                 (<= (nfix sweep-position) (nfix source))
  ;;                 (<= (nfix sweep-position) (lit->var a))
  ;;                 (<= (nfix sweep-position) (lit->var b))
  ;;                 (not (equal (lit->var a) (lit->var b)))
  ;;                 (equal (contradictory-literal-badguy (lit->var a) source invals regvals aignet obs-dom-array)
  ;;                        (lit-fix b)))
  ;;            (not (equal (contradictory-literal-badguy (lit->var b) source invals regvals aignet obs-dom-array)
  ;;                        (lit-fix a))))
  ;;   :hints (("goal" :use ((:instance contradictory-literal-badguy-invar
  ;;                          (sink (lit->var a)))
  ;;                         (:instance contradictory-literal-badguy-invar
  ;;                          (sink (lit->var b)))
  ;;                         (:instance no-mutual-domination-lemma
  ;;                          (sink parent))
  ;;                         (:instance no-mutual-domination-lemma
  ;;                          (sink parent) (a b) (b a)))
  ;;            :in-theory (disable contradictory-literal-badguy-invar)))
  ;;   :otf-flg t)
                  

  (local (defthm b-xor-equal-1
           (equal (equal 1 (b-xor x y))
                  (equal (bfix x) (b-not y)))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local (defthm b-xor-when-not-equal-b-not
           (implies (and (bitp a)
                         (not (equal a (b-not b))))
                    (equal (b-xor a b) 0))
           :hints(("Goal" :in-theory (enable b-xor bitp)))))
  
  (defret contradictory-badguy-eval
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (or (not (obs-dom-info->reached (nth source obs-dom-array)))
                      (cube-contradictionp (obs-dom-info->doms (nth source obs-dom-array))))
                  badguy
                  (<= (nfix sweep-position) (nfix sink))
                  (<= (nfix sweep-position) (nfix source)))
             ;; (and (member-equal badguy (obs-dom-info->doms (nth sink obs-dom-array)))
             (equal (lit-eval badguy invals regvals aignet) 0))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((equal (stype (car (lookup-id sink aignet))) :and))))
            (and stable-under-simplificationp
                 '(:expand ((:free (bla) (descendant-p sink bla aignet)))))))

  (local (defret contradictory-badguy-eval-rw
           (implies (and (equal lit badguy)
                         (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                         (or (not (obs-dom-info->reached (nth source obs-dom-array)))
                             (cube-contradictionp (obs-dom-info->doms (nth source obs-dom-array))))
                         badguy
                         (case-split (<= (nfix sweep-position) (nfix sink)))
                         (<= (nfix sweep-position) (nfix source)))
                    ;; (and (member-equal badguy (obs-dom-info->doms (nth sink obs-dom-array)))
                    (equal (id-eval (lit->var lit) invals regvals aignet)
                           (lit->neg lit)))
           :hints (("goal" :use contradictory-badguy-eval
                    :in-theory (disable contradictory-badguy-eval)
                    :expand ((lit-eval badguy invals regvals aignet))))))

  (local (defret contradictory-badguy-eval-rw2
           (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                         (or (not (obs-dom-info->reached (nth source obs-dom-array)))
                             (cube-contradictionp (obs-dom-info->doms (nth source obs-dom-array))))
                         badguy
                         (case-split (<= (nfix sweep-position) (nfix sink)))
                         (<= (nfix sweep-position) (nfix source)))
                    ;; (and (member-equal badguy (obs-dom-info->doms (nth sink obs-dom-array)))
                    (equal (id-eval (lit->var badguy) invals regvals aignet)
                           (lit->neg badguy)))
           :hints (("goal" :use contradictory-badguy-eval
                    :in-theory (disable contradictory-badguy-eval)
                    :expand ((lit-eval badguy invals regvals aignet))))))

  
  (local (defthm b-xor-b-xors
           (equal (b-xor (b-xor n1 x) (b-xor n2 x))
                  (b-xor n1 n2))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local (defthm b-and-b-xors
           (equal (b-and (b-xor n1 x) (b-xor n2 x))
                  (b-and (b-not (b-xor n1 n2)) (b-xor n1 x)))
           :hints(("Goal" :in-theory (enable b-xor)))))

  
  
  (defret contradictory-literals-invariant
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (obs-parent-invar obs-dom-array aignet)
                  (or (not (obs-dom-info->reached (nth source obs-dom-array)))
                      (cube-contradictionp (obs-dom-info->doms (nth source obs-dom-array))))
                  (<= (nfix sweep-position) (nfix sink))
                  (<= (nfix sweep-position) (nfix source))
                  (aignet-idp sink aignet)
                  (obs-dom-info->reached (nth sink obs-dom-array))
                  (or (not badguy)
                      (bit->bool (lit-eval badguy invals regvals aignet))))
             (equal (id-eval sink invals regvals aignet)
                    (id-eval-toggle sink source invals regvals aignet)))
    :hints (("goal" :induct (id-eval-ind sink aignet)
             ;; :do-not-induct t
             :expand (<call>
                      (id-eval sink invals regvals aignet)
                      (:free (source) (id-eval-toggle sink source invals regvals aignet))
                      (:free (x) (lit-eval x invals regvals aignet))
                      (:free (x y) (lit-eval-toggle x y invals regvals aignet))
                      (:free (x y) (eval-and-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
                      (:free (x y) (eval-xor-of-lits x y invals regvals aignet))
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet))))
            ;; (and stable-under-simplificationp
            ;;      '(:cases ((< (lit->var (fanin :gate0 (lookup-id sink aignet))) (nfix sweep-position)))))
            ;; (and stable-under-simplificationp
            ;;      '(:cases ((< (lit->var (fanin :gate1 (lookup-id sink aignet))) (nfix sweep-position)))))
            ;; (and stable-under-simplificationp
            ;;      '(:cases ((cube-contradictionp (obs-dom-info->doms (nth sink obs-dom-array))))))
            )))

  
  
  (define choose-observability-badguy ((sink natp) (source natp)
                                       obs-dom-array invals regvals aignet)
    :measure (nfix sink)
    :returns (maybe-badguy maybe-litp :rule-classes :type-prescription)
    (b* (((when (<= (nfix sink) (nfix source))) nil)
         ((unless (eql (id->type sink aignet) (gate-type))) nil)
         (contra (cube-contradictionp (obs-dom-info->doms (get-dominfo sink obs-dom-array))))
         ((when contra)
          (if (lit-eval contra invals regvals aignet)
              (lit-negate contra)
            contra))
         (xor (eql (id->regp sink aignet) 1))
         (fanin0 (gate-id->fanin0 sink aignet))
         (fanin1 (gate-id->fanin1 sink aignet))
         (fanin0-toggledp (not (eql (lit-eval fanin0 invals regvals aignet)
                                    (lit-eval-toggle fanin0 source invals regvals aignet))))
         (fanin1-toggledp (not (eql (lit-eval fanin1 invals regvals aignet)
                                    (lit-eval-toggle fanin1 source invals regvals aignet))))
         ((when xor)
          (if fanin0-toggledp
              (choose-observability-badguy (lit->var fanin0) source obs-dom-array invals regvals aignet)
            (choose-observability-badguy (lit->var fanin1) source obs-dom-array invals regvals aignet)))
         (

  
  

  ;; Instead, let's focus on one observability dominator.  If a node is not
  ;; observable, then either it is unreachable or else there is some dominator
  ;; that evaluates to false.  We'll take the unreachable case separately.  Let
  ;; D be the dominator that is false.  We'll show that only other nodes that
  ;; have D as a dominator or are unreachable may be affected by a toggle of
  ;; the node.

  ;; Unreachable nodes only affect other unreachable nodes.  Not true: e.g.,
  ;; n0 = n1 & n2
  ;; n2 = ~n1 & n3
  ;; n3 is unreachable, but n2 is not, and n3 can affect n2.
  ;; (defthm obs-dom-info-eval-when-not-reached
  ;;   (implies (not (obs-dom-info->reached info))
  ;;            (not (obs-dom-info-eval info invals regvals aignet)))
  ;;   :hints(("Goal" :in-theory (enable obs-dom-info-eval))))

  (local (defthm lit-var-when-equal-lit-negate
           (implies (equal x (lit-negate y))
                    (and (equal (lit->neg x) (b-not (lit->neg y)))
                         (equal (lit->var x) (lit->var y))))
           ;; :rule-classes :forward-chaining
           ))

  (local (defthm b-xor-b-xors
           (equal (b-xor (b-xor n1 x) (b-xor n2 x))
                  (b-xor n1 n2))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (local (defthm b-and-b-xors
           (equal (b-and (b-xor n1 x) (b-xor n2 x))
                  (b-and (b-not (b-xor n1 n2)) (b-xor n1 x)))
           :hints(("Goal" :in-theory (enable b-xor)))))
  
  (defthm observability-of-unreachables
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix source))
                  (<= (nfix sweep-position) (nfix sink))
                  (aignet-idp sink aignet)
                  (not (obs-dom-info->reached (nth source obs-dom-array)))
                  (obs-dom-info->reached (nth sink obs-dom-array))
                  (not (cube-contradictionp (obs-dom-info->doms (nth sink obs-dom-array))))
                  ;; (obs-dom-info-eval (nth sink obs-dom-array) invals regvals aignet)
                  )
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
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet))))))

  

  
  
  (defthm observability-when-gated
    (implies (and (obs-dom-info-sweep-invariant sweep-position obs-dom-array aignet)
                  (<= (nfix sweep-position) (nfix source))
                  (<= (nfix sweep-position) (nfix sink))
                  (aignet-idp sink aignet)
                  (member dom (obs-dom-info->doms (nth source obs-dom-array)))
                  (equal (lit-eval dom invals regvals aignet) 0)
                  (obs-dom-info->reached (nth sink obs-dom-array))
                  (not (member dom (obs-dom-info->doms (nth sink obs-dom-array)))))
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
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet))))))
             
  
  )






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
