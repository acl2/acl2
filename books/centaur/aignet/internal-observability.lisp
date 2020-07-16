; Copyright (C) 2020 Centaur Technology
; AIGNET - And-Inverter Graph Networks
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
(include-book "eval-toggle")
(include-book "cube-contradictionp")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;; (local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
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


;; Observability deals with situations in which a change in value of a node may
;; or may not be observable at the outputs (or some other distinguished set of
;; nodes).  To begin reasoning about it we define id-eval-toggle and
;; lit-eval-toggle, which gives the value of a (node/literal) when a certain
;; node's value has been negated.  A source node is unobservable from a sink
;; node if for all inputs, the id-eval-toggle of the sink node with source node
;; as the toggle input equals the id-eval of the sink node.




;; We formalize the notion of a path between a source and sink node.  This is
;; just a list of bits saying which child to traverse at each two-input gate
;; along the way.

;; The main result we prove is that if source toggles sink under some inputs,
;; then there must be a path between them such that:
;;  1) no two AND siblings of the path are contradictory literals
;;  2) no AND sibling of the path is 0 under both values of source.


;; A path through some descendants of a sink exists if all the nodes it says to
;; traverse are gate nodes.
(define path-existsp ((sink natp) (path bit-listp) aignet)
  :guard (id-existsp sink aignet)
  (if (atom path)
      t
    (and (eql (id->type sink aignet) (gate-type))
         (path-existsp (lit->var
                        (mbe :logic (non-exec (fanin (car path) (lookup-id sink aignet)))
                             :exec (snode->fanin (id->slot sink (car path) aignet))))
                       (cdr path) aignet)))
  ///
  (defthm path-existsp-when-consp
    (implies (and (path-existsp sink path aignet)
                  (consp path))
             (and (equal (ctype (stype (car (lookup-id sink aignet)))) :gate)
                  ;; (path-existsp (lit->var (fanin (car path) (lookup-id sink aignet)))
                  ;;                        (cdr path) aignet)
                  (implies (bit-equiv dir (car path))
                           (path-existsp (lit->var (fanin dir (lookup-id sink aignet)))
                                         (cdr path) aignet)))))

  (defthm path-existsp-of-cons
    (equal (path-existsp sink (cons dir path) aignet)
           (and (equal (ctype (stype (car (lookup-id sink aignet)))) :gate)
                (path-existsp (lit->var (fanin dir (lookup-id sink aignet))) path aignet))))

  (defthm path-existsp-of-atom
    (implies (not (consp path))
             (equal (path-existsp sink path aignet) t)))
  
  (defthm path-existsp-of-nil
    (equal (path-existsp sink nil aignet) t))

  (local (in-theory (disable (:d path-existsp)))))


;; The endpoint of a path from a sink node is the source node it ends up at.
(define path-endpoint ((sink natp) (path bit-listp) aignet)
  :guard (and (id-existsp sink aignet)
              (path-existsp sink path aignet))
  (if (atom path)
      (lnfix sink)
    (path-endpoint (lit->var
                    (mbe :logic (non-exec (fanin (car path) (lookup-id sink aignet)))
                         :exec (snode->fanin (id->slot sink (car path) aignet))))
                   (cdr path) aignet))
  ///
  (defthm path-endpoint-of-cons
    (equal (path-endpoint sink (cons dir rest) aignet)
           (path-endpoint (lit->var (fanin dir (lookup-id sink aignet))) rest aignet)))

  (defthm path-endpoint-of-atom
    (implies (not (consp path))
             (equal (path-endpoint sink path aignet)
                    (nfix sink))))
  
  (defthm path-endpoint-of-nil
    (equal (path-endpoint sink nil aignet)
           (nfix sink)))

  (local (in-theory (disable (:d path-endpoint)))))


;; Check whether any AND gate in a path has x as the sibling (i.e. the other
;; branch, that the path did not take).
(define path-contains-and-sibling ((x litp) (sink natp) (path bit-listp) aignet)
  :guard (and (id-existsp sink aignet)
              (path-existsp sink path aignet))
  :measure (len path)
  :guard-hints (("Goal" :expand ((path-existsp sink path aignet))))
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-fix-backchain
                                        lookup-id-out-of-bounds
                                        lookup-id-in-bounds-when-positive))))
  :returns (contains)
  (b* (((when (atom path)) nil)
       (next (mbe :logic (non-exec (fanin (car path)
                                          (lookup-id sink aignet)))
                  :exec (snode->fanin (id->slot sink (car path) aignet))))
       ((unless (mbe :logic (non-exec (eq (stype (car (lookup-id sink aignet))) :and))
                     :exec (eql (id->regp sink aignet) 0)))
        (path-contains-and-sibling x (lit->var next) (cdr path) aignet))
       (sib (mbe :logic (non-exec (fanin (b-not (car path))
                                         (lookup-id sink aignet)))
                 :exec (snode->fanin (id->slot sink (b-not (car path)) aignet))))
       ((when (eql sib (lit-fix x))) t))
    (path-contains-and-sibling x (lit->var next) (cdr path) aignet))
  ///
  (local (in-theory (disable (:d path-contains-and-sibling))))

  (local (defthm equal-of-lit-fix-implies-lit->var
           (implies (equal x (lit-fix y))
                    (equal (lit->var x) (lit->var y)))
           :rule-classes :forward-chaining))

  (defthm path-contains-and-sibling-of-atom
    (implies (not (consp path))
             (equal (path-contains-and-sibling x sink path aignet) nil))
    :hints (("goal" :expand ((path-contains-and-sibling x sink path aignet)))))

  (defthm path-contains-and-sibling-of-cons
    (equal (path-contains-and-sibling x sink (cons first rest) aignet)
           (or (and (equal (stype (car (lookup-id sink aignet))) :and)
                    (equal (fanin (b-not first)
                                  (lookup-id sink aignet))
                           (lit-fix x)))
               (path-contains-and-sibling
                x
                (lit->var (fanin first (lookup-id sink aignet)))
                rest aignet)))
    :hints (("goal" :expand ((:free (path) (path-contains-and-sibling x sink path aignet))))))
  
  (defthm path-contains-and-sibling-of-nil
    (equal (path-contains-and-sibling x sink nil aignet) nil)
    :hints (("goal" :expand ((path-contains-and-sibling x sink nil aignet)))))
  
  (defretd path-contains-and-sibling-when-gte-sink
    (implies (and (<= (nfix sink) (lit->var x))
                  (path-existsp sink path aignet))
             (not contains))
    :hints (("goal" :induct <call> :expand (<call> (path-existsp sink path aignet))))))

;; Check whether any two AND siblings in the path are contradictory literals.
(define path-contains-contradictory-siblings ((sink natp) (path bit-listp) aignet)
  :guard (and (id-existsp sink aignet)
              (path-existsp sink path aignet))
  :measure (len path)
  :guard-hints (("Goal" :expand ((path-existsp sink path aignet))))
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-fix-backchain
                                        lookup-id-out-of-bounds
                                        lookup-id-in-bounds-when-positive))))
  (b* (((when (atom path)) nil)
       (next (mbe :logic (non-exec (fanin (car path)
                                          (lookup-id sink aignet)))
                  :exec (snode->fanin (id->slot sink (car path) aignet))))
       ((unless (mbe :logic (non-exec (eq (stype (car (lookup-id sink aignet))) :and))
                     :exec (eql (id->regp sink aignet) 0)))
        (path-contains-contradictory-siblings (lit->var next) (cdr path) aignet))
       (sib (mbe :logic (non-exec (fanin (b-not (car path))
                                         (lookup-id sink aignet)))
                 :exec (snode->fanin (id->slot sink (b-not (car path)) aignet)))))
    (or (path-contains-and-sibling (lit-negate sib) (lit->var next) (cdr path) aignet)
        (path-contains-contradictory-siblings (lit->var next) (cdr path) aignet)))
  ///
  (local (in-theory (disable (:d path-contains-contradictory-siblings))))

  (defthm path-contains-contradictory-siblings-of-atom
    (implies (not (consp path))
             (equal (path-contains-contradictory-siblings sink path aignet) nil))
    :hints (("goal" :expand ((path-contains-contradictory-siblings sink path aignet)))))

  (defthm path-contains-contradictory-siblings-of-cons
    (equal (path-contains-contradictory-siblings sink (cons first rest) aignet)
           (let ((next (fanin first (lookup-id sink aignet))))
             (or (and (equal (stype (car (lookup-id sink aignet))) :and)
                      (path-contains-and-sibling
                       (lit-negate (fanin (b-not first)
                                          (lookup-id sink aignet)))
                       (lit->var next) rest aignet))
                 (path-contains-contradictory-siblings
                  (lit->var next) rest aignet))))
    :hints (("goal" :expand ((:free (path) (path-contains-contradictory-siblings sink path aignet))))))
  
  (defthm path-contains-contradictory-siblings-of-nil
    (equal (path-contains-contradictory-siblings sink nil aignet) nil)
    :hints (("goal" :expand ((path-contains-contradictory-siblings sink nil aignet)))))

  (defthm path-contains-contradictory-siblings-when-contains-contradictory-and-siblings
    (implies (and (path-contains-and-sibling lit sink path aignet)
                  (path-contains-and-sibling (lit-negate lit) sink path aignet))
             (path-contains-contradictory-siblings sink path aignet))
    :hints (("Goal" :induct (path-contains-contradictory-siblings sink path aignet)
             :expand ((path-contains-contradictory-siblings sink path aignet)
                      (:free (lit) (path-contains-and-sibling lit sink path aignet)))))))


;; Check whether any AND siblings in the path are 0 under the inputs with the
;; source both toggled and not toggled.
(define path-contains-const0-sibling ((sink natp) (source natp) (toggles nat-listp) invals regvals (path bit-listp) aignet)
  :guard (and (id-existsp sink aignet)
              (id-existsp source aignet)
              (path-existsp sink path aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :measure (len path)
  :guard-hints (("Goal" :expand ((path-existsp sink path aignet))))
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-fix-backchain
                                        lookup-id-out-of-bounds
                                        lookup-id-in-bounds-when-positive))))
  :returns (contains)
  (b* (((when (atom path)) nil)
       (next (mbe :logic (non-exec (fanin (car path)
                                          (lookup-id sink aignet)))
                  :exec (snode->fanin (id->slot sink (car path) aignet))))
       ((unless (mbe :logic (non-exec (eq (stype (car (lookup-id sink aignet))) :and))
                     :exec (eql (id->regp sink aignet) 0)))
        (path-contains-const0-sibling (lit->var next) source toggles invals regvals (cdr path) aignet))
       (sib (mbe :logic (non-exec (fanin (b-not (car path))
                                         (lookup-id sink aignet)))
                 :exec (snode->fanin (id->slot sink (b-not (car path)) aignet)))))
    (or (and (eql 0 (lit-eval-toggle sib toggles invals regvals aignet))
             (eql 0 (lit-eval-toggle sib (cons source toggles) invals regvals aignet)))
        (path-contains-const0-sibling (lit->var next) source toggles invals regvals (cdr path) aignet)))
  ///
  (local (in-theory (disable (:d path-contains-const0-sibling))))

  (defret path-contains-const0-sibling-when-has-sibling
    (implies (and (path-contains-and-sibling x sink path aignet)
                  (equal (lit-eval-toggle x toggles invals regvals aignet) 0)
                  (equal (lit-eval-toggle x (cons source toggles) invals regvals aignet) 0))
             contains)
    :hints (("goal" :induct <call>
             :expand (<call>
                      (path-contains-and-sibling x sink path aignet))))))

(local (in-theory (disable member
                           lookup-id-in-bounds-when-positive
                           lookup-id-out-of-bounds
                           satlink::equal-of-lit-negate-backchain
                           satlink::lit-negate-not-equal-when-vars-mismatch)))

(define toggle-witness-path ((sink natp) (source natp) (toggles nat-listp) invals regvals aignet)
  ;; Given that sink is toggled by source, find a path from sink to source
  ;; containing no contradictory AND siblings and no const0 siblings.
  :guard (and (id-existsp sink aignet)
              (id-existsp source aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :measure (nfix sink)
  :returns (path bit-listp)
  :prepwork ((local (in-theory (disable satlink::equal-of-lit-fix-backchain
                                        lookup-id-out-of-bounds
                                        lookup-id-in-bounds-when-positive))))
  (b* (((when (or (<= (lnfix sink) (lnfix source))
                  (not (eql (id->type sink aignet) (gate-type)))))
        nil)
       (fanin0 (gate-id->fanin0 sink aignet))
       (fanin1 (gate-id->fanin1 sink aignet))
       (xor (eql (id->regp sink aignet) 1))
       (fanin0-val (lit-eval-toggle fanin0 toggles invals regvals aignet))
       (fanin1-val (lit-eval-toggle fanin1 toggles  invals regvals aignet))
       (fanin0-toggles (not (eql (lit-eval-toggle fanin0 (cons source toggles) invals regvals aignet)
                                 fanin0-val)))
       (fanin1-toggles (not (eql (lit-eval-toggle fanin1 (cons source toggles) invals regvals aignet)
                                 fanin1-val)))
       ((when xor)
        (if fanin0-toggles
            (cons 0 (toggle-witness-path (lit->var fanin0) source toggles invals regvals aignet))
          (cons 1 (toggle-witness-path (lit->var fanin1) source toggles invals regvals aignet))))
       ((unless fanin0-toggles)
        ;; fanin0 must be const 1.
        (cons 1 (toggle-witness-path (lit->var fanin1) source toggles invals regvals aignet)))
       ((unless fanin1-toggles)
        (cons 0 (toggle-witness-path (lit->var fanin0) source toggles invals regvals aignet)))
       ((when (<= (lit->var fanin0) (lit->var fanin1)))
        (cons 0 (toggle-witness-path (lit->var fanin0) source toggles invals regvals aignet))))
    (cons 1 (toggle-witness-path (lit->var fanin1) source toggles invals regvals aignet)))
  ///
  (local (in-theory (disable (:d toggle-witness-path))))
  
  (defret path-existsp-of-toggle-witness-path
    (path-existsp sink path aignet)
    :hints (("goal" :induct <call> :expand (<call>))))

  (local (defthm cancel-equal-b-xor
           (equal (equal (b-xor a b) (b-xor a c))
                  (equal (bfix b) (bfix c)))
           :hints(("Goal" :in-theory (enable b-xor bfix)))))
  
  (local (defthm equal-of-b-and-first-same
           (equal (equal (b-and a b) (b-and a c))
                  (or (equal (bfix a) 0)
                      (equal (bfix b) (bfix c))))
           :hints(("Goal" :in-theory (enable b-and bfix)))))

  (local (defthm equal-of-b-and-second-same
           (equal (equal (b-and b a) (b-and c a))
                  (or (equal (bfix a) 0)
                      (equal (bfix b) (bfix c))))
           :hints(("Goal" :in-theory (enable b-and bfix)))))

  (local (defthm equal-of-b-and-first/second
           (equal (equal (b-and b a) (b-and a c))
                  (or (equal (bfix a) 0)
                      (equal (bfix b) (bfix c))))
           :hints(("Goal" :in-theory (enable b-and bfix)))))

  (defret path-endpoint-of-<fn>
    (implies (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                         (id-eval-toggle sink (cons source toggles) invals regvals aignet)))
             (equal (path-endpoint sink path aignet) (nfix source)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (a b c) (member-equal a (cons b c)))
                      (:free (toggles) (id-eval-toggle sink toggles invals regvals aignet))
                      (:free (x y) (lit-eval-toggle x y invals regvals aignet))
                      (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet))))))

  (defret const0-siblings-of-<fn>
    (implies (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                         (id-eval-toggle sink (cons source toggles) invals regvals aignet)))
             (not (path-contains-const0-sibling
                   sink source toggles invals regvals path aignet)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (a b c) (member-equal a (cons b c)))
                      (:free (toggles) (id-eval-toggle sink toggles invals regvals aignet))
                      (:free (x y) (lit-eval-toggle x y invals regvals aignet))
                      (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet))
                      (:free (p source)
                       (path-contains-const0-sibling
                        sink source toggles invals regvals p aignet))))))

  (local (defret path-contains-no-and-sibling-when-no-const0-sibling
           (implies (and (bind-free '((invals . invals) (regvals . regvals) (source . source) (toggles . toggles))
                                    (invals regvals source toggles))
                         (not contains)
                         (equal (lit-eval-toggle x toggles invals regvals aignet) 0)
                         (equal (lit-eval-toggle x (cons source toggles) invals regvals aignet) 0))
                    (not (path-contains-and-sibling x sink path aignet)))
           :fn path-contains-const0-sibling))

  (local (defthm equal-b-not-of-bits
           (implies (and (bitp x) (bitp y))
                    (equal (equal (b-not x) y)
                           (not (equal x y))))
           :hints(("Goal" :in-theory (enable bitp)))))

  (local (in-theory (enable path-contains-and-sibling-when-gte-sink)))
  
  (defret contradictions-of-<fn>
    (implies (not (equal (id-eval-toggle sink toggles invals regvals aignet)
                         (id-eval-toggle sink (cons source toggles) invals regvals aignet)))
             (not (path-contains-contradictory-siblings
                   sink path aignet)))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (:free (a b c) (member-equal a (cons b c)))
                      (:free (toggles) (id-eval-toggle sink toggles invals regvals aignet))
                      (:free (x y) (lit-eval-toggle x y invals regvals aignet))
                      (:free (x y z) (eval-and-of-lits-toggle x y z invals regvals aignet))
                      (:free (x y z) (eval-xor-of-lits-toggle x y z invals regvals aignet)))))))


;; Dominator info for each node is stored as either
;; (1) T, signifying that every path from an output to the node contains
;;     contradictory literals, or
;; (2) a list of literals, all of which must occur as AND-siblings in every
;;     path from an output to the node not containing contradictory literals.


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


;; (define cube-contradictionp ((x lit-listp))
;;   :returns (contradictionp maybe-litp :rule-classes :type-prescription)
;;   (if (atom x)
;;       nil
;;     (if (member (lit-negate (car x)) (lit-list-fix (cdr x)))
;;         (lit-fix (car x))
;;       (cube-contradictionp (cdr x))))
;;   ///
;;   (local (defthm aignet-eval-conjunction-when-member
;;            (implies (and (member x (lit-list-fix y))
;;                          (equal (lit-eval x invals regvals aignet) 0))
;;                     (equal (aignet-eval-conjunction y invals regvals aignet) 0))
;;            :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))
  
;;   (defret <fn>-correct
;;     (implies contradictionp
;;              (equal (aignet-eval-conjunction x invals regvals aignet)
;;                     0))
;;     :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

;;   (defret <fn>-membership
;;     (implies contradictionp
;;              (and (member-equal contradictionp (lit-list-fix x))
;;                   (member (lit-negate contradictionp) (lit-list-fix x)))))

;;   (defret <fn>-membership-no-fix
;;     (implies (and contradictionp (lit-listp x))
;;              (and (member-equal contradictionp x)
;;                   (member (lit-negate contradictionp) x)))))



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

  (defretd <fn>-implies-reached
    (implies (and subsetp
                  (obs-dom-info->reached y)
                  (not (cube-contradictionp (obs-dom-info->doms y)))
                  )
             (obs-dom-info->reached x)))

  (defretd <fn>-implies-member
    (implies (and subsetp
                  (obs-dom-info->reached y)
                  (not (cube-contradictionp (obs-dom-info->doms y)))
                  (not (member-equal lit (obs-dom-info->doms y))))
             (not (member lit (obs-dom-info->doms x))))))

(define obs-dom-info-add ((lit litp) (x obs-dom-info-p))
  :returns (new obs-dom-info-p)
  (b* (((obs-dom-info x)))
    (if x.reached
        (make-obs-dom-info-reached (cons (lit-fix lit) x.doms))
      (make-obs-dom-info-unreached)))
  ///

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




(define obs-dom-info-for-child ((fanout-info obs-dom-info-p)
                                (fanout natp)
                                (fanin bitp)
                                aignet)
  :guard (and (id-existsp fanout aignet)
              (eql (id->type fanout aignet) (gate-type)))
  :returns (child-fanout-info obs-dom-info-p)
  (b* (;; (fanin0 (gate-id->fanin0 fanout aignet))
       ;; (fanin1 (gate-id->fanin1 fanout aignet))
       (xor (eql 1 (id->regp fanout aignet))))
    (if xor
        ;; Won't complicate things with this optimization since hashing should prevent this anyhow.
        ;; (if (or (eql fanin0 fanin1)
        ;;         (eql fanin0 (lit-negate fanin1)))
        ;;     (make-obs-dom-info-unreached)
        (obs-dom-info-fix fanout-info)
      ;; (cond ((eql fanin0 fanin1) (obs-dom-info-fix fanout-info))
      ;;       ((eql fanin0 (lit-negate fanin1)) (make-obs-dom-info-unreached))
      ;;       (t
      (obs-dom-info-add
       (mbe :logic (non-exec (fanin (b-not fanin) (lookup-id fanout aignet)))
            :exec (snode->fanin (id->slot-fn fanout (b-not fanin) aignet)))
       fanout-info)))
  ///

  (defret <fn>-when-xor
    (implies (equal (stype (car (lookup-id fanout aignet))) :xor)
             (equal child-fanout-info
                    (obs-dom-info-fix fanout-info))))
  
  (defret <fn>-when-and
    (implies (equal (stype (car (lookup-id fanout aignet))) :and)
             (equal child-fanout-info
                    (obs-dom-info-add (fanin (b-not fanin)
                                             (lookup-id fanout aignet))
                                      fanout-info)))))



(define obs-dom-fanout-ok ((fanout natp) obs-dom-array aignet)
  :guard (and (id-existsp fanout aignet)
              (<= (num-fanins aignet) (dominfo-length obs-dom-array)))
  (or (not (equal (id->type fanout aignet) (gate-type)))
      (and (obs-dom-info-subsetp
            (get-dominfo (lit->var (gate-id->fanin0 fanout aignet)) obs-dom-array)
            (obs-dom-info-for-child
             (get-dominfo fanout obs-dom-array) fanout 0 aignet))
           (obs-dom-info-subsetp
            (get-dominfo (lit->var (gate-id->fanin1 fanout aignet)) obs-dom-array)
            (obs-dom-info-for-child
             (get-dominfo fanout obs-dom-array) fanout 1 aignet))))
  ///
  (defthm obs-dom-fanout-ok-implies
    (implies (and (obs-dom-fanout-ok fanout obs-dom-array aignet)
                  (equal (ctype (stype (car (lookup-id fanout aignet)))) :gate))
             (obs-dom-info-subsetp
              (nth (lit->var (fanin dir (lookup-id fanout aignet))) obs-dom-array)
              (obs-dom-info-for-child
               (nth fanout obs-dom-array) fanout dir aignet)))
    :hints (("goal" :cases ((equal dir 1)))))

  (defthmd obs-dom-fanout-ok-out-of-bounds
    (implies (< (fanin-count aignet) (nfix n))
             (obs-dom-fanout-ok n obs-dom-array aignet))
    :hints(("Goal" :in-theory (enable obs-dom-fanout-ok)))))





(define obs-dom-info-normalize ((x obs-dom-info-p))
  :returns (new-x obs-dom-info-p)
  (b* (((obs-dom-info x)))
    (if (and x.reached
             (cube-contradictionp x.doms))
        (make-obs-dom-info-unreached)
      (obs-dom-info-fix x)))
  ///

  ;; (local (defthm cube-contradictionp-by-member
  ;;          (implies (and (member x cube)
  ;;                        (member (lit-negate x) cube)
  ;;                        (lit-listp cube))
  ;;                   (cube-contradictionp cube))
  ;;          :hints(("Goal" :in-theory (enable cube-contradictionp)))))
  
  ;; (local (defthm cube-contradictionp-when-subsetp
  ;;          (implies (and (subsetp x y)
  ;;                        (cube-contradictionp x)
  ;;                        (lit-listp y) (lit-listp x))
  ;;                   (cube-contradictionp y))
  ;;          :hints(("Goal" :in-theory (enable cube-contradictionp
  ;;                                            subsetp)))))
  (local (in-theory (enable cube-contradictionp-by-member
                            cube-contradictionp-when-subsetp)))
  
  (defret subsetp-of-<fn>-1
    (iff (obs-dom-info-subsetp new-x y)
         (obs-dom-info-subsetp x y))
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp))))

  (defret subsetp-of-<fn>-2
    (iff (obs-dom-info-subsetp y new-x)
         (obs-dom-info-subsetp y x))
    :hints(("Goal" :in-theory (enable obs-dom-info-subsetp)))))

(define obs-dom-info-intersect ((x obs-dom-info-p) (y obs-dom-info-p))
  :returns (int obs-dom-info-p)
  (b* (((obs-dom-info x))
       ((obs-dom-info y)))
    (if (and x.reached (not (cube-contradictionp x.doms)))
        (if (and y.reached (not (cube-contradictionp y.doms)))
            (make-obs-dom-info-reached (intersection$ x.doms y.doms))
          (obs-dom-info-fix x))
      (obs-dom-info-normalize y)))
  ///
  (local (in-theory (enable obs-dom-info-subsetp
                            obs-dom-info-normalize)))
  
  (local (defthm subsetp-of-intersect-1
           (subsetp (intersection$ x y) x)))
  (local (defthm subsetp-of-intersect-2
           (subsetp (intersection$ x y) y)))
  (local (defthm lit-negate-by-equal-lit-negate
           (implies (equal (lit-negate x) (lit-fix y))
                    (equal (lit-negate y) (lit-fix x)))))
  (local (defthm cube-contradictionp-implies-not-member
           (implies (and (not (cube-contradictionp y))
                         (member-equal (lit-negate x) (lit-list-fix y)))
                    (not (member-equal (lit-fix x) (lit-list-fix y))))
           :hints(("Goal" :in-theory (enable cube-contradictionp lit-list-fix)))))
  (local (defthm cube-contradiction-by-subsetp
           (implies (and (subsetp (lit-list-fix x) (lit-list-fix y))
                         (not (cube-contradictionp y)))
                    (not (cube-contradictionp x)))
           :hints(("Goal" :in-theory (enable cube-contradictionp lit-list-fix)
                   :induct (lit-list-fix x)))))

  (local (defthm cube-contradiction-by-subsetp-lits
           (implies (and (subsetp x y)
                         (lit-listp x) (lit-listp y)
                         (not (cube-contradictionp y)))
                    (not (cube-contradictionp x)))
           :hints (("goal" :use ((:instance cube-contradiction-by-subsetp))
                    :in-theory (disable cube-contradiction-by-subsetp)))))
  
  (defret obs-dom-info-subsetp-of-obs-dom-info-intersect-1
    (obs-dom-info-subsetp int x))

  (defret obs-dom-info-subsetp-of-obs-dom-info-intersect-2
    (obs-dom-info-subsetp int y))

  (defret obs-dom-info-intersect-preserves-obs-dom-info-subsetp-1
    (implies (obs-dom-info-subsetp x z)
             (obs-dom-info-subsetp int z)))
  
  (defret obs-dom-info-intersect-preserves-obs-dom-info-subsetp-2
    (implies (obs-dom-info-subsetp y z)
             (obs-dom-info-subsetp int z))))


(define obs-dom-info-sweep-node ((n natp) obs-dom-array aignet)
  :guard (and (id-existsp n aignet)
              (< n (dominfo-length obs-dom-array)))
  :returns new-obs-dom-array
  (b* ((slot0 (id->slot n 0 aignet))
       (type (snode->type slot0))
       (node-info (get-dominfo n obs-dom-array)))
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
    (implies (< (nfix n) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-preserves-correct
    (implies (and (< (nfix n) (nfix i))
                  (obs-dom-fanout-ok i obs-dom-array aignet))
             (obs-dom-fanout-ok i new-obs-dom-array aignet))
    :hints(("Goal" :in-theory (enable obs-dom-fanout-ok)
            :do-not-induct t)))

  (defret <fn>-sets-correct
    (obs-dom-fanout-ok n new-obs-dom-array aignet)
    :hints(("Goal" :in-theory (enable obs-dom-fanout-ok)
            :do-not-induct t)))

  (local (defthm intersection-with-nil
           (equal (intersection-equal x nil) nil)
           :hints(("Goal" :in-theory (enable intersection-equal)))))
  
  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-dom-array)
                    (make-obs-dom-info-reached nil))
             (equal (nth i new-obs-dom-array)
                    (make-obs-dom-info-reached nil)))
    :hints(("Goal" :in-theory (enable obs-dom-info-intersect)))))



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
    (implies (<= (nfix n) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-preserves-correct
    (implies (and (<= (nfix n) (nfix i))
                  (obs-dom-fanout-ok i obs-dom-array aignet))
             (obs-dom-fanout-ok i new-obs-dom-array aignet)))

  (defret <fn>-sets-correct
    (implies (< (nfix i) (nfix n))
             (obs-dom-fanout-ok i new-obs-dom-array aignet)))
  
  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-dom-array)
                    (make-obs-dom-info-reached nil))
             (equal (nth i new-obs-dom-array)
                    (make-obs-dom-info-reached nil)))
    :hints(("Goal" :in-theory (enable obs-dom-info-intersect)))))

(define obs-dom-info-set-pos ((n natp) obs-dom-array aignet)
  :guard (and (<= n (num-outs aignet))
              (<= (num-fanins aignet) (dominfo-length obs-dom-array)))
  :measure (nfix (- (num-outs aignet) (nfix n)))
  :returns new-obs-dom-array
  (b* (((when (mbe :logic (zp (- (num-outs aignet) (nfix n)))
                   :exec (eql n (num-outs aignet))))
        obs-dom-array)
       (fanin-node (lit->var (outnum->fanin n aignet)))
       (obs-dom-array (set-dominfo fanin-node (make-obs-dom-info-reached nil) obs-dom-array)))
    (obs-dom-info-set-pos (1+ (lnfix n)) obs-dom-array aignet))
  ///
  (defret <fn>-length
    (implies (< (fanin-count aignet) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-dom-array)
                    (make-obs-dom-info-reached nil))
             (equal (nth i new-obs-dom-array)
                    (make-obs-dom-info-reached nil))))

  (defret fanin-dominfo-of-<fn>
    (implies (and (<= (nfix n) (nfix k))
                  (< (nfix k) (num-outs aignet)))
             (equal (nth (lit->var (fanin 0 (lookup-stype k :po aignet))) new-obs-dom-array)
                    (make-obs-dom-info-reached nil)))))

(define obs-dom-info-set-nxsts ((n natp) obs-dom-array aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (dominfo-length obs-dom-array)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns new-obs-dom-array
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql n (num-regs aignet))))
        obs-dom-array)
       (fanin-node (lit->var (regnum->nxst n aignet)))
       (obs-dom-array (set-dominfo fanin-node (make-obs-dom-info-reached nil) obs-dom-array)))
    (obs-dom-info-set-nxsts (1+ (lnfix n)) obs-dom-array aignet))
  ///
  (defret <fn>-length
    (implies (< (fanin-count aignet) (len obs-dom-array))
             (equal (len new-obs-dom-array)
                    (len obs-dom-array))))

  (defret <fn>-preserves-empty-dominators
    (implies (equal (nth i obs-dom-array)
                    (make-obs-dom-info-reached nil))
             (equal (nth i new-obs-dom-array)
                    (make-obs-dom-info-reached nil))))

  (defret fanin-dominfo-of-<fn>
    (implies (and (<= (nfix n) (nfix k))
                  (< (nfix k) (num-regs aignet)))
             (equal (nth (lit->var (lookup-reg->nxst k aignet)) new-obs-dom-array)
                    (make-obs-dom-info-reached nil)))))

(define aignet-compute-obs-dom-info (obs-dom-array aignet)
  :returns new-obs-dom-array
  (b* ((obs-dom-array (resize-dominfo 0 obs-dom-array))
       (obs-dom-array (resize-dominfo (num-fanins aignet) obs-dom-array))
       (obs-dom-array (obs-dom-info-set-pos 0 obs-dom-array aignet))
       (obs-dom-array (obs-dom-info-set-nxsts 0 obs-dom-array aignet)))
    (obs-dom-info-sweep-nodes (num-fanins aignet) obs-dom-array aignet))
  ///
  (defret <fn>-length
    (equal (len new-obs-dom-array) (num-fanins aignet)))

  (defret po-dominfo-of-<fn>
    (implies (< (nfix k) (num-outs aignet))
             (equal (nth (lit->var (fanin 0 (lookup-stype k :po aignet))) new-obs-dom-array)
                    (make-obs-dom-info-reached nil))))

  (defret nxst-dominfo-of-<fn>
    (implies (< (nfix k) (num-regs aignet))
             (equal (nth (lit->var (lookup-reg->nxst k aignet)) new-obs-dom-array)
                    (make-obs-dom-info-reached nil))))

  (defret <fn>-fanouts-ok
    (obs-dom-fanout-ok i new-obs-dom-array aignet)
    :hints(("Goal" :in-theory (enable obs-dom-fanout-ok-out-of-bounds)
            :cases ((< (nfix i) (+ 1 (fanin-count aignet))))))))


(defsection obs-dom-array-correct
  
  (defun-sk obs-dom-array-correct (obs-dom-array aignet)
    (forall fanout
            (obs-dom-fanout-ok fanout obs-dom-array aignet))
    :rewrite :direct)

  (in-theory (disable obs-dom-array-correct))

  (defthm obs-dom-array-correct-of-obs-dom-info-sweep-nodes
    (obs-dom-array-correct
     (obs-dom-info-sweep-nodes (+ 1 (fanin-count aignet)) obs-dom-array aignet)
     aignet)
    :hints(("Goal" :in-theory (enable obs-dom-array-correct
                                      obs-dom-fanout-ok-out-of-bounds)
            :cases ((<= (nfix
                         (obs-dom-array-correct-witness
                          (obs-dom-info-sweep-nodes (+ 1 (fanin-count aignet))
                                                    obs-dom-array aignet)
                          aignet))
                        (fanin-count aignet))))))

  (defthm obs-dom-array-correct-of-aignet-compute-obs-dom-info
    (obs-dom-array-correct (aignet-compute-obs-dom-info obs-dom-array aignet) aignet)
    :hints(("Goal" :in-theory (enable obs-dom-array-correct)))))



(define path-contains-and-siblings ((x lit-listp) (sink natp) (path bit-listp) aignet)
  :guard (and (id-existsp sink aignet)
              (path-existsp sink path aignet))
  (if (atom x)
      t
    (and (path-contains-and-sibling (car x) sink path aignet)
         (path-contains-and-siblings (cdr x) sink path aignet)))
  ///
  (defthm path-contains-and-siblings-implies-member
    (implies (and (member lit x)
                  (path-contains-and-siblings x sink path aignet))
             (path-contains-and-sibling lit sink path aignet)))

  (defthm path-contains-and-siblings-when-atom
    (implies (not (consp x))
             (equal (path-contains-and-siblings x sink path aignet) t))))

(define path-last ((x bit-listp))
  :guard (consp x)
  :returns (last bitp :rule-classes :type-prescription)
  (lbfix (car (last x))))

(define path-butlast ((x bit-listp))
  :guard (consp x)
  :returns (prefix bit-listp)
  (bit-list-fix (butlast x 1))
  ///
  (defret len-of-<fn>
    (implies (consp x)
             (equal (len prefix) (+ -1 (len x)))))
  
  (defret path-exists-of-path-butlast
    (implies (path-existsp sink x aignet)
             (path-existsp sink prefix aignet))
    :hints(("Goal" :in-theory (enable path-existsp))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (not (consp x)))))

  (local (in-theory (disable satlink::equal-of-lit-fix-backchain)))

  (defthmd path-endpoint-in-terms-of-butlast
    (equal (path-endpoint sink path aignet)
           (if (atom path)
               (nfix sink)
             (b* ((prev (path-endpoint sink (path-butlast path) aignet))
                  (last (path-last path)))
               (lit->var (fanin last (lookup-id prev aignet))))))
    :hints(("Goal" :in-theory (enable path-last (:i path-endpoint))
            :induct (path-endpoint sink path aignet)
            :expand ((:free (path) (path-endpoint sink path aignet)))))
    :rule-classes ((:definition :controller-alist ((path-endpoint nil t nil)))))

    (defthmd path-existsp-in-terms-of-butlast
      (equal (path-existsp sink path aignet)
             (if (atom path)
                 t
               (and (path-existsp sink (path-butlast path) aignet)
                    (equal (ctype (stype (car (lookup-id
                                               (path-endpoint sink (path-butlast path) aignet)
                                               aignet))))
                           :gate))))
      :hints(("Goal" :in-theory (enable path-endpoint path-existsp)))
      :rule-classes ((:definition :controller-alist ((path-existsp nil t nil)))))
  


  (defthmd path-contains-and-sibling-in-terms-of-butlast
    ;;(implies (consp path)
    (equal (path-contains-and-sibling x sink path aignet)
           (if (atom path)
               nil
             (or (path-contains-and-sibling x sink (path-butlast path) aignet)
                 (let ((sink2 (path-endpoint sink (path-butlast path) aignet)))
                   (and (equal (stype (car (lookup-id sink2 aignet))) :and)
                        (equal (fanin (b-not (path-last path))
                                      (lookup-id sink2 aignet))
                               (lit-fix x)))))))
    :hints(("Goal" :in-theory (enable path-last (:i path-endpoint))
            :induct (path-endpoint sink path aignet)
            :expand ((:with path-endpoint (:free (path) (path-endpoint sink path aignet)))
                     (:free (path) (path-contains-and-sibling x sink path aignet)))))
    :rule-classes ((:definition :controller-alist ((path-contains-and-sibling nil nil t nil)))))

  (defthmd path-contains-contradictory-siblings-in-terms-of-butlast
    (equal (path-contains-contradictory-siblings sink path aignet)
           (if (atom path)
               nil
             (or (path-contains-contradictory-siblings sink (path-butlast path) aignet)
                 (let ((sink2 (path-endpoint sink (path-butlast path) aignet)))
                   (and (equal (stype (car (lookup-id sink2 aignet))) :and)
                        (path-contains-and-sibling
                         (lit-negate (fanin (b-not (path-last path))
                                            (lookup-id sink2 aignet)))
                         sink
                         (path-butlast path) aignet))))))
    :hints(("Goal" :in-theory (e/d (path-last (:i path-endpoint)))
            :induct (path-endpoint sink path aignet)
            :expand ((:with path-endpoint (:free (path) (path-endpoint sink path aignet)))
                     (:free (path) (path-contains-contradictory-siblings sink path aignet))
                     (:with path-contains-and-sibling-in-terms-of-butlast
                      (:free (x sink) (path-contains-and-sibling x sink (cdr path) aignet))))))
    :rule-classes ((:definition :controller-alist ((path-contains-contradictory-siblings nil t nil)))))

  (local (defthm path-contains-and-siblings-of-remove-equal
           (implies (path-contains-and-sibling lit sink path aignet)
                    (equal (path-contains-and-siblings (remove-equal lit x) sink path aignet)
                           (path-contains-and-siblings x sink path aignet)))
           :hints(("Goal" :in-theory (enable path-contains-and-siblings remove-equal)))))
  
  (local (defthm lit-listp-of-remove-equal
           (implies (lit-listp x)
                    (lit-listp (remove-equal k x)))))

  (local (defthm remove-equal-same
           (equal (remove-equal k (remove-equal k x))
                  (remove-equal k x))))
  
  (defthmd path-contains-and-siblings-in-terms-of-butlast
    (equal (path-contains-and-siblings x sink path aignet)
           (b* (((when (atom path)) (atom x))
                (prev-endpoint (path-endpoint sink (path-butlast path) aignet))
                (last (path-last path))
                (sib (fanin (b-not last) (lookup-id prev-endpoint aignet)))
                ((when (equal (stype (car (lookup-id prev-endpoint aignet))) :and))
                 (path-contains-and-siblings
                  (remove sib (lit-list-fix x))
                  sink (path-butlast path) aignet)))
             (path-contains-and-siblings
              x sink (path-butlast path) aignet)))
    :hints(("Goal" :in-theory (enable path-contains-and-siblings)
            :induct (path-contains-and-siblings x sink path aignet)
            :expand ((:free (path) (path-contains-and-siblings x sink path aignet))
                     (:with path-contains-and-sibling-in-terms-of-butlast
                      (:free (x) (path-contains-and-sibling x sink path aignet)))
                     (lit-list-fix x))))))


(defsection obs-dom-array-implies-path-contains-dominators
  (local
   (progn
     (define path-induct-reverse ((x bit-listp))
       :measure (len x)
       (if (atom x)
           (bit-list-fix x)
         (path-induct-reverse (path-butlast x))))

     (defthm path-contains-and-siblings-implies-not-cube-contradictionp
       (implies (and (path-contains-and-siblings
                      lits sink path aignet)
                     (not (path-contains-contradictory-siblings
                           sink path aignet)))
                (not (cube-contradictionp lits)))
       :hints (("Goal" :use ((:instance path-contains-and-siblings-implies-member
                              (lit (cube-contradiction-witness lits))
                              (x (lit-list-fix lits)))
                             (:instance path-contains-and-siblings-implies-member
                              (lit (lit-negate (cube-contradiction-witness lits)))
                              (x (lit-list-fix lits))))
                :in-theory (disable path-contains-and-siblings-implies-member))))

     (defthm path-contains-and-siblings-implies-not-member
       (implies (and (path-contains-and-siblings
                      lits sink path aignet)
                     (not (path-contains-and-sibling lit sink path aignet))
                     (litp lit) (lit-listp lits))
                (not (member lit lits)))
       :hints(("Goal" :in-theory (enable member path-contains-and-siblings))))


     (defthm obs-dom-fanout-ok-implies-reachable-and
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array aignet)
                     (equal (ctype (stype (car (lookup-id fanout aignet)))) :gate)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))))
                     (not (member-equal
                           (lit-negate (fanin (b-not dir)
                                              (lookup-id fanout aignet)))
                           (obs-dom-info->doms (nth fanout obs-dom-array)))))
                (obs-dom-info->reached (nth (lit->var (fanin dir (lookup-id fanout aignet)))
                                            obs-dom-array)))
       :hints(("Goal" :in-theory (e/d (obs-dom-info-for-child
                                       obs-dom-info-add
                                       obs-dom-info-subsetp)
                                      (obs-dom-fanout-ok-implies))
               :expand ((:free (a b) (cube-contradictionp (cons a b))))
               :use obs-dom-fanout-ok-implies)))

     (defthm obs-dom-fanout-ok-implies-reachable-xor
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :xor)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))))
                     ;; (not (member-equal
                     ;;       (lit-negate (fanin (b-not dir)
                     ;;                          (lookup-id fanout aignet)))
                     ;;       (obs-dom-info->doms (nth fanout obs-dom-array))))
                     )
                (obs-dom-info->reached (nth (lit->var (fanin dir (lookup-id fanout aignet)))
                                            obs-dom-array)))
       :hints(("Goal" :in-theory (e/d (obs-dom-info-for-child
                                       obs-dom-info-add
                                       obs-dom-info-subsetp)
                                      (obs-dom-fanout-ok-implies))
               :expand ((:free (a b) (cube-contradictionp (cons a b))))
               :use obs-dom-fanout-ok-implies)))



     (defthm subsetp-of-doms-when-reached
       (implies (and (obs-dom-info-subsetp x y)
                     (obs-dom-info->reached y)
                     (not (cube-contradictionp
                           (obs-dom-info->doms y))))
                (subsetp (obs-dom-info->doms x) (obs-dom-info->doms y)))
       :hints(("Goal" :in-theory (enable obs-dom-info-subsetp))))

     (defthm path-contains-and-siblings-when-subsetp
       (implies (and (path-contains-and-siblings x sink path aignet)
                     (subsetp y x))
                (path-contains-and-siblings y sink path aignet))
       :hints(("Goal" :in-theory (enable path-contains-and-siblings subsetp)
               :induct (path-contains-and-siblings y sink path aignet)
               :expand ((path-contains-and-siblings y sink path aignet)
                        (subsetp y x)))))


     (defthm obs-dom-fanout-ok-implies-subsetp-xor
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :xor)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array)))))
                (subsetp (obs-dom-info->doms
                          (nth (lit->var (fanin dir (lookup-id fanout aignet))) obs-dom-array))
                         (obs-dom-info->doms
                          (nth fanout obs-dom-array))))
       :hints (("goal" :use obs-dom-fanout-ok-implies
                :in-theory (e/d (obs-dom-info-for-child)
                                (obs-dom-fanout-ok-implies)))))


     (defthm obs-dom-fanout-ok-implies-subsetp-and
       (implies (and (obs-dom-fanout-ok fanout obs-dom-array aignet)
                     (equal (stype (car (lookup-id fanout aignet))) :and)
                     (obs-dom-info->reached (nth fanout obs-dom-array))
                     (not (cube-contradictionp
                           (obs-dom-info->doms (nth fanout obs-dom-array))))
                     (not (member (lit-negate (fanin (b-not dir) (lookup-id fanout aignet)))
                                  (obs-dom-info->doms
                                   (nth fanout obs-dom-array)))))
                (subsetp (obs-dom-info->doms
                          (nth (lit->var (fanin dir (lookup-id fanout aignet))) obs-dom-array))
                         (cons (fanin (b-not dir) (lookup-id fanout aignet))
                               (obs-dom-info->doms
                                (nth fanout obs-dom-array)))))
       :hints (("goal" :use obs-dom-fanout-ok-implies
                :in-theory (e/d (obs-dom-info-for-child
                                 obs-dom-info-subsetp
                                 obs-dom-info-add cube-contradictionp)
                                (obs-dom-fanout-ok-implies)))))


     (defthm subsetp-remove-equal
       (implies (subsetp x (cons k y))
                (subsetp (remove k x) y))
       :hints(("Goal" :in-theory (enable subsetp remove))))))


  
  (defthm obs-dom-array-implies-path-contains-dominators
    (implies (and (obs-dom-array-correct obs-dom-array aignet)
                  (path-existsp sink path aignet)
                  (not (path-contains-contradictory-siblings sink path aignet))
                  (obs-dom-info->reached (nth sink obs-dom-array))
                  (equal (obs-dom-info->doms (nth sink obs-dom-array)) nil))
             (let ((source (path-endpoint sink path aignet)))
               (and (obs-dom-info->reached (nth source obs-dom-array))
                    (path-contains-and-siblings
                     (obs-dom-info->doms (nth source obs-dom-array))
                     sink path aignet))))
    :hints (("goal" :induct (path-induct-reverse path)
             :in-theory (enable (:i path-induct-reverse))
             :expand ((:with path-contains-contradictory-siblings-in-terms-of-butlast
                       (path-contains-contradictory-siblings sink path aignet))
                      (:with path-contains-and-siblings-in-terms-of-butlast
                       (:free (doms)
                        (path-contains-and-siblings
                         doms sink path aignet)))
                      (:with path-existsp-in-terms-of-butlast
                       (path-existsp sink path aignet))
                      (:with path-endpoint-in-terms-of-butlast
                       (path-endpoint sink path aignet)))))))
                



(defthm toggle-does-not-affect-sink-when-not-reached
  (implies (and (obs-dom-array-correct obs-dom-array aignet)
                (not (obs-dom-info->reached (nth source obs-dom-array)))
                (obs-dom-info->reached (nth sink obs-dom-array))
                (equal (obs-dom-info->doms (nth sink obs-dom-array)) nil))
           (equal (id-eval-toggle sink (cons source toggles) invals regvals aignet)
                  (id-eval-toggle sink toggles invals regvals aignet)))
  :hints (("goal" :use ((:instance obs-dom-array-implies-path-contains-dominators
                         (path (toggle-witness-path sink source toggles invals regvals aignet))))
           :in-theory (disable obs-dom-array-implies-path-contains-dominators))))


(defsection toggle-does-not-affect-output-when-dominator-false
  (local (defthm path-contains-const0-sibling-when-member-and-siblings
           (implies (and (path-contains-and-siblings lits sink path aignet)
                         (lit-listp lits)
                         (member lit lits)
                         (equal (lit-eval-toggle lit toggles invals regvals aignet) 0)
                         (equal (lit-eval-toggle lit (cons source toggles) invals regvals aignet) 0))
                    (path-contains-const0-sibling sink source toggles invals regvals path aignet))
           :hints(("Goal" :in-theory (enable path-contains-and-siblings)))))

  (defthm toggle-does-not-affect-output-when-dominator-false
    (implies (and (obs-dom-array-correct obs-dom-array aignet)
                  (obs-dom-info->reached (nth source obs-dom-array))
                  (member-equal lit (obs-dom-info->doms (nth source obs-dom-array)))
                  (equal (lit-eval-toggle lit toggles invals regvals aignet) 0)
                  (equal (lit-eval-toggle lit (cons source toggles) invals regvals aignet) 0)
                  (obs-dom-info->reached (nth sink obs-dom-array))
                  (equal (obs-dom-info->doms (nth sink obs-dom-array)) nil))
             (equal (id-eval-toggle sink (cons source toggles) invals regvals aignet)
                    (id-eval-toggle sink toggles invals regvals aignet)))
    :hints (("goal" :use ((:instance obs-dom-array-implies-path-contains-dominators
                           (path (toggle-witness-path sink source toggles invals regvals aignet)))
                          (:instance path-contains-const0-sibling-when-member-and-siblings
                           (lits (obs-dom-info->doms (nth source obs-dom-array)))
                           (path (toggle-witness-path sink source toggles invals regvals aignet))))
             :in-theory (disable obs-dom-array-implies-path-contains-dominators
                                 path-contains-const0-sibling-when-member-and-siblings)))))





(define obs-dom-array-collect ((n natp) obs-dom-array)
  :guard (<= n (dominfo-length obs-dom-array))
  :measure (nfix (- (dominfo-length obs-dom-array) (nfix n)))
  (b* (((when (mbe :logic (zp (- (dominfo-length obs-dom-array) (nfix n)))
                   :exec (eql (dominfo-length obs-dom-array) n)))
        nil))
    (cons (get-dominfo n obs-dom-array)
          (obs-dom-array-collect (1+ (lnfix n)) obs-dom-array))))

(define map-len (x)
  (if (atom x)
      nil
    (cons (len (car x))
          (map-len (cdr x)))))

(define frequencies (x acc)
  (if (atom x)
      (fast-alist-free (fast-alist-clean acc))
    (frequencies (cdr x)
                 (hons-acons (car x)
                             (+ 1 (nfix (cdr (hons-get (car x) acc))))
                             acc))))
