; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../wtree/top")
(include-book "../../../scheduler/util/top")
(set-induction-depth-limit 1)

; Sum and Sum-range  ----------------------------------------------------------

; helpers to compute the work completed by a wtree so far.

; compute sum of numbers up to n.
; TODO: rename to sum_of_nats
(define sum ((n natp))
  (b* ((n (nfix n))
       ((if (= n 0)) 0))
      (+ n (sum (1- n)))))

; Compute the sum of integer in the given range.
; (sum-range 0 2) -> 3
; (sum-range 1 2) -> 3
; (sum-range 1 3) -> 6
; (sum-range 5 6) -> 11
(define sum-range ((i natp) (j natp))
  :returns (n natp)
  :measure (acl2-count (- (nfix j) (nfix i)))
  (b* ((i (nfix i))
       (j (nfix j))
       ((if (< j i)) 0)
       ((if (equal i j)) i))
      (+ i (sum-range (+ 1 i) j)))
  ///
    (defcong nat-equiv equal (sum-range i j) 1)
    (defcong nat-equiv equal (sum-range i j) 2)
    
    (defrule sum-range-of-consequitve
      (implies
        (and (natp i) (natp j) (natp n) (<= i j) (< j n))
        (equal (+ (sum-range i j) (sum-range (+ j 1) n))
               (sum-range i n))))
    (defruled sum-range-to-sum
      (implies
        (and (natp i) (natp j) (<= i j))
        (equal (sum-range i j) (- (sum j) (sum (1- i)))))
      :enable sum)
    (defrule sum-range-of-one
      (implies (natp j) (equal (sum-range 1 j) (sum j)))
      :enable (sum sum-range-to-sum))
    (defrule sum-range-of-zero
      (implies (natp j) (equal (sum-range 0 j) (sum j)))
      :enable (sum sum-range-to-sum))
    (defrule sum-range-of-identical
      (implies (natp i) (equal (sum-range i i) i)))
    (defrule sum-range-of-add
      (implies (and (natp i) (natp j) (< i j))
               (equal (+ j (sum-range i (+ -1 j))) (sum-range i j)))
      :enable sum)
    (defrule sum-range-consequitve-2
      (implies
        (and (natp i) (natp j) (natp n) (< i j) (<= j n))
        (equal (+ (sum-range i (+ -1 j)) (sum-range j n)) (sum-range i n)))
      :disable (sum-range sum-range-of-consequitve)
      :use (:instance sum-range-of-consequitve (i i) (j (+ -1 j)) (n n))))

; Wtree Utility ---------------------------------------------------------------

; The children of a node whose messages have no been received yet.
; Remark: In an earlier implementation, instead of ChildHd and ChildTl,
; the last clause of reduce had CPids as a parameter, and then
; matched head and tail of the arguments in the body of the function.
; Now, it has a single pattern [ChildHd | ChildTl] instead of Cpids. The
; function 'remaining-children' creates the would be Cpids corresponding to
; ChildHd and ChildTl, such that it can be used by existing proofs without a
; major change.
(define remaining-children-p ((bind bind-p))
  :returns (r booleanp)
  (b* ((bind (bind-fix bind)))
      (and (omap::assoc 'ChildHd bind)
           (omap::assoc 'ChildTl bind)
           (equal (erl-val-kind (omap::lookup 'ChildTl bind)) :cons)
           t))
  ///
    (defcong bind-equiv equal (remaining-children-p bind) 1))

(define remaining-children ((bind bind-p))
  :guard (remaining-children-p bind)
  :guard-hints (("Goal" :in-theory (enable remaining-children-p)))
  :returns (cpids erl-vlst-p)
  (b* ((bind (bind-fix bind)))
      (cons (erl-val-fix (omap::lookup 'ChildHd bind))
            (erl-val-cons->lst (omap::lookup 'ChildTl bind))))
  ///
    (defcong bind-equiv equal (remaining-children bind) 1)

    (defrule consp-of-remaining-children
      (consp (remaining-children bind)))

    (defrule car-of-remaining-children
      (equal (car (remaining-children bind))
             (erl-val-fix (omap::lookup 'ChildHd (bind-fix bind)))))

    (defrule cdr-of-remaining-children
      (equal (cdr (remaining-children bind))
             (erl-val-cons->lst (omap::lookup 'ChildTl (bind-fix bind))))))

; Check if the parent of a process has not yet received its message.
(define parent-still-waiting-p ((self pid-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
  (b* ((self (pid-fix self))
       (parent (erl-val-fix parent))
       (net (network-fix net))
       ; the root has no parent to wait for it
       ((unless (pid-p parent)) t)
       ((unless (omap::assoc parent net)) nil)
       (pproc (omap::lookup parent net))
       (pbind (erl-state->bind (proc->s pproc)))
       ; the parent cannot terminate until it receives all messages.
       ((if (equal (proc->ps pproc) :terminated)) nil)
       ; ChildHd and ChildTl must be bound, because there should
       ; be at least one more child.
       ((unless (remaining-children-p pbind)) t))
    (consp (member-equal self (remaining-children pbind))))
  ///
    (defcong pid-equiv equal (parent-still-waiting-p a b c) 1)
    (defcong erl-val-equiv equal (parent-still-waiting-p a b c) 2)
    (defcong network-equiv equal (parent-still-waiting-p a b c) 3)
    
    (defrule parent-still-waiting-p-when-not-pid
      (implies
        (not (pid-p (erl-val-fix parent)))
        (parent-still-waiting-p self parent net)))
    
    ; parent-still-waiting-p after a deliver step.
    (defrule parent-still-waiting-p-of-update-deliver
      (implies
        (and
          (network-p net) (network-p (omap::update p proc net))
          (omap::assoc p net)
          ; The binding do not change after delivery.
          (equal (erl-state->bind (proc->s proc))
                 (erl-state->bind (proc->s (omap::lookup p net))))
          ; The process state either did not change,
          ; or it has transitioned to receive from blocked.
          (or (equal (proc->ps proc) (proc->ps (omap::lookup p net)))
              (equal (proc->ps proc) :receive))
          (parent-still-waiting-p self parent net))
        (parent-still-waiting-p self parent (omap::update p proc net)))
      :enable omap::lookup-of-update)

  ; parent-still-waiting-p after a run step.
  (defrule parent-still-waiting-p-of-update-run
    (implies
      (and
        (network-p net) (network-p (omap::update p proc net))
        (not (equal (proc->ps proc) :terminated))
        ; The auxillary variables do not change after a run step.
        (equal (remaining-children (erl-state->bind (proc->s proc)))
               (remaining-children (erl-state->bind (proc->s (omap::lookup p net)))))
        (equal (remaining-children-p (erl-state->bind (proc->s proc)))
               (remaining-children-p (erl-state->bind (proc->s (omap::lookup p net)))))
        (parent-still-waiting-p self parent net))
      (parent-still-waiting-p self parent (omap::update p proc net)))
    :enable omap::lookup-of-update))

; General Utility -------------------------------------------------------------

; TODO: Some of these should move to other files, and some of them might be obselete. 

(defrule commutuativity-of-remove-equal
  (equal (remove-equal a (remove-equal b l))
         (remove-equal b (remove-equal a l))))

(defrule pid-lst-crock
  (implies
    (and (prefixp (rev l2) (rev l1)) (erl-vlst-p l2) (pid-lst-p l1))
    (pid-lst-p l2))
  :use (:instance prefix-of-pid-lst-p (l1 (rev l1)) (l2 (rev l2)))
  :disable prefix-of-pid-lst-p
  :prep-lemmas
    ((defrule prefix-of-pid-lst-p
       (implies
         (and (pid-lst-p l1) (erl-vlst-p l2) (prefixp l2 l1))
         (pid-lst-p l2))
       :enable prefixp)))

(defrule submap-of-update-new-key
  (implies (and (omap::mapp m) (not (omap::assoc k m)))
           (omap::submap m (omap::update k v m)))
  :enable (omap::submap-to-submap-sk omap::submap-sk))

(defrule assoc-of-update-when-assoc
  (implies (omap::assoc p net)
           (iff (omap::assoc x (omap::update p proc net))
                (omap::assoc x net))))

(defrule assoc-of-update
  (omap::assoc k (omap::update k v m)))

(defrule lookup-of-update-new
  (implies (not (equal x k))
           (equal (omap::lookup x (omap::update k v m))
                  (omap::lookup x m)))
  :enable omap::lookup-of-update)

  (defrule lookup-of-update-val
  (equal (omap::lookup k (omap::update k v m)) v)
  :enable omap::lookup-of-update)

(defrule prefixp-of-same
  (prefixp x x)
  :enable prefixp)

(defrule len-of-pid-lst-when-consp
  (implies (and (pid-lst-p x) x) (<= 1 (len x)))
  :rule-classes :linear)

(defrule prefixp-of-rev-of-cdr
  (implies (prefixp (rev l) x) (prefixp (rev (cdr l)) x))
  :use ((:instance prefixp-transitive
          (x (rev (cdr l))) (y (rev l)) (z x)))
  :prep-lemmas
  ((defrule prefixp-of-append
    (prefixp x (append x y)) :enable prefixp)
   (defrule prefixp-transitive
     (implies (and (prefixp x y) (prefixp y z)) (prefixp x z))
     :enable prefixp)
   (defrule prefixp-of-rev-cdr-rev
     (prefixp (rev (cdr l)) (rev l))
     :expand (rev l))))