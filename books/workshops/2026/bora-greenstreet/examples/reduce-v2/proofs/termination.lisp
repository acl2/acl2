; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "inv")

; Show that reduce causes no deadlocks.

; Some helpers functions
(local (define node-index (pid net)
  :returns (n natp :rule-classes :type-prescription)
  :verify-guards nil
  (nfix (erl-val-integer->val
          (omap::lookup 'Index (wtree-bind (omap::lookup pid net)))))))

(local (define max-index ((net network-p))
  :returns (n natp :rule-classes :type-prescription)
  :measure (acl2-count (network-fix net))
  :verify-guards nil
  (b* ((net (network-fix net))
       ((if (omap::emptyp net)) 0))
      (max (nfix (erl-val-integer->val
                   (omap::lookup 'Index
                     (wtree-bind (omap::head-val net)))))
           (max-index (omap::tail net))))
  ///
    (defcong network-equiv equal (max-index net) 1)
    (defrule node-index-<=-max-index
      (implies
        (and (network-p net) (pid-p pid) (omap::assoc pid net))
        (<= (node-index pid net) (max-index net)))
      :rule-classes :linear
      :enable (node-index omap::lookup))))

; Some helper rules
(local (defrule ps-of-terminated-network
  (implies
    (and (network-p net) (pid-p pid)
         (omap::assoc pid net) (terminated? net))
    (and (not (equal (proc->ps (omap::lookup pid net)) :idle))
         (not (equal (proc->ps (omap::lookup pid net)) :receive))
         (not (proc->outbox (omap::lookup pid net)))))
  :enable (terminated? omap::lookup)))

(local (defrule member-equal-of-prefixp
  (implies (and (prefixp x y) (member-equal e x))
           (member-equal e y))
  :enable prefixp))

(local (defrule member-equal-of-rev-prefixp
  (implies (and (prefixp (rev l2) (rev l1)) (member-equal e l2))
           (member-equal e l1))
  :use (:instance member-equal-of-prefixp
          (x (rev l2)) (y (rev l1)))))

(local (defruled parent-of-member-of-check-children
  (implies
    (and (network-p net) (pid-p pid) (pid-lst-p children)
         (member-equal cpid children)
         (check-children pid children net))
    (and (omap::assoc cpid net)
         (leaf-p (omap::lookup cpid net))
         (equal (omap::lookup 'Parent
                  (wtree-bind (omap::lookup cpid net)))
                pid)))
  :enable check-children))

; BOZO: another brute-force solution
(local (defruled inv-blocked-node-props
  (implies
    (and
      (inv pid net)
      (network-p net) (pid-p pid) (omap::assoc pid net)
      (or (leaf-p (omap::lookup pid net))
          (root-p (omap::lookup pid net)))
      (equal (proc->ps (omap::lookup pid net)) :blocked))
    (and
      (remaining-children-p
        (erl-state->bind (proc->s (omap::lookup pid net))))
      (erl-val-p
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (omap::lookup pid net)))))
      (prefixp
        (rev (remaining-children
               (erl-state->bind (proc->s (omap::lookup pid net)))))
        (rev (erl-val-cons->lst
               (omap::lookup 'ChildPids
                 (wtree-bind (omap::lookup pid net))))))
      (omap::assoc
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (omap::lookup pid net))))
        net)
      (leaf-p
        (omap::lookup
          (omap::lookup 'ChildHd
            (erl-state->bind (proc->s (omap::lookup pid net))))
          net))
      (< (erl-val-integer->val
           (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
         (erl-val-integer->val
           (omap::lookup 'Index
             (wtree-bind
               (omap::lookup
                 (omap::lookup 'ChildHd
                   (erl-state->bind (proc->s (omap::lookup pid net))))
                 net)))))
      (null (proc->inbox-new (omap::lookup pid net)))
      (not (inbox-contains
             (proc->inbox-tried (omap::lookup pid net))
             (omap::lookup 'ChildHd
               (erl-state->bind (proc->s (omap::lookup pid net))))))))
  :enable remaining-children-p
  :expand (inv pid net)))

; BOZO: another brute-force solution
(local (defruled inv-blocked-node-child-props
  (implies
    (and
      (inv-all net) (network-p net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps (omap::lookup pid net)) :blocked))
    (and
      (pid-p
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (omap::lookup pid net)))))
      (omap::assoc
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (omap::lookup pid net))))
        net)
      (leaf-p
        (omap::lookup
          (omap::lookup 'ChildHd
            (erl-state->bind (proc->s (omap::lookup pid net))))
          net))
      (equal
        (omap::lookup 'Parent
          (wtree-bind
            (omap::lookup
              (omap::lookup 'ChildHd
                (erl-state->bind (proc->s (omap::lookup pid net))))
              net)))
        pid)
      (remaining-children-p
        (erl-state->bind (proc->s (omap::lookup pid net))))
      (member-equal
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (omap::lookup pid net))))
        (remaining-children
          (erl-state->bind (proc->s (omap::lookup pid net)))))
      (null (proc->inbox-new (omap::lookup pid net)))
      (not (inbox-contains
             (proc->inbox-tried (omap::lookup pid net))
             (omap::lookup 'ChildHd
               (erl-state->bind (proc->s (omap::lookup pid net))))))
      (< (node-index pid net)
         (node-index
           (omap::lookup 'ChildHd
             (erl-state->bind (proc->s (omap::lookup pid net))))
           net))))
  :enable node-index
  :disable wtree-p-of-inv
  :use
    ((:instance inv-blocked-node-props)
     (:instance wtree-nodes-are-leaf-or-root)
     (:instance wtree-p-of-inv)
     (:instance parent-of-member-of-check-children
       (cpid (omap::lookup 'ChildHd
               (erl-state->bind (proc->s (omap::lookup pid net)))))
       (children (erl-val-cons->lst
                   (omap::lookup 'ChildPids
                     (wtree-bind (omap::lookup pid net)))))))))

(local (defrule inv-terminated-node-sent-message-wf
  (implies
    (and
      (network-p net) (pid-p pid) (omap::assoc pid net)
      (or (leaf-p (omap::lookup pid net))
          (root-p (omap::lookup pid net)))
      (equal (proc->ps (omap::lookup pid net)) :terminated)
      (inv pid net))
    (sent-message-wf
      (omap::lookup pid net)
      (proc->outbox (omap::lookup pid net))
      (omap::lookup 'Parent 
        (wtree-bind (omap::lookup pid net)))
      net))
  :expand (inv pid net)))

; If a process is blocked, ChildHd should not have terminated yet.
(local (defrule blocked-child-not-terminated
  (implies
    (and
      (network-p net) (pid-p pid) (pid-p chd)
      (omap::assoc pid net) (omap::assoc chd net)
      (equal (proc->ps (omap::lookup pid net)) :blocked)
      (equal (omap::lookup 'Parent
               (wtree-bind (omap::lookup chd net))) pid)
      (remaining-children-p
        (erl-state->bind (proc->s (omap::lookup pid net))))
      (member-equal chd
        (remaining-children
          (erl-state->bind (proc->s (omap::lookup pid net)))))
      (null (proc->inbox-new (omap::lookup pid net)))
      (not (inbox-contains
            (proc->inbox-tried (omap::lookup pid net))
            chd))
      (not (proc->outbox (omap::lookup chd net)))
      (or (leaf-p (omap::lookup chd net))
          (root-p (omap::lookup chd net)))
      (inv chd net))
    (not (equal (proc->ps (omap::lookup chd net)) :terminated)))
  :enable sent-message-wf
  :expand (inbox-contains nil chd)
  :use (:instance inv-terminated-node-sent-message-wf (pid chd))))

(local (defruled proc-state-cases
  (implies (proc-p p)
    (or (equal (proc->ps p) :idle)
        (equal (proc->ps p) :terminated)
        (equal (proc->ps p) :receive)
        (equal (proc->ps p) :blocked)))
  :enable proc-state-p))

; If the network is terminated, a blocked worker's child must also be blocked.
(local (defrule blocked-node-has-blocked-child-when-terminated
  (implies
    (and
      (network-p net) (inv-all net) (terminated? net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps (omap::lookup pid net)) :blocked))
    (and
      (pid-p
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (omap::lookup pid net)))))
      (omap::assoc
        (omap::lookup 'ChildHd
          (erl-state->bind (proc->s (omap::lookup pid net))))
        net)
      (equal
        (proc->ps
          (omap::lookup
            (omap::lookup 'ChildHd
              (erl-state->bind (proc->s (omap::lookup pid net))))
            net))
        :blocked)
      (< (node-index pid net)
         (node-index
           (omap::lookup 'ChildHd
             (erl-state->bind (proc->s (omap::lookup pid net))))
           net))))
  :use ((:instance inv-blocked-node-child-props)
        (:instance proc-state-cases
          (p (omap::lookup
               (omap::lookup 'ChildHd
                 (erl-state->bind (proc->s (omap::lookup pid net))))
               net))))))

(local (defrule no-blocked-node-when-terminated
  (implies
    (and
      (network-p net) (inv-all net) (terminated? net)
      (pid-p pid) (omap::assoc pid net))
    (not (equal (proc->ps (omap::lookup pid net)) :blocked)))
  :induct (index-induct pid net)
  :prep-lemmas
    ((define index-induct (pid net)
      :enabled t
      :irrelevant-formals-ok t
      :ignore-ok t
      :verify-guards nil
      :measure (nfix (- (max-index net) (node-index pid net)))
      (b* ((chd (omap::lookup 'ChildHd
                  (erl-state->bind (proc->s (omap::lookup pid net)))))
          ((unless (pid-p chd)) net)
          ((unless (< (node-index pid net) (node-index chd net))) net)
          ((unless (<= (node-index chd net) (max-index net))) net))
          (index-induct chd net))))))

; Finally:
(defrule terminated-of-inv
  (implies
    (and
      (inv-all net) (terminated? net) (network-p net)
      (pid-p pid) (omap::assoc pid net))
    (equal (proc->ps (omap::lookup pid net)) :terminated))
  :use (:instance proc-state-cases (p (omap::lookup pid net))))
