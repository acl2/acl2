; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "run-helpers")

; receive -> receive ------------------------------------------------------------

; proc-receive-of-match grows the klst.
(local (defrule reduce-receive-klst-p-of-receive-step
  (implies
    (and (reduce-receive-klst-p klst bind) (> (erl-k->fuel (car klst)) 104))
    (reduce-receive-klst-p
      (list* (erl-k (+ -4 (erl-k->fuel (car klst))) (erl-k->kont (car klst)))
             (erl-k (+ -4 (erl-k->fuel (car klst))) '(:exprs nil))
             (erl-k (+ -3 (erl-k->fuel (car klst)))
                    (kont-function-return b 'local))
             (erl-k (+ -1 (erl-k->fuel (car klst))) '(:exprs nil))
             (cdr klst))
      bind))
  :disable reduce-receive-klst-p
  :use reduce-receive-klst-p-of-append))

; wtree-bind remains unchanged, regardless of the size of the call stack.
(local (defrule wtree-bind0-of-receive-step
  (implies
    (and (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind))
    (equal (wtree-bind0 b (list* k1 k2 k3 k4 (cdr (proc->klst p))))
           (wtree-bind p)))
  :enable wtree-bind
  :use ((:instance consp-cdr-of-reduce-receive-klst-p (klst (proc->klst p)))
        (:instance wtree-bind0-of-reduce-receive-klst-p
          (bind b) (klst (proc->klst p)))
        (:instance wtree-bind0-of-cons
          (a (car (proc->klst p))) (x (cdr (proc->klst p)))))
  :prep-lemmas
    ((defrule wtree-bind0-of-cons
       (implies (consp x) (equal (wtree-bind0 b (cons a x)) (wtree-bind0 b x)))
       :enable wtree-bind0)
     (defruled consp-cdr-of-reduce-receive-klst-p
       (implies (reduce-receive-klst-p klst rbind)
                (consp (cdr klst)))
       :enable reduce-receive-klst-p))))

(local (defrule remove-equal-of-non-member
  (implies (and (not (member-equal a x)) (true-listp x))
           (equal (remove-equal a x) x))))

; The properties that need to hold specifically for the process that ran
; from receive to receive.
(local (defruled inv-of-run-receive-to-receive-self
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
       (c2 (car ctl))
       (inbox (proc->inbox-new pp)))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps pp) :receive)
      (receiving-proc-p p pp net)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (natp index)
      (pid-lst-p children)
      (inbox-contains inbox chd)
      (consp ctl)
      (pid-p chd)
      (pid-lst-p ctl)
      (wf-inbox-p inbox)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid bind)) :pid)
          (equal (omap::lookup 'ParentPid bind) (make-erl-val-atom :val 'none)))
      (not (member-equal chd ctl))
      (omap::assoc c2 net)
      (leaf-p (omap::lookup c2 net))
      (not (equal c2 p))
      (< index (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup c2 net)))))
      (equal (+ (erl-val-integer->val (omap::lookup 'LeftTotal bind))
                (erl-val-integer->val (inbox->value inbox chd)))
             (sum-range index
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind (omap::lookup c2 net))))))))
    (inv p (omap::update p (proc-receive pp) net))))
  :enable (proc-receive-of-match remaining-children-p remaining-children
           wtree-fields omap::from-lists proc->outbox)
  :expand ((rev (erl-val-cons->lst
                 (omap::lookup 'ChildTl
                   (erl-state->bind (proc->s (omap::lookup p net)))))))
  :disable inv-of-run-to-receiving
  :use ((:instance inv-of-run-to-receiving
          (proc (proc-receive (omap::lookup p net))))
        (:instance prefixp-of-rev-of-cdr
          (l (remaining-children
               (erl-state->bind (proc->s (omap::lookup p net)))))
          (x (rev (erl-val-cons->lst
                    (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))))
        (:instance received-messages-wf-of-remove
          (inbox (proc->inbox-new (omap::lookup p net)))
          (cpids (remaining-children
                   (erl-state->bind (proc->s (omap::lookup p net)))))
          (pid (omap::lookup 'ChildHd
                 (erl-state->bind (proc->s (omap::lookup p net)))))))))

; sent-message-wf still holds for the sender of the received message 
(local (defrule sent-message-wf-of-receive-match
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (chd (car (remaining-children bind)))
       (qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp))))
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (pid-p pid) (not (equal pid p))
      (omap::assoc pid net) (omap::assoc p net)
      (erl-val-p qparent)
      (equal (proc->ps pp) :receive)
      (equal (proc->ps proc) :receive)
      (remaining-children-p bind)
      (remaining-children-p (erl-state->bind (proc->s proc)))
      (equal (remaining-children (erl-state->bind (proc->s proc)))
             (cdr (remaining-children bind)))
      (not (member-equal chd (cdr (remaining-children bind))))
      (pid-p chd)
      (equal (proc->inbox-new proc) (inbox-without (proc->inbox-new pp) chd))
      (outbox-emptyp (proc->outbox (omap::lookup chd net)))
      (sent-message-wf qp (proc->outbox qp) qparent net))
    (sent-message-wf qp (proc->outbox qp) qparent (omap::update p proc net))))
  :cases ((equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))
  :enable (sent-message-wf proc->pid omap::lookup-of-update)
  :use (:instance inbox-without-of-neq-pid
         (inbox (proc->inbox-new (omap::lookup p net)))
         (x (car (remaining-children
                   (erl-state->bind (proc->s (omap::lookup p net)))))))))

; parent-still-waiting-p still holds for the sender of the received message 
(local (defrule parent-still-waiting-p-of-receive-match
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (chd (car (remaining-children bind)))
       (qparent (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))))
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (pid-p pid) (not (equal pid p))
      (omap::assoc pid net) (omap::assoc p net)
      (erl-val-p qparent)
      (equal (proc->ps proc) :receive)
      (remaining-children-p bind)
      (remaining-children-p (erl-state->bind (proc->s proc)))
      (equal (remaining-children (erl-state->bind (proc->s proc)))
             (cdr (remaining-children bind)))
      (equal (proc->ps (omap::lookup chd net)) :terminated)
      (not (equal (proc->ps (omap::lookup pid net)) :terminated))
      (parent-still-waiting-p pid qparent net))
    (parent-still-waiting-p pid qparent (omap::update p proc net))))
  :cases ((equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))
  :enable (parent-still-waiting-p omap::lookup-of-update)))

; receive -> receive, for every other node.
(local (defruled inv-of-run-receive-to-receive-other
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
       (c2 (car ctl))
       (inbox (proc->inbox-new pp))
       (qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (pid-p pid) (not (equal pid p)) (omap::assoc pid net)
      (equal (proc->ps pp) :receive)
      (receiving-proc-p p pp net)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (natp index)
      (pid-lst-p children)
      (inbox-contains inbox chd)
      (consp ctl)
      (pid-p chd)
      (pid-lst-p ctl)
      (wf-inbox-p inbox)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid bind)) :pid)
          (equal (omap::lookup 'ParentPid bind) (make-erl-val-atom :val 'none)))
      (not (member-equal chd ctl))
      (equal (proc->ps (omap::lookup chd net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup chd net)))
      (omap::assoc c2 net)
      (leaf-p (omap::lookup c2 net))
      (not (equal c2 p))
      (< index (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup c2 net)))))
      (equal (+ (erl-val-integer->val (omap::lookup 'LeftTotal bind))
                (erl-val-integer->val (inbox->value inbox chd)))
             (sum-range index
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind (omap::lookup c2 net)))))))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p (proc-receive pp) net))))
  :enable (proc-receive-of-match remaining-children-p remaining-children
           omap::from-lists wtree-fields)))

; receive -> receive, for every node.
(defruled inv-of-run-receive-to-receive
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
       (c2 (car ctl))
       (inbox (proc->inbox-new pp))
       (qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps pp) :receive)
      (receiving-proc-p p pp net)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (natp index)
      (pid-lst-p children)
      (inbox-contains inbox chd)
      (consp ctl)
      (pid-p chd)
      (pid-lst-p ctl)
      (wf-inbox-p inbox)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid bind)) :pid)
          (equal (omap::lookup 'ParentPid bind) (make-erl-val-atom :val 'none)))
      (not (member-equal chd ctl))
      (equal (proc->ps (omap::lookup chd net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup chd net)))
      (omap::assoc c2 net)
      (leaf-p (omap::lookup c2 net))
      (not (equal c2 p))
      (< index (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup c2 net)))))
      (equal (+ (erl-val-integer->val (omap::lookup 'LeftTotal bind))
                (erl-val-integer->val (inbox->value inbox chd)))
             (sum-range index
               (1- (erl-val-integer->val
                     (omap::lookup 'Index
                       (wtree-bind (omap::lookup c2 net)))))))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p (proc-receive pp) net))))
  :cases ((equal pid p))
  :use ((:instance inv-of-run-receive-to-receive-self)
        (:instance inv-of-run-receive-to-receive-other)))
