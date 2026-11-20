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

; receive -> terminated ---------------------------------------------------------

; klst remains unchanged after termination. (This might change at some point)
(local (defrule wtree-bind0-of-same-klst
  (implies
    (and (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind))
    (equal (wtree-bind0 b (proc->klst p))
           (wtree-bind p)))
  :enable wtree-bind))

; The properties that need to hold specifically for the process that ran
; from receive to terminated. 
(local (defruled inv-of-run-receive-to-terminated-self
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
       (r (rightmost-child p net))
       (ri (erl-val-integer->val
             (omap::lookup 'Index (wtree-bind (omap::lookup r net)))))
       (inbox (proc->inbox-new pp)))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps pp) :receive)
      (receiving-proc-p p pp net)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (pid-lst-p children)
      (inbox-contains inbox chd)
      (not (consp ctl))
      (pid-p chd)
      (wf-inbox-p inbox)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid bind)) :pid)
          (equal (omap::lookup 'ParentPid bind) (make-erl-val-atom :val 'none)))
      (omap::assoc r net)
      (leaf-p (omap::lookup r net))
      (<= index ri)
      (equal (+ (erl-val-integer->val (omap::lookup 'LeftTotal bind))
                (erl-val-integer->val (inbox->value inbox chd)))
             (sum-range index ri))
      (not (inbox-without inbox chd)))
    (inv p (omap::update p (proc-receive pp) net))))
  :enable (proc-receive-of-match-last remaining-children-p wtree-fields
           proc->outbox proc->pid omap::from-lists)
  :disable (inv-of-run-to-terminated wtree-bind0-of-reduce-receive-klst-p)
  :use ((:instance inv-of-run-to-terminated
          (proc (proc-receive (omap::lookup p net)))))))

; sent-message-wf still holds for p's children
(local (defrule sent-message-wf-of-receive-to-terminated
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
      (equal (proc->ps proc) :terminated)
      (remaining-children-p bind)
      (not (consp (cdr (remaining-children bind))))
      (pid-p chd)
      (outbox-emptyp (proc->outbox (omap::lookup chd net)))
      (sent-message-wf qp (proc->outbox qp) qparent net))
    (sent-message-wf qp (proc->outbox qp) qparent (omap::update p proc net))))
  :enable (sent-message-wf proc->pid omap::lookup-of-update)))

; parent-still-waiting-p still holds for p's children
(local (defrule parent-still-waiting-p-of-receive-to-terminated
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
      (remaining-children-p bind)
      (not (consp (cdr (remaining-children bind))))
      (equal (proc->ps (omap::lookup chd net)) :terminated)
      (not (equal (proc->ps (omap::lookup pid net)) :terminated))
      (parent-still-waiting-p pid qparent net))
    (parent-still-waiting-p pid qparent (omap::update p proc net))))
  :enable (parent-still-waiting-p omap::lookup-of-update)))

(local (defrule outbox-crock
  (implies (not (proc->outbox p)) (not (erl-state->outbox (proc->s p))))
  :enable proc->outbox))

; receive -> terminated, for all nodes other than p.
(local (defruled inv-of-run-receive-to-terminated-other
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
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
      (pid-lst-p children)
      (inbox-contains inbox chd)
      (not (consp ctl))
      (pid-p chd)
      (wf-inbox-p inbox)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid bind)) :pid)
          (equal (omap::lookup 'ParentPid bind) (make-erl-val-atom :val 'none)))
      (equal (proc->ps (omap::lookup chd net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup chd net)))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p (proc-receive pp) net))))
  :enable (proc-receive-of-match-last remaining-children-p remaining-children
           omap::from-lists wtree-fields)
  :disable wtree-bind0-of-reduce-receive-klst-p))

; receive -> terminated, for every node.
(defruled inv-of-run-receive-to-terminated
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (omap::lookup 'ChildHd bind))
       (ctl (erl-val-cons->lst (omap::lookup 'ChildTl bind)))
       (r (rightmost-child p net))
       (ri (erl-val-integer->val
             (omap::lookup 'Index (wtree-bind (omap::lookup r net)))))
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
      (pid-lst-p children)
      (inbox-contains inbox chd)
      (not (consp ctl))
      (pid-p chd)
      (wf-inbox-p inbox)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid bind)) :pid)
          (equal (omap::lookup 'ParentPid bind) (make-erl-val-atom :val 'none)))
      (omap::assoc r net)
      (leaf-p (omap::lookup r net))
      (<= index ri)
      (equal (+ (erl-val-integer->val (omap::lookup 'LeftTotal bind))
                (erl-val-integer->val (inbox->value inbox chd)))
             (sum-range index ri))
      (not (inbox-without inbox chd))
      (equal (proc->ps (omap::lookup chd net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup chd net)))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p (proc-receive pp) net))))
  :use ((:instance inv-of-run-receive-to-terminated-self)
        (:instance inv-of-run-receive-to-terminated-other)))
