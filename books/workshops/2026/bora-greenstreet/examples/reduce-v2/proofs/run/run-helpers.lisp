; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "proc-receive")

; Helpers for the run proof.

; Hypotheses needed by every run proof. This follows from inv.
(define run-hyps (p proc net)
  :enabled t
  :verify-guards nil
  (and
    (network-p net) (inv-all net)
    (pid-p p) (omap::assoc p net)
    ; the scheduler only runs a runnable process
    (not (equal (proc->ps (omap::lookup p net)) :terminated))
    ; the updated process does not leave the network.
    (proc-p proc)
    (network-p (omap::update p proc net))
    (equal (wtree-fields proc) (wtree-fields (omap::lookup p net)))))

; No delivery during run, so this is easy
(defrule received-messages-wf-of-run
  (implies
    (and (run-hyps p proc net)
         (received-messages-wf inbox cpids net))
    (received-messages-wf inbox cpids (omap::update p proc net)))
  :enable (received-messages-wf omap::lookup-of-update))

; No delivery during run, so this is easy
(defrule sent-message-wf-of-run
  (implies
    (and (run-hyps p proc net)
         (erl-val-p parent) (not (equal parent p))
         (sent-message-wf self outbox parent net))
    (sent-message-wf self outbox parent (omap::update p proc net)))
  :enable (sent-message-wf omap::lookup-of-update))

; No delivery during run, so this is easy
(defrule parent-still-waiting-p-of-run
  (implies
    (and (run-hyps p proc net)
         (erl-val-p parent) (not (equal parent p))
         (parent-still-waiting-p self parent net))
    (parent-still-waiting-p self parent (omap::update p proc net)))
  :enable (parent-still-waiting-p omap::lookup-of-update))

; The children of the process being run will need to satisfy sent-message-wf and
; parent-still-waiting-p afterwards.
(defrule inv-of-run-other
  (implies
    (and (run-hyps p proc net)
         ; pid belons to a different process.
         (not (equal pid p))
         (pid-p pid) (omap::assoc pid net)
         (or (not (equal (proc->ps (omap::lookup pid net)) :terminated))
             (sent-message-wf (omap::lookup pid net)
               (proc->outbox (omap::lookup pid net))
               (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
               (omap::update p proc net)))
         (or (equal (proc->ps (omap::lookup pid net)) :terminated)
             (parent-still-waiting-p pid
               (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
               (omap::update p proc net))))
    (inv pid (omap::update p proc net)))
  :disable (inv-of-inv-all sent-message-wf parent-still-waiting-p)
  :expand ((inv pid (omap::update p proc net))
           (inv pid net))
  :use (:instance inv-of-inv-all))

; Nodes that are not children of the running process are unchanged.
(defrule inv-of-run-non-child
  (implies
    (and (run-hyps p proc net)
         (pid-p pid) (not (equal pid p)) (omap::assoc pid net)
         (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p)))
    (inv pid (omap::update p proc net)))
  :disable inv-of-inv-all
  :expand (inv pid net)
  :use (:instance inv-of-inv-all))

; A proc that is (:blocked) or (:receive) will satisfiy the following if inv holds.
(define receiving-proc-p (p proc net)
  :enabled t
  :verify-guards nil
  (b* ((bind (erl-state->bind (proc->s proc)))
       (wbind (wtree-bind proc))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (cps (remaining-children bind))
       (chd (car cps))
       (cindex (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup chd net))))))
    (and
      (or (equal (proc->ps proc) :receive) (equal (proc->ps proc) :blocked))
      (consp children)
      (not (equal parent p))
      (parent-still-waiting-p p parent net)
      (equal (erl-val-kind (erl-state->in (proc->s proc))) :none)
      (not (omap::assoc 'RightTotal bind))
      (omap::assoc 'ParentPid bind)
      (equal (omap::lookup 'ParentPid bind) parent)
      ; [ChildHd | ChildTl]:]
      (remaining-children-p bind)
      (prefixp (rev cps) (rev children))
      (omap::assoc chd net)
      (not (equal chd p))
      (leaf-p (omap::lookup chd net))
      (< index cindex)
      ; LeftTotal
      (omap::assoc 'LeftTotal bind)
      (equal (erl-val-kind (omap::lookup 'LeftTotal bind)) :integer)
      (equal (erl-val-integer->val (omap::lookup 'LeftTotal bind))
             (sum-range index (1- cindex)))
      (null (proc->outbox proc))
      (equal (erl-state->world (proc->s proc)) (sum-reduce-world))
      (equal (erl-state->module (proc->s proc)) 'local)
      ; inboxes
      (if (equal (proc->ps proc) :blocked)
          (and (null (proc->inbox-new proc))
               (received-messages-wf (proc->inbox-tried proc) cps net)
               (not (inbox-contains (proc->inbox-tried proc) chd)))
        (and (null (proc->inbox-tried proc))
             (received-messages-wf (proc->inbox-new proc) cps net)))
      ; continuations
      (reduce-receive-klst-p (proc->klst proc)
        (omap::from-lists
          (list 'ChildPids 'Parent 'Index)
          (list (make-erl-val-cons :lst children)
                parent
                (make-erl-val-integer :val index))))
      (> (erl-k->fuel (car (proc->klst proc)))
         (+ 100 (* 6 (len cps)))))))

; if receiving-proc-p and run-hyps both hold, then inv holds.
(defrule inv-of-run-to-receiving
  (implies
    (and (run-hyps p proc net)
         (receiving-proc-p p proc net))
    (inv p (omap::update p proc net)))
  :disable inv-of-inv-all
  :expand ((inv p (omap::update p proc net)))
  :use (:instance inv-of-inv-all (pid p)))

; A proc that is (:terminated) will satisfiy the following if inv holds.
(define terminated-proc-p (p proc net)
  :enabled t
  :verify-guards nil
  (b* ((wbind (wtree-bind proc))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (val (erl-state->in (proc->s proc)))
       (cpid (rightmost-child p net))
       (cindex (erl-val-integer->val
                 (omap::lookup 'Index (wtree-bind (omap::lookup cpid net))))))
    (and
      (equal (proc->ps proc) :terminated)
      (equal (erl-val-kind val) :integer)
      (if (consp children)
          (and (omap::assoc cpid net)
               (leaf-p (omap::lookup cpid net))
               (<= index cindex)
               (equal (erl-val-integer->val val) (sum-range index cindex))
               (null (proc->inbox-tried proc))
               (null (proc->inbox-new proc)))
        (equal (erl-val-integer->val val) index))
      ; message is well-formed
      (equal (erl-state->self (proc->s proc)) p)
      (erl-val-p parent)
      (not (equal parent p))
      (parent-still-waiting-p p parent net)
      (equal (proc->outbox proc)
             (if (pid-p parent)
                 (omap::update parent
                   (list (make-erl-val-tuple :lst (list p val)))
                   nil)
               nil)))))

; if terminated-proc-p and run-hyps both hold, then inv holds.
(defrule inv-of-run-to-terminated
  (implies
    (and (run-hyps p proc net)
         (terminated-proc-p p proc net))
    (inv p (omap::update p proc net)))
  :expand ((inv p (omap::update p proc net)))
  :enable (sent-message-wf parent-still-waiting-p proc->pid)
  :disable inv-of-inv-all
  :use (:instance inv-of-inv-all (pid p)))


; TODO: simplify and move
(defruled chd-not-in-ctl
  (b* ((bind (erl-state->bind (proc->s (omap::lookup p net))))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))))
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc p net)
         (pid-lst-p children)
         (prefixp (rev (remaining-children bind)) (rev children)))
    (not (member-equal (omap::lookup 'ChildHd bind)
                       (erl-val-cons->lst (omap::lookup 'ChildTl bind))))))
  :expand ((no-duplicatesp-equal
            (remaining-children (erl-state->bind (proc->s (omap::lookup p net))))))
  :use ((:instance no-duplicatesp-of-check-children
          (pid p)
          (children (erl-val-cons->lst
                      (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))))
        (:instance no-duplicatesp-of-suffix
          (x (remaining-children (erl-state->bind (proc->s (omap::lookup p net)))))
          (y (erl-val-cons->lst
               (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))))))

(defrule inbox-without-of-last-child
  (implies (and (network-p net) (pid-p p)
                (received-messages-wf inbox (list p) net))
           (not (inbox-without inbox p)))
  :use ((:instance received-messages-wf-of-remove
          (cpids (list p)) (pid p))
        (:instance inbox-of-received-messages-wf-of-nil
          (inbox (inbox-without inbox p)))))