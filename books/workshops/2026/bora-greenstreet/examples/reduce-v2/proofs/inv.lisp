; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "util")
(include-book "inv-helpers")

; Invariant for Reduce Correctness --------------------------------------------

; This is what we need to know to show that reduce is correct. It is a lot.
(define inv ((pid pid-p) (net network-p))
  :ignore-ok t
  :returns (r booleanp)
  :guard-hints
    (("Goal" 
      :in-theory (enable omap::from-lists wtree-nodes-are-leaf-or-root
                         reduce-receive-klst-p)
      :use ((:instance wtree-nodes-are-leaf-or-root (net net) (pid pid))
            (:instance wtree-nodes-are-leaf-or-root
              (net net)
              (pid
                (omap::lookup 'childhd
                  (erl-state->bind (proc->s (omap::lookup pid net)))))))))
  (b* ((pid (pid-fix pid))
       (net (network-fix net))
       ((unless (wtree-p net)) nil)
       ((unless (omap::assoc pid net)) nil)
       (proc (omap::lookup pid net))
       (ps (proc->ps proc))
       (bind (erl-state->bind (proc->s proc)))
       (wbind (wtree-bind proc))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (index (erl-val-integer->val (omap::lookup 'Index wbind))))
      (case ps
        (:idle
          ; If the process has not been run yet, it is has not changed
          ; at all since it was spawned. However, it might have received
          ; messages.
          ; - init-proc simulates a proc that has just been spawned,
          ;   having received no messages.
          (b* (; The process has not entered the reduce call, so the
               ; there should be no new bindings yet.
               ((unless (equal bind wbind)) nil)
               (init-proc (make-reduce-proc pid parent children index))
               ((unless (equal (proc->s proc) (proc->s init-proc))) nil)
               ((unless (equal (proc->klst proc) (proc->klst init-proc))) nil)
               ((unless (null (proc->inbox-tried proc))) nil)
               ; nothing has been sent, so the parent has not received anything.
               ((unless (parent-still-waiting-p pid parent net)) nil)
               (inbox (proc->inbox-new proc)))
              (received-messages-wf inbox children net)))
        (:terminated
          (b* ((val (erl-state->in (proc->s proc)))
               ((unless (equal (erl-val-kind val) :integer)) nil)
               (val (erl-val-integer->val val))
               ; If the node has no children, it simply sends its index.
               ((if (null children))
                (and (equal val index)
                     (sent-message-wf proc (proc->outbox proc) parent net)))
               (cpid (rightmost-child pid net))
               
               ; TODO: this can be derived from wtree-p
               ((unless (omap::assoc cpid net)) nil)
               ((unless (leaf-p (omap::lookup cpid net))) nil)

               (cproc (omap::lookup cpid net))
               (cbind (wtree-bind cproc))
               (cindex (erl-val-integer->val (omap::lookup 'Index cbind)))
               ((unless (<= index cindex)) nil))
              (and
                ; the value must be the sum of indices of this branch.
                (equal val (sum-range index cindex))
                ; message sent must be well formed, if any
                (sent-message-wf proc (proc->outbox proc) parent net)
                ; all messages have been received already   
                (null (proc->inbox-tried proc))
                (null (proc->inbox-new proc)))))
        ((:blocked :receive)
          (b* (; if the node has no children, then it should not block
               ; or try to receive.
               ((if (null children)) nil)

               ; nothing has been sent yet, a node sends only when it
               ; terminates, so the parent must not have received.
               ((unless (parent-still-waiting-p pid parent net)) nil)

               ; during receive the latest value is wiped.
               (val (erl-state->in (proc->s proc)))
               ((unless (equal (erl-val-kind val) :none)) nil)

               ; RightTotal should not be bound. This ends up being
               ; a road block otherwise.
               ((if (omap::assoc 'RightTotal bind)) nil)
               
               ; Parent never changes.
               ((unless (omap::assoc 'ParentPid bind)) nil)
               ((unless (equal parent (omap::lookup 'ParentPid bind))) nil)
               
               ; The remaining children [ChildHd | ChildTl] are bound,
               ; and they are a postfix of the original children.
               ((unless (remaining-children-p bind)) nil)
               (cps (remaining-children bind))
               (chd (car cps))
               ((unless (prefixp (rev cps) (rev children))) nil)
              
               ; TODO: This follows from wtree-p
               ((unless (omap::assoc chd net)) nil)

               ; Acquire the index of the ChildHead
               ; we should know from the prefix that chd is a valid pid.
               (chdproc (omap::lookup chd net))
               
               ; TODO: This follows from wtree-p
               ((unless (leaf-p chdproc)) nil)

               (chdbind (wtree-bind chdproc))
               (cindex (erl-val-integer->val (omap::lookup 'Index chdbind)))
               ((unless (< index cindex)) nil)

               ; LeftTotal (a missing key would look like the integer 0)
               ((unless (omap::assoc 'LeftTotal bind)) nil)
               ((unless (equal (erl-val-kind (omap::lookup 'LeftTotal bind)) :integer)) nil)
               (lt (erl-val-integer->val (omap::lookup 'LeftTotal bind)))
               ((unless (equal lt (sum-range index (1- cindex)))) nil)

               ; The outbox must be empty, as the process will only send a
               ; message when it is done computing the sum.
               ((unless (null (proc->outbox proc))) nil)
               ; The parent, if any, must not have received the message yet.
               ; However, this could be a property of the parent.

               ; The world and module do not change
               ((unless (equal (erl-state->world (proc->s proc))
                               (sum-reduce-world))) nil)
               ((unless (equal (erl-state->module (proc->s proc)) 'local)) nil)

               ; :blocked - Inbox-new is empty, else the process would be
               ;   unblocked. Inbox-tried does not contain chd, otherwise the
               ;   process would have continued.
               ; :receive - Inbox-tried is empty, because the process has not
               ;   started attempting to receive yet.
               ; The other inbox contains valid messages.
               ((unless
                  (if (equal ps :blocked)
                      (and (null (proc->inbox-new proc))
                           (received-messages-wf (proc->inbox-tried proc)
                                                 cps net)
                           (not (inbox-contains (proc->inbox-tried proc) chd)))
                    (and (null (proc->inbox-tried proc))
                         (received-messages-wf (proc->inbox-new proc)
                                               cps net)))) nil)

               ; For messages not have yet received;
               ; the sender is either
               ; - not terminated
               ; - or has the message in the outbox
               ; Though I check this on the sender side.
 
               ; Klst is correct
               (klst (proc->klst proc))
               ; TODO: passing rbind may have become unnecessary,
               ;  since the definition of wtree has changed. It does
               ;  not seem to hurt for now.
               (rbind
                (omap::from-lists
                  (list 'ChildPids 'Parent 'Index)
                  (list (make-erl-val-cons :lst children)
                        parent
                        (make-erl-val-integer :val index))))
               ((unless (reduce-receive-klst-p klst rbind)) nil)
               
               ; There must be enough fuel. calls to apply-k use 6 fuel.
               ; Meanwhile, I picked 100 as a minumum because I can.
               ((unless (> (erl-k->fuel (car klst))
                           (+ 100 (* 6 (len cps))))) nil))
             t))))
  ///
    (defcong pid-equiv equal (inv pid net) 1)
    (defcong network-equiv equal (inv pid net) 2)
    
    (defrule wtree-p-of-inv
      (implies (inv pid net) (wtree-p net)))
    
    (defrule integer-value-of-inv-terminated
      (implies
        (and
          (network-p net) (pid-p pid)
          (equal (proc->ps (omap::lookup pid net)) :terminated)
          (inv pid net))
        (equal
          (erl-val-kind
            (erl-state->in (proc->s (omap::lookup pid net))))
          :integer)))

    (defrule parent-still-waiting-p-of-inv
      (implies
        (and
          (network-p net) (pid-p pid)
          (not (equal (proc->ps (omap::lookup pid net)) :terminated))
          (inv pid net))
        (parent-still-waiting-p pid
          (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
          net))))

; The invariant should hold for every pid in the network. 
(define inv-all0 ((net network-p) (net0 network-p))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
       (net0 (network-fix net0))
       ((if (omap::emptyp net)) t))
      (and (inv (omap::head-key net) net0)
           (inv-all0 (omap::tail net) net0)))
  ///
    (defcong network-equiv equal (inv-all0 net net0) 1)
    (defcong network-equiv equal (inv-all0 net net0) 2)

    (defrule inv-of-inv-all0
      (implies
        (and (network-p net) (omap::assoc pid net)
             (inv-all0 net net0))
        (inv pid net0))))

(define inv-all ((net network-p))
  :returns (r booleanp)
  (b* ((net (network-fix net)))
      (inv-all0 net net))
  ///
    (defcong network-equiv equal (inv-all net) 1)

    (defrule inv-of-inv-all
      (implies
        (and (network-p net) (omap::assoc pid net)
             (inv-all net))
        (inv pid net))))