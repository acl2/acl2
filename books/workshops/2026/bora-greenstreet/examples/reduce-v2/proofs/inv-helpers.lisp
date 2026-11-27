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

(set-induction-depth-limit 1)

; Helpers for the reduce invariant.

; Received Messages Well Formed -----------------------------------------------

; forall messages in inbox
; the sender exists in cpids and net,
; the sender is terminated and has drained its outbox,
; the received message has the same value as the terminated process' value,
; no two messages have the same sender
(define received-messages-wf ((inbox erl-vlst-p) (cpids erl-vlst-p) (net network-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       (cpids (erl-vlst-fix cpids))
       (net (network-fix net))
       ((unless inbox) t)
       (m (car inbox))
       ((unless (equal (erl-val-kind m) :tuple)) nil)
       (lst (erl-val-tuple->lst m))
       ; The message is in the form {sender, value}.
       ((unless (equal (len lst) 2)) nil)
       (sender (car lst))
       (val (cadr lst))
       ; the sender exists
       ((unless (member-equal sender cpids)) nil)
       ((unless (omap::assoc sender net)) nil)
       (sproc (omap::lookup sender net))
       ; the sender must have terminated
       ((unless (equal (proc->ps sproc) :terminated)) nil)
       ; and the sender must have already sent its message,
       ; else there would be duplicates.
       ((unless (outbox-emptyp (proc->outbox sproc))) nil)
       ; the sender must have sent its own value
       ; which will be equal to its sum-range.
       (sval (erl-state->in (proc->s sproc)))
       ((unless (equal sval val)) nil)
       ; the value is an integer
       ((unless (equal (erl-val-kind val) :integer)) nil))
      ; Ensure that no two messages have arrived from the same sender.
      (received-messages-wf (cdr inbox) (remove-equal sender cpids) net))
  ///
    (defcong erl-vlst-equiv equal (received-messages-wf x y z) 1
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x-equiv y z)))))
    (defcong erl-vlst-equiv equal (received-messages-wf x y z) 2
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x y-equiv z)))))
    (defcong network-equiv equal (received-messages-wf x y z) 3
      :hints (("Goal" :expand ((received-messages-wf x y z)
                               (received-messages-wf x y z-equiv)))))
    
    (defrule received-messages-wf-of-nil
      (received-messages-wf nil nil net))

    (defrule inbox-of-received-messages-wf-of-nil
      (implies
        (and (erl-vlst-p inbox) (received-messages-wf inbox nil net))
        (not inbox))
      :rule-classes :forward-chaining)

    ; Removing a message from the inbox maintains the invariant.
    (defrule received-messages-wf-of-remove
      (implies
        (and (network-p net) (erl-vlst-p cpids) (pid-p pid)
             (received-messages-wf inbox cpids net))
        (received-messages-wf (inbox-without inbox pid)
                              (remove-equal pid cpids) net))
      :enable inbox-without)
    
    ; The inbox cannot contain a message that has not yet been received.
    (defrule inbox-contains-of-received-messages-wf-1
      (implies
        (and
          (network-p net) (omap::assoc sender net)
          (not (outbox-emptyp (proc->outbox (omap::lookup sender net))))
          (received-messages-wf inbox cpids net))
        (not (inbox-contains inbox sender)))
      :enable inbox-contains)
    
    ; If the inbox contains a message, the well-formedness properties
    ; are the follwing:
    (defrule inbox-contains-of-received-messages-wf-2
      (implies
        (and (network-p net) (pid-p pid)
             (received-messages-wf inbox cpids net)
             (inbox-contains inbox pid))
        (and (omap::assoc pid net)
             (equal (proc->ps (omap::lookup pid net)) :terminated)
             (outbox-emptyp (proc->outbox (omap::lookup pid net)))
             (equal (inbox->value inbox pid)
                    (erl-state->in (proc->s (omap::lookup pid net))))))
      :enable (inbox->value inbox-contains))
    
    ; updating the network with a non-terminated process has no
    ; effect in received messages since in this implementation, only
    ; terminating processes send messages.
    (defrule received-messages-wf-of-update-of-non-terminated
      (implies
        (and
          (network-p net) (network-p (omap::update p proc net))
          (omap::assoc p net)
          (not (equal (proc->ps (omap::lookup p net)) :terminated))
          (received-messages-wf inbox cpids net))
        (received-messages-wf inbox cpids (omap::update p proc net)))
      :enable omap::lookup-of-update))

; Sent Messages Well Formed ---------------------------------------------------

; The sender counterpart of received-messages-wf
; - the root always has an empty outbox.
; - if the outbox holds a message for the parent, it is a single message:
;   {self, value}
; - The parent has not terminated yet, or removed this pid from the remaining children.
; - otherwise the outbox is empty and the message has reached the parent:
;   it is in the parent's inbox-new (or inbox-tried, when :blocked), or the
;   parent has already processed it, or the parent has terminated.
(define sent-message-wf ((self proc-p) (outbox outbox-p) (parent erl-val-p) (net network-p))
  :returns (r booleanp)
  (b* ((self (proc-fix self))
       (outbox (outbox-fix outbox))
       (parent (erl-val-fix parent))
       (net (network-fix net)) 
       ; the root does not send messages
       ((unless (pid-p parent)) (omap::emptyp outbox))
       ; the parent exists, though we already know this when calling this helper.
       ((unless (omap::assoc parent net)) nil)
       (pproc (omap::lookup parent net))
       (ps (proc->ps pproc))
       (pbind (erl-state->bind (proc->s pproc)))
       ; Check if the message has been received and processed
       ; by the parent.
       (received
         (and (remaining-children-p pbind)
              (not (member-equal
                    (proc->pid self)
                    (remaining-children pbind)))))
       (val (erl-state->in (proc->s self))))
      (if (not (and (omap::assoc parent outbox) (omap::lookup parent outbox)))
          ; If there is no message for the parent, then
          (and
           ; all messages must have been sent, and
           (outbox-emptyp outbox)
           (case ps
            ; if the parent has terminated, we are done.
            (:terminated t)
            ; if the parent is idle, the message must be in
            ; the correct inbox (new).
            (:idle
              (inbox-contains (proc->inbox-new pproc) (proc->pid self)))
            ; if the parent is blocked, then
            (:blocked
              ; either the message is in one of the inboxes,
              ; or it was already received and processed.
              (or (inbox-contains (proc->inbox-new pproc) (proc->pid self))
                  (inbox-contains (proc->inbox-tried pproc) (proc->pid self))
                  received))
            ; if the parent is receiving, the same conditions as blocked hold,
            ; execpt that the message must not have been tried yet.
            (:receive
              (or (inbox-contains (proc->inbox-new pproc) (proc->pid self))
                  received))))
          ; If there is a message for the parent, then
          (b* ((ms (omap::lookup parent outbox))
               ; the parent should not have terminated yet
               ((if (equal ps :terminated)) nil)
               ; the parent obviously should not have received the message yet,
               ; as it is not sent yet. 
               ((if received) nil)
               ; there must be only one message, since this implementation
               ; only sends one.
               ((unless (and ms (not (cdr ms)))) nil)
               ((unless (omap::emptyp (omap::tail outbox))) nil)
               (m (car ms))
               ; the message should be in form: {sender, value}
               ((unless (equal (erl-val-kind m) :tuple)) nil)
               (lst (erl-val-tuple->lst m))
               ((unless (equal (len lst) 2)) nil)
               ((unless (equal (car lst) (proc->pid self))) nil)
               ((unless (equal (cadr lst) val)) nil))
              t)))
  ///
    (defcong proc-equiv equal (sent-message-wf a b c d) 1)
    (defcong outbox-equiv equal (sent-message-wf a b c d) 2)
    (defcong erl-val-equiv equal (sent-message-wf a b c d) 3)
    (defcong network-equiv equal (sent-message-wf a b c d) 4)
    
    ; The seneder is well-formed, if its parent has the message in its inbox-new,
    ; and its outbox is empty.
    (defrule sent-message-wf-when-parent-has-message
      (implies
        (and
          (network-p net) (outbox-p outbox)
          (outbox-emptyp outbox)
          (omap::assoc parent net)
          (inbox-contains (proc->inbox-new (omap::lookup parent net)) (proc->pid self)))
        (sent-message-wf self outbox parent net))))

; Klst Well Formed ------------------------------------------------------------

; Continuation after the receive
(defconst *reduce-receive-clauses*
  '(((cases (:tuple (:cons (:var ChildHd) (:cons (:var RightTotal) (:nil)))))
     (guards)
     (body
      (:call sum_reduce
        (:cons (:var ParentPid)
          (:cons (:var ChildTl)
              (:cons (:binop + (:var LeftTotal) (:var RightTotal)) (:nil)))))))))

; TODO: Here is another consequence of not having tail-call elimination.
; As a worker node calls reduce again and again, it will accumluate a list
; of continuations where every three continuations in a row are:
; 1- (:exprs nil), remaining form the body of the matched receive clauses
; 2- (:exprs nil), remaining from the body of reduce function clauses
; 3- (:function-return ..), the return from the call to reduce
; As a temporary solution, the following predicate defines such lists of
; continuations produced by calls to reduce.
(define reduce-klst-lst-p ((klst erl-klst-p) (bind bind-p))
  :returns (r booleanp)
  :measure (len (erl-klst-fix klst))
  (b* ((klst (erl-klst-fix klst))
       (bind (bind-fix bind))
       ((unless (<= 3 (len klst))) nil)
       (k1 (car klst))
       (k2 (cadr klst))
       (k3 (caddr klst))
       ((unless (> (erl-k->fuel k1) 100)) nil)
       ((unless (> (erl-k->fuel k2) 100)) nil)
       ((unless (> (erl-k->fuel k3) 100)) nil)
       ((unless (equal (erl-k->kont k1) (make-kont-exprs :exprs nil))) nil)
       ((unless (equal (erl-k->kont k2) (make-kont-exprs :exprs nil))) nil)
       ((unless (equal (kont-kind (erl-k->kont k3)) :function-return)) nil)
       ((unless (equal (kont-function-return->module (erl-k->kont k3)) 'local)) nil)
       ; The last bindings is the one the process was spawned with.
       ((unless (cdddr klst))
        (equal (kont-function-return->bind (erl-k->kont k3)) bind)))
      (reduce-klst-lst-p (cdddr klst) bind))
  ///
    (defcong erl-klst-equiv equal (reduce-klst-lst-p klst bind) 1)
    (defcong bind-equiv equal (reduce-klst-lst-p klst bind) 2))

(local (defrule last-of-reduce-klst-lst-p
  (implies
    (reduce-klst-lst-p klst bind)
    (and
      (equal (kont-kind (erl-k->kont (car (last (erl-klst-fix klst)))))
             :function-return)
      (equal (kont-function-return->bind (erl-k->kont (car (last (erl-klst-fix klst)))))
             (bind-fix bind))))
  :enable reduce-klst-lst-p))

; Check if the klst of a process that is awaiting to receive is well fromed.
; TODO: Exactly the same as above, but with an extra check on the first continuation.
;       These two can easily be refactored.
(define reduce-receive-klst-p ((klst erl-klst-p) (bind bind-p))
  :returns (r booleanp)
  (b* ((klst (erl-klst-fix klst))
       (bind (bind-fix bind))
       ((unless (<= 3 (len klst))) nil)
       (k1 (car klst))
       (k2 (cadr klst))
       (k3 (caddr klst))
       ; There must be enough fuel, let's overshoot and say at least 100.
       ((unless (> (erl-k->fuel k1) 100)) nil)
       ((unless (> (erl-k->fuel k2) 100)) nil)
       ((unless (> (erl-k->fuel k3) 100)) nil)
       ; The three continuations at the head must be the following:
       (kont1 (erl-k->kont k1))
       (kont2 (erl-k->kont k2))
       (kont3 (erl-k->kont k3))
       ((unless
        (equal kont1 (make-kont-receive :clauses *reduce-receive-clauses*)))
        nil)
       ((unless (equal kont2 (make-kont-exprs :exprs nil))) nil)
       ((unless (equal (kont-kind kont3) :function-return)) nil)
       ((unless (equal (kont-function-return->module kont3) 'local)) nil)
       ; Ensure that the auxillary varaibles have not changed.
       ((unless (cdddr klst))
        (equal (kont-function-return->bind kont3) bind)))
      ; If there are more continuations, then they must be call stacks
      ; of previous calls to reduce.
      (reduce-klst-lst-p (cdddr klst) bind))
  ///
    (defcong erl-klst-equiv equal (reduce-receive-klst-p klst bind) 1)
    (defcong bind-equiv equal (reduce-receive-klst-p klst bind) 2)

    (defrule wtree-bind0-of-reduce-receive-klst-p
      (implies (reduce-receive-klst-p klst rbind)
               (equal (wtree-bind0 bind klst) (bind-fix rbind)))
      :enable wtree-bind0)
    
    (defruled normalize-reduce-receive-klst-p
      (implies
        (reduce-receive-klst-p (proc->klst p) bind)
        (reduce-receive-klst-p (proc->klst p) (wtree-bind p)))
      :enable wtree-bind
      :disable reduce-receive-klst-p)
      )

; This is how the call stack grows, when apply-k returns.
(defrule reduce-receive-klst-p-of-append
  (implies
    (and
      (reduce-receive-klst-p klst bind) (> (erl-k->fuel (car klst)) 104))
    (reduce-receive-klst-p
      (append
        (list (erl-k (- (erl-k->fuel (car klst)) 4) (erl-k->kont (car klst)))
              (erl-k (- (erl-k->fuel (car klst)) 4)
                     (make-kont-exprs :exprs nil))
              (erl-k (- (erl-k->fuel (car klst)) 3)
                     (make-kont-function-return :bind b :module 'local))
              (erl-k (- (erl-k->fuel (car klst)) 1)
                     (make-kont-exprs :exprs nil)))
        (cdr klst))
      bind))
  :enable (reduce-receive-klst-p reduce-klst-lst-p))

; Inbox Well-Formed ----------------------------------------------------------------

; An inbox is well formed if every message is of the form {pid, val}.
(define wf-inbox-p ((inbox erl-vlst-p))
  :returns (r booleanp)
  :measure (acl2-count (erl-vlst-fix inbox))
  (b* ((inbox (erl-vlst-fix inbox))
       ((unless inbox) t)
       (m (car inbox))
       ((unless (equal (erl-val-kind m) :tuple)) nil)
       ((unless (equal (len (erl-val-tuple->lst m)) 2)) nil)
       ((unless (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer))
        nil))
      (wf-inbox-p (cdr inbox)))
  ///
    (defcong erl-vlst-equiv equal (wf-inbox-p inbox) 1
      :hints (("Goal" :expand ((wf-inbox-p inbox)
                               (wf-inbox-p inbox-equiv)))))

    (defrule wf-inbox-p-of-received-messages-wf
      (implies (received-messages-wf inbox cpids net)
               (wf-inbox-p inbox))
      :enable received-messages-wf)

    (defrule wf-inbox-p-of-car
      (implies
        (and (wf-inbox-p inbox) (erl-vlst-p inbox) (consp inbox))
        (and (erl-val-p (car inbox))
             (equal (erl-val-kind (car inbox)) :tuple)
             (equal (len (erl-val-tuple->lst (car inbox))) 2)
             (equal (erl-val-kind (cadr (erl-val-tuple->lst (car inbox))))
                    :integer))))

    (defrule wf-inbox-p-of-cdr
      (implies (and (wf-inbox-p inbox) (erl-vlst-p inbox))
               (wf-inbox-p (cdr inbox)))))