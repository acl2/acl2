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

; receive -> blocked ------------------------------------------------------------

; sent-message-wf holds after a process blocks.
(local (defrule sent-message-wf-of-receive-to-blocked
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (omap::assoc p net)
      (equal (proc->ps (omap::lookup p net)) :receive)
      (equal (proc->ps proc) :blocked)
      (equal (proc->s proc) (proc->s (omap::lookup p net)))
      (equal (proc->inbox-tried proc)
             (append (proc->inbox-tried (omap::lookup p net))
                     (proc->inbox-new (omap::lookup p net))))
      (sent-message-wf self outbox parent net))
    (sent-message-wf self outbox parent (omap::update p proc net)))
  :enable (sent-message-wf omap::lookup-of-update)))

; The properties that need to hold specifically for the process that blocked.
(local (defruled inv-of-run-receive-to-blocked-self
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (proc (change-proc pp
               :ps :blocked
               :inbox-new nil
               :inbox-tried (append (proc->inbox-tried pp) (proc->inbox-new pp)))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps pp) :receive)
      (not (equal (omap::lookup 'Parent wbind) p))
      (pid-lst-p (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
      (not (inbox-contains (proc->inbox-new pp) (omap::lookup 'ChildHd bind))))
    (inv p (omap::update p proc net))))
  :enable (wtree-fields remaining-children-p remaining-children proc->outbox)
  :disable (inv-of-inv-all inv-of-run-to-receiving
            wtree-bind0-of-reduce-receive-klst-p)
  :expand ((inv p net) (wtree-bind (omap::lookup p net)))
  :use ((:instance inv-of-inv-all (pid p))
        (:instance inv-of-run-to-receiving
          (proc (b* ((pp (omap::lookup p net)))
                  (change-proc pp
                    :ps :blocked
                    :inbox-new nil
                    :inbox-tried (append (proc->inbox-tried pp)
                                         (proc->inbox-new pp)))))))))

; receive -> blocked, for every node.
(defruled inv-of-run-receive-to-blocked
  (b* ((pp (omap::lookup p net))
       (bind (erl-state->bind (proc->s pp)))
       (wbind (wtree-bind pp))
       (qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp)))
       (proc (change-proc pp
               :ps :blocked
               :inbox-new nil
               :inbox-tried (append (proc->inbox-tried pp) (proc->inbox-new pp)))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps pp) :receive)
      (not (equal (omap::lookup 'Parent wbind) p))
      (pid-lst-p (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
      (not (inbox-contains (proc->inbox-new pp) (omap::lookup 'ChildHd bind)))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p proc net))))
  :cases ((equal pid p))
  :expand ((wtree-bind (omap::lookup p net)))
  :enable wtree-fields
  :use ((:instance inv-of-run-receive-to-blocked-self)
        (:instance inv-of-run-other
          (proc (b* ((pp (omap::lookup p net)))
                  (change-proc pp
                    :ps :blocked
                    :inbox-new nil
                    :inbox-tried (append (proc->inbox-tried pp)
                                         (proc->inbox-new pp))))))))
