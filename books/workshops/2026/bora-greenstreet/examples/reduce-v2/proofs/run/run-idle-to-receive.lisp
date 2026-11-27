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

; idle -> receive ---------------------------------------------------------------

; The properties that need to hold specifically for the process that ran
; from idle to receive. Afterwards, we still need to show that the process' children
; also satisfiy the invariant.
(local (defruled inv-of-run-idle-to-receive-self
  (b* ((pp (omap::lookup p net))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (chd (car children))
       (ns (apply-k (proc->s pp) (proc->klst pp)))
       (proc (change-proc pp
               :s (update-erl-state->in ns (make-erl-val-none))
               :ps :receive
               :klst (erl-val-receive->klst (erl-state->in ns)))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps pp) :idle)
      (consp children)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (not (equal parent p))
      (natp index)
      (pid-lst-p children)
      (omap::assoc chd net)
      (not (equal chd p))
      (leaf-p (omap::lookup chd net))
      (equal (erl-val-integer->val
               (omap::lookup 'Index (wtree-bind (omap::lookup chd net))))
             (+ 1 index)))
    (inv p (omap::update p proc net))))
  :enable (wtree-fields remaining-children-p remaining-children make-reduce-proc)
  :disable (inv-of-inv-all inv-of-run-to-receiving apply-k-of-idle-with-children)
  :expand (inv p net)
  :use ((:instance inv-of-inv-all (pid p))
        (:instance apply-k-of-idle-with-children
          (s (proc->s (omap::lookup p net)))
          (klst (proc->klst (omap::lookup p net)))
          (self p)
          (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
          (children (erl-val-cons->lst
                      (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
          (index (erl-val-integer->val
                   (omap::lookup 'Index (wtree-bind (omap::lookup p net))))))
        (:instance inv-of-run-to-receiving
          (proc (b* ((pp (omap::lookup p net))
                     (ns (apply-k (proc->s pp) (proc->klst pp))))
                  (change-proc pp
                    :s (update-erl-state->in ns (make-erl-val-none))
                    :ps :receive
                    :klst (erl-val-receive->klst (erl-state->in ns)))))))))

; sent-message-wf still holds for p's children
(local (defrule sent-message-wf-of-idle-to-receive
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (not (equal pid p))
      (omap::assoc pid net) (omap::assoc p net)
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal (proc->ps (omap::lookup p net)) :idle)
      (equal (proc->ps proc) :receive)
      (equal (proc->inbox-new proc) (proc->inbox-new (omap::lookup p net)))
      (remaining-children-p (erl-state->bind (proc->s proc)))
      (equal (remaining-children (erl-state->bind (proc->s proc)))
             (erl-val-cons->lst
               (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
      (or (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))
          (member-equal pid
            (erl-val-cons->lst
              (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))))
      (sent-message-wf (omap::lookup pid net)
                       (proc->outbox (omap::lookup pid net))
                       (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
                       net))
    (sent-message-wf (omap::lookup pid net)
                     (proc->outbox (omap::lookup pid net))
                     (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
                     (omap::update p proc net)))
  :enable (sent-message-wf proc->pid omap::lookup-of-update)
  :cases ((equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))))

; parent-still-waiting-p still holds for p's children
(local (defrule parent-still-waiting-p-of-idle-to-receive
  (implies
    (and
      (network-p net) (network-p (omap::update p proc net))
      (proc-p proc) (pid-p pid) (not (equal pid p))
      (omap::assoc pid net) (omap::assoc p net)
      (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))))
      (equal (proc->ps proc) :receive)
      (remaining-children-p (erl-state->bind (proc->s proc)))
      (equal (remaining-children (erl-state->bind (proc->s proc)))
             (erl-val-cons->lst
               (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
      (or (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))
          (member-equal pid
            (erl-val-cons->lst
              (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net))))))
      (parent-still-waiting-p pid
        (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) net))
    (parent-still-waiting-p pid
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      (omap::update p proc net)))
  :enable (parent-still-waiting-p omap::lookup-of-update)
  :cases ((equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))))

; Every other node (other than the one that was run) also satisfy inv.
(local (defruled inv-of-run-idle-to-receive-other
  (b* ((pp (omap::lookup p net))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids (wtree-bind pp))))
       (qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp))))
  (implies
    (and
      (run-hyps p proc net)
      (pid-p pid) (not (equal pid p)) (omap::assoc pid net)
      (equal (proc->ps pp) :idle)
      (equal (proc->ps proc) :receive)
      (equal (proc->inbox-new proc) (proc->inbox-new pp))
      (remaining-children-p (erl-state->bind (proc->s proc)))
      (equal (remaining-children (erl-state->bind (proc->s proc))) children)
      (or (not (equal qparent p)) (member-equal pid children))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p proc net))))
  :disable inv-of-run-other
  :use inv-of-run-other))

; BOZO: another brute force solution.
(local (defruled idle-to-receive-props
  (b* ((pp (omap::lookup p net))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (ns (apply-k (proc->s pp) (proc->klst pp)))
       (proc (change-proc pp
               :s (update-erl-state->in ns (make-erl-val-none))
               :ps :receive
               :klst (erl-val-receive->klst (erl-state->in ns)))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (equal (proc->ps pp) :idle)
      (consp children)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (natp index)
      (pid-lst-p children))
    (and
      (network-p (omap::update p proc net))
      (equal (wtree-fields proc) (wtree-fields pp))
      (remaining-children-p (erl-state->bind (proc->s proc)))
      (equal (remaining-children (erl-state->bind (proc->s proc))) children))))
  :expand ((inv p net))
  :enable (wtree-fields remaining-children-p remaining-children make-reduce-proc)
  :disable (inv-of-inv-all apply-k-of-idle-with-children)
  :use ((:instance inv-of-inv-all (pid p))
        (:instance apply-k-of-idle-with-children
          (s (proc->s (omap::lookup p net)))
          (klst (proc->klst (omap::lookup p net)))
          (self p)
          (parent (omap::lookup 'Parent (wtree-bind (omap::lookup p net))))
          (children (erl-val-cons->lst
                      (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
          (index (erl-val-integer->val
                   (omap::lookup 'Index (wtree-bind (omap::lookup p net)))))))))

; idle -> receive, for every node.
(defruled inv-of-run-idle-to-receive
  (b* ((pp (omap::lookup p net))
       (wbind (wtree-bind pp))
       (parent (omap::lookup 'Parent wbind))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (chd (car children))
       (qp (omap::lookup pid net))
       (qparent (omap::lookup 'Parent (wtree-bind qp)))
       (ns (apply-k (proc->s pp) (proc->klst pp)))
       (proc (change-proc pp
               :s (update-erl-state->in ns (make-erl-val-none))
               :ps :receive
               :klst (erl-val-receive->klst (erl-state->in ns)))))
  (implies
    (and
      (network-p net) (inv-all net)
      (pid-p p) (omap::assoc p net)
      (pid-p pid) (omap::assoc pid net)
      (equal (proc->ps pp) :idle)
      (consp children)
      ; tree facts about p
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
      (not (equal parent p))
      (natp index)
      (pid-lst-p children)
      (omap::assoc chd net)
      (not (equal chd p))
      (leaf-p (omap::lookup chd net))
      (equal (erl-val-integer->val
               (omap::lookup 'Index (wtree-bind (omap::lookup chd net))))
             (+ 1 index))
      ; facts about pid
      (or (not (equal qparent p)) (member-equal pid children))
      (erl-val-p qparent)
      (or (not (equal (proc->ps qp) :terminated))
          (sent-message-wf qp (proc->outbox qp) qparent net))
      (or (equal (proc->ps qp) :terminated)
          (parent-still-waiting-p pid qparent net)))
    (inv pid (omap::update p proc net))))
  :cases ((equal pid p))
  :use ((:instance inv-of-run-idle-to-receive-self)
        (:instance idle-to-receive-props)
        (:instance inv-of-run-idle-to-receive-other
          (proc (b* ((pp (omap::lookup p net))
                     (ns (apply-k (proc->s pp) (proc->klst pp))))
                  (change-proc pp
                    :s (update-erl-state->in ns (make-erl-val-none))
                    :ps :receive
                    :klst (erl-val-receive->klst (erl-state->in ns))))))))
