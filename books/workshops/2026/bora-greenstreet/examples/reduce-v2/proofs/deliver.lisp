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

; Inv of Deliver ---------------------------------------------------------------

; Hypotheses needed by every deliver case.
; In the current implementation, there are a lot of them...
(local (define deliver-hyps (src dst psrc pdst net)
  :enabled t
  :verify-guards nil
  (and
    (network-p net) (pid-p src) (pid-p dst)
    (inv-all net) (has-message-for-dst? net src dst)
    (omap::assoc src net) (omap::assoc dst net) (not (equal src dst))
    
    ; src is terminated, dst is not
    (equal (proc->ps (omap::lookup src net)) :terminated)
    (not (equal (proc->ps (omap::lookup dst net)) :terminated))

    ; message is well-formed
    (equal
      (erl-val-kind (car (omap::lookup dst (proc->outbox (omap::lookup src net)))))
      :tuple)
    (equal
      (len (erl-val-tuple->lst (car (omap::lookup dst
                                      (proc->outbox (omap::lookup src net)))))) 2)
    (equal (car (erl-val-tuple->lst
              (car (omap::lookup dst
                     (proc->outbox (omap::lookup src net)))))) src)
    
    ; updated sender: unchanged except for outbox
    (proc-p psrc)
    (equal (proc->ps psrc) :terminated)
    (network-p (omap::update src psrc net))
    (network-p (omap::update dst pdst (omap::update src psrc net)))
    (equal (erl-state->bind (proc->s psrc))
           (erl-state->bind (proc->s (omap::lookup src net))))
    (equal (erl-state->in (proc->s psrc))
           (erl-state->in (proc->s (omap::lookup src net))))
    (equal (proc->klst psrc) (proc->klst (omap::lookup src net)))
    (equal (proc->inbox-new psrc) (proc->inbox-new (omap::lookup src net)))
    (equal (proc->inbox-tried psrc)
           (proc->inbox-tried (omap::lookup src net)))
    (outbox-emptyp (proc->outbox psrc))
    
    ; updated destination: inbox-new changes, unblocks if required
    (proc-p pdst)
    (equal (proc->s pdst) (proc->s (omap::lookup dst net)))
    (equal (proc->klst pdst) (proc->klst (omap::lookup dst net)))
    (or (and (not (equal (proc->ps (omap::lookup dst net)) :blocked))
             (equal (proc->ps pdst) (proc->ps (omap::lookup dst net)))
             (equal (proc->inbox-tried pdst)
                    (proc->inbox-tried (omap::lookup dst net)))
             (equal (proc->inbox-new pdst)
                    (append (proc->inbox-new (omap::lookup dst net))
                            (list (car (omap::lookup dst
                                         (proc->outbox
                                           (omap::lookup src net))))))))
        (and (equal (proc->ps (omap::lookup dst net)) :blocked)
             (equal (proc->ps pdst) :receive)
             (null (proc->inbox-tried pdst))
             (equal (proc->inbox-new pdst)
                    (append (proc->inbox-tried (omap::lookup dst net))
                            (proc->inbox-new (omap::lookup dst net))
                            (list (car (omap::lookup dst
                                         (proc->outbox
                                           (omap::lookup src net))))))))))))

(local (defrule received-messages-wf-of-deliver
  (implies
    (and (deliver-hyps src dst psrc pdst net)
         (received-messages-wf inbox cpids net))
    (received-messages-wf inbox cpids
      (omap::update dst pdst (omap::update src psrc net))))
  :enable (received-messages-wf omap::lookup-of-update)))

(local (defrule sent-message-wf-of-deliver
  (implies
    (and (deliver-hyps src dst psrc pdst net)
         (sent-message-wf self outbox parent net))
    (sent-message-wf self outbox parent
      (omap::update dst pdst (omap::update src psrc net))))
  :prep-lemmas
    ((defrule lookup-when-not-assoc
       (implies (not (omap::assoc k m))
                (equal (omap::lookup k m) nil))
       :enable omap::lookup))
  :enable (sent-message-wf omap::lookup-of-update)))

; inv of the nodes other than src and dst ---------------------------------------

(local (defrule inv-of-deliver-other
  (implies
    (and (deliver-hyps src dst psrc pdst net)
         (not (equal pid src)) (not (equal pid dst))
         (omap::assoc pid net))
    (inv pid (omap::update dst pdst (omap::update src psrc net))))
  :expand ((inv pid (omap::update dst pdst (omap::update src psrc net)))
           (inv pid net)
           (wtree-bind psrc) (wtree-bind (omap::lookup src net))
           (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
  :enable wtree-fields
  :disable (inv-of-inv-all)
  :use (:instance inv-of-inv-all)))

; inv of the sender ---------------------------------------------------------------

(local (defrule inv-of-deliver-src
  (implies
    (and (deliver-hyps src dst psrc pdst net)
         (equal (omap::lookup 'Parent (wtree-bind (omap::lookup src net))) dst))
    (inv src (omap::update dst pdst (omap::update src psrc net))))  
  :enable wtree-fields
  :disable (inv-of-inv-all sent-message-wf-when-parent-has-message)
  :expand ((:free (x) (inv src (omap::update x pdst (omap::update src psrc net))))
           (:free (x) (wtree-bind (omap::lookup x net))) (inv src net)
           (wtree-bind pdst) (wtree-bind psrc) (wtree-bind (omap::lookup src net))) 
  :use ((:instance inv-of-inv-all (pid src))
        (:instance sent-message-wf-when-parent-has-message
          (self psrc) (outbox (proc->outbox psrc))
          (parent (omap::lookup 'Parent (wtree-bind (omap::lookup src net))))
          (net (omap::update dst pdst (omap::update src psrc net)))))
  :prep-lemmas
    ((defrule lemma-1
       (implies (and (network-p (omap::update k p net)) (pid-p k))
                (equal (proc->pid p) k))
       :use ((:instance proc->pid-of-lookup-of-network
               (pid k) (net (omap::update k p net)))))
     (defrule lemma-2
       (implies
        (and (outbox-p outbox) (equal (erl-val-kind (car (omap::lookup d outbox))) :tuple))
        (erl-val-p (car (omap::lookup d outbox))))
       :cases ((omap::assoc d outbox))
       :hints (("Subgoal 2" :in-theory (enable omap::lookup)))))))

; inv of the receiver ------------------------------------------------------------

(local (defrule received-messages-wf-of-append-message
  (implies
    (and
      (network-p net) (omap::assoc sender net)
      (erl-vlst-p inbox) (erl-vlst-p cpids)
      (member-equal sender cpids)
      (not (inbox-contains inbox sender))
      (equal (proc->ps (omap::lookup sender net)) :terminated)
      (outbox-emptyp (proc->outbox (omap::lookup sender net)))
      (equal
        (erl-val-kind
          (erl-state->in (proc->s (omap::lookup sender net))))
        :integer)
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (car (erl-val-tuple->lst m)) sender)
      (equal (cadr (erl-val-tuple->lst m))
             (erl-state->in (proc->s (omap::lookup sender net))))
      (received-messages-wf inbox cpids net))
    (received-messages-wf (append inbox (list m)) cpids net))
  :enable (received-messages-wf inbox-contains)
  :induct (received-messages-wf inbox cpids net)))

(local (defrule inv-of-deliver-dst
  (implies
    (and
      (deliver-hyps src dst psrc pdst net)
      (equal
        (cadr (erl-val-tuple->lst
                (car (omap::lookup dst (proc->outbox (omap::lookup src net))))))
        (erl-state->in (proc->s (omap::lookup src net))))
      (member-equal src
        (erl-val-cons->lst
          (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net)))))
      (or (not (remaining-children-p (erl-state->bind (proc->s (omap::lookup dst net)))))
          (member-equal src
            (remaining-children (erl-state->bind (proc->s (omap::lookup dst net)))))))
    (inv dst (omap::update dst pdst (omap::update src psrc net))))
  :enable wtree-fields
  :disable (inv-of-inv-all wtree-bind0-of-reduce-receive-klst-p member-equal
            received-messages-wf-of-append-message inv len not member-of-cons)
  :expand ((:free (c n) (received-messages-wf nil c n))
           (inv dst (omap::update dst pdst (omap::update src psrc net)))
           (inv dst net) (proc->outbox pdst) (proc->outbox (omap::lookup dst net))
           (wtree-bind psrc) (wtree-bind (omap::lookup src net))
           (wtree-bind pdst) (wtree-bind (omap::lookup dst net)))
  :do-not-induct t
  :use ((:instance inv-of-inv-all (pid src)) (:instance inv-of-inv-all (pid dst))
        (:instance integer-value-of-inv-terminated (pid src)) ; this causes speedup?
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst (omap::update src psrc net))) (sender src)
          (m (car (omap::lookup dst (proc->outbox (omap::lookup src net)))))
          (inbox (proc->inbox-new (omap::lookup dst net)))
          (cpids (erl-val-cons->lst
                   (omap::lookup 'ChildPids (wtree-bind (omap::lookup dst net))))))
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst (omap::update src psrc net))) (sender src)
          (m (car (omap::lookup dst (proc->outbox (omap::lookup src net)))))
          (inbox (proc->inbox-new (omap::lookup dst net)))
          (cpids (remaining-children (erl-state->bind (proc->s (omap::lookup dst net))))))
        (:instance received-messages-wf-of-append-message
          (net (omap::update dst pdst (omap::update src psrc net))) (sender src)
          (m (car (omap::lookup dst (proc->outbox (omap::lookup src net)))))
          (inbox (proc->inbox-tried (omap::lookup dst net)))
          (cpids (remaining-children (erl-state->bind (proc->s (omap::lookup dst net)))))))))

; inv of deliver ---------------------------------------------------------------

; The following can be derived from (inv-all net).
; BOZO: This is a brute force solution.
(local (defruled inv-of-deliver-props
  (implies
    (and (network-p net) (inv-all net)
         (pid-p src) (pid-p dst)
         (has-message-for-dst? net src dst))
    (and
      (omap::assoc src net)
      (equal (proc->ps (omap::lookup src net)) :terminated)
      (equal (omap::lookup 'Parent (wtree-bind (omap::lookup src net))) dst)
      (not (equal (proc->ps (omap::lookup dst net)) :terminated))
      (omap::emptyp (omap::tail (proc->outbox (omap::lookup src net))))
      (not (cdr (omap::lookup dst (proc->outbox (omap::lookup src net)))))
      (equal (erl-val-kind
               (car (omap::lookup dst (proc->outbox (omap::lookup src net)))))
             :tuple)
      (equal
        (len (erl-val-tuple->lst
              (car (omap::lookup dst
                      (proc->outbox (omap::lookup src net)))))) 2)
      (equal
        (car (erl-val-tuple->lst
          (car (omap::lookup dst
                  (proc->outbox (omap::lookup src net)))))) src)
      (equal
        (cadr (erl-val-tuple->lst
          (car (omap::lookup dst
                (proc->outbox (omap::lookup src net))))))
        (erl-state->in (proc->s (omap::lookup src net))))
      (or (not (remaining-children-p (erl-state->bind (proc->s (omap::lookup dst net)))))
          (member-equal src
            (remaining-children (erl-state->bind (proc->s (omap::lookup dst net))))))))
  :enable (sent-message-wf has-message-for-dst? proc-has-message-for-dst?
           proc->outbox make-reduce-proc)
  :disable (omap::assoc-of-tail-when-not-head)
  :expand (inv src net)
  :use ((:instance inv-of-inv-all (pid src))
        (:instance omap::assoc-of-tail-when-not-head
          (key dst) (map (proc->outbox (omap::lookup src net))))
        (:instance omap::assoc-of-tail-when-not-head
          (key (omap::lookup 'Parent (wtree-bind (omap::lookup src net))))
          (map (proc->outbox (omap::lookup src net)))))))

; The deliver step preseves the invariant.
(defrule inv-of-erl-step-of-deliver
  (implies
    (and
      (network-p net) (inv-all net) (not (terminated? net))
      (equal (scheduling-kind (schedule net)) :deliver)
      (omap::assoc pid (erl-step net)))
    (inv pid (erl-step net)))
  :enable (erl-step check-parent)
  :disable (omap::update-different scheduler-correct-when-deliver
            check-parent-of-wtree-p)
  :use ((:instance scheduler-correct-when-deliver)
        (:instance inv-of-deliver-props
          (src (scheduling-deliver->p1 (schedule net)))
          (dst (scheduling-deliver->p2 (schedule net))))
        (:instance wtree-p-of-inv
          (pid (scheduling-deliver->p1 (schedule net))))
        (:instance check-parent-of-wtree-p
          (pid (scheduling-deliver->p1 (schedule net)))))
  :cases ((equal pid (scheduling-deliver->p1 (schedule net)))
          (equal pid (scheduling-deliver->p2 (schedule net)))))