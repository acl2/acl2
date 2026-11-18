; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "abstract")
(include-book "../evaluator/theorems/state/self")


; Given a process that is evaluating a receive expression, try to receive from the message queue.
(define proc-receive ((proc proc-p))
  :returns (rp proc-p)
  :measure (len (proc->inbox-new (proc-fix proc)))
  (b* ((proc (proc-fix proc))

       ; If there are no more messages to try, the process is blocked.
       ((unless (proc->inbox-new proc))
        (b* ((- (cw "Pid: ~x0 failed to receive, it is now blocked.~%~%" (proc->pid proc))))
            (change-proc proc :ps :blocked)))
       (- (cw "Attempting to receive message ~x0~%" (car (proc->inbox-new proc))))

       (rs (update-erl-state->in (proc->s proc) (car (proc->inbox-new proc))))
       (rs (apply-k rs (proc->klst proc))))
      (cond
        ; If the first message did not match any of the receive clauses, try the rest of the queue.
        ((equal (erl-val-kind (erl-state->in rs)) :blocked)
         (b* ((- (cw "Could not receive message. Trying next one.~%")))
              (proc-receive
                (change-proc proc
                  :inbox-new (cdr (proc->inbox-new proc))
                  :inbox-tried (append (proc->inbox-tried proc) (list (car (proc->inbox-new proc))))))))
        
        ; If the message was received successfully, check if it is still runnable or if it has terminated.
        ((equal (erl-val-kind (erl-state->in rs)) :receive)
         (b* ((klst (erl-val-receive->klst (erl-state->in rs)))
              ((unless (erl-klst-p klst))
               (b* ((- (cw "proc-receive: bad continuation list.~%"))) proc))
              (- (cw "Received the message and ran till the next receive.~%~%")))
             (change-proc
               proc
                 :s (update-erl-state->in rs (make-erl-val-none))
                 :ps :receive
                 :inbox-new (append (proc->inbox-tried proc) (cdr (proc->inbox-new proc)))
                 :inbox-tried nil
                 :klst klst)))
        (t (b* ((- (cw "Process received a message and terminated with the value: ~x0~%~%" (erl-state->in rs))))
                (change-proc
                   proc
                     :s rs
                     :ps :terminated
                     :inbox-new (append (proc->inbox-tried proc) (cdr (proc->inbox-new proc)))
                     :inbox-tried nil)))))
  ///
    (defcong proc-equiv equal (proc-receive p) 1)
    (more-returns
      (rp :name proc->pid-of-proc-receive
        (equal (proc->pid rp) (proc->pid proc))
        :hints (("Goal" :in-theory (enable proc->pid))))))


; A single step of the Erlang runtime. Invoke the scheduler and follow its decision.
(define erl-step ((net network-p))
  :prepwork
    ((defrule crock-1
      (implies (omap::assoc p (network-fix net))
               (equal (proc->pid (omap::lookup p (network-fix net))) p))
      :enable (omap::lookup network-fix network-p))
    (defrule crock-2
      (implies (omap::assoc p (network-fix net))
               (equal (erl-state->self (proc->s (omap::lookup p (network-fix net)))) p))
      :disable crock-1 :enable proc->pid :use (:instance crock-1)))
  :returns rnet
  :guard-hints
    (("Goal"
      :in-theory
        (e/d (network-p network-fix
              proc-has-message-for-dst?
              has-message-for-dst?)
             (scheduler-correct-when-run
              scheduler-correct-when-deliver))
      :use ((:instance scheduler-correct-when-run)
            (:instance scheduler-correct-when-deliver))))
  (b* ((net (network-fix net))
       ((if (terminated? net)) net)
       ; Invoke the scheduler.
       (sc (schedule net))
       (- (cw "Scheduler decision: ~x0.~%~%" sc)))
    (scheduling-case sc
      (:stutter net)
      (:run
        (b* ((- (cw "Running: ~x0.~%" (scheduling-run->p sc)))
             (pid (scheduling-run->p sc))
             (proc (omap::lookup pid net))
             (s (proc->s proc))
             (klst (proc->klst proc))
             ((unless (erl-klst-p klst))
              (b* ((- (cw "erl-step: bad continuation list.~%"))) nil)))
            (if (equal (proc->ps proc) :idle)
                ; The process is running for the first time.
                (b* ((- (cw "Evaluating ~x0 for the first time. ~%" pid))
                     (ns (apply-k s klst)))
                    (if (equal (erl-val-kind (erl-state->in ns)) :receive)
                        ; The process ran until a receive was encountered.
                        (b*
                          ((- (cw "Evaluated ~x0 till the next receive. ~%~%" pid))
                           (nklst (erl-val-receive->klst (erl-state->in ns)))
                           ((unless (erl-klst-p nklst))
                            (b* ((- (cw "erl-step: bad continuation list.~%"))) nil)))
                          (omap::update pid
                            (change-proc proc
                                :s (update-erl-state->in ns (make-erl-val-none))
                                :ps :receive
                                :klst nklst)
                            net))
                        ; The process terminated.
                        (b*
                          ((- (cw "~x0 terminated. ~%~%" pid)))
                          (omap::update pid
                            (change-proc proc
                              :s ns
                              :ps :terminated
                             :klst nil)
                            net))))
                ; The process is attempting to receive.
                (b* ((- (cw "~x0 is trying to receive. ~%" pid)))
                    (omap::update pid (proc-receive proc) net)))))
        (:deliver
          (b* ((src (scheduling-deliver->p1 sc))
               (dst (scheduling-deliver->p2 sc))
               (psrc (omap::lookup src net))
               (ssrc (proc->s psrc))
               (- (cw "Delivering message from: ~x0 to ~x1~%" src dst))
               
               ; If the destination does not exist, drop the message.
               ((unless (omap::assoc dst net))
                (b* ((- (cw "Destination: ~x0 does not exist.~%" dst)))
                     (omap::update
                       src
                       (change-proc psrc
                         :s  (update-erl-state->outbox ssrc
                               (omap::update dst
                                 (cdr (omap::lookup dst (proc->outbox psrc)))
                                 (proc->outbox psrc))))
                       net)))
              
               (pdst (omap::lookup dst net))

               (- (cw "Message delivered from: ~x0 to ~x1.~%~%" src dst)))
              (if (equal (proc->ps pdst) :blocked)
                  ; The destination should no longer be blocked.
                  (b*
                    ((- (cw "Dst: ~x0 is now unblocked.~%" dst)))
                    (omap::update dst
                      (change-proc pdst
                        :inbox-new (append (proc->inbox-tried pdst)
                                           (proc->inbox-new pdst)
                                           (list (car (omap::lookup dst (proc->outbox psrc)))))
                        :inbox-tried nil
                        :ps :receive)
                      (omap::update src
                        (change-proc psrc
                          :s (update-erl-state->outbox ssrc
                               (omap::update dst
                                 (cdr (omap::lookup dst (proc->outbox psrc)))
                                 (proc->outbox psrc))))
                        net)))
                  (omap::update dst
                      (change-proc pdst
                        :inbox-new (append (proc->inbox-new pdst)
                                           (list (car (omap::lookup dst (proc->outbox psrc))))))
                      (omap::update src
                        (change-proc psrc
                          :s (update-erl-state->outbox ssrc
                               (omap::update dst
                                 (cdr (omap::lookup dst (proc->outbox psrc)))
                                 (proc->outbox psrc))))
                        net)))))))
  ///
    (more-returns
      (rnet network-p :rule-classes :type-prescription
        ; BOZO: This can be done with single computational hint.
        :hints
          (("Subgoal 9"
            :in-theory
              (e/d (runnable? proc-runnable? network-p-of-update) (scheduler-correct-when-run))
            :use ((:instance scheduler-correct-when-run)))
          ("Subgoal 8"
            :in-theory
              (e/d (runnable? proc-runnable? proc->pid) (scheduler-correct-when-run))
            :use ((:instance scheduler-correct-when-run)))
          ("Subgoal 7"
            :in-theory
              (e/d (runnable? proc-runnable? proc->pid) (scheduler-correct-when-run))
            :use ((:instance scheduler-correct-when-run)))
          ("Subgoal 6"
            :in-theory
              (e/d (runnable? proc-runnable? proc->pid) (scheduler-correct-when-run))
            :use ((:instance scheduler-correct-when-run)))
          ("Subgoal 5"
            :in-theory
              (e/d (runnable? proc-runnable? proc->pid) (scheduler-correct-when-run))
            :use ((:instance scheduler-correct-when-run)))
          ("Subgoal 4"
            :in-theory
              (e/d (has-message-for-dst? proc-has-message-for-dst? proc->pid)
                   (scheduler-correct-when-deliver))
            :use ((:instance scheduler-correct-when-deliver)))
          ("Subgoal 3"
            :in-theory
              (e/d (has-message-for-dst? proc-has-message-for-dst? proc->pid)
                   (scheduler-correct-when-deliver))
            :use ((:instance scheduler-correct-when-deliver)))
          ("Subgoal 2"
            :in-theory
              (e/d (has-message-for-dst? proc-has-message-for-dst? proc->pid)
                   (scheduler-correct-when-deliver))
            :use ((:instance scheduler-correct-when-deliver))))))
      (defcong network-equiv equal (erl-step net) 1))

; Run multiple Erlang processes.
(define erl-runner ((net network-p) (fuel natp))
  :measure (nfix fuel)
  :returns (rnet network-p)
  (b* ((net (network-fix net))
       (fuel (nfix fuel))
       ((if (= fuel 0)) net)
       ((if (terminated? net)) net))
      (erl-runner (erl-step net) (1- fuel))))