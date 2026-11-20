; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "network")

(set-induction-depth-limit 1)
(local (in-theory (enable lookup-of-tail-when-assoc-tail-of-network)))

; Possible Scheduling Steps ---------------------------------------------------

(fty::deftagsum scheduling
  (:run ((p pid-p)))
  (:deliver ((p1 pid-p) (p2 pid-p)))
  (:stutter ()))

; Weakly Fair Abstract Scheduler ----------------------------------------------

; Helper to pick a message from the given outbox, or nil if none exists. If there
; are multiple messages for the same destination, the earliest sent message is picked.
(define parse-outbox ((x outbox-p))
  :returns rpid
  :measure (acl2-count (outbox-fix x))
  (b* ((x (outbox-fix x))
       ((if (omap::emptyp x)) nil)
       ((if (null (omap::head-val x))) (parse-outbox (omap::tail x))))
      (omap::head-key x))
  ///
    (defcong outbox-equiv equal (parse-outbox x) 1)
    (more-returns
      (rpid :name pid-p-of-parse-outbox
        :rule-classes :type-prescription
        (implies rpid (pid-p rpid)))
      (rpid :name assoc-of-parse-outbox
        (implies rpid (omap::assoc rpid x)))
      (rpid :name parse-outbox-has-message
        (implies rpid (omap::lookup rpid x))
        :hints (("Goal" :in-theory (enable omap::lookup)))))
    
    (defrule parse-outbox-when-outbox-has-message-for-dst
      (implies
        (and (outbox-p x) (pid-p dst)
              (omap::assoc dst x)
              (omap::lookup dst x))
        (parse-outbox x))
      :enable omap::lookup)
    
    (defrule parse-outbox-when-proc-has-message-for-dst
      (implies
        (and (proc-p p) (pid-p dst)
              (proc-has-message-for-dst? p dst))
        (parse-outbox (proc->outbox p)))
      :enable (proc->outbox proc-has-message-for-dst?)))

; Weakly fair abstract scheduler.
; Remark: This scheduler is very weak. The only guarantee is
; that it will not decide to stutter if there a possible non
; stutter action.
(encapsulate
  (((schedule * ) => * :formals (net) :guard (network-p net)))

  ; Witness function
  (local (define schedule ((net network-p))
    :returns s
    :measure (acl2-count (network-fix net))
    (b* ((net (network-fix net))
         ((if (omap::emptyp net)) (make-scheduling-stutter))
         (pid (omap::head-key net))
         ((if (runnable? net pid)) (make-scheduling-run :p pid))
         (outbox (proc->outbox (omap::lookup pid net)))
         ((if (parse-outbox outbox))
          (make-scheduling-deliver :p1 pid :p2 (parse-outbox outbox))))
        (schedule (omap::tail net)))
    :hints (("Goal" :in-theory (enable network-fix)))
    ///
      (verify-guards schedule
        :hints (("Goal" :in-theory (enable network-p))))))
  
  ; Theorems
  (more-returns schedule
    (s
     :name scheduling-p-of-schedule
     :rule-classes :type-prescription
     :hints (("Goal" :in-theory (enable schedule)))
     scheduling-p))

  (defcong network-equiv equal (schedule net) 1
    :hints (("Goal" :in-theory (enable schedule))))
  
  (local (defrule crock-1
    (implies (and (omap::assoc x m) (not (omap::assoc x (omap::tail m))))
             (equal (omap::head-key m) x))))

  ; The scheduler does not stutter unless necessary.
  (defrule scheduler-weakly-fair-when-runnable
    (implies
      (and (pid-p pid)
           (network-p net)
           (omap::assoc pid net)
           (runnable? net pid))
      (not (equal (schedule net) (make-scheduling-stutter))))
    :enable (schedule runnable? proc-runnable?)
    :hints (("Subgoal *1/4" :use (:instance crock-1 (x pid) (m net)))))

  (defrule scheduler-weakly-fair-when-deliverable
    (implies
      (and (pid-p pid) (pid-p dst)
           (network-p net)
           (omap::assoc pid net)
           (has-message-for-dst? net pid dst))
      (not (equal (schedule net) (make-scheduling-stutter))))
    :enable schedule
    :hints (("Subgoal *1/6" :use (:instance crock-1 (x pid) (m net)))))
  
  ; The scheduler is correct, i.e. only runs runnable processes and
  ; only attempts to deliver existing messages.
  (defrule scheduler-correct-when-run
    (implies
      (equal (scheduling-kind (schedule net)) :run)
      (runnable? net (scheduling-run->p (schedule net))))
    :enable (network-fix schedule))

  (defrule scheduler-correct-when-deliver
    (implies
      (equal (scheduling-kind (schedule net)) :deliver)
      (has-message-for-dst?
        net
        (scheduling-deliver->p1 (schedule net))
        (scheduling-deliver->p2 (schedule net))))
    :enable (schedule network-fix has-message-for-dst? proc-has-message-for-dst?)))


; Executable counterpart: run the first runnable process, and deliver
; the first encountered message, starting from the head of the network.
(define in-order-schedule ((net network-p))
  :returns (s scheduling-p)
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
       ((if (omap::emptyp net)) (make-scheduling-stutter))
       (pid (omap::head-key net))
       ((if (runnable? net pid)) (make-scheduling-run :p pid))
       (outbox (proc->outbox (omap::lookup pid net)))
       ((if (parse-outbox outbox))
        (make-scheduling-deliver :p1 pid :p2 (parse-outbox outbox))))
      (in-order-schedule (omap::tail net)))
  :hints (("Goal" :in-theory (enable network-fix)))
  ///
    (defcong network-equiv equal (in-order-schedule net) 1)
    (verify-guards in-order-schedule
      :hints (("Goal" :in-theory (enable network-p))))
    (local (defrule crock-1
      (implies (and (omap::assoc x m) (not (omap::assoc x (omap::tail m))))
              (equal (omap::head-key m) x))))

    (defrule in-order-scheduler-weakly-fair-when-runnable
      (implies 
        (and (pid-p pid)
             (network-p net)
             (omap::assoc pid net)
             (runnable? net pid))
        (not (equal (in-order-schedule net) '(:stutter))))
      :enable (runnable? proc-runnable?)
      :hints (("Subgoal *1/4" :use (:instance crock-1 (x pid) (m net)))))
    
    (defrule in-order-scheduler-weakly-fair-when-deliverable
      (implies 
        (and (pid-p pid) (pid-p dst)
             (network-p net)
             (omap::assoc pid net)
             (has-message-for-dst? net pid dst))
        (not (equal (in-order-schedule net) '(:stutter))))
      :hints (("Subgoal *1/6" :use (:instance crock-1 (x pid) (m net)))))
    
    (defrule in-order-scheduler-correct-when-run
      (implies
        (equal (scheduling-kind (in-order-schedule net)) :run)
        (runnable? net (scheduling-run->p (in-order-schedule net))))
      :enable network-fix)
    
    (defrule in-order-scheduler-correct-when-deliver
      (implies
        (equal (scheduling-kind (in-order-schedule net)) :deliver)
        (has-message-for-dst?
          net
          (scheduling-deliver->p1 (in-order-schedule net))
          (scheduling-deliver->p2 (in-order-schedule net))))
      :enable (network-fix has-message-for-dst? proc-has-message-for-dst? proc->outbox)))

(defattach (schedule in-order-schedule)
  :hints (("Goal" :use (:instance in-order-scheduler-weakly-fair-when-deliverable))))