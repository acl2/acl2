; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../evaluator/top")

; Erlang Process --------------------------------------------------------------

(std::defenum proc-state-p
  (:idle :terminated :receive :blocked))

(fty::defprod proc
  (; State of the Erlang process
   (ps proc-state-p :default :idle)

   ; State of the Erlang program run by the process
   (s erl-state-p :default (make-erl-state))

   ; TODO: while it is not necessary to split the inbox as done
   ; below, it has made some parts of the implementation and proofs
   ; easier. However, the scheduler has changed a lot since then,
   ; and they may no longer be useful.

   ; Messages that have been received, but not yet matched in a
   ; receive expression.
   (inbox-new erl-vlst-p :default nil)

   ; Messages that have been received and have been tried to be matched
   ; by the current receive expression, and have failed.
   (inbox-tried erl-vlst-p :default nil)
   
   ; the remaining computation
   (klst erl-klst-p :default nil)))

; Get the PID of a process.
(define proc->pid ((p proc-p))
  :returns (pid pid-p)
  (b* ((p (proc-fix p)))
      (erl-state->self (proc->s p)))
  ///
    (more-returns
      (pid :name erl-val-kind-of-proc->pid
        (equal (erl-val-kind pid) :pid)
       :hints
        (("Goal"
            :in-theory (e/d (pid-p) (proc->pid pid-p-of-proc->pid))
            :use (:instance pid-p-of-proc->pid)))))
    (defcong proc-equiv equal (proc->pid p) 1)
    
    (defrule proc->pid-of-proc
      (equal (proc->pid (proc ps s inew itried klst))
             (erl-state->self (erl-state-fix s)))))

; Get the outbox of a process.
(define proc->outbox ((p proc-p))
  :returns (o outbox-p)
  (b* ((p (proc-fix p)))
      (erl-state->outbox (proc->s p)))
  ///
    (defcong proc-equiv equal (proc->outbox p) 1))

; Check if a process if runnable.
(define proc-runnable? ((p proc-p))
  :returns (b booleanp)
  (b* ((p (proc-fix p)))
      (or (equal (proc->ps p) :idle)
          (equal (proc->ps p) :receive)))
  ///
    (defcong proc-equiv equal (proc-runnable? p) 1))

; Check if a process has a message for the given destination process.
(define proc-has-message-for-dst? ((p proc-p) (dst pid-p))
  (b* ((p (proc-fix p))
       (dst (pid-fix dst)))
      (and (proc->outbox p)
           (omap::assoc dst (proc->outbox p))
           (omap::lookup dst (proc->outbox p))))
  ///
    (defcong proc-equiv equal (proc-has-message-for-dst? p dst) 1)
    (defcong pid-equiv equal (proc-has-message-for-dst? p dst) 2))