; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "eval")

; All reasoning regarding proc-receive for the reduce proof.

(local (defun receive-induct (proc)
  (declare (xargs :measure (len (proc->inbox-new proc))))
  (if (and (consp (proc->inbox-new proc))
           (not (equal (car (erl-val-tuple->lst (car (proc->inbox-new proc))))
                       (omap::lookup 'ChildHd (erl-state->bind (proc->s proc))))))
      (receive-induct
        (change-proc proc
          :inbox-new (cdr (proc->inbox-new proc))
          :inbox-tried (append (proc->inbox-tried proc)
                               (list (car (proc->inbox-new proc))))))
    proc)))

; receive -> blocked: no message from ChildHd.
(defruled proc-receive-when-no-match
  (implies
    (and
      (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind)
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (pid-p (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (wf-inbox-p (proc->inbox-new p))
      (not
        (inbox-contains
          (proc->inbox-new p)
          (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))))
    (equal (proc-receive p)
           (change-proc p
             :ps :blocked
             :inbox-new nil
             :inbox-tried (append (proc->inbox-tried p) (proc->inbox-new p)))))
  :enable proc-receive)

; A single step of proc-receive
(local (defruled proc-receive-step
  (implies
    (and
      (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind)
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (consp (proc->inbox-new p)) (wf-inbox-p (proc->inbox-new p))
      (not (equal (car (erl-val-tuple->lst (car (proc->inbox-new p))))
                  (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))))
    (equal (proc-receive p)
           (proc-receive
             (change-proc p
               :inbox-new (cdr (proc->inbox-new p))
               :inbox-tried (append (proc->inbox-tried p) (list (car (proc->inbox-new p))))))))
  :expand ((proc-receive p) (wf-inbox-p (proc->inbox-new p)))))

; receive -> receive: ChildHd's message is at the head of the inbox. ChildTl is not nil.
(local (defruled proc-receive-of-match-car
  (implies
    (and
      (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind)
      (equal (erl-state->world (proc->s p)) (sum-reduce-world))
      (equal (erl-state->module (proc->s p)) 'local)
      ; The following variables are bound.
      (omap::assoc 'ParentPid (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s p)))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s p)))
      ; RightTotal is not bound yet.
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (pid-p (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
      ; ChildTl is not nil.
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))) :cons)
      (pid-lst-p (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
      (consp (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind (proc->s p)))) :integer)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid (erl-state->bind (proc->s p)))) :pid)
          (equal (omap::lookup 'ParentPid (erl-state->bind (proc->s p))) (make-erl-val-atom :val 'none)))
      (consp (proc->inbox-new p)) (wf-inbox-p (proc->inbox-new p))
      ; ChildHd is a match.
      (equal (car (erl-val-tuple->lst (car (proc->inbox-new p))))
             (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))
    (equal
      (proc-receive p)
      (change-proc p
        :ps :receive
        :inbox-tried nil
        :inbox-new (append (proc->inbox-tried p) (cdr (proc->inbox-new p)))
        :klst
          (append
            (list (erl-k (- (erl-k->fuel (car (proc->klst p))) 4)
                         (erl-k->kont (car (proc->klst p))))
                  (erl-k (- (erl-k->fuel (car (proc->klst p))) 4)
                         (make-kont-exprs :exprs nil))
                  (erl-k (- (erl-k->fuel (car (proc->klst p))) 3)
                         (make-kont-function-return
                           :bind (omap::update 'RightTotal
                                   (cadr (erl-val-tuple->lst (car (proc->inbox-new p))))
                                   (erl-state->bind (proc->s p)))
                           :module 'local))
                  (erl-k (- (erl-k->fuel (car (proc->klst p))) 1)
                         (make-kont-exprs :exprs nil)))
            (cdr (proc->klst p)))
        :s (update-erl-state->in
             (update-erl-state->bind (proc->s p)
               (omap::from-lists
                 (list 'ChildHd 'ChildTl 'LeftTotal 'ParentPid)
                 (list (car (erl-val-cons->lst
                              (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
                       (make-erl-val-cons :lst
                        (cdr (erl-val-cons->lst
                               (omap::lookup 'ChildTl (erl-state->bind (proc->s p))))))
                       (make-erl-val-integer
                         :val (+ (erl-val-integer->val
                                   (omap::lookup 'LeftTotal (erl-state->bind (proc->s p))))
                                 (erl-val-integer->val
                                  (cadr (erl-val-tuple->lst (car (proc->inbox-new p)))))))
                       (omap::lookup 'ParentPid (erl-state->bind (proc->s p))))))
             (make-erl-val-none)))))
  :expand ((proc-receive p)
           (wf-inbox-p (proc->inbox-new p)))))

; receive -> receive: ChildHd's message is in the inbox. ChildTl is not nil.
(defruled proc-receive-of-match
  (implies
    (and
      (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind)
      (equal (erl-state->world (proc->s p)) (sum-reduce-world))
      (equal (erl-state->module (proc->s p)) 'local)
      (omap::assoc 'ParentPid (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s p)))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s p)))
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (pid-p (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))) :cons)
      (pid-lst-p (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
      (consp (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind (proc->s p)))) :integer)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid (erl-state->bind (proc->s p)))) :pid)
          (equal (omap::lookup 'ParentPid (erl-state->bind (proc->s p))) (make-erl-val-atom :val 'none)))
      (wf-inbox-p (proc->inbox-new p))
      (inbox-contains (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))
    (equal
      (proc-receive p)
      (change-proc p
        :ps :receive
        :inbox-tried nil
        :inbox-new (append (proc->inbox-tried p)
                           (inbox-without (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))
        :klst (append (list (erl-k (- (erl-k->fuel (car (proc->klst p))) 4) (erl-k->kont (car (proc->klst p)))) (erl-k (- (erl-k->fuel (car (proc->klst p))) 4) (make-kont-exprs :exprs nil)) (erl-k (- (erl-k->fuel (car (proc->klst p))) 3) (make-kont-function-return :bind (omap::update 'RightTotal (inbox->value (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))) (erl-state->bind (proc->s p))) :module 'local)) (erl-k (- (erl-k->fuel (car (proc->klst p))) 1) (make-kont-exprs :exprs nil))) (cdr (proc->klst p)))
        :s (update-erl-state->in
             (update-erl-state->bind (proc->s p)
               (omap::from-lists
                 (list 'ChildHd 'ChildTl 'LeftTotal 'ParentPid)
                 (list (car (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
                       (make-erl-val-cons :lst (cdr (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind (proc->s p))))))
                       (make-erl-val-integer
                         :val (+ (erl-val-integer->val
                                   (omap::lookup 'LeftTotal (erl-state->bind (proc->s p))))
                                 (erl-val-integer->val (inbox->value (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))))
                       (omap::lookup 'ParentPid (erl-state->bind (proc->s p))))))
             (make-erl-val-none)))))
  :induct (receive-induct p)
  :enable (proc-receive-step proc-receive-of-match-car)
  :expand ((wf-inbox-p (proc->inbox-new p))
           (:free (x) (inbox-contains nil x))
           (:free (x) (inbox-contains (proc->inbox-new p) x))
           (:free (x) (inbox-without (proc->inbox-new p) x))
           (:free (x) (inbox->value (proc->inbox-new p) x))))

; receive -> terminated: receive the last message, which is obviously at the car of the inbox.
(local (defruled proc-receive-of-match-last-car
  (implies
    (and
      (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind)
      (equal (erl-state->world (proc->s p)) (sum-reduce-world))
      (equal (erl-state->module (proc->s p)) 'local)
      (not (erl-state->outbox (proc->s p)))
      (omap::assoc 'ParentPid (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s p)))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s p)))
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (pid-p (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))) :cons)
      (not (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind (proc->s p)))) :integer)
      (or (pid-p (omap::lookup 'ParentPid (erl-state->bind (proc->s p)))) (equal (omap::lookup 'ParentPid (erl-state->bind (proc->s p))) (make-erl-val-atom :val 'none)))
      (consp (proc->inbox-new p)) (wf-inbox-p (proc->inbox-new p))
      (equal (car (erl-val-tuple->lst (car (proc->inbox-new p)))) (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))
    (equal
      (proc-receive p)
      (change-proc p
        :ps :terminated
        :inbox-tried nil
        :inbox-new (append (proc->inbox-tried p) (cdr (proc->inbox-new p)))
        :s (update-erl-state->bind-mod
             (update-erl-state->outbox
               (update-erl-state->bind
                 (update-erl-state->in (proc->s p) (make-erl-val-integer :val (+ (erl-val-integer->val (omap::lookup 'LeftTotal (erl-state->bind (proc->s p)))) (erl-val-integer->val (cadr (erl-val-tuple->lst (car (proc->inbox-new p))))))))
                 (omap::update 'RightTotal (cadr (erl-val-tuple->lst (car (proc->inbox-new p)))) (erl-state->bind (proc->s p))))
               (if (pid-p (omap::lookup 'ParentPid (erl-state->bind (proc->s p))))
                   (omap::update (omap::lookup 'ParentPid (erl-state->bind (proc->s p)))
                     (list (make-erl-val-tuple
                             :lst (list (erl-state->self (proc->s p)) (make-erl-val-integer :val (+ (erl-val-integer->val (omap::lookup 'LeftTotal (erl-state->bind (proc->s p)))) (erl-val-integer->val (cadr (erl-val-tuple->lst (car (proc->inbox-new p))))))))))
                     nil)
                 nil))
             (bind-fix rbind)
             'local))))
  :expand ((proc-receive p)
           (wf-inbox-p (proc->inbox-new p)))))

; receive -> terminated: lift the previous rule to inbox-contains
(defruled proc-receive-of-match-last
  (implies
    (and
      (proc-p p) (reduce-receive-klst-p (proc->klst p) rbind)
      (equal (erl-state->world (proc->s p)) (sum-reduce-world))
      (equal (erl-state->module (proc->s p)) 'local)
      (not (erl-state->outbox (proc->s p)))
      (omap::assoc 'ParentPid (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildHd (erl-state->bind (proc->s p)))
      (omap::assoc 'ChildTl (erl-state->bind (proc->s p)))
      (omap::assoc 'LeftTotal (erl-state->bind (proc->s p)))
      (not (omap::assoc 'RightTotal (erl-state->bind (proc->s p))))
      (pid-p (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))) :cons)
      (not (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind (proc->s p)))))
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind (proc->s p)))) :integer)
      (or (pid-p (omap::lookup 'ParentPid (erl-state->bind (proc->s p)))) (equal (omap::lookup 'ParentPid (erl-state->bind (proc->s p))) (make-erl-val-atom :val 'none)))
      (wf-inbox-p (proc->inbox-new p))
      (inbox-contains (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))
    (equal
      (proc-receive p)
      (change-proc p
        :ps :terminated
        :inbox-tried nil
        :inbox-new (append (proc->inbox-tried p)
                           (inbox-without (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))))
        :s (update-erl-state->bind-mod
             (update-erl-state->outbox
               (update-erl-state->bind
                 (update-erl-state->in (proc->s p) (make-erl-val-integer :val (+ (erl-val-integer->val (omap::lookup 'LeftTotal (erl-state->bind (proc->s p)))) (erl-val-integer->val (inbox->value (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))))))
                 (omap::update 'RightTotal (inbox->value (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p)))) (erl-state->bind (proc->s p))))
               (if (pid-p (omap::lookup 'ParentPid (erl-state->bind (proc->s p))))
                   (omap::update (omap::lookup 'ParentPid (erl-state->bind (proc->s p)))
                     (list (make-erl-val-tuple
                             :lst (list (erl-state->self (proc->s p)) (make-erl-val-integer :val (+ (erl-val-integer->val (omap::lookup 'LeftTotal (erl-state->bind (proc->s p)))) (erl-val-integer->val (inbox->value (proc->inbox-new p) (omap::lookup 'ChildHd (erl-state->bind (proc->s p))))))))))
                     nil)
                 nil))
             (bind-fix rbind)
             'local))))
  :induct (receive-induct p)
  :enable (proc-receive-step proc-receive-of-match-last-car)
  :expand ((wf-inbox-p (proc->inbox-new p))
           (:free (x) (inbox-contains nil x))
           (:free (x) (inbox-contains (proc->inbox-new p) x))
           (:free (x) (inbox-without (proc->inbox-new p) x))
           (:free (x) (inbox->value (proc->inbox-new p) x))))

