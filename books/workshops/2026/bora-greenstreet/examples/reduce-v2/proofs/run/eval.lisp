; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../inv")
(include-book "../../../../evaluator/theorems/top")

; All reasoning regarding apply-k for the reduce proof.

; idle -> terminated: a node without children sends its index to its parent.
(defrule apply-k-of-idle-with-no-children
  (implies
    (and
      ; The process has no children
      (equal s (proc->s (make-reduce-proc self parent nil index)))
      (equal klst (proc->klst (make-reduce-proc self parent nil index)))
      (pid-p self) (natp index)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none))))
    (b* ((ns (apply-k s klst)))
      (and
        (not (equal (erl-val-kind (erl-state->in ns)) :receive))
        (equal (erl-state->in ns) (make-erl-val-integer :val index))
        (equal (erl-state->bind ns) (erl-state->bind s))
        (equal (erl-state->self ns) (erl-state->self s))
        (equal (erl-state->world ns) (sum-reduce-world))
        (equal (erl-state->module ns) 'local)
        (equal
          (erl-state->outbox ns)
          (if (pid-p parent)
              (omap::update parent
                (list (make-erl-val-tuple
                        :lst (list self (make-erl-val-integer :val index))))
                nil)
            nil)))))
  :enable
    (wf-state-p pid-p make-reduce-proc omap::from-lists
     apply-k-of-local-call-when-match apply-k-of-local-call-no-match
     apply-k-of-cons apply-k-of-binop-expr1 eval-guard-expr eval-bif
     eval-local-call eval-clauses eval-clauses-when-consp eval-guard
     match-args eval-match eval-guard-seq eval-guard-seq-when-consp
     omap::lookup-of-update))


; idle -> receive: a node with children runs till it receives.
(defrule apply-k-of-idle-with-children
  (implies
    (and
      ; the process has children.
      (equal s (proc->s (make-reduce-proc self parent children index)))
      (pid-lst-p children) (consp children)

      (equal klst (proc->klst (make-reduce-proc self parent children index)))
      (pid-p self) (natp index)
      (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none))))
    (b* ((ns (apply-k s klst))
         (bind (erl-state->bind ns))
         (nklst (erl-val-receive->klst (erl-state->in ns))))
      (and
        ; the process runs to a receive
        (equal (erl-val-kind (erl-state->in ns)) :receive)
        (erl-klst-p nklst)
        ; The reduce call binds these variables.
        (omap::assoc 'ParentPid bind)
        (omap::assoc 'ChildHd bind)
        (omap::assoc 'ChildTl bind)
        (omap::assoc 'LeftTotal bind)
        (not (omap::assoc 'RightTotal bind))
        ; The auxillary variables still exist.
        (equal (omap::lookup 'ParentPid bind) parent)
        (equal (omap::lookup 'ChildHd bind) (car children))
        (equal (omap::lookup 'ChildTl bind)
               (make-erl-val-cons :lst (cdr children)))
        (equal (omap::lookup 'LeftTotal bind)
               (make-erl-val-integer :val index))
        ; no messages are sent
        (equal (erl-state->outbox ns) nil)
        (equal (erl-state->self ns) (erl-state->self s))
        (equal (erl-state->world ns) (sum-reduce-world))
        (equal (erl-state->module ns) 'local)
        ; the continuation is well-formed
        (reduce-receive-klst-p nklst (erl-state->bind s))
        (equal (erl-k->fuel (car nklst)) (+ 97 (* 100 (len children)))))))
  :enable
    (reduce-receive-klst-p
     wf-state-p pid-p make-reduce-proc omap::from-lists
     apply-k-of-local-call-when-match apply-k-of-local-call-no-match
     apply-k-of-cons apply-k-of-binop-expr1 eval-guard-expr eval-bif
     eval-local-call eval-clauses eval-clauses-when-consp eval-guard
     match-args eval-match eval-guard-seq eval-guard-seq-when-consp
     omap::lookup-of-update omap::compatiblep))

; receive ----------------------------------------------------------------------

; Body of the receive clause.
(defconst *reduce-receive-body*
  '((:call sum_reduce
      (:cons (:var parentpid)
        (:cons (:var childtl)
          (:cons (:binop + (:var lefttotal) (:var righttotal)) (:nil)))))))

(local (defrule tuple-lst-of-len-2
  (implies (equal (len (erl-val-tuple->lst m)) 2)
           (and (consp (cdr (erl-val-tuple->lst m)))
                (not (cddr (erl-val-tuple->lst m)))))
  :expand ((len (erl-val-tuple->lst m))
           (len (cdr (erl-val-tuple->lst m)))
           (len (cddr (erl-val-tuple->lst m))))
  :enable erl-vlst-p))

; eval-receive of the reduce clauses with a matching message.
(defrule eval-receive-of-reduce-clauses-when-match
  (implies
    (and
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (omap::assoc 'ChildHd (erl-state->bind s))
      (equal (erl-val-kind (omap::lookup 'ChildHd (erl-state->bind s))) :pid)
      ; RightTotal is not already bound, else it would shadow the new one.
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      ; the message is from ChildHd
      (equal (car (erl-val-tuple->lst m)) (omap::lookup 'ChildHd (erl-state->bind s))))
    (and
      (equal
        (mv-nth 1 (eval-receive (update-erl-state->in s m) *reduce-receive-clauses*))
        *reduce-receive-body*)
      (equal
        (mv-nth 0 (eval-receive (update-erl-state->in s m) *reduce-receive-clauses*))
        (update-erl-state->bind (update-erl-state->in s m)
          (omap::update 'RightTotal (cadr (erl-val-tuple->lst m)) (erl-state->bind s))))))
  :enable (eval-receive eval-clauses eval-clauses-when-consp
           match-args eval-match eval-guard-seq wf-state-p))

; eval-receive of the reduce clauses with no matching message.
(defrule eval-receive-of-reduce-clauses-when-no-match
  (implies
    (and
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (omap::assoc 'ChildHd (erl-state->bind s))
      ; RightTotal is not already bound, else it would shadow the new one.
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      ; The message is not from ChildHd.
      (not (equal (car (erl-val-tuple->lst m))
                  (omap::lookup 'ChildHd (erl-state->bind s)))))
    (and
      (equal
        (mv-nth 1 (eval-receive (update-erl-state->in s m) *reduce-receive-clauses*))
        nil)
      (equal
        (mv-nth 0 (eval-receive (update-erl-state->in s m)  *reduce-receive-clauses*))
        (update-erl-state->in (erl-state-fix s) (make-erl-val-blocked)))))
  :enable (eval-receive eval-clauses eval-clauses-when-consp
           match-args eval-match eval-guard-seq wf-state-p))

; receive -> blocked: the message is not from ChildHd.
(defrule apply-k-of-receive-when-no-match
  (implies
    (and
      (reduce-receive-klst-p klst rbind)
      (erl-val-p m)
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (omap::assoc 'ChildHd (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (not (equal (car (erl-val-tuple->lst m))
                  (omap::lookup 'ChildHd (erl-state->bind s)))))
    (equal (apply-k (update-erl-state->in s m) klst)
           (update-erl-state->in (erl-state-fix s) (make-erl-val-blocked))))
  :do-not-induct t
  :use ((:instance apply-k-of-append
          (s (update-erl-state->in s m))
          (kl1 (list (car klst)))
          (kl2 (cdr klst))))
  :enable (reduce-receive-klst-p wf-state-p apply-k-of-receive-no-match)
  :disable (eval-receive eval-clauses eval-clauses-when-consp eval-match))

; receive -> receive: the message is from ChildHd but ChildTl is not empty.
(local (defrule apply-k-of-reduce-to-receive
  (implies
    (and
      (equal (erl-k->kont k) (make-kont-receive :clauses *reduce-receive-clauses*))
      (> (erl-k->fuel k) 100)
      (equal (erl-state->world s) (sum-reduce-world))
      (equal (erl-state->module s) 'local)
      (omap::assoc 'ParentPid (erl-state->bind s))
      (omap::assoc 'ChildHd (erl-state->bind s))
      (omap::assoc 'ChildTl (erl-state->bind s))
      (omap::assoc 'LeftTotal (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal (erl-val-kind (omap::lookup 'ChildHd (erl-state->bind s))) :pid)
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind s))) :cons)
      (pid-lst-p (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind s))))
      (consp (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind s))))
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind s))) :integer)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid (erl-state->bind s))) :pid)
          (equal (omap::lookup 'ParentPid (erl-state->bind s))
                 (make-erl-val-atom :val 'none)))
      (erl-val-p m) (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (equal (car (erl-val-tuple->lst m)) (omap::lookup 'ChildHd (erl-state->bind s))))
    (equal
      (apply-k (update-erl-state->in s m) (list k))
      (update-erl-state->in
        (update-erl-state->bind (erl-state-fix s)
          (omap::from-lists
            (list 'ChildHd 'ChildTl 'LeftTotal 'ParentPid)
            (list (car (erl-val-cons->lst
                         (omap::lookup 'ChildTl (erl-state->bind s))))
                  (make-erl-val-cons
                    :lst (cdr (erl-val-cons->lst
                                (omap::lookup 'ChildTl (erl-state->bind s)))))
                  (make-erl-val-integer
                    :val (+ (erl-val-integer->val
                              (omap::lookup 'LeftTotal (erl-state->bind s)))
                            (erl-val-integer->val
                              (cadr (erl-val-tuple->lst m)))))
                  (omap::lookup 'ParentPid (erl-state->bind s)))))
        (make-erl-val-receive :klst
          (list (erl-k (- (erl-k->fuel k) 4) (erl-k->kont k))
                (erl-k (- (erl-k->fuel k) 4) (make-kont-exprs :exprs nil))
                (erl-k (- (erl-k->fuel k) 3)
                       (make-kont-function-return
                         :bind (omap::update 'RightTotal
                                 (cadr (erl-val-tuple->lst m))
                                 (erl-state->bind s))
                         :module 'local))
                (erl-k (- (erl-k->fuel k) 1)
                       (make-kont-exprs :exprs nil)))))))
  :enable
    (wf-state-p pid-p omap::from-lists omap::lookup-of-update
     apply-k-of-receive-when-match match-args eval-match
     apply-k-of-local-call-when-match apply-k-of-local-call-no-match
     apply-k-of-cons apply-k-of-binop-expr1
     eval-local-call eval-clauses eval-clauses-when-consp
     eval-guard-seq eval-bif omap::compatiblep)))

; same as above, lifted to klst.
(defrule apply-k-of-reduce-to-receive-klst
  (implies
    (and
      (erl-klst-p klst) (reduce-receive-klst-p klst rbind)
      (equal (erl-state->world s) (sum-reduce-world))
      (equal (erl-state->module s) 'local)
      (omap::assoc 'ParentPid (erl-state->bind s))
      (omap::assoc 'ChildHd (erl-state->bind s))
      (omap::assoc 'ChildTl (erl-state->bind s))
      (omap::assoc 'LeftTotal (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal (erl-val-kind (omap::lookup 'ChildHd (erl-state->bind s))) :pid)
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind s))) :cons)
      (pid-lst-p (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind s))))
      (consp (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind s))))
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind s))) :integer)
      (or (equal (erl-val-kind (omap::lookup 'ParentPid (erl-state->bind s))) :pid)
          (equal (omap::lookup 'ParentPid (erl-state->bind s))
                 (make-erl-val-atom :val 'none)))
      (erl-val-p m)
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (equal (car (erl-val-tuple->lst m))
             (omap::lookup 'ChildHd (erl-state->bind s))))
    (equal
      (apply-k (update-erl-state->in s m) klst)
      (update-erl-state->in
        (update-erl-state->bind (erl-state-fix s)
          (omap::from-lists
            (list 'ChildHd 'ChildTl 'LeftTotal 'ParentPid)
            (list (car (erl-val-cons->lst
                         (omap::lookup 'ChildTl (erl-state->bind s))))
                  (make-erl-val-cons
                    :lst (cdr (erl-val-cons->lst
                                (omap::lookup 'ChildTl (erl-state->bind s)))))
                  (make-erl-val-integer
                    :val (+ (erl-val-integer->val
                              (omap::lookup 'LeftTotal (erl-state->bind s)))
                            (erl-val-integer->val
                              (cadr (erl-val-tuple->lst m)))))
                  (omap::lookup 'ParentPid (erl-state->bind s)))))
        (make-erl-val-receive :klst
          (append
            (list (erl-k (- (erl-k->fuel (car klst)) 4)
                         (erl-k->kont (car klst)))
                  (erl-k (- (erl-k->fuel (car klst)) 4)
                         (make-kont-exprs :exprs nil))
                  (erl-k (- (erl-k->fuel (car klst)) 3)
                         (make-kont-function-return
                           :bind (omap::update 'RightTotal
                                   (cadr (erl-val-tuple->lst m))
                                   (erl-state->bind s))
                           :module 'local))
                  (erl-k (- (erl-k->fuel (car klst)) 1)
                         (make-kont-exprs :exprs nil)))
            (cdr klst))))))
  :use ((:instance apply-k-of-append
          (s (update-erl-state->in s m))
          (kl1 (list (car klst)))
          (kl2 (cdr klst))))
  :enable reduce-receive-klst-p)

; receive -> terminated: the message is from the last child.

; TODO: this should already exist in eval/theorems?
(defruled apply-k-of-exprs-nil-2
  (implies
    (and
      (consp klst) (wf-state-p s)
      (not (equal (erl-val-kind (erl-state->in s)) :excpt))
      (> (erl-k->fuel (car klst)) 0)
      (equal (kont-kind (erl-k->kont (car klst))) :exprs)
      (endp (kont-exprs->exprs (erl-k->kont (car klst)))))
    (equal (apply-k s klst) (apply-k (erl-state-fix s) (cdr klst))))
  :use ((:instance apply-k-of-append (kl1 (list (car klst))) (kl2 (cdr klst))))
  :enable wf-state-p)

; TODO: this should already exist in eval/theorems?
(defruled apply-k-of-function-return-2
  (implies
    (and
      (consp klst) (wf-state-p s)
      (> (erl-k->fuel (car klst)) 0)
      (equal (kont-kind (erl-k->kont (car klst))) :function-return))
    (equal
      (apply-k s klst)
      (apply-k
        (update-erl-state->bind-mod
          (erl-state-fix s)
          (kont-function-return->bind (erl-k->kont (car klst)))
          (kont-function-return->module (erl-k->kont (car klst))))
        (cdr klst))))
  :use ((:instance apply-k-of-append
          (kl1 (list (car klst))) (kl2 (cdr klst)))))

(local (defruled apply-k-of-reduce-klst-lst-p
  (implies
    (and
      (erl-klst-p klst) (wf-state-p s)
      (not (equal (erl-val-kind (erl-state->in s)) :excpt))
      (reduce-klst-lst-p klst rbind))
    (equal
      (apply-k s klst)
      (update-erl-state->bind-mod
        (erl-state-fix s)
        (bind-fix rbind)
        'local)))
  :induct (tmp-induct s klst)
  :enable (reduce-klst-lst-p apply-k-of-exprs-nil-2
           apply-k-of-function-return-2 wf-state-p
           update-erl-state->bind-mod)
  :prep-lemmas
    ((defun tmp-induct (s klst)
      (declare (xargs :measure (len (erl-klst-fix klst))))
      (b* ((klst (erl-klst-fix klst))
           ((unless (<= 3 (len klst))) s))
          (tmp-induct
            (update-erl-state->bind-mod s
              (kont-function-return->bind (erl-k->kont (caddr klst))) 'local)
            (cdddr klst)))))))

(local (defrule apply-k-of-reduce-receive-to-terminate
  (implies
    (and 
      (equal
        (erl-k->kont k)
        (make-kont-receive :clauses *reduce-receive-clauses*))
      (> (erl-k->fuel k) 100)
      (equal (erl-state->world s) (sum-reduce-world))
      (equal (erl-state->module s) 'local)
      (not (erl-state->outbox s))
      (omap::assoc 'ParentPid (erl-state->bind s))
      (omap::assoc 'ChildHd (erl-state->bind s))
      (omap::assoc 'ChildTl (erl-state->bind s))
      (omap::assoc 'LeftTotal (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal (erl-val-kind (omap::lookup 'ChildHd (erl-state->bind s))) :pid)
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind s))) :cons)
      (not (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind s))))
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind s))) :integer)
      (or (pid-p (omap::lookup 'ParentPid (erl-state->bind s)))
          (equal (omap::lookup 'ParentPid (erl-state->bind s))
                 (make-erl-val-atom :val 'none)))
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer)
      (equal (car (erl-val-tuple->lst m))
             (omap::lookup 'ChildHd (erl-state->bind s))))
    (equal
      (apply-k (update-erl-state->in s m) (list k))
      (update-erl-state->outbox
        (update-erl-state->bind
          (update-erl-state->in (erl-state-fix s)
            (make-erl-val-integer
              :val (+ (erl-val-integer->val
                        (omap::lookup 'LeftTotal (erl-state->bind s)))
                      (erl-val-integer->val
                        (cadr (erl-val-tuple->lst m))))))
          (omap::update 'RightTotal
            (cadr (erl-val-tuple->lst m)) (erl-state->bind s)))
        (if (pid-p (omap::lookup 'ParentPid (erl-state->bind s)))
            (omap::update (omap::lookup 'ParentPid (erl-state->bind s))
              (list
                (make-erl-val-tuple
                  :lst
                    (list
                      (erl-state->self s)
                      (make-erl-val-integer
                        :val (+ (erl-val-integer->val
                                  (omap::lookup 'LeftTotal (erl-state->bind s)))
                                (erl-val-integer->val (cadr (erl-val-tuple->lst m))))))))
              nil)
          nil))))
  :enable
    (wf-state-p pid-p erl-state-send match-args eval-match eval-bif
     update-erl-state->bind-mod omap::from-lists omap::lookup-of-update
     eval-clauses-when-consp apply-k-of-receive-when-match
     eval-local-call eval-guard-seq apply-k-of-local-call-when-match
     apply-k-of-binop-expr1 apply-k-of-local-call-no-match
     apply-k-of-cons eval-clauses)))

; receive -> terminated/blocked, lifted to klst
(defrule apply-k-of-reduce-receive-klst
  (implies
    (and
      (erl-klst-p klst) (reduce-receive-klst-p klst rbind)
      (equal (erl-state->world s) (sum-reduce-world))
      (equal (erl-state->module s) 'local)
      (not (erl-state->outbox s))
      (omap::assoc 'ParentPid (erl-state->bind s))
      (omap::assoc 'ChildHd (erl-state->bind s))
      (omap::assoc 'ChildTl (erl-state->bind s))
      (omap::assoc 'LeftTotal (erl-state->bind s))
      (not (omap::assoc 'RightTotal (erl-state->bind s)))
      (equal (erl-val-kind (omap::lookup 'ChildHd (erl-state->bind s))) :pid)
      (equal (erl-val-kind (omap::lookup 'ChildTl (erl-state->bind s))) :cons)
      (not (erl-val-cons->lst (omap::lookup 'ChildTl (erl-state->bind s))))
      (equal (erl-val-kind (omap::lookup 'LeftTotal (erl-state->bind s))) :integer)
      (or (pid-p (omap::lookup 'ParentPid (erl-state->bind s)))
          (equal (omap::lookup 'ParentPid (erl-state->bind s))
                 (make-erl-val-atom :val 'none)))
      (equal (erl-val-kind m) :tuple)
      (equal (len (erl-val-tuple->lst m)) 2)
      (equal (erl-val-kind (cadr (erl-val-tuple->lst m))) :integer))
    (equal
      (apply-k (update-erl-state->in s m) klst)
      (if (equal (car (erl-val-tuple->lst m))
                 (omap::lookup 'ChildHd (erl-state->bind s)))
          (update-erl-state->bind-mod
            (update-erl-state->outbox
              (update-erl-state->bind
                (update-erl-state->in (erl-state-fix s)
                  (make-erl-val-integer
                    :val (+ (erl-val-integer->val
                              (omap::lookup 'LeftTotal
                                (erl-state->bind s)))
                            (erl-val-integer->val
                              (cadr (erl-val-tuple->lst m))))))
                (omap::update 'RightTotal
                  (cadr (erl-val-tuple->lst m)) (erl-state->bind s)))
              (if (pid-p (omap::lookup 'ParentPid (erl-state->bind s)))
                  (omap::update (omap::lookup 'ParentPid (erl-state->bind s))
                    (list
                      (make-erl-val-tuple
                        :lst
                          (list
                            (erl-state->self s)
                            (make-erl-val-integer
                              :val (+ (erl-val-integer->val
                                        (omap::lookup 'LeftTotal
                                          (erl-state->bind s)))
                                      (erl-val-integer->val
                                        (cadr (erl-val-tuple->lst m))))))))
                    nil)
                nil))
            (bind-fix rbind)
            'local)
          (update-erl-state->in
            (erl-state-fix s) (make-erl-val-blocked)))))
  :enable
    (reduce-receive-klst-p wf-state-p
     apply-k-of-exprs-nil-2 apply-k-of-function-return-2
     apply-k-of-reduce-klst-lst-p
     update-erl-state->bind-mod)
  :use ((:instance apply-k-of-append
          (s (update-erl-state->in s m))
          (kl1 (list (car klst)))
          (kl2 (cdr klst)))))
