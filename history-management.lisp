; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; Section:  Proof Trees

; We develop proof trees in this file, rather than in prove.lisp, because
; print-summary calls print-proof-tree.

; A goal tree is a structure of the following form, with the fields indicated
; below.  We put the two non-changing fields at the end; note:

; ACL2 p>:sbt 4
;
; The Binary Trees with Four Tips
; 2.000  ((2 . 2) 2 . 2)
; 2.250  (1 2 3 . 3)

(defrec goal-tree (children processor cl-id . fanout) nil)

; Cl-id is a clause-id record for the name of the goal.

; Children is a list of goal trees whose final cdr is either nil or a positive
; integer.  In the latter case, this positive integer indicates the remaining
; number of children for which to build goal trees.

; Fanout is the original number of children.

; Processor is one of the processors from *preprocess-clause-ledge* (except for
; settled-down-clause, which has no use here), except that we have two special
; annotations and two "fictitious" processors.

; Instead of push-clause, we use (push-clause cl-id), where cl-id is the
; clause-id of the clause pushed (e.g., the clause-id corresponding to "*1").
; Except: (push-clause cl-id :REVERT) is used when we are reverting to the
; original goal, and in this case, cl-id always corresponds to *1; also,
; (push-clause cl-id :ABORT) is used when the proof is aborted by push-clause.

; Instead of a processor pr, we may have (pr :forced), which indicates that
; this processor forced assumptions (but remember, some of those might get
; proved during the final clean-up phase).  When we enter the next forcing
; round, we will "decorate" the above "processor" by adding a list of new goals
; created by that forcing: (pr :forced clause-id_1 ... clause-id_n).  As we go
; along we may prune away some of those new clause ids.

; Finally, occasionally the top-level node in a goal-tree is "fictitious", such
; as the one for "[1]Goal" if the first forcing round presented more than one
; forced goal, and such as any goal to be proved by induction.  In that case,
; the "processor" is one of the keyword labels :INDUCT or :FORCING-ROUND or a
; list headed by such keywords, e.g. if we want to say what induction scheme is
; being used.

; A proof tree is simply a non-empty list of goal trees.  The "current" goal
; tree is the CAR of the current proof tree; it's the one for the current
; forcing round or proof by induction.

; There is always a current proof tree, (@ proof-tree), except when we are
; inhibiting proof-tree output or are not yet in a proof.  The current goal in
; a proof is always the first one associated with the first subtree of the
; current goal-tree that has a non-nil final CDR, via a left-to-right
; depth-first traversal of that tree.  We keep the proof tree pruned, trimming
; away proved subgoals and their children.

; The proof tree is printed to the screen, enclosed in #\n\<0 ... #\n\>.  We
; start with # because that seems like a rare character, and we want to leave
; emacs as unburdened as possible in its use of string-matching.  And, we put a
; newline in front of \ because in ordinary PRINT-like (as opposed to
; PRINC-like) printing, as done by the prover, \ is always quoted and hence
; would not appear in a sequence such as <newline>\?, where ? is any character
; besides \.  Naturally, this output can be inhibited, simply by putting
; 'proof-tree on the state global variable inhibit-output-lst.  Mike Smith has
; built, and we have modified, a "filter" tool for redirecting such output in a
; nice form to appropriate emacs buffers.  People who do not want to use the
; emacs facility (or some other display utility) should probably inhibit
; proof-tree output using :stop-proof-tree.

(defun start-proof-tree-fn (remove-inhibit-p state)

; Note that we do not override existing values of the indicated state global
; variables.

  (if remove-inhibit-p
      (f-put-global 'inhibit-output-lst
                    (remove1-eq 'proof-tree
                                (f-get-global 'inhibit-output-lst state))
                    state)
    state))

#+acl2-loop-only
(defmacro start-proof-tree ()
  '(pprogn (start-proof-tree-fn t state)
           (fms "Proof tree output is now enabled.  Note that ~
                 :START-PROOF-TREE works by removing 'proof-tree from ~
                 the inhibit-output-lst; see :DOC ~
                 set-inhibit-output-lst.~%"
                nil
                (standard-co state)
                state
                nil)
           (value :invisible)))

#-acl2-loop-only
(defmacro start-proof-tree ()
  '(let ((state *the-live-state*))
     (fms "IT IS ILLEGAL to invoke (START-PROOF-TREE) from raw Lisp.  Please ~
           first enter the ACL2 command loop with (LP)."
          nil
          (proofs-co state)
          state
          nil)
     (values)))

(defmacro checkpoint-forced-goals (val)
  `(pprogn (f-put-global 'checkpoint-forced-goals ',val state)
           (value ',val)))

(defun stop-proof-tree-fn (state)
  (f-put-global 'inhibit-output-lst
                (add-to-set-eq 'proof-tree
                               (f-get-global 'inhibit-output-lst state))
                state))

(defmacro stop-proof-tree ()
  '(pprogn (stop-proof-tree-fn state)
           (fms "Proof tree output is now inhibited.  Note that ~
                 :STOP-PROOF-TREE works by adding 'proof-tree to the ~
                 inhibit-output-lst; see :DOC set-inhibit-output-lst.~%"
                nil
                (standard-co state)
                state
                nil)
           (value :invisible)))

(mutual-recursion

(defun insert-into-goal-tree-rec (cl-id processor n goal-tree)
  (let ((new-children (insert-into-goal-tree-lst
                       cl-id processor n
                       (access goal-tree goal-tree :children))))
    (and new-children
         (change goal-tree goal-tree
                 :children new-children))))

(defun insert-into-goal-tree-lst (cl-id processor n goal-tree-lst)
  (cond
   ((consp goal-tree-lst)
    (let ((new-child (insert-into-goal-tree-rec
                      cl-id processor n (car goal-tree-lst))))
      (if new-child
          (cons new-child (cdr goal-tree-lst))
        (let ((rest-children (insert-into-goal-tree-lst
                              cl-id processor n (cdr goal-tree-lst))))
          (if rest-children
              (cons (car goal-tree-lst) rest-children)
            nil)))))
   ((integerp goal-tree-lst)
    (cons (make goal-tree
                :cl-id cl-id
                :processor processor
                :children n
                :fanout (or n 0))
          (if (eql goal-tree-lst 1)
              nil
            (1- goal-tree-lst))))
   (t nil)))
)

(defun insert-into-goal-tree (cl-id processor n goal-tree)

; This function updates the indicated goal-tree by adding a new goal tree built
; from cl-id, processor, and n, in place of the first integer "children" field
; of a subgoal in a left-to-right depth-first traversal of the goal-tree.
; (Recall that an integer represents the number of unproved children remaining;
; hence the first integer found corresponds to the goal that corresponds to the
; parameters of this function.)  However, we return nil if no integer
; "children" field is found; similarly for the -rec and -lst versions, above.

; Note that n should be nil or a (strictly) positive integer.  Also note that
; when cl-id is *initial-clause-id*, then goal-tree doesn't matter (for
; example, it may be nil).

  (cond
   ((equal cl-id *initial-clause-id*)
    (make goal-tree
          :cl-id cl-id
          :processor processor
          :children n
          :fanout (or n 0)))
   (t (insert-into-goal-tree-rec cl-id processor n goal-tree))))

(defun set-difference-equal-changedp (l1 l2)

; Like set-difference-equal, but returns (mv changedp lst) where lst is the set
; difference and changedp is t iff the set difference is not equal to l1.

  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2))))
  (cond ((endp l1) (mv nil nil))
        (t (mv-let (changedp lst)
                   (set-difference-equal-changedp (cdr l1) l2)
                   (cond
                    ((member-equal (car l1) l2)
                     (mv t lst))
                    (changedp (mv t (cons (car l1) lst)))
                    (t (mv nil l1)))))))

(mutual-recursion

(defun prune-goal-tree (forcing-round dead-clause-ids goal-tree)

; Removes all proved goals from a goal tree, where all dead-clause-ids are
; considered proved.  Actually returns two values:  a new goal tree (or nil),
; and a new (extended) list of dead-clause-ids.

; Goals with processor (push-clause id . x) are handled similarly to forced
; goals, except that we know that there is a unique child.

; Note that a non-nil final cdr prevents a goal from being considered proved
; (unless its clause-id is dead, which shouldn't happen), which is appropriate.

  (let* ((processor (access goal-tree goal-tree :processor))
         (cl-id (access goal-tree goal-tree :cl-id))
         (goal-forcing-round (access clause-id cl-id :forcing-round)))
    (cond ((member-equal cl-id dead-clause-ids)
           (mv (er hard 'prune-goal-tree
                   "Surprise!  We didn't think this case could occur.")
               dead-clause-ids))
          ((and (not (= forcing-round goal-forcing-round))

; So, current goal is from a previous forcing round.

                (consp processor)
                (eq (cadr processor) :forced))

; So, processor is of the form (pr :forced clause-id_1 ... clause-id_n).

           (mv-let
            (changedp forced-clause-ids)
            (set-difference-equal-changedp (cddr processor) dead-clause-ids)
            (cond
             ((null forced-clause-ids)
              (mv nil (cons cl-id dead-clause-ids)))

; Notice that goal-tree may have children, even though it comes from an earlier
; forcing round, because it may have generated children that themselves did
; some forcing.

             (t
              (mv-let
               (children new-dead-clause-ids)
               (prune-goal-tree-lst
                forcing-round
                dead-clause-ids
                (access goal-tree goal-tree :children))
               (cond
                (changedp
                 (mv (change goal-tree goal-tree
                             :processor
                             (list* (car processor) :forced forced-clause-ids)
                             :children children)
                     new-dead-clause-ids))
                (t (mv (change goal-tree goal-tree
                               :children children)
                       new-dead-clause-ids))))))))
          ((and (consp processor)
                (eq (car processor) 'push-clause))
           (assert$
            (null (access goal-tree goal-tree :children))

; It is tempting also to assert (null (cddr processor)), i.e., that we have not
; reverted or aborted.  But that can fail for a branch of a disjunctive (:or)
; split.

            (if (member-equal (cadr processor) dead-clause-ids)
                (mv nil (cons cl-id dead-clause-ids))
              (mv goal-tree dead-clause-ids))))
          (t
           (mv-let (children new-dead-clause-ids)
                   (prune-goal-tree-lst forcing-round
                                        dead-clause-ids
                                        (access goal-tree goal-tree :children))
                   (cond
                    ((or children

; Note that the following test implies that we're in the current forcing round,
; and hence "decoration" (adding a list of new goals created by that forcing)
; has not yet been done.

                         (and (consp processor)
                              (eq (cadr processor) :forced)))
                     (mv (change goal-tree goal-tree
                                 :children children)
                         new-dead-clause-ids))
                    (t (mv nil (cons cl-id new-dead-clause-ids)))))))))

(defun prune-goal-tree-lst (forcing-round dead-clause-ids goal-tree-lst)
  (cond
   ((consp goal-tree-lst)
    (mv-let (x new-dead-clause-ids)
            (prune-goal-tree forcing-round dead-clause-ids (car goal-tree-lst))
            (if x
                (mv-let (rst newer-dead-clause-ids)
                        (prune-goal-tree-lst
                         forcing-round new-dead-clause-ids (cdr goal-tree-lst))
                        (mv (cons x rst)
                            newer-dead-clause-ids))
              (prune-goal-tree-lst
               forcing-round new-dead-clause-ids (cdr goal-tree-lst)))))
   (t (mv goal-tree-lst dead-clause-ids))))

)

(defun prune-proof-tree (forcing-round dead-clause-ids proof-tree)
  (if (null proof-tree)
      nil
    (mv-let (new-goal-tree new-dead-clause-ids)
            (prune-goal-tree forcing-round dead-clause-ids (car proof-tree))
            (if new-goal-tree
                (cons new-goal-tree
                      (prune-proof-tree forcing-round
                                        new-dead-clause-ids
                                        (cdr proof-tree)))
              (prune-proof-tree forcing-round
                                new-dead-clause-ids
                                (cdr proof-tree))))))

(defun print-string-repeat (increment level col channel state)
  (declare (type (signed-byte 30) col level))
  (the2s
   (signed-byte 30)
   (if (= level 0)
       (mv col state)
     (mv-letc (col state)
              (fmt1 "~s0"
                    (list (cons #\0 increment))
                    col channel state nil)
              (print-string-repeat increment (1-f level) col channel state)))))

(defconst *format-proc-alist*
  '((apply-top-hints-clause-or-hit . ":OR")
    (apply-top-hints-clause . "top-level-hints")
    (preprocess-clause . "preprocess")
    (simplify-clause . "simp")
    ;;settled-down-clause
    (eliminate-destructors-clause . "ELIM")
    (fertilize-clause . "FERT")
    (generalize-clause . "GEN")
    (eliminate-irrelevance-clause . "IRREL")
    ;;push-clause
    ))

(defun format-forced-subgoals (clause-ids col max-col channel state)

; Print the "(FORCED ...)" annotation, e.g., the part after "(FORCED" on this
; line:

;   0 |  Subgoal 3 simp (FORCED [1]Subgoal 1)

  (cond
   ((null clause-ids)
    (princ$ ")" channel state))
   (t (let ((goal-name (string-for-tilde-@-clause-id-phrase (car clause-ids))))
        (if (or (null max-col)

; We must leave room for final " ...)" if there are more goals, in addition to
; the space, the goal name, and the comma.  Otherwise, we need room for the
; space and the right paren.

                (if (null (cdr clause-ids))
                    (<= (+ 2 col (length goal-name)) max-col)
                  (<= (+ 7 col (length goal-name)) max-col)))
            (mv-let (col state)
                    (fmt1 " ~s0~#1~[~/,~]"
                          (list (cons #\0 goal-name)
                                (cons #\1 clause-ids))
                          col channel state nil)
                    (format-forced-subgoals
                     (cdr clause-ids) col max-col channel state))
          (princ$ " ...)" channel state))))))

(defun format-processor (col goal-tree channel state)
  (let ((proc (access goal-tree goal-tree :processor)))
    (cond
     ((consp proc)
      (cond
       ((eq (car proc) 'push-clause)
        (mv-let
         (col state)
         (fmt1 "~s0 ~@1"
               (list (cons #\0 "PUSH")
                     (cons #\1
                           (cond
                            ((eq (caddr proc) :REVERT)
                             "(reverting)")
                            ((eq (caddr proc) :ABORT)
                             "*ABORTING*")
                            (t
                             (tilde-@-pool-name-phrase
                              (access clause-id
                                      (cadr proc)
                                      :forcing-round)
                              (access clause-id
                                      (cadr proc)
                                      :pool-lst))))))
               col channel state nil)
         (declare (ignore col))
         state))
       ((eq (cadr proc) :forced)
        (mv-let (col state)
                (fmt1 "~s0 (FORCED"

; Note that (car proc) is in *format-proc-alist*, because neither push-clause
; nor either of the "fake" processors (:INDUCT, :FORCING-ROUND) forces in the
; creation of subgoals.

                      (list (cons #\0 (cdr (assoc-eq (car proc)
                                                     *format-proc-alist*))))
                      col channel state nil)
                (format-forced-subgoals
                 (cddr proc) col
                 (f-get-global 'proof-tree-buffer-width state)
                 channel state)))
       (t (let ((err (er hard 'format-processor
                         "Unexpected shape for goal-tree processor, ~x0"
                         proc)))
            (declare (ignore err))
            state))))
     (t (princ$ (or (cdr (assoc-eq proc *format-proc-alist*))
                    proc)
                channel state)))))

(mutual-recursion

(defun format-goal-tree-lst
  (goal-tree-lst level fanout increment checkpoints
                 checkpoint-forced-goals channel state)
  (cond
   ((null goal-tree-lst)
    state)
   ((atom goal-tree-lst)
    (mv-let (col state)
            (pprogn (princ$ "     " channel state)
                    (print-string-repeat
                     increment
                     (the-fixnum! level 'format-goal-tree-lst)
                     5 channel state))
            (mv-let (col state)
                    (fmt1 "<~x0 ~#1~[~/more ~]subgoal~#2~[~/s~]>~%"
                          (list (cons #\0 goal-tree-lst)
                                (cons #\1 (if (= fanout goal-tree-lst) 0 1))
                                (cons #\2 (if (eql goal-tree-lst 1)
                                              0
                                            1)))
                          col channel state nil)
                    (declare (ignore col))
                    state)))
   (t
    (pprogn
     (format-goal-tree
      (car goal-tree-lst) level increment checkpoints
      checkpoint-forced-goals channel state)
     (format-goal-tree-lst
      (cdr goal-tree-lst) level fanout increment checkpoints
      checkpoint-forced-goals channel state)))))

(defun format-goal-tree (goal-tree level increment checkpoints
                                   checkpoint-forced-goals channel state)
  (let* ((cl-id (access goal-tree goal-tree :cl-id))
         (pool-lst (access clause-id cl-id :pool-lst))
         (fanout (access goal-tree goal-tree :fanout))
         (raw-processor (access goal-tree goal-tree :processor))
         (processor (if (atom raw-processor)
                        raw-processor
                      (car raw-processor))))
    (mv-letc
     (col state)
     (pprogn (mv-letc
              (col state)
              (fmt1 "~#0~[c~/ ~]~c1 "
                    (list (cons #\0 (if (or (member-eq processor checkpoints)
                                            (and checkpoint-forced-goals
                                                 (consp raw-processor)
                                                 (eq (cadr raw-processor)
                                                     :forced)))
                                        0
                                      1))
                          (cons #\1 (cons fanout 3)))
                    0 channel state nil)
              (print-string-repeat increment
                                   (the-fixnum! level 'format-goal-tree)
                                   col channel state)))
     (mv-letc
      (col state)
      (if (and (null (access clause-id cl-id :case-lst))
               (= (access clause-id cl-id :primes) 0)
               pool-lst)
          (fmt1 "~@0 "
                (list (cons #\0 (tilde-@-pool-name-phrase
                                 (access clause-id cl-id :forcing-round)
                                 pool-lst)))
                col channel state nil)
        (fmt1 "~@0 "
              (list (cons #\0 (tilde-@-clause-id-phrase cl-id)))
              col channel state nil))
      (pprogn
       (format-processor col goal-tree channel state)
       (pprogn
        (newline channel state)
        (format-goal-tree-lst
         (access goal-tree goal-tree :children)
         (1+ level) fanout increment checkpoints checkpoint-forced-goals
         channel state)))))))

)

(defun format-proof-tree (proof-tree-rev increment checkpoints
                                         checkpoint-forced-goals channel state)

; Recall that most recent forcing rounds correspond to the goal-trees closest
; to the front of a proof-tree.  But here, proof-tree-rev is the reverse of a
; proof-tree.

  (if (null proof-tree-rev)
      state
    (pprogn (format-goal-tree
             (car proof-tree-rev) 0 increment checkpoints
             checkpoint-forced-goals channel state)
            (if (null (cdr proof-tree-rev))
                state
              (mv-let (col state)
                      (fmt1 "++++++++++++++++++++++++++++++~%"
                            nil 0 channel state nil)
                      (declare (ignore col))
                      state))
            (format-proof-tree
             (cdr proof-tree-rev) increment checkpoints
             checkpoint-forced-goals channel state))))

(defun print-proof-tree1 (ctx channel state)
  (let ((proof-tree (f-get-global 'proof-tree state)))
    (if (null proof-tree)
        (if (and (consp ctx) (eq (car ctx) :failed))
            state
          (princ$ "Q.E.D." channel state))
      (format-proof-tree (reverse proof-tree)
                         (f-get-global 'proof-tree-indent state)
                         (f-get-global 'checkpoint-processors state)
                         (f-get-global 'checkpoint-forced-goals state)
                         channel
                         state))))

(defconst *proof-failure-string*
  "******** FAILED ********~|")

(defun print-proof-tree-ctx (ctx channel state)
  (let* ((failed-p (and (consp ctx) (eq (car ctx) :failed)))
         (actual-ctx (if failed-p (cdr ctx) ctx)))
    (mv-let
     (erp val state)
     (state-global-let*
      ((fmt-hard-right-margin 1000 set-fmt-hard-right-margin)
       (fmt-soft-right-margin 1000 set-fmt-soft-right-margin))

; We need the event name to fit on a single line, hence the state-global-let*
; above.

      (mv-let (col state)
              (fmt-ctx actual-ctx 0 channel state)
              (mv-let
               (col state)
               (fmt1 "~|~@0"
                     (list (cons #\0
                                 (if failed-p *proof-failure-string* "")))
                     col channel state nil)
               (declare (ignore col))
               (value nil))))
     (declare (ignore erp val))
     state)))

(defconst *proof-tree-start-delimiter* "#<\\<0")

(defconst *proof-tree-end-delimiter* "#>\\>")

(defun print-proof-tree-finish (state)
  (if (f-get-global 'proof-tree-start-printed state)
      (pprogn (mv-let (col state)
                      (fmt1! "~s0"
                             (list (cons #\0 *proof-tree-end-delimiter*))
                             0 (proofs-co state) state nil)
                      (declare (ignore col))
                      (f-put-global 'proof-tree-start-printed nil state)))
    state))

(defun print-proof-tree (state)

; WARNING: Every call of print-proof-tree should be underneath some call of the
; form (io? ...).  We thus avoid enclosing the body below with (io? proof-tree
; ...).

  (let ((chan (proofs-co state))
        (ctx (f-get-global 'proof-tree-ctx state)))
    (pprogn
     (if (f-get-global 'window-interfacep state)
         state
       (pprogn
        (f-put-global 'proof-tree-start-printed t state)
        (mv-let (col state)
                (fmt1 "~s0"
                      (list (cons #\0 *proof-tree-start-delimiter*))
                      0 chan state nil)
                (declare (ignore col)) ;print-proof-tree-ctx starts with newline
                state)))
     (print-proof-tree-ctx ctx chan state)
     (print-proof-tree1 ctx chan state)
     (print-proof-tree-finish state))))

(mutual-recursion

(defun decorate-forced-goals-1 (goal-tree clause-id-list forced-clause-id)
  (let ((cl-id (access goal-tree goal-tree :cl-id))
        (new-children (decorate-forced-goals-1-lst
                       (access goal-tree goal-tree :children)
                       clause-id-list
                       forced-clause-id)))
    (cond
     ((member-equal cl-id clause-id-list)
      (let ((processor (access goal-tree goal-tree :processor)))
        (change goal-tree goal-tree
                :processor
                (list* (car processor) :forced forced-clause-id (cddr processor))
                :children new-children)))
     (t
      (change goal-tree goal-tree
              :children new-children)))))

(defun decorate-forced-goals-1-lst
  (goal-tree-lst clause-id-list forced-clause-id)
  (cond
   ((null goal-tree-lst)
    nil)
   ((atom goal-tree-lst)

; By the time we've gotten this far, we've gotten to the next forcing round,
; and hence there shouldn't be any children remaining to process.  Of course, a
; forced goal can generate forced subgoals, so we can't say that there are no
; children -- but we CAN say that there are none remaining to process.

    (er hard 'decorate-forced-goals-1-lst
        "Unexpected goal-tree in call ~x0"
        (list 'decorate-forced-goals-1-lst
              goal-tree-lst
              clause-id-list
              forced-clause-id)))
   (t (cons (decorate-forced-goals-1
             (car goal-tree-lst) clause-id-list forced-clause-id)
            (decorate-forced-goals-1-lst
             (cdr goal-tree-lst) clause-id-list forced-clause-id)))))

)

(defun decorate-forced-goals (forcing-round goal-tree clause-id-list-list n)

; See decorate-forced-goals-in-proof-tree.

  (if (null clause-id-list-list)
      goal-tree
    (decorate-forced-goals
     forcing-round
     (decorate-forced-goals-1 goal-tree
                              (car clause-id-list-list)
                              (make clause-id
                                    :forcing-round forcing-round
                                    :pool-lst nil
                                    :case-lst (and n (list n))
                                    :primes 0))
     (cdr clause-id-list-list)
     (and n (1- n)))))

(defun decorate-forced-goals-in-proof-tree
  (forcing-round proof-tree clause-id-list-list n)

; This function decorates the goal trees in proof-tree so that the appropriate
; previous forcing round's goals are "blamed" for the new forcing round goals.
; See also extend-proof-tree-for-forcing-round.

; At the top level, n is either an integer greater than 1 or else is nil.  This
; corresponds respectively to whether or not there is more than one goal
; produced by the forcing round.

  (if (null proof-tree)
      nil
    (cons (decorate-forced-goals
           forcing-round (car proof-tree) clause-id-list-list n)
          (decorate-forced-goals-in-proof-tree
           forcing-round (cdr proof-tree) clause-id-list-list n))))

(defun assumnote-list-to-clause-id-list (assumnote-list)
  (if (null assumnote-list)
      nil
    (cons (access assumnote (car assumnote-list) :cl-id)
          (assumnote-list-to-clause-id-list (cdr assumnote-list)))))

(defun assumnote-list-list-to-clause-id-list-list (assumnote-list-list)
  (if (null assumnote-list-list)
      nil
    (cons (assumnote-list-to-clause-id-list (car assumnote-list-list))
          (assumnote-list-list-to-clause-id-list-list (cdr assumnote-list-list)))))

(defun extend-proof-tree-for-forcing-round
  (forcing-round parent-clause-id clause-id-list-list state)

; This function pushes a new goal tree onto the global proof-tree.  However, it
; decorates the existing goal trees so that the appropriate previous forcing
; round's goals are "blamed" for the new forcing round goals.  Specifically, a
; previous goal with clause id in a member of clause-id-list-list is blamed for
; creating the appropriate newly-forced goal, with (car clause-id-list-list)
; associated with the highest-numbered (first) forced goal, etc.

  (cond
   ((null clause-id-list-list)

; then the proof is complete!

    state)
   (t
    (let ((n (length clause-id-list-list))) ;note n>0
      (f-put-global
       'proof-tree
       (cons (make goal-tree
                   :cl-id parent-clause-id
                   :processor :FORCING-ROUND
                   :children n
                   :fanout n)
             (decorate-forced-goals-in-proof-tree
              forcing-round
              (f-get-global 'proof-tree state)
              clause-id-list-list
              (if (null (cdr clause-id-list-list))
                  nil
                (length clause-id-list-list))))
       state)))))

(defun initialize-proof-tree1 (parent-clause-id x pool-lst forcing-round ctx
                                                state)

; X is from the "x" argument of waterfall.  Thus, if we are starting a forcing
; round then x is list of pairs (assumnote-lst . clause) where the clause-ids
; from the assumnotes are the names of goals from the preceding forcing round
; to "blame" for the creation of that clause.

  (pprogn

; The user might have started up proof trees with something like (assign
; inhibit-output-lst nil).  In that case we need to ensure that appropriate
; state globals are initialized.  Note that start-proof-tree-fn does not
; override existing bindings of those state globals (which the user may have
; deliberately set).

   (start-proof-tree-fn nil state)
   (f-put-global 'proof-tree-ctx ctx state)
   (cond
    ((and (null pool-lst)
          (eql forcing-round 0))
     (f-put-global 'proof-tree nil state))
    (pool-lst
     (f-put-global 'proof-tree
                   (cons (let ((n (length x)))
                           (make goal-tree
                                 :cl-id parent-clause-id
                                 :processor :INDUCT
                                 :children (if (= n 0) nil n)
                                 :fanout n))
                         (f-get-global 'proof-tree state))
                   state))
    (t
     (extend-proof-tree-for-forcing-round
      forcing-round parent-clause-id
      (assumnote-list-list-to-clause-id-list-list (strip-cars x))
      state)))))

(defun initialize-proof-tree (parent-clause-id x ctx state)

; X is from the "x" argument of waterfall.  See initialize-proof-tree1.

; We assume (not (output-ignored-p 'proof-tree state)).

  (let ((pool-lst (access clause-id parent-clause-id :pool-lst))
        (forcing-round (access clause-id parent-clause-id
                               :forcing-round)))
    (pprogn
     (io? proof-tree nil state
          (ctx forcing-round pool-lst x parent-clause-id)
          (initialize-proof-tree1 parent-clause-id x pool-lst forcing-round ctx
                                  state))
     (io? prove nil state
          (forcing-round pool-lst)
          (cond ((intersectp-eq '(prove proof-tree)
                                (f-get-global 'inhibit-output-lst state))
                 state)
                ((and (null pool-lst)
                      (eql forcing-round 0))
                 (fms "<< Starting proof tree logging >>~|"
                      nil (proofs-co state) state nil))
                (t state))))))

(defconst *star-1-clause-id*
  (make clause-id
        :forcing-round 0
        :pool-lst '(1)
        :case-lst nil
        :primes 0))

(mutual-recursion

(defun revert-goal-tree-rec (cl-id revertp goal-tree)

; See revert-goal-tree.  This nest also returns a value cl-id-foundp, which is
; nil if the given cl-id was not found in goal-tree or any subsidiary goal
; trees, else :or-found if cl-id is found under a disjunctive split, else t.

  (let ((processor (access goal-tree goal-tree :processor)))
    (cond
     ((and (consp processor)
           (eq (car processor) 'push-clause))
      (mv (equal cl-id (access goal-tree goal-tree :cl-id))
          (if revertp
              (change goal-tree goal-tree
                      :processor
                      (list 'push-clause *star-1-clause-id* :REVERT))
            goal-tree)))
     (t (mv-let (cl-id-foundp new-children)
                (revert-goal-tree-lst (eq processor
                                          'apply-top-hints-clause-or-hit)
                                      cl-id
                                      revertp
                                      (access goal-tree goal-tree :children))
                (mv cl-id-foundp
                    (change goal-tree goal-tree :children new-children)))))))

(defun revert-goal-tree-lst (or-p cl-id revertp goal-tree-lst)

; Or-p is true if we want to limit changes to the member of goal-tree-lst that
; is, or has a subsidiary, goal-tree for cl-id.

  (cond
   ((atom goal-tree-lst)
    (mv nil nil))
   (t (mv-let (cl-id-foundp new-goal-tree)
              (revert-goal-tree-rec cl-id revertp (car goal-tree-lst))
              (cond ((or (eq cl-id-foundp :or-found)
                         (and cl-id-foundp or-p))
                     (mv :or-found
                         (cons new-goal-tree (cdr goal-tree-lst))))
                    (t (mv-let (cl-id-foundp2 new-goal-tree-lst)
                               (revert-goal-tree-lst or-p
                                                     cl-id
                                                     revertp
                                                     (cdr goal-tree-lst))
                               (mv (or cl-id-foundp2 cl-id-foundp)
                                   (cons (if (eq cl-id-foundp2 :or-found)
                                             (car goal-tree-lst)
                                           new-goal-tree)
                                         new-goal-tree-lst)))))))))

)

(defun revert-goal-tree (cl-id revertp goal-tree)

; If there are no disjunctive (:or) splits, this function replaces every final
; cdr of any :children field of each subsidiary goal tree (including goal-tree)
; by nil, for other than push-clause processors, indicating that there are no
; children left to consider proving.  If revertp is true, it also replaces each
; (push-clause *n) with (push-clause *star-1-clause-id* :REVERT), meaning that
; we are reverting.

; The spec in the case of disjunctive splits is similar, except that if cl-id
; is under such a split, then the changes described above are limited to the
; innermost disjunct containing cl-id.

  (mv-let (cl-id-foundp new-goal-tree)
          (revert-goal-tree-rec cl-id revertp goal-tree)
          (assert$ cl-id-foundp
                   new-goal-tree)))

; The pool is a list of pool-elements, as shown below.  We explain
; in push-clause.

(defrec pool-element (tag clause-set . hint-settings) t)

(defun pool-lst1 (pool n ans)
  (cond ((null pool) (cons n ans))
        ((eq (access pool-element (car pool) :tag)
             'to-be-proved-by-induction)
         (pool-lst1 (cdr pool) (1+ n) ans))
        (t (pool-lst1 (cdr pool) 1 (cons n ans)))))

(defun pool-lst (pool)

; Pool is a pool as constructed by push-clause.  That is, it is a list
; of pool-elements and the tag of each is either 'to-be-proved-by-
; induction or 'being-proved-by-induction.  Generally when we refer to
; a pool-lst we mean the output of this function, which is a list of
; natural numbers.  For example, '(3 2 1) is a pool-lst and *3.2.1 is
; its printed representation.

; If one thinks of the pool being divided into gaps by the
; 'being-proved-by-inductions (with gaps at both ends) then the lst
; has as many elements as there are gaps and the ith element, k, in
; the lst tells us there are k-1 'to-be-proved-by-inductions in the
; ith gap.

; Warning: It is assumed that the value of this function is always
; non-nil.  See the use of "jppl-flg" in the waterfall and in
; pop-clause.

  (pool-lst1 pool 1 nil))

(defun increment-proof-tree
  (cl-id ttree processor clause-count new-hist signal pspv state)

; Modifies the global proof-tree so that it incorporates the given cl-id, which
; creates n child goals via processor.  Also prints out the proof tree.

  (if (or (eq processor 'settled-down-clause)
          (and (consp new-hist)
               (consp (access history-entry (car new-hist)
                              :processor))))
      state
    (let* ((forcing-round (access clause-id cl-id :forcing-round))
           (aborting-p (and (eq signal 'abort)
                            (not (equal (tagged-objects 'abort-cause ttree)
                                        '(revert)))))
           (clause-count
            (cond ((eq signal 'or-hit)
                   (assert$
                    (eq processor 'apply-top-hints-clause)
                    (length (nth 2 (tagged-object :or ttree)))))
                  (t clause-count)))
           (processor
            (cond
             ((tagged-objectsp 'assumption ttree)
              (assert$ (and (not (eq processor 'push-clause))
                            (not (eq signal 'or-hit)))
                       (list processor :forced)))
             ((eq processor 'push-clause)
              (list* 'push-clause
                     (make clause-id
                           :forcing-round forcing-round
                           :pool-lst
                           (pool-lst
                            (cdr (access prove-spec-var pspv
                                         :pool)))
                           :case-lst nil
                           :primes 0)
                     (if aborting-p '(:ABORT) nil)))
             ((eq signal 'or-hit)
              'apply-top-hints-clause-or-hit)
             (t processor)))
           (starting-proof-tree (f-get-global 'proof-tree state))
           (new-goal-tree
            (insert-into-goal-tree cl-id
                                   processor
                                   (if (eql clause-count 0)
                                       nil
                                     clause-count)
                                   (car starting-proof-tree))))
      (pprogn
       (if new-goal-tree
           (f-put-global 'proof-tree
                         (if (and (consp processor)
                                  (eq (car processor) 'push-clause)
                                  (eq signal 'abort)
                                  (not aborting-p))
                             (if (and (= forcing-round 0)
                                      (null (cdr starting-proof-tree)))
                                 (list (revert-goal-tree cl-id t new-goal-tree))
                               (er hard 'increment-proof-tree
                                   "Internal Error: Attempted to ``revert'' ~
                                    the proof tree with forcing round ~x0 and ~
                                    proof tree of length ~x1.  This reversion ~
                                    should only have been tried with forcing ~
                                    round 0 and proof tree of length 1.  ~
                                    Please contact the ACL2 implementors."
                                   forcing-round
                                   (length starting-proof-tree)))
                           (prune-proof-tree
                            forcing-round nil
                            (cons (if (eq signal 'abort)
                                      (revert-goal-tree cl-id
                                                        nil
                                                        new-goal-tree)
                                    new-goal-tree)
                                  (cdr starting-proof-tree))))
                         state)
         (prog2$ (er hard 'increment-proof-tree
                     "Found empty goal tree from call ~x0"
                     (list 'insert-into-goal-tree
                           cl-id
                           processor
                           (if (= clause-count 0)
                               nil
                             clause-count)
                           (car starting-proof-tree)))
                 state))
       (print-proof-tree state)))))

(defun goal-tree-with-cl-id (cl-id goal-tree-lst)
  (cond ((atom goal-tree-lst)
         nil)
        ((equal cl-id (access goal-tree (car goal-tree-lst) :cl-id))
         (car goal-tree-lst))
        (t (goal-tree-with-cl-id cl-id (cdr goal-tree-lst)))))

(mutual-recursion

(defun goal-tree-choose-disjunct-rec (cl-id disjunct-cl-id goal-tree)

; This is the recursive version of goal-tree-choose-disjunct.  It either
; returns (mv nil goal-tree) without any change to the given goal-tree, or else
; it returns (mv t new-goal-tree) where new-goal-tree is not equal to
; goal-tree.

  (let ((children (access goal-tree goal-tree :children)))
    (cond
     ((equal cl-id (access goal-tree goal-tree :cl-id))
      (assert$
       (eq (access goal-tree goal-tree :processor)
           'apply-top-hints-clause-or-hit)
       (let ((child (goal-tree-with-cl-id disjunct-cl-id children)))
         (mv t
             (cond (child
                    (change goal-tree goal-tree
                            :children (list child)))
                   (t ; child was proved
                    (change goal-tree goal-tree
                            :children nil)))))))
     ((atom children) (mv nil goal-tree)) ; optimization
     (t (mv-let
         (found new-children)
         (goal-tree-choose-disjunct-lst cl-id disjunct-cl-id children)
         (cond (found (mv t (change goal-tree goal-tree
                                    :children new-children)))
               (t (mv nil goal-tree))))))))

(defun goal-tree-choose-disjunct-lst (cl-id disjunct-cl-id goal-tree-lst)
  (cond ((consp goal-tree-lst)
         (mv-let (found new-goal-tree)
                 (goal-tree-choose-disjunct-rec
                  cl-id disjunct-cl-id (car goal-tree-lst))
                 (cond (found (mv t (cons new-goal-tree (cdr goal-tree-lst))))
                       (t (mv-let (found new-goal-tree-lst)
                                  (goal-tree-choose-disjunct-lst
                                   cl-id disjunct-cl-id (cdr goal-tree-lst))
                                  (cond (found (mv t (cons (car goal-tree-lst)
                                                           new-goal-tree-lst)))
                                        (t (mv nil goal-tree-lst))))))))
        (t (mv nil goal-tree-lst))))
)

(defun goal-tree-choose-disjunct (cl-id disjunct-cl-id goal-tree)

; Replace the subtree at the goal-tree with the given cl-id with the subtree at
; its child having the given disjunct-cl-id, but eliminating the extra "D" case
; from every clause id in that subtree.

  (mv-let (foundp new-goal-tree)
          (goal-tree-choose-disjunct-rec cl-id disjunct-cl-id goal-tree)
          (assert$ foundp
                   new-goal-tree)))

(defun install-disjunct-into-proof-tree (cl-id disjunct-cl-id state)

; Replace disjunct-cl-id by cl-id in the global proof tree, discarding the
; other disjunctive cases under cl-id.

  (let ((proof-tree (f-get-global 'proof-tree state)))
    (assert$
     (consp proof-tree)
     (pprogn (f-put-global
              'proof-tree
              (prune-proof-tree
               (access clause-id cl-id :forcing-round)
               nil
               (cons (goal-tree-choose-disjunct cl-id disjunct-cl-id (car proof-tree))
                     (cdr proof-tree)))
              state)
             (print-proof-tree state)))))

; Logical Names

; Logical names are names introduced by the event macros listed in
; primitive-event-macros, e.g., they are the names of functions,
; macros, theorems, packages, etc.  Logical names have two main uses
; in this system.  The first is in theory expressions, where logical
; names are used to denote times in the past, i.e., "Give me the list
; of all rules enabled when nm was introduced."  The second is in the
; various keyword commands available to the user to enquire about his
; current state, i.e., "Show me the history around the time nm was
; introduced."

; The latter use involves the much more sophisticated notion of
; commands as well as that of events.  We will deal with it later.

; We make special provisions to support the mapping from a logical
; name to the world at the time that name was introduced.  At the
; conclusion of the processing of an event, we set the 'global-value
; of 'event-landmark to an "event tuple."  This happens in stop-event.
; Among other things, an event tuple lists the names introduced by the
; event.  The successive settings of 'event-landmark are all visible
; on the world and thus effectively divide the world up into "event
; blocks."  Because the setting of 'event-landmark is the last thing
; we do for an event, the world at the termination of a given event is
; the world whose car is the appropriate event tuple.  So one way to
; find the world is scan down the current world, looking for the
; appropriate event landmark.

; This however is slow, because often the world is not in physical
; memory and must be paged in.  We therefore have worked out a scheme
; to support the faster lookup of names.  We could have stored the
; appropriate world on the property list of each symbolic name.  We
; did not want to do this because it might cause consternation when a
; user looked at the properties.  So we instead associate a unique
; nonnegative integer with each event and provide a mapping from those
; "absolute event numbers" to worlds.  We store the absolute event
; number of each symbolic name on the property list of the name (in
; stop-event).  The only other logical names are the strings that name
; packages.  We find them by searching through the world.

(defun logical-namep (name wrld)

; Returns non-nil if name is a logical name, i.e., a symbolic or
; string name introduced by an event, or the keyword :here meaning the
; most recent event.

  (declare (xargs :guard
                  (and (plist-worldp wrld)
                       (known-package-alistp (global-val 'known-package-alist
                                                         wrld)))))
  (cond ((symbolp name)
         (cond ((eq name :here) (not (null wrld)))
               (t (getpropc name 'absolute-event-number nil wrld))))
        ((and (stringp name)
              (find-non-hidden-package-entry
               name (global-val 'known-package-alist wrld)))
         t)
        (t nil)))

; Logical-name-type has been moved up to translate.lisp in support of
; chk-all-but-new-name, which supports handling of flet by translate11.

(defun logical-name-type-string (typ)
  (case typ
        (package "package")
        (function "function")
        (macro "macro")
        (const "constant")
        (stobj "single-threaded object")
        (stobj-live-var "single-threaded object live var")
        (theorem "theorem")
        (theory "theory")
        (label "label")
        (t (symbol-name typ))))

; Event tuples, command tuples, and absolute event and command numbers could
; naturally be introduced here.  However, they are introduced earlier, to
; support the definition of ev-fncall-rec-logical (specifically, the definition
; of guard-raw, which is called by ev-fncall-guard-er, which in turn is called
; by ev-fncall-rec-logical).

; Scanning to find Landmarks

; Scan-to-event has been moved to rewrite.lisp.

(defun scan-to-command (wrld)

; Scan to the next binding of 'command-landmark.

  (cond ((null wrld) nil)
        ((and (eq (caar wrld) 'command-landmark)
              (eq (cadar wrld) 'global-value))
         wrld)
        (t (scan-to-command (cdr wrld)))))

; Scan-to-landmark-number was previously defined here, but is now introduced
; earlier to support the definition of ev-fncall-rec-logical (specifically, the
; definition of guard-raw, which is called by ev-fncall-guard-er, which in turn
; is called by ev-fncall-rec-logical).

; The Event and Command Indices

; How do we convert an absolute event number into the world created by
; that event?  The direct way to do this is to search the world for
; the appropriate binding of 'event-landmark.  To avoid much of this
; search, we keep a map from some absolute event numbers to the
; corresponding tails of world.

; Rather than store an entry for each event number we will store one
; for every 10th.  Actually, *event-index-interval* determines the
; frequency.  This is a completely arbitrary decision.  A typical :pe
; or :ubt will request a tail within 5 event of a saved one, on the
; average.  At 8 properties per event (the bootstrap right now is
; running 7.4 properties per event), that's about 40 tuples, each of
; the form (name prop . val).  We will always look at name and
; sometimes (1/8 of the time) look at prop and the car of val, which
; says we'll need to swap in about 40+40+1/8(40 + 40) = 90 conses.  We
; have no idea how much this costs (and without arguments about
; locality, it might be as bad as 90 pages!), but it seems little
; enough.  In any case, this analysis suggests that the decision to
; save every nth world will lead to swapping in only 9n conses.

; Assuming that a big proof development costs 3000 events (that's
; about the size of the Piton proof) and that the initial bootstrap is
; about 2000 (right now it is around 1700), we imagine that we will be
; dealing with 5000 events.  So our map from event numbers to
; tails of world will contain about 500 entries.  Of interest here is
; the choice of representation for that map.

; The requirement is that it be a map from the consecutive positive
; integers to tails of world (or nil for integers not yet claimed).
; It should operate comfortably with 500 entries.  It will be the
; value of the world global, 'event-index, and every time we add a
; new entry (i.e., every 10 events), we will rebind that global.
; Thus, by the time the table has 500 entries we will also be holding
; onto the 499 old versions of the table as well.

; Three representations came immediately to mind: a linear array, an
; association list, and a balanced binary tree.  A fourth was invented
; to solve the problem.  We discuss all four here.

; Linear Array.  If the event-index is an array then it will be
; extremely efficient to "search".  We will have to grow the array as
; we go, as we do in load-theory-into-enabled-structure.  So by the
; time the array has 500 entries the underlying Common Lisp array will
; probably contain around 750 words.  The alist version of the array
; will be of length 500 (ignoring the :HEADER) and consume 1000
; conses.  So in all we'll have about 1750 words tied up in this
; structure.  Old versions of the table will share the alist
; representation and cost little.  However, we imagine keeping only
; one Common Lisp array object and it will always hold the compressed
; version of the latest index.  So old versions of the index will be
; "out of date" and will have to be recompressed upon recovery from a
; :ubt, as done by recompress-global-enabled-structure.  This
; complicates the array representation and we have decided to dismiss
; it.

; Alist.  If the event-index is an alist it will typically be 500
; long and contain 1000 conses which are all perfectly shared with old
; copies.  Adding new entries is very fast, i.e., 2 conses.  Lookup is
; relatively slow: .004 seconds, average with an alist of size 500.
; For comparison purposes, we imagine the following scenario: The user
; starts with a world containing 2000 bootstrap events.  He adds
; another 3000 events of his own.  Every event, however, provokes
; him to do 10 :pes to look at old definitions.  (We are purposefully
; biasing the scenario toward fast lookup times.)  Given the
; convention of saving every 10th tail of world in the index, the
; scenario becomes: The user starts with a index containing 200
; entries.  He grows it to 500 entries.  However, between each growth
; step he inspects 100 entries spread more or less evenly throughout
; the interval.  If the index is represented by an alist, how long
; does this scenario take?  Answer: 77 seconds (running AKCL on a Sun
; 360 with 20Mb).

; Balanced Binary Tree.  We have done an extensive study of the use of
; balanced binary trees (bbts) for this application.  Using bbts, the
; scenario above requires only 13 seconds.  However, bbts use a lot
; more space.  In particular, the bbt for 500 entries consumes 2000
; conses (compared to the alist's 1000 conses).  Worse, the bbt for
; 500 shares little of the structure for 499, while the alist shares
; it all.  (We did our best with structure sharing between successive
; bbts, it's just that rebalancing the tree after an addition
; frequently destroys the possibility for sharing.  Of the 2000 conses
; in the 500 entry bbt, 1028 are new and the rest are shared with the
; 499 bbt.)  In particular, to keep all 500 of the bbts will cost us
; 156,000 conses.  By contrast, the entire world after a bootstrap
; currently costs about 418,000 conses.

; So we need a representation that shares structure and yet is
; efficiently accessed.  Why are alists so slow?  Because we have to
; stop at every entry and ask "is this the one?"  But that is silly
; because we know that if we're looking for 2453 and we see 3000 then
; we have to skip down 547.  That is, our values are all associated
; with consecutive integer indices and the alist is ordered.  But we
; could just use a positional indexing scheme.

; Zap Table.  A zap table is a linear list of values indexed by
; 0-based positions STARTING FROM THE RIGHT.  To enable us to count
; from the right we include, as the first element in the list, the
; maximum index.  For example, the zap table that maps each of the
; integers from 0 to 9 to itself is: (9 9 8 7 6 5 4 3 2 1 0).  To add
; a new (10th) value to the table, we increment the car by 1 and cons
; the new value to the cdr.  Thus, we spend two conses per entry and
; share all other structure.  To fetch the ith entry we compute how
; far down the list it is with arithmetic and then retrieve it with
; nth.  To our great delight this scheme carries out our scenario in
; 13 seconds, as fast as balanced binary trees, but shares as much
; structure as alists.  This is the method we use.

; Code for zap tables (add-to-zap-table, etc.) was previously found here, but
; is now introduced earlier to support the definition of ev-fncall-rec-logical
; (specifically, the definition of guard-raw, which is called by
; ev-fncall-guard-er, which in turn is called by ev-fncall-rec-logical).

(defun update-world-index (flg wrld)

; Flg is either 'COMMAND or 'EVENT and indicates which of the two
; indices we are to update.

; In the comments below, we assume flg is 'EVENT.

; This function is called every time we successfully complete the
; processing of an event.  We here decide if it is appropriate
; to save a pointer to the resulting world, wrld.  If so, we update
; the event-index.  If not, we do nothing.  Our current algorithm
; is to save every *event-index-interval*th world.  That is, if
; *event-index-interval* is 10 then we save the worlds whose
; max-absolute-event-numbers are 0, 10, 20, etc., into slots 0, 1, 2,
; etc. of the index.

  (cond
   ((eq flg 'EVENT)
    (let ((n (max-absolute-event-number wrld)))
      (cond ((= (mod n *event-index-interval*) 0)
             (let ((event-index (global-val 'event-index wrld)))

; Things will get very confused if we ever miss a multiple of "10."
; For example, if some bug in the system causes us never to call this
; function on a world with absolute-event-number 10, say, then the
; next multiple we do call it on, e.g., 20, will be stored in the
; slot for 10 and things will be royally screwed.  So just to be
; rugged we will confirm the correspondence between what we think
; we're adding and where it will go.

               (cond ((= (floor n *event-index-interval*)
                         (if (null event-index)
                             0
                             (1+ (car event-index))))
                      (global-set 'event-index
                                  (add-to-zap-table wrld event-index)
                                  wrld))
                     (t (er hard 'update-world-index
                            "The event-index and the maximum absolute ~
                             event number have gotten out of sync!  ~
                             In particular, the next available index ~
                             is ~x0 but the world has event number ~
                             ~x1, which requires index ~x2."
                            (if (null event-index)
                                0
                                (1+ (car event-index)))
                            n
                            (floor n *event-index-interval*))))))
            (t wrld))))
   (t
    (let ((n (max-absolute-command-number wrld)))
      (cond ((= (mod n *command-index-interval*) 0)
             (let ((command-index (global-val 'command-index wrld)))
               (cond ((= (floor n *command-index-interval*)
                         (if (null command-index)
                             0
                             (1+ (car command-index))))
                      (global-set 'command-index
                                  (add-to-zap-table wrld command-index)
                                  wrld))
                     (t (er hard 'update-world-index
                            "The command-index and the maximum ~
                             absolute command number have gotten out ~
                             of sync!  In particular, the next ~
                             available index is ~x0 but the world has ~
                             command number ~x1, which requires index ~
                             ~x2."
                            (if (null command-index)
                                0
                                (1+ (car command-index)))
                            n
                            (floor n *command-index-interval*))))))
            (t wrld))))))

; Lookup-world-index1 and lookup-world-index were previously defined here, but
; are now introduced earlier to support the definition of ev-fncall-rec-logical
; (specifically, the definition of guard-raw, which is called by
; ev-fncall-guard-er, which in turn is called by ev-fncall-rec-logical).

; Maintaining the Invariants Associated with Logical Names and Events

(defun store-absolute-event-number (namex n wrld boot-strap-flg)

; Associated with each symbolic logical name is the
; 'absolute-event-number.  This function is responsible for storing
; that property.  Namex is either 0, denoting the empty set, an atom,
; denoting the singleton set containing that atom, or a true-list of
; atoms denoting the corresponding set.

; It is convenient to store the 'predefined property here as well.

  (cond ((equal namex 0)
         wrld)
        ((atom namex)

; If namex is "MY-PKG" we act as though it were the empty list.

         (cond ((symbolp namex)
                (putprop namex 'absolute-event-number n
                         (cond (boot-strap-flg
                                (putprop namex 'predefined t wrld))
                               (t wrld))))
               (t wrld)))
        (t (store-absolute-event-number
            (or (cdr namex) 0)
            n
            (if (stringp (car namex))
                wrld
              (putprop (car namex) 'absolute-event-number n
                       (cond (boot-strap-flg
                              (putprop (car namex) 'predefined t wrld))
                             (t wrld))))
            boot-strap-flg))))

(defun the-namex-symbol-class1 (lst wrld symbol-class1)
  (cond ((null lst) symbol-class1)
        ((stringp (car lst))
         (the-namex-symbol-class1 (cdr lst) wrld symbol-class1))
        (t (let ((symbol-class2 (symbol-class (car lst) wrld)))
             (cond ((eq symbol-class1 nil)
                    (the-namex-symbol-class1 (cdr lst) wrld symbol-class2))
                   ((eq symbol-class2 nil)
                    (the-namex-symbol-class1 (cdr lst) wrld symbol-class1))
                   ((eq symbol-class1 symbol-class2)
                    (the-namex-symbol-class1 (cdr lst) wrld symbol-class1))
                   (t (er hard 'the-namex-symbol-class
                          "The symbolp elements of the namex argument ~
                           to add-event-landmark are all supposed to ~
                           have the same symbol-class, but the first ~
                           one we found with a symbol-class had class ~
                           ~x0 and now we've found another with ~
                           symbol-class ~x1.  The list of elements, ~
                           starting with the one that has ~
                           symbol-class ~x0 is ~x2."
                          symbol-class2 symbol-class1 lst)))))))

(defun the-namex-symbol-class (namex wrld)
  (cond ((equal namex 0) nil)
        ((atom namex)
         (cond ((symbolp namex)
                (symbol-class namex wrld))
               (t nil)))
        (t (the-namex-symbol-class1 namex wrld nil))))

(defun add-event-landmark (form ev-type namex wrld boot-strap-flg
                                skipped-proofs-p)

; We use a let* below and a succession of worlds just to make clear
; the order in which we store the various properties.  We update the
; world index before putting the current landmark on it.  This
; effectively adds the previous landmark to the index if it was a
; multiple of our interval.  We do this just so that the
; event-landmark we are about to lay down is truly the last thing we
; do.  Reflection on this issue leads to the conclusion that it is not
; really important whether the index entry is inside or outside of the
; landmark, in the case of event-landmarks.

  (let* ((n (next-absolute-event-number wrld))
         (wrld1 (store-absolute-event-number namex n wrld boot-strap-flg))
         (wrld2 (update-world-index 'event wrld1))
         (wrld3
           (global-set 'event-landmark
                       (make-event-tuple n
                                         (length (global-val
                                                  'embedded-event-lst
                                                  wrld))
                                         form
                                         ev-type
                                         namex
                                         (the-namex-symbol-class namex wrld2)
                                         skipped-proofs-p)
                       wrld2)))
    wrld3))

; Decoding Logical Names was handled here through Version_8.0, but some
; definitions have been moved to rewrite.lisp to support find-rules-of-rune.

(defun er-decode-logical-name (name wrld ctx state)

; Like decode-logical-name but causes an error rather than returning nil.

  (let ((wrld1 (decode-logical-name name wrld)))
    (cond
     ((null wrld1)
      (let ((hits (and (stringp name)
                       (not (find-non-hidden-package-entry
                             name
                             (global-val 'known-package-alist wrld)))
                       (multiple-assoc-terminal-substringp
                        (possibly-add-lisp-extension name)
                        (global-val 'include-book-alist wrld)))))

; Hits is a subset of the include-book-alist.  The form of each
; element is (full-book-name user-book-name familiar-name
; cert-annotations . book-hash).

        (cond
         ((and hits (cdr hits))
          (er soft ctx
              "More than one book matches the name ~x0, in particular ~&1.  We ~
               therefore consider ~x0 not to be a logical name and insist ~
               that you use an unambiguous form of it.  See :DOC logical-name."
              name
              (strip-cars hits)))
         (t (er soft ctx
                "The object ~x0 is not a logical name.  See :DOC logical-name."
                name)))))
     (t (value wrld1)))))

(defun renew-lemmas (fn lemmas)

; We copy lemmas, which is a list of rewrite rules, deleting those whose
; runes have fn as their base symbol.  These are, we believe, all and only
; the rules stored by the event which introduced fn.

  (cond ((null lemmas) nil)
        ((eq (base-symbol (access rewrite-rule (car lemmas) :rune)) fn)
         (renew-lemmas fn (cdr lemmas)))
        (t (cons (car lemmas) (renew-lemmas fn (cdr lemmas))))))

(defun renew-name/erase (name old-getprops wrld)

; Name is a symbol, old-getprops is the list returned by getprops on name,
; i.e., an alist dotting properties to values.  We map over that list and
; "unbind" every property of name in wrld.  We do not touch 'GLOBAL-VALUE
; because that is not a property affected by an event (consider what would
; happen if the user defined and then redefined COMMAND-LANDMARK).  Similarly,
; we do not touch 'table-alist or 'table-guard.  See the list of properties
; specially excepted by new-namep.

  (cond
   ((null old-getprops) wrld)
   (t (renew-name/erase
       name
       (cdr old-getprops)
       (if (member-eq (caar old-getprops)
                      '(global-value table-alist table-guard))
           wrld
           (putprop name
                    (caar old-getprops)
                    *acl2-property-unbound*
                    wrld))))))

;; Historical Comment from Ruben Gamboa:
;; Hmmm, this code assumes it knows all of the properties stored
;; on a function symbol.  Sad.  I added 'CLASSICALP to the list.

(defun renew-name/overwrite (name old-getprops wrld)

; Name is a function symbol, old-getprops is the list returned by getprops on
; name, i.e., an alist dotting properties to values.  We map over that list and
; "unbind" those properties of name in wrld that were stored by the event
; introducing name.

; Note: Even when the ld-redefinition-action specifies :overwrite we sometimes
; change it to :erase (see maybe-coerce-overwrite-to-erase).  Thus, this
; function is actually only called on function symbols, not constants or stobjs
; or stobj-live-vars.  The erase version, above, is called on those redefinable
; non-functions.

; Finally, we back up our claim that name must be a function symbol.  The
; reason is that renew-name is the only place that calls renew-name/overwrite
; and it only does that when the renewal-mode is :overwrite or
; :reclassifying-overwrite.  Now renew-name is only called by
; chk-redefineable-namep which sets the renewal-mode using
; redefinition-renewal-mode.

; Finally, if you inspect redefinition-renewal-mode you can see that it only
; returns :overwrite or :reclassifying-overwrite on functions.  The proof of
; this for the :overwrite cases is tedious but pretty straightforward.  Most
; branches through redefinition-renewal-mode signal an error prohibiting the
; redefinition attempt, a few explicitly return :erase, and the normal cases in
; which :overwrite could be returned are all coming out of calls to
; maybe-coerce-overwrite-to-erase, which returns :erase unless the old and new
; type of the event is FUNCTION.

; The harder part of the proof (that only functions get renewal-mode :overwrite
; or :reclassifying-overwrite) is when we return :reclassifying-overwrite.
; Whether redefinition-renewal-mode does that depends on the argument
; reclassifyingp supplied by chk-redefineable-namep, which in turn depends on
; what value of reclassifyingp is supplied to chk-redefineable-namep by its
; only caller, chk-just-new-name, which in turn just passes in the value it is
; supplied by its callers, of which there are many.  However, all but
; chk-acceptable-defuns1 supply reclassifyingp of nil.

; So we know that we reclassify only function symbols and we know that only
; function symbols get :overwrite or :reclassifying-overwrite for their
; renewal-modes.

  (cond
   ((null old-getprops) wrld)
   ((eq (caar old-getprops) 'redefined)
    (renew-name/overwrite
     name
     (cdr old-getprops)
     wrld))
   ((member-eq (caar old-getprops)
               '(FORMALS
                 STOBJS-IN
                 STOBJS-OUT
                 SYMBOL-CLASS
                 NON-EXECUTABLEP
                 SIBLINGS
                 LEVEL-NO
                 TAU-PAIR
                 QUICK-BLOCK-INFO
                 PRIMITIVE-RECURSIVE-DEFUNP
                 CONSTRAINEDP
                 HEREDITARILY-CONSTRAINED-FNNAMES
                 #+:non-standard-analysis CLASSICALP
                 DEF-BODIES
                 INDUCTION-MACHINE
                 JUSTIFICATION
                 UNNORMALIZED-BODY
                 CONSTRAINT-LST
                 RECURSIVEP
                 LOOP$-RECURSION
                 TYPE-PRESCRIPTIONS
                 GUARD
                 SPLIT-TYPES-TERM
                 INVARIANT-RISK
                 ABSOLUTE-EVENT-NUMBER

; It is tempting to add CONGRUENT-STOBJ-REP to this list.  But it is a property
; of stobjs, not functions, so that isn't necessary.

; Note: If you delete RUNIC-MAPPING-PAIRS from this list you must reconsider
; functions like current-theory-fn which assume that if a name has the
; REDEFINED property then its runic-mapping-pairs has been set to
; *acl2-property-unbound*.

                 RUNIC-MAPPING-PAIRS

; This property is stored by defstobj on all supporting functions.

                 STOBJ-FUNCTION))

; The properties above are stored by the defun, constrain or defstobj
; that introduced name and we erase them.

    (renew-name/overwrite
     name
     (cdr old-getprops)
     (putprop name
              (caar old-getprops)
              *acl2-property-unbound*
              wrld)))
   ((eq (caar old-getprops) 'lemmas)

; We erase from the lemmas property just those rules stored by the introductory event.

    (renew-name/overwrite
     name
     (cdr old-getprops)
     (putprop name
              'lemmas
              (renew-lemmas name
                            (getpropc name 'lemmas nil wrld))
              wrld)))
   ((member-eq (caar old-getprops)

; As of this writing, the property in question must be one of the following,
; since name is a function symbol.  Note that these are not created by the
; introductory event of name (which must have been a defun or constrain) and
; hence are left untouched here.

               '(GLOBAL-VALUE
                 LINEAR-LEMMAS
                 FORWARD-CHAINING-RULES
                 ELIMINATE-DESTRUCTORS-RULE
                 COARSENINGS
                 CONGRUENCES
                 RECOGNIZER-ALIST
                 PEQUIVS
                 INDUCTION-RULES
                 DEFCHOOSE-AXIOM
                 TABLE-GUARD ; functions names can also be table names
                 TABLE-ALIST ; functions names can also be table names
                 PREDEFINED
                 DEFAXIOM-SUPPORTER
                 ATTACHMENT ; see Essay on Defattach re: :ATTACHMENT-DISALLOWED
                 CLAUSE-PROCESSOR
                 TAU-PAIR-SAVED
                 POS-IMPLICANTS
                 NEG-IMPLICANTS
                 UNEVALABLE-BUT-KNOWN
                 SIGNATURE-RULES-FORM-1
                 SIGNATURE-RULES-FORM-2
                 BIG-SWITCH
                 TAU-BOUNDERS-FORM-1
                 TAU-BOUNDERS-FORM-2
                 ))
   (renew-name/overwrite
    name
    (cdr old-getprops)
    wrld))
  (t
   (illegal 'renew-name/overwrite
            "We thought we knew all the properties stored by events ~
             introducing redefinable function names, but we don't know about ~
             the property ~x0."
            (list (cons #\0 (caar old-getprops)))))))

(defun renew-name (name renewal-mode wrld)

; We make it sort of appear as though name is sort of new in wrld.  Ah, to be
; young again...  We possibly erase all properties of name (depending on the
; renewal-mode, which must be :erase, :overwrite or :reclassifying-overwrite),
; and we put a 'redefined property on name.  Note that we always put the
; 'redefined property, even if name already has that property with that value,
; because one of our interests in this property is in stop-event, which uses it
; to identify which names have been redefined in this event.

; The value of the 'redefined property is (renewal-mode . old-sig),
; where old-sig is either the internal form signature of name if name
; is function and is otherwise nil.

; By storing the renewal-mode we make it possible to recover exactly how the
; final world was obtained from the initial one.  For purposes of renewal, we
; treat renewal-mode :reclassifying-overwrite as :overwrite; the only
; difference is that we store the :reclassifying-overwrite in the 'redefined
; property.  The only time :reclassifying-overwrite is the renewal-mode is when
; a :program function is being reclassified to an identical-defp :logic
; function.

  (putprop name 'redefined
           (cons renewal-mode
                 (cond ((and (symbolp name)
                             (function-symbolp name wrld))
                        (list name
                              (formals name wrld)
                              (stobjs-in name wrld)
                              (stobjs-out name wrld)))
                       (t nil)))
           (cond
            ((eq renewal-mode :erase)
             (renew-name/erase name
                               (getprops name 'current-acl2-world wrld)
                               wrld))
            ((or (eq renewal-mode :overwrite)
                 (eq renewal-mode :reclassifying-overwrite))
             (renew-name/overwrite name
                                   (getprops name 'current-acl2-world wrld)
                                   wrld))
            (t wrld))))

(defun renew-names (names renewal-mode wrld)
  (cond ((endp names) wrld)
        (t (renew-names (cdr names)
                        renewal-mode
                        (renew-name (car names) renewal-mode wrld)))))

(defun collect-redefined (wrld ans)

; We return a list of all redefined names down to the next event-landmark
; except those redefined in the :reclassifying-overwrite mode.  (Quoting from a
; comment in renew-name: The only time :reclassifying-overwrite is the
; renewal-mode is when a :program function is being reclassified to an
; identical-defp :logic function.)

  (cond ((or (null wrld)
             (and (eq (caar wrld) 'event-landmark)
                  (eq (cadar wrld) 'global-value)))
         ans)
        ((and (eq (cadar wrld) 'redefined)
              (consp (cddar wrld))
              (not (eq (car (cddar wrld)) :reclassifying-overwrite)))
         (collect-redefined
          (cdr wrld)
          (cons (caar wrld) ans)))
        (t (collect-redefined (cdr wrld) ans))))

(defun scrunch-eq (lst)
  (cond ((null lst) nil)
        ((member-eq (car lst) (cdr lst)) (scrunch-eq (cdr lst)))
        (t (cons (car lst) (scrunch-eq (cdr lst))))))

(defun print-redefinition-warning (wrld ctx state)

; If the 'ld-redefinition-action of state says we should :warn and some names
; were redefined, then we print a warning.  See :DOC ld-redefinition-action.
; Note that if the action specifies :warn and a system function is
; redefined, then a query is made.  Provided the user approves, the system
; function is redefined and then this warning is printed because the action
; says :warn.  This is a bit odd since we try, in general, to avoid warning
; if we have queried.  But we don't want to have to determine now if the
; redefined names are system functions, so we warn regardless.

  (cond
   ((warning-disabled-p "Redef")
    state)
   ((let ((act (f-get-global 'ld-redefinition-action state)))
      (and (consp act)
           (or (eq (car act) :warn)
               (eq (car act) :warn!))))
    (let ((redefs
           (scrunch-eq
            (reverse
             (collect-redefined
              (cond ((and (consp wrld)
                          (eq (caar wrld) 'event-landmark)
                          (eq (cadar wrld) 'global-value))
                     (cdr wrld))
                    (t (er hard 'print-redefinition-warning
                           "This function is supposed to be called on a world ~
                             that starts at an event landmark, but this world ~
                             starts with (~x0 ~x1 . val)."
                           (caar wrld)
                           (cadar wrld))))
              nil)))))
      (cond (redefs
             (warning$ ctx ("Redef") "~&0 redefined.~%" redefs))
            (t state))))
   (t state)))

(defun clear-event-data (state)
  (f-put-global 'last-event-data nil state))

(defun get-event-data (key state)

; See :DOC get-event-data.

  (cdr (assoc key (f-get-global 'last-event-data state))))

(defun put-event-data (key val state)

; See get-event-data for keys.

  (f-put-global 'last-event-data
                (acons key val (f-get-global 'last-event-data state))
                state))

(defun last-prover-steps (state)
  (get-event-data 'prover-steps-counted state))

(defun initialize-summary-accumulators (state)

; This function is the standard way to start an ACL2 event.  We push a 0 onto
; each of the timers, thus protecting the times accumulated by any superior
; (e.g., an encapsulate) and initializing an accumulator for this event.  The
; accumulated times AND warnings are printed by print-time-summary.

; Note that some state globals also need to be initialized when starting an
; event, but that is accomplished using the macro save-event-state-globals.

  #+(and (not acl2-loop-only) acl2-rewrite-meter) ; for stats on rewriter depth
  (setq *rewrite-depth-max* 0)

  (cond
   ((global-val 'include-book-path (w state))
    state)
   (t
    (progn$

; If these time-tracker calls are changed, update :doc time-tracker
; accordingly.

     (time-tracker :tau :end) ; in case interrupt prevented preceding summary
     (time-tracker :tau :init
                   :times '(1 5)
                   :interval 10
                   :msg (concatenate
                         'string
                         (if (f-get-global 'get-internal-time-as-realtime
                                           state)
                             "Elapsed realtime"
                           "Elapsed runtime")
                         " in tau is ~st secs; see :DOC time-tracker-tau.~|~%"))
     (pprogn (cond ((null (cdr (get-timer 'other-time state))) ; top-level event
                    (mv-let (x state)
                      (main-timer state)
                      (declare (ignore x))
                      state))
                   (t ; inbetween events
                    (increment-timer 'other-time state)))
             (push-timer 'other-time 0 state)
             (push-timer 'prove-time 0 state)
             (push-timer 'print-time 0 state)
             (push-timer 'proof-tree-time 0 state)
             (push-warning-frame state))))))

(defun clear-warning-summaries-alist (alist)

; Delete every entry in alist whose key is string-equal to a member of
; *tracked-warning-summaries*.

  (cond
   ((endp alist) nil)
   ((and (stringp (car (car alist)))
         (standard-string-p (car (car alist)))
         (member-string-equal (car (car alist))
                              *tracked-warning-summaries*))
    (clear-warning-summaries-alist (cdr alist)))
   (t (cons (car alist)
            (clear-warning-summaries-alist (cdr alist))))))

(defun clear-warning-summaries ()

; We update the COMMENT-WINDOW-IO wormhole data to remove all the
; *tracked-warning-summaries*.  Doing this means that the next time those
; warning situations arise the warnings are actually printed.

  (wormhole 'COMMENT-WINDOW-IO
            '(lambda (whs)
               (make-wormhole-status
                whs
                :SKIP
                (clear-warning-summaries-alist
                 (wormhole-data whs))))
            nil
            nil))

(defun print-warnings-summary (state)
  (mv-let
   (warnings state)
   (pop-warning-frame t state)
   (pprogn
    (put-event-data 'warnings warnings state)
    (io? summary nil state
         (warnings)
         (cond ((member-eq 'warnings
                           (f-get-global 'inhibited-summary-types
                                         state))
                state)
               ((null warnings)
                state)
               (t
                (let ((channel (proofs-co state)))
                  (mv-let
                   (col state)
                   (fmt1 "Warnings:  ~*0~%"
                         (list (cons #\0
                                     (list "None" "~s*" "~s* and " "~s*, "
                                           warnings)))
                         0 channel state nil)
                   (declare (ignore col))
                   state))))))))

(defun skip-proof-tree-time (state)

; Note that get-timer is untouchable, and :pso calls trans-eval, hence
; translate1.  Thus, we define this little function in order to avoid hitting
; get-timer during the io? call in print-time-summary.

  (and (member-eq 'proof-tree
                  (f-get-global 'inhibit-output-lst state))
       (= (car (get-timer 'proof-tree-time state)) 0)))

(defun print-time-summary (state)

; Print the time line, e.g.,

;Time:  0.15 seconds (prove: 0.00, print: 0.02, other: 0.13)

; assuming that the cursor is at the left margin.

; Once upon a time we considered extending fmt so that it knew how to print
; timers.  However, fmt needs to know which column it is left in and returns
; that to the user.  Thus, if fmt printed a timer (at least in the most
; convenient way) the user could detect the number of digits in it.  So we are
; doing it this way.

; Through Version_8.1 we called print-timer to print timers.  However, :pso
; then failed to print the original time.  Now we first obtain the times before
; doing the printing, so that the io? call below can save the times originally
; printed.

  (pprogn
     (cond
      ((member-eq 'time
                  (f-get-global 'inhibited-summary-types
                                state))
       state)
      (t
       (let ((skip-proof-tree-time (skip-proof-tree-time state)))
         (pprogn
          (push-timer 'total-time 0 state)
          (add-timers 'total-time 'prove-time state)
          (add-timers 'total-time 'print-time state)
          (add-timers 'total-time 'proof-tree-time state)
          (add-timers 'total-time 'other-time state)
          (let ((total-time (car (get-timer 'total-time state)))
                (prove-time (car (get-timer 'prove-time state)))
                (print-time (car (get-timer 'print-time state)))
                (proof-tree-time (and (not skip-proof-tree-time)
                                      (car (get-timer 'proof-tree-time
                                                      state))))
                (other-time (car (get-timer 'other-time state))))
            (io? summary nil state
                 (total-time prove-time print-time proof-tree-time other-time)
                 (let ((channel (proofs-co state)))
                   (pprogn
                    (princ$ "Time:  " channel state)
                    (print-rational-as-decimal total-time channel state)
                    (princ$ " seconds (prove: " channel state)
                    (print-rational-as-decimal prove-time channel state)
                    (princ$ ", print: " channel state)
                    (print-rational-as-decimal print-time channel state)
                    (if (null proof-tree-time)
                        state
                      (pprogn (princ$ ", proof tree: " channel state)
                              (print-rational-as-decimal proof-tree-time channel
                                                         state)))
                    (princ$ ", other: " channel state)
                    (print-rational-as-decimal other-time channel state)
                    (princ$ ")" channel state)
                    (newline channel state)))))
          (pop-timer 'total-time nil state)))))

; The function initialize-summary-accumulators makes corresponding calls of
; push-timer, not under an io? call.  So the balancing calls of pop-timer below
; also are not under an io? call.

   (pop-timer 'prove-time t state)
   (pop-timer 'print-time t state)
   (pop-timer 'proof-tree-time t state)
   (pop-timer 'other-time t state)))

(defun prover-steps (state)

; Returns nil if no steps were taken (or if state global 'last-step-limit is
; nil, though that may be impossible).  Otherwise returns the (positive) number
; of steps taken, with one exception: If the number of steps exceeded the
; starting limit, then we return the negative of the starting limit.

  (let* ((rec (f-get-global 'step-limit-record state))
         (start (assert$ rec
                         (access step-limit-record rec :start)))
         (last-limit (assert$ start
                              (f-get-global 'last-step-limit state))))
    (cond ((and last-limit
                (not (int= start last-limit)))
           (cond ((eql last-limit -1)   ; more than start steps
                  (assert$ (natp start) ; else start <= -2; impossible
                           (- start)))
                 (t (- start last-limit))))
          (t nil))))

(defun print-steps-summary (steps state)
  (cond
   ((null steps) state)
   (t (io? summary nil state
           (steps)
           (cond
            ((member-eq 'steps
                        (f-get-global 'inhibited-summary-types
                                      state))
             state)
            (t (let ((channel (proofs-co state)))
                 (pprogn (princ$ "Prover steps counted:  " channel state)
                         (cond ((<= steps 0)
                                (pprogn
                                 (princ$ "More than " channel state)
                                 (princ$ (- steps) channel state)))
                               (t (princ$ steps channel state)))
                         (newline channel state)))))))))

#+acl2-rewrite-meter
(defun merge-cdr-> (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((> (cdr (car l1)) (cdr (car l2)))
         (cons (car l1) (merge-cdr-> (cdr l1) l2)))
        (t (cons (car l2) (merge-cdr-> l1 (cdr l2))))))

#+acl2-rewrite-meter
(defun merge-sort-cdr-> (l)
  (cond ((null (cdr l)) l)
        (t (merge-cdr-> (merge-sort-cdr-> (evens l))
                        (merge-sort-cdr-> (odds l))))))

(defconst *gag-prefix* "([ ")
(defconst *gag-suffix* (msg "])~|"))

(defun gag-start-msg (cl-id pool-name)
  (msg "~@0A key checkpoint~#1~[ while proving ~@2 ~
        (descended from ~@3)~/~]:"
       *gag-prefix*
       (if cl-id 0 1)
       pool-name
       (and cl-id (tilde-@-clause-id-phrase cl-id))))

(defun print-gag-info (info state)
  (fms "~@0~%~Q12~|"
       (list (cons #\0 (tilde-@-clause-id-phrase
                        (access gag-info info :clause-id)))
             (cons #\1 (prettyify-clause
                        (access gag-info info :clause)
                        (let*-abstractionp state)
                        (w state)))
             (cons #\2 (term-evisc-tuple nil state)))
       (proofs-co state) state nil))

(defun set-checkpoint-summary-limit-fn (val state)
  (if (or (eq val nil)
          (eq val t)
          (natp val)
          (and (consp val)
               (or (null (car val))
                   (natp (car val)))
               (or (null (cdr val))
                   (natp (cdr val)))))
      (let ((val (if (natp val)
                     (cons val val)
                   val)))
        (pprogn (f-put-global 'checkpoint-summary-limit val state)
                (value val)))
    (er soft 'set-checkpoint-summary-limit
        "Illegal value, ~x0, for checkpoint-summary-limit; see :DOC ~
         set-checkpoint-summary-limit."
        val)))

(defmacro set-checkpoint-summary-limit (val)
  (let ((x (if (and (consp val)
                    (eq (car val) 'quote))
               val
             (list 'quote val))))
    `(set-checkpoint-summary-limit-fn ,x state)))

(defmacro checkpoint-summary-limit ()
  '(f-get-global 'checkpoint-summary-limit state))

(defun print-gag-stack-rev (lst limit orig-limit msg chan state)

; Lst is the reverse of the :abort-stack, :top-stack, or :sub-stack field of a
; gag-state.

  (cond ((endp lst) state)
        ((eql limit 0)
         (fms "Note: ~#2~[Not shown~/There~] ~#0~[is~#2~[ the~/~] ~n1~#2~[~/ ~
               additional~] key checkpoint~/are~#2~[ the~/~] ~n1~#2~[~/ ~
               additional~] key checkpoints~] ~@3.  See :DOC ~
               set-checkpoint-summary-limit to ~#4~[change the number ~
               printed~/print this key checkpoint~/print some or all of these ~
               key checkpoints~].~|"
              (list (cons #\0 lst)
                    (cons #\1 (length lst))
                    (cons #\2 (if (eql orig-limit 0) 0 1))
                    (cons #\3 msg)
                    (cons #\4 (cond ((not (eql orig-limit 0)) 0)
                                    ((null (cdr lst)) 1)
                                    (t 2))))
              chan state nil))
        (t (pprogn (print-gag-info (car lst) state)
                   (print-gag-stack-rev (cdr lst) (and limit (1- limit))
                                        orig-limit msg chan state)))))

(defun reverse-gag-stack (stack acc)

; Stack is a list of gag-info records.  This function is just revappend, except
; that if we encounter a goal with :clause nil, then we return the first such
; goal encountered as the first element of the result.

  (cond ((null stack) acc)
        ((equal (access gag-info (car stack) :clause)
                nil)
         (cons (car stack)
               (revappend (cdr stack) acc)))
        (t (reverse-gag-stack (cdr stack)
                              (cons (car stack) acc)))))

(defun print-gag-state-abort-stack-msg (abort-stack)

; See print-gag-state.

  (case abort-stack
    (empty-clause
     (msg "~|    before generating a goal of ~x0 (see :DOC nil-goal)"
          'nil))
    (do-not-induct
     "~|    before a :DO-NOT-INDUCT hint stopped the proof attempt")
    (induction-depth-limit-exceeded
     "~|    before the induction-depth-limit stopped the proof attempt")
    (otherwise "")))

(defun print-gag-state1 (gag-state state)
  (cond
   ((eq (f-get-global 'checkpoint-summary-limit state) t)
    state)
   (gag-state
    (let* ((chan (proofs-co state))
           (abort-stack
            (access gag-state gag-state :abort-stack))
           (top-stack0 (access gag-state gag-state :top-stack))
           (top-stack (if (consp abort-stack) abort-stack top-stack0))
           (sub-stack (access gag-state gag-state :sub-stack))
           (some-stack (or sub-stack

; We use top-stack0 here instead of top-stack because if the only non-empty
; stack is the :abort-stack, then presumably the proof completed modulo :by
; hints that generated :bye tags in the ttree.

                           top-stack0))
           (forcing-round-p
            (and some-stack
                 (let ((cl-id (access gag-info (car some-stack)
                                      :clause-id)))
                   (not (eql 0 (access clause-id cl-id
                                       :forcing-round)))))))
      (cond
       (some-stack
        (pprogn
         (fms "---~|The key checkpoint goal~#0~[~/s~], below, may help you to ~
               debug this failure.  See :DOC failure and see :DOC ~
               set-checkpoint-summary-limit.~@1~|---~|"
              (list (cons #\0
                          (if (or (and top-stack sub-stack)
                                  (cdr top-stack)
                                  (cdr sub-stack))
                              1
                            0))
                    (cons #\1
                          (if forcing-round-p
                              "  Note that at least one checkpoint is in a ~
                               forcing round, so you may want to see a full ~
                               proof."
                            "")))
              chan state nil)
         (cond (top-stack
                (let ((limit (car (f-get-global
                                   'checkpoint-summary-limit
                                   state))))
                  (pprogn
                   (fms "*** Key checkpoint~#0~[~/s~] ~#1~[before reverting ~
                         to proof by induction~/at the top level~@2~]: ***"
                        (list (cons #\0 top-stack)
                              (cons #\1 (if (consp abort-stack) 0 1))
                              (cons #\2 (if sub-stack
                                            ""
                                          (print-gag-state-abort-stack-msg
                                           abort-stack))))
                        chan state nil)
                   (newline chan state)
                   (print-gag-stack-rev
                    (reverse-gag-stack top-stack nil)
                    limit limit "before induction" chan
                    state))))
               (t state))
         (cond (sub-stack
                (let ((limit (cdr (f-get-global
                                   'checkpoint-summary-limit
                                   state))))
                  (pprogn
                   (fms "*** Key checkpoint~#0~[~/s~] under a top-level ~
                         induction~@1: ***"
                        (list (cons #\0 sub-stack)
                              (cons #\1 (print-gag-state-abort-stack-msg
                                         abort-stack)))
                        chan state nil)
                   (newline chan state)
                   (print-gag-stack-rev
                    (reverse-gag-stack sub-stack nil)
                    limit
                    limit
                    "under a top-level induction"
                    chan
                    state))))
               (t state))))
       (t ; no checkpoints; aborted
        (fms #-acl2-par
             "*** Note: No checkpoints to print. ***~|"
             #+acl2-par
             "*** Note: No checkpoints from gag-mode to print. ***~|"
             nil chan state nil)))))
   (t ; no checkpoints; proof never started
    state)))

(defun erase-gag-state (state)

; Avoid repeated printing of the gag state, e.g. for a theorem under several
; levels of encapsulate or under certify-book.  We set 'gag-state here rather
; than directly inside print-gag-state because gag-state is untouchable and
; translate11 is called on in the process of running :psog.

  (pprogn (f-put-global 'gag-state-saved (f-get-global 'gag-state state) state)
          (f-put-global 'gag-state nil state)))

(defun print-gag-state (state)
  (io? error nil state
       ()
       (let ((gag-state (f-get-global 'gag-state state)))
         (pprogn (erase-gag-state state)
                 (print-gag-state1 gag-state state)))))

#+acl2-par
(defun clause-id-is-top-level (cl-id)
  (and (null (access clause-id cl-id :pool-lst))
       (equal (access clause-id cl-id :forcing-round) 0)))

#+acl2-par
(defun clause-id-is-induction-round (cl-id)
  (and (access clause-id cl-id :pool-lst)
       (equal (access clause-id cl-id :forcing-round) 0)))

#+acl2-par
(defun clause-id-is-forcing-round (cl-id)

; Note that we do not have a recognizer for inductions that occur while
; forcing.

  (not (equal (access clause-id cl-id :forcing-round) 0)))

#+acl2-par
(defun print-acl2p-checkpoints1 (checkpoints top-level-banner-printed
                                             induction-banner-printed
                                             forcing-banner-printed)
  (declare (ignorable top-level-banner-printed induction-banner-printed
                      forcing-banner-printed))
  (cond
   ((atom checkpoints)
    nil)
   (t (let* ((cl-id (caar checkpoints))
             (prettyified-clause (cdar checkpoints))
             (top-level-banner-printed
              (or top-level-banner-printed
                  (if (and (not top-level-banner-printed)
                           (clause-id-is-top-level cl-id))
                      (prog2$ (cw "~%*** ACL2(p) key checkpoint[s] at the ~
                                   top level: ***~%")
                              t)
                    top-level-banner-printed)))
             (induction-banner-printed
              (or induction-banner-printed
                  (if (and (not induction-banner-printed)
                           (clause-id-is-induction-round cl-id))
                      (prog2$ (cw "~%*** ACL2(p) key checkpoint[s] under ~
                                   induction: ***~%")
                              t)
                    induction-banner-printed)))

             (forcing-banner-printed
              (or forcing-banner-printed
                  (if (and (not forcing-banner-printed)
                           (clause-id-is-forcing-round cl-id))
                      (prog2$ (cw "~%*** ACL2(p) key checkpoint[s] under a ~
                                   forcing round: ***~%")
                              t)
                    forcing-banner-printed))))
        (progn$ (cw "~%~s0~%"
                    (string-for-tilde-@-clause-id-phrase cl-id))
                (cw "~x0~%" prettyified-clause)
                (print-acl2p-checkpoints1 (cdr checkpoints)
                                          top-level-banner-printed
                                          induction-banner-printed
                                          forcing-banner-printed))))))

#+acl2-par
(deflock *acl2p-checkpoint-saving-lock*)

#+acl2-par
(defun erase-acl2p-checkpoints-for-summary (state)
  (with-acl2p-checkpoint-saving-lock
   (f-put-global 'acl2p-checkpoints-for-summary nil state)))

#+acl2-par
(defun print-acl2p-checkpoints (state)
  (with-acl2p-checkpoint-saving-lock

; Technically, this lock acquisition is unnecessary, because we only print
; acl2p checkpoints after we have finished the waterfall (ACL2(p) is operating
; with only a single thread at that point).  However, we go ahead and do it
; anyway, as an example of good programming practice.

   (prog2$
    (if (and (f-get-global 'waterfall-parallelism state)
             (f-get-global 'acl2p-checkpoints-for-summary state))
        (prog2$
         (cw "~%~%Printing the ACL2(p) key checkpoints that were encountered ~
              during the proof attempt (and pushed for induction or ~
              sub-induction).  Note that some of these checkpoints may have ~
              been later proven by induction or sub-induction.  Thus, you ~
              must decide for yourself which of these checkpoints are ~
              relevant to debugging your proof.~%~%")
         (print-acl2p-checkpoints1
          (reverse (f-get-global 'acl2p-checkpoints-for-summary
                                 state))
          nil nil nil))
      nil)

; At first we followed the precedent set by erase-gag-state and tried only
; clearing the set of ACL2(p) checkpoints to print whenever this function is
; called.  However, we noticed that successful proof attempts then do not clear
; the saved checkpoints.  As such, we also clear the checkpoints in defthm-fn1.

    (erase-acl2p-checkpoints-for-summary state))))

(defun tilde-@p (arg)
  (declare (xargs :guard t))
  (or (stringp arg)
      (and (consp arg)
           (stringp (car arg))
           (character-alistp (cdr arg)))))

(defun print-failure1 (erp ctx state)
  (let ((channel (proofs-co state)))
    (pprogn
     (newline channel state)
     (error-fms-channel nil ctx "~@0See :DOC failure."
                        (list (cons #\0
                                    (if (tilde-@p erp)
                                        erp
                                      "")))
                        channel state)
     (newline channel state)
     (io? summary nil state (channel)
          (fms *proof-failure-string* nil channel state nil)))))

(defun print-failure (erp event-type ctx state)
  (pprogn
   (io? summary nil state nil
        (print-gag-state state))
   #+acl2-par
   (print-acl2p-checkpoints state)
   (cond ((not (member-eq event-type

; For events whose failure already produces a message of type error, we
; consider further failure messages to be of type summary.  That way we see the
; true source of errors when output is inhibited to show only errors.  Compound
; events are in this category.  Defthm is not, since when a proof fails no
; output of type error is typically generated, and thus the only error
; generated for defthm is typically the failure message from print-failure1.
; Defun is however in this category, since proof failures result in error
; messages about guard proof failure or termination proof failure.

                          '(encapsulate progn make-event defun)))
          (cond
           ((output-ignored-p 'error state)
            (io? summary nil state (erp ctx)
                 (print-failure1 erp ctx state)))
           (t (print-failure1 erp ctx state))))
         ((member-eq 'errors (f-get-global 'inhibited-summary-types state))
          state)
         (t (io? summary nil state (erp ctx)
                 (print-failure1 erp ctx state))))))

; The following two defproxy events will be "upgraded" to defstub events after
; state-p, which is called in the guard for each, is in :logic mode.
(defproxy initialize-event-user (* * state) => state)
(defproxy finalize-event-user (* * state) => state)

(defun lmi-seed (lmi)

; The "seed" of an lmi is either a symbolic name denoting an event, a doublet
; whose cadr is such a name and whose car is :termination-theorem or
; :guard-theorem, or else a term.  In particular, the seed of a symbolp lmi is
; the lmi itself, the seed of a rune is its base symbol, the seed of a :theorem
; is the term indicated, and the seed of an :instance or :functional-instance
; is obtained recursively from the inner lmi.

  (cond ((atom lmi) ; Lmi is a symbolic name denoting an event.
         lmi)
        (t (case (car lmi)
             ((:instance :functional-instance)
              (lmi-seed (cadr lmi)))
             (:theorem
              (cadr lmi))
             ((:termination-theorem :termination-theorem!)
              (list :termination-theorem (cadr lmi)))
             (:guard-theorem
              (list :guard-theorem (cadr lmi)))
             (otherwise
              (base-symbol lmi))))))

(defun lmi-techs (lmi)
  (cond
   ((atom lmi) nil)
   ((eq (car lmi) '(:theorem
                    :termination-theorem
                    :termination-theorem!
                    :guard-theorem))
    nil)
   ((eq (car lmi) :instance)
    (add-to-set-equal "instantiation" (lmi-techs (cadr lmi))))
   ((eq (car lmi) :functional-instance)
    (add-to-set-equal "functional instantiation" (lmi-techs (cadr lmi))))
   (t nil)))

(defun lmi-seed-lst (lmi-lst)
  (cond ((null lmi-lst) nil)
        (t (add-to-set-equal (lmi-seed (car lmi-lst))
                             (lmi-seed-lst (cdr lmi-lst))))))

(defun lmi-techs-lst (lmi-lst)
  (cond ((null lmi-lst) nil)
        (t (union-equal (lmi-techs (car lmi-lst))
                        (lmi-techs-lst (cdr lmi-lst))))))

(defun lmi-seeds-info (flg lst)

; Lst is a list of objects each of which could be returned by lmi-seed, hence
; categorized as follows:

; a symbolic name denoting an event;
; a theorem; or
; of the form (:kwd name), where :kwd is :termination-theorem or
;    :guard-theorem, and name is a symbolic name denoting an event.

; Depending on flg we return the following.

; If flg = t, then return all such symbolic names, including each name for
; which (:kwd name) is in lst.

; If flg = nil, then return only the theorems among lst.

; Otherwise (in which case flg = 'hint-events), return all non-theorems among
; list.  This is the same as the case flg = t except that (:kwd name) is not
; replaced by name -- it is included in the result as (:kwd name).

  (cond ((endp lst) nil)
        (t (let ((lmi-type
                  (cond ((mbe :logic (atom (car lst))
                              :exec (symbolp (car lst)))
                         'name)
                        ((member-eq (car (car lst))
                                    '(:termination-theorem :guard-theorem))
                         'extended-name)
                        (t 'theorem))))
             (cond ((eq flg t)
                    (case lmi-type
                      (name
                       (cons (car lst) (lmi-seeds-info flg (cdr lst))))
                      (extended-name
                       (cons (cadr (car lst)) (lmi-seeds-info flg (cdr lst))))
                      (otherwise
                       (lmi-seeds-info flg (cdr lst)))))
                   ((iff flg (eq lmi-type 'theorem))
                    (lmi-seeds-info flg (cdr lst)))
                   (t
                    (cons (car lst) (lmi-seeds-info flg (cdr lst)))))))))

(defun print-runes-summary (ttree state)
  (let ((runes (merge-sort-runes (all-runes-in-ttree ttree nil))))
    (pprogn (put-event-data 'rules runes state)
            (io? summary nil state
                 (runes)
                 (let ((channel (proofs-co state)))
                   (mv-let (col state)
                     (fmt1 "Rules: ~y0~|"
                           (list (cons #\0 runes))
                           0 channel state nil)
                     (declare (ignore col))
                     state))))))

(defun use-names-in-ttree (ttree names-only)

; Warning: This does not include use-names under :clause-processor tags.

  (let* ((objs (tagged-objects :USE ttree))
         (lmi-lst (append-lst (strip-cars (strip-cars objs))))
         (seeds (lmi-seed-lst lmi-lst)))
    (if names-only
        (lmi-seeds-info t seeds)
      (lmi-seeds-info 'hint-events seeds))))

(defun by-names-in-ttree (ttree names-only)

; Warning: This does not include by-names under :clause-processor tags.

  (let* ((objs (tagged-objects :BY ttree))
         (lmi-lst (append-lst (strip-cars objs)))
         (seeds (lmi-seed-lst lmi-lst)))
    (if names-only
        (lmi-seeds-info t seeds)
      (lmi-seeds-info 'hint-events seeds))))

(defrec clause-processor-hint
  (term stobjs-out . verified-p)
  nil)

(defun collect-non-hint-events (lst non-symbols-okp)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (let ((x (car lst)))
             (cond
              ((symbolp x)
               (collect-non-hint-events (cdr lst) non-symbols-okp))
              ((and non-symbols-okp
                    (consp x)
                    (consp (cdr x))
                    (null (cddr x))
                    (member-eq (car x)
                               '(:termination-theorem :guard-theorem))
                    (symbolp (cadr x)))
               (collect-non-hint-events (cdr lst) non-symbols-okp))
              (t (cons x
                       (collect-non-hint-events (cdr lst)
                                                non-symbols-okp))))))))

(defun hint-events-symbols (lst)
  (declare (xargs :guard (null (collect-non-hint-events lst t))))
  (cond ((atom lst) nil)
        ((symbolp (car lst))
         (cons (car lst)
               (hint-events-symbols (cdr lst))))
        (t
         (cons (cadr (car lst))
               (hint-events-symbols (cdr lst))))))

(defmacro get-summary-data (summary-data field &optional names-only)
  (declare (xargs :guard (member-eq field '(:use-names
                                            :by-names
                                            :clause-processor-fns))))
  (let ((val-expr `(access summary-data ,summary-data ,field)))
    `(cond (,names-only (let ((lst ,val-expr))
                          (if (symbol-listp lst) ; common case
                              lst
                            (hint-events-symbols lst))))
           (t ,val-expr))))

(defun cl-proc-data-in-ttree-1 (objs use-names by-names cl-proc-fns
                                     names-only)

; Each member of the list, objs, is of the form (cl-proc-hint summary-data
; . new-clauses), as per the call of add-to-tag-tree! on tag :clause-processor
; in the definition of apply-top-hints-clause.

  (cond ((endp objs) (mv use-names by-names cl-proc-fns))
        (t (let* ((obj (car objs))
                  (cl-proc-hint (car obj))
                  (cl-proc-fn (ffn-symb (access clause-processor-hint
                                                cl-proc-hint
                                                :term)))
                  (new-cl-proc-fns

; We want to present the proof-builder clause-processor as a built-in, the way
; we present simplify-clause and the other waterfall clause-processors.  So we
; avoid recording it here.

                   (if (eq cl-proc-fn 'proof-builder-cl-proc)
                       cl-proc-fns
                     (cons cl-proc-fn cl-proc-fns)))
                  (summary-data (cadr obj)))
             (cond
              ((null summary-data)
               (cl-proc-data-in-ttree-1 (cdr objs) use-names by-names
                                        new-cl-proc-fns
                                        names-only))
              (t (cl-proc-data-in-ttree-1
                  (cdr objs)
                  (append (get-summary-data summary-data :use-names names-only)
                          use-names)
                  (append (get-summary-data summary-data :by-names names-only)
                          by-names)
                  (append (access summary-data summary-data
                                  :clause-processor-fns)
                          new-cl-proc-fns)
                  names-only)))))))

(defun cl-proc-data-in-ttree (ttree names-only)
  (cl-proc-data-in-ttree-1 (tagged-objects :CLAUSE-PROCESSOR ttree)
                           nil nil nil
                           names-only))

(defun hint-event-names-in-ttree (ttree)
  (mv-let (use-names by-names cl-proc-fns)
    (cl-proc-data-in-ttree ttree nil)
    (mv (merge-sort-lexorder (union-equal-removing-duplicates
                              use-names
                              (use-names-in-ttree ttree nil)))
        (merge-sort-lexorder (union-equal-removing-duplicates
                              by-names
                              (by-names-in-ttree ttree nil)))
        (sort-symbol-listp cl-proc-fns))))

(defun print-hint-events-summary (ttree state)
  (flet ((make-rune-like-objs (kwd lst)
                              (and lst ; optimization for common case
                                   (pairlis$ (make-list (length lst)
                                                        :INITIAL-ELEMENT kwd)
                                             (pairlis$ lst nil)))))
    (mv-let (use-lst by-lst cl-proc-fns)
      (hint-event-names-in-ttree ttree)
      (let ((lst (append (make-rune-like-objs :BY by-lst)
                         (make-rune-like-objs :CLAUSE-PROCESSOR cl-proc-fns)
                         (make-rune-like-objs :USE use-lst))))
        (pprogn (put-event-data 'hint-events lst state)
                (cond (lst (io? summary nil state
                                (lst)
                                (let ((channel (proofs-co state)))
                                  (mv-let (col state)
                                    (fmt1 "Hint-events: ~y0~|"
                                          (list (cons #\0 lst))
                                          0 channel state nil)
                                    (declare (ignore col))
                                    state))))
                      (t state)))))))

(defun print-splitter-rules-summary-1 (cl-id clauses
                                             case-split immed-forced if-intro
                                             state)

; The caller (or its caller, etc.) must take responsibility for surrounding
; this call with any necessary io? wrapper.

  (let ((channel (proofs-co state)))
    (mv-let
      (col state)
      (fmt1 "Splitter ~s0 (see :DOC splitter)~@1~s2~|~@3~@4~@5"
            (list
             (cons #\0 (if cl-id "note" "rules"))
             (cons #\1
                   (if cl-id

; Since we are printing during a proof (see comment above) but not already
; printing the clause-id, we do so now.  This is redundant if (f-get-global
; 'print-clause-ids state) is true, but necessary when parallelism is enabled
; for #+acl2-par, and anyhow, adds a bit of clarity.

; We leave it to waterfall-msg1 to track print-time, so we avoid calling
; waterfall-print-clause-id.

                       (msg " for ~@0 (~x1 subgoal~#2~[~/s~])"
                            (tilde-@-clause-id-phrase cl-id)
                            (length clauses)
                            clauses)
                     ""))
             (cons #\2 (if cl-id "." ":"))
             (cons #\3
                   (cond
                    (case-split (msg "  case-split: ~y0"
                                     case-split))
                    (t "")))
             (cons #\4
                   (cond
                    (immed-forced (msg "  immed-forced: ~y0"
                                       immed-forced))
                    (t "")))
             (cons #\5
                   (cond
                    (if-intro (msg "  if-intro: ~y0"
                                   if-intro))
                    (t ""))))
            0 channel state nil)
      (declare (ignore col))
      (cond ((and cl-id (gag-mode))
             (newline channel state))
            (t state)))))

(defun print-splitter-rules-summary (cl-id clauses ttree state)

; When cl-id is nil, we are printing for the summary; so clauses is ignored,
; and we need here to use a suitable wrapper (io? summary ...).  Otherwise we
; are printing during a proof under waterfall-msg1, for gag-mode, in which case
; we are already under a suitable io? wrapper.

  (let ((if-intro (merge-sort-runes
                   (tagged-objects 'splitter-if-intro ttree)))
        (case-split (merge-sort-runes
                     (tagged-objects 'splitter-case-split ttree)))
        (immed-forced (merge-sort-runes
                       (tagged-objects 'splitter-immed-forced ttree))))
    (cond ((or if-intro case-split immed-forced)
           (cond
            (cl-id ; printing during a proof
             (pprogn
              (newline (proofs-co state) state)
              (with-output-lock
               (print-splitter-rules-summary-1
                cl-id clauses case-split immed-forced if-intro state))))
            (t ; printing for the summary
             (pprogn
              (put-event-data 'splitter-rules
                              (list case-split immed-forced if-intro)
                              state)
              (io? summary nil state
                   (cl-id clauses case-split immed-forced if-intro)
                   (print-splitter-rules-summary-1
                    cl-id clauses case-split immed-forced if-intro state))))))
          (cl-id state)
          (t (put-event-data 'splitter-rules nil state)))))

(defun print-rules-and-hint-events-summary (acc-ttree state)

; This function is expected not to be called under (io? ...), so subroutines
; are responsible for adding such wrappers.  With this structure, the
; subroutines can (and are) also responsible for calling put-event-data outside
; such (io? ...) wrappers, so that put-event-data is not called again during
; proof replay (via :pso and related utilities).

  (let ((inhibited-summary-types (f-get-global 'inhibited-summary-types
                                               state)))
    (pprogn
     (cond ((member-eq 'rules inhibited-summary-types)
            state)
           (t (print-runes-summary acc-ttree state)))
     (cond ((member-eq 'hint-events inhibited-summary-types)
            state)
           (t (print-hint-events-summary acc-ttree state)))
     (cond ((member-eq 'splitter-rules inhibited-summary-types)
            state)
           (t (print-splitter-rules-summary nil nil acc-ttree state)))

; Since we've already printed from the accumulated-ttree, there is no need to
; print again the next time we want to print rules or hint-events.  That is why
; we set the accumulated-ttree to nil here.  If we ever want certify-book, say,
; to be able to print rules and hint-events when it fails, then we should use a
; stack of ttrees rather than a single accumulated-ttree.

     (f-put-global 'accumulated-ttree nil state))))

(defun modified-system-attachment (pair recs)
  (cond ((endp recs) (cons (car pair) nil))
        (t (let ((tmp (assoc-eq (car pair)
                                (access attachment (car recs) :pairs))))
             (cond (tmp (and (not (eq (cdr tmp) (cdr pair)))
                             tmp))
                   (t (modified-system-attachment pair (cdr recs))))))))

(defun modified-system-attachments-1 (pairs recs acc)
  (cond ((endp pairs) acc)
        (t (modified-system-attachments-1
            (cdr pairs)
            recs
            (let ((x (modified-system-attachment (car pairs) recs)))
              (if x
                  (cons x acc)
                acc))))))

(defun modified-system-attachments (state)
  (let* ((wrld (w state))
         (lst (global-val 'attachment-records wrld))
         (cache (f-get-global 'system-attachments-cache state)))

; It would be nice to use EQ instead of EQUAL in the test just below.  However,
; that would not really be legal ACL2; besides, EQUAL is probably sufficiently
; efficient, since we can expect it to devolve to a successful EQ most of the
; time and perhaps produce a quick failure otherwise.

    (cond ((equal lst (car cache))
           (value (cdr cache)))
          (t (let ((mods (modified-system-attachments-1
                          (global-val 'attachments-at-ground-zero wrld)
                          lst
                          nil)))
               (pprogn (f-put-global 'system-attachments-cache
                                     (cons lst mods)
                                     state)
                       (value mods)))))))

(defun print-system-attachments-summary (state)
  (cond
   ((f-get-global 'boot-strap-flg state)

; Then world global attachments-at-ground-zero is not yet set for use in
; modified-system-attachments.

    state)
   (t
    (mv-let (erp pairs state)
      (modified-system-attachments state)
      (assert$
       (null erp)
       (pprogn
        (put-event-data 'system-attachments pairs state)
        (io? summary nil state
             (pairs)
             (cond ((member-eq 'system-attachments
                               (f-get-global 'inhibited-summary-types state))
                    state)
                   ((null pairs)
                    state)
                   (t
                    (let ((channel (proofs-co state)))
                      (mv-let
                        (col state)

; Let's line up the attachment list with "Rules: ".

                        (fmt1 "Modified system attachments:~|       ~y0"
                              (list (cons #\0 (alist-to-doublets pairs)))
                              0 channel state nil)
                        (declare (ignore col))
                        state)))))))))))

(defun print-summary (erp noop-flg event-type ctx state)

; This function prints the Summary paragraph.  Part of that paragraph includes
; the timers.  Time accumulated before entry to this function is charged to
; 'other-time.  We then pop the timers, adding their accumulations to the newly
; exposed time.  This has the effect of charging superior events for the time
; used by their inferiors.

; For simplicity, we do the above and all other computations even if we are not
; to print the summary or parts of it.  For example, we handle
; pop-warning-frame regardless of whether or not we print the warning summary.

; If erp is non-nil, the "event" caused an error and we do not scan for
; redefined names but we do print the failure string.  If noop-flg is t then
; the installed world did not get changed by the "event" (e.g., the "event" was
; redundant or was not really an event but was something like a call of (thm
; ...)) and we do not scan the most recent event block for redefined names.

; If erp is a message, as recognized by tilde-@p, then that message will be
; printed by the call below of print-failure.

  #+(and (not acl2-loop-only) acl2-rewrite-meter) ; for stats on rewriter depth
  (cond ((atom ctx))
        ((symbolp (cdr ctx))
         (cond ((not (eql *rewrite-depth-max* 0))
                (setq *rewrite-depth-alist*
                      (cons (cons (intern (symbol-name (cdr ctx)) "ACL2")

; We intern into the ACL2 package so that our tools can read this alist back in
; without needing a DEFPKG to be executed first.  The name is really all we
; care about here anyhow; all we would do with it is to search for it in the
; indicated file.

                                  *rewrite-depth-max*)
                            *rewrite-depth-alist*))
                (setq *rewrite-depth-max* 0))))
        ((eq (car ctx) 'certify-book)
         (let* ((bookname (extend-pathname
                           (f-get-global 'connected-book-directory state)
                           (cdr ctx)
                           state))
                (filename (concatenate 'string bookname ".lisp")))
           (with-open-file
             (str filename
                  :direction :output
                  :if-exists :rename-and-delete)
             (format str
                     "~s~%"
                     (cons filename
                           (merge-sort-cdr-> *rewrite-depth-alist*)))))
         (setq *rewrite-depth-alist* nil)))

  #-acl2-loop-only (dmr-flush)

  (let ((wrld (w state)))
    (cond
     ((global-val 'include-book-path wrld)
      (clear-event-data state))
     (t
      (let ((steps (prover-steps state)))
        (pprogn
         (clear-event-data state)
         (prog2$ (clear-warning-summaries) state)
         (let ((trip (car wrld)))
           (cond ((and (not noop-flg)
                       (eq (car trip) 'EVENT-LANDMARK)
                       (eq (cadr trip) 'GLOBAL-VALUE))
                  (put-event-data 'namex
                                  (access-event-tuple-namex (cddr trip))
                                  state))
                 (t state)))
         (put-event-data 'prover-steps-counted steps state)
         (put-event-data 'form ctx state)
         (increment-timer 'other-time state)
         (put-event-data 'time
                         (list (car (get-timer 'prove-time state))
                               (car (get-timer 'print-time state))
                               (car (get-timer 'proof-tree-time state))
                               (car (get-timer 'other-time state)))
                         state)
         (let ((abort-causes
                (tagged-objects 'abort-cause
                                (f-get-global 'accumulated-ttree state))))
           (if abort-causes
               (put-event-data 'abort-causes abort-causes state)
             state))
         (cond
          ((ld-skip-proofsp state)
           (pprogn (if (or erp noop-flg)
                       state
                     (print-redefinition-warning wrld ctx state))
                   (pop-timer 'prove-time t state)
                   (pop-timer 'print-time t state)
                   (pop-timer 'proof-tree-time t state)
                   (pop-timer 'other-time t state)
                   (mv-let (warnings state)
                     (pop-warning-frame nil state)
                     (declare (ignore warnings))
                     state)))
          (t

; Even if this case were only taken when 'summary is inhibited, we would still
; use io? below, and inside some functions below, because of its window hacking
; and saved-output functions.

           (let ((output-ignored-p (output-ignored-p 'summary state)))
             (pprogn
              (if (or erp noop-flg output-ignored-p)
                  state
                (print-redefinition-warning wrld ctx state))
              (io? summary nil state
                   ()
                   (let ((channel (proofs-co state)))
                     (cond ((member-eq 'header
                                       (f-get-global 'inhibited-summary-types
                                                     state))
                            state)
                           (t
                            (pprogn (newline channel state)
                                    (princ$ "Summary" channel state)
                                    (newline channel state))))))
              (io? summary nil state
                   (ctx)
                   (let ((channel (proofs-co state)))
                     (cond ((member-eq 'form
                                       (f-get-global 'inhibited-summary-types
                                                     state))
                            state)
                           (t
                            (mv-let
                              (col state)
                              (fmt1 "Form:  " nil 0 channel state nil)
                              (mv-let
                                (col state)
                                (fmt-ctx ctx col channel state)
                                (declare (ignore col))
                                (newline channel state)))))))
              (print-rules-and-hint-events-summary
               (f-get-global 'accumulated-ttree state)
               state)
              (print-system-attachments-summary state)
              (print-warnings-summary state)
              (print-time-summary state)
              (print-steps-summary steps state)
              (progn$
               (and (not output-ignored-p)

; If the time-tracker call below is changed, update :doc time-tracker
; accordingly.

                    (time-tracker
                     :tau :print?
                     :min-time 1
                     :msg
                     (concatenate
                      'string
                      "For the proof above, the total "
                      (if (f-get-global 'get-internal-time-as-realtime
                                        state)
                          "realtime"
                        "runtime")
                      " spent in the tau system was ~st seconds.  See :DOC ~
                    time-tracker-tau.~|~%")))

; At one time we put (time-tracker :tau :end) here.  But in community book
; books/hints/basic-tests.lisp, the recursive proof attempt failed just below
; (add-custom-keyword-hint :recurse ...), apparently because the time-tracker
; wasn't initialized for tag :tau when the proof resumed.  It's harmless anyhow
; to avoid :end here; after all, we invoke :end before invoking :init anyhow,
; in case the proof was aborted without printing this part of the summary.

               state)
              (pprogn
               (cond (erp
                      (pprogn
                       (print-failure erp event-type ctx state)
                       (cond
                        ((f-get-global 'proof-tree state)
                         (io? proof-tree nil state
                              (ctx)
                              (pprogn (f-put-global 'proof-tree-ctx
                                                    (cons :failed ctx)
                                                    state)
                                      (print-proof-tree state))))
                        (t state))))
                     (t (pprogn
                         #+acl2-par
                         (erase-acl2p-checkpoints-for-summary state)
                         state)))
               (f-put-global 'proof-tree nil state))))))))))))

(defun with-prover-step-limit-fn (limit form no-change-flg)

; See the Essay on Step-limits.

  (let ((protected-form
         `(state-global-let*
           ((step-limit-record
             (make step-limit-record
                   :start wpsl-limit
                   :strictp wpsl-strictp
                   :sub-limit nil)))
           (check-vars-not-free (wpsl-limit wpsl-strictp)
                                ,form))))
    `(mv-let
      (wpsl-limit wpsl-strictp) ; for child environment
      (let ((limit ,limit))
        (cond ((or (null limit)
                   (eql limit *default-step-limit*))
               (mv *default-step-limit* nil))
              ((eq limit :start)

; We inherit the  limit and strictness from the parent environment.

; Warning: Keep the following code in sync with initial-step-limit.

               (let ((rec (f-get-global 'step-limit-record state)))
                 (cond (rec (mv (or (access step-limit-record rec :sub-limit)
                                    (f-get-global 'last-step-limit state))

; Warning: Keep the following case in sync with step-limit-strictp.

                                (access step-limit-record rec :strictp)))
                       (t (let ((limit (step-limit-from-table (w state))))
                            (mv limit
                                (< limit *default-step-limit*)))))))
              ((and (natp limit)
                    (< limit *default-step-limit*))
               (mv limit t))
              (t (mv 0 ; arbitrary
                     (er hard! 'with-prover-step-limit
                         "Illegal value for ~x0, ~x1.  See :DOC ~
                          with-prover-step-limit."
                         'with-prover-step-limit
                         limit)))))
      ,(cond
        (no-change-flg
         `(state-global-let*
           ((last-step-limit wpsl-limit))
           ,protected-form))
        (t
         `(let ((wpsl-old-limit ; existing value of last-step-limit
                 (f-get-global 'last-step-limit state)))
            (pprogn
             (f-put-global 'last-step-limit wpsl-limit state) ; new step-limit
             (mv-let
              (erp val state)
              (check-vars-not-free (wpsl-old-limit)
                                   ,protected-form)
              (let* ((steps-taken

; Even if the value of 'last-step-limit is -1, the following difference
; correctly records the number of prover steps taken, where we consider it a
; step to cause an error at the transition in step-limit from 0 to -1.  After
; all, the sub-event will say "more than", which assumes that this final step
; is counted.

                      (- wpsl-limit (f-get-global 'last-step-limit state)))
                     (new-step-limit (cond
                                      ((< wpsl-old-limit steps-taken)
                                       -1)
                                      (t (- wpsl-old-limit steps-taken)))))
                (pprogn
                 (f-put-global 'last-step-limit new-step-limit state)
                 (cond
                  (erp (mv erp val state))

; Next we consider the case that the step-limit is exceeded after completion of
; a sub-event of a compound event, for example, between the two defthm events
; below.

; (set-prover-step-limit 100)
; (encapsulate
;  ()
;  (with-prover-step-limit 500
;                          (defthm foo
;                            (equal (append (append x y) z)
;                                   (append x y z))))
;  (defthm bar (equal (car (cons x y)) x)))

                  ((and (eql new-step-limit -1)
                        (step-limit-strictp state))
                   (step-limit-error t))
                  (t (value val)))))))))))))

#+acl2-loop-only
(defmacro with-prover-step-limit (limit form
                                        &optional (actual-form 'nil
                                                               actual-form-p))

; See the Essay on Step-limits.

; Form should evaluate to an error triple.  A value of :START for limit says
; that we use the current limit, i.e., the value of state global
; 'last-step-limit if the value of state global 'step-limit-record is not nil,
; else the value from the acl2-defaults-table; see initial-step-limit.

  (declare (xargs :guard (or (not actual-form-p)
                             (booleanp form))))
  (cond (actual-form-p
         (with-prover-step-limit-fn limit actual-form form))
        (t
         (with-prover-step-limit-fn limit form nil))))

#-acl2-loop-only
(defmacro with-prover-step-limit (limit form
                                        &optional (actual-form 'nil
                                                               actual-form-p))
  (declare (ignore limit))
  (cond (actual-form-p actual-form)
        (t form)))

(defmacro with-prover-step-limit! (limit form &optional no-change-flg)
  (declare (xargs :guard (booleanp no-change-flg)))
  (with-prover-step-limit-fn limit form no-change-flg))

; Start development of with-ctx-summarized.  But first we need to define
; set-w!.

; Essay on the proved-functional-instances-alist

; The world global 'proved-functional-instances-alist caches information about
; theorems proved on behalf of functional instantiation, in order to avoid the
; cost of re-proving such theorems.  In this Essay we track the flow of
; information to and from that world global.

; The above world global is a list of the following records.

(defrec proved-functional-instances-alist-entry

; Constraint-event-name is the name of an event such that the functional
; instance of that event's constraint (i.e., function's constraint or axiom's
; 'theorem property) by restricted-alist was proved on behalf of the event
; named behalf-of-event-name.  Note that behalf-of-event-name could be 0, e.g.,
; for a verify-guards event.  We arrange that restricted-alist is sorted; see
; the comment in event-responsible-for-proved-constraint.

  (constraint-event-name restricted-alist . behalf-of-event-name)
  t)

; In a nutshell, these records have the following life cycle:
; (1) They are created by hint translation, appealing to the existing value of
;     world global 'proved-functional-instances-alist to prune the list.
; (2) They go into tag-trees when hints are applied; see calls of
;     add-to-tag-tree with tags :use and :by in apply-use-hint-clauses and
;     apply-top-hints-clause1, respectively.
; (3) They are extracted from those tag-trees when events are installed.

; We focus now on (1).  Hint translation creates these records with functions
; translate-use-hint and translate-by-hint.  Translate-use-hint returns an
; object of the form

; (lmi-lst (hyp1 ... hypn) cl k event-names new-entries)

; while translate-by-hint returns an object of the form
;
; (lmi-lst thm-cl-set constraint-cl k event-names new-entries).

; In each case, new-entries is a list of
; proved-functional-instances-alist-entry records created by
; translate-lmi/functional-instance; just follow the call tree down from
; translate-use-hint or translate-by-hint to translate-lmi and then
; translate-lmi/functional-instance.  But following the call tree further, we
; see that new-entries ultimately comes from relevant-constraints, which in
; turn passes along the new-entries created by relevant-constraints1-axioms and
; relevant-constraints1.  These two functions use the already-existing records
; from world global 'proved-functional-instances-alist to prune the set of
; generated constraints (and save the behalf-of-event-name fields justifying
; such pruning for a suitable message -- see the call of tilde-@-lmi-phrase in
; apply-top-hints-clause-msg1).  These same two functions
; (relevant-constraints1-axioms and relevant-constraints1) also return a list
; of new proved-functional-instances-alist-entry records.

; The records created as above are missing the :behalf-of-event-name field
; (i.e., its value is nil), and that is how they go into tag-trees as
; components of values associated with :use and :by tags.  That missing field
; is eventually filled in by
; supply-name-for-proved-functional-instances-alist-entry in
; proved-functional-instances-from-tagged-objects, which is called by
; install-event in order to update world global
; 'proved-functional-instances-alist.

; End of Essay on the proved-functional-instances-alist

(defun supply-name-for-proved-functional-instances-alist-entry (name lst)
  (cond
   ((endp lst) nil)
   (t (cons (change proved-functional-instances-alist-entry (car lst)
                    :behalf-of-event-name name)
            (supply-name-for-proved-functional-instances-alist-entry name (cdr lst))))))

(defun proved-functional-instances-from-tagged-objects (name lst)

; For context, see the Essay on the proved-functional-instances-alist.

; Returns a list of proved-functional-instances-alist-entry records.  Lst is a
; list of values generated by calls

; (cdr (assoc-eq key (access prove-spec-var pspv :hint-settings)))

; where key is :use or :by, and where each member of lst is a value returned by
; translate-use-hint and translate-by-hint,

; (list x0 x1 x2 x3 x4 new-entries)

; -- although in the case of :by, this value could be an atom.

  (cond
   ((null lst) nil)
   ((atom (cdr (car lst)))
    (proved-functional-instances-from-tagged-objects name (cdr lst)))
   (t (append (supply-name-for-proved-functional-instances-alist-entry
               name (nth 5 (car lst)))
              (proved-functional-instances-from-tagged-objects
               name (cdr lst))))))

; Statistical and related information related to image size.
;
; Here is some information collected while first creating a small version near
; the completion of Version 1.8.
;
; At one point we had the following size statistic, using GCL 2.0:
;
; -rwxrwxr-x  1 kaufmann 13473876 May  1 11:27 small-saved_acl2
;
; We were able to account for nearly all of this 13.5 megabytes by the following
; reckoning.  Some associated code follows.
;
;  3.2    Raw GCL 2.0
;  2.9    Additional space from loading ACL2 object files
;         [note:  not much more than Nqthm, less than Pc-Nqthm!]
;  3.7    Conses (327648) from (count-objects (w state)), less those that
;         are from constants: (* 12 (- 327648 (- 21040 145))).  Note:
;         36,236 = (length (w state))
;  0.9    Extra conses (72888) generated by (get sym *CURRENT-ACL2-WORLD-KEY*);
;         see code below.  The first few such numbers, in order, are:
;         ((4207 . EVENT-LANDMARK) (3806 . COMMAND-LANDMARK)
;          (3734 . CLTL-COMMAND) (424 . EVENT-INDEX) (384 . COMMAND-INDEX)
;          (103 . PC-COMMAND-TABLE) (76 . PRIN1-WITH-SLASHES1) (75 . NTH)
;          (74 . NONCONSTRUCTIVE-AXIOM-NAMES) (72 . UPDATE-NTH))
;  0.3    Extra conses (23380) generated on symbol-plists; see code below
;  0.9    Mystery conses, (- 5.8 (+ 3.7 0.9 0.3)).  Where does 5.8 come from?
;         It's (* SYSTEM:LISP-PAGESIZE (- 1617 200)), where 1617 is the number
;         of cons pages in the ACL2 image and 200 is the number in an image
;         obtained by loading the .o files.
;  0.7    Extra cell space, other than cons, over the image obtained from .o
;         files only (including string, fixnum, ..., arrays for enabled
;         structures and type-set tables, ...):
;         (* SYSTEM:LISP-PAGESIZE
;            (- (+ 34 162 1 2 73 6 20)
;               (+  3  74 1 1 27 6 18)))
;  0.4    Other extra space, which is probably NOT related to TMP1.o space
;         (because presumably that space doesn't show up in (room)):
;         (* SYSTEM:LISP-PAGESIZE
;            (- (+ 6 107)
;               (+ 1 11)))
;  0.4    TMP1.o size calculated by:  (- 12195924 11823188), the difference
;         in sizes of two images built using (acl2::load-acl2 t) followed by
;         (initialize-acl2 nil nil t), but using a patch the second time that
;         avoided loading TMP1.o.
; ---
; 13.4    Total
;
; NOTE:  From
;
; ACL2>(length (w state))
; 36351
;
; we suspect that it would not be easy to significantly reduce the figure from
; (count-objects (w state)) above.
;
; Some relevant code:
;
; ;;;;;;;;;;;;;;; count.lisp
;
; (eval-when (load)
;            (si::allocate 'fixnum 100)))
;
; (defvar *monitor-count* nil)
;
; (defvar *string-count*
;   (make-array$ '(1) :initial-element (the fixnum 0) :element-type 'fixnum))
;
; (defvar *cons-count*
;   (make-array$ '(1) :initial-element (the fixnum 0) :element-type 'fixnum))
;
; (defvar *count-hash-table*
;   (make-hash-table :test 'eq :size 500000))
;
; (defun increment-string-count (len)
;   (declare (type fixnum len))
;   (cond ((and *monitor-count*
;               (= (the fixnum
;                    (logand (the fixnum (aref *string-count* 0))
;                            (the fixnum 4095)))
;                  0))
;          (format t "String count: ~s" (aref *string-count* 0))))
;   (setf (aref (the (array fixnum (1)) *string-count*)
;               0)
;         (the fixnum (1+ (the fixnum
;                              (+ (the fixnum len)
;                                 (the fixnum (aref *string-count* 0)))))))
;   t)
;
; (defun increment-cons-count ()
;   (cond ((and *monitor-count*
;               (= (the fixnum
;                    (logand (the fixnum (aref *cons-count* 0))
;                            (the fixnum 4095)))
;                  0))
;          (format t "Cons count: ~s" (aref *cons-count* 0))))
;   (setf (aref (the (array fixnum (1)) *cons-count*)
;               0)
;         (the fixnum (+ 1 (the fixnum (aref *cons-count* 0)))))
;   t)
;
; (defvar *acl2-strings*)
;
; (defun count-objects1 (x)
;   (cond
;    ((consp x)
;     (cond
;      ((gethash x *count-hash-table*)
;       nil)
;      (t
;       (increment-cons-count)
;       (setf (gethash x *count-hash-table*) t)
;       (count-objects1 (car x))
;       (count-objects1 (cdr x)))))
;    ((stringp x)
;     (or (gethash x *count-hash-table*)
;         (progn (increment-string-count (the fixnum (length x)))
;                (setq *acl2-strings* (cons x *acl2-strings*))
;                (setf (gethash x *count-hash-table*) t))))))
;
; (defun count-objects (x &optional clear)
;   (setq *acl2-strings* nil)
;   (setf (aref *cons-count* 0) 0)
;   (setf (aref *string-count* 0) 0)
;   (when clear
;     (clrhash *count-hash-table*))
;   (count-objects1 x)
;   (list 'cons-count (aref *cons-count* 0)
;         'string-count (aref *string-count* 0)))
;
; ;;;;;;;;;;;;;;; end of count.lisp
;
; (compile
;  (defun extra-count (&aux ans)
;    ;;  (count-objects (w state)) already done
;    (do-symbols (sym "ACL2")
;      (let ((temp (get sym *CURRENT-ACL2-WORLD-KEY*)))
;        (cond (temp
;               (let ((count (count-objects temp)))
;                 (cond
;                  (count (push (cons sym count) ans))))))))
;    ans))
;
; (progn (setq new-alist
;              (stable-sort
;               (loop for x in (extra-count)
;                     collect (cons (caddr x) (car x)))
;               (function (lambda (x y) (> (car x) (car y))))))
;        17)
;
; (loop for x in new-alist
;       sum (car x))
;
; ACL2>(take 10 new-alist)
; ((4207 . EVENT-LANDMARK) (3806 . COMMAND-LANDMARK)
;  (3734 . CLTL-COMMAND) (424 . EVENT-INDEX) (384 . COMMAND-INDEX)
;  (103 . PC-COMMAND-TABLE) (76 . PRIN1-WITH-SLASHES1) (75 . NTH)
;  (74 . NONCONSTRUCTIVE-AXIOM-NAMES) (72 . UPDATE-NTH))
;
; ACL2>(length new-alist)
; 3835
;
; Note that the symbol-plists also take up space.
;
; (compile
;  (defun more-count (&aux ans)
;    ;;  (count-objects (w state)) already done
;    (do-symbols (sym "ACL2")
;      (let ((temp (symbol-plist sym)))
;        (cond (temp
;               (let ((count (count-objects temp)))
;                 (cond
;                  (count (push (cons (cadr count) sym) ans))))))))
;    ans))
;
; (progn (setq more-alist
;              (stable-sort
;               (more-count)
;               (function (lambda (x y) (> (car x) (car y))))))
;        17)
;
; ACL2>(car more-alist)
; (180 . AREF)
;
; ACL2>(loop for x in more-alist sum (car x))
; [lots of GCs]
; 38657
; [Note:  Was 7607 using LISP package in raw GCL.]
;
; Note:  There are 3835 symbols for which ACL2 causes at least two conses on
; their symbol-plist, in the following sense.
;
; (let ((temp 0))
;        (do-symbols (x "ACL2")
;          (when (get x *CURRENT-ACL2-WORLD-KEY*)
;            (setq temp (1+ temp))))
;        temp)
;
; But that still leaves (- 38657 (+ 7607 (* 2 3835))) = 23380 conses not
; accounted for.  That's 281K of memory for "phantom" symbol-plist conses?
;
; Consider just those conses in (w state) other than 'const conses, since (except
; for the cell used to extend (w state)) these are part of the load image.
;
; (compile (defun foo ()
;            (let ((temp (loop for trip in (w state)
;                              when (eq (cadr trip) 'const)
;                              collect trip)))
;              (list (length temp) (count-objects temp)))))
; (foo)
; -->
; (145 (CONS-COUNT 21040 STRING-COUNT 5468))
;
; End of statistical and related information related to image size.

(defun add-command-landmark (defun-mode form cbd last-make-event-expansion
                              wrld)

; As with add-event-landmark above, we first update the world index
; and then add the command-landmark.  However, here it is crucial that
; the index be inside the landmark, i.e., that the landmark happen
; last.  Suppose we put the landmark down first and then added the
; index for that landmark.  If we later did a :ubt of the subsequent
; command, we would kill the index entry.  No harm would come then.
; But n commands later we would find the index out of sync with the
; maximum command number.  The problem is that :ubt keys on
; 'command-landmark and we ought to keep them outside everything else.

; The function maybe-add-command-landmark, which ld-loop uses to add
; command-landmarks in response to user commands, relies upon the fact
; that well-formed worlds always contain a command-landmark as their
; first element.

; Defun-Mode is generally the default-defun-mode of the world in which this
; form is being executed.  But there are two possible exceptions.  When we add
; the command landmarks for enter-boot-strap-mode and exit-boot-strap-mode we
; just use the defun-mode :logic.  That happens to be correct for
; exit-boot-strap-mode, but is wrong for enter-boot-strap-mode, which today is
; being executed with default-defun-mode :program.  But it is irrelevant
; because neither of those two commands are sensitive to the
; default-defun-mode.

  (global-set 'command-landmark
              (make-command-tuple
               (next-absolute-command-number wrld)
               defun-mode
               form
               cbd
               last-make-event-expansion)
              (update-world-index 'command wrld)))

(defun find-longest-common-retraction1 (wrld1 wrld2)
  (cond ((equal wrld1 wrld2) wrld1)
        (t (find-longest-common-retraction1
            (scan-to-command (cdr wrld1))
            (scan-to-command (cdr wrld2))))))

(defun find-longest-common-retraction1-event (wrld1 wrld2)
  (cond ((equal wrld1 wrld2) wrld1)
        (t (find-longest-common-retraction1-event
            (scan-to-event (cdr wrld1))
            (scan-to-event (cdr wrld2))))))

(defun find-longest-common-retraction (event-p wrld1 wrld2)

; Wrld1 and wrld2 are two worlds.  We find and return a wrld3 that
; concludes with a command-landmark such that both wrld1 and wrld2 are
; extensions of wrld3.  Of course, nil would do, but we find the
; longest.

  (cond
   (event-p
    (let* ((n (min (max-absolute-event-number wrld1)
                   (max-absolute-event-number wrld2))))
      (find-longest-common-retraction1-event
       (scan-to-landmark-number 'event-landmark n wrld1)
       (scan-to-landmark-number 'event-landmark n wrld2))))
   (t
    (let* ((n (min (max-absolute-command-number wrld1)
                   (max-absolute-command-number wrld2))))
      (find-longest-common-retraction1
       (scan-to-landmark-number 'command-landmark n wrld1)
       (scan-to-landmark-number 'command-landmark n wrld2))))))

(defun install-global-enabled-structure (wrld state)
  (cond
   ((null wrld) ; see initial call of set-w in enter-boot-strap-mode
    state)
   ((active-useless-runes state) ; then we already updated
    state)
   (t
    (let* ((augmented-theory (global-val 'current-theory-augmented wrld))
           (ens (f-get-global 'global-enabled-structure state))
           (theory-array (access enabled-structure ens :theory-array))
           (current-theory-index (global-val 'current-theory-index wrld))
           (eq-theories (equal augmented-theory (cdr theory-array))))
      (cond ((and eq-theories
                  (eql current-theory-index
                       (access enabled-structure ens :index-of-last-enabling)))
             state)
            ((and eq-theories
                  (< current-theory-index
                     (car (dimensions (access enabled-structure ens
                                              :array-name)
                                      theory-array))))
             (f-put-global 'global-enabled-structure
                           (change enabled-structure ens
                                   :index-of-last-enabling
                                   current-theory-index)
                           state))
            (t
             (mv-let (erp new-ens state)
                     (load-theory-into-enabled-structure
                      :no-check augmented-theory t
                      ens nil current-theory-index wrld
                      'irrelevant-ctx state)
                     (assert$ (null erp)
                              (f-put-global 'global-enabled-structure
                                            new-ens
                                            state)))))))))

#-acl2-loop-only
(defvar *defattach-fns*) ; see the Essay on Memoization with Attachments

#+acl2-loop-only
(partial-encapsulate
; See discussion in the #-acl2-loop-only definition of retract-stobj-tables.
 (((retract-stobj-tables * state) => state))
 () ; supporters
 (local (defun retract-stobj-tables (wrld state)
          (declare (xargs :stobjs state)
                   (ignore wrld))
          state)))

#-acl2-loop-only
(defun retract-stobj-tables (wrld state)

; This function logically covers the issue of stale stobjs in stobj-tables,
; i.e., those keys (stobj names) that no longer name the stobj that was present
; when the entry was inserted into the stobj-table, because of undoing the
; stobj.  (Note that although the stobj might or might not exist again later,
; there is no guarantee that the new stobj is congruent to the old one.)  We
; make an undone stobj name an inaccessible key by removing it from
; *current-stobj-gensym-ht* in undo-trip, as a consequence of having pushed a
; remhash form for *current-stobj-gensym-ht* onto the '*undo-stack* of the
; stobj name.  Retract-stobj-tables provides the logical explanation for this
; removal.  The call (retract-stobj-tables wrld state) is intended to remove
; all entries from stobj-tables that will become stale when we retract the
; current ACL2 world back to wrld (assuming wrld is indeed a retraction of (w
; state)).  The function is left undefined in the logic by the
; partial-encapsulate that introduces it (in #+acl2-loop-only code).

; Aside.  If some day we really want a legitimate version of
; retract-stobj-tables, we could surely walk through (user-stobj-alist state)
; looking recursively (through stobj fields) for stobj-tables.  That code
; wouldn't respect single-threadedness restrictions but it would only be for
; logical modeling anyhow; it could thus be introduced with defun-nx.

  (declare (ignore wrld))
  state)

(defun set-w (flg wrld state)

; Ctx is ignored unless we are extending the current ACL2 world, in which case
; if ctx is not nil, there will be a check on the new theory from a call of
; maybe-warn-about-theory.

; This is the only way in ACL2 (as opposed to raw Common Lisp) to
; install wrld as the current-acl2-world.  Flg must be either
; 'extension or 'retraction.  Logically speaking, all this function
; does is set the state global value of 'current-acl2-world in state
; to be wrld and possibly set current-package to "ACL2".  Practically,
; speaking however, it installs wrld on the symbol-plists in Common
; Lisp.  However, wrld must be an extension or retraction, as
; indicated, of the currently installed ACL2 world.

; Statement of Policy regarding Erroneous Events and
; Current ACL2 World Installation:

; Any event which causes an error must leave the current-acl2-world of
; state unchanged.  That is, if you extend the world in an event, you
; must revert on error back to the original world.  Once upon a time
; we enforced this rule in LD, simply by reverting the world on every
; erroneous command.  But then we made that behavior conditional on
; the LD special ld-error-triples.  If ld-error-triples is nil, then
; (mv t nil state) is not treated as an error by LD.  Hence, an
; erroneous DEFUN, say, evaluated with ld-error-triples nil, does not
; cause LD to revert.  Therefore, DEFUN must manage the reversion
; itself.

  #-acl2-loop-only
  (declare (ftype (function (t t) (values t))
                  invalidate-some-cl-cache-lines))

  #+acl2-loop-only
  (declare (xargs :guard
                  (and (or (eq flg 'extension)
                           (eq flg 'retraction))
                       (plist-worldp wrld)
                       (known-package-alistp
                        (getpropc 'known-package-alist 'global-value nil wrld))
                       (symbol-alistp
                        (getpropc 'acl2-defaults-table 'table-alist nil wrld))
                       (state-p state))))

  #+acl2-loop-only
  (pprogn
   (cond ((eq flg 'retraction)
          (retract-stobj-tables wrld state))
         (t state))
   (f-put-global 'current-acl2-world wrld state)
   (install-global-enabled-structure wrld state)
   (cond ((find-non-hidden-package-entry (current-package state)
                                         (known-package-alist state))
          state)
         (t (f-put-global 'current-package "ACL2" state))))
  #-acl2-loop-only
  (cond ((live-state-p state)
         (setf (car *fncall-cache*) nil)
         (ev-fncall-w-guard1-cache-clear)
         (cond ((and *wormholep*
                     (not (eq wrld (w *the-live-state*))))
                (push-wormhole-undo-formi 'cloaked-set-w! (w *the-live-state*)
                                          nil)))
         (and (not (f-get-global 'boot-strap-flg *the-live-state*))
              (invalidate-some-cl-cache-lines
               flg
               wrld))
         (let ((*defattach-fns* nil))
           (cond ((eq flg 'extension)
                  (extend-world1 'current-acl2-world wrld)
                  state)
                 (t
                  (retract-world1 'current-acl2-world wrld)
                  state))))
        (t (f-put-global 'current-acl2-world wrld state)
           (install-global-enabled-structure wrld state)
           (cond ((find-non-hidden-package-entry (current-package state)
                                                 (known-package-alist state))
                  state)
                 (t (f-put-global 'current-package "ACL2" state))))))

(defun set-w! (wrld state)

; This function makes wrld the current-acl2-world, but doesn't require
; that wrld be either an 'extension or a 'retraction of the current
; one.  Note that any two worlds, wrld1 and wrld2, can be related by a
; retraction followed by an extension: retract wrld1 back to the first
; point at which it is a tail of wrld2, and then extend that world to
; wrld2.  That is what we do.

  (let ((w (w state)))
    (cond ((equal wrld w)
           state)
          (t
           (pprogn (set-w 'retraction
                          (find-longest-common-retraction

; It is important to use events rather than commands here when certifying or
; including a book.  Otherwise, when make-event expansion extends the world, we
; will have to revert back to the beginning of the most recent top-level
; command and install the world from there.  With a large number of such
; make-event forms, such quadratic behavior could be unfortunate.  And, the
; community book books/make-event/stobj-test.lisp illustrates that if after
; make-event expansion we revert to the beginning of the book being certified,
; we could lose the setting of a stobj in that expansion.

; But really, there seems no point in using command landmarks here (as we
; always did until adding this use of event landmarks in Version_3.1).  After
; all, why back up all the way to a command landmark?  (With a different scheme
; we can imagine a reason; we'll get to that at the end of this long comment.)
; Moreover, if installation of an event were to consult the installed world, it
; would be important that all previous events have already been installed.  For
; example, in the hons version of v3-6-1, the following example caused a hard
; error, as shown and explained below.

; (defun foo (x)
;   (declare (xargs :guard t))
;   (cons x x))
;
; (progn
;   (defun foo-cond (x)
;     (declare (ignore x)
;              (xargs :guard 't))
;     nil)
;   (memoize 'foo :condition-fn 'foo-cond)
;   (progn
;     (deflabel some-label)
;     (defthm non-thm (equal x y))))

; HARD ACL2 ERROR in SCAN-TO-LANDMARK-NUMBER:  We have scanned the world
; looking for absolute event number 6463 and failed to find it....

; How could this have happened?  First note that the cltl-command for memoize
; invoked function cltl-def-from-name, which was looking in the installed world
; for the definition of foo-cond.  But the world containing that 'cltl-command
; had not yet been installed in the state, because extend-world1 only installs
; the world after processing all the new trips.  So when the defthm failed, its
; revert-world-on-error first retracted the world all the way back to just
; after the command for foo (not to just after the deflabel).  The above error
; occurred because the attempt to fetch the cltl definition of foo-cond was
; passed the installed world: the world just after the introduction of foo.
; Now we don't get that error: instead we only roll back to the event landmark
; for the deflabel, and then we back out gracefully.  Actually, we have also
; changed the implementation of memoize to avoid looking in the installed world
; for the cltl definition.  But we still like using event landmarks, which can
; result in a lot less processing of world triples since we are not backing up
; all the way to a command landmark.

; Finally we address the "different scheme" promised above for the use of
; command landmarks.  In a chat with Sol Swords we came to realize that it would
; likely be more efficient to pop all the way back to the last command, and not
; extend that command world at all.  (Recall that each command is protected by
; ld-read-eval-print.)  For example, with the failure of non-thm above, its
; revert-world-on-error puts us at just after the deflabel; then the
; revert-world-on-error for the inner progn puts us at just after the memoize;
; and finally, the revert-world-on-error of the outer progn puts us just after
; the command introducing foo.  Why not just revert directly to that final
; world?  We could, but the current scheme has stood the test of time as being
; robust and efficient, albeit using command landmarks instead of event
; landmarks (and the latter should help performance rather than hurt it).  But
; here is a more compelling reason not to try such a scheme.  At the time a
; form fails, it is hard to know whether the error really cannot be tolerated
; and should pop us out to the start of the command.  Consider for example
; something like:

;    (progn
;      (defun h1 (x) x)
;      (make-event (mv-let (erp val state)
;                          (defthm my-bad (equal t nil))
;                          (declare (ignore erp val))
;                          (value '(value-triple nil))))
;      (defun h2 (x) (h1 x)))

; This event succeeds, and we want that to continue to be the case.  It is hard
; to see how that could work if we were left in the world before h1 when the
; make-event failed.

; Old code, using event landmarks (rather than command landmarks) only in the
; indicated situations:

;                          (or (f-get-global 'certify-book-info state)
;                              (global-val 'include-book-path w))

                           t ; always use event landmarks (see comments above)
                           wrld
                           w)
                          state)
                   (set-w 'extension
                          wrld
                          state))))))

(defmacro save-event-state-globals (form)

; Form should evaluate to an error triple.

  `(state-global-let*
    ((accumulated-ttree nil)
     (gag-state nil)
     (print-base 10 set-print-base)
     (print-radix nil set-print-radix)
     (proof-tree-ctx nil)
     (saved-output-p

; We set saved-output-p in prove, which allows io-record structures to start
; accumulating into state global 'saved-output-reversed; see
; saved-output-token-p and its use in guarding saved-output-token-p in the
; definition of io?.  See also analogous treatment in pc-prove.

      nil))
    (with-prover-step-limit! :START ,form)))

(defconst *protected-system-state-globals*
  (let ((val
         (set-difference-eq
          (union-eq (strip-cars *initial-ld-special-bindings*)
                    (strip-cars *initial-global-table*))
          '(acl2-raw-mode-p ;;; keep raw mode status
            bddnotes        ;;; for feedback after expansion failure

; We handle world and enabled structure installation ourselves, with set-w! and
; revert-world-on-error.  We do not want to rely just on state globals because
; the world protection/modification functions do pretty fancy things.

            current-acl2-world global-enabled-structure
            acl2-world-alist           ;;; manage this ourselves, e.g., for pso
            inhibit-output-lst         ;;; allow user to modify this in a book
            inhibited-summary-types    ;;; allow user to modify this in a book
            keep-tmp-files             ;;; allow user to modify this in a book
            make-event-debug           ;;; allow user to modify this in a book
            saved-output-token-lst     ;;; allow user to modify this in a book
            print-clause-ids           ;;; allow user to modify this in a book
            fmt-soft-right-margin      ;;; allow user to modify this in a book
            fmt-hard-right-margin      ;;; allow user to modify this in a book
            compiler-enabled           ;;; allow user to modify this in a book
            port-file-enabled          ;;; allow user to modify this in a book
            parallel-execution-enabled ;;; allow user to modify this in a book
            waterfall-parallelism      ;;; allow user to modify this in a book
            waterfall-parallelism-timing-threshold ;;; see just above
            waterfall-printing ;;; allow user to modify this in a book
            waterfall-printing-when-finished ;;; see just above
            saved-output-reversed ;;; for feedback after expansion failure
            saved-output-p        ;;; for feedback after expansion failure
            ttags-allowed         ;;; propagate changes outside expansion
            ld-evisc-tuple        ;;; see just above
            term-evisc-tuple      ;;; see just above
            abbrev-evisc-tuple    ;;; see just above
            gag-mode-evisc-tuple  ;;; see just above
            slow-apply$-action    ;;; see just above
            slow-array-action     ;;; see just above
            iprint-ar             ;;; see just above
            iprint-fal            ;;; see just above
            iprint-soft-bound     ;;; see just above
            iprint-hard-bound     ;;; see just above
            trace-co              ;;; see just above
            trace-specs           ;;; see just above
            show-custom-keyword-hint-expansion
            timer-alist                ;;; preserve accumulated summary info
            main-timer                 ;;; preserve accumulated summary info
            verbose-theory-warning     ;;; warn if disabling a *bbody-alist* key
            pc-ss-alist                ;;; for saves under :instructions hints
            last-step-limit            ;;; propagate step-limit past expansion
            illegal-to-certify-message ;;; needs to persist past expansion
            splitter-output            ;;; allow user to modify this in a book
            serialize-character        ;;; allow user to modify this in a book
            serialize-character-system ;;; ditto; useful during certification
            top-level-errorp           ;;; allow TOP-LEVEL errors to propagate

; Do not remove deferred-ttag-notes or deferred-ttag-notes-saved from this
; list!  Consider the following example.

;   (make-event (er-progn (set-deferred-ttag-notes t state)
;                         (defttag t1)
;                         (defttag t2)
;                         (value '(value-triple :done))))

; When deferred-ttag-notes and deferred-ttag-notes-saved were not in this list
; (through Version_7.1), we never saw a TTAG NOTE for :T2.

            deferred-ttag-notes       ;;; see comment immediately above
            deferred-ttag-notes-saved ;;; see comment immediately above

            certify-book-info         ;;; need effect from with-useless-runes

; The following two are protected a different way; see
; protect-system-state-globals.

            writes-okp
            cert-data
            ))))
    val))

(defun state-global-bindings (names)
  (cond ((endp names)
         nil)
        (t (cons `(,(car names) (f-get-global ',(car names) state))
                 (state-global-bindings (cdr names))))))

(defmacro protect-system-state-globals (form)

; Form must return an error triple.  This macro not only reverts built-in state
; globals after evaluating form, but it also disables the opening of output
; channels.

  `(state-global-let*
    ((writes-okp nil)
     (cert-data nil) ; avoid using global cert-data; see make-event-fn
     ,@(state-global-bindings *protected-system-state-globals*))
    ,form))

(defun formal-value-triple (erp val)

; Keep in sync with formal-value-triple@par.

; Returns a form that evaluates to the error triple (mv erp val state).

  (fcons-term* 'cons erp
               (fcons-term* 'cons val
                            (fcons-term* 'cons 'state *nil*))))

#+acl2-par
(defun formal-value-triple@par (erp val)

; Keep in sync with formal-value-triple.

  (fcons-term* 'cons erp
               (fcons-term* 'cons val *nil*)))

(defun@par translate-simple-or-error-triple (uform ctx wrld state)

; First suppose either #-acl2-par or else #+acl2-par with waterfall-parallelism
; disabled.  Uform is an untranslated term that is expected to translate either
; to an error triple or to an ordinary value.  In those cases we return an
; error triple whose value component is the translated term or, respectively,
; the term representing (mv nil tterm state) where tterm is the translated
; term.  Otherwise, we return a soft error.

; Now consider the case of #+acl2-par with waterfall-parallelism enabled.
; Uform is an untranslated term that is expected to translate to an ordinary
; value.  In this case, we return an error pair (mv nil val) where val is the
; translated term.  Otherwise, uform translates into an error pair (mv t nil).

  (mv-let@par
   (erp term bindings state)
   (translate1@par uform
                   :stobjs-out ; form must be executable
                   '((:stobjs-out . :stobjs-out))
                   '(state) ctx wrld state)
   (cond
    (erp (mv@par t nil state))
    (t
     (let ((stobjs-out (translate-deref :stobjs-out bindings)))
       (cond
        ((equal stobjs-out '(nil)) ; replace term by (value@par term)
         (value@par (formal-value-triple@par *nil* term)))
        ((equal stobjs-out *error-triple-sig*)
         (serial-first-form-parallel-second-form@par
          (value@par term)

; #+ACL2-PAR note: This message is used to check that computed hints and custom
; keyword hints (and perhaps other hint mechanisms too) do not modify state.
; Note that not all hint mechanisms rely upon this check.  For example,
; apply-override-hint@par and eval-clause-processor@par perform their own
; checks.

; Parallelism wart: it should be possible to return (value@par term) when
; waterfall-parallelism-hacks-enabled is non-nil.  This would allow more types
; of hints to fire when waterfall-parallelism-hacks are enabled.

          (er@par soft ctx
            "Since we are translating a form in ACL2(p) intended to be ~
             executed with waterfall parallelism enabled, the form ~x0 was ~
             expected to represent an ordinary value, not an error triple (mv ~
             erp val state), as would be acceptable in a serial execution of ~
             ACL2.  Therefore, the form returning a tuple of the form ~x1 is ~
             an error.  See :DOC unsupported-waterfall-parallelism-features ~
             and :DOC error-triples-and-parallelism for further explanation."
            uform
            (prettyify-stobj-flags stobjs-out))))
        #+acl2-par
        ((serial-first-form-parallel-second-form@par
          nil
          (and

; The test of this branch is never true in the non-@par version of the
; waterfall.  We need this test for custom-keyword-hints, which are evaluated
; using the function eval-and-translate-hint-expression[@par].  Since
; eval-and-translate-hint-expression[@par] calls
; translate-simple-or-error-triple[@par] to check the return signature of the
; custom hint, we must not cause an error when we encounter this legitimate
; use.

; Parallelism wart: consider eliminating the special case below, given the spec
; for translate-simple-or-error-triple[@par] in the comment at the top of this
; function.  This could be achieved by doing the test below before calling
; translate-simple-or-error-triple@par, either inline where we now call
; translate-simple-or-error-triple@par or else with a wrapper that handles this
; special case before calling translate-simple-or-error-triple@par.

           (equal stobjs-out *cmp-sig*)
           (eq (car uform) 'custom-keyword-hint-interpreter@par)))
         (value@par term))
        (t (serial-first-form-parallel-second-form@par
            (er soft ctx
                "The form ~x0 was expected to represent an ordinary value or ~
                 an error triple (mv erp val state), but it returns a tuple ~
                 of the form ~x1."
                uform
                (prettyify-stobj-flags stobjs-out))
            (er@par soft ctx
              "The form ~x0 was expected to represent an ordinary value, but ~
               it returns a tuple of the form ~x1.  Note that error triples ~
               are not allowed in this feature in ACL2(p) (see :doc ~
               error-triples-and-parallelism)"
              uform
              (prettyify-stobj-flags stobjs-out))))))))))

(defun xtrans-eval (uterm alist trans-flg ev-flg ctx state aok)

; NOTE: Do not call this function with er-let* if ev-flg is nil.  Use mv-let
; and check erp manually.  See the discussion of 'wait below.

; Ignore trans-flg and ev-flg for the moment (or imagine their values are t).
; Then the spec of this function is as follows:

; Uterm is an untranslated term with an output signature of * or (mv * *
; state).  We translate it and eval it under alist (after extending alist with
; state bound to the current state) and return the resulting error triple or
; signal a translate or evaluation error.

; We restore the world and certain state globals
; (*protected-system-state-globals*) after the evaluation, by using
; protect-system-state-globals below.  Be sure not to change that protection
; without considering the consequences; in particular, make-event expansion
; relies on this restoration (via protected-eval, which calls
; protect-system-state-globals), as do proof-builder macro commands.  Without
; that protection we expect that unsoundness or bad errors could arise during
; book certification.

; If trans-flg is nil, we do not translate.  We *assume* uterm is a
; single-threaded translated term with output signature (mv * * state)!

; Ev-flg is either t or nil.  If ev-flg is nil, we are to evaluate uterm only
; if all of its free vars are bound in the evaluation environment.  If ev-flg
; is nil and we find that a free variable of uterm is not bound, we return a
; special error triple, namely (mv t 'wait state) indicating that the caller
; should wait until it can get all the vars bound.  On the other hand, if
; ev-flg is t, it means eval the translated uterm, which will signal an error
; if there is an unbound var.

; Note that we do not evaluate in safe-mode.  Perhaps we should.  However, we
; experimented by timing certification for community books directory
; books/hints/ without and with safe-mode, and found times of 13.5 and 16.4
; user seconds, respectively.  That's not a huge penalty for safe-mode but it's
; not small, either, so out of concern for scalability we will avoid safe-mode
; for now.

  (er-let* ((term
             (if trans-flg
                 (translate-simple-or-error-triple uterm ctx (w state) state)
               (value uterm))))
    (cond
     ((or ev-flg
          (subsetp-eq (all-vars term)
                      (cons 'state (strip-cars alist))))

; We are to ev the term. But first we protect ourselves by arranging
; to revert the world and restore certain state globals.

      (let ((original-world (w state)))
        (er-let*
          ((val
            (acl2-unwind-protect
             "xtrans-eval"
             (protect-system-state-globals
              (mv-let (erp val latches)
                      (ev term
                          (cons (cons 'state
                                      (coerce-state-to-object state))
                                alist)
                          state
                          (list (cons 'state
                                      (coerce-state-to-object state)))
                          nil
                          aok)
                      (let ((state (coerce-object-to-state
                                    (cdr (car latches)))))
                        (cond
                         (erp

; An evaluation error occurred.  This could happen if we encountered
; an undefined (but constrained) function.  We print the error
; message.

                          (er soft ctx "~@0" val))
                         (t

; Val is the list version of (mv erp' val' state) -- and it really is
; state in that list (typically, the live state).  We assume that if
; erp' is non-nil then the evaluation also printed the error message.
; We return an error triple.

                          (mv (car val)
                              (cadr val)
                              state))))))
             (set-w! original-world state)
             (set-w! original-world state))))
          (value val))))
     (t

; In this case, ev-flg is nil and there are variables in tterm that are
; not bound in the environment.  So we tell our caller to wait to ev the
; term.

      (mv t 'wait state)))))

#+acl2-par
(defun xtrans-eval-with-ev-w (uterm alist trans-flg ev-flg ctx state aok)

; See xtrans-eval documentation.

; This function was originally introduced in support of the #+acl2-par version.
; We could have named it "xtrans-eval@par".  However, this function seems
; worthy of having its own name, suggestive of what it is: a version of
; xtrans-eval that uses ev-w for evaluation rather than using ev.  The extra
; function call adds only trivial cost.

  (er-let*@par
   ((term
     (if trans-flg

; #+ACL2-PAR note: As of August 2011, there are two places that call
; xtrans-eval@par with the trans-flg set to nil: apply-override-hint@par and
; eval-and-translate-hint-expression@par.  In both of these cases, we performed
; a manual inspection of the code (aided by testing) to determine that if state
; can be modified by executing uterm, that the user will receive an error
; before even reaching this call of xtrans-eval@par.  In this way, we guarantee
; that the invariant for ev-w (that uterm does not modify state) is maintained.

         (translate-simple-or-error-triple@par uterm ctx (w state) state)
       (value@par uterm))))
   (cond
    ((or ev-flg
         (subsetp-eq (all-vars term)
                     (cons 'state (strip-cars alist))))

; #+ACL2-PAR note: we currently discard any changes to the world of the live
; state.  But if we restrict to terms that don't modify state, as discussed in
; the #+ACL2-PAR note above, then there is no issue because state hasn't
; changed.  Otherwise, if we cheat, the world could indeed change out from
; under us, which is just one example of the evils of cheating by modifying
; state under the hood.

     (er-let*-cmp
      ((val
        (mv-let (erp val)
                (ev-w term
                      (cons (cons 'state
                                  (coerce-state-to-object state))
                            alist)
                      (w state)
                      (user-stobj-alist state)
                      (f-get-global 'safe-mode state)
                      (gc-off state)
                      nil
                      aok)
                (cond
                 (erp

; An evaluation error occurred.  This could happen if we encountered
; an undefined (but constrained) function.  We print the error
; message.

                  (er@par soft ctx "~@0" val))
                 (t

; Val is the list version of (mv erp' val' state) -- and it really is
; state in that list (typically, the live state).  We assume that if
; erp' is non-nil then the evaluation also printed the error message.
; We return an error triple.

                  (mv (car val)
                      (cadr val)))))))
      (value@par val)))
    (t

; In this case, ev-flg is nil and there are variables in tterm that are
; not bound in the environment.  So we tell our caller to wait to ev the
; term.

     (mv t 'wait)))))

#+acl2-par
(defun xtrans-eval@par (uterm alist trans-flg ev-flg ctx state aok)
  (xtrans-eval-with-ev-w uterm alist trans-flg ev-flg ctx state aok))

(defmacro xtrans-eval-state-fn-attachment (form ctx)

; We call xtrans-eval on (pprogn (fn state) (value nil)), unless we are in the
; boot-strap or fn is unattached, in which cases we return (value nil).

; Note that arguments trans-flg and aok are t in our call of xtrans-eval.

  (declare (xargs :guard (and (true-listp form)
                              (symbolp (car form)))))
  `(let ((form ',form)
         (fn ',(car form))
         (ctx ,ctx))
     (cond ((or (f-get-global 'boot-strap-flg state)
                (null (attachment-pair fn (w state))))
            (value nil))
           (t (let ((form (list 'pprogn
                                (append form '(state))
                                '(value nil))))
                (mv-let (erp val state)
                        (xtrans-eval form
                                     nil ; alist
                                     t   ; trans-flg
                                     t   ; ev-flg
                                     ctx
                                     state
                                     t ; aok
                                     )
                        (cond (erp (er soft ctx
                                       "The error above occurred during ~
                                        evaluation of ~x0."
                                       form))
                              (t (value val)))))))))

(defmacro with-ctx-summarized (ctx body &key event-type)

; A typical use of this macro by an event creating function is:

; (with-ctx-summarized (cons 'defun name)
;   (er-progn ...
;             (er-let* (... (v form) ...)
;             (install-event ...))))

; Note that with-ctx-summarized binds the variables ctx and saved-wrld, which
; thus can be used in body.

; If body changes the installed world then the new world must end with an
; event-landmark (we cause an error otherwise).  The segment of the new world
; back to the previous event-landmark is scanned for redefined names and an
; appropriate warning message is printed, as per ld-redefinition-action.

; The most obvious way to satisfy this restriction on world is for each
; branch through body to (a) stop with stop-redundant-event, (b) signal an
; error, or (c) conclude with install-event.  Two of our current uses of this
; macro do not follow so simple a paradigm.  In include-book-fn we add many
; events (in process-embedded-events) but we do conclude with an install-event
; which couldn't possibly redefine any names because no names are defined in
; the segment from the last embedded event to the landmark for the include-book
; itself.  In certify-book-fn we conclude with an include-book-fn.  So in both
; of those cases the scan for redefined names ends quickly (without going into
; the names possibly redefined in the embedded events) and finds nothing to
; report.

; This macro initializes the timers for an event and then executes the supplied
; body, which should return an error triple.  Whether an error is signaled or
; not, the macro prints the summary and then pass the error triple on up.  The
; stats must be available from the state.  In particular, we print redefinition
; warnings that are recovered from the currently installed world in state and
; we print the runes from 'accumulated-ttree.

  `(let ((ctx (or (f-get-global 'global-ctx state)
                  ,ctx))
         (saved-wrld (w state)))
     (pprogn (initialize-summary-accumulators state)
             (mv-let
              (erp val state)
              (save-event-state-globals
               (mv-let (erp val state)
                       (er-progn
                        (xtrans-eval-state-fn-attachment
                         (initialize-event-user ',ctx ',body)
                         ctx)
                        ,body)
                       (pprogn
                        (print-summary erp
                                       (equal saved-wrld (w state))
                                       ,event-type
                                       ctx state)
                        (er-progn
                         (xtrans-eval-state-fn-attachment
                          (finalize-event-user ',ctx ',body)
                          ctx)
                         (mv erp val state)))))

; In the case of a compound event such as encapsulate, we avoid saving io?
; forms for proof replay that were generated after a failed proof attempt,
; since the user probably won't want to see them.  If we make a change here,
; consider carefully whether replay from an encapsulate with a failed defthm
; will pop warnings more often than pushing them (resulting in an error from
; pop-warning-frame); could the pushes be only from io? forms saved inside the
; defthm, even though pops are saved from the enclosing encapsulate?

              (pprogn (f-put-global 'saved-output-p nil state)
                      (mv erp val state))))))

(defmacro revert-world-on-error (form)

; With this macro we can write (revert-world-on-error &) and if &
; causes an error the world will appear unchanged (because we revert
; back to the world of the initial state).  The local variable used to
; save the old world is a long ugly name only because we prohibit its
; use in ,form.  (Historical Note: Before the introduction of
; acl2-unwind-protect we had to use raw lisp to handle this and the
; handling of that special variable was very subtle.  Now it is just
; an ordinary local of the let.)

  `(let ((revert-world-on-error-temp (w state)))
     (acl2-unwind-protect
      "revert-world-on-error"
      (check-vars-not-free (revert-world-on-error-temp) ,form)
      (set-w! revert-world-on-error-temp state)
      state)))

(defun@par chk-theory-expr-value1 (lst wrld expr macro-aliases ctx state)

; A theory expression must evaluate to a common theory, i.e., a truelist of
; rule name designators.  A rule name designator, recall, is something we can
; interpret as a set of runes and includes runes themselves and the base
; symbols of runes, such as APP and ASSOC-OF-APP.  We already have a predicate
; for this concept: theoryp.  This checker checks for theoryp but with better
; error reporting.

; Generally speaking, if a member of lst is not a rule name designator, then
; some theory function (set-difference-theories, etc.) will have reported it,
; using check-theory, before we get here.

  (cond ((atom lst)
         (cond ((null lst)
                (value@par nil))
               (t (er@par soft ctx
                    "The value of the alleged theory expression ~x0 is not a ~
                     true list and, hence, is not a legal theory value.  In ~
                     particular, the final non-consp cdr is the atom ~x1.  ~
                     See :DOC theories."
                    expr lst))))
        ((rule-name-designatorp (car lst) macro-aliases wrld)
         (chk-theory-expr-value1@par (cdr lst) wrld expr macro-aliases ctx
                                     state))
        (t (er@par soft ctx
             "The value of the alleged theory expression ~x0 includes the ~
              element ~x1, which we do not know how to interpret as a rule ~
              name.  See :DOC theories and :DOC rune."
             expr (car lst)))))

(defun@par chk-theory-expr-value (lst wrld expr ctx state)

; This checker ensures that expr, whose value is lst, evaluated to a theoryp.
; Starting after Version_3.0.1 we no longer check the theory-invariant table,
; because the ens is not yet available at this point.

  (chk-theory-expr-value1@par lst wrld expr (macro-aliases wrld) ctx state))

(defun theory-fn-translated-callp (x)

; We return t or nil.  If t, then we know that the term x evaluates to a runic
; theory.  See also theory-fn-callp.

  (and (nvariablep x)
       (not (fquotep x))
       (member-eq (car x)
                  '(current-theory-fn
                    e/d-fn
                    executable-counterpart-theory-fn
                    function-theory-fn
                    intersection-theories-fn
                    set-difference-theories-fn
                    set-difference-current-theory-fn
                    theory-fn
                    union-theories-fn
                    union-current-theory-fn
                    universal-theory-fn))
       t))

(defun eval-theory-expr (expr ctx wrld state)

; returns a runic theory

; Keep in sync with eval-theory-expr@par.

  (cond ((equal expr '(current-theory :here))
         (mv-let (erp val latches)
                 (ev '(current-theory-fn ':here world)
                     (list (cons 'world wrld))
                     state nil nil t)
                 (declare (ignore latches))
                 (mv erp val state)))
        (t (er-let*
            ((trans-ans
              (state-global-let*
               ((guard-checking-on t) ; see the Essay on Guard Checking
;               ;;; (safe-mode t) ; !! long-standing "experimental" deletion
                )
               (simple-translate-and-eval
                expr
                (list (cons 'world wrld))
                nil
                "A theory expression" ctx wrld state t))))

; Trans-ans is (term . val).

            (cond ((theory-fn-translated-callp (car trans-ans))
                   (value (cdr trans-ans)))
                  (t
                   (er-progn
                    (chk-theory-expr-value (cdr trans-ans) wrld expr ctx state)
                    (value (runic-theory (cdr trans-ans) wrld)))))))))

#+acl2-par
(defun eval-theory-expr@par (expr ctx wrld state)

; returns a runic theory

; Keep in sync with eval-theory-expr.

  (cond ((equal expr '(current-theory :here))
         (mv-let (erp val)
                 (ev-w '(current-theory-fn ':here world)
                       (list (cons 'world wrld))
                       (w state)
                       (user-stobj-alist state)
                       (f-get-global 'safe-mode state)
                       (gc-off state)
                       nil t)
                 (mv erp val)))
        (t (er-let*@par
            ((trans-ans
              (simple-translate-and-eval@par
               expr
               (list (cons 'world wrld))
               nil
               "A theory expression" ctx wrld state t

; The following arguments are intended to match the safe-mode and gc-off values
; from the state in eval-theory-expr at the call there of
; simple-translate-and-eval.  Since there is a superior state-global-let*
; binding guard-checking-on to t, we bind our gc-off argument below to what
; would be the value of (gc-off state) in that function, which is nil.

               (f-get-global 'safe-mode state)
               nil)))

; Trans-ans is (term . val).

            (cond ((theory-fn-translated-callp (car trans-ans))
                   (value@par (cdr trans-ans)))
                  (t
                   (er-progn@par
                    (chk-theory-expr-value@par (cdr trans-ans) wrld expr ctx state)
                    (value@par (runic-theory (cdr trans-ans) wrld)))))))))

(defun append-strip-cars (x y)

; This is (append (strip-cars x) y).

  (cond ((null x) y)
        (t (cons (car (car x)) (append-strip-cars (cdr x) y)))))

(defun append-strip-cdrs (x y)

; This is (append (strip-cdrs x) y).

  (cond ((null x) y)
        (t (cons (cdr (car x)) (append-strip-cdrs (cdr x) y)))))

(defun no-rune-based-on (runes symbols)
  (cond ((null runes) t)
        ((member-eq (base-symbol (car runes)) symbols)
         nil)
        (t (no-rune-based-on (cdr runes) symbols))))

(defun revappend-delete-runes-based-on-symbols1 (runes symbols ans)

; We delete from runes all those with base-symbols listed in symbols
; and accumulate them in reverse order onto ans.

  (cond ((null runes) ans)
        ((member-eq (base-symbol (car runes)) symbols)
         (revappend-delete-runes-based-on-symbols1 (cdr runes) symbols ans))
        (t (revappend-delete-runes-based-on-symbols1 (cdr runes)
                                                     symbols
                                                     (cons (car runes) ans)))))

(defun revappend-delete-runes-based-on-symbols (runes symbols ans)

; In computing the useful theories we will make use of previously stored values
; of those theories.  However, those stored values might contain "runes" that
; are no longer runes because of redefinition.  The following function is used
; to delete from those non-runes, based on the redefined base symbols.

; This function returns the result of appending the reverse of ans to the
; result of removing runes based on symbols from the given list of runes.  It
; should return a runic theory.

  (cond ((or (null symbols) (no-rune-based-on runes symbols))

; This case is not only a time optimization, but it also allows sharing.  For
; example, runes could be the 'current-theory, and in this case we will just be
; extending that theory.

         (revappend ans runes))
        (t (reverse
            (revappend-delete-runes-based-on-symbols1 runes symbols ans)))))

(defun current-theory1 (lst ans redefined)

; Warning: Keep this in sync with current-theory1-augmented.

; Lst is a cdr of wrld.  We wish to return the enabled theory as of the time
; lst was wrld.  When in-theory is executed it stores the newly enabled theory
; under the 'global-value of the variable 'current-theory.  When new rule names
; are introduced, they are automatically considered enabled.  Thus, the enabled
; theory at any point is the union of the current value of 'current-theory and
; the names introduced since that value was set.  However, :REDEF complicates
; matters.  See universal-theory-fn1.

  (cond ((null lst)
         #+acl2-metering (meter-maid 'current-theory1 500)
         (reverse ans)) ; unexpected, but correct
        ((eq (cadr (car lst)) 'runic-mapping-pairs)
         #+acl2-metering (setq meter-maid-cnt (1+ meter-maid-cnt))
         (cond
          ((eq (cddr (car lst)) *acl2-property-unbound*)
           (current-theory1 (cdr lst) ans
                            (add-to-set-eq (car (car lst)) redefined)))
          ((member-eq (car (car lst)) redefined)
           (current-theory1 (cdr lst) ans redefined))
          (t
           (current-theory1 (cdr lst)
                            (append-strip-cdrs (cddr (car lst)) ans)
                            redefined))))
        ((and (eq (car (car lst)) 'current-theory)
              (eq (cadr (car lst)) 'global-value))

; We append the reverse of our accumulated ans to the appropriate standard
; theory, but deleting all the redefined runes.

         #+acl2-metering (meter-maid 'current-theory1 500)
         (revappend-delete-runes-based-on-symbols (cddr (car lst))
                                                  redefined ans))
        (t
         #+acl2-metering (setq meter-maid-cnt (1+ meter-maid-cnt))
         (current-theory1 (cdr lst) ans redefined))))

(defun first-n-ac-rev (i l ac)

; This is the same as first-n-ac, except that it reverses the accumulated
; result and traffics in fixnums -- more efficient if you want the reversed
; result.

  (declare (type (unsigned-byte 29) i)
           (xargs :guard (and (true-listp l)
                              (true-listp ac))))
  (cond ((zpf i)
         ac)
        (t (first-n-ac-rev (the (unsigned-byte 29)
                                (1- (the (unsigned-byte 29) i)))
                           (cdr l)
                           (cons (car l) ac)))))

(defun longest-common-tail-length-rec (old new len-old acc)
  (declare (type (signed-byte 30) acc len-old))
  #-acl2-loop-only
  (when (eq old new)
    (return-from longest-common-tail-length-rec (+ len-old acc)))
  (cond ((endp old)
         (assert$ (null new)
                  acc))
        (t (longest-common-tail-length-rec (cdr old)
                                           (cdr new)
                                           (1-f len-old)
                                           (if (equal (car old) (car new))
                                               (1+f acc)
                                             0)))))

(defun longest-common-tail-length (old new len-old)

; We separate out this wrapper function so that we don't need to be concerned
; about missing the #-acl2-loop-only case in the recursive computation, which
; could perhaps happen if we are in safe-mode and oneification prevents escape
; into Common Lisp.

  (longest-common-tail-length-rec old new len-old 0))

(defun extend-current-theory (old-th len-old new-th len-new old-aug-th wrld)

; Logically this function just returns new-th.  However, the copy of new-th
; that is returned shares a maximal tail with old-th.  A second value similarly
; extends old-aug-th, under the assumption that old-aug-th is the
; augmented-theory corresponding to old-th; except, if old-aug-th is :none then
; the second value is undefined.

  (let* ((len-common
          (cond ((int= len-old len-new)
                 (longest-common-tail-length old-th new-th len-old))
                ((< len-old len-new)
                 (longest-common-tail-length
                  old-th
                  (nthcdr (- len-new len-old) new-th)
                  len-old))
                (t
                 (longest-common-tail-length
                  (nthcdr (- len-old len-new) old-th)
                  new-th
                  len-new))))
         (take-new (- len-new len-common))
         (nthcdr-old (- len-old len-common))
         (old-th-tail (nthcdr nthcdr-old old-th))
         #-acl2-loop-only
         (return-new-p (eq (nthcdr take-new new-th)
                           old-th-tail))
         (new-part-of-new-rev
          (cond #-acl2-loop-only
                ((and return-new-p (eq old-aug-th :none))
                 'irrelevant)
                (t
                 (first-n-ac-rev (the-unsigned-byte! 29 take-new
                                                     'extend-current-theory)
                                 new-th
                                 nil)))))
    (mv (cond #-acl2-loop-only
              (return-new-p new-th)
              (t (revappend new-part-of-new-rev old-th-tail)))
        (if (eq old-aug-th :none)
            :none
          (augment-runic-theory1 new-part-of-new-rev nil wrld
                                 (nthcdr nthcdr-old old-aug-th))))))

(defun update-current-theory (theory0 theory0-length wrld)
  (mv-let (theory theory-augmented)
          (extend-current-theory

; It's not necessarily reasonable to assume that theory0 shares a lot of
; structure with the most recent value of 'current-theory.  But it could
; happen, so we take the opportunity to save space.  Consider the not uncommon
; case that theory0 is the value of (current-theory :here).  Theory0 may be eq
; to the value of 'current-theory, in which case this extend-current-theory
; call below will be cheap because it will just do a single eq test.  However,
; theory0 could be a copy of the most recent 'current-theory that doesn't share
; much structure with it, in which case it's a good thing that we are here
; calling extend-current-theory.

           (global-val 'current-theory wrld)
           (global-val 'current-theory-length wrld)
           theory0
           theory0-length
           (global-val 'current-theory-augmented wrld)
           wrld)
          (global-set
           'current-theory theory
           (global-set
            'current-theory-augmented theory-augmented
            (global-set
             'current-theory-index (1- (get-next-nume wrld))
             (global-set 'current-theory-length theory0-length
                         wrld))))))

(defun put-cltl-command (cltl-cmd wrld wrld0)

; We extend wrld by noting cltl-cmd.  Wrld0 is supplied because it may more
; efficient for property lookup than wrld; it is critical therefore that wrld0
; and wrld have the same values of 'include-book-path,
; 'top-level-cltl-command-stack, and 'boot-strap-flg.

  (let ((wrld (if (or (global-val 'include-book-path wrld0)
                      (global-val 'boot-strap-flg wrld0))
                  wrld
                (global-set 'top-level-cltl-command-stack
                            (cons cltl-cmd
                                  (global-val 'top-level-cltl-command-stack
                                              wrld0))
                            wrld))))
    (global-set 'cltl-command cltl-cmd wrld)))

(defun strip-non-nil-base-symbols (runes acc)
  (cond ((endp runes) acc)
        (t (strip-non-nil-base-symbols
            (cdr runes)
            (let ((b (base-symbol (car runes))))
              (cond ((null b) acc)
                    (t (cons b acc))))))))

(defun install-proof-supporters (namex ttree wrld)

; This function returns an extension of wrld in which the world global
; 'proof-supporters-alist is extended by associating namex, when a symbol or
; list of symbols, with the list of names of events used in an admissibility
; proof.  This list is sorted (by symbol<) and is based on event names
; recorded in ttree, including runes as well as events from hints of type :use,
; :by, or :clause-processor.  However, if the list of events is empty, then we
; do not extend wrld.  See :DOC dead-events.

  (mv-let (use-names0 by-names0 cl-proc-fns0)
    (cl-proc-data-in-ttree ttree t)
    (let* ((runes (all-runes-in-ttree ttree nil))
           (use-lst (use-names-in-ttree ttree t))
           (by-lst (by-names-in-ttree ttree t))
           (names (append by-names0 by-lst
                          cl-proc-fns0
                          use-names0 use-lst
                          (strip-non-nil-base-symbols runes nil)))
           (sorted-names (and names ; optimization
                              (sort-symbol-listp
                               (cond ((symbolp namex)
                                      (cond ((member-eq namex names)

; For example, the :induction rune for namex, or a :use (or maybe even :by)
; hint specifying namex, can be used in the guard proof.

                                             (remove-eq namex names))
                                            (t names)))
                                     ((intersectp-eq namex names)
                                      (set-difference-eq names namex))
                                     (t names))))))
      (cond ((and (not (eql namex 0))
                  sorted-names)
             (global-set 'proof-supporters-alist
                         (acons namex
                                sorted-names
                                (global-val 'proof-supporters-alist wrld))
                         wrld))
            (t wrld)))))

(defmacro update-w (condition new-w &optional retract-p)

; WARNING: This function installs a world, so it may be necessary to call it
; only in the (dynamic) context of revert-world-on-error.  For example, its
; calls during definitional processing are all under the call of
; revert-world-on-error in defuns-fn.

  (let ((form `(pprogn ,(if retract-p
                            '(set-w 'retraction wrld state)
                          '(set-w 'extension wrld state))
                       (value wrld))))

; We handle condition t separately, to avoid a compiler warning (at least in
; Allegro CL) that the final COND branch (t (value wrld)) is unreachable.

    (cond
     ((eq condition t)
      `(let ((wrld ,new-w)) ,form))
     (t
      `(let ((wrld ,new-w))
         (cond
          (,condition ,form)
          (t (value wrld))))))))

(defun skip-proofs-due-to-system (state)

; This utility returns true when we are skipping proofs because the system
; insists on that, but not because of any user action that is taken to skip
; proofs.  Normally we can just check state global 'skip-proofs-by-system.
; However, without the first disjunct below, we fail to pick up a skip-proofs
; during the Pcertify step of provisional certification.

  (and (not (f-get-global 'inside-skip-proofs state))
       (f-get-global 'skip-proofs-by-system state)))

(defun install-event (val form ev-type namex ttree cltl-cmd
                          chk-theory-inv-p ctx wrld state)

; This function is the way to finish off an ACL2 event.  Val is the value to be
; returned by the event (in the standard error flag/val/state three-valued
; result).  Namex is either 0, standing for the empty set of names, an atom,
; standing for the singleton set of names containing that atom, or a true list
; of symbols, standing for the set of names in the list.  Each symbol among
; these names will be given an 'absolute-event-number property.  In addition,
; we set 'event-landmark 'global-value to an appropriate event tuple, thus
; marking the world for this event.  Cltl-cmd is the desired value of the
; 'global-value for 'cltl-command (see below).  Chk-theory-inv-p is generally
; nil, but is non-nil if we are to check theory invariants, and is :PROTECT if
; the call is not already in the scope of a revert-world-on-error.  Wrld is the
; world produced by the ACL2 event and state is the current state, and before
; extending it as indicated above, we extend it if necessary by an appropriate
; record of the proof obligations discharged in support of functional
; instantiation, in order to avoid such proofs in later events.

; Ttree is the final ttree of the event.  We install it as 'accumulated-ttree
; so that the runes reported in the summary are guaranteed to be those of the
; carefully tracked ttree passed along through the proof.  It is possible that
; the 'accumulated-ttree already in state contains junk, e.g., perhaps we
; accumulated some runes from a branch of the proof we have since abandoned.
; We try to avoid this mistake, but just to be sure that a successful proof
; reports the runes that we really believe got used, we do it this way.

; We store the 'absolute-event-number property for each name.  We set
; 'event-landmark.  We store the cltl-cmd as the value of the variable
; 'cltl-command (if cltl-cmd is non-nil).  We update the event index.  We
; install the new world as the current ACL2 world in state.  Non-logical code
; in set-w notes the 'cltl-command requests in the world and executes
; appropriate raw Common Lisp for effect.  This function returns the triple
; indicating a non-erroneous return of val.

; The installation of the world into state causes "secret" side-effects on the
; underlying lisp state, as controlled by 'cltl-command.  Generally, the value
; is a raw lisp form to execute, e.g., (defconst name val).  But when the car
; of the form is DEFUNS the general form is (DEFUNS defun-mode-flg ignorep def1
; ...  defn).  The raw lisp form to execute is actually (DEFUNS def1'
; ... defn'), where the defi' are computed from the defi depending on
; defun-mode-flg and ignorep.  Defun-Mode-flg is either nil (meaning the
; function is :non-executable or the parent event is an encapsulate which is
; trying to define the executable-counterparts of the constrained functions) or
; a defun-mode (meaning the parent event is an executable DEFUNS and the
; defun-mode is the defun-mode of the defined functions).  Ignorep is
; 'reclassifying, '(defstobj . stobj-name), or nil.  If ignorep is nil, we add
; each def and its *1* counterpart, after pushing the old bodies on the undo
; stack.  If ignorep is 'reclassifying (which means we are reclassifying a
; :program fn to a :logic fn without changing its definition -- which is
; probably hand coded ACL2 source), we define only the *1* counterparts after
; pushing only the *1* counterparts on the undo stack.  If ignorep is
; '(defstobj . stobj-name) we do not add the def or its *1* counterpart, but we
; do push both the main name and the *1* name.  This is because we know
; defstobj will supply a symbol-function for the main name and its *1*
; counterpart in a moment.  We use the stobj-name in the *1* body to compute
; the stobjs-in of the function.  See the comment in add-trip.

; One might ask why we make add-trip do the oneify to produce the *1* bodies,
; instead of compute them when we generate the CLTL-COMMAND.  The reason is
; that we use the 'cltl-command of a DEFUN as the only place we can recover the
; exact ACL2 defun command that got executed.  (Exception: in the case that the
; :defun-mode is nil, i.e., the definition is non-executable, we have replaced
; the body with a throw-raw-ev-fncall.)

  (let ((currently-installed-wrld (w state)))
    (mv-let
     (chk-theory-inv-p theory-invariant-table)
     (cond ((member-eq (ld-skip-proofsp state)
                       '(include-book include-book-with-locals))
            (mv nil nil))
           (t (let ((tbl (table-alist 'theory-invariant-table
                                      currently-installed-wrld)))
                (cond ((null tbl) ; avoid work of checking theory invariant
                       (mv nil nil))
                      (t (mv chk-theory-inv-p tbl))))))
     (let* ((new-proved-fnl-insts
             (proved-functional-instances-from-tagged-objects
              (cond ((atom namex)

; We deliberately include the case namex = 0 here.

                     namex)
                    (t (car namex)))
              (revappend (strip-cars (tagged-objects :use ttree))
                         (reverse ; for backwards compatibility with v4-2
                          (tagged-objects :by ttree)))))
            (wrld0 (if (or (ld-skip-proofsp state)
                           (and (atom namex) (not (symbolp namex))))
                       wrld
                     (install-proof-supporters namex ttree wrld)))
            (wrld1a (if (and (f-get-global 'in-local-flg state)
                             (f-get-global 'certify-book-info state)
                             (not ; not inside include-book
                              (global-val 'include-book-path wrld))
                             (not (global-val 'cert-replay wrld)))
                        (global-set 'cert-replay t wrld0)
                      wrld0))
            (wrld1 (if new-proved-fnl-insts
                       (global-set
                        'proved-functional-instances-alist
                        (append new-proved-fnl-insts
                                (global-val 'proved-functional-instances-alist
                                            wrld1a))
                        wrld1a)
                     wrld1a))

; We set world global 'skip-proofs-seen or 'redef-seen if ld-skip-proofsp or
; ld-redefinition-action (respectively) is non-nil and the world global is not
; already true.  This information is important for vetting a proposed
; certification world.  See the Essay on Soundness Threats.  We also make a
; note in the event-tuple when skipping proofs (by the user, not merely the
; system as for include-book), since that information could be useful to those
; who want to know what remains to be proved.

            (skipped-proofs-p
             (and (ld-skip-proofsp state)
                  (not (member-eq ev-type

; Comment on irrelevance of skip-proofs:

; The following event types do not generate any proof obligations that can be
; skipped, so for these, there is no point in storing whether proofs have been
; skipped (either in the event tuple or in skip-proofs-seen).  Do not include
; defaxiom, or any other event that can have a :corollary rule class, since
; that can generate a proof obligation.  Also do not include encapsulate; even
; though it takes responsibility for setting skip-proofs-seen based on its
; first pass, nevertheless it does not account for a skip-proofs surrounding
; the encapsulate.  Finally, do not include defattach; the use of (skip-proofs
; (defattach f g)) can generate bogus data in world global
; 'proved-functional-instances-alist that can be used to prove nil later.

                                  '(include-book
                                    defchoose
                                    defconst
                                    deflabel
                                    defmacro
                                    defpkg
                                    defstobj
                                    deftheory
                                    in-arithmetic-theory
                                    in-theory
                                    push-untouchable
                                    regenerate-tau-database
                                    remove-untouchable
                                    reset-prehistory
                                    set-body
                                    table)))
                  (not (skip-proofs-due-to-system state))))
            (wrld2 (cond
                    ((and skipped-proofs-p
                          (let ((old (global-val 'skip-proofs-seen wrld)))
                            (or (not old)

; In certify-book-fn we find a comment stating that "we are trying to record
; whether there was a skip-proofs form in the present book, not merely on
; behalf of an included book".  That is why here, we replace value
; (:include-book ...) for 'skip-proofs-seen.

                                (eq (car old) :include-book))))
                     (global-set 'skip-proofs-seen form wrld1))
                    (t wrld1)))
            (wrld3 (cond
                    ((and (ld-redefinition-action state)

; We tolerate redefinition inside a book, because there must have been a trust
; tag that allowed it.  We are only trying to protect against redefinition
; without a trust tag, especially in the certification world.  (Without a trust
; tag there cannot be any redefinition in a certified book anyhow.)

                          (not (global-val 'include-book-path wrld))
                          (not (global-val 'redef-seen wrld)))
                     (global-set 'redef-seen form wrld2))
                    (t wrld2)))
            (wrld4 (if cltl-cmd
                       (put-cltl-command cltl-cmd wrld3
                                         currently-installed-wrld)
                       wrld3)))
       (er-let*
         ((wrld4a (update-w t wrld4)) ; for ev-xxx calls under tau-visit-event
          (wrld5 (tau-visit-event t ev-type namex
                                  (tau-auto-modep wrld4a)
                                  (ens state)
                                  ctx wrld4a state)))

; WARNING: Do not put down any properties here!  The cltl-command should be the
; last property laid down before the call of add-event-landmark.  We rely on
; this invariant when looking for 'redefined tuples in
; compile-uncompiled-defuns and compile-uncompiled-*1*-defuns.

         (let ((wrld6 (add-event-landmark form ev-type namex wrld5
                                          (f-get-global 'boot-strap-flg
                                                        state)
                                          skipped-proofs-p)))
           (pprogn
            (f-put-global 'accumulated-ttree ttree state)
            (cond
             ((eq chk-theory-inv-p :protect)
              (revert-world-on-error
               (let ((state (set-w 'extension wrld6 state)))
                 (er-progn
                  (chk-theory-invariant1 :install
                                         (ens state)
                                         theory-invariant-table
                                         nil ctx state)
                  (value val)))))
             (t (let ((state (set-w 'extension wrld6 state)))
                  (cond (chk-theory-inv-p
                         (er-progn
                          (chk-theory-invariant1 :install
                                                 (ens state)
                                                 theory-invariant-table
                                                 nil ctx state)
                          (value val)))
                        (t (value val)))))))))))))

(defun stop-redundant-event-fn1 (chan ctx extra-msg state)
  (mv-let (col state)
    (fmt "The event " nil chan state nil)
    (mv-let (col state)
      (fmt-ctx ctx col chan state)
      (mv-let (col state)
        (fmt1 " is redundant.  See :DOC redundant-events.~#0~[~/  ~@1~]~%"
              (list (cons #\0 (if (null extra-msg) 0 1))
                    (cons #\1 extra-msg))
              col chan state nil)
        (declare (ignore col))
        state))))

(defun stop-redundant-event-fn (ctx state extra-msg)

; Through Version_8.3 we printed an "is redundant" message as event output (in
; the sense of io?)  only.  But when we reduced output from defstub, we still
; wanted that message even though we were inhibiting event output.  We
; considered simply switching to summary output, but we want the user to see
; "is redundant" when summary output is inhibited but event output is not; the
; "is redundant" output is appropriate both as event-level and summary-level
; explanations, though it should only be printed once.  Our solution is to
; print it as event output if event output is not inhibited, and otherwise as
; summary output unless 'redundant is among the inhibited summary types.

  (let ((chan (proofs-co state))
        (ctx (or (f-get-global 'global-ctx state)
                 ctx)))
    (pprogn
     (cond ((ld-skip-proofsp state) state)
           ((not (member-eq 'event
                            (f-get-global 'inhibit-output-lst state)))
            (io? event nil state
                 (chan ctx extra-msg)
                 (stop-redundant-event-fn1 chan ctx extra-msg state)))
           ((member-eq 'redundant
                       (f-get-global 'inhibited-summary-types state))
            state)
           (t (io? summary nil state
                   (chan ctx extra-msg)
                   (stop-redundant-event-fn1 chan ctx extra-msg state))))
     (value :redundant))))

(defmacro stop-redundant-event (ctx state &optional extra-msg)
  `(stop-redundant-event-fn ,ctx ,state ,extra-msg))

; Examining the World

; The user must be given facilities for poking around the world.  To describe
; where in the world he wishes to look, we provide "landmark descriptors."
; A landmark descriptor, lmd, identifies a given landmark in the world.
; It does this by "decoding" to either (COMMAND-LANDMARK . n) or
; (EVENT-LANDMARK . n), where n is an absolute command or event number, as
; appropriate.  Then, using lookup-world-index, one can obtain the
; relevant world.  The language of lmds is designed to let the user
; poke conveniently given the way we have chosen to display worlds.
; Below is a typical display:

; d    1 (DEFUN APP (X Y) ...)
; d    2 (DEFUN REV (X) ...)
;      3 (ENCAPSULATE (((HD *) => *)) ...)
; D       (DEFTHM HD-CONS ...)
; D       (DEFTHM HD-ATOM ...)
;      4 (IN-THEORY #)

; Observe firstly that the commands are always displayed in chronological
; order.

; Observe secondly that user commands are numbered consecutively.  We
; adopt the policy that the commands are numbered from 1 starting with
; the first command after the boot-strap.  Negative integers number
; the commands in "pre-history."  These command numbers are not our
; absolute command numbers.  Indeed, until we have completed the
; boot-strapping we don't know what "relative" command number to
; assign to the chronologically first command in the boot-strap.  We
; therefore internally maintain only absolute command numbers and just
; artificially offset them by a certain baseline when we display them
; to the user.

(defrec command-number-baseline-info
  (current permanent-p . original)
  nil)

(defun absolute-to-relative-command-number (n wrld)
  (- n (access command-number-baseline-info
               (global-val 'command-number-baseline-info wrld)
               :current)))

(defun relative-to-absolute-command-number (n wrld)
  (+ n (access command-number-baseline-info
               (global-val 'command-number-baseline-info wrld)
               :current)))

(defun normalize-absolute-command-number (n wrld)

; We have arranged that the first value of this function is a flag, which is
; set iff n exceeds the maximum absolute command number in the current world.
; Our intention is to prevent expressions like
; :ubt (:here +1)
; from executing.

  (let ((m (max-absolute-command-number wrld)))
    (cond ((> n m) (mv t m))
          ((< n 0) (mv nil 0))
          (t (mv nil n)))))

; Observe thirdly that events that are not commands are unnumbered.
; They must be referred to by logical name.

; Command Descriptors (CD)

; The basic facilities for poking around the world will operate at the
; command level.  We will define a class of objects called "command
; descriptors" which denote command landmarks in the current world.
; We will provide a function for displaying an event and its command
; block, but that will come later.

; The legal command descriptors and their meaning are shown below.  N
; is an integer, name is a logical name, and cd is a command descriptor.

; :min   -- the chronologically first command of the boot

; :start -- 0 at startup, but always refers to (exit-boot-strap-mode), even
;           after a reset-prehistory command

; :max   -- the most recently executed command -- synonymous with :x

; n      -- the nth command landmark, as enumerated by relative command
;           numbers

; name   -- the command containing the event that introduced name

; (cd n) -- the command n removed from the one described by cd

; (:search pat cd1 cd2) -- search the interval from cd1 to cd2 for the first
;           command whose form (or one of whose event forms) matches pat.
;           By "match" we mean "contains all of the elements listed".
;           We search FROM cd1 TO cd2, which will search backwards
;           if cd2 > cd1.  The special case (:search pat) means
;           (:search pat :max 1).

; The search cd is implemented as follows:

(defun tree-occur (x y)

; Does x occur in the cons tree y?

  (cond ((equal x y) t)
        ((atom y) nil)
        (t (or (tree-occur x (car y))
               (tree-occur x (cdr y))))))

(defun cd-form-matchp (pat form)

; We determine whether the form matches pat.  We support only a
; rudimentary notion of matching right now: pat is a true list of
; objects and each must occur in form.

  (cond ((symbolp form) ;eviscerated
         nil)
        ((null pat) t)
        ((tree-occur (car pat) form)
         (cd-form-matchp (cdr pat) form))
        (t nil)))

(defun cd-some-event-matchp (pat wrld)

; This is an odd function.  At first, it was as simple predicate that
; determined whether some event form in the current command block
; matched pat.  It returned t or nil.  But then we changed it so that
; if it fails it returns the world as of the next command block.  So
; if it returns t, it succeeded; non-t means failure and tells where
; to start looking next.

  (cond ((null wrld) nil)
        ((and (eq (caar wrld) 'command-landmark)
              (eq (cadar wrld) 'global-value))
         wrld)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value)
              (cd-form-matchp pat (access-event-tuple-form (cddar wrld))))
         t)
        (t (cd-some-event-matchp pat (cdr wrld)))))

(defun cd-search (pat earliestp start-wrld end-wrld)

; Start-wrld is a world containing end-wrld as a predecessor.  Both
; worlds start on a command landmark.  Pat is a true list of objects.
; Earliestp it t or nil initially, but in general is either nil, t, or
; the last successfully matched world seen.

; We search from start-wrld through end-wrld looking for a command
; world that matches pat in the sense that either the command form
; itself or one of the event forms in the command block contains all
; the elements of pat.  If earliestp is non-nil we return the
; chronologically earliest matching command world.  If earliestp is
; nil we return the chronologically latest matching command world.

  (cond ((equal start-wrld end-wrld)
         (cond
          ((or (cd-form-matchp pat
                               (access-command-tuple-form (cddar start-wrld)))
               (eq t (cd-some-event-matchp pat (cdr start-wrld))))
           start-wrld)
          ((eq earliestp t) nil)
          (t earliestp)))
        ((cd-form-matchp pat
                         (access-command-tuple-form (cddar start-wrld)))
         (cond
          (earliestp
           (cd-search pat
                      start-wrld
                      (scan-to-command (cdr start-wrld))
                      end-wrld))
          (t start-wrld)))
        (t (let ((wrld1 (cd-some-event-matchp pat (cdr start-wrld))))
             (cond ((eq wrld1 t)
                    (cond (earliestp
                           (cd-search pat
                                      start-wrld
                                      (scan-to-command (cdr start-wrld))
                                      end-wrld))
                          (t start-wrld)))
                   (t (cd-search pat earliestp wrld1 end-wrld)))))))

(defun superior-command-world (wrld1 wrld ctx state)

; Given a world, wrld1, and the current ACL2 world, we return the
; world as of the command that gave rise to wrld1.  We do this by
; scanning down wrld1 for the command landmark that occurred
; chronologically before it, increment the absolute command number
; found there by 1, and look that world up in the index.  If no such
; world exists then this function has been called in a peculiar way,
; such as (progn (defun fn1 nil 1) (pc 'fn1)) at the top-level.
; Observe that when pc is called, there is not yet a command superior
; to the event fn1.  Hence, when we scan down wrld1 (which starts at
; the event for fn1) we'll find the previous command number, and
; increment it to obtain a number that is too big.  When this happens,
; we cause a soft error.

  (let ((prev-cmd-wrld (scan-to-command wrld1)))
    (cond
     ((<= (1+ (access-command-tuple-number (cddar prev-cmd-wrld)))
          (max-absolute-command-number wrld))
      (value
       (lookup-world-index 'command
                           (if prev-cmd-wrld
                               (1+ (access-command-tuple-number
                                    (cddar prev-cmd-wrld)))
                               0)
                           wrld)))
     (t (er soft ctx
            "We have been asked to find the about-to-be-most-recent ~
             command landmark.  We cannot do that because that ~
             landmark hasn't been laid down yet!")))))

(defun er-decode-cd (cd wrld ctx state)
  (let ((msg "The object ~x0 is not a legal command descriptor.  See ~
              :DOC command-descriptor."))
    (cond
     ((or (symbolp cd)
          (stringp cd))
      (cond
       ((or (eq cd :max)
            (eq cd :x))
        (value (scan-to-command wrld)))
       ((eq cd :min) (value (lookup-world-index 'command 0 wrld)))
       ((eq cd :start)
        (value (lookup-world-index
                'command
                (access command-number-baseline-info
                        (global-val 'command-number-baseline-info wrld)
                        :original)
                wrld)))
       ((and (keywordp cd)
             (let ((str (symbol-name cd)))
               (and (eql (char str 0) #\X)
                    (eql (char str 1) #\-)
                    (mv-let (k pos)
                            (parse-natural nil str 2 (length str))
                            (and k
                                 (= pos (length str)))))))

; This little piece of code parses :x-123 into (:max -123).

        (er-decode-cd (list :max
                            (- (mv-let
                                (k pos)
                                (parse-natural nil (symbol-name cd) 2
                                               (length (symbol-name cd)))
                                (declare (ignore pos))
                                k)))
                      wrld ctx state))
       (t (er-let* ((ev-wrld (er-decode-logical-name cd wrld ctx state)))
                   (superior-command-world ev-wrld wrld ctx state)))))
     ((integerp cd)
      (mv-let (flg n)
              (normalize-absolute-command-number
               (relative-to-absolute-command-number cd wrld)
               wrld)
              (cond (flg (er soft ctx
                             "The object ~x0 is not a legal command descriptor ~
                              because it exceeds the current maximum command ~
                              number, ~x1."
                             cd
                             (absolute-to-relative-command-number n wrld)))
                    (t (value
                        (lookup-world-index 'command n wrld))))))
     ((and (consp cd)
           (true-listp cd))
      (case
       (car cd)
       (:SEARCH
        (cond
         ((and (or (= (length cd) 4)
                   (= (length cd) 2))
               (or (atom (cadr cd))
                   (true-listp (cadr cd))))
          (let* ((pat (if (atom (cadr cd))
                          (list (cadr cd))
                          (cadr cd))))
            (er-let* ((wrld1 (er-decode-cd (cond ((null (cddr cd)) :max)
                                                 (t (caddr cd)))
                                           wrld ctx state))
                      (wrld2 (er-decode-cd (cond ((null (cddr cd)) 0)
                                                 (t (cadddr cd)))
                                           wrld ctx state)))
                     (let ((ans
                            (cond
                             ((>= (access-command-tuple-number (cddar wrld1))
                                  (access-command-tuple-number (cddar wrld2)))
                              (cd-search pat nil wrld1 wrld2))
                             (t
                              (cd-search pat t wrld2 wrld1)))))
                       (cond
                        ((null ans)
                         (er soft ctx
                             "No command or event in the region from ~x0 to ~
                              ~x1 contains ~&2.  See :DOC command-descriptor."
                             (cond ((null (cddr cd)) :x)
                                   (t (caddr cd)))
                             (cond ((null (cddr cd)) 0)
                                   (t (cadddr cd)))
                             pat
                             cd))
                        (t (value ans)))))))
         (t (er soft ctx msg cd))))
       (otherwise
        (cond
         ((and (consp (cdr cd))
               (integerp (cadr cd))
               (null (cddr cd)))
          (er-let* ((wrld1 (er-decode-cd (car cd) wrld ctx state)))
                   (mv-let (flg n)
                           (normalize-absolute-command-number
                            (+ (access-command-tuple-number
                                (cddar wrld1))
                               (cadr cd))
                            wrld)
                           (cond (flg (er soft ctx
                                          "The object ~x0 is not a legal ~
                                           command descriptor because it ~
                                           represents command number ~x1,  ~
                                           which exceeds the current maximum ~
                                           command number, ~x2."
                                          cd
                                          (absolute-to-relative-command-number
                                           (+ (access-command-tuple-number
                                               (cddar wrld1))
                                              (cadr cd))
                                           wrld)
                                          (absolute-to-relative-command-number
                                           n
                                           wrld)))
                                 (t (value (lookup-world-index 'command
                                                               n
                                                               wrld)))))))
         (t (er soft ctx msg cd))))))
     (t (er soft ctx msg cd)))))

; Displaying Events and Commands

; When we display an event we will also show the "context" in which
; it occurs, by showing the command block.  The rationale is that
; the user cannot undo back to any random event -- he must always
; undo an entire command block -- and thus our convention serves to
; remind him of what will fall should he undo the displayed event.
; Similarly, when we display a command we will sketch the events in
; its block, to remind him of all the effects of that command.

; The commands in the display will be numbered sequentially.  Command
; 1 will be the first command typed by the user after bootstrap.  Negative
; command numbers refer to prehistoric commands.

; Commands will be displayed in chronological order.  This means we
; must print them in the reverse of the order in which we encounter
; them in the world.  Actually, it is not exactly the reverse, because
; we wish to print commands, encapsulates, and include-books before
; their events, but they are stored on the world after their events.

; Because some events include others it is possible for the user to
; accidentally ask us to print out large blocks, even though the
; interval specified, e.g., commands 1 through 3, is small.  This
; means that a tail recursive implementation is desirable.  (We could
; print in reverse order by printing on the way out of the recursion.)

; Because of all these complications, we have adopted a two pass
; approach to printing out segments of the world.  Both passes are
; tail recursive.  During the first, we collect a list of "landmark
; display directives" (ldd's) and during the second we interpret those
; directives to display the landmarks.  Roughly speaking, each ldd
; corresponds to one line of the display.

; Note to Software Archaeologists of the Future:

; As you study this code, you may wonder why the authors are so
; persistent in inventing long, pompous sounding names, e.g.,
; "landmark display directives" or "prove spec var" and then
; shortening them to unpronounceable letter sequences, e.g., "ldd" and
; "pspv".  This certainly goes against the grain of some software
; scientists who rail against unpronounceable names, acronyms, and
; unnecessary terminology in general.  For the record, we are not
; unsympathetic to their pleas.  However, by adopting these
; conventions we make it easy to use Emacs to find out where these
; objects are documented and manipulated.  Until this code was added
; to the system, the character string "ldd" did not occur in it.  Big
; surprise!  Had we used some perfectly reasonable English word, e.g.,
; "line" (as we might have had we described this code in isolation
; from all other) there would be many false matches.  Of course, we
; could adopt an ordinary word, e.g., "item" that just happened not to
; occur in our sources.  But unfortunately this suffers not only from
; giving a very technical meaning to an ordinary word, but offers no
; protection against the accidental use of the word later in a
; confusing way.  Better, we thought, to come up with the damn
; acronyms which one pretty much has to know about to use.

; In addition to telling us the form to print, an ldd must tell us the
; form to print, whether it is a command or an event, the command
; number, whether it is to be printed in full or only sketched,
; whether it is to be marked, whether it is fully, partially, or not
; disabled, and how far to indent it.

(defrec ldd-status
  (defun-mode-pair disabled memoized)
  nil) ; could change to t after awhile; this new record was created April 2011

(defun make-ldd-flags (class markp status fullp)

; Class is 'COMMAND or 'EVENT, markp is t or nil indicating whether we are to
; print the ">" beside the line, status is a record containing characters that
; indicate the defun-mode and disabled and memoize status, and fullp is t or
; nil indicating whether we are to print the form in full or just sketch it.
; Once upon a time this fn didn't do any consing because there were only a
; small number of combinations and they were all built in.  But with the
; introduction of colors (which became defun-modes) that strategy lost its
; allure.

 (cons (cons class markp) (cons status fullp)))

(defun make-ldd (class markp status n fullp form)

; Class is 'command or 'event.
; Markp is t or nil, indicating whether we are to print a ">".
; Status is a an ldd-status record indicating defun-mode, disabled status, and
;   memoized status.
; n is a natural number whose interpretation depends on class:
;   if class is 'command, n is the command number; otherwise,
;   n is how far we are to indent, where 1 means indent one
;   space in from the command column.
; fullp is t or nil, indicating whether we are to print the form
;   in full or only sketch it.
; form is the form to print.

  (cons (make-ldd-flags class markp status fullp)
        (cons n form)))

(defun access-ldd-class  (ldd) (caaar ldd))
(defun access-ldd-markp  (ldd) (cdaar ldd))
(defun access-ldd-status (ldd) (cadar ldd))
(defun access-ldd-fullp  (ldd) (cddar ldd))
(defun access-ldd-n      (ldd) (cadr ldd))
(defun access-ldd-form   (ldd) (cddr ldd))

(defun big-d-little-d-name1 (lst ens ans)

; Lst is a list of runic-mapping-pairs.  The car of each pair is a nume.  We
; are considering the enabled status of the runes (numes) in lst.  If all
; members of the list are enabled, we return #\E.  If all are disabled, we
; return #\D.  If some are enabled and some are disabled, we return #\d.  Ans
; is #\E or #\D signifying that we have seen some runes so far and they are all
; enabled or disabled as indicated.

  (cond ((null lst) ans)
        ((equal ans (if (enabled-numep (caar lst) ens) #\E #\D))
         (big-d-little-d-name1 (cdr lst) ens ans))
        (t #\d)))

(defun big-d-little-d-name (name ens wrld)

; Name is a symbol.  If it is the basic symbol of some nonempty set of runes,
; then we return either #\D, #\d, or #\E, depending on whether all, some, or
; none of the runes based on name are disabled.  If name is not the basic
; symbol of any rune, we return #\Space.

  (let ((temp (getpropc name 'runic-mapping-pairs nil wrld)))
    (cond ((null temp) #\Space)
          (t (big-d-little-d-name1 (cdr temp) ens
                                   (if (enabled-numep (caar temp) ens)
                                       #\E
                                       #\D))))))

(defun big-d-little-d-clique1 (names ens wrld ans)

; Same drill, one level higher.  Names is a clique of function symbols.  Ans is
; #\E or #\D indicating that all the previously seen names in the clique
; are enabled or disabled as appropriate.  We return #\E, #\D or #\d.

  (cond ((null names) ans)
        (t (let ((ans1 (big-d-little-d-name (car names) ens wrld)))
             (cond ((eql ans1 #\d) #\d)
                   ((eql ans1 ans)
                    (big-d-little-d-clique1 (cdr names) ens wrld ans))
                   (t #\d))))))

(defun big-d-little-d-clique (names ens wrld)

; Names is a list of function symbols.  As such, each symbol in it is the basic
; symbol of a set of runes.  If all of the runes are enabled, we return
; #\E, if all are disabled, we return #\D, and otherwise we return #\d.  We
; assume names is non-nil.

  (let ((ans (big-d-little-d-name (car names) ens wrld)))
    (cond ((eql ans #\d) #\d)
          (t (big-d-little-d-clique1 (cdr names) ens wrld ans)))))

(defun big-d-little-d-event (ev-tuple ens wrld)

; This function determines the enabled/disabled status of an event.  Ev-Tuple
; is an event tuple.  Wrld is the current ACL2 world.

; We return #\D, #\d, #\E or #\Space, with the following interpretation:
; #\D - at least one rule was added by this event and all rules added
;       are currently disabled;
; #\d - at least one rule was added by this event and at least one rule added
;       is currently disabled and at least one rule added is currently enabled.
; #\E - at least one rule was added by this event and all rules added
;       are currently enabled.
; #\Space - no rules were added by this event.

; Note that we do not usually print #\E and we mash it together with #\Space to
; mean all rules added, if any, are enabled.  But we need the stronger
; condition to implement our handling of blocks of events.

  (let ((namex (access-event-tuple-namex ev-tuple)))
    (case (access-event-tuple-type ev-tuple)
          ((defun defthm defaxiom)
           (big-d-little-d-name namex ens wrld))
          (defuns (big-d-little-d-clique namex ens wrld))
          (defstobj (big-d-little-d-clique (cddr namex) ens wrld))
          (otherwise #\Space))))

(defun big-d-little-d-command-block (wrld1 ens wrld s)

; Same drill, one level higher.  We scan down wrld1 to the next command
; landmark inspecting each of the event landmarks in the current command block.
; (Therefore, initially wrld1 ought to be just past the command landmark for
; the block in question.)  We determine whether this command ought to have a
; #\D, #\E, #\d, or #\Space printed beside it, by collecting that information for
; each event in the block.  Wrld is the current ACL2 world and is used to
; obtain both the current global enabled structure and the numes of the runes
; involved.

; The interpretation of the character is as described in big-d-little-d-event.

; We sweep through the events accumulating our final answer in s, which we
; think of as a "state" (but not STATE).  The interpretation of s is:
; #\D - we have seen at least one event with status #\D and all the
;       events we've seen have status #\D or status #\Space.
; #\E - we have seen at least one event with status #\E and all the
;       events we've seen have status #\E or status #\Space
; #\Space - all events seen so far (if any) have status #\Space

  (cond ((or (null wrld1)
             (and (eq (caar wrld1) 'command-landmark)
                  (eq (cadar wrld1) 'global-value)))
         s)
        ((and (eq (caar wrld1) 'event-landmark)
              (eq (cadar wrld1) 'global-value))
         (let ((s1 (big-d-little-d-event (cddar wrld1) ens wrld)))
; S1 = #\D, #\E, #\d, or #\Space
           (cond
            ((or (eql s s1)
                 (eql s1 #\Space))
             (big-d-little-d-command-block (cdr wrld1) ens wrld s))
            ((or (eql s1 #\d)
                 (and (eql s #\E)
                      (eql s1 #\D))
                 (and (eql s #\D)
                      (eql s1 #\E)))
             #\d)
            (t ; s must be #\Space
             (big-d-little-d-command-block (cdr wrld1) ens wrld s1)))))
        (t (big-d-little-d-command-block (cdr wrld1) ens wrld s))))

(defun big-m-little-m-name (name wrld)

; This function, which supports the printing of the memoization status, is
; analogous to function big-d-little-d-name, which supports the printing of the
; disabled status.

  (cond ((and (function-symbolp name wrld)
              (not (getpropc name 'constrainedp nil wrld)))
         (if (memoizedp-world name wrld)
             #\M
           #\E))
        (t #\Space)))

(defun big-m-little-m-clique1 (names wrld ans)

; This function, which supports the printing of the memoization status, is
; analogous to function big-d-little-d-clique1, which supports the printing of
; the disabled status.

  (cond ((null names) ans)
        (t (let ((ans1 (big-m-little-m-name (car names) wrld)))
             (cond ((eql ans1 #\m) #\m)
                   ((eql ans1 ans)
                    (big-m-little-m-clique1 (cdr names) wrld ans))
                   (t #\m))))))

(defun big-m-little-m-clique (names wrld)

; This function, which supports the printing of the memoization status, is
; analogous to function big-d-little-d-clique, which supports the printing of
; the disabled status.

  (let ((ans (big-m-little-m-name (car names) wrld)))
    (cond ((eql ans #\m) #\m)
          (t (big-m-little-m-clique1 (cdr names) wrld ans)))))

(defun big-m-little-m-event (ev-tuple wrld)

; This function, which supports the printing of the memoization status, is
; analogous to function big-d-little-d-event, which supports the printing of
; the disabled status.

  (let ((namex (access-event-tuple-namex ev-tuple)))
    (case (access-event-tuple-type ev-tuple)
          ((defun)
           (big-m-little-m-name namex wrld))
          (defuns (big-m-little-m-clique namex wrld))
          (defstobj (big-m-little-m-clique (cddr namex) wrld))
          (otherwise #\Space))))

(defun big-m-little-m-command-block (wrld1 wrld s)

; This function, which supports the printing of the memoization status, is
; analogous to function big-d-little-d-command-block, which supports the
; printing of the disabled status.

  (cond ((or (null wrld1)
             (and (eq (caar wrld1) 'command-landmark)
                  (eq (cadar wrld1) 'global-value)))
         s)
        ((and (eq (caar wrld1) 'event-landmark)
              (eq (cadar wrld1) 'global-value))
         (let ((s1 (big-m-little-m-event (cddar wrld1) wrld)))
; S1 = #\M, #\E, #\m, or #\Space
           (cond
            ((or (eql s s1)
                 (eql s1 #\Space))
             (big-m-little-m-command-block (cdr wrld1) wrld s))
            ((or (eql s1 #\m)
                 (and (eql s #\E)
                      (eql s1 #\M))
                 (and (eql s #\M)
                      (eql s1 #\E)))
             #\m)
            (t ; s must be #\Space
             (big-m-little-m-command-block (cdr wrld1) wrld s1)))))
        (t (big-m-little-m-command-block (cdr wrld1) wrld s))))

(defun symbol-class-char (symbol-class)

; Note: If you change the chars used below, recall that big-c-little-c-event
; knows that #\v is the symbol-class char for encapsulated fns.

  (case symbol-class
        (:program #\P)
        (:ideal #\L)
        (:common-lisp-compliant #\V)
        (otherwise #\Space)))

(defun defun-mode-string (defun-mode)
  (case defun-mode
        (:logic ":logic")
        (:program ":program")
        (otherwise (er hard 'defun-mode-string
                       "Unrecognized defun-mode, ~x0."
                       defun-mode))))

(defun big-c-little-c-event (ev-tuple wrld)

; The big-c-little-c of an event tuple with non-0 namex is a pair of
; characters, (c1 . c2), where each indicates a symbol-class.  C1 indicates the
; introductory symbol-class of the namex.  C2 indicates the current
; symbol-class.  However, if the current class is the same as the introductory
; one, c2 is #\Space.  Note that all elements of namex have the same
; symbol-class forever.  (Only defuns and encapsulate events introduce more
; than one name, and those cliques of functions are in the same class forever.)
; If an event tuple introduces no names, we return (#\Space . #\Space).

; Note: The name big-c-little-c-event is a misnomer from an earlier age.

  (case
    (access-event-tuple-type ev-tuple)
    ((defuns defun defstobj)
     (let ((c1 (symbol-class-char (access-event-tuple-symbol-class ev-tuple)))
           (c2 (symbol-class-char
                (let ((namex (access-event-tuple-namex ev-tuple)))
                  (cond ((symbolp namex) (symbol-class namex wrld))
                        (t (symbol-class (car namex) wrld)))))))
       (cond ((eql c1 c2)
              (cons c1 #\Space))
             (t (cons c1 c2)))))
    (encapsulate '(#\v . #\Space))
    (otherwise '(#\Space . #\Space))))

(defun big-c-little-c-command-block (wrld1 wrld s)

; This function determines the big-c-little-c pair of a block of events.  If
; the block contains more than one event, its pair is (#\Space . #\Space)
; because we expect the individual events in the block to have their own
; pairs printed.  If the block contains only one event, its pair is
; the pair of the block, because we generally print such blocks as the
; event.

; We scan down wrld1 to the next command landmark inspecting each of the event
; landmarks in the current command block.  (Therefore, initially wrld1 ought to
; be just past the command landmark for the block in question.) S is initially
; nil and is set to the pair of the first event we find.  Upon finding a
; second event we return (#\Space . #\Space), but if we get to the end of the
; block, we return s.

  (cond ((or (null wrld1)
             (and (eq (caar wrld1) 'command-landmark)
                  (eq (cadar wrld1) 'global-value)))

; Can a block contain no events?  I don't know anymore.  But if so, its
; defun-mode is '(#\Space . #\Space).

         (or s '(#\Space . #\Space)))
        ((and (eq (caar wrld1) 'event-landmark)
              (eq (cadar wrld1) 'global-value))
         (cond (s '(#\Space . #\Space))
               (t (big-c-little-c-command-block
                   (cdr wrld1) wrld
                   (big-c-little-c-event (cddar wrld1) wrld)))))
        (t (big-c-little-c-command-block (cdr wrld1) wrld s))))

; Now we turn to the problem of printing according to some ldd.  We first
; develop the functions for sketching a command or event form.  This is
; like evisceration (indeed, it uses the same mechanisms) but we handle
; commonly occurring event and command forms specially so that we see
; what we often want to see and no more.

(defun print-ldd-full-or-sketch/mutual-recursion (lst)

; See print-ldd-full-or-sketch.

  (cond ((null lst) nil)
        (t (cons (list 'defun (cadr (car lst)) (caddr (car lst))
                       *evisceration-ellipsis-mark*)
                 (print-ldd-full-or-sketch/mutual-recursion (cdr lst))))))

(defun print-ldd-full-or-sketch/encapsulate (lst)

; See print-ldd-full-or-sketch.

  (cond ((null lst) nil)
        (t (cons (list (car (car lst)) *evisceration-ellipsis-mark*)
                 (print-ldd-full-or-sketch/encapsulate (cdr lst))))))

; If a form has a documentation string in the database, we avoid printing
; the string.  We'll develop the general handling of doc strings soon.  But
; for now we have to define the function that recognizes when the user
; intends his string to be inserted into the database.

(defun normalize-char (c hyphen-is-spacep)
  (if (or (eql c #\Newline)
          (and hyphen-is-spacep (eql c #\-)))
      #\Space
      (char-upcase c)))

(defun normalize-string1 (str hyphen-is-spacep j ans)
  (cond ((< j 0) ans)
        (t (let ((c (normalize-char (char str j)
                                    hyphen-is-spacep)))
             (normalize-string1 str
                                hyphen-is-spacep
                                (1- j)
                                (cond ((and (eql c #\Space)
                                            (eql c (car ans)))
                                       ans)
                                      (t (cons c ans))))))))

(defun normalize-string (str hyphen-is-spacep)

; Str is a string for which we wish to search.  A normalized pattern
; is a list of the chars in the string, all of which are upper cased
; with #\Newline converted to #\Space and adjacent #\Spaces collapsed
; to one #\Space.  If hyphen-is-spacep is t, #\- is normalized to
; #\Space too.

  (normalize-string1 str hyphen-is-spacep (1- (length str)) nil))

(defun string-matchp (pat-lst str j jmax normp skippingp)

; Pat-lst is a list of characters.  Str is a string of length jmax.
; 0<=j<jmax.  If normp is non-nil we are to see str as though it had
; been normalized.  Normp should be either nil, t or
; 'hyphen-is-space.  If Skippingp is t then we are skipping
; whitespace in the str.

  (cond
   ((null pat-lst) t)
   ((>= j jmax) nil)
   (t (let ((c (if normp
                   (normalize-char (char str j)
                                   (eq normp 'hyphen-is-space))
                   (char str j))))
        (cond
         ((and skippingp (eql c #\Space))
          (string-matchp pat-lst str (1+ j) jmax normp t))
         (t (and (eql c (car pat-lst))
                 (string-matchp (cdr pat-lst)
                                str (1+ j) jmax
                                normp
                                (if normp
                                    (eql c #\Space)
                                    nil)))))))))

(defun print-ldd-full-or-sketch (fullp form state)

; When fullp is nil, this function is like eviscerate with print-level
; 2 and print-length 3, except that we here recognize several special
; cases.  We return the eviscerated form.

; Forms with the cars shown below are always eviscerated as
; shown:

; (defun name args ...)
; (defmacro name args ...)
; (defthm name ...)
; (mutual-recursion (defun name1 args1 ...) etc)
; (encapsulate ((name1 ...) etc) ...)    ; which is also:
; (encapsulate (((P * *) ...) etc) ...)

; When fullp is t we zap the documentation strings out of event
; forms.

; It is assumed that form is well-formed.  In particular, that it has
; been evaluated without error.  Thus, if its car is defun, for
; example, it really is of the form (defun name args dcls* body).

; Technically, we should eviscerate the name and args to ensure that
; any occurrence of the *evisceration-mark* in them is properly protected.
; But the mark is a keyword and inspection of the special forms above
; reveals that there are no keywords among the uneviscerated parts.

  (cond
   ((atom form) (mv form state))
   (fullp (let* ((evisc-tuple (ld-evisc-tuple state))
                 (evisc-alist (world-evisceration-alist state (car evisc-tuple)))
                 (print-level (cadr evisc-tuple))
                 (print-length (caddr evisc-tuple)))
            (cond (evisc-tuple
                   (eviscerate-top form
                                   print-level
                                   print-length
                                   evisc-alist
                                   (table-alist 'evisc-table (w state))
                                   nil
                                   state))
                  (t (mv form state)))))
   (t
    (mv
     (case
       (car form)
       ((defun defund defmacro)
        (list (car form) (cadr form) (caddr form) *evisceration-ellipsis-mark*))
       ((defthm defthmd)
        (list (car form) (cadr form) *evisceration-ellipsis-mark*))
       (defconst
        (list (car form) (cadr form) *evisceration-ellipsis-mark*))
       (mutual-recursion
        (cons 'mutual-recursion
              (print-ldd-full-or-sketch/mutual-recursion (cdr form))))
       (encapsulate
        (list 'encapsulate
              (print-ldd-full-or-sketch/encapsulate (cadr form))
              *evisceration-ellipsis-mark*))
       (t (eviscerate-simple form 2 3 nil nil nil)))
     state))))

(defmacro with-base-10 (form)

; Form evaluates to state.  Here, we want to evaluate form with the print base
; set to 10 and the print radix set to nil.

; In order to avoid parallelism hazards due to wormhole printing from inside
; the waterfall (see for example (io? prove t ...) in waterfall-msg), we avoid
; calling state-global-let* below when the print-base is already 10, as it
; typically will be (see with-ctx-summarized).  The downside is that we are
; replicating the code, form.  Without this change, if you build ACL2 with
; #+acl2-par, then evaluate the following forms, you'll see lots of parallelism
; hazard warnings.

;   :mini-proveall
;   :ubt! force-test
;   (set-waterfall-parallelism :pseudo-parallel)
;   (set-waterfall-printing :full)
;   (f-put-global 'parallelism-hazards-action t state)
;   (DEFTHM FORCE-TEST ...) ; see mini-proveall

  `(cond ((and (eql (f-get-global 'print-base state) 10)
               (eq (f-get-global 'print-radix state) nil))
          ,form)
         (t (mv-let (erp val state)
                    (state-global-let* ((print-base 10 set-print-base)
                                        (print-radix nil set-print-radix))
                                       (pprogn ,form (value nil)))
                    (declare (ignore erp val))
                    state))))

(defun print-ldd-formula-column ()
  14)

(defun print-ldd (ldd channel state)

; This is the general purpose function for printing out an ldd.

  (with-base-10
   (let ((formula-col
          (if (eq (access-ldd-class ldd) 'command)
              (print-ldd-formula-column)
            (+ (print-ldd-formula-column)
               (access-ldd-n ldd))))
         (status (access-ldd-status ldd)))
     (declare (type (signed-byte 30) formula-col))
     (pprogn
      (princ$ (if (access-ldd-markp ldd)
                  (access-ldd-markp ldd)
                #\Space)
              channel state)
      (let ((defun-mode-pair (access ldd-status status :defun-mode-pair)))
        (pprogn
         (princ$ (car defun-mode-pair) channel state)
         (princ$ (cdr defun-mode-pair) channel state)))
      (let ((disabled (access ldd-status status :disabled)))
        (princ$ (if (eql disabled #\E) #\Space disabled)
                channel state))
      (let ((memoized (access ldd-status status :memoized)))
        (princ$ (if (eql memoized #\E) #\Space memoized)
                channel state))
      (let ((cur-col 5))
        (if (eq (access-ldd-class ldd) 'command)
            (mv-let
             (col state)
             (fmt1 "~c0~s1"
                   (list
                    (cons #\0 (cons (access-ldd-n ldd) 7))
                    (cons #\1 (cond
                               ((= (access-ldd-n ldd)
                                   (absolute-to-relative-command-number
                                    (max-absolute-command-number (w state))
                                    (w state)))
                                ":x")
                               (t "  "))))
                   cur-col channel state nil)
             (declare (ignore col))
             state)
          (spaces (- formula-col cur-col) cur-col channel state)))
      (mv-let
       (form state)
       (print-ldd-full-or-sketch (access-ldd-fullp ldd)
                                 (access-ldd-form ldd)
                                 state)
       (fmt-ppr
        form
        t
        (+f (fmt-hard-right-margin state) (-f formula-col))
        0
        formula-col channel state
        (not (and (access-ldd-fullp ldd)
                  (null (ld-evisc-tuple state))))))
      (newline channel state)))))

(defun print-ldds (ldds channel state)
  (cond ((null ldds) state)
        (t (pprogn (print-ldd (car ldds) channel state)
                   (print-ldds (cdr ldds) channel state)))))

; Now we turn to the problem of assembling lists of ldds.  There are
; currently three different situations in which we do this and rather
; than try to unify them, we write a special-purpose function for
; each.  The three situations are:

; (1) When we wish to print out a sequence of commands:  We print only the
;     commands, not their events, and we only sketch each command.  We
;     mark the endpoints.

; (2) When we wish to print out an entire command block, meaning the
;     command and each of its events: We will print the command in
;     full and marked, and we will only sketch each event.  We will
;     not show any events in the special case that there is only one
;     event and it has the same form as the command.  This function,
;     make-ldd-command-block, is the simplest of our functions that
;     deals with a mixture of commands and events.  It has to crawl
;     over the world, reversing the order (more or less) of the events
;     and taking the command in at the end.

; (3) When we wish to print out an event and its context: This is like
;     case (2) above in that we print a command and its block.  But we
;     only sketch the forms involved, except for the event requested,
;     which we print marked and in full.  To make things monumentally
;     more difficult, we also elide away irrelevant events in the
;     block.

(defun make-command-ldd (markp fullp cmd-wrld ens wrld)
  (make-ldd 'command
            markp
            (make ldd-status
                  :defun-mode-pair
                  (big-c-little-c-command-block (cdr cmd-wrld) wrld nil)
                  :disabled
                  (big-d-little-d-command-block (cdr cmd-wrld) ens wrld
                                                #\Space)
                  :memoized
                  (big-m-little-m-command-block (cdr cmd-wrld) wrld #\Space))
            (absolute-to-relative-command-number
             (access-command-tuple-number (cddar cmd-wrld))
             wrld)
            fullp
            (access-command-tuple-form (cddar cmd-wrld))))

(defmacro extend-pe-table (name form)
  `(with-output
     :off error ; avoid extra needless layer of error
     (table pe-table
            ',name
            (cons (cons (getpropc ',name 'absolute-event-number
                                  (list :error
                                        (concatenate 'string
                                                     "Event for "
                                                     ,(symbol-name name)
                                                     " (package "
                                                     ,(symbol-package-name name)
                                                     ") not found."))
                                  world)
                        ',form)
                  (cdr (assoc-eq ',name
                                 (table-alist 'pe-table world)))))))

(defun pe-event-form (event-tuple wrld)

; Note: change cd-some-event-matchp to use this function if the :SEARCH utility
; described in :doc command-descriptor is to use the pe-table.

  (let* ((ev-form (access-event-tuple-form event-tuple))
         (ev-n (access-event-tuple-number event-tuple))
         (pe-entry (cdr (assoc ev-n
                               (cdr (assoc-eq (cadr ev-form)
                                              (table-alist 'pe-table
                                                           wrld)))))))
    (or pe-entry
        ev-form)))

(defun make-event-ldd (markp indent fullp ev-tuple ens wrld)
  (make-ldd 'event
            markp
            (make ldd-status
                  :defun-mode-pair
                  (big-c-little-c-event ev-tuple wrld)
                  :disabled
                  (big-d-little-d-event ev-tuple ens wrld)
                  :memoized
                  (big-m-little-m-event ev-tuple wrld))
            indent
            fullp
            (pe-event-form ev-tuple wrld)))

(defun make-ldds-command-sequence (cmd-wrld1 cmd2 ens wrld markp ans)

; Cmd-wrld1 is a world that starts on a command landmark.  Cmd2 is a command
; tuple somewhere in cmd-wrld1 (that is, cmd1 occurred chronologically after
; cmd2).  We assemble onto ans the ldds for sketching each command between the
; two.  We mark the two endpoints provided markp is t.  If we mark, we use / as
; the mark for the earliest command and \ as the mark for the latest, so that
; when printed chronologically the marks resemble the ends of a large brace.
; If only one command is in the region, we mark it with the pointer character,
; >.

  (cond ((equal (cddar cmd-wrld1) cmd2)
         (cons (make-command-ldd (and markp (cond ((null ans) #\>) (t #\/)))
                                 nil cmd-wrld1 ens wrld)
               ans))
        (t (make-ldds-command-sequence
            (scan-to-command (cdr cmd-wrld1))
            cmd2
            ens wrld
            markp
            (cons (make-command-ldd (and markp (cond ((null ans) #\\)(t nil)))
                                    nil cmd-wrld1 ens wrld)
                  ans)))))

(defun make-ldds-command-block1 (wrld1 cmd-ldd indent fullp super-stk ens wrld
                                       ans)

; Wrld1 is a world created by the command tuple described by cmd-ldd.
; Indent is the current indent value for the ldds we create.
; Super-stk is a list of event tuples, each of which is a currently
; open superior event (e.g., encapsulation or include-book).  We wish
; to make a list of ldds for printing out that command and every event
; in its block.  We print the command marked and in full.  We only
; sketch the events, but we sketch each of them.  This is the simplest
; function that shows how to crawl down a world and produce
; print-order ldds that suggest the structure of a block.

  (cond
   ((or (null wrld1)
        (and (eq (caar wrld1) 'command-landmark)
             (eq (cadar wrld1) 'global-value)))
    (cond
     (super-stk
      (make-ldds-command-block1
       wrld1
       cmd-ldd
       (1- indent)
       fullp
       (cdr super-stk)
       ens wrld
       (cons (make-event-ldd nil (1- indent) fullp (car super-stk) ens wrld)
             ans)))
     (t (cons cmd-ldd ans))))
   ((and (eq (caar wrld1) 'event-landmark)
         (eq (cadar wrld1) 'global-value))
    (cond
     ((and super-stk
           (<= (access-event-tuple-depth (cddar wrld1))
               (access-event-tuple-depth (car super-stk))))
      (make-ldds-command-block1
       wrld1
       cmd-ldd
       (1- indent)
       fullp
       (cdr super-stk)
       ens wrld
       (cons (make-event-ldd nil (1- indent) fullp (car super-stk) ens wrld)
             ans)))
     ((or (eq (access-event-tuple-type (cddar wrld1)) 'encapsulate)
          (eq (access-event-tuple-type (cddar wrld1)) 'include-book))
      (make-ldds-command-block1
       (cdr wrld1)
       cmd-ldd
       (1+ indent)
       fullp
       (cons (cddar wrld1) super-stk)
       ens wrld
       ans))
     (t (make-ldds-command-block1
         (cdr wrld1)
         cmd-ldd
         indent
         fullp
         super-stk
         ens wrld
         (cons (make-event-ldd nil indent fullp (cddar wrld1) ens wrld)
               ans)))))
   (t (make-ldds-command-block1 (cdr wrld1)
                                cmd-ldd
                                indent
                                fullp
                                super-stk
                                ens wrld
                                ans))))

(defun make-ldds-command-block (cmd-wrld ens wrld fullp ans)

; Cmd-wrld is a world starting with a command landmark.  We make a list of ldds
; to describe the entire command block, sketching the command and sketching
; each of the events contained within the block.

  (let ((cmd-ldd (make-command-ldd nil fullp cmd-wrld ens wrld))
        (wrld1 (scan-to-event (cdr cmd-wrld))))
    (cond
     ((equal (pe-event-form (cddar wrld1) wrld)
             (access-command-tuple-form (cddar cmd-wrld)))

; If the command form is the same as the event form of the
; chronologically last event then that event is to be skipped.

      (make-ldds-command-block1 (cdr wrld1) cmd-ldd 1 fullp nil ens wrld ans))
     (t (make-ldds-command-block1 wrld1 cmd-ldd 1 fullp nil ens wrld ans)))))

(defun ens-maybe-brr (state)

; We want history commands to show the "appropriate" enabled status.  For the
; user inside break-rewrite, "appropriate" suggests using the enabled structure
; at the current point in the proof.

  (or (and (eq (f-get-global 'wormhole-name state) 'brr)
           (access rewrite-constant
                   (get-brr-local 'rcnst state)
                   :current-enabled-structure))
      (ens state)))

(defun pcb-pcb!-fn (cd fullp state)
  (io? history nil (mv erp val state)
       (cd fullp)
       (let ((wrld (w state))
             (ens (ens-maybe-brr state)))
         (er-let* ((cmd-wrld (er-decode-cd cd wrld :pcb state)))
                  (pprogn
                   (print-ldds
                    (make-ldds-command-block cmd-wrld ens wrld fullp nil)
                    (standard-co state)
                    state)
                   (value :invisible))))))

(defun pcb!-fn (cd state)
  (pcb-pcb!-fn cd t state))

(defun pcb-fn (cd state)
  (pcb-pcb!-fn cd nil state))

(defmacro pcb! (cd)
  (list 'pcb!-fn cd 'state))

(defun pc-fn (cd state)
  (io? history nil (mv erp val state)
       (cd)
       (let ((wrld (w state)))
         (er-let* ((cmd-wrld (er-decode-cd cd wrld :pc state)))
                  (pprogn
                   (print-ldd
                    (make-command-ldd nil t cmd-wrld (ens-maybe-brr state) wrld)
                    (standard-co state)
                    state)
                   (value :invisible))))))

(defmacro pc (cd)
  (list 'pc-fn cd 'state))

(defun pcs-fn (cd1 cd2 markp state)

; We print the commands between cd1 and cd2 (relative order of these two cds is
; irrelevant).  We always print the most recent command here, possibly elided
; into the cd1-cd2 region.  We mark the end points of the region if markp is t.

  (io? history nil (mv erp val state)
       (cd1 markp cd2)
       (let ((wrld (w state))
             (ens (ens-maybe-brr state)))
         (er-let*
          ((cmd-wrld1 (er-decode-cd cd1 wrld :ps state))
           (cmd-wrld2 (er-decode-cd cd2 wrld :ps state)))
          (let ((later-wrld
                 (if (>= (access-command-tuple-number (cddar cmd-wrld1))
                         (access-command-tuple-number (cddar cmd-wrld2)))
                     cmd-wrld1
                   cmd-wrld2))
                (earlier-wrld
                 (if (>= (access-command-tuple-number (cddar cmd-wrld1))
                         (access-command-tuple-number (cddar cmd-wrld2)))
                     cmd-wrld2
                   cmd-wrld1)))
            (pprogn
             (print-ldds (make-ldds-command-sequence later-wrld
                                                     (cddar earlier-wrld)
                                                     ens
                                                     wrld
                                                     markp
                                                     nil)
                         (standard-co state)
                         state)
             (cond
              ((= (access-command-tuple-number (cddar later-wrld))
                  (max-absolute-command-number wrld))
               state)
              ((= (1+ (access-command-tuple-number (cddar later-wrld)))
                  (max-absolute-command-number wrld))
               (print-ldd (make-command-ldd nil nil wrld ens wrld)
                          (standard-co state)
                          state))
              (t (pprogn (mv-let
                          (col state)
                          (fmt1 "~t0: ...~%"
                                (list (cons #\0
                                            (- (print-ldd-formula-column)
                                               2)))
                                0 (standard-co state) state nil)
                          (declare (ignore col))
                          state)
                         (print-ldd (make-command-ldd nil nil wrld ens wrld)
                                    (standard-co state)
                                    state))))
             (value :invisible)))))))

(defmacro pcs (cd1 cd2)
  (list 'pcs-fn cd1 cd2 t 'state))

(defun get-command-sequence-fn1 (cmd-wrld1 cmd2 ans)

; Keep this in sync with make-ldds-command-sequence.

  (cond ((equal (cddar cmd-wrld1) cmd2)
         (cons (access-command-tuple-form (cddar cmd-wrld1))
               ans))
        (t (get-command-sequence-fn1
            (scan-to-command (cdr cmd-wrld1))
            cmd2
            (cons (access-command-tuple-form (cddar cmd-wrld1))
                  ans)))))

(defun get-command-sequence-fn (cd1 cd2 state)

; We print the commands between cd1 and cd2 (relative order of these two cds is
; irrelevant).  We always print the most recent command here, possibly elided
; into the cd1-cd2 region.  We mark the end points of the region if markp is t.

  (let ((wrld (w state))
        (ctx 'get-command-sequence))
    (er-let*
        ((cmd-wrld1 (er-decode-cd cd1 wrld ctx state))
         (cmd-wrld2 (er-decode-cd cd2 wrld ctx state)))
      (let ((later-wrld
             (if (>= (access-command-tuple-number (cddar cmd-wrld1))
                     (access-command-tuple-number (cddar cmd-wrld2)))
                 cmd-wrld1
               cmd-wrld2))
            (earlier-wrld
             (if (>= (access-command-tuple-number (cddar cmd-wrld1))
                     (access-command-tuple-number (cddar cmd-wrld2)))
                 cmd-wrld2
               cmd-wrld1)))
        (value (get-command-sequence-fn1 later-wrld
                                         (cddar earlier-wrld)
                                         nil))))))

(defmacro get-command-sequence (cd1 cd2)
  (list 'get-command-sequence-fn cd1 cd2 'state))

(defmacro gcs (cd1 cd2)
  `(get-command-sequence ,cd1 ,cd2))

(defmacro pbt (cd1)
  (list 'pcs-fn cd1 :x nil 'state))

(defmacro pcb (cd)
  (list 'pcb-fn cd 'state))

(defun print-indented-list-msg (objects indent final-string)

; Indents the indicated number of spaces, then prints the first object, then
; prints a newline; then, recurs.  Finally, prints the string final-string.  If
; final-string is punctuation as represented by fmt directive ~y, then it will
; be printed just after the last object.

  (cond
   ((null objects) "")
   ((and final-string (null (cdr objects)))
    (msg (concatenate 'string "~_0~y1" final-string)
         indent
         (car objects)))
   (t
    (msg "~_0~y1~@2"
         indent
         (car objects)
         (print-indented-list-msg (cdr objects) indent final-string)))))

(defun print-indented-list (objects indent last-col channel evisc-tuple state)
  (cond ((null objects)
         (mv last-col state))
        (t (fmt1 "~@0"
                 (list (cons #\0 (print-indented-list-msg objects indent nil)))
                 0 channel state evisc-tuple))))

(defun relativize-book-path (filename system-books-dir action)

; System-books-dir is presumably the value of state global 'system-books-dir.
; There are three possibilities, depending on action, which should either be
; :make-cons (the default), nil, or a book name as supplied to include-book
; (hence without the .lisp extension).

; First suppose that the given filename is an absolute pathname extending the
; absolute directory name system-books-dir.  Then if action is :make-cons,
; return (:system . suffix), where suffix is a relative pathname that points to
; the same file with respect to system-books-dir.  Otherwise return action.lisp
; if action is non-nil, and otherwise, a suitable pathname relative to the
; community books directory, prefixed by "[books]/".

; Otherwise, return action.lisp if action is a string, else the given filename.

  (declare (xargs :guard (and (stringp filename)
                              (stringp system-books-dir)
                              (<= (length system-books-dir) (fixnum-bound))
                              (or (eq action :make-cons)
                                  (eq action nil)
                                  (stringp action)))))
  (cond ((and (stringp filename) ; could already be (:system . fname)
              (string-prefixp system-books-dir filename))
         (let ((relative-pathname
                (subseq filename (length system-books-dir) nil)))
           (cond
            ((eq action :make-cons)
             (cons :system relative-pathname))
            (action
             (concatenate 'string action ".lisp"))
            (t
             (concatenate 'string "[books]/" relative-pathname)))))
        ((stringp action)
         (concatenate 'string action ".lisp"))
        (t filename)))

(defun relativize-book-path-lst (lst root action)
  (declare (xargs :guard (and (string-listp lst)
                              (stringp root))))
  (cond ((endp lst) nil)
        (t (cons (relativize-book-path (car lst) root action)
                 (relativize-book-path-lst (cdr lst) root action)))))

(defun print-book-path (book-path indent channel state)
  (assert$
   book-path
   (mv-let (col state)
     (fmt1 "~_0[Included books, outermost to innermost:~|"
           (list (cons #\0 indent))
           0 channel state nil)
     (declare (ignore col))
     (mv-let (col state)
       (print-indented-list
        (cond ((f-get-global 'script-mode state)
               (relativize-book-path-lst book-path
                                         (f-get-global 'system-books-dir state)
                                         nil))
              (t book-path))
        (1+ indent) 0 channel nil state)
       (pprogn (if (eql col 0)
                   (spaces indent col channel state)
                 state)
               (princ$ #\] channel state))))))

(defun pe-fn1 (wrld channel ev-wrld cmd-wrld state)
  (cond
   ((equal (pe-event-form (cddar ev-wrld) wrld)
           (access-command-tuple-form (cddar cmd-wrld)))
    (print-ldd
     (make-command-ldd nil t cmd-wrld (ens-maybe-brr state) wrld)
     channel state))
   (t
    (let ((indent (print-ldd-formula-column))
          (ens (ens-maybe-brr state)))
      (pprogn
       (print-ldd
        (make-command-ldd nil nil cmd-wrld ens wrld)
        channel state)
       (mv-let (col state)
         (fmt1 "~_0\\~%" (list (cons #\0 indent)) 0 channel state nil)
         (declare (ignore col))
         state)
       (let ((book-path (global-val 'include-book-path ev-wrld)))
         (cond (book-path
                (pprogn
                 (print-book-path (reverse book-path)
                                  indent channel state)
                 (fms "~_0\\~%" (list (cons #\0 indent)) channel state nil)))
               (t state)))
       (print-ldd
        (make-event-ldd #\> 1 t (cddar ev-wrld) ens wrld)
        channel
        state))))))

(defun pe-fn2 (logical-name wrld channel ev-wrld state)
  (er-let* ((cmd-wrld (superior-command-world ev-wrld wrld :pe state)))
           (pprogn (pe-fn1 wrld channel ev-wrld cmd-wrld state)
                   (let ((new-ev-wrld (decode-logical-name
                                       logical-name
                                       (scan-to-event (cdr ev-wrld)))))
                     (if new-ev-wrld
                         (pe-fn2 logical-name wrld channel new-ev-wrld state)
                       (value :invisible))))))

(defun pe-fn-main (logical-name wrld channel state)
  (er-let* ((ev-wrld (er-decode-logical-name logical-name wrld :pe
                                             state))
            (cmd-wrld (superior-command-world ev-wrld wrld :pe
                                              state)))
    (pprogn
     (pe-fn1 wrld channel ev-wrld cmd-wrld state)
     (let ((new-ev-wrld (and (not (eq logical-name :here))
                             (decode-logical-name
                              logical-name
                              (scan-to-event (cdr ev-wrld))))))
       (if (null new-ev-wrld)
           (value :invisible)
         (pprogn
          (fms "Additional events for the logical name ~x0:~%"
               (list (cons #\0 logical-name))
               channel
               state
               nil)
          (pe-fn2 logical-name wrld channel new-ev-wrld
                  state)))))))

(defun pe-fn (logical-name state)
  (io? history nil (mv erp val state)
       (logical-name)
       (let ((wrld (w state))
             (channel (standard-co state)))
         (cond
          ((and (symbolp logical-name)
                (not (eq logical-name :here))
                (eql (getpropc logical-name 'absolute-event-number nil wrld)
                     0))

; This special case avoids printing something like the following, which isn't
; very useful.

;       -7479  (ENTER-BOOT-STRAP-MODE :UNIX)

; We make the change here rather than in pe-fn1 because don't want to mess
; around at the level of ldd structures.  It's a close call.

; We don't make the corresponding change to pc-fn.  With pe, one is asking for
; an event, which in the case of a function is probably a request for a
; definition.  We want to serve the intention of that request.  With pc, one is
; asking for the full command, so we give it to them.

           (pprogn
            (fms "~x0 is built into ACL2 without a defining event.~#1~[  See ~
                  :DOC ~x0.~/~]~|"
                 (list (cons #\0 logical-name)
                       (cons #\1 (if (assoc-eq logical-name
                                               (global-val 'documentation-alist
                                                           wrld))
                                     0
                                   1)))
                 channel state nil)
            (value :invisible)))
          (t
           (let ((fn (deref-macro-name logical-name (macro-aliases wrld))))
             (cond
              ((eq fn logical-name)
               (pe-fn-main logical-name wrld channel state))
              (t
               (pprogn
                (fms "Note that macro ~x0 is a macro alias for the function ~
                      ~x1; so we print event information for each in turn.~|"
                     (list (cons #\0 logical-name)
                           (cons #\1 fn))
                     channel
                     state
                     nil)
                (fms "Printing event information for ~x0:~|"
                     (list (cons #\0 logical-name))
                     channel
                     state
                     nil)
                (er-progn
                 (pe-fn-main logical-name wrld channel state)
                 (pprogn
                  (fms "Printing event information for ~x0:~|"
                       (list (cons #\0 fn))
                       channel
                       state
                       nil)
                  (pe-fn-main fn wrld channel state))))))))))))

(defmacro pe (logical-name)
  (list 'pe-fn logical-name 'state))

(defmacro pe! (logical-name)
  `(with-output :off (summary event)
     (make-event (er-progn
                  (let ((logical-name ,logical-name))
                    (cond
                     ((eq logical-name :here)
                      (pe :here))
                     (t (er-progn (table pe-table nil nil :clear)
                                  (pe ,logical-name)))))
                  (value '(value-triple :invisible))))))

(defmacro gthm (fn &optional (simp-p 't) guard-debug)
  `(untranslate (guard-theorem ,fn ,simp-p ,guard-debug (w state) state)
                t
                (w state)))

(defmacro tthm (fn)
  `(let* ((fn ,fn)
          (term (termination-theorem fn (w state))))
     (cond ((and (consp term)
                 (eq (car term) :failed))
            (er soft 'top
                "There is no termination theorem for ~x0.  ~@1."
                fn (cdr term)))
           (t (value (untranslate term t (w state)))))))

(defun command-block-names1 (wrld ans symbol-classes)

; Symbol-Classes is a list of symbol-classes or else is t.  We scan down world
; to the next command landmark unioning into ans all the names whose
; introduction-time symbol-class is contained in symbol-classes, where
; symbol-classes t denotes the set of everything (!).  Note that symbol-classes
; t is different from symbol-classes (:program :ideal :common-lisp-compliant)
; because some names, e.g., label names, don't have symbol-classes (i.e., have
; access-event-tuple-symbol-class nil).  We return the final ans and the wrld
; starting with the next command landmark.  Note also that we use the
; symbol-class at introduction, not the current one.

  (cond
   ((or (null wrld)
        (and (eq (caar wrld) 'command-landmark)
             (eq (cadar wrld) 'global-value)))
    (mv ans wrld))
   ((and (eq (caar wrld) 'event-landmark)
         (eq (cadar wrld) 'global-value))
    (cond
     ((or (eq symbol-classes t)
          (member-eq (access-event-tuple-symbol-class (cddar wrld))
                     symbol-classes))
      (let ((namex (access-event-tuple-namex (cddar wrld))))
        (command-block-names1 (cdr wrld)
                              (cond ((equal namex 0) ans)
                                    ((equal namex nil) ans)
                                    ((atom namex)
; Might be symbolp or stringp.
                                     (add-to-set-equal namex ans))
                                    (t (union-equal namex ans)))
                              symbol-classes)))
     (t (command-block-names1 (cdr wrld) ans symbol-classes))))
   (t (command-block-names1 (cdr wrld) ans symbol-classes))))

(defun command-block-names (wrld symbol-classes)

; Wrld is a world that begins with a command landmark.  We collect all the
; names introduced in the symbol-classes listed.  Symbol-Classes = t means all
; (including nil).  We return the collection of names and the world starting
; with the next command landmark.

  (command-block-names1 (cdr wrld) nil symbol-classes))

(defun symbol-name-lst (lst)
  (declare (xargs :guard (symbol-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (symbol-name (car lst))
                 (symbol-name-lst (cdr lst))))))

(defun acl2-query-simulate-interaction (msg alist controlledp ans state)
  (cond ((and (atom ans)
              (or controlledp
                  (and (not (f-get-global 'window-interfacep state))

; If a special window is devoted to queries, then there is no way to
; pretend to answer, so we don't.  We just go on.  Imagine that we
; answered and the window disappeared so quickly you couldn't see the
; answer.

                       (not (eq (standard-co state) *standard-co*)))))
         (pprogn
          (fms msg alist (standard-co state) state (ld-evisc-tuple state))
          (princ$ ans (standard-co state) state)
          (newline (standard-co state) state)
          state))
        (t state)))

(defun acl2-query1 (id qt alist state)

; This is the function actually responsible for printing the query
; and getting the answer, for the current level in the query tree qt.
; See acl2-query for the context.

  (let ((dv (cdr-assoc-query-id id (ld-query-control-alist state)))
        (msg "ACL2 Query (~x0):  ~@1  (~*2):  ")
        (alist1 (list (cons #\0 id)
                      (cons #\1 (cons (car qt) alist))
                      (cons #\2
                            (list "" "~s*" "~s* or " "~s*, "
                                  (symbol-name-lst (evens (cdr qt))))))))
    (cond
     ((null dv)
      (pprogn
       (io? query nil state
            (alist1 msg)
            (fms msg alist1 *standard-co* state (ld-evisc-tuple state)))
       (er-let*
        ((ans (with-infixp-nil
               (read-object *standard-oi* state))))
        (let ((temp (and (symbolp ans)
                         (assoc-keyword
                          (intern (symbol-name ans) "KEYWORD")
                          (cdr qt)))))
          (cond (temp
                 (pprogn
                  (acl2-query-simulate-interaction msg alist1 nil ans state)
                  (value (cadr temp))))
                (t (acl2-query1 id qt alist state)))))))
     ((eq dv t)
      (pprogn
       (acl2-query-simulate-interaction msg alist1 t (cadr qt) state)
       (value (caddr qt))))
     (t (let ((temp (assoc-keyword (if (consp dv) (car dv) dv) (cdr qt))))
          (cond
           ((null temp)
            (er soft 'acl2-query
                "The default response, ~x0, supplied in ~
                 ld-query-control-alist for the ~x1 query, is not one ~
                 of the expected responses.  The ~x1 query ~
                 is~%~%~@2~%~%Note the expected responses above.  See ~
                 :DOC ld-query-control-alist."
                (if (consp dv) (car dv) dv)
                id
                (cons msg alist1)))
           (t
            (pprogn
             (acl2-query-simulate-interaction msg alist1 t dv state)
             (value (cadr temp))))))))))

(defun acl2-query (id qt alist state)

; A query-tree qt is either an atom or a cons of the form
;   (str :k1 qt1 ... :kn qtn)
; where str is a string suitable for printing with ~@, each :ki is a
; keyword, and each qti is a query tree.  If qt is an atom, it is
; returned.  Otherwise, str is printed and the user is prompted for
; one of the keys.  When ki is typed, we recur on the corresponding
; qti.  Note that the user need not type a keyword, just a symbol
; whose symbol-name is that of one of the keywords.

; Thus, '("Do you want to redefine ~x0?" :y t :n nil) will print
; the question and require a simple y or n answer, returning t or nil
; as appropriate.

; Warning: We don't always actually read an answer!  We sometimes
; default.  Our behavior depends on the LD specials standard-co,
; standard-oi, and ld-query-control-alist, as follows.

; Let x be (cdr (assoc-eq id (ld-query-control-alist state))).  X must
; be either nil, a keyword, or a singleton list containing a keyword.
; If it is a keyword, then it must be one of the keys in (cdr qt) or
; else we cause an error.  If x is a keyword or a one-element list
; containing a keyword, we act as though we read that keyword as the
; answer to our query.  If x is nil, we read *standard-oi* for an
; answer.

; Now what about printing?  Where does the query actually appear?  If
; we get the answer from the control alist, then we print both the
; query and the answer to standard-co, making it simulate an
; interaction -- except, if the control alist gave us a singleton
; list, then we do not do any printing.  If we get the answer from
; *standard-oi* then we print the query to *standard-co*.  In
; addition, if we get the answer from *standard-oi* but *standard-co*
; is not standard-co, we simulate the interaction on standard-co.

  (cond ((atom qt) (value qt))
        ((not (and (or (stringp (car qt))
                       (and (consp (car qt))
                            (stringp (caar qt))))
                   (consp (cdr qt))
                   (keyword-value-listp (cdr qt))))
         (er soft 'acl2-query
             "The object ~x0 is not a query tree!  See the comment in ~
              acl2-query."
             qt))
        (t
         (er-let* ((qt1 (acl2-query1 id qt alist state)))
                  (acl2-query id qt1 alist state)))))

(defun collect-names-in-defun-modes (names defun-modes wrld)

; Collect the elements of names (all of which are fn symbols) whose current
; defun-mode is in the given set.

  (cond ((null names) nil)
        ((member-eq (fdefun-mode (car names) wrld) defun-modes)
         (cons (car names)
               (collect-names-in-defun-modes (cdr names) defun-modes wrld)))
        (t (collect-names-in-defun-modes (cdr names) defun-modes wrld))))

(defun ubt-ubu-query (kwd wrld1 wrld0 seen kept-commands wrld state banger)

; Wrld0 is a predecessor world of wrld1 which starts with a command landmark.
; We scan down wrld1 until we get to wrld0.  For each command encountered we
; ask the user if he wants us to preserve the :program names introduced.
; If so, we add the command to kept-commands.  We only ask about the latest
; definition of any name (the accumulator seen contains all the names we've
; asked about).  We return the list of commands to be re-executed (in
; chronological -- not reverse chronological -- order).  Of course, this is an
; error/value/state function.

; Kwd is :ubt, :ubu, or :ubt-prehistory.

; Note: The kept-commands, when non-nil, always starts with a defun-mode
; keyword command, i.e., :logic or :program.  This is the
; default-defun-mode in which the next command on the list, the first "real
; command," was executed.  When we grow the kept-command list, we remove
; redundant mode changes.  So for example, if kept-commands were
; '(:program cmd2 ...) and we then wished to add cmd1, then if the mode in
; which cmd1 was executed was :program the result is '(:program cmd1
; cmd2 ...)  while if cmd1's mode is :logic the result is '(:logic cmd1
; :program cmd2 ...).  Note that the mode may indeed be :logic, even
; though cmd1 introduces a :program function, because the mode of the
; introduced function may not be the default-defun-mode.  The commands are kept
; because the functions they introduce are :program, not because they were
; executed in :program mode.  But we must make sure the default mode is
; the same as it was when the command was last executed, just in case the mode
; of the functions is the default one.

  (cond
   ((or (null wrld1)
        (equal wrld1 wrld0))
    (value kept-commands))
   (t (mv-let
       (names wrld2)
       (command-block-names wrld1 '(:program))

; Names is the list of all names in the current command block whose
; introduction-time symbol-class was :program.

       (cond
        ((and names (set-difference-eq names seen))
         (er-let*
          ((ans (if banger
                    (value banger)
                    (let ((logic-names
                           (collect-names-in-defun-modes names '(:logic) wrld)))
                      (acl2-query
                       kwd
                       '("The command ~X01 introduced the :program ~
                          name~#2~[~/s~] ~&2.~#5~[~/  ~&3 ~#4~[has~/have~] ~
                          since been made logical.~]  Do you wish to ~
                          re-execute this command after the ~xi?"
                         :y t :n nil :y! :all :n! :none :q :q
                         :? ("We are undoing some commands.  We have ~
                              encountered a command, printed above, that ~
                              introduced a :program function symbol.  It is ~
                              unusual to use ~xi while defining :program ~
                              functions, since redefinition is permitted.  ~
                              Therefore, we suspect that you are mixing ~
                              :program and :logic definitions, as when one is ~
                              developing utilities for the prover.  When ~
                              undoing through such a mixed session, it is ~
                              often intended that the :logic functions be ~
                              undone while the :program ones not be, since the ~
                              latter ones are just utilities.  While we cannot ~
                              selectively undo commands, we do offer to redo ~
                              selected commands when we have finished undoing. ~
                               The situation is complicated by the fact that ~
                              :programs can become :logic functions after the ~
                              introductory event and that the same name can be ~
                              redefined several times.  Unless noted in the ~
                              question above, the functions discussed are all ~
                              still :program. The commands we offer for ~
                              re-execution are those responsible for ~
                              introducing the most recent definitions of ~
                              :program names, whether the names are still ~
                              :program or not.  That is, if in the region ~
                              undone there is more than one :program ~
                              definition of a name, we will offer to redo the ~
                              chronologically latest one.~%~%If you answer Y, ~
                              the command printed above will be re-executed.  ~
                              If you answer N, it will not be.  The answer Y! ~
                              means the same thing as answering Y to this and ~
                              all subsequent queries in this ~xi  The answer ~
                              N! is analogous.  Finally, Q means to abort the ~
                              ~xi without undoing anything."
                             :y t :n nil :y! :all :n! :none :q :q))
                       (list (cons #\i kwd)
                             (cons #\0
                                   (access-command-tuple-form (cddar wrld1)))
                             (cons #\1 (term-evisc-tuple t state))
                             (cons #\2 names)
                             (cons #\3 logic-names)
                             (cons #\4 (if (cdr logic-names) 1 0))
                             (cons #\5 (if (null logic-names) 0 1)))
                       state)))))
          (cond
           ((eq ans :q) (mv t nil state))
           (t
            (ubt-ubu-query
             kwd wrld2 wrld0
             (union-eq names seen)
             (if (or (eq ans t) (eq ans :all))
                 (cons (access-command-tuple-defun-mode (cddar wrld1))
                       (cons (access-command-tuple-form (cddar wrld1))
                             (cond
                              ((eq (access-command-tuple-defun-mode
                                    (cddar wrld1))
                                   (car kept-commands))
                               (cdr kept-commands))
                              (t kept-commands))))
               kept-commands)
             wrld state
             (or banger
                 (if (eq ans :all) :all nil)
                 (if (eq ans :none) :none nil)))))))
        (t (ubt-ubu-query kwd wrld2 wrld0 seen kept-commands wrld state
                          banger)))))))

; We can't define ubt?-ubu?-fn until we define LD, because it uses LD to replay
; selected commands.  So we proceed as though we had defined ubt?-ubu?-fn.

(defmacro ubt? (cd)
  (list 'ubt?-ubu?-fn :ubt cd 'state))

(defmacro ubt (cd)
  (list 'ubt-ubu-fn :ubt cd 'state))

(defmacro ubt! (cd)
  (list 'ubt!-ubu!-fn :ubt cd 'state))

(defmacro ubu? (cd)
  (list 'ubt?-ubu?-fn :ubu cd 'state))

(defmacro ubu (cd)
  (list 'ubt-ubu-fn :ubu cd 'state))

(defmacro ubu! (cd)
  (list 'ubt!-ubu!-fn :ubu cd 'state))

(defmacro u nil
  '(ubt! :x))

; We now develop the most trivial event we have: deflabel.  It
; illustrates the basic structure of our event code.

(defun chk-virgin-msg (name new-type wrld state)
  #-acl2-loop-only
  (mv (chk-virgin-msg2 name new-type wrld state)
      state)
  #+acl2-loop-only
  (declare (ignore name new-type wrld))
  #+acl2-loop-only
  (mv-let (erp val state)
    (read-acl2-oracle state)
    (let ((msg (or erp val)))
      (mv (and (msgp msg) msg)
          state))))

(defun chk-virgin (name new-type ctx wrld state)
  (mv-let (msg state)
    (chk-virgin-msg name new-type wrld state)
    (cond (msg (er soft ctx "~@0" msg))
          (t (value nil)))))

(defun chk-boot-strap-redefineable-namep (name ctx wrld state)
  (cond ((global-val 'boot-strap-pass-2 wrld)
         (value nil))
        ((not (member-eq name (global-val 'chk-new-name-lst wrld)))
         (er soft ctx
             "The name ~x0 is already in use and is not among those expected ~
              by chk-boot-strap-redefineable-namep to be redundantly defined ~
              during initialization. If you wish it to be, add ~x0 to the ~
              global-val setting of 'chk-new-name-lst in ~
              primordial-world-globals."
             name))
        (t (chk-virgin name t ctx wrld state))))

(defun maybe-coerce-overwrite-to-erase (old-type new-type mode)
  (cond ((and (eq old-type 'function)
              (eq new-type 'function))
         mode)
        (t :erase)))

(defun redefinition-renewal-mode (name all-names old-type new-type
                                       reclassifyingp ctx wrld state)

; We use 'ld-redefinition-action to determine whether the redefinition of name,
; currently of old-type in wrld, is to be :erase, :overwrite or
; :reclassifying-overwrite.  New-type is the new type name will have and
; reclassifyingp is a non-nil, non-cons value only if this is a :program
; function to identical-defp :logic function redefinition.  If this
; redefinition is not permitted, we cause an error, in which case if
; reclassifyingp is a cons then it is an explanatory message to be printed in
; the error message, in the context "Note that <msg>".

; The only time we permit a redefinition when ld-redefinition-action prohibits
; it is when we return :reclassifying-overwrite, except for the case of
; updating non-executable :program mode ("proxy") functions; see :DOC
; defproxy.  In the latter case we have some concern about redefining inlined
; functions, so we proclaim them notinline; see install-defs-for-add-trip.

; This function interacts with the user if necessary.  See :DOC
; ld-redefinition-action.

  (let ((act (f-get-global 'ld-redefinition-action state))
        (proxy-upgrade-p
         (and (eq old-type 'function)
              (consp new-type)

; New-type is (function stobjs-in . stobjs-out); see chk-signature.

              (eq (car new-type) 'function)
              (eq (getpropc name 'non-executablep nil wrld)
                  :program)

; A non-executable :program-mode function has no logical content, so it is
; logically safe to redefine it.  We check however that the signature hasn't
; changed, for the practical reason that we don't want to break existing
; calls.

              (equal (stobjs-in name wrld) (cadr new-type))
              (equal (stobjs-out name wrld) (cddr new-type))))
        (attachment-alist (attachment-alist name wrld)))
    (cond
     ((and reclassifyingp
           (not (consp reclassifyingp)))
      (cond ((and (let ((okp (f-get-global
                              'verify-termination-on-raw-program-okp
                              state)))
                    (not (or (eq okp t)
                             (member-eq name okp))))
                  (member-eq name
                             (f-get-global 'program-fns-with-raw-code state)))
             (er soft ctx
                 "The function ~x0 must remain in :PROGRAM mode, because it ~
                  has been marked as a function that has special raw Lisp ~
                  code.  To avoid this error, see :DOC ~
                  verify-termination-on-raw-program-okp."
                 name))
            (t (value :reclassifying-overwrite))))
     ((and attachment-alist
           (not (eq (car attachment-alist) :ATTACHMENT-DISALLOWED))

; During the boot-strap, we may replace non-executable :program mode
; definitions (from defproxy) without removing attachments, so that system
; functions implemented using attachments will not be disrupted.

           (not (f-get-global 'boot-strap-flg state)))
      (er soft ctx
          "The name ~x0 is in use as a ~@1, and it has an attachment.  Before ~
           redefining it you must remove its attachment, for example by ~
           executing the form ~x2.  We hope that this is not a significant ~
           inconvenience; it seemed potentially too complex to execute such a ~
           defattach form safely on your behalf."
          name
          (logical-name-type-string old-type)
          (cond ((programp name wrld)
                 `(defattach (,name nil) :skip-checks t))
                (t
                 `(defattach ,name nil)))))
     ((and (null act)
           (not proxy-upgrade-p))

; We cause an error, with rather extensive code below designed to print a
; helpful error message.

      (mv-let
       (erp val state)
       (er soft ctx
           "The name ~x0 is in use as a ~@1.~#2~[  ~/  (This name is used in ~
            the implementation of single-threaded objects.)  ~/  Note that ~
            ~@3~|~]The redefinition feature is currently off.  See :DOC ~
            ld-redefinition-action.~@4"
           name
           (logical-name-type-string old-type)
           (cond ((eq new-type 'stobj-live-var) 1)
                 ((consp reclassifyingp) 2)
                 (t 0))
           reclassifyingp
           (cond ((eq (getpropc name 'non-executablep nil wrld)
                      :program)
                  (msg "  Note that you are attempting to upgrade a proxy, ~
                        which is only legal using an encapsulate signature ~
                        that matches the original signature of the function; ~
                        see :DOC defproxy."))
                 (t "")))
       (declare (ignore erp val))
       (er-let*
        ((ev-wrld (er-decode-logical-name name wrld ctx state)))
        (pprogn
         (let ((book-path-rev (reverse (global-val 'include-book-path
                                                   ev-wrld)))
               (current-path-rev (reverse (global-val 'include-book-path
                                                      wrld))))
           (io? error nil state
                (name book-path-rev current-path-rev wrld)
                (pprogn
                 (cond ((and (null book-path-rev)
                             (acl2-system-namep name wrld))
                        (fms "Note: ~x0 has already been defined as a system ~
                              name; that is, it is built into ACL2.~|~%"
                             (list (cons #\0 name))
                             (standard-co state) state nil))
                       ((null book-path-rev)
                        (fms "Note: ~x0 was previously defined at the top ~
                              level~#1~[~/ of the book being certified~].~|~%"
                             (list (cons #\0 name)
                                   (cons #\1
                                         (if (f-get-global 'certify-book-info
                                                           state)
                                             1
                                           0)))
                             (standard-co state) state nil))
                       (t (pprogn
                           (fms "Note: ~x0 was previously defined in the last ~
                                 of the following books.~|~%"
                                (list (cons #\0 name))
                                (standard-co state) state nil)
                           (print-book-path
                            book-path-rev
                            3 (standard-co state) state)
                           (newline (standard-co state) state))))
                 (cond ((null current-path-rev)
                        state)
                       (t (pprogn
                           (fms "Note: the current attempt to define ~x0 is ~
                                 being made in the last of the following ~
                                 books.~|~%"
                                (list (cons #\0 name))
                                (standard-co state) state nil)
                           (print-book-path
                            current-path-rev
                            3 (standard-co state) state)
                           (newline (standard-co state) state)))))))
         (silent-error state)))))
     ((cdr (assoc-eq name (table-alist 'memoize-table wrld)))
      (er soft ctx
          "The name ~x0 is in use as a ~@1, and it is currently memoized.  ~
           You must execute ~x2 before attempting to redefine it."
          name
          (logical-name-type-string old-type)
          (list 'unmemoize (kwote name))))
     ((eq new-type 'package)

; Some symbols seen by this fn have new-type package, namely the base
; symbol of the rune naming the rules added by defpkg, q.v.  Old-type
; can't be 'package.  If this error message is eliminated and
; redefinition is ever permitted, then revisit the call of
; chk-just-new-name in chk-acceptable-defpkg and arrange for it to use
; the resulting world.

      (er soft ctx
          "When a package is introduced, a rule is added describing the ~
           result produced by (symbol-package-name (intern x pkg)).  That ~
           rule has a name, i.e., a rune, based on some symbol which must ~
           be new.  In the case of the current package definition the base ~
           symbol for the rune in question is ~x0.  The symbol is not new. ~
            Furthermore, the redefinition facility makes no provision for ~
           packages.  Please rename the package or :ubt ~x0.  Sorry."
          name))
     ((null (getpropc name 'absolute-event-number nil wrld))

; One might think that (a) this function is only called on old names and (b)
; every old name has an absolute event number.  Therefore, why do we ask the
; question above?  Because we could have a name introduced by the signature in
; encapsulate that is intended to be local, but was not embedded in a local
; form.

      (er soft ctx
          "The name ~x0 appears to have been introduced in the signature list ~
           of an encapsulate, yet is being defined non-locally."
          name))

; We do not permit any supporter of a single-threaded object implementation to
; be redefined, except by redefining the single-threaded object itself.  The
; main reason is that even though the functions like the recognizers appear as
; ordinary predicates, the types are really built in across the whole
; implementation.  So it's all or nothing.  Besides, I don't really want to
; think about the weird combinations of changing a defstobj supporter to an
; unrelated function, even if the user thinks he knows what he is doing.

     ((and (defstobj-supporterp name wrld)
           (not (and (eq new-type 'stobj)
                     (eq old-type 'stobj))))

; I sweated over the logic above.  How do we get here?  Name is a defstobj
; supporter.  Under what conditions do we permit a defstobj supporter to be
; redefined?  Only by redefining the object name itself -- not by redefining
; individual functions.  So we want to avoid causing an error if the new and
; old types are both 'stobj (i.e., name is the name of the single-threaded
; object both in the old and the new worlds).

; WARNING: If this function does not cause an error, we proceed, in
; chk-redefineable-namep, to renew name.  In the case of stobj names, that
; function renews all the supporting names as well.  Thus, it is important to
; maintain the invariant: if this function does not cause an error and name is
; a defstobj supporter, then name is the stobj name.

      (er soft ctx
          "The name ~x0 is in use supporting the implementation of ~
           the single-threaded object ~x1.  We do not permit such ~
           names to be redefined except by redefining ~x1 itself with ~
           a new DEFSTOBJ."
          name
          (defstobj-supporterp name wrld)))

; If we get here, we know that either name is not currently a defstobj
; supporter of any kind or else that it is the old defstobj name and is being
; redefined as a defstobj.

     (t
      (let ((sysdefp (acl2-system-namep name wrld)))
        (cond
         ((and sysdefp
               (not (ttag (w state)))
               (not (and proxy-upgrade-p
                         (f-get-global 'boot-strap-flg state))))
          (er soft ctx
              "Redefinition of system names, such as ~x0, is not permitted ~
               unless there is an active trust tag (ttag).  See :DOC defttag."
              name))
         (proxy-upgrade-p

; We erase all vestiges of the old function.  It may well be safe to return
; :overwrite instead.  But at one time we tried that while also leaving the
; 'attachment property unchanged by renew-name/overwrite (rather than making it
; unbound), and we then got an error from the following sequence of events,
; "HARD ACL2 ERROR in LOGICAL-NAME-TYPE: FOO is evidently a logical name but of
; undetermined type."

;  (defproxy foo (*) => *)
;  (defttag t)
;  (defun g (x) x)
;  (defattach (foo g) :skip-checks t)
;  (defattach (foo nil) :skip-checks t)
;  (defstub foo (x) t)

; When we promote boot-strap functions from non-executable :program mode
; ("proxy") functions to encapsulated functions, we thus lose the 'attachment
; property.  Outside the boot-strap, where we disallow all redefinition when
; there is an attachment, this is not a restriction.  But in the boot-strap, we
; will lose the 'attachment property even though the appropriate Lisp global
; (the attachment-symbol) remains set.  This doesn't present a problem,
; however; system functions are special, in that they can very temporarily have
; attachments without an 'attachment property, until the redefinition in
; progress (by an encapsulate) is complete.

          (cond ((eq (car attachment-alist) :ATTACHMENT-DISALLOWED)
                 (er soft ctx
                     "Implementation error: It is surprising to see ~
                      attachments disallowed for a non-executable :program ~
                      mode function (a proxy).  See ~
                      redefinition-renewal-mode."))
                (t (value :erase))))
         ((eq (car act) :doit!)
          (value
           (maybe-coerce-overwrite-to-erase old-type new-type (cdr act))))
         ((or (eq (car act) :query)
              (and sysdefp
                   (or (eq (car act) :warn)
                       (eq (car act) :doit))))
          (let ((rest (cdr (member-eq name all-names))))
            (er-let* ((ans
                       (acl2-query
                        :redef
                        `("~#0~[~x1 is an ACL2 system~/The name ~x1 is in use ~
                           as a~] ~@2.~#3~[~/  Its current defun-mode is ~
                           ~@4.~] Do you ~#0~[really ~/~]want to redefine ~
                           it?~#6~[~/  Note: if you redefine it we will first ~
                           erase its supporters, ~&7.~]"
                          :n nil :y t :e erase :o overwrite
                          ,@(and rest '(:y! y!))
                          :?
                          ("N means ``no'' and answering that way will abort ~
                            the attempted redefinition.  All other responses ~
                            allow the redefinition and may render ACL2 unsafe ~
                            and/or unsound.  Y in the current context is the ~
                            same as ~#5~[E~/O~]~@8.  E means ``erase the ~
                            property list of ~x1 before redefining it.''  O ~
                            means ``Overwrite existing properties of ~x1 ~
                            while redefining it'' but is different from ~
                            erasure only when a function is being redefined ~
                            as another function.   Neither alternative is ~
                            guaranteed to produce a sensible ACL2 state.  If ~
                            you are unsure of what all this means, abort with ~
                            N and see :DOC ld-redefinition-action for details."
                           :n nil :y t :e erase :o overwrite
                           ,@(and rest '(:y! y!))))
                        (list (cons #\0 (if sysdefp 0 1))
                              (cons #\1 name)
                              (cons #\2 (logical-name-type-string old-type))
                              (cons #\3 (if (eq old-type 'function) 1 0))
                              (cons #\4 (if (eq old-type 'function)
                                            (defun-mode-string
                                              (fdefun-mode name wrld))
                                          nil))
                              (cons #\5 (if (eq (cdr act)
                                                :erase)
                                            0 1))
                              (cons #\6 (if (defstobj-supporterp name wrld)
                                            1 0))
                              (cons #\7 (getpropc (defstobj-supporterp name
                                                    wrld)
                                                  'stobj nil wrld))
                              (cons #\8
                                    (if rest
                                        (msg ", and Y! will assume a Y ~
                                              response without further query ~
                                              for the list of related names ~
                                              not yet redefined, ~X01"
                                             rest
                                             (abbrev-evisc-tuple state))
                                      "")))
                        state)))
              (cond
               ((null ans) (mv t nil state))
               ((eq ans t)
                (value
                 (maybe-coerce-overwrite-to-erase old-type new-type (cdr act))))
               ((eq ans 'y!)
                (er-progn
                 (set-ld-redefinition-action (cons ':doit! (cdr act)) state)
                 (value
                  (maybe-coerce-overwrite-to-erase old-type new-type (cdr act)))))
               ((eq ans 'erase) (value :erase))
               (t (value
                   (maybe-coerce-overwrite-to-erase old-type new-type
                                                    :overwrite)))))))
         (t

; If name is a system name, then the car of 'ld-redefinition-action must be
; :warn!  If name is not a system name, the car of 'ld-redefinition-action may
; be :warn!, :doit, or :warn.  In all cases, we are to proceed with the
; redefinition without any interaction here.

          (value
           (maybe-coerce-overwrite-to-erase old-type new-type
                                            (cdr act))))))))))

(defun redefined-names1 (wrld ans)
  (cond ((null wrld) ans)
        ((eq (cadar wrld) 'redefined)
         (cond
          ((eq (car (cddar wrld)) :reclassifying-overwrite)
           (redefined-names1 (cdr wrld) ans))
          (t (redefined-names1 (cdr wrld)
                               (add-to-set-eq (caar wrld) ans)))))
        (t (redefined-names1 (cdr wrld) ans))))

(defun redefined-names (state)
  (redefined-names1 (w state) nil))

(defun chk-redefineable-namep (name all-names new-type reclassifyingp ctx wrld
                                    state)

; Name is a non-new name in wrld.  We are about to redefine it and make its
; logical-name-type be new-type.  If reclassifyingp is non-nil and not a consp
; message (see redundant-or-reclassifying-defunp) then we know that in fact
; this new definition is just a conversion of the existing definition.
; Redefinition is permitted if the value of 'ld-redefinition-action is not nil,
; or if we are defining a function to replace a non-executable :program mode
; function (such as is introduced by defproxy).  In all these non-erroneous
; cases, we renew name appropriately and return the resulting world.

; The LD special 'ld-redefinition-action determines how we react to
; redefinition attempts.  See :DOC ld-redefinition-action.

; It must be understood that if 'ld-redefinition-action is non-nil then no
; logical sense is maintained, all bets are off, the system is unsound and
; liable to cause all manner of hard lisp errors, etc.

  (let ((old-type (logical-name-type name wrld nil)))
    (cond
     ((and (f-get-global 'boot-strap-flg state)
           (not (global-val 'boot-strap-pass-2 wrld))
           (or (not reclassifyingp)
               (consp reclassifyingp)))

; If we are in the first pass of booting and name is one of those we know is
; used before it is defined, we act as though it were actually new.

      (er-progn
       (chk-boot-strap-redefineable-namep name ctx wrld state)
       (value wrld)))
     (t

; In obtaining the renewal mode, :erase or :overwrite, we might cause an error
; that aborts because name is not to be redefined.

      (er-let*
       ((renewal-mode
         (redefinition-renewal-mode name all-names
                                    old-type new-type reclassifyingp
                                    ctx wrld state)))
       (cond
        ((defstobj-supporterp name wrld)

; Because of the checks in redefinition-renewal-mode, we know the
; defstobj-supporterp above returns name itself.  But to be rugged I
; will code it this way.  If name is a defstobj supporter of any kind,
; we renew all the supporters!

         (value
          (renew-names (let ((prop (getpropc (defstobj-supporterp name wrld)
                                             'stobj nil wrld)))
                         (list* name
                                (access stobj-property prop :live-var)
                                (access stobj-property prop :recognizer)
                                (access stobj-property prop :creator)
                                (access stobj-property prop :fixer)
                                (access stobj-property prop :names)))
                       renewal-mode wrld)))
        (t (value (renew-name name renewal-mode wrld)))))))))

(defun chk-just-new-name (name all-names new-type reclassifyingp ctx w
                               state)

; Assuming that name has survived chk-all-but-new-name, we check that it is in
; fact new.  If it is, we return the world, w.  If it is not new, then what we
; do depends on various state variables such as whether we are in boot-strap
; and whether redefinition is allowed.  But unless we cause an error we will
; always return the world extending w in which the redefinition is to occur.
; All-names is a list of all names, including name, for which redefinition is
; also currently to be considered.

; Name is being considered for introduction with logical-name-type new-type.
; Reclassifyingp, when not nil and not a consp, means that this redefinition is
; known to be identical to the existing definition except that it has been
; given the new defun-mode :logic.  This will allow us to permit the
; redefinition of system functions.  See the comment in
; redundant-or-reclassifying-defunp for more about reclassifyingp.

; Observe that it is difficult for the caller to tell whether redefinition is
; occurring.  In fact, inspection of the returned world will reveal the answer:
; sweep down the world to the next event-landmark and see whether any
; 'redefined property is stored.  All names with such a property are being
; redefined by this event (possibly soundly by reclassifying :program names).
; This sweep is actually done by collect-redefined on behalf of stop-event
; which prints a suitable warning message.

  (cond
   ((new-namep name w)

; If name has no properties in w, then we next check that it is not
; defined in raw Common Lisp.

    (let ((actual-new-type
           (cond ((and (consp new-type)
                       (eq (car new-type) 'function))
                  'function)
                 (t new-type))))
      (er-progn (chk-virgin name actual-new-type ctx w state)
                (value w))))
   ((and (f-get-global 'boot-strap-flg state)
         (not (global-val 'boot-strap-pass-2 w))
         (or (not reclassifyingp)
             (consp reclassifyingp)))

; If we are in the first pass of booting and name is one of those we know is
; used before it is defined, we act as though it were actually new.

    (er-progn
     (chk-boot-strap-redefineable-namep name ctx w state)
     (value w)))
   (t
    (chk-redefineable-namep name all-names new-type reclassifyingp ctx w
                            state))))

(defun no-new-namesp (lst wrld)

; Lst is a true list of symbols.  We return t if every name in it
; is old.

  (cond ((null lst) t)
        ((new-namep (car lst) wrld) nil)
        (t (no-new-namesp (cdr lst) wrld))))

(defun chk-just-new-names-rec (names all-names new-type reclassifyingp ctx w state)
  (cond
   ((null names) (value w))
   (t (er-let*
          ((wrld1 (chk-just-new-name (car names) all-names new-type
                                     reclassifyingp ctx w state)))
        (chk-just-new-names-rec (cdr names) all-names new-type reclassifyingp
                                ctx wrld1 state)))))

(defun chk-just-new-names (names new-type reclassifyingp ctx w state)

; Assuming that names has survived chk-all-but-new-names, we check that they
; are in fact all new.  We either cause an error or return the world, we are to
; use in the coming definition.  Observe that it is difficult for the caller to
; tell whether redefinition is occurring.  In fact, inspection of world will
; reveal the answer: sweep down world to the next event-landmark and see
; whether any 'redefined property is stored.  All names with such a property
; are being redefined by this event.  This sweep is actually done by
; collect-redefined on behalf of stop-event which prints a suitable warning
; message.

; Reclassifyingp is as explained in redundant-or-reclassifying-defunp.  In
; particular, it can be a message (a cons pair suitable for printing with ~@).

  (cond
   ((null names) (value w))
   (t (state-global-let*
       ((ld-redefinition-action (ld-redefinition-action state)))
       (chk-just-new-names-rec names names new-type reclassifyingp
                               ctx w state)))))

(defun alpha-< (x y)

; X and y are symbols or strings.  We return t iff x comes before y in
; an alphabetic ordering of their print names.  We are somewhat free
; to decide how to handle packages and strings v. symbols.  We choose
; to put 'ABC before "ABC" and we use package-names only to break
; ties among two symbols with the same symbol-name.

  (let ((xstr (if (symbolp x) (symbol-name x) x))
        (ystr (if (symbolp y) (symbol-name y) y)))
    (cond ((string< xstr ystr) t)
          ((equal xstr ystr)
           (if (symbolp x)
               (if (symbolp y)
                   (string< (symbol-package-name x)
                            (symbol-package-name y))
                   t)
               nil))
          (t nil))))

(defun merge-alpha-< (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((alpha-< (car l1) (car l2))
         (cons (car l1) (merge-alpha-< (cdr l1) l2)))
        (t (cons (car l2) (merge-alpha-< l1 (cdr l2))))))

(defun merge-sort-alpha-< (l)
  (cond ((null (cdr l)) l)
        (t (merge-alpha-< (merge-sort-alpha-< (evens l))
                          (merge-sort-alpha-< (odds l))))))

(defun putprop-unless (sym key val exception wrld)

; We do (putprop sym key val wrld) unless val is exception, in which case we do
; nothing.  We return the possibly modified wrld.

; It has occurred to us to wonder whether a form such as (putprop-unless sym
; prop val nil wrld) -- that is, where exception is nil -- might cause problems
; if the the value of property prop for symbol sym is *acl2-property-unbound*.
; We don't think that's a problem, though, since in that case (getprop sym prop
; default name wrld) returns nil, just as though we'd actually put nil
; explicitly as the property value.

; See also the related function putprop-if-different, whose definition contains
; a comment showing how it relates to the present function.

  (cond ((equal val exception) wrld)
        (t (putprop sym key val wrld))))

(defun redefined-warning (redef ctx state)

; Redef is either nil, a true-list of symbols, a single symbol, or a
; single string.  In the latter two cases we think of redef denoting a
; singleton list.  If the list denoted by redef is non-nil we print a
; warning that every name in that list has been redefined.

  (if redef
      (warning$ ctx "Redef"
               "~&0 redefined.~%~%"
               (if (atom redef) (list redef) redef))
      state))

; Get-event was previously defined here, but is now introduced earlier to
; support the definition of ev-fncall-rec-logical (specifically, the definition
; of guard-raw, which is called by ev-fncall-guard-er, which in turn is called
; by ev-fncall-rec-logical).

(defun redundant-labelp (name event-form wrld)

; The only time a label is considered redundant is during the second pass of
; initialization and only then if it was already defined with the same
; event-form.

  (and (global-val 'boot-strap-pass-2 wrld)
       (getpropc name 'label nil wrld)
       (equal event-form (get-event name wrld))))

(defmacro make-ctx-for-event (event-form ctx)
  #+acl2-infix
  `(if (output-in-infixp state) ,event-form ,ctx)
  #-acl2-infix
  (declare (ignore event-form))
  #-acl2-infix
  ctx)

(defun deflabel-fn (name state event-form)

; Warning: If this event ever generates proof obligations, remove it from the
; list of exceptions in install-event just below its "Comment on irrelevance of
; skip-proofs".

  (with-ctx-summarized
   (make-ctx-for-event event-form (cons 'deflabel name))
   (let ((wrld1 (w state))
         (event-form (or event-form
                         (list 'deflabel name))))
     (cond
      ((redundant-labelp name event-form wrld1)
       (stop-redundant-event ctx state))
      (t
       (er-progn
        (chk-all-but-new-name name ctx 'label wrld1 state)
        (er-let*
         ((wrld2 (chk-just-new-name name nil 'label nil ctx wrld1 state)))
         (let ((wrld3 (putprop name 'label t wrld2)))

; The only reason we store the 'label property is so that name-introduced
; recognizes this name.

; Note:  We do not permit DEFLABEL to be made redundant.  If this
; is changed, change the text of the :DOC for redundant-events.

           (install-event name
                          event-form
                          'deflabel
                          name
                          nil
                          nil
                          nil
                          nil
                          wrld3
                          state)))))))))

(defun degree-of-match2 (ch1 ch2 str i maximum)
  (cond ((< (1+ i) maximum)
         (if (and (eql ch1 (normalize-char (char str i) nil))
                  (eql ch2 (normalize-char (char str (1+ i)) nil)))
             1
             (degree-of-match2 ch1 ch2 str (1+ i) maximum)))
        (t 0)))

(defun degree-of-match1 (pat-lst str maximum)
  (cond ((null pat-lst) 0)
        ((null (cdr pat-lst)) 0)
        (t (+ (degree-of-match2 (car pat-lst) (cadr pat-lst) str 0 maximum)
              (degree-of-match1 (cdr pat-lst) str maximum)))))

(defun degree-of-match (pat-lst str)

; Pat-lst is a normalized string (with hyphen-is-space nil).  We
; normalize str similarly and compute the degree of match between
; them.  The answer is a rational between 0 and 1.  The number is just
; n divided by (length pat)-1, where n is the number of adjacent
; character pairs in pat that occur adjacently in str.  This is just
; a Royal Kludge that seems to work.

  (if (< (length pat-lst) 2)
      0
      (/ (degree-of-match1 pat-lst str (length str))
         (1- (length pat-lst)))))

(defun find-likely-near-misses (pat-lst alist)

; Alist is the documentation-alist.  Pat-lst is a normalized string
; (with hyphen-is-space nil).  We collect the cars of the pairs in
; alist that have a degree of match of more than one half.  Again, an
; utter kludge.

  (cond ((null alist) nil)
        (t (let ((d (degree-of-match pat-lst
                                     (if (stringp (caar alist))
                                         (caar alist)
                                         (symbol-name (caar alist))))))
             (cond ((<= d 1/2)
                    (find-likely-near-misses pat-lst (cdr alist)))
                   (t (cons (cons d (caar alist))
                            (find-likely-near-misses pat-lst
                                                     (cdr alist)))))))))

(defun print-doc-dwim (name ctx state)
  (let ((lst (merge-sort-car->
              (find-likely-near-misses
               (normalize-string
                (if (stringp name) ; impossible after Version_6.3
                    name
                    (symbol-name name))
                nil)
               *acl2-system-documentation*))))
    (er soft ctx
        "There is no documentation for ~x0.~#1~[~/  A similar documented name ~
         is ~&2.~/  Similar documented names are ~&2.~]~|~%NOTE: See also ~
         :DOC finding-documentation."
        name
        (zero-one-or-more (length lst))
        (strip-cdrs lst))))

(defun doc-fn (name state)
  (cond
   ((not (symbolp name))
    (er soft 'doc
        "Documentation topics are symbols."))
   (t (let ((entry (assoc name *acl2-system-documentation*)))
        (cond (entry (mv-let
                      (col state)
                      (fmt1 "Parent~#0~[~/s~]: ~&0.~|~%"
                            (list (cons #\0 (cadr entry)))
                            0 *standard-co* state nil)
                      (declare (ignore col))
                      (pprogn (princ$ (caddr entry) *standard-co* state)
                              (newline *standard-co* state)
                              (value :invisible))))
              (t (print-doc-dwim name :doc state)))))))

(defmacro doc (name)
  (list 'doc-fn name 'state))

(defmacro help nil
  '(pprogn (fms "For information about <name>, type :DOC <name>.  For an ~
                 introduction to the ACL2 documentation, type :DOC ~
                 documentation.~|"
                nil (standard-co state) state nil)
           (value :invisible)))

(defun trans-fn (form state)
  (io? temporary nil (mv erp val state)
       (form)
       (let ((wrld (w state))
             (channel (standard-co state)))
         (mv-let (flg val bindings state)
                 (translate1 form
                             :stobjs-out
                             '((:stobjs-out . :stobjs-out))
                             t ;;; known-stobjs = t (user interface)
                             'top-level wrld state)
                 (cond ((null flg)
                        (pprogn
                         (fms "~Y01~%=> ~y2~|~%"
                              (list
                               (cons #\0 val)
                               (cons #\1 (term-evisc-tuple nil state))
                               (cons #\2
                                     (prettyify-stobjs-out
                                      (translate-deref :stobjs-out bindings))))
                              channel state nil)
                         (value :invisible)))
                       (t
                        (er soft 'trans
                            ":Trans has failed.  Consider trying :trans! ~
                             instead; see :DOC trans!.")))))))

(defun trans!-fn (form state)
  (io? temporary nil (mv erp val state)
       (form)
       (let ((wrld (w state))
             (channel (standard-co state)))
         (mv-let (flg val bindings state)
                 (translate1 form
                             t
                             nil
                             t ;;; known-stobjs = t (user interface)
                             'top-level wrld state)
                 (declare (ignore bindings))
                 (cond ((null flg)
                        (pprogn
                         (fms "~Y01~|~%"
                              (list (cons #\0 val)
                                    (cons #\1 (term-evisc-tuple nil state)))
                              channel state nil)
                         (value :invisible)))
                       (t (value :invisible)))))))

(defmacro trans (form)
  (list 'trans-fn form 'state))

(defmacro trans! (form)
  (list 'trans!-fn form 'state))

(defun trans1-fn (form state)
  (if (and (consp form)
           (true-listp form)
           (symbolp (car form))
           (getpropc (car form) 'macro-body))
      (macroexpand1 form 'top-level state)
    (er soft 'top-level
        "TRANS1 may only be applied to a form (m t1 ... tk) where m is a ~
         symbol with a 'macro-body property.")))

(defmacro trans1 (form)
  `(trans1-fn ,form state))

(defmacro translam (x)
  `(mv-let (flg val bindings state)
     (cmp-and-value-to-error-quadruple
      (translate11-lambda-object
       ,x
       '(nil) ; stobjs-out
       nil    ; bindings
       nil    ; known-stobjs
       nil    ; flet-alist
       nil    ; cform
       'translam
       (w state)
       (default-state-vars state)
       nil))
     (declare (ignore bindings))
     (mv flg val state)))

(defun tilde-*-props-fn-phrase1 (alist)
  (cond ((null alist) nil)
        (t (cons (msg "~y0~|~ ~y1~|"
                      (caar alist)
                      (cdar alist))
                 (tilde-*-props-fn-phrase1 (cdr alist))))))

(defun tilde-*-props-fn-phrase (alist)
  (list "none" "~@*" "~@*" "~@*"
        (tilde-*-props-fn-phrase1 alist)))

(defun props-fn (sym state)
  (cond ((symbolp sym)
         (io? temporary nil (mv erp val state)
              (sym)
              (pprogn
               (fms "ACL2 Properties of ~y0:~%~*1~%"
                    (list (cons #\0 sym)
                          (cons #\1
                                (tilde-*-props-fn-phrase
                                 (getprops sym
                                           'current-acl2-world
                                           (w
                                            state)))))
                    (standard-co state)
                    state
                    (ld-evisc-tuple state))
               (value :invisible))))
        (t (er soft :props
               "~x0 is not a symbol."
               sym))))

(defmacro props (sym)
  (list 'props-fn sym 'state))

; We now develop walkabout, an extremely useful tool for exploring

(defun walkabout-nth (i x)

; Enumerate the elements of the print representation of the list x,
; from 0.  Include the possible dot as an element.

;      Example x                  Example x
;      (a b c . d)                (a b c d)
; i     0 1 2 3 4                  0 1 2 3

; We fetch the ith element.  But how do we return the dot?  We
; actually return two values (mv dotp xi).  If dotp is true, we're
; really returning the dot.  In this case xi is the character #\.,
; just in case we want to pretend there was a dot there and try
; to go into it or return it.  If dotp is false, then xi is the
; corresponding element of x.

  (cond ((int= i 0)
         (cond ((atom x)
                (mv t #\.))
               (t (mv nil (car x)))))
        ((atom x) (mv nil x))
        (t (walkabout-nth (1- i) (cdr x)))))

(defun walkabout-ip (i x)

; See the examples above showing how we enumerate the elements of the
; print representation of x.  We return t if i is a legal index
; and nil otherwise.

  (cond ((null x) nil)
        ((atom x) (or (int= i 0) (int= i 1)))
        ((int= i 0) t)
        (t (walkabout-ip (1- i) (cdr x)))))

(defun walkabout-huh (state)
  (pprogn (princ$ "Huh?" *standard-co* state)
          (newline *standard-co* state)
          (mv 'continue nil state)))

(defun walkabout1 (i x state intern-flg evisc-tuple alt-evisc-tuple)

; X is a list and we are at position i within it.  This function
; reads commands from *standard-oi* and moves us around in x.  This
; function is inefficient in that it computes the current object,
; xi, from i and x each time.  It would be better to maintain the
; current tail of x so nx could be fast.

  (mv-let
   (dotp xi)
   (walkabout-nth i x)
   (pprogn
    (mv-let (col state)
            (fmt1 (if dotp ".~%:" "~y0~|:")
                  (list (cons #\0 xi))
                  0
                  *standard-co* state
                  (if (eq alt-evisc-tuple :none)
                      evisc-tuple
                    alt-evisc-tuple))
            (declare (ignore col))
            state)
    (mv-let
     (signal val state)
     (mv-let
      (erp obj state)
      (with-infixp-nil
       (read-object *standard-oi* state))
      (cond
       (erp (mv 'exit nil state))
       (t (let ((obj (cond ((not intern-flg) obj)
                           ((symbolp obj)
                            (intern (symbol-name obj) "ACL2"))
                           ((atom obj) obj)
                           ((symbolp (car obj)) ; probably always true
                            (cons (intern (symbol-name (car obj)) "ACL2")
                                  (cdr obj)))
                           (t obj))))
            (case obj
              (nx (if (walkabout-ip (1+ i) x)
                      (mv 'continue (1+ i) state)
                    (walkabout-huh state)))
              (bk (if (= i 0)
                      (walkabout-huh state)
                    (mv 'continue (1- i) state)))
              (0 (mv 'up nil state))
              (pp (mv 'continue-fullp nil state))
              (= (mv 'exit xi state))
              (q (mv 'exit :invisible state))
              (otherwise
               (cond
                ((and (integerp obj) (> obj 0))
                 (cond
                  ((atom xi)
                   (walkabout-huh state))
                  ((walkabout-ip (1- obj) xi)
                   (walkabout1 (1- obj) xi state intern-flg evisc-tuple
                               :none))
                  (t (walkabout-huh state))))
                ((and (consp obj)
                      (eq (car obj) 'pp))
                 (mv-let (print-level print-length)
                         (let ((args (cdr obj)))
                           (case-match args
                             ((print-level print-length)
                              (mv print-level print-length))
                             ((n) (mv n n))
                             (& (mv :bad nil))))
                         (cond ((and (or (natp print-level)
                                         (null print-level))
                                     (or (natp print-length)
                                         (null print-length)))
                                (mv 'continue-fullp
                                    (evisc-tuple print-level print-length
                                                 nil nil)
                                    state))
                               (t (walkabout-huh state)))))
                ((and (consp obj)
                      (eq (car obj) '=)
                      (consp (cdr obj))
                      (symbolp (cadr obj))
                      (null (cddr obj)))
                 (pprogn
                  (f-put-global 'walkabout-alist
                                (cons (cons (cadr obj) xi)
                                      (f-get-global 'walkabout-alist
                                                    state))
                                state)
                  (mv-let (col state)
                          (fmt1 "(walkabout= ~x0) is~%"
                                (list (cons #\0 (cadr obj)))
                                0 *standard-co* state (ld-evisc-tuple state))
                          (declare (ignore col))
                          (mv 'continue nil state))))
                (t (walkabout-huh state)))))))))
     (cond
      ((eq signal 'continue)
       (walkabout1 (or val i) x state intern-flg evisc-tuple :none))
      ((eq signal 'up)
       (mv 'continue nil state))
      ((eq signal 'continue-fullp)
       (walkabout1 i x state intern-flg evisc-tuple val))
      (t (mv 'exit val state)))))))

(defun walkabout (x state)
  (pprogn
   (fms "Commands:~|0, 1, 2, ..., nx, bk, pp, (pp n), (pp lev len), =, (= ~
         symb), and q.~%~%"
        nil *standard-co* state nil)
   (mv-let (signal val state)
           (walkabout1 0 (list x)
                       state
                       (not (equal (current-package state) "ACL2"))
                       (evisc-tuple 2 3 nil nil)
                       :none)
           (declare (ignore signal))
           (value val))))

(defun walkabout=-fn (var state)
  (cond ((symbolp var)
         (cdr (assoc-eq var (f-get-global 'walkabout-alist state))))
        (t nil)))

(defmacro walkabout= (var)
  `(walkabout=-fn ',var state))

; Here we develop the code for inspecting the results of using OBDDs.

(defun lookup-bddnote (cl-id bddnotes)
  (cond
   ((endp bddnotes) nil)
   ((equal cl-id (access bddnote (car bddnotes) :cl-id))
    (car bddnotes))
   (t (lookup-bddnote cl-id (cdr bddnotes)))))

(defun update-bddnote-with-term (cl-id term bddnotes)
  (cond
   ((endp bddnotes)
    (er hard 'update-bddnote-with-term
        "Expected to find clause with name ~@0, but did not!"
        (tilde-@-clause-id-phrase cl-id)))
   ((equal cl-id (access bddnote (car bddnotes) :cl-id))
    (cons (change bddnote (car bddnotes)
                  :term term)
          (cdr bddnotes)))
   (t (cons (car bddnotes)
            (update-bddnote-with-term cl-id term (cdr bddnotes))))))

(defmacro show-bdd (&optional str
                              goal-query-response
                              counterex-query-response
                              term-query-response)

; Not documented below is our use of evisc-tuples that hardwire the print-level
; and print-length, rather than using say the abbrev-evisc-tuple.  That seems
; reasonable given the design of show-bdd, which allows printing terms in full
; after the user sees their abbreviated versions.  It could add more confusion
; than clarity for us to add such documentation below, but if anyone complains,
; then we should probably do so.

  (cond
   ((not (symbolp goal-query-response))
    `(er soft 'show-bdd
         "The optional second argument of show-bdd must be a symbol, but ~x0 ~
          is not."
         ',goal-query-response))
   ((not (symbolp counterex-query-response))
    `(er soft 'show-bdd
         "The optional third argument of show-bdd must be a symbol, but ~x0 ~
          is not."
         ',counterex-query-response))
   ((not (symbolp term-query-response))
    `(er soft 'show-bdd
         "The optional fourth argument of show-bdd must be a symbol, but ~x0 ~
          is not."
         ',term-query-response))
   (t
    `(show-bdd-fn ,str
                  ',goal-query-response
                  ',counterex-query-response
                  ',term-query-response
                  state))))

(defun show-bdd-goal (query-response bddnote chan state)
  (let* ((goal (untranslate (access bddnote bddnote :goal-term) t (w state))))
    (pprogn
     (fms "BDD input term (derived from ~@1):~|"
          (list (cons #\1 (tilde-@-clause-id-phrase
                           (access bddnote bddnote :cl-id))))
          (standard-co state) state nil)
     (cond
      (query-response
       state)
      (t
       (fms "~q2~|"
            (list (cons #\2 goal))
            (standard-co state) state (evisc-tuple 5 7 nil nil))))
     (cond
      ((equal goal (eviscerate-simple goal 5 7 nil
                                      (table-alist 'evisc-table (w state))
                                      nil))
       state)
      (t
       (mv-let (erp ans state)
               (if query-response
                   (let ((query-response
                          (intern (symbol-name query-response) "KEYWORD")))
                     (value (case query-response
                                  (:w :w)
                                  (:nil nil)
                                  (otherwise t))))
                 (acl2-query
                  :show-bdd
                  '("Print the goal in full?"
                    :n nil :y t :w :w
                    :? ("Y will print the goal in full.  W will put you in a ~
                         structural display editor that lets you type a ~
                         positive integer N to dive to the Nth element of the ~
                         current list, 0 to go up a level, PP to print the ~
                         current object in full, and Q to quit."
                        :n nil :y t :w :w))
                  nil
                  state))
               (declare (ignore erp))
               (cond ((eq ans :w)
                      (mv-let (erp ans state)
                              (walkabout goal state)
                              (declare (ignore erp ans))
                              state))
                     (ans (fms "~x0~|"
                               (list (cons #\0 goal))
                               chan state nil))
                     (t state))))))))

(defun merge-car-term-order (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((term-order (car (car l1)) (car (car l2)))
         (cons (car l1) (merge-car-term-order (cdr l1) l2)))
        (t (cons (car l2) (merge-car-term-order l1 (cdr l2))))))

(defun merge-sort-car-term-order (l)
  (cond ((null (cdr l)) l)
        (t (merge-car-term-order (merge-sort-car-term-order (evens l))
                                 (merge-sort-car-term-order (odds l))))))

(defun falsifying-pair-p (term val asst)
  (cond
   ((endp asst) nil)
   ((equal term (caar asst))
    (or (and (null val) (equal (cadar asst) *some-non-nil-value*))
        (and (null (cadar asst)) (equal val *some-non-nil-value*))
        (falsifying-pair-p term val (cdr asst))))
   (t nil)))

(defun bogus-falsifying-assignment-var (asst)

; Asst is assumed to be sorted by car.

  (cond
   ((endp asst) nil)
   ((falsifying-pair-p (caar asst) (cadar asst) (cdr asst))
    (caar asst))
   (t
    (bogus-falsifying-assignment-var (cdr asst)))))

(defun show-falsifying-assignment (query-response bddnote chan state)
  (let ((cst (access bddnote bddnote :cst)))
    (cond
     ((cst-tp cst)
      (fms "There is no falsifying assignment, since ~@0 was proved."
           (list (cons #\0 (tilde-@-clause-id-phrase
                            (access bddnote bddnote :cl-id))))
           chan state nil))
     (t
      (let ((asst (falsifying-assignment
                   cst
                   (access bddnote bddnote :mx-id))))
        (pprogn (let ((var (bogus-falsifying-assignment-var
                            (merge-sort-car-term-order asst))))
                  (cond (var (fms "WARNING:  The term ~p0 is assigned both to ~
                                   nil and a non-nil value in the following ~
                                   assignment.  This generally occurs because ~
                                   the term is not known to be Boolean.  ~
                                   Consider adding appropriate booleanp or ~
                                   boolean-listp hypotheses. See :DOC ~
                                   bdd-introduction."
                                  (list (cons #\0 var))
                                  (standard-co state) state
                                  (evisc-tuple 5 7 nil nil)))
                        (t state)))
                (fms "Falsifying constraints:~%"
                     nil chan state nil)
                (cond
                 (query-response
                  state)
                 (t
                  (fms "~x0~|"
                       (list (cons #\0 asst))
                       chan state
                       (evisc-tuple 5 (max 7 (length asst)) nil nil))))
                (cond
                 ((equal asst
                         (eviscerate-simple
                          asst 5 (max 7 (length asst)) nil
                          (table-alist 'evisc-table (w state))
                          nil))
                  state)
                 (t
                  (mv-let
                   (erp ans state)
                   (if query-response
                       (let ((query-response
                              (intern (symbol-name query-response) "KEYWORD")))
                         (value (case query-response
                                      (:w :w)
                                      (:nil nil)
                                      (otherwise t))))
                     (acl2-query
                      :show-bdd
                      '("Print the falsifying constraints in full?"
                        :n nil :y t :w :w
                        :? ("Y will print the constraints in full.  W will put ~
                             you in a structural display editor that lets you ~
                             type a positive integer N to dive to the Nth ~
                             element of the current list, 0 to go up a level, ~
                             PP to print the current object in full, and Q to ~
                             quit."
                            :n nil :y t :w :w))
                      nil
                      state))
                   (declare (ignore erp))
                   (cond ((eq ans :w)
                          (mv-let (erp ans state)
                                  (walkabout asst state)
                                  (declare (ignore erp ans))
                                  state))
                         (ans (fms "~x0~|"
                                   (list (cons #\0 asst))
                                   chan state nil))
                         (t state)))))))))))

(defun show-bdd-term (query-response bddnote chan state)
  (let* ((orig-term (access bddnote bddnote :term))
         (term (if orig-term
                   orig-term
                 (mv-let (term cst-array)
                         (decode-cst (access bddnote bddnote
                                             :cst)
                                     (leaf-cst-list-array
                                      (access bddnote bddnote
                                              :mx-id)))
                         (declare (ignore cst-array))
                         term))))
    (pprogn
     (cond ((null orig-term)
            (f-put-global 'bddnotes
                          (update-bddnote-with-term
                           (access bddnote bddnote :cl-id)
                           term
                           (f-get-global 'bddnotes state))
                          state))
           (t state))
     (fms "Term obtained from BDD computation on ~@1:~|"
          (list (cons #\1 (tilde-@-clause-id-phrase
                           (access bddnote bddnote :cl-id))))
          (standard-co state) state nil)
     (cond
      (query-response
       state)
      (t
       (fms "~x2~|"
            (list (cons #\2 term))
            (standard-co state) state (evisc-tuple 5 7 nil nil))))
     (cond
      ((equal term (eviscerate-simple term 5 7 nil
                                      (table-alist 'evisc-table (w state))
                                      nil))
       state)
      (t
       (mv-let (erp ans state)
               (if query-response
                   (let ((query-response
                          (intern (symbol-name query-response) "KEYWORD")))
                     (value (case query-response
                                  (:w :w)
                                  (:nil nil)
                                  (otherwise t))))
                 (acl2-query
                  :show-bdd
                  '("Print the term in full?"
                    :n nil :y t :w :w
                    :? ("Y will print the term in full.  W will put you in a ~
                         structural display editor that lets you type a ~
                         positive integer N to dive to the Nth element of the ~
                         current list, 0 to go up a level, PP to print the ~
                         current object in full, and Q to quit."
                        :n nil :y t :w :w))
                  nil
                  state))
               (declare (ignore erp))
               (cond ((eq ans :w)
                      (mv-let (erp ans state)
                              (walkabout term state)
                              (declare (ignore erp ans))
                              state))
                     (ans (fms "~x0~|"
                               (list (cons #\0 term))
                               chan state nil))
                     (t state))))))))

(defun tilde-*-substitution-phrase1 (alist is-replaced-by-str evisc-tuple wrld)
  (cond ((null alist) nil)
        (t (cons (msg "~P01 ~s2 ~P31"
                      (untranslate (caar alist) nil wrld)
                      evisc-tuple
                      is-replaced-by-str
                      (untranslate (cdar alist) nil wrld))
                 (tilde-*-substitution-phrase1 (cdr alist)
                                               is-replaced-by-str
                                               evisc-tuple wrld)))))

(defun tilde-*-substitution-phrase (alist is-replaced-by-str evisc-tuple wrld)
  (list* "" "~@*" "~@* and " "~@*, "
         (tilde-*-substitution-phrase1 alist is-replaced-by-str evisc-tuple
                                       wrld)
         nil))

(defun show-bdd-backtrace (call-stack cst-array chan state)
  (cond
   ((endp call-stack)
    state)
   (t (mv-let
       (term-list cst-array)
       (decode-cst-lst
        (strip-cdrs (cdar call-stack))
        cst-array)
       (let ((term (untranslate (caar call-stack) nil (w state)))
             (alist (pairlis$ (strip-cars (cdar call-stack))

; Once upon a time we untranslate term-list below, but
; tilde-*-substitution-phrase does an untranslate.

                              term-list)))
         (pprogn
          (fms "~X02~|  alist: ~*1~|"
               (list (cons #\0 term)
                     (cons #\1 (tilde-*-substitution-phrase
                                alist
                                ":="
                                (evisc-tuple 5 (max 7 (length alist))
                                             nil nil)
                                (w state)))
                     (cons #\2 (evisc-tuple 5 7 nil nil)))
               chan state nil)
          (show-bdd-backtrace (cdr call-stack) cst-array chan state)))))))

(defun show-bdd-fn (str goal-query-response
                        counterex-query-response
                        term-query-response
                        state)
  (let ((bddnotes (f-get-global 'bddnotes state))
        (cl-id (parse-clause-id str))
        (separator "==============================~%"))
    (cond
     ((and str (null cl-id))
      (er soft 'show-bdd
          "The string ~x0 does not have the syntax of a goal name.  See :DOC ~
           goal-spec."
          str))
     (t
      (let ((bddnote (if cl-id ;equivalently, if str
                         (lookup-bddnote cl-id bddnotes)
                       (car bddnotes)))
            (chan (standard-co state)))
        (cond
         ((null bddnote)
          (er soft 'show-bdd
              "There is no recent record of applying BDDs~#0~[~/ to ~s1~]."
              (if str 1 0)
              (if (eq str t) "Goal" str)))
         (t
          (pprogn
            (show-bdd-goal goal-query-response
                           bddnote chan state)
            (fms "~@0" (list (cons #\0 separator)) chan state nil)
            (fms "BDD computation on ~@0 yielded ~x1 nodes.~|~@2"
                (list (cons #\0 (tilde-@-clause-id-phrase
                                 (access bddnote bddnote :cl-id)))
                      (cons #\1 (access bddnote bddnote :mx-id))
                      (cons #\2 separator))
                chan state nil)
            (cond
             ((access bddnote bddnote :err-string)
              (pprogn (fms
                       "BDD computation was aborted on ~@0, and hence there is ~
                        no falsifying assignment that can be constructed.  ~
                        Here is a backtrace of calls, starting with the ~
                        top-level call and ending with the one that led to the ~
                        abort.  See :DOC show-bdd.~|"
                       (list (cons #\0 (tilde-@-clause-id-phrase
                                        (access bddnote bddnote :cl-id))))
                       chan state nil)
                      (show-bdd-backtrace (access bddnote bddnote
                                                  :bdd-call-stack)

; Note that we will probably be building the same array as the one just below
; for show-bdd-term, but that seems a small price to pay for modularity here.

                                          (leaf-cst-list-array
                                           (access bddnote bddnote :mx-id))
                                          chan state)
                      (value :invisible)))
             (t (pprogn (show-falsifying-assignment counterex-query-response
                                                    bddnote chan state)
                        (fms "~@0" (list (cons #\0 separator)) chan state nil)
                        (show-bdd-term term-query-response bddnote chan state)
                        (value :invisible))))))))))))

(defun get-docs (lst)

; Each element of lst is a 5-tuple (name args doc edcls body).  We
; return a list in 1:1 correspondence with lst containing the docs
; (each of which is either a stringp or nil).

  (cond ((null lst) nil)
        (t (cons (third (car lst))
                 (get-docs (cdr lst))))))

; Rockwell Addition:  Now when you declare a fn to traffic in the stobj st
; the guard is automatically extended with a (stp st).

; Get-guards2, get-guards1, and get-guards were previously defined here, but
; are now introduced earlier to support the definition of ev-fncall-rec-logical
; (specifically, the definition of guard-raw, which is called by
; ev-fncall-guard-er, which in turn is called by ev-fncall-rec-logical).

(defun get-guardsp (lst wrld)

; Note that get-guards always returns a list of untranslated terms as long as
; lst and that if a guard is not specified (via either a :GUARD or :STOBJS XARG
; declaration or a TYPE declaration) then *t* is used.  But in order to default
; the verify-guards flag in defuns we must be able to decide whether no such
; declaration was specified.  That is the role of this function.  It returns t
; or nil according to whether at least one of the 5-tuples in lst specifies a
; guard (or stobj) or a type.

; Thus, specification of a type is sufficient for this function to return t,
; even if :split-types t was specified.  If that changes, adjust :doc
; set-verify-guards-eagerness accordingly.

  (cond ((null lst) nil)
        ((get-guards1 (fourth (car lst)) '(guards types)
                      nil nil ; any implicit state-p call is irrelevant here
                      wrld)
         t)
        (t (get-guardsp (cdr lst) wrld))))

(defconst *no-measure*

; We expect this to be a term, in particular because of the call of
; chk-free-vars on the measure in chk-free-and-ignored-vars.  If this value is
; changed to a term other than *nil*, consider updating documentation for defun
; and xargs, which explain that :measure nil is treated as though :measure was
; omitted.

  *nil*)

(defun get-measures1 (m edcls ctx state)

; A typical edcls is given above, in the comment for get-guards.  Note that the
; :MEASURE entry is found in an XARGS declaration.  By the check in chk-dcl-lst
; we know there is at most one :MEASURE entry in each XARGS declaration.  But
; there may be more than one declaration.  If more than one measure is
; specified by this edcls, we'll cause an error.  Otherwise, we return the
; measure or the term *no-measure*, which is taken as a signal that no measure
; was specified.

; Our first argument, m, is the measure term found so far, or *no-measure* if
; none has been found.  We map down edcls and ensure that each XARGS either
; says nothing about :MEASURE or specifies m.

  (cond ((null edcls) (value m))
        ((eq (caar edcls) 'xargs)
         (let ((temp (assoc-keyword :MEASURE (cdar edcls))))
           (cond ((null temp)
                  (get-measures1 m (cdr edcls) ctx state))
                 ((equal m *no-measure*)
                  (get-measures1 (cadr temp) (cdr edcls) ctx state))
                 ((equal m (cadr temp))
                  (get-measures1 m (cdr edcls) ctx state))
                 (t (er soft ctx
                        "It is illegal to declare two different ~
                         measures for the admission of a single ~
                         function.  But you have specified :MEASURE ~
                         ~x0 and :MEASURE ~x1."
                        m (cadr temp))))))
        (t (get-measures1 m (cdr edcls) ctx state))))

(defun get-measures2 (lst ctx state)
  (cond ((null lst) (value nil))
        (t (er-let* ((m (get-measures1 *no-measure* (fourth (car lst)) ctx
                                       state))
                     (rst (get-measures2 (cdr lst) ctx state)))
                    (value (cons m rst))))))


(defun get-measures (lst ctx state)

; This function returns a list in 1:1 correspondence with lst containing the
; user's specified :MEASUREs (or *no-measure* if no measure is specified).  We
; cause an error if more than one :MEASURE is specified within the edcls of a
; given element of lst.

  (get-measures2 lst ctx state))

(defconst *no-ruler-extenders*
  :none)

(defconst *basic-ruler-extenders*

; We ensure that these are sorted, although this may no longer be important.

  (let ((lst '(if mv-list return-last)))
    (sort-symbol-listp lst)))

(defconst *basic-ruler-extenders-plus-lambdas*

; We ensure that these are sorted, although this may no longer be important.

  (let ((lst (cons :lambdas *basic-ruler-extenders*)))
    (sort-symbol-listp lst)))

(defun get-ruler-extenders1 (r edcls default ctx wrld state)

; This function is analogous to get-measures1, but for obtaining the
; :ruler-extenders xarg.

  (cond ((null edcls) (value (if (eq r *no-ruler-extenders*)
                                 default
                               r)))
        ((eq (caar edcls) 'xargs)
         (let ((temp (assoc-keyword :RULER-EXTENDERS (cdar edcls))))
           (cond ((null temp)
                  (get-ruler-extenders1 r (cdr edcls) default ctx wrld state))
                 (t
                  (let ((r0 (cadr temp)))
                    (cond
                     ((eq r *no-ruler-extenders*)
                      (er-let*
                       ((r1

; If keywords other than :ALL, :BASIC, and :LAMBDAS are supported, then also
; change set-ruler-extenders.

                         (cond ((eq r0 :BASIC)
                                (value *basic-ruler-extenders*))
                               ((eq r0 :LAMBDAS)
                                (value *basic-ruler-extenders-plus-lambdas*))
                               ((eq r0 :ALL)
                                (value :ALL))
                               (t (er-progn
                                   (chk-ruler-extenders r0 soft ctx wrld)
                                   (value r0))))))
                       (get-ruler-extenders1 r1 (cdr edcls) default ctx
                                             wrld state)))
                     ((equal r r0)
                      (get-ruler-extenders1 r (cdr edcls) default ctx wrld
                                            state))
                     (t (er soft ctx
                            "It is illegal to declare two different ~
                             ruler-extenders for the admission of a single ~
                             function.  But you have specified ~
                             :RULER-EXTENDERS ~x0 and :RULER-EXTENDERS ~x1."
                            r r0))))))))
        (t (get-ruler-extenders1 r (cdr edcls) default ctx wrld state))))

(defun get-ruler-extenders2 (lst default ctx wrld state)
  (cond ((null lst) (value nil))
        (t (er-let* ((r (get-ruler-extenders1
                         *no-ruler-extenders* (fourth (car lst)) default ctx
                         wrld state))
                     (rst (get-ruler-extenders2 (cdr lst) default ctx wrld
                                                state)))
                    (value (cons r rst))))))

(defmacro default-ruler-extenders-from-table (alist)
  `(let ((pair (assoc-eq :ruler-extenders ,alist)))
     (cond ((null pair)
            *basic-ruler-extenders*)
           (t (cdr pair)))))

(defun default-ruler-extenders (wrld)
  (default-ruler-extenders-from-table (table-alist 'acl2-defaults-table wrld)))

(defun get-ruler-extenders-lst (symbol-class lst ctx wrld state)

; This function returns a list in 1:1 correspondence with lst containing the
; user's specified :RULER-EXTENDERS (or *no-ruler-extenders* if no
; ruler-extenders is specified).  We cause an error if more than one
; :RULER-EXTENDERS is specified within the edcls of a given element of lst.

; If symbol-class is program, we ignore the contents of lst and simply return
; all *no-ruler-extenders*.  See the comment in chk-acceptable-defuns where
; get-ruler-extenders is called.

  (cond
   ((eq symbol-class :program)
    (value (make-list (length lst) :initial-element *no-ruler-extenders*)))
   (t (get-ruler-extenders2 lst (default-ruler-extenders wrld) ctx wrld
                            state))))

(defun get-hints1 (edcls)

; A typical edcls might be

; '((IGNORE X Y)
;   (XARGS :GUARD g1 :MEASURE m1 :HINTS ((id :USE ... :IN-THEORY ...)))
;   (TYPE ...)
;   (XARGS :GUARD g2 :MEASURE m2))

; We find all the :HINTS and append them together.

  (cond ((null edcls) nil)
        ((eq (caar edcls) 'xargs)

; We know there is at most one occurrence of :HINTS in this XARGS entry.

         (let ((temp (assoc-keyword :HINTS (cdar edcls))))
           (cond ((null temp) (get-hints1 (cdr edcls)))
                 ((true-listp (cadr temp))
                  (append (cadr temp) (get-hints1 (cdr edcls))))
                 (t (er hard 'get-hints
                        "The value of :HINTS must satisfy the predicate ~x0.  ~
                         The value ~x1 is thus illegal.  See :DOC hints."
                        'true-listp
                        (cadr temp))))))
        (t (get-hints1 (cdr edcls)))))

(defun get-hints (lst)

; Lst is a list of tuples of the form (name args doc edcls body).  We
; scan the edcls in each tuple and collect all of the hints together
; into one list of hints.

  (cond ((null lst) nil)
        (t (append (get-hints1 (fourth (car lst)))
                   (get-hints (cdr lst))))))

(defun get-guard-hints1 (edcls)

; A typical edcls might be

; '((IGNORE X Y)
;   (XARGS :GUARD g1 :MEASURE m1 :GUARD-HINTS ((id :USE ... :IN-THEORY ...)))
;   (TYPE ...)
;   (XARGS :GUARD g2 :MEASURE m2))

; We find all the :GUARD-HINTS and append them together.

  (cond ((null edcls) nil)
        ((eq (caar edcls) 'xargs)

; We know there is at most one occurrence of :GUARD-HINTS in this
; XARGS entry.

         (let ((temp (assoc-keyword :GUARD-HINTS (cdar edcls))))
           (cond ((null temp) (get-guard-hints1 (cdr edcls)))
                 ((true-listp (cadr temp))
                  (append (cadr temp) (get-guard-hints1 (cdr edcls))))
                 (t (er hard 'get-guard-hints
                        "The value of :GUARD-HINTS must satisfy the predicate ~
                         ~x0.  The value ~x1 is thus illegal.  See :DOC hints."
                        'true-listp
                        (cadr temp))))))
        (t (get-guard-hints1 (cdr edcls)))))

(defun get-guard-hints (lst)

; Lst is a list of tuples of the form (name args doc edcls body).  We
; scan the edcls in each tuple and collect all of the guard-hints together
; into one list of hints.

  (cond ((null lst) nil)
        (t (append (get-guard-hints1 (fourth (car lst)))
                   (get-guard-hints (cdr lst))))))

#+:non-standard-analysis
(defun get-std-hints1 (edcls)

; A typical edcls might be

; '((IGNORE X Y)
;   (XARGS :STD-HINTS ((id :USE ... :IN-THEORY ...)))
;   (TYPE ...)
;   (XARGS :GUARD g2 :MEASURE m2))

; We find all the :STD-HINTS and append them together.

  (cond ((null edcls) nil)
        ((eq (caar edcls) 'xargs)

; We know there is at most one occurrence of :STD-HINTS in this
; XARGS entry.

         (let ((temp (assoc-keyword :STD-HINTS (cdar edcls))))
           (cond ((null temp) (get-std-hints1 (cdr edcls)))
                 ((true-listp (cadr temp))
                  (append (cadr temp) (get-std-hints1 (cdr edcls))))
                 (t (er hard 'get-std-hints
                        "The value of :STD-HINTS must satisfy the predicate ~
                         ~x0.  The value ~x1 is thus illegal.  See :DOC hints."
                        'true-listp
                        (cadr temp))))))
        (t (get-std-hints1 (cdr edcls)))))

#+:non-standard-analysis
(defun get-std-hints (lst)

; Lst is a list of tuples of the form (name args doc edcls body).  We
; scan the edcls in each tuple and collect all of the std-hints together
; into one list of hints.

  (cond ((null lst) nil)
        (t (append (get-std-hints1 (fourth (car lst)))
                   (get-std-hints (cdr lst))))))

(defun get-normalizep (edcls ans ctx state)

; A typical edcls might be

; '((IGNORE X Y)
;   (XARGS :GUARD g1 :MEASURE m1 :HINTS ((id :USE ... :IN-THEORY ...)))
;   (TYPE ...)
;   (XARGS :GUARD g2 :MEASURE m2))

; We find the first :NORMALIZE, if there is one.  But we check that there is
; not more than one.

  (cond ((null edcls)
         (value (if (eq ans :absent)
                    t ; default
                  ans)))
        ((eq (caar edcls) 'xargs)

; We know there is at most one occurrence of :NORMALIZE in this XARGS entry,
; but we are concerned about the possibility of other XARGS entries (from other
; declare forms).  Perhaps we should be concerned in other cases too, e.g.,
; :HINTS.

         (let ((temp (assoc-keyword :NORMALIZE (cdar edcls))))
           (cond
            ((null temp)
             (get-normalizep (cdr edcls) ans ctx state))
            ((not (member-eq (cadr temp) '(t nil)))
             (er soft ctx
                 "The :NORMALIZE keyword specified by XARGS must have value t ~
                  or nil, but the following has been supplied: ~p0."
                 (cadr temp)))
            ((eq ans :absent)
             (get-normalizep (cdr edcls) (cadr temp) ctx state))
            (t
             (er soft ctx
                 "Only one :NORMALIZE keyword may be specified by XARGS.")))))
        (t (get-normalizep (cdr edcls) ans ctx state))))

(defun get-normalizeps (lst acc ctx state)

; Lst is a list of tuples of the form (name args doc edcls body).  We
; scan the edcls in each tuple and collect all of the normalizeps together
; into one list, checking that each is Boolean.

  (cond ((null lst) (value (reverse acc)))
        (t (er-let* ((normalizep (get-normalizep (fourth (car lst)) :absent
                                                 ctx state)))
             (get-normalizeps (cdr lst) (cons normalizep acc) ctx state)))))

; The definition of get-unambiguous-xargs-flg1/edcls1 and related events were
; previously introduced here, but have been moved earlier to support the
; definition of ev-fncall-rec-logical (specifically, the definition of
; guard-raw, which is called by ev-fncall-guard-er, which in turn is called by
; ev-fncall-rec-logical).

(defun chk-xargs-keywords1 (edcls keywords ctx state)
  (cond ((null edcls) (value nil))
        ((eq (caar edcls) 'xargs)
         (cond ((null keywords)
                (er soft ctx
                    "No XARGS declaration is legal in this context."))
               ((subsetp-eq (evens (cdar edcls)) keywords)
                (chk-xargs-keywords1 (cdr edcls) keywords ctx state))
               (t (er soft ctx
                      "The only acceptable XARGS keyword~#0~[ in this ~
                       context is~/s in this context are~] ~&0.  Thus, ~
                       the keyword~#1~[ ~&1 is~/s ~&1 are~] illegal."
                      keywords
                      (set-difference-eq (evens (cdar edcls))
                                         keywords)))))
        (t (chk-xargs-keywords1 (cdr edcls) keywords ctx state))))

(defun chk-xargs-keywords (lst keywords ctx state)

; Lst is a list of 5-tuples of the form (name args doc edcls body).  The
; edcls contain XARGS keyword lists, e.g., a typical edcls might be

; '((IGNORE X Y)
;   (XARGS :GUARD g1 :MEASURE m1 :HINTS ((id :USE ... :IN-THEORY ...)))
;   (TYPE ...)
;   (XARGS :GUARD g2 :MEASURE m2))

; We check that the only keywords mentioned in the list are those of
; keywords.  We once put this check into translate itself, when it
; was producing the edcls.  But the keywords allowed by DEFUN are
; different from those allowed by DEFMACRO, and so we've moved this
; check into the specific event file.

  (cond
   ((null lst) (value nil))
   (t (er-progn (chk-xargs-keywords1 (fourth (car lst)) keywords ctx state)
                (chk-xargs-keywords (cdr lst) keywords ctx state)))))

(defun get-names (lst)
  (cond ((null lst) nil)
        (t (cons (caar lst)
                 (get-names (cdr lst))))))

(defun get-bodies (lst)
  (cond ((null lst) nil)
        (t (cons (fifth (car lst))
                 (get-bodies (cdr lst))))))

; Essay on the Shift from Governors to Rulers

; Why did we shift from governors to rulers?  Unfortunately, as far as we can
; tell (as of Version_8.0), we did not document this decision very well. ACL2
; has used rulers for a long time.  The notion of ``ruler'' is present in the
; definition of termination-machine in ACL2 Version_1.9, from Fall, 1996.  We
; do not have earlier versions of the sources to compare.  The notion of
; ruler-extenders was evidently introduced in Version_3.5 (see Note-3-5),
; May, 2009, as there is no mention of ``ruler'' in any earlier release note.

; By the way, it might be of interest to note that Example 11 in the book
; books/misc/misc2/ruler-extenders-tests.lisp shows a function for which the
; induction machine generated before Version_3.5 was heuristically inadequate
; because it did not provide an induction hypothesis that it should have.
; This bug was fixed when :ruler-extenders were added.

; Returning to the reason for shifting from governors to rulers, the comment
; in the v1-9 definition of termination-machine, which may still be found in
; v8-0, reads in part:

;  The reason for taking this weaker notion of governance is that we
;  can show easily that the tests-and-calls are together sufficient to
;  imply the tests-and-calls generated by induction-machine.

; This comment is supported by our discussion of ``rulers'' in Computer-Aided
; Reasoning: An Approach, by Kaufmann, Manolios, and Moore, Kluwer, 2000.  On
; page 90 footnote 5 explains that in the expression:

; (if p (if (q (if x y z)) u v) w)

; we do not consider x a ruler of y or (NOT x) a ruler of z, because of ``the
; induction scheme we prefer to generate from such definitions.''  For what
; it is worth, ``governors'' is not mentioned in the book nor does the book
; elaborate on the ``induction scheme we prefer.''

; This decision to abandon governs and focus on rulers deserves elaboration.
; In the following we refer to the :basic ruler-extenders (which as of v8-0 is
; (MV-LIST RETURN-LAST)), as the ``basic'' or ``conventional'' ruler-extenders
; and that is used implicitly unless otherwise noted.

; The termination machine for:

; (defun h (x y)
;   (if (endp x)
;       nil
;       (let ((val (h (cdr x) y)))
;         (if y
;             (cons 1 val)
;             (cons 2 val)))))

; is

; ((TESTS-AND-CALL ((NOT (ENDP X)))
;                  (H (CDR X) Y)))

; which means that to admit h we must prove that some measure of (CDR X) and
; Y is smaller than the same measure of X and Y, when (NOT (ENDP X)).

; The induction machine for h is:

; ((TESTS-AND-CALLS ((ENDP X)))                ; base case
;  (TESTS-AND-CALLS ((NOT (ENDP X)) Y)         ; induction step 1
;                   (H (CDR X) Y))
;  (TESTS-AND-CALLS ((NOT (ENDP X)) (NOT Y))   ; induction step 2
;                   (H (CDR X) Y)))

; [Minor note: The termination machine has one call per item while the
; induction machine, in general, has multiple calls per item.  Note the names
; of the records: TESTS-AND-CALL versus TESTS-AND-CALLS.  But this is not
; apparent in this example because each item in the induction machine above
; shows only one call.]

; The calls of h in the induction steps implicitly represent substitutions to
; form the induction hypotheses.  In this case both substitutions are {X <--
; (CDR X), Y <-- Y}.  To be legal we need to know that some measure goes down
; under each of these substitutions, when the indicated tests are true.
; Obviously, the appropriate measure is that used to admit h.

; But note that the induction machine may include additional tests so as to
; split out the cases with suitable induction hypotheses.  While the
; termination machine just tests (NOT (ENDP X)), the induction machine
; encodes two induction steps, one testing (NOT (ENDP X)) and Y and the other
; testing (NOT (ENDP X)) and (NOT Y).  But it is easy to see that the measure
; used for the admission of h works here.

; Note that the termination machine really cannot afford to look inside the LET
; (i.e., the LAMBDA expression to which (h (cdr x) y) is supplied as an actual)
; to see how val is used.  (It must look inside the LET for additional
; recursive calls of h!)  If termination is to mean termination when evaluated
; by Common Lisp's call-by-value interpreter, the call of h in the actual to
; that LAMBDA must decrease the measure regardless of what happens to the
; resulting value inside the body of the LAMBDA.  (Imagine that the LET
; sometimes uses val and sometimes doesn't and that the ``improved''
; termination machine only proved that the measure goes down on branches
; use val.  Then the call of h in the actuals might not terminate.)

; In any case, the termination machine was apparently driven by the desire to
; guarantee that the evaluation by Common Lisp will always terminate.  The
; induction machine is a little freer to use a different case analysis so as to
; ``optimize'' the provision of induction hypotheses.

; It is possible that we introduced rulers to deal with LET in a way consistent
; with Common Lisp's evaluation model.  Nqthm supported LET only as an
; abbreviation for the term obtained by substituting the translated bindings
; for the local vars in the translated body of the LET.  Thus, Nqthm's
; evaluation semantics for LET were not Common Lisp's.  But this possibility is
; just raised speculatively.

; The adoption of rulers also gives the user some heuristic control for both
; termination machines and induction machines.  By lifting IFs out or pushing
; them down into calls of other functions one can control which tests ACL2
; considers crucial.  We give two examples.

; (1) The measure that ACL2 guesses (when the user fails to provide one) is
; the ACL2-COUNT of (informally) the first formal that is tested on every
; branch leading to a recursion and changed in recursion.  But by ``tested''
; we mean ``tested in the termination machine,'' i.e., we mean the formal is
; involved in a ruling term.  One can imagine that if we allowed additional
; tests to make it into the termination machine we might confuse the measure
; guessing heuristic.  Indeed, this happens in the regression.

; If one changes the ACL2 source code so that default-ruler-extenders is :all,
; then we can get more tests in the termination machines.  A regression will
; then fail to guess the right measure on

; (DEFUN QUICK-ORDER (PIVOT LIST)
;   (DECLARE (XARGS :GUARD (AND (SYMBOL-LISTP LIST)
;                               (SYMBOLP PIVOT))
;                    :VERIFY-GUARDS NIL))
;   (IF
;    (CONSP LIST)
;    (MV-LET
;      (LESS MORE)
;      (SEPARATE PIVOT LIST NIL NIL)
;      (LET ((NEW-LESS (IF (CONSP LESS)
;                          (IF (CONSP (CDR LESS))
;                              (QUICK-ORDER (CAR LESS) (CDR LESS))
;                              (LIST (CAR LESS)))
;                          NIL))
;            (NEW-MORE (IF (CONSP MORE)
;                          (IF (CONSP (CDR MORE))
;                              (CONS PIVOT
;                                    (QUICK-ORDER (CAR MORE) (CDR MORE)))
;                              (CONS PIVOT (LIST (CAR MORE))))
;                          (LIST PIVOT))))
;        (APPEND NEW-LESS NEW-MORE)))
;    NIL))

; in the book books/projects/taspi/code/tree-manip/quicksort.lisp.

; With our conventional notion of ruler-extenders the system correctly guesses
; (ACL2-COUNT LIST), because (CONSP LIST) is the only ruler and LIST is changed
; in recursion.  But with :ALL, it guesses (ACL2-COUNT PIVOT) because PIVOT
; occurs before LIST in the formals and is tested (as part of the inspection of
; LESS and MORE which are computed in terms of PIVOT) in the more expansive
; termination machine.  PIVOT is not tested in the conventional machine.
; Indeed, it is hard to imagine rewriting this definition in a way that tests
; PIVOT as a ruler in the conventional machine because that would require
; avoiding the LET and computing LESS and MORE with two separate calls of
; SEPARATE.  This example benefits from our conventional interpretion of
; ``rulers''.

; (2) During proof attempts the pre-computed induction machines are
; instantiated to get suggested inductions and then we run various heuristics
; (e.g., induction subsumption, flawing and merging) to manipulate the
; candidates to throw out some and create a preferred candidate by sometimes
; combining others.  The simpler the machines are the more sensible these
; manipulations are.  That is an odd remark because we, of course, believe
; that the manipulations are sound no matter how complicated the candidates
; are.  But we believe the heuristics lead to ``appropriate'' inductions more
; often for simpler candidates.  For example, if two candidates have
; irrelevant tests then they might not merge to create the ``appropriate''
; induction.

; This is a second-order effect since we are dealing now with induction
; machines not termination machines.  (Recall that the computation of an
; induction machine is free to add additional tests, including irrelevant
; ones.  But the induction machine must at least include the rulers and so
; having fewer rulers supports having fewer tests in induction machines.)

; The following extremely contrived example shows that it is possible to trick
; ACL2 into guessing the wrong induction by using the induction machines
; produced by ruler-extenders :all.  But two points deserve to be highlighted:
; (1) What's new?  It's virtually always possible to trick ACL2 into doing the
; wrong thing! (2) We have no evidence that a failure of the type described
; below would happen in the regression if we adopted a more generous notion of
; ruler.

; In the following script, r1 and r2 are defined identically except for their
; names.  So too are q1 and q2.  However, while r1 and q1 are processed with
; the conventional ruler-extenders, r2 and q2 are processed with
; :ruler-extenders :all.  Thus, r1 and r2 are equivalent recursive functions
; but have different induction machines; an analogous relationship holds for q1
; and q2.  Furthermore, r2's induction machine has a test that q2's does not
; and vice versa.  The induction suggested by q1 is subsumed by that suggested
; by r1.  But, because of the additional tests in each, the induction suggested
; by q2 is not subsumed by that for r2, or vice versa.  Furthermore, q2's
; induction cannot be merged into r2's nor vice versa.  In fact, r2 and q2 flaw
; each other.  (Indeed, if there is anything odd about this contrived example
; it is that it's possible to define a q whose induction is subsumed but flawed
; by that of r!)  So if you have a theorem involving both r1 and q1 then the q1
; induction is subsumed into the r1 induction and thus doubles the score,
; whereas if the theorem involves r2 and q2, neither subsumption nor merging
; happen and each maintains its original score.  Finally, if we involve a third
; function, p, in the conjecture we can arrange for it to suggest an
; inappropriate induction and for that inappropriate induction to be chosen
; when r2 and q2 are not combined to create a clear winner.  [This example was
; difficult to work out.]

; The end result is that we demonstrate a theorem for which we choose the
; ``right'' induction if the machines are built with the conventional
; ruler-extenders and the ``wrong'' induction if they're built with
; ruler-extenders :all.

; (defstub irrel-r-test (x) t)
; (defstub irrel-q-test (x) t)

; We form our theorem with H, below, and use it to Hold together the calls of
; p, q, and r.  We arrange for H to be provable if the last argument is reduced
; to T and we arrange for it to be not provable, by the available rules, if the
; wrong induction is done.  Of course, the ``not provable'' theorem can be
; proved by the right induction.

; (encapsulate ((H (p q r) t)
;               (blocker (p q r) t))
;   (local
;    (defun H (p q r)
;      (declare (ignore p q))
;      r))

;   (local
;    (defun blocker (p q r)
;      (declare (ignore p q))
;      r))

;   (defthm H-prop
;     (implies r (equal (H p q r) r)))

;   (defthm H-blocker
;     (implies (syntaxp (equal p 'z)) ; designed to shut down wrong induction
;              (equal (H p q r) (blocker p q r)))))

; Note that r1 and r2, defined below, are identical modulo their names.

; (defun r1 (x y) ; Simple inductive truth.
;   (if (endp x)
;       (equal y (cdr (cons x y))) ; hidden T
;       (identity
;        (if (irrel-r-test y)
;            (or (r1 (cdr x) (identity y))
;                (r1 (cdr x) y))
;            t))))

; (defun r2 (x y) ; Simple inductive truth.
;   (declare (xargs :ruler-extenders :all))
;   (if (endp x)
;       (equal y (cdr (cons x y))) ; hidden T
;       (identity
;        (if (irrel-r-test y)
;            (or (r2 (cdr x) (identity y))
;                (r2 (cdr x) y))
;            t))))

; Analogously, q1 and q2 are identical modulo their names.

; (defun q1 (x y) ; Subsumed by r1
;   (if (endp x)
;       (equal y (cdr (cons x y))) ; hidden T
;       (identity
;        (if (irrel-q-test y)
;            (q1 (cdr x) (identity y))
;            t))))

; (defun q2 (x y) ; Not Subsumed or mergeable with r2
;   (declare (xargs :ruler-extenders :all))
;   (if (endp x)
;       (equal y (cdr (cons x y))) ; hidden T
;       (identity
;        (if (irrel-q-test y)
;            (q2 (cdr x) (identity y))
;            t))))

; (defun p (z) ; Value is irrelevant.  This just suggests an inappropriate
;              ; induction for our goal theorem.
;   (if (endp z)
;       z
;       (p (cdr z))))

; (thm (h (p z) (q1 x y) (r1 x y)))

; The above succeeds and the explanation of the induction selection reads:

;  Perhaps we can prove *1 by induction.  Three induction schemes are
;  suggested by this conjecture.  Subsumption reduces that number to two.
;  One of these has a score higher than the other.

;  We will induct according to a scheme suggested by (R1 X Y).

; In particular, the q1 suggestion is subsumed by the r1 suggestion, increasing
; the score of the r1 suggestion.  Trace flush-cand1-down-cand2 to see the
; subsumption.

; But the version of that theorem using the induction machines produced with
; ruler-extenders :all fails!

; (thm (h (p z) (q2 x y) (r2 x y)))

; The explanation of the induction selection reads:

;  Perhaps we can prove *1 by induction.  Three induction schemes are
;  suggested by this conjecture.  However, two of these are flawed and
;  so we are left with one viable candidate.

;  We will induct according to a scheme suggested by (P Z).

; Note that no subsumption or merging happens, each candidate has a score of 1,
; but the q2 and r2 inductions flaw one another leaving the inappropriate p
; induction as the only choice.

(mutual-recursion

(defun find-nontrivial-rulers (var term)

; Returns a non-empty list of rulers governing an occurrence of var in term, if
; such exists.  Otherwise returns :none if var occurs in term and nil if var
; does not occur in term.

  (cond ((variablep term)
         (if (eq var term) :none nil))
        ((fquotep term)
         nil)
        ((eq (ffn-symb term) 'if)
         (let ((x (find-nontrivial-rulers var (fargn term 2))))
           (cond (x (cons (fargn term 1)
                          (if (eq x :none)
                              nil
                            x)))
                 (t (let ((x (find-nontrivial-rulers var (fargn term 3))))
                      (cond (x (cons (dumb-negate-lit (fargn term 1))
                                     (if (eq x :none)
                                         nil
                                       x)))
                            (t
                             (find-nontrivial-rulers var (fargn term 1)))))))))
        (t (find-nontrivial-rulers-lst var (fargs term) nil))))

(defun find-nontrivial-rulers-lst (var termlist flg)
  (cond ((endp termlist) flg)
        (t (let ((x (find-nontrivial-rulers var (car termlist))))
             (cond ((or (null x)
                        (eq x :none))
                    (find-nontrivial-rulers-lst var (cdr termlist) (or flg x)))
                   (t x))))))
)

(defun tilde-@-free-vars-phrase (vars term wrld)
  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-termp term)
                              (nvariablep term)
                              (not (fquotep term))
                              (plist-worldp wrld))))
  (cond ((endp vars) "")
        (t (let ((rulers (find-nontrivial-rulers (car vars) term)))
             (assert$
              rulers ; (car vars) occurs in term, so expect :none if no rulers
              (cond ((eq rulers :none)
                     (tilde-@-free-vars-phrase (cdr vars) term wrld))
                    ((null (cdr rulers))
                     (msg "  Note that ~x0 occurs in the context of condition ~
                           ~x1 from a surrounding IF test."
                          (car vars)
                          (untranslate (car rulers) t wrld)))
                    (t
                     (msg "  Note that ~x0 occurs in the following context, ~
                           i.e., governed by these conditions from ~
                           surrounding IF tests.~|~%  (AND~|~@1"
                          (car vars)
                          (print-indented-list-msg
                           (untranslate-lst rulers t wrld)
                           3
                           ")")))))))))

(defun chk-free-vars (name formals term loc-str ctx state)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-termp term))))
  (cond ((subsetp (all-vars term) formals) (value nil))
        ((variablep term)
         (er soft ctx
             "The ~@0 ~x1 is a free variable occurrence."
             loc-str name))
        (t (assert$
            (not (fquotep term))
            (let ((vars (set-difference-eq (all-vars term) formals)))
              (er soft ctx
                  "The ~@0 ~x1 contains ~#2~[a free occurrence of the ~
                   variable symbol~/free occurrences of the variable ~
                   symbols~] ~&2.~@3"
                  loc-str name
                  (set-difference-eq vars formals)
                  (tilde-@-free-vars-phrase vars term (w state))))))))

(defun chk-declared-ignores (name ignores term loc-str ctx state)
  (declare (xargs :guard (and (symbol-listp ignores)
                              (pseudo-termp term))))
  (cond ((intersectp-eq (all-vars term) ignores)
         (er soft ctx
             "The ~@0 ~x1 uses the variable symbol~#2~[~/s~] ~&2, ~
              contrary to the declaration that ~#2~[it is~/they are~] ~
              IGNOREd."
             loc-str name
             (reverse (intersection-eq (all-vars term) ignores))))
        (t (value nil))))

(defun chk-free-and-ignored-vars (name formals guard split-types-term measure
                                       ignores ignorables body ctx state)
  (er-progn
   (chk-free-vars name formals guard "guard for" ctx state)
   (chk-free-vars name formals split-types-term "split-types expression for"
                  ctx state)
   (chk-free-vars name formals measure "measure supplied with" ctx state)
   (chk-free-vars name formals (cons 'list ignores)
                  "list of variables declared IGNOREd in" ctx state)
   (chk-free-vars name formals (cons 'list ignorables)
                  "list of variables declared IGNORABLE in" ctx state)
   (chk-free-vars name formals body "body of" ctx state)

; Once upon a time we considered a variable used if it occurred in the
; guard or the measure of a function.  Thus, we signaled an error
; if it was declared ignored but used in the guard or measure.
; Now we don't.  Why?  Because this meant that one was not allowed to
; declare ignored a variable used only in (say) the guard.  But when
; the defun is compiled by Allegro, it would complain that the variable
; should have been declared ignored.  We simply are not free to give
; semantics to IGNORE.  CLTL does that and it only cares about the
; body.

   (chk-declared-ignores name ignores body "body of" ctx state)
   (let* ((ignore-ok (cdr (assoc-eq
                           :ignore-ok
                           (table-alist 'acl2-defaults-table (w state)))))
          (undeclared-ignores ; first conjunct is an optimization
           (cond ((or (eq ignore-ok t)
                      (and (not (eq ignore-ok nil))
                           (warning-disabled-p "Ignored-variables")))
                  nil)
                 (t (set-difference-eq
                     formals
                     (union-eq (all-vars body)
                               (union-eq ignorables ignores)))))))
     (cond ((and undeclared-ignores
                 (eq ignore-ok nil))
            (er soft ctx
                "The formal variable~#0~[ ~&0 is~/s ~&0 are~] not used in the ~
                 definition of ~x1 but ~#0~[is~/are~] not DECLAREd IGNOREd or ~
                 IGNORABLE.  Any formal variable not used in the body of a ~
                 definition must be so declared.  To remove this requirement, ~
                 see :DOC set-ignore-ok."
                undeclared-ignores name))
           (undeclared-ignores ; :warn
            (pprogn
             (warning$ ctx ("Ignored-variables")
                      "The formal variable~#0~[ ~&0 is~/s ~&0 are~] not used ~
                       in the definition of ~x1 but ~#0~[is~/are~] not ~
                       DECLAREd IGNOREd or IGNORABLE.  See :DOC set-ignore-ok ~
                       for how to either remove this warning or to enforce it ~
                       by causing an error."
                      undeclared-ignores name)
             (value nil)))
           (t (value nil))))))

(defun chk-free-and-ignored-vars-lsts (names arglists guards split-types-terms
                                             measures ignores ignorables bodies
                                             ctx state)

; This function does all of the defun checking related to the use of free vars
; and ignored/ignorable vars.  We package it all up here to simplify the
; appearance (and post-macro-expansion size) of the caller,
; chk-acceptable-defuns.  The first 6 args are in 1:1 correspondence.

  (declare (xargs :guard (and (symbol-listp names)
                              (symbol-list-listp arglists)
                              (pseudo-term-listp guards)
                              (pseudo-term-listp split-types-terms)
                              (pseudo-term-listp measures)
                              (pseudo-term-listp bodies)
                              (symbol-list-listp ignores)
                              (symbol-list-listp ignorables))))
  (cond ((null names) (value nil))
        (t (er-progn (chk-free-and-ignored-vars (car names)
                                                (car arglists)
                                                (car guards)
                                                (car split-types-terms)
                                                (car measures)
                                                (car ignores)
                                                (car ignorables)
                                                (car bodies)
                                                ctx state)
                     (chk-free-and-ignored-vars-lsts (cdr names)
                                                     (cdr arglists)
                                                     (cdr guards)
                                                     (cdr split-types-terms)
                                                     (cdr measures)
                                                     (cdr ignores)
                                                     (cdr ignorables)
                                                     (cdr bodies)
                                                     ctx state)))))

(defun putprop-x-lst1 (symbols key value wrld)

; For every sym in symbols, (putprop sym key value).

  (cond ((null symbols) wrld)
        (t (putprop-x-lst1 (cdr symbols)
                           key
                           value
                           (putprop (car symbols) key value wrld)))))

(defun putprop-x-lst2 (symbols key vals wrld)

; For corresponding symi,vali pairs in symbols x vals, (putprop symi key vali).
; The result has properties in reverse order from symbols, and we rely on that;
; see the comment in chk-acceptable-defuns1.

  (cond ((null symbols) wrld)
        (t (putprop-x-lst2 (cdr symbols)
                           key
                           (cdr vals)
                           (putprop (car symbols) key (car vals) wrld)))))

(defun putprop-x-lst2-unless (symbols key vals exception wrld)

; For corresponding symi,vali pairs in symbols x vals, (putprop symi
; key vali), unless vali is exception, in which case we do nothing.

  (cond ((null symbols) wrld)
        (t (putprop-x-lst2-unless (cdr symbols)
                                  key
                                  (cdr vals)
                                  exception
                                  (putprop-unless (car symbols)
                                                  key
                                                  (car vals)
                                                  exception
                                                  wrld)))))

(defun@par translate-term-lst (terms stobjs-out logic-modep known-stobjs-lst
                                     ctx wrld state)

; WARNING: Keep this in sync with translate-measures.

; This function translates each of the terms in terms and returns the
; list of translations or causes an error.  It uses the given
; stobjs-out and logic-modep on each term.  As it maps over terms it
; maps over known-stobjs-lst and uses the corresponding element for
; the known-stobjs of each translation.  However, if known-stobjs-lst
; is t it uses t for each.  Note the difference between the treatment
; of stobjs-out and logic-modep, on the one hand, and known-stobjs-lst
; on the other.  The former are ``fixed'' in the sense that the same
; setting is used for EACH term in terms, whereas the latter allows a
; different setting for each term in terms.

; Call this function with stobjs-out t if you want
; merely the logical meaning of the terms.  Call this function with
; stobjs-out '(nil state nil), for example, if you want to ensure that
; each term has the output signature given.

  (cond ((null terms) (value@par nil))
        (t (er-let*@par
            ((term (translate@par (car terms) stobjs-out logic-modep
                                  (if (eq known-stobjs-lst t)
                                      t
                                    (car known-stobjs-lst))
                                  ctx wrld state))
             (rst (translate-term-lst@par (cdr terms) stobjs-out logic-modep
                                          (if (eq known-stobjs-lst t)
                                              t
                                            (cdr known-stobjs-lst))
                                          ctx wrld state)))
            (value@par (cons term rst))))))

; We now turn to the major question of translating user typed hints into
; their internal form.  We combine this translation process with the
; checking that ensures that the hints are legal.  While our immediate
; interest is in the hints for defuns, we in fact handle all the hints
; supported by the system.

; Defthm takes a keyword argument, :HINTS, whose expected value is a
; "hints" of the form ((str1 . hints1) ... (strn . hintsn)) where
; each stri is a string that parses to a clause-id and each hintsi is
; a keyword/value list of the form :key1 val1 ... :keyk valk, where a
; typical :keyi might be :USE, :DO-NOT-INDUCT, :IN-THEORY, etc.  Thus,
; a typical defthm event might be:

; (defthm foo (equal x x)
;   :hints (("Goal''" :use assoc-of-append :in-theory *bar*)))

; Defun, the other event most commonly given hints, does not have room
; in its arg list for :HINTS since defun is a CLTL primitive.  So we have
; implemented the notion of the XARGS of DEFUN and permit it to have as its
; value a keyword/value list exactly like a keyword/value list in macro
; calls.  Thus, to pass the hint above into a defun event you would write

; (defun foo (x)
;   (declare (xargs :hints (("Goal''" :use assoc-of-append :in-theory *bar*))))
;   body)

; Making matters somewhat more complicated are the facts that defuns may
; take more than one defun tuple, i.e., one might be defining a clique of
; functions

;  (defuns
;    (fn1 (x) (DECLARE ...) ... body1)
;    ...
;    (fnn (x) (DECLARE ...) ... bodyn))

; and each such tuple may have zero or more DECLARE forms (or, in
; general, arbitrary forms which macroexpand into DECLARE forms).
; Each of those DECLAREs may have zero or more XARGS and we somehow
; have to extract a single list of hints from them collectively.  What
; we do is just concatenate the hints from each DECLARE form.  Thus,
; it is possible that fn1 will say to use hint settings hs1 on
; "Goal''" and fn2 will say to use hs2 on it.  Because we concatenate
; in the presented order, the clause-id's specified by fn1 have the
; first shot.

; The basic function we define below is translate-hints which takes a
; list of the alleged form ((str1 . hint-settings1) ...) and
; translates the strings and processes the keyword/value pairs
; appropriately.

; Just for the record, the complete list of hint keywords that might
; be used in a given hint-settings may be found in *hint-keywords*.

; For each hint keyword, :x, we have a function,
; translate-x-hint-value, that checks the form.  Each of these
; functions gets as its arg argument the object that was supplied as
; the value of the keyword.  We cause an error or return a translated
; value.  Of course, "translate" here means more than just apply the
; function translate; it means "convert to internal form", e.g.,
; in-theory hints are evaluated into theories.

(defun find-named-lemma (sym lst top-level)

; Sym is a symbol and lst is a list of lemmas, and top-level is initially t.
; We return a lemma in lst whose rune has base-symbol sym, if such a lemma is
; unique and top-level is t.  Otherwise we return nil, except we return
; :several if top-level is nil.

  (cond ((null lst) nil)
        ((equal sym
                (base-symbol (access rewrite-rule (car lst) :rune)))
         (cond ((and top-level
                     (null (find-named-lemma sym (cdr lst) nil)))
                (car lst))
               (top-level nil)
               (t :several)))
        (t (find-named-lemma sym (cdr lst) top-level))))

(defun find-runed-lemma (rune lst)

; Lst must be a list of lemmas.  We find the first one with :rune rune (but we
; make no assumptions on the form of rune).

  (cond ((null lst) nil)
        ((equal rune
                (access rewrite-rule (car lst) :rune))
         (car lst))
        (t (find-runed-lemma rune (cdr lst)))))

(mutual-recursion

(defun free-varsp-member (term vars)

; Like free-varsp, but takes a list of variables instead of an alist.

  (cond ((variablep term) (not (member-eq term vars)))
        ((fquotep term) nil)
        (t (free-varsp-member-lst (fargs term) vars))))

(defun free-varsp-member-lst (args vars)
  (cond ((null args) nil)
        (t (or (free-varsp-member (car args) vars)
               (free-varsp-member-lst (cdr args) vars)))))

)

(defun@par translate-expand-term1 (name form free-vars ctx wrld state)

; Returns an error triple (mv erp val state) where if erp is not nil, then val
; is an expand-hint determined by the given rune and alist.

  (cond
   ((not (arglistp free-vars))
    (er@par soft ctx
      "The use of :FREE in :expand hints should be of the form (:FREE ~
       var-list x), where var-list is a list of distinct variables, unlike ~
       ~x0."
      free-vars))
   (t
    (er-let*@par
     ((term (translate@par form t t t ctx wrld state)))
     (let ((term (remove-guard-holders term wrld)))
       (cond
        ((or (variablep term)
             (fquotep term))
         (er@par soft ctx
           "The term ~x0 is not expandable.  See the :expand discussion in ~
            :DOC hints."
           form))
        ((flambda-applicationp term)
         (cond
          (name (er@par soft ctx
                  "An :expand hint may only specify :WITH for an expression ~
                   that is the application of a function, unlike ~x0."
                  form))
          (t (value@par (make expand-hint
                              :pattern term
                              :alist (if (null free-vars)
                                         :none
                                       (let ((bound-vars
                                              (set-difference-eq (all-vars term)
                                                                 free-vars)))
                                         (pairlis$ bound-vars bound-vars)))
                              :rune nil
                              :equiv 'equal
                              :hyp nil
                              :lhs term
                              :rhs (subcor-var (lambda-formals (ffn-symb term))
                                               (fargs term)
                                               (lambda-body (ffn-symb term))))))))
        (t
         (mv-let
           (er-msg rune equiv hyp lhs rhs)
           (cond
            (name
             (let* ((fn (ffn-symb term))
                    (lemmas (getpropc fn 'lemmas nil wrld))
                    (lemma (cond ((symbolp name)
                                  (find-named-lemma
                                   (deref-macro-name name (macro-aliases wrld))
                                   lemmas
                                   t))
                                 (t (find-runed-lemma name lemmas)))))
               (cond
                (lemma
                 (let* ((hyps (access rewrite-rule lemma :hyps))
                        (lhs (access rewrite-rule lemma :lhs))
                        (lhs-vars (all-vars lhs))
                        (rhs (access rewrite-rule lemma :rhs)))
                   (cond
                    ((or (free-varsp-member-lst hyps lhs-vars)
                         (free-varsp-member rhs lhs-vars))
                     (mv (msg "The ~@0 of a rule given to :with in an :expand ~
                               hint must not contain free variables that are ~
                               not among the variables on its left-hand side. ~
                               ~ The ~#1~[variable ~&1 violates~/variables ~
                               ~&1 violate~] this requirement."
                              (if (free-varsp-member rhs lhs-vars)
                                  "left-hand side"
                                "hypotheses")
                              (if (free-varsp-member rhs lhs-vars)
                                  (reverse
                                   (set-difference-eq (all-vars rhs) lhs-vars))
                                (reverse
                                 (set-difference-eq (all-vars1-lst hyps nil)
                                                    lhs-vars))))
                         nil nil nil nil nil))
                    (t (mv nil
                           (access rewrite-rule lemma :rune)
                           (access rewrite-rule lemma :equiv)
                           (and hyps (conjoin hyps))
                           lhs
                           rhs)))))
                (t (mv (msg "Unable to find a lemma for :expand hint (:WITH ~
                             ~x0 ...)."
                            name)
                       nil nil nil nil nil)))))
            (t (let ((def-body (def-body (ffn-symb term) wrld)))
                 (cond
                  (def-body
                    (let ((formals (access def-body def-body :formals)))
                      (mv nil
                          (access def-body def-body :rune)
                          (access def-body def-body :equiv)
                          (access def-body def-body :hyp)
                          (cons-term (ffn-symb term) formals)
                          (access def-body def-body :concl))))
                  (t (mv (msg "The :expand hint for ~x0 is illegal, because ~
                               ~x1 is not a defined function."
                              form
                              (ffn-symb term))
                         nil nil nil nil nil))))))

; We could do an extra check that the lemma has some chance of applying.  This
; would involve a call of (one-way-unify lhs term) unless :free was specified,
; in which case we would need to call a full unification routine.  That doesn't
; seem worth the trouble merely for early user feedback.

           (cond
            (er-msg (er@par soft ctx "~@0" er-msg))
            (t (value@par (make expand-hint
                                :pattern term
                                :alist (if (null free-vars)
                                           :none
                                         (let ((bound-vars
                                                (set-difference-eq (all-vars term)
                                                                   free-vars)))
                                           (pairlis$ bound-vars bound-vars)))
                                :rune rune
                                :equiv equiv
                                :hyp hyp
                                :lhs lhs
                                :rhs rhs))))))))))))

(defun@par translate-expand-term (x ctx wrld state)

; X is a "term" given to an expand hint, which can be a term or the result of
; prepending (:free vars) or (:with name-or-rune), or both, to a term.  We
; return (mv erp expand-hint state).

  (case-match x
    (':lambdas
     (value@par x))
    ((':free vars (':with name form))
     (translate-expand-term1@par name form vars ctx wrld state))
    ((':with name (':free vars form))
     (translate-expand-term1@par name form vars ctx wrld state))
    ((':with name form)
     (translate-expand-term1@par name form nil  ctx wrld state))
    ((':free vars form)
     (translate-expand-term1@par nil  form vars ctx wrld state))
    (&
     (cond ((or (atom x)
                (keywordp (car x)))
            (er@par soft ctx
              "An :expand hint must either be a term, the keyword :lambdas, ~
               one of the forms (:free vars term) or (:with name term), or a ~
               combination of those final two forms.  The form ~x0 is thus ~
               illegal for an :expand hint.  See :DOC hints."
              x))
           (t (translate-expand-term1@par nil x nil ctx wrld state))))))

(defun@par translate-expand-hint1 (arg acc ctx wrld state)
  (cond ((atom arg)
         (cond
          ((null arg) (value@par (reverse acc)))
          (t (er@par soft ctx
               "The value of the :expand hint must be a true list, but your ~
                list ends in ~x0.  See :DOC hints."
               arg))))
        (t (er-let*@par
            ((xtrans (translate-expand-term@par (car arg) ctx wrld state)))
            (translate-expand-hint1@par (cdr arg) (cons xtrans acc) ctx wrld
                                        state)))))

(defun@par translate-expand-hint (arg ctx wrld state)

; Arg is whatever the user typed after the :expand keyword.  We
; allow it to be either a term or a list of terms.  For example,
; all of the following are legal:

;   :expand (append a b)
;   :expand ((append a b))
;   :expand (:with append (append a b))
;   :expand ((:with append (append a b)))
;   :expand ((:free (a) (append a b)))
;   :expand (:with append (:free (a) (append a b)))
;   :expand ((:with append (:free (a) (append a b))))

; Here we allow a general notion of "term" that includes expressions of the
; form (:free (var1 ... varn) term), indicating that the indicated variables
; are instantiatable in term, and (:with rd term), where rd is a runic
; designator (see :doc theories).  We also interpret :lambdas specially, to
; represent the user's desire that all lambda applications be expanded.

  (cond ((eq arg :lambdas)
         (translate-expand-hint1@par (list arg) nil ctx wrld state))
        ((atom arg)

; Arg had better be nil, otherwise we'll cause an error.

         (translate-expand-hint1@par arg nil ctx wrld state))
        ((and (consp arg)
              (symbolp (car arg))
              (not (eq (car arg) :lambdas)))

; In this case, arg is of the form (sym ...).  Now if arg were really
; intended as a list of terms to expand, the user would be asking us
; to expand the symbol sym, which doesn't make sense, and so we'd
; cause an error in translate-expand-hint1 above.  So we will treat
; this arg as a term.

         (translate-expand-hint1@par (list arg) nil ctx wrld state))
        ((and (consp arg)
              (consp (car arg))
              (eq (caar arg) 'lambda))

; In this case, arg is of the form ((lambda ...) ...).  If arg were
; really intended as a list of terms, then the first object on the
; list is illegal and would cause an error because lambda is not a
; function symbol.  So we will treat arg as a single term.

         (translate-expand-hint1@par (list arg) nil ctx wrld state))
        (t

; Otherwise, arg is treated as a list of terms.

         (translate-expand-hint1@par arg nil ctx wrld state))))

(defun cons-all-to-lst (new-members lst)
  (cond ((null new-members) nil)
        (t (cons (cons (car new-members) lst)
                 (cons-all-to-lst (cdr new-members) lst)))))

(defun@par translate-substitution (substn ctx wrld state)

; Note: This function deals with variable substitutions.  For
; functional substitutions, use translate-functional-substitution.

; Substn is alleged to be a substitution from variables to terms.
; We know it is a true list!  We check that each element is of the
; the form (v term) where v is a variable symbol and term is a term.
; We also check that no v is bound twice.  If things check out we
; return an alist in which each pair is of the form (v . term'), where
; term' is the translation of term.  Otherwise, we cause an error.

  (cond
   ((null substn) (value@par nil))
   ((not (and (true-listp (car substn))
              (= (length (car substn)) 2)))
    (er@par soft ctx
      "Each element of a substitution must be a pair of the form (var term), ~
       where var is a variable symbol and term is a term.  Your alleged ~
       substitution contains the element ~x0, which is not of this form.  See ~
       the discussion of :instance in :DOC lemma-instance."
      (car substn)))
   (t (let ((var (caar substn))
            (term (cadar substn)))
        (cond
         ((not (legal-variablep var))
          (mv-let (x str)
                  (find-first-bad-arg (list var))
                  (declare (ignore x))
                  (er@par soft ctx
                    "It is illegal to substitute for the non-variable ~x0.  ~
                     It fails to be a variable because ~@1.  See :DOC name ~
                     and see :DOC lemma-instance, in particular the ~
                     discussion of :instance."
                    var
                    (or str "LEGAL-VARIABLEP says so, but FIND-FIRST-BAD-ARG ~
                             can't see why"))))
         (t (er-let*@par
             ((term (translate@par term t t t ctx wrld state))
; known-stobjs = t (stobjs-out = t)
              (y (translate-substitution@par (cdr substn) ctx wrld state)))
             (cond ((assoc-eq var y)
                    (er@par soft ctx
                      "It is illegal to bind ~x0 twice in a substitution.  ~
                       See the discussion of :instance in :DOC lemma-instance."
                      var))
                   (t (value@par (cons (cons var term) y)))))))))))

(defun@par translate-substitution-lst (substn-lst ctx wrld state)
  (cond
   ((null substn-lst) (value@par nil))
   (t (er-let*@par
       ((tsubstn
         (translate-substitution@par (car substn-lst) ctx wrld state))
        (rst
         (translate-substitution-lst@par (cdr substn-lst) ctx wrld state)))
       (value@par (cons tsubstn rst))))))

(defun get-rewrite-and-defn-runes-from-runic-mapping-pairs (pairs)
  (cond
   ((null pairs)
    nil)
   ((member-eq (cadr (car pairs)) '(:rewrite :definition))
    (cons (cdr (car pairs))
          (get-rewrite-and-defn-runes-from-runic-mapping-pairs (cdr pairs))))
   (t (get-rewrite-and-defn-runes-from-runic-mapping-pairs (cdr pairs)))))

(defun@par translate-restrict-hint (arg ctx wrld state)

; Arg is whatever the user typed after the :restrict keyword.

  (cond
   ((atom arg)
    (cond
     ((null arg) (value@par nil))
     (t (er@par soft ctx
          "The value of the :RESTRICT hint must be an alistp (association ~
           list), and hence a true list, but your list ends in ~x0.  See :DOC ~
           hints."
          arg))))
   ((not (and (true-listp (car arg))
              (cdr (car arg))))
    (er@par soft ctx
      "Each member of a :RESTRICT hint must be a true list associating a name ~
       with at least one substitution, but the member ~x0 of your hint ~
       violates this requirement.  See :DOC hints."
      (car arg)))
   ((not (or (symbolp (caar arg))
             (and (runep (caar arg) wrld)
                  (member-eq (car (caar arg)) '(:rewrite :definition)))))
    (er@par soft ctx
      "Each member of a :RESTRICT hint must be a true list whose first ~
       element is either a symbol or a :rewrite or :definition rune in the ~
       current ACL2 world.  The member ~x0 of your hint violates this ~
       requirement."
      (car arg)))
   (t (let ((runes (if (symbolp (caar arg))
                       (get-rewrite-and-defn-runes-from-runic-mapping-pairs
                        (getpropc (caar arg) 'runic-mapping-pairs nil wrld))
                     (list (caar arg)))))
        (cond
         ((null runes)
          (er@par soft ctx
            "The name ~x0 does not correspond to any :rewrite or :definition ~
             runes, so the element ~x1 of your :RESTRICT hint is not valid.  ~
             See :DOC hints."
            (caar arg) (car arg)))
         (t (er-let*@par
             ((subst-lst (translate-substitution-lst@par
                          (cdr (car arg)) ctx wrld state))
              (rst (translate-restrict-hint@par (cdr arg) ctx wrld state)))
             (value@par (append (cons-all-to-lst runes subst-lst)
                                rst)))))))))

(defconst *do-not-processes*
  '(generalize preprocess simplify eliminate-destructors
               fertilize eliminate-irrelevance))

(defun coerce-to-process-name-lst (lst)
  (declare (xargs :guard (symbol-listp lst)))
  (if lst
      (cons (intern (string-append (symbol-name (car lst)) "-CLAUSE") "ACL2")
            (coerce-to-process-name-lst (cdr lst)))
      nil))

(defun coerce-to-acl2-package-lst (lst)
  (declare (xargs :guard (symbol-listp lst)))
  (if lst
      (cons (intern (symbol-name (car lst)) "ACL2")
            (coerce-to-acl2-package-lst (cdr lst)))
      nil))

(defun@par chk-do-not-expr-value (lst expr ctx state)

  ;; here lst is the raw names, coerced to the "ACL2" package

  (cond ((atom lst)
         (cond ((null lst)
                (value@par nil))
               (t (er@par soft ctx
                    "The value of the :DO-NOT expression ~x0 is not a true ~
                     list and, hence, is not legal.  In particular, the final ~
                     non-consp cdr is the atom ~x1.  See :DOC hints."
                    expr lst))))
        ((and (symbolp (car lst))
              (member-eq (car lst) *do-not-processes*))
         (chk-do-not-expr-value@par (cdr lst) expr ctx state))
        ((eq (car lst) 'induct)
         (er@par soft ctx
           "The value of the alleged :DO-NOT expression ~x0 includes INDUCT, ~
            which is not the name of a process to turn off.  You probably ~
            mean to use :DO-NOT-INDUCT T or :DO-NOT-INDUCT :BYE instead.  The ~
            legal names are ~&1."
           expr *do-not-processes*))
        (t (er@par soft ctx
             "The value of the alleged :DO-NOT expression ~x0 includes the ~
              element ~x1, which is not the name of a process to turn off.  ~
              The legal names are ~&2."
             expr (car lst) *do-not-processes*))))

(defun@par translate-do-not-hint (expr ctx state)

; We translate and evaluate expr and make sure that it produces something that
; is appropriate for :do-not.  We either cause an error or return the resulting
; list.

  (let ((wrld (w state)))
    (er-let*@par
     ((trans-ans (if (legal-variablep expr)
                     (value@par (cons nil (list expr)))
                   (serial-first-form-parallel-second-form@par
                    (simple-translate-and-eval
                     expr
                     (list (cons 'world wrld))
                     nil
                     "A :do-not hint"
                     ctx wrld state t)
                    (simple-translate-and-eval@par
                     expr
                     (list (cons 'world wrld))
                     nil
                     "A :do-not hint"
                     ctx wrld state t
                     (f-get-global 'safe-mode state)
                     (gc-off state))))))

; trans-ans is (& . val), where & is either nil or a term.

     (cond
      ((not (symbol-listp (cdr trans-ans)))
       (er@par soft ctx
         "The expression following :do-not is required either to be a symbol ~
          or an expression whose value is a true list of symbols, but the ~
          expression ~x0 has returned the value ~x1.  See :DOC hints."
         expr (cdr trans-ans)))
      (t
       (er-progn@par
        (chk-do-not-expr-value@par
         (coerce-to-acl2-package-lst (cdr trans-ans)) expr ctx state)
        (value@par (coerce-to-process-name-lst (cdr trans-ans)))))))))

(defun@par translate-do-not-induct-hint (arg ctx wrld state)
  (declare (ignore wrld))
  (cond ((symbolp arg)
         (cond ((member-eq arg '(:otf :otf-flg-override))
                (value@par arg))
               ((keywordp arg)
                (er@par soft ctx
                  "We do not allow :do-not-induct hint values in the keyword ~
                   package other than :OTF and :OTF-FLG-OVERRIDE.  The value ~
                   ~x0 is thus illegal."
                  arg))
               (t (value@par arg))))
        (t (er@par soft ctx
             "The :do-not-induct hint should be followed by a symbol.  ~x0 is ~
              thus illegal.  See the :do-not-induct discussion in :DOC hints."
             arg))))

(defun@par translate-hands-off-hint1 (arg ctx wrld state)
  (cond
   ((atom arg)
    (cond
     ((null arg) (value@par nil))
     (t (er@par soft ctx
          "The value of the :hands-off hint must be a true list, but your ~
           list ends in ~x0.  See the :hands-off discussion in :DOC hints."
          arg))))
   ((and (consp (car arg))
         (eq (car (car arg)) 'lambda)
         (consp (cdr (car arg)))
         (true-listp (cadr (car arg))))

; At this point we know that the car of arg is of the form (lambda
; (...) . &) and we want to translate it.  To do so, we create a term
; by applying it to a list of terms.  Where do we get a list of the
; right number of terms?  We use its own formals!

    (er-let*@par
     ((term (translate@par (cons (car arg) (cadr (car arg)))
                           t t t ctx wrld state))
      (term (value@par (remove-guard-holders term wrld)))
; known-stobjs = t (stobjs-out = t)
      (rst (translate-hands-off-hint1@par (cdr arg) ctx wrld state))
      (rst (value@par (remove-guard-holders-lst rst wrld))))

; Below we assume that if you give translate ((lambda ...) ...) and it
; does not cause an error, then it gives you back a function application.

     (value@par (cons (ffn-symb term) rst))))
   ((and (symbolp (car arg))
         (function-symbolp (car arg) wrld))
    (er-let*@par
     ((rst (translate-hands-off-hint1@par (cdr arg) ctx wrld state)))
     (value@par (cons (car arg) rst))))
   (t (er@par soft ctx
        "The object ~x0 is not a legal element of a :hands-off hint.  See the ~
         :hands-off discussion in :DOC hints."
        (car arg)))))

(defun@par translate-hands-off-hint (arg ctx wrld state)

; Arg is supposed to be a list of function symbols.  However, we
; allow either
;   :hands-off append
; or
;   :hands-off (append)
; in the singleton case.  If the user writes
;   :hands-off (lambda ...)
; we will understand it as
;   :hands-off ((lambda ...))
; since lambda is not a function symbol.

  (cond ((atom arg)
         (cond ((null arg) (value@par nil))
               ((symbolp arg)
                (translate-hands-off-hint1@par (list arg) ctx wrld state))
               (t (translate-hands-off-hint1@par arg ctx wrld state))))
        ((eq (car arg) 'lambda)
         (translate-hands-off-hint1@par (list arg) ctx wrld state))
        (t (translate-hands-off-hint1@par arg ctx wrld state))))

(defun truncated-class (rune mapping-pairs classes)

; Rune is a rune and mapping-pairs and classes are the corresponding
; properties of its base symbol.  We return the class corresponding to
; rune.  Recall that the classes stored are truncated classes, e.g.,
; they have the proof-specific parts removed and no :COROLLARY if it
; is the same as the 'THEOREM of the base symbol.  By convention, nil
; is the truncated class of a rune whose base symbol has no 'classes
; property.  An example of such a rune is (:DEFINITION fn).

  (cond ((null classes) nil)
        ((equal rune (cdr (car mapping-pairs))) (car classes))
        (t (truncated-class rune (cdr mapping-pairs) (cdr classes)))))

(defun tests-and-alists-lst-from-fn (fn wrld)
  (let* ((formals (formals fn wrld))
         (term (fcons-term fn formals))
         (quick-block-info
          (getpropc fn 'quick-block-info
                    '(:error "See SUGGESTED-INDUCTION-CANDS1.")
                    wrld))
         (justification
          (getpropc fn 'justification
                    '(:error "See SUGGESTED-INDUCTION-CANDS1.")
                    wrld))
         (mask (sound-induction-principle-mask term formals
                                               quick-block-info
                                               (access justification
                                                       justification
                                                       :subset)))
         (machine (getpropc fn 'induction-machine nil wrld)))
    (tests-and-alists-lst (pairlis$ formals (fargs term))
                          (fargs term) mask machine)))

(defun corollary (rune wrld)

; We return the :COROLLARY that justifies the rule named by rune.
; Nil is returned when we cannot recover a suitable formula.

  (let* ((name (base-symbol rune))
         (classes (getpropc name 'classes nil wrld)))
    (cond
     ((null classes)
      (cond
       ((or (eq (car rune) :definition)
            (eq (car rune) :executable-counterpart))
        (let ((body (body name t wrld)))
          (cond ((null body) nil)
                ((eq (car rune) :definition)
                 (let ((lemma
                        (find-runed-lemma rune
                                          (getpropc name 'lemmas nil wrld))))
                   (and lemma
                        (let ((concl
                               (mcons-term* (access rewrite-rule lemma :equiv)
                                            (access rewrite-rule lemma :lhs)
                                            (access rewrite-rule lemma :rhs))))
                          (if (access rewrite-rule lemma :hyps) ; impossible?
                              (mcons-term* 'implies
                                           (conjoin (access rewrite-rule lemma
                                                            :hyps))
                                           concl)
                            concl)))))
                (t
                 (mcons-term* 'equal
                              (cons-term name (formals name wrld))
                              body)))))
       ((eq (car rune) :type-prescription)
        (let ((tp (find-runed-type-prescription
                   rune
                   (getpropc name 'type-prescriptions nil wrld))))
          (cond
           ((null tp) *t*)
           (t (access type-prescription tp :corollary)))))
       ((and (eq (car rune) :induction)
             (equal (cddr rune) nil))

; At one time we returned a result based on induction-formula.  But that result
; was not a term: it contained calls of :P and was untranslated (see pf-fn for
; how that is now handled).  There is truly no formula associated with an
; induction "rule", as opposed to the corresponding symbol (which represents a
; defthm event with formula 'T), so we return nil here.

        nil)
       (t (er hard 'corollary
              "It was thought to be impossible for a rune to have no ~
               'classes property except in the case of the four or five ~
               definition runes described in the Essay on the ~
               Assignment of Runes and Numes by DEFUNS.  But ~x0 is a ~
               counterexample."
              rune))))
     (t (let ((term
               (cadr
                (assoc-keyword
                 :COROLLARY
                 (cdr
                  (truncated-class
                   rune
                   (getpropc name 'runic-mapping-pairs
                             '(:error "See COROLLARY.")
                             wrld)
                   classes))))))
          (or term
              (getpropc name 'theorem nil wrld)))))))

(defun formula (name normalp wrld)

; Name may be either an event name or a rune.  We return the formula associated
; with name.  We may return nil if we can find no such formula.

  (cond ((consp name) (corollary name wrld))
        (t (let ((body (body name normalp wrld)))
             (cond ((and body normalp)

; We have a defined function.  We want to use the original definition, not one
; installed by a :definition rule with non-nil :install-body field.

                    (corollary `(:DEFINITION ,name) wrld))
                   (body
                    (mcons-term* 'equal
                                 (cons-term name (formals name wrld))
                                 body))
                   (t (or (getpropc name 'theorem nil wrld)
                          (getpropc name 'defchoose-axiom nil wrld))))))))

(defun pf-induction-scheme (x wrld state)
  (declare (xargs :guard (or (symbolp x)
                             (runep x wrld))))
  (flet ((induction-pretty-clause-set
          (name flg wrld)
          (prettyify-clause-set
           (induction-formula (list (list (cons :p (formals name wrld))))
                              (tests-and-alists-lst-from-fn name wrld))
           flg
           wrld)))
    (let* ((rune (if (symbolp x)
                     (let ((r (list :induction x)))
                       (and (runep r wrld)
                            r))
                   (and (eq (car x) :induction)
                        (null (cddr x)) ; sanity check
                        x)))
           (name (and rune (base-symbol rune))))
      (cond
       ((null rune) (mv nil nil))
       ((function-symbolp name wrld)
        (mv (induction-pretty-clause-set name (let*-abstractionp state) wrld)
            nil))
       (t (let* ((class (truncated-class
                         rune
                         (getpropc name 'runic-mapping-pairs
                                   '(:error "See COROLLARY.")
                                   wrld)
                         (getpropc name 'classes nil wrld)))
                 (scheme (and (consp class)
                              (eq (car class) :induction)
                              (cadr (member :scheme class))))
                 (fn (and scheme
                          (ffn-symb scheme))))
            (cond ((runep `(:induction ,fn) wrld)
                   (mv (induction-pretty-clause-set fn
                                                    (let*-abstractionp state)
                                                    wrld)
                       fn))
                  (t (mv nil nil)))))))))

(defun pf-fn (name state)
  (io? temporary nil (mv erp val state)
       (name)
       (let ((wrld (w state)))
         (cond
          ((or (symbolp name)
               (runep name wrld))
           (let* ((name (if (symbolp name)
                            (deref-macro-name name (macro-aliases (w state)))
                          name))
                  (term (if (and (not (symbolp name)) ; (runep name wrld)
                                 (eq (car name) :induction))
                            nil
                          (formula name t wrld))))
             (mv-let (col state)
               (cond
                ((or (null term)
                     (equal term *t*))
                 (fmt1 (if (null term)
                           "There is no formula associated with ~x0.~@1"
                         "The formula associated with ~x0 is simply T.~@1")
                       (list (cons #\0 name)
                             (cons #\1
                                   (mv-let (s fn)
                                     (pf-induction-scheme name wrld state)
                                     (if s
                                         (msg "~|However, there is the ~
                                               following associated induction ~
                                               scheme~@0.~|~x1~|"
                                              (if fn
                                                  (msg " based on the ~
                                                        function symbol, ~x0"
                                                       fn)
                                                "")
                                              s)
                                       "~|"))))
                       0
                       (standard-co state) state nil))
                (term
                 (fmt1 "~p0~|"
                       (list (cons #\0 (untranslate term t wrld)))
                       0
                       (standard-co state) state
                       (term-evisc-tuple nil state)))
                (t
                 (fmt1 "There is no formula associated with ~x0.~|"
                       (list (cons #\0 name))
                       0 (standard-co state) state nil)))
               (declare (ignore col))
               (value :invisible))))
          (t
           (er soft 'pf
               "~x0 is neither a symbol nor a rune in the current world."
               name))))))

(defmacro pf (name)
  (list 'pf-fn name 'state))

(defun merge-symbol< (l1 l2 acc)
  (declare (xargs :guard (and (symbol-listp l1)
                              (symbol-listp l2)
                              (true-listp acc))))
  (cond ((endp l1) (revappend acc l2))
        ((endp l2) (revappend acc l1))
        ((symbol< (car l1) (car l2))
         (merge-symbol< (cdr l1) l2 (cons (car l1) acc)))
        (t (merge-symbol< l1 (cdr l2) (cons (car l2) acc)))))

(defun merge-sort-symbol< (l)
  (declare (xargs :guard (symbol-listp l)))
  (cond ((endp (cdr l)) l)
        (t (merge-symbol< (merge-sort-symbol< (evens l))
                          (merge-sort-symbol< (odds l))
                          nil))))

;; Historical Comment from Ruben Gamboa:
;; I added the non-standard primitives here.

(defconst *non-instantiable-primitives*

; WARNING: Note that there may be an implicit functional substitution applied
; to a :termination-theorem in translate-lmi.  Although we believe that the
; termination-theorem for O< is justified logically, that theorem depends on
; the definition of O< itself, so it is not OK to replace O< in its termination
; theorem by using a functional substitution (because its termination theorem
; is not a theorem when O< is viewed as being introduced by a defstub).
; Therefore we must include O< in this list, to guarantee that instantiablep
; fails for O<.  Indeed, the following example from Eric Smith exploits the
; lack of such an instantiablep check on the domain of that implicit functional
; substitution, starting in Version_7.3 when such implicit functional
; substitutions were first applied and through Version_8.0 (after which this
; bug was fixed).

;   (defun bad (x y)
;      (declare (xargs :measure (acl2-count x)
;                      ;; The problematic hint:
;                      :hints (("Goal" :use (:termination-theorem o<)))))
;      (if (or (o-finp x)
;              (o-finp y)
;              (equal (o-first-expt x)
;                     (o-first-expt y)))
;          nil
;        (if (bad (acl2-count (o-first-expt x))
;                 (acl2-count x))
;            nil
;          (+ 1 (bad x y)))))
;
;   (defthm bad-1-4
;      (not (bad 1 4)))
;
;   (in-theory (disable bad (:e bad)))
;
;   (defthmd bad-lemma
;      (equal (bad '((1 . 1)) '((2 . 2)))
;             (+ 1 (bad '((1 . 1)) '((2 . 2)))))
;      :instructions ((:dv 1) :x :top :s))
;
;   (defthm bad-thm
;      nil
;      :rule-classes nil
;      :hints (("Goal" :use (:instance bad-lemma))))

; We could redefine ENDP in terms of CONS so that ATOM doesn't have to be on
; the list below, but this seems unimportant.  If we take ATOM off, we need to
; change the definition of MAKE-CHARACTER-LIST.

  '(NOT IMPLIES
        O<                  ;;; used in its own termination theorem (see above)
        MEMBER-EQUAL        ;;; perhaps not needed; we are conservative here
        FIX                 ;;; used in DEFAULT-+-2
        BOOLEANP            ;;; used in BOOLEANP-CHARACTERP
        CHARACTER-LISTP     ;;; used in CHARACTER-LISTP-COERCE
        FORCE               ;;; just nice to protect
        CASE-SPLIT          ;;; just nice to protect
        MAKE-CHARACTER-LIST ;;; used in COMPLETION-OF-COERCE
        EQL ENDP            ;;; probably used in others
        ATOM                ;;; used in ENDP; probably used in others
        BAD-ATOM            ;;; used in several defaxioms
        RETURN-LAST         ;;; affects constraints (see remove-guard-holders1)
        MV-LIST             ;;; affects constraints (see remove-guard-holders1)
        CONS-WITH-HINT      ;;; affects constraints (see remove-guard-holders1)
        THE-CHECK           ;;; affects constraints (see remove-guard-holders1)

; The next six are used in built-in defpkg axioms.

        MEMBER-SYMBOL-NAME
        SYMBOL-PACKAGE-NAME
        INTERN-IN-PACKAGE-OF-SYMBOL
        PKG-IMPORTS
        SYMBOL-LISTP
        NO-DUPLICATESP-EQUAL
        NO-DUPLICATESP-EQ-EXEC ; not critical?
        NO-DUPLICATESP-EQ-EXEC$GUARD-CHECK ; not critical?

; We do not want vestiges of the non-standard version in the standard version.

        #+:non-standard-analysis STANDARDP
        #+:non-standard-analysis STANDARD-PART
        #+:non-standard-analysis I-LARGE-INTEGER
        #+:non-standard-analysis REALFIX
        #+:non-standard-analysis I-LARGE
        #+:non-standard-analysis I-SMALL

        ))

(defun instantiablep (fn wrld)

; This function returns t if fn is instantiable and nil otherwise; except, if
; if it has been introduced with unknown-constraints, then it returns the
; the 'constrainedp property, i.e., *unknown-constraints*.

  (and (symbolp fn)
       (not (member-eq fn *non-instantiable-primitives*))

; The list of functions above consists of o<, which we believe is built in
; implicitly in the defun principle, plus every symbol mentioned in any
; defaxiom in axioms.lisp that is not excluded by the tests below.  The
; function check-out-instantiablep, when applied to an :init world will check
; that this function excludes all the fns mentioned in axioms.  We call this
; function in initialize-acl2 to make sure we haven't forgotten some fns.

; We believe it would be ok to permit the instantiation of any defun'd
; function (except maybe o<) because we believe only one function
; satisfies each of those defuns.  It is not clear if we should be biased
; against the other fns above.

       (function-symbolp fn wrld)

; A :logic mode function symbol is non-primitive if and only if it has an
; 'unnormalized-body or 'constrainedp property.  For the forward implication,
; note that the symbol must have been introduced either in the signature of an
; encapsulate, in defuns, or in defchoose.  Note that the value of the
; 'constrainedp property can be *unknown-constraints*, in which case that is
; the value we want to return here; so do not switch the order of the disjuncts
; below!  (In particular, we take advantage of such an *unknown-constraints*
; value in translate-functional-substitution.)

       (or (getpropc fn 'constrainedp nil wrld)
           (and (body fn nil wrld)
                t))))

(defun constraint-info (fn wrld)

; Warning: If fn is defined by mutual-recursion, this function returns only the
; defining equation for f, not of its mutual-recursion siblings.  To obtain
; their constraints as well, see constraint-info+.

; Be careful about calling this function when fn is a program mode function
; symbol!  In that case we return the formula equating the call of fn on its
; formals with the unnormalized-body of fn, which probably is not sensible
; logically (but might be useful for finding ancestors, for example).

; This function returns a pair (mv flg x).  In the simplest and perhaps most
; common case, there is no 'constraint-lst property for fn, e.g., when fn is
; defined by defun or defchoose and not in the scope of an encapsulate.  In
; this case, flg is nil, and x is the defining axiom for fn.  In the other
; case, flg is the name under which the actual constraint for fn is stored
; (possibly name itself), and x is the list of constraints stored there or else
; a value (*unknown-constraints* . supporters), indicating that the constraints
; cannot be determined but involve at most the indicated supporters (immediate
; ancestors).

; We assume that if fn was introduced by a non-local defun or defchoose in the
; context of an encapsulate that introduced constraints, then the defining
; axiom for fn is included in its 'constraint-lst property.  That is:  in that
; case, we do not need to use the definitional axiom explicitly in order to
; obtain the full list of constraints.

  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (let ((prop (getpropc fn 'constraint-lst

; We want to distinguish between not finding a list of constraints, and finding
; a list of constraints of nil.  Perhaps we only store non-nil constraints, but
; even if so, there is no need to rely on that invariant, and future versions
; of ACL2 may not respect it.

                        t wrld)))

    (cond
     ((eq prop t)
      (let ((body ; (body fn nil wrld), but easier to guard-verify:
             (getpropc fn 'unnormalized-body nil wrld)))
        (cond (body

; Warning: Do not apply remove-guard-holders to body.  We rely on having all
; ancestors of body present in the constraint-info in our calculation of
; immediate-canonical-ancestors.  In particular, all function symbols in a call
; of return-last, especially one generated by mbe, must be collected here, to
; support the correct use of attachments in calls of metafunctions and
; clause-processor functions; see the remark about mbe in the Essay on
; Correctness of Meta Reasoning.

               (mv nil (fcons-term* 'equal
                                    (fcons-term fn (formals fn wrld))
                                    body)))
              (t
               (mv nil
                   (or (getpropc fn 'defchoose-axiom nil wrld)

; Then fn is a primitive, and has no constraint.

                       *t*))))))
     ((and (symbolp prop)
           prop
; The following must be true since prop is a symbol:
;          (not (unknown-constraints-p prop))
           )

; Then prop is a name, and the constraints for fn are found under that name.

      (mv prop
          (getpropc prop 'constraint-lst
                    '(:error "See constraint-info:  expected to find a ~
                              'constraint-lst property where we did not.")
                    wrld)))
     (t ; includes the case of (unknown-constraints-p prop)
      (mv fn prop)))))

(defun@par chk-equal-arities (fn1 n1 fn2 n2 ctx state)
  (cond
   ((not (equal n1 n2))
    (er@par soft ctx
      "It is illegal to replace ~x0 by ~x1 because the former ~#2~[takes no ~
       arguments~/takes one argument~/takes ~n3 arguments~] while the latter ~
       ~#4~[takes none~/takes one~/takes ~n5~].  See the :functional-instance ~
       discussion in :DOC :lemma-instance."
      fn1
      fn2
      (cond ((int= n1 0) 0)
            ((int= n1 1) 1)
            (t 2))
      n1
      (cond ((int= n2 0) 0)
            ((int= n2 1) 1)
            (t 2))
      n2))
   (t (value@par nil))))

(defun extend-sorted-symbol-alist (pair alist)
  (cond
   ((endp alist)
    (list pair))
   ((symbol< (car pair) (caar alist))
    (cons pair alist))
   (t
    (cons (car alist)
          (extend-sorted-symbol-alist pair (cdr alist))))))

;; Historical Comment from Ruben Gamboa:
;; This checks to see whether two function symbols are both
;; classical or both non-classical

#+:non-standard-analysis
(defun@par chk-equiv-classicalp (fn1 fn2 termp ctx wrld state)
  (let ((cp1 (classicalp fn1 wrld))
        (cp2 (if termp ; fn2 is a term, not a function symbol
                 (classical-fn-list-p (all-fnnames fn2) wrld)
               (classicalp fn2 wrld))))
    (if (equal cp1 cp2)
        (value@par nil)
      (er@par soft ctx
        "It is illegal to replace ~x0 by ~x1 because the former ~#2~[is ~
         classical~/is not classical~] while the latter ~#3~[is~/is not~]."
        (if (symbolp fn1) fn1 (untranslate fn1 nil wrld))
        (if (symbolp fn2) fn2 (untranslate fn2 nil wrld))
        (if cp1 0 1)
        (if cp2 0 1)))))

;; Historical Comment from Ruben Gamboa:
;; I modified the following, so that we do not allow substn to
;; map a non-classical constrained function into a classical function
;; or vice versa.

(defun@par translate-functional-substitution (substn ctx wrld state)

; Substn is alleged to be a functional substitution.  We know that it is a true
; list!  We check that each element is a pair of the form (fn1 fn2), where fn1
; is an instantiable function symbol of arity n and fn2 is either a function
; symbol of arity n or else a lambda expression of arity n with a body that
; translates.  We also check that no fn1 is bound twice.

; Note: We permit free variables to occur in the body, we permit implicitly
; ignored variables, and we do not permit declarations in the lambda.  That is,
; we take each lambda to be of the form (lambda (v1 ... vn) body) and we merely
; insist that body be a term with no particular relation to the vi.

; If substn satisfies these conditions we return an alist in which each pair
; has the form (fn1 . fn2'), where fn2' is the symbol fn2 or the lambda
; expression (lambda (v1 ... vn) body'), where body' is the translation of
; body.  We call this the translated functional substitution.  The returned
; result is sorted by car; see event-responsible-for-proved-constraint for how
; we make use of this fact.

; Warning: The presence of free variables in the lambda expressions means that
; capturing is possible during functional substitution.  We do not check that
; no capturing occurs, since we are not given the terms into which we will
; substitute.

  (cond
   ((null substn) (value@par nil))
   ((not (and (true-listp (car substn))
              (= (length (car substn)) 2)))
    (er@par soft ctx
      "The object ~x0 is not of the form (fi gi) as described in the ~
       :functional-instance discussion of :DOC lemma-instance."
      (car substn)))
   (t (let ((fn1 (caar substn))
            (fn2 (cadar substn))
            (str "The object ~x0 is not of the form (fi gi) as described in ~
                  the :functional-instance discussion of :DOC lemma-instance. ~
                  ~ ~x1 is neither a function symbol nor a pseudo-lambda ~
                  expression."))
        (cond
         ((not (and (symbolp fn1)
                    (function-symbolp fn1 wrld)))
          (er@par soft ctx
            "Each domain element in a functional substitution must be a ~
             function symbol, but ~x0 is not.  See the :functional-instance ~
             discussion of :DOC lemma-instance."
            fn1))
         ((not (eq (instantiablep fn1 wrld) t))
          (er@par soft ctx
            "The function symbol ~x0 cannot be instantiated~@1.  See the ~
             :functional-instance discussion about `instantiable' in :DOC ~
             lemma-instance."
            fn1
            (if (eq (instantiablep fn1 wrld) nil)
                ""
              (assert$
               (eq (instantiablep fn1 wrld) *unknown-constraints*)
               (msg " because it has unknown-constraints; see :DOC ~
                     partial-encapsulate")))))
         (t
          (er-let*@par
           ((x
             (cond
              ((symbolp fn2)
               (let ((fn2 (deref-macro-name fn2 (macro-aliases wrld))))
                 (cond
                  ((function-symbolp fn2 wrld)
                   (er-progn@par
                    (chk-equal-arities@par fn1 (arity fn1 wrld)
                                           fn2 (arity fn2 wrld)
                                           ctx state)
                    #+:non-standard-analysis
                    (chk-equiv-classicalp@par fn1 fn2 nil ctx wrld state)
                    (value@par (cons fn1 fn2))))
                  (t (er@par soft ctx str (car substn) fn2)))))
              ((and (true-listp fn2)
                    (= (length fn2) 3)
                    (eq (car fn2) 'lambda))
               (er-let*@par
                ((body
                  (translate@par (caddr fn2) t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
                (er-progn@par
                 (chk-arglist@par (cadr fn2) t ctx wrld state)
                 (chk-equal-arities@par fn1 (arity fn1 wrld)
                                        fn2 (length (cadr fn2))
                                        ctx state)
                 #+:non-standard-analysis
                 (chk-equiv-classicalp@par fn1 body t ctx wrld state)
                 (value@par (cons fn1 (make-lambda (cadr fn2) body))))))
              (t (er@par soft ctx str (car substn) fn2))))
            (y
             (translate-functional-substitution@par (cdr substn)
                                                    ctx wrld state)))
           (cond ((assoc-eq fn1 y)
                  (er@par soft ctx
                    "It is illegal to bind ~x0 twice in a functional ~
                     substitution.  See the :functional-instance discussion ~
                     of :DOC lemma-instance."
                    fn1))
                 (t (value@par (extend-sorted-symbol-alist x y)))))))))))

(mutual-recursion

; After Version_3.4, Ruben Gamboa added the variable allow-freevars-p, with the
; following explanation:

; Allow-freevars-p should be set to t in the #-:non-standard-analysis case, but
; otherwise set to nil when we are trying to apply the substitution to a
; non-classical formula.  In those cases, free variables in the body can
; capture non-standard objects, resulting in invalid theorems.  For example,
; take the following theorem
;
; (standardp x) => (standardp (f x))
;
; This theorem is true for classical constrained function f.  Now instantiate
; (f x) with (lambda (x) (+ x y)).  The result is
;
; (standardp x) => (standardp (+ x y))
;
; This formula is false.  E.g., it fails when x=0 and y=(i-large-integer).

(defun sublis-fn-rec (alist term bound-vars allow-freevars-p)

; See the comment just above for additional discussion of allow-freevars-p.

; This function carries out the functional substitution into term specified by
; the translated functional substitution alist.  It checks that alist does not
; allow capturing of its free variables by lambda expressions in term.  If
; allow-freevars-p is nil, it also checks that the alist does not have free
; variables in lambda expressions.  The return value is either (mv vars term),
; for vars a non-empty list of variables -- those having captured occurrences
; when allow-freevars-p is true, else all free variables of lambda expressions
; in alist when allow-freevars-p is nil -- or else is (mv nil new-term) when
; there are no such captures or invalid free variables, in which case new-term
; is the result of the functional substitution.  Note that the caller can tell
; whether an error is caused by capturing or by having disallowed free
; variables, since in the case that allow-freevars-p is nil, it is impossible
; for free variables to be captured (since no free variables are allowed).

; Let us say that an occurrence of fn in term is problematic if fn is bound to
; lambda-expr in alist and for some variable v that occurs free in lambda-expr,
; this occurrence of fn is in the scope of a lambda binding of v in term.  Key
; Observation: If there is no problematic occurrence of any function symbol in
; term, then we can obtain the result of this call of sublis-fn by first
; replacing v in lambda-app by a fresh variable v', then carrying out the
; functional substitution, and finally doing an ordinary substitution of v for
; v'.  This Key Observation explains why it suffices to check that there is no
; such problematic occurrence.  As we recur, we maintain bound-vars to be a
; list that includes all variables lambda-bound in the original term at the
; present occurrence of term.

; Every element of alist is either of the form (fn . sym) or of the form (fn
; . (LAMBDA (v1...vn) body)) where the vi are distinct variables and body is a
; translated term, but it is not known that body mentions only vars in formals.

; The former case, where fn is bound to a sym, is simple to handle: when we see
; calls of fn we replace them by calls of sym.  The latter case is not.  When
; we hit (g (FOO) y) with the functional substitution in which FOO gets (LAMBDA
; NIL X), we generate (g X y).  Note that this "imports" a free X into a term,
; (g (foo) y), where there was no X.

; But there is a problem.  If you hit ((lambda (z) (g (FOO) z)) y) where FOO
; gets (LAMBDA NIL X), you would naively produce ((lambda (z) (g X z)) y),
; importing the X into the G term as noted above.  But we also just imported
; the X into the scope of a lambda!  Even though there is no capture, we now
; have a lambda expression whose body contains a var not among the formals.
; That is not a term!

; The solution is to scan the new lambda body, which is known to be a term, and
; collect the free vars -- vars not bound among the formals of the lambda --
; and add them both to the lambda formals and to the actuals.

  (cond
   ((variablep term) (mv nil term))
   ((fquotep term) (mv nil term))
   ((flambda-applicationp term)
    (let ((old-lambda-formals (lambda-formals (ffn-symb term))))
      (mv-let
       (erp new-lambda-body)
       (sublis-fn-rec alist
                      (lambda-body (ffn-symb term))
                      (append old-lambda-formals bound-vars)
                      allow-freevars-p)
       (cond
        (erp (mv erp new-lambda-body))
        (t (mv-let
            (erp args)
            (sublis-fn-rec-lst alist (fargs term) bound-vars allow-freevars-p)
            (cond (erp (mv erp args))
                  (t (let* ((body-vars (all-vars new-lambda-body))
                            (extra-body-vars
                             (set-difference-eq body-vars
                                                old-lambda-formals)))
                       (mv nil
                           (fcons-term
                            (make-lambda
                             (append old-lambda-formals extra-body-vars)
                             new-lambda-body)
                            (append args extra-body-vars))))))))))))
   (t (let ((temp (assoc-eq (ffn-symb term) alist)))
        (cond
         (temp
          (cond ((symbolp (cdr temp))
                 (mv-let
                  (erp args)
                  (sublis-fn-rec-lst alist (fargs term) bound-vars
                                     allow-freevars-p)
                  (cond (erp (mv erp args))
                        (t (mv nil
                               (cons-term (cdr temp) args))))))
                (t
                 (let ((bad (if allow-freevars-p
                                (intersection-eq
                                 (set-difference-eq
                                  (all-vars (lambda-body (cdr temp)))
                                  (lambda-formals (cdr temp)))
                                 bound-vars)
                              (set-difference-eq
                               (all-vars (lambda-body (cdr temp)))
                               (lambda-formals (cdr temp))))))
                   (cond
                    (bad (mv bad term))
                    (t (mv-let
                        (erp args)
                        (sublis-fn-rec-lst alist (fargs term) bound-vars
                                           allow-freevars-p)
                        (cond (erp (mv erp args))
                              (t (mv nil
                                     (sublis-var
                                      (pairlis$ (lambda-formals (cdr temp))
                                                args)
                                      (lambda-body (cdr temp)))))))))))))
         (t (mv-let (erp args)
                    (sublis-fn-rec-lst alist (fargs term) bound-vars
                                       allow-freevars-p)
                    (cond (erp (mv erp args))
                          (t (mv nil
                                 (cons-term (ffn-symb term) args)))))))))))

(defun sublis-fn-rec-lst (alist terms bound-vars allow-freevars-p)
  (cond ((null terms) (mv nil nil))
        (t (mv-let
            (erp term)
            (sublis-fn-rec alist (car terms) bound-vars allow-freevars-p)
            (cond (erp (mv erp term))
                  (t (mv-let
                      (erp tail)
                      (sublis-fn-rec-lst alist (cdr terms) bound-vars
                                         allow-freevars-p)
                      (cond (erp (mv erp tail))
                            (t (mv nil (cons term tail)))))))))))

)

(defun sublis-fn (alist term bound-vars)

; This is just the usual case.  We call the more general function
; sublis-fn-rec, which can be used on the non-standard case.

  (sublis-fn-rec alist term bound-vars t))

(defun sublis-fn-simple (alist term)

; This is the normal case, in which we call sublis-fn with no bound vars and we
; expect no vars to be captured (say, because alist has no free variables).

  (mv-let (vars result)
          (sublis-fn-rec alist term nil t)
          (assert$ (null vars)
                   result)))

(defun sublis-fn-lst-simple (alist termlist)

; See sublis-fn-simple, as this is the analogous function for a list of terms.

  (mv-let (vars result)
          (sublis-fn-rec-lst alist termlist nil t)
          (assert$ (null vars)
                   result)))

(mutual-recursion

(defun instantiable-ffn-symbs (term wrld ans ignore-fns)

; We collect every instantiablep ffn-symb occurring in term except those listed
; in ignore-fns.  We include functions introduced by a partial-encapsulate.

  (cond
   ((variablep term) ans)
   ((fquotep term) ans)
   ((flambda-applicationp term)
    (let ((ans (instantiable-ffn-symbs (lambda-body (ffn-symb term))
                                       wrld
                                       ans
                                       ignore-fns)))
      (instantiable-ffn-symbs-lst (fargs term)
                                  wrld
                                  ans
                                  ignore-fns)))
   (t (instantiable-ffn-symbs-lst
       (fargs term)
       wrld
       (cond ((or (not (instantiablep (ffn-symb term) wrld))
                  (member-eq (ffn-symb term) ignore-fns))
              ans)
             (t (add-to-set-eq (ffn-symb term) ans)))
       ignore-fns))))

(defun instantiable-ffn-symbs-lst (lst wrld ans ignore-fns)
  (cond ((null lst) ans)
        (t
         (instantiable-ffn-symbs-lst (cdr lst)
                                     wrld
                                     (instantiable-ffn-symbs (car lst) wrld ans
                                                             ignore-fns)
                                     ignore-fns))))

)

(defun unknown-constraints-p (prop)
  (declare (xargs :guard t))
  (and (consp prop)
       (eq (car prop) *unknown-constraints*)))

(defun unknown-constraints-supporters (prop)
  (declare (xargs :guard (unknown-constraints-p prop)))
  (cdr prop))

(defun collect-instantiablep1 (fns wrld ignore-fns)

; We assume that fns has no duplicates.

  (cond ((endp fns) nil)
        ((and (not (member-eq (car fns) ignore-fns))
              (instantiablep (car fns) wrld))
         (cons (car fns)
               (collect-instantiablep1 (cdr fns) wrld ignore-fns)))
        (t (collect-instantiablep1 (cdr fns) wrld ignore-fns))))

(defun all-instantiablep (fns wrld)
  (cond ((endp fns) t)
        ((instantiablep (car fns) wrld)
         (all-instantiablep (cdr fns) wrld))
        (t nil)))

(defun collect-instantiablep (fns wrld ignore-fns)

; We assume that fns has no duplicates.

  (cond ((and (not (intersectp-eq fns ignore-fns))
              (all-instantiablep fns wrld))
         fns)
        (t (collect-instantiablep1 fns wrld ignore-fns))))

(defun immediate-instantiable-ancestors (fn wrld ignore-fns)

; We return the list of all the instantiable function symbols ('instantiablep
; property t) that are immediate supporters of the introduction of fn, except
; those appearing in ignore-fns.

; If there are (possibly empty) constraints associated with fn, then we get all
; of the instantiable function symbols used in the constraints, which includes
; the definitional axiom if there is one.

; If fn was introduced by a defun or defchoose (it should be a non-primitive),
; we return the list of all instantiable functions used in its introduction.
; Note that even if fn is introduced by a defun, it may have constraints if its
; definition was within the scope of an encapsulate, in which case the
; preceding paragraph applies.

; If fn is introduced any other way we consider it primitive and all of the
; axioms about it had better involve non-instantiable symbols, so the answer is
; nil.

; Note: We pass down ignore-fns simply to avoid consing into our answer a
; function that the caller is going to ignore anyway.  It is possible for fn to
; occur as an element of its "immediate ancestors" as computed here.  This
; happens, for example, if fn is defun'd recursively and fn is not in
; ignore-fns.  At the time of this writing the only place we use
; immediate-instantiable-ancestors is in ancestors, where fn is always in
; ignore-fns (whether fn is recursive or not).

  (mv-let (name x)
          (constraint-info fn wrld)
    (cond
     ((unknown-constraints-p x)
      (let ((supporters (unknown-constraints-supporters x)))
        (collect-instantiablep supporters wrld ignore-fns)))
     (name (instantiable-ffn-symbs-lst x wrld nil ignore-fns))
     (t (instantiable-ffn-symbs x wrld nil ignore-fns)))))

(defun instantiable-ancestors (fns wrld ans)

; Fns is a list of function symbols.  We compute the list of all instantiable
; function symbols that are ancestral to the functions in fns and accumulate
; them in ans, including those introduced in a partial-encapsulate.

  (cond
   ((null fns) ans)
   ((member-eq (car fns) ans)
    (instantiable-ancestors (cdr fns) wrld ans))
   (t
    (let* ((ans1 (cons (car fns) ans))
           (imm (immediate-instantiable-ancestors (car fns) wrld ans1))
           (ans2 (instantiable-ancestors imm wrld ans1)))
      (instantiable-ancestors (cdr fns) wrld ans2)))))

(mutual-recursion

(defun hitp (term alist)

; Alist is a translated functional substitution.  We return t iff
; term mentions some function symbol in the domain of alist.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (hitp (lambda-body (ffn-symb term)) alist)
             (hitp-lst (fargs term) alist)))
        ((assoc-eq (ffn-symb term) alist) t)
        (t (hitp-lst (fargs term) alist))))

(defun hitp-lst (terms alist)
  (cond ((null terms) nil)
        (t (or (hitp (car terms) alist)
               (hitp-lst (cdr terms) alist)))))

)

(defun event-responsible-for-proved-constraint (name alist
                                                     proved-fnl-insts-alist)

; For context, see the Essay on the proved-functional-instances-alist.

; Here proved-fnl-insts-alist is of the form of the world global
; 'proved-functional-instances-alist.  Thus, it is a list of entries of the
; form (constraint-event-name restricted-alist . behalf-of-event-name), where
; constraint-event-name is the name of an event such that the functional
; instance of that event's constraint (i.e., function's constraint or axiom's
; 'theorem property) by restricted-alist was proved on behalf of the event
; named behalf-of-event-name.

  (cond
   ((endp proved-fnl-insts-alist)
    nil)
   ((and (eq name
             (access proved-functional-instances-alist-entry
                     (car proved-fnl-insts-alist)
                     :constraint-event-name))
         (equal alist
                (access proved-functional-instances-alist-entry
                        (car proved-fnl-insts-alist)
                        :restricted-alist)))

; We allow the behalf-of-event-name field (see comment above) to be nil in
; temporary versions of this sort of data structure, but we do not expect to
; find nil for that field in proved-fnl-insts-alist, which comes from the ACL2
; world.  (We store 0 there when there is no event name to use, e.g. when the
; event was a verify-guards event.  See the call of
; proved-functional-instances-from-tagged-objects in install-event.)  But to be
; safe in avoiding confusion with the first branch of our cond (in which there
; is no appropriate entry for our proof obligation), we check for nil here.

    (or (access proved-functional-instances-alist-entry
                (car proved-fnl-insts-alist)
                :behalf-of-event-name)
        (er hard 'event-responsible-for-proved-constraint
            "Implementation error: We expected to find a non-nil ~
             :behalf-of-event-name field in the following entry of the world ~
             global 'proved-functional-instances-alist, but did not:~%~x0."
            (car proved-fnl-insts-alist))))
   (t (event-responsible-for-proved-constraint
       name alist (cdr proved-fnl-insts-alist)))))

(defun getprop-x-lst (symbols prop wrld)
  (cond ((null symbols) nil)
        (t (cons (getpropc (car symbols) prop nil wrld)
                 (getprop-x-lst (cdr symbols) prop wrld)))))

(defun filter-hitps (lst alist ans)
  (cond
   ((endp lst) ans)
   ((hitp (car lst) alist)
    (filter-hitps (cdr lst) alist (cons (car lst) ans)))
   (t (filter-hitps (cdr lst) alist ans))))

(defun relevant-constraints1 (names alist proved-fnl-insts-alist constraints
                                    event-names new-entries seen wrld)

; For context, see the Essay on the proved-functional-instances-alist.

; Names is a list of function symbols, each of which therefore has a constraint
; formula.  We return three values, corresponding respectively to the following
; three formals, which are initially nil:  constraints, event-names, and
; new-entries.  The first value is the result of collecting those constraint
; formulas that are hit by the translated functional substitution alist, except
; for those that are known (via proved-fnl-insts-alist) to have already been
; proved.  The second is a list of names of events responsible for the validity
; of the omitted formulas.  The third is a list of pairs (cons name
; restr-alist), where restr-alist is obtained by restricting the given alist to
; the instantiable function symbols occurring in the constraint generated by
; name (in the sense of constraint-info).

; Exception: We are free to return (mv u g nil), where (unknown-constraints-p
; u).  However, we only do so if the constraints cannot be determined because
; of the presence of unknown-constraints on some function g encountered.

; Seen is a list of names already processed.  Suppose that foo and bar are both
; constrained by the same encapsulate, and that the 'constraint-lst property of
; 'bar is 'foo.  Since both foo and bar generate the same constraint, we want
; to be sure only to process that constraint once.  So, we put foo on the list
; seen as soon as bar is processed, so that foo will not have to be processed.

; Note that the current ttree is not available here.  If it were, we could
; choose to avoid proving constraints that were already generated in the
; current proof.  It doesn't seem that this would buy us very much, though:
; how often does one find more than one :functional-instance lemma instance in
; a single proof, especially with overlapping constraints?

; See also relevant-constraints1-axioms, which is a similar function for
; collecting constraint information from defaxiom events.

  (cond ((null names) (mv constraints event-names new-entries))
        ((member-eq (car names) seen)
         (relevant-constraints1
          (cdr names) alist proved-fnl-insts-alist
          constraints event-names new-entries seen wrld))
        (t (mv-let
            (name x)
            (constraint-info (car names) wrld)

; Note that -- ignoring the case of unknown-constraints -- x is a single
; constraint if name is nil and otherwise x is a list of constraints.

            (cond
             ((unknown-constraints-p x)

; If there is a hit among the supporters, then we stop here, returning x to
; indicate that there are unknown-constraints.  Otherwise, we recurs on (cdr
; names), just as we do in the normal case (known constraints) when there is no
; hit.

              (let ((supporters (unknown-constraints-supporters x)))
                (cond
                 ((first-assoc-eq supporters alist)
                  (mv x name nil))
                 (t (relevant-constraints1
                     (cdr names) alist proved-fnl-insts-alist
                     constraints event-names new-entries
                     seen
                     wrld)))))
             ((and name
                   (not (eq name (car names)))

; Minor point:  the test immediately above is subsumed by the one below, since
; we already know at this point that (not (member-eq (car names) seen)), but we
; keep it in for efficiency.

                   (member-eq name seen))
              (relevant-constraints1
               (cdr names) alist proved-fnl-insts-alist
               constraints event-names new-entries
               (cons (car names) seen) wrld))
             (t
              (let* ((x (cond (name (filter-hitps x alist nil))
                              ((hitp x alist) x)

; We continue to treat x as a list of constraints or a single constraint,
; depending respectively on whether name is non-nil or nil; except, we will
; use nil for x when there are no constraints even when name is nil.

                              (t nil)))
                     (instantiable-fns
                      (and x ; optimization
                           (cond (name (instantiable-ffn-symbs-lst
                                        x wrld nil nil))
                                 (t (instantiable-ffn-symbs
                                     x wrld nil nil))))))
                (let* ((constraint-alist
                        (and x ; optimization
                             (restrict-alist instantiable-fns alist)))
                       (ev
                        (and x ; optimization: ev unused when (null x) below
                             (event-responsible-for-proved-constraint
                              (or name (car names))
                              constraint-alist
                              proved-fnl-insts-alist)))
                       (seen (cons (car names)
                                   (if (and name (not (eq name (car names))))
                                       (cons name seen)
                                     seen))))
                  (cond
                   ((null x)
                    (relevant-constraints1
                     (cdr names) alist proved-fnl-insts-alist
                     constraints event-names new-entries
                     seen
                     wrld))
                   (ev (relevant-constraints1
                        (cdr names) alist proved-fnl-insts-alist
                        constraints

; Notice that ev could be 0; see event-responsible-for-proved-constraint.
; Where do we handle such an "event name"?  Here is an inverted call stack:

;           relevant-constraints1             ; called by:
;           relevant-constraints              ; called by:
;           translate-lmi/functional-instance ; called by:
;           translate-lmi                     ; called by:
; translate-use-hint(1)   translate-by-hint   ; called by:
;           translate-x-hint-value

; So, hints are translated.  Who looks at the results?  Well,
; apply-top-hints-clause adds :use and :by to the tag-tree.
; Who looks at the tag-tree?  It's
; apply-top-hints-clause-msg1, which in turn calls
; tilde-@-lmi-phrase -- and THAT is who sees and handles an "event" of 0.
; We might want to construct an example that illustrates this "0 handling" by
; way of providing a :functional-instance lemma-instance in a verify-guards.

                        (add-to-set ev event-names)
                        new-entries
                        seen
                        wrld))
                   (t (relevant-constraints1
                       (cdr names) alist proved-fnl-insts-alist
                       (if name
                           (append x constraints)
                         (cons x constraints))
                       event-names

; On which name's behalf do we note the constraint-alist?  If name is not nil,
; then it is a "canonical" name for which constraint-info returns the
; constraints we are using, in the sense that its constraint-lst is a list.
; Otherwise, (car names) is the name used to obtain constraint-info.

                       (cons (make proved-functional-instances-alist-entry
                                   :constraint-event-name (or name
                                                              (car names))
                                   :restricted-alist constraint-alist
                                   :behalf-of-event-name

; Eventually, the ``nil'' below may be filled in with the event name on behalf
; of which we are carrying out the current proof.

                                   nil)
                             new-entries)
                       seen
                       wrld)))))))))))

(defun relevant-constraints1-axioms (names alist proved-fnl-insts-alist
                                           constraints event-names new-entries
                                           wrld)

; For context, see the Essay on the proved-functional-instances-alist.

; This function is similar to relevant-constraints1, and should be kept more or
; less conceptually in sync with it.  However, in this function, names is a
; list of distinct axiom names rather than function names.  See
; relevant-constraints1 for comments.

  (cond ((null names) (mv constraints event-names new-entries))
        (t (let* ((constraint
                   (getpropc (car names)
                             'theorem
                             '(:error "See relevant-constraints1-axioms.")
                             wrld))
                  (instantiable-fns
                   (instantiable-ffn-symbs constraint wrld nil nil)))
             (cond ((hitp constraint alist)
                    (let* ((constraint-alist
                            (restrict-alist
                             instantiable-fns
                             alist))
                           (ev (event-responsible-for-proved-constraint
                                (car names)
                                constraint-alist
                                proved-fnl-insts-alist)))
                      (cond
                       (ev (relevant-constraints1-axioms
                            (cdr names) alist proved-fnl-insts-alist
                            constraints
                            (add-to-set ev event-names)
                            new-entries
                            wrld))
                       (t (relevant-constraints1-axioms
                           (cdr names) alist proved-fnl-insts-alist
                           (cons constraint constraints)
                           event-names
                           (cons (make proved-functional-instances-alist-entry
                                       :constraint-event-name (car names)
                                       :restricted-alist constraint-alist
                                       :behalf-of-event-name nil)
                                 new-entries)
                           wrld)))))
                   (t (relevant-constraints1-axioms
                       (cdr names) alist proved-fnl-insts-alist
                       constraints event-names new-entries
                       wrld)))))))

(defun relevant-constraints (thm alist proved-fnl-insts-alist wrld)

; For context, see the Essay on the proved-functional-instances-alist.

; Thm is a term and alist is a translated functional substitution.  We return
; three values.  The first value is the list of the constraints that must be
; instantiated with alist and proved in order to justify the functional
; instantiation of thm.  The second value is a list of names of events on whose
; behalf proof obligations were not generated that would otherwise have been,
; because those proof obligations were proved during processing of those
; events.  (In such cases we do not include these constraints in our first
; value.)  Our third and final value is a list of new entries to add to the
; world global 'proved-functional-instances-alist, as described in the comment
; for event-responsible-for-proved-constraint.

; Keep the following comment in sync with the corresponding comment in
; defaxiom-supporters.

; The relevant theorems are the set of all terms, term, such that
;   (a) term mentions some function symbol in the domain of alist,
;   AND
;   (b) either
;      (i) term arises from a definition of or constraint on a function symbol
;          ancestral either in thm or in some defaxiom,
;       OR
;      (ii) term is the body of a defaxiom.
; In translate-lmi/functional-instance we check that variable capture is
; avoided.

  (let ((nonconstructive-axiom-names
         (global-val 'nonconstructive-axiom-names wrld)))
    (mv-let
     (constraints event-names new-entries)
     (relevant-constraints1-axioms
      nonconstructive-axiom-names alist proved-fnl-insts-alist
      nil nil nil
      wrld)
     (assert$
      (not (unknown-constraints-p constraints))
      (let* ((instantiable-fns
              (instantiable-ffn-symbs-lst
               (cons thm (getprop-x-lst nonconstructive-axiom-names
                                        'theorem wrld))
               wrld nil nil))
             (ancestors (instantiable-ancestors instantiable-fns wrld nil)))
        (relevant-constraints1 ancestors alist proved-fnl-insts-alist
                               constraints event-names new-entries nil
                               wrld))))))

(mutual-recursion

(defun bound-vars (term ans)
  (cond ((variablep term) ans)
        ((fquotep term) ans)
        ((flambda-applicationp term)
         (bound-vars
          (lambda-body (ffn-symb term))
          (bound-vars-lst (fargs term)
                                  (union-eq (lambda-formals (ffn-symb term))
                                            ans))))
        (t (bound-vars-lst (fargs term) ans))))

(defun bound-vars-lst (terms ans)
  (cond ((null terms) ans)
        (t (bound-vars-lst
            (cdr terms)
            (bound-vars (car terms) ans)))))

)

(defun translate-lmi/instance-fix-alist (un-mentioned-vars formula-vars alist)
  (cond
   ((endp un-mentioned-vars) alist)
   (t (let ((alist (translate-lmi/instance-fix-alist
                    (cdr un-mentioned-vars) formula-vars alist)))
        (cond ((eq alist :failed) :failed)
              (t (let* ((bad-var (car un-mentioned-vars))
                        (name (symbol-name bad-var))
                        (tail (member-symbol-name name formula-vars)))
                   (cond (tail
                          (cond ((or (assoc-eq (car tail) alist)
                                     (member-symbol-name name (cdr tail)))

; Consider these events, to see (below) why we need both disjuncts just above.

;  (defpkg "FOO" nil)
;  (defpkg "BAR" nil)
;  (defthm my-car-cons (equal (car (cons x foo::y)) x))
;  (defthm my-car-cons2 (equal (car (cons bar::y foo::y)) bar::y))

; The member-symbol-name disjunct above is needed in order for this to fail.
;  (thm (equal a a)
;       :hints
;       (("Goal" :use ((:instance my-car-cons2 (y 17))))))

; The assoc-eq disjunct above is needed in order for this to fail.
;  (thm (equal a a)
;       :hints
;       (("Goal" :use ((:instance my-car-cons (x x) (foo::y 18) (y 17))))))


                                 :failed)
                                (t (let ((val (cdr (assoc-eq bad-var alist))))
                                     (assert$
                                      val
                                      (acons (car tail)
                                             val
                                             (remove1-assoc-eq bad-var
                                                               alist)))))))
                         (t :failed)))))))))

(defun@par translate-lmi/instance (formula constraints event-names new-entries
                                           extra-bindings-ok substn ctx wrld
                                           state)

; Formula is some term, obtained by previous instantiations.  Constraints
; are the constraints generated by those instantiations -- i.e., if the
; constraints are theorems then formula is a theorem.  Substn is an
; alleged variable substitution.  We know substn is a true list.

; Provided substn indeed denotes a substitution that is ok to apply to formula,
; we create the instance of formula.  We return a list whose car is the
; instantiated formula and whose cdr is the incoming constraints, event-names
; and new-entries, which all pass through unchanged.  Otherwise, we cause an
; error.

  (er-let*@par
   ((alist (translate-substitution@par substn ctx wrld state)))
   (let* ((vars (all-vars formula))
          (un-mentioned-vars (and (not extra-bindings-ok)
                                  (set-difference-eq (strip-cars alist)
                                                     vars)))
          (alist
           (if un-mentioned-vars
               (translate-lmi/instance-fix-alist un-mentioned-vars vars alist)
             alist)))
     (cond
      ((eq alist :failed) ; un-mentioned-vars is non-nil; unable to fix alist
       (er@par soft ctx
         "The formula you wish to instantiate, ~p3, mentions ~#0~[no ~
          variables~/only the variable ~&1~/the variables ~&1~].  Thus, there ~
          is no reason to include ~&2 in the domain of your substitution.  We ~
          point this out only because it frequently indicates that a mistake ~
          has been made.  See the discussion of :instance in :DOC ~
          lemma-instance, which explains how to use a keyword, ~
          :extra-bindings-ok, to avoid this error (for example, in case your ~
          substitution was automatically generated by a macro)."
         (zero-one-or-more vars)
         (merge-sort-symbol< vars)
         (merge-sort-symbol< un-mentioned-vars)
         (untranslate formula t wrld)))
      (t (value@par (list (sublis-var alist formula)
                          constraints
                          event-names
                          new-entries)))))))

(defun fn-subst-free-vars (alist)
  (cond ((endp alist) nil)
        ((symbolp (cdar alist))
         (fn-subst-free-vars (cdr alist)))
        (t ; (flambdap (cdar alist))
         (let* ((fn (cdar alist))
                (formals (lambda-formals fn))
                (body (lambda-body fn))
                (free-vars (set-difference-eq (all-vars body) formals)))
           (union-eq free-vars
                     (fn-subst-free-vars (cdr alist)))))))

(defun fn-subst-renaming-alist (vars avoid-vars)
  (cond ((endp vars) nil)
        (t (let* ((var (car vars))
                  (new-var (genvar (car vars)
                                   (concatenate 'string
                                                (symbol-name (car vars))
                                                "-RENAMED")
                                   0
                                   avoid-vars)))
             (acons var new-var
                    (fn-subst-renaming-alist (cdr vars)
                                             (cons new-var avoid-vars)))))))

(defun remove-capture-in-constraint-lst (alist new-constraints)
  (let* ((new-constraints-vars

; Alist is a (translated) functional substitution and new-constraints is a list
; of terms.  In the intended use of this function, new-constraints is the list
; of "relevant-constraints" generated by a :functional-instance lemma-instance
; whose functional substitution is alist.  We return a possibly-modified
; version of new-constraints in order to avoid a kind of variable capture, as
; explained below.

; In Version_3.0.2 we removed a "draconian restriction to avoid capture" that
; had been too aggressive in avoiding this problem, but total removal was also
; too aggressive, as demonstrated by the following proof of nil using
; Version_7.3, the last version with this particular bug.

;   (defun f (n) (declare (ignore n)) 3)
;   (defthm f-thm (equal (f x) 3) :rule-classes nil)
;   (defthm not-true
;     (implies (equal n 3)
;              (equal x 3))
;     :hints (("Goal" :by (:functional-instance
;                          f-thm
;                          (f (lambda (n2) (if (equal n 3) n2 3))))))
;     :rule-classes nil)
;   (defthm ouch
;     nil
;     :hints (("Goal" :use ((:instance not-true (n 3) (x 4)))))
;     :rule-classes nil)

; This example illustrates a kind of variable capture, but not by a lambda.
; Rather, when the functional substitution is naively applied to the constraint
; (equal (f n) 3), the result identifies the distinct variables n and n2 in the
; lambda, to get (equal (if (equal n 3) n 3) 3), which unfortunately is
; provable.  Imagine that instead the constraint on f had been (equal (f k) 3);
; then the result of applying the functional substitution would be (equal (if
; (equal n 3) k 3) 3), which (quite appropriately) is not a theorem.
; Logically, we are substituting into the universal closure of the constraint
; on f.  So there is indeed capture in the example above: we are substituting
; the indicated lambda for f into the formula (forall (n) (equal (f n) 3)), and
; the free variable n of the lambda is captured by the universal quantifier!

; Our solution here is to rename every variable in new-constraints that occurs
; free in some lambda.  We return (mv bad-vars-alist C'), where bad-vars-alist
; is a substitution that contain all pairs (v . v') for which v is renamed to
; v', and C' is the result of applying that substitution to new-constraints.

; We can view this function as providing a modified new-constraints that is
; just an alpha-variant of the original, to which alist can safely be applied
; naively.  When we think of constraint-lst as an alpha-equivalence class of
; universally quantified sentences, it it clear that this renaming not cause a
; problem for our maintenance of world global
; 'proved-functional-instances-alist; just view that global as saying which
; (properly applied) functional instances of the universally quantified formula
; are known to be valid.

          (all-vars1-lst new-constraints nil))
         (fn-subst-free-vars (fn-subst-free-vars alist))
         (bad-vars (intersection-eq new-constraints-vars
                                    fn-subst-free-vars)))
    (cond
     (bad-vars
      (let* ((bad-vars-alist ; rename bad vars to fresh vars
              (fn-subst-renaming-alist bad-vars
                                       fn-subst-free-vars))
             (new-constraints-renamed
              (sublis-var-lst bad-vars-alist new-constraints)))
        (mv bad-vars-alist new-constraints-renamed)))
     (t (mv nil new-constraints)))))

(defun@par translate-lmi/functional-instance (formula constraints event-names
                                                      new-entries substn
                                                      proved-fnl-insts-alist
                                                      ctx wrld state)

; For context, see the Essay on the proved-functional-instances-alist.

; Formula is some term, obtained by previous instantiations.  Constraints are
; the constraints generated by those instantiations -- i.e., if the constraints
; are theorems then formula is a theorem.  Substn is an untranslated object
; alleged to be a functional substitution.

; Provided substn indeed denotes a functional substitution that is ok to apply
; to both formula and the new constraints imposed, we create the functional
; instance of formula and the new constraints to prove.  We return a pair whose
; car is the instantiated formula and whose cdr is the incoming constraints
; appended to the new ones added by this functional instantiation.  Otherwise,
; we cause an error.

  (er-let*@par
   ((alist (translate-functional-substitution@par substn ctx wrld state)))
   (mv-let (new-constraints new-event-names new-new-entries)
     (relevant-constraints formula alist proved-fnl-insts-alist wrld)
     (cond
      ((unknown-constraints-p new-constraints)
       (er@par soft ctx
         "Functional instantiation is disallowed in this context, because the ~
          function ~x0 has unknown-constraints.  See :DOC partial-encapsulate."
         new-event-names))
      (t
       (mv-let (bad-vars-alist new-constraints)

; For many versions through 7.3, we called sublis-fn-rec-lst below without
; possibly modifying new constraints with this call of
; remove-capture-in-constraint-lst.  See a comment in that function for why we
; call it here.  Note that there is no similar issue for substituting into
; formula, whose universal closure is known to be a theorem: conceptually, we
; could first rename free variables in formula to avoid alist, then after
; applying alist to formula, map each renamed variable back to the original.

         (remove-capture-in-constraint-lst alist new-constraints)
         (pprogn@par
          (cond (bad-vars-alist (warning$@par ctx "Capture"
                                  "In order to avoid variable capture, ~
                                   functional instantiation is generating a ~
                                   version of the constraints in which free ~
                                   variables are renamed by the following ~
                                   alist:~|~x0"
                                  bad-vars-alist))
                (t (state-mac@par)))
          (let ((allow-freevars-p
                 #-:non-standard-analysis
                 t
                 #+:non-standard-analysis
                 (classical-fn-list-p (all-fnnames formula) wrld)))
            (mv-let
              (erp0 formula0)
              (sublis-fn-rec alist formula nil allow-freevars-p)
              (mv-let
                (erp new-constraints0)
                (cond (erp0 (mv erp0 formula0))
                      (t (sublis-fn-rec-lst alist new-constraints nil
                                            allow-freevars-p)))
                (cond
                 (erp

; The following message is surprising in a situation where a variable is
; captured by a binding to itself, since for example (let ((x x)) ...)
; translates and then untranslates back to (let () ...).  Presumably we could
; detect such cases and not consider them to be captures.  But we keep it
; simple and simply expect and hope that such a misleading message is never
; actually seen by a user.

                  (er@par soft ctx
                    (if allow-freevars-p
                        "Your functional substitution contains one or more ~
                         free occurrences of the variable~#0~[~/s~] ~&0 in ~
                         its range. ~ Alas, ~#1~[this variable occurrence ~
                         is~/these variables occurrences are~] bound in a LET ~
                         or MV-LET expression of ~#2~[the formula you wish to ~
                         functionally instantiate, ~p3.~|~/the constraints ~
                         that must be relieved.  ~]You must therefore change ~
                         your functional substitution so that it avoids such ~
                         ``capture.''  It will suffice for your functional ~
                         substitution to stay clear of all the variables ~
                         bound by a LET or MV-LET expression that are used in ~
                         the target formula or in the corresponding ~
                         constraints.  Thus it will suffice for your ~
                         substitution not to contain free occurrences of ~v4 ~
                         in its range, by using fresh variables instead.  ~
                         Once you have fixed this problem, you can :use an ~
                         :instance of your :functional-instance to bind the ~
                         fresh variables to ~&4."

; With allow-freevars-p = nil, it is impossible for free variables to be
; captured, since no free variables are allowed.

                      "Your functional substitution contains one or more free ~
                       occurrences of the variable~#0~[~/s~] ~&0 in its ~
                       range. Alas, the formula you wish to functionally ~
                       instantiate is not a classical formula, ~p3.  Free ~
                       variables in lambda expressions are only allowed when ~
                       the formula to be instantiated is classical, since ~
                       these variables may admit non-standard values, for ~
                       which the theorem may be false.")
                    (merge-sort-symbol< erp)
                    erp
                    (if erp0 0 1)
                    (untranslate formula t wrld)
                    (bound-vars-lst (cons formula new-constraints)
                                    nil)))
                 (t (value@par
                     (list formula0
                           (append constraints new-constraints0)
                           (union-equal new-event-names event-names)
                           (union-equal new-new-entries
                                        new-entries)))))))))))))))

; We are trying to define termination-theorem-clauses, but for that, we need
; termination-machines.  The latter was originally defined in defuns.lisp, but
; we move it and supporting definitions here.

(defrec tests-and-call (tests call) nil)

; In nqthm this record was called TEST-AND-CASE and the second component was
; the arglist of a recursive call of the function being analyzed.  Because of
; the presence of mutual recursion, we have renamed it tests-and-call and the
; second component is a "recursive" call (possibly mutually recursive).

(mutual-recursion

(defun all-calls (names term alist ans)

; Names is a list of defined function symbols.  We accumulate into ans all
; terms u/alist such that for some f in names, u is a subterm of term that is a
; call of f.  The algorithm just explores term looking for calls, and
; instantiate them as they are found.

; Our answer is in reverse print order (displaying lambda-applications
; as LETs).  For example, if a, b and c are all calls of fns in names,
; then if term is (foo a ((lambda (x) c) b)), which would be printed
; as (foo a (let ((x b)) c)), the answer is (c b a).

  (cond ((variablep term) ans)
        ((fquotep term) ans)
        ((flambda-applicationp term)
         (all-calls names
                    (lambda-body (ffn-symb term))
                    (pairlis$ (lambda-formals (ffn-symb term))
                              (sublis-var-lst alist (fargs term)))
                    (all-calls-lst names (fargs term) alist ans)))
        ((and (eq (ffn-symb term) 'return-last)
              (quotep (fargn term 1))
              (eq (unquote (fargn term 1)) 'mbe1-raw))
         (all-calls names (fargn term 3) alist ans))
        (t (all-calls-lst names
                          (fargs term)
                          alist
                          (cond ((member-eq (ffn-symb term) names)
                                 (add-to-set-equal
                                  (sublis-var alist term)
                                  ans))
                                (t ans))))))

(defun all-calls-lst (names lst alist ans)
  (cond ((null lst) ans)
        (t (all-calls-lst names
                          (cdr lst)
                          alist
                          (all-calls names (car lst) alist ans)))))

)

(defun all-calls-alist (names alist ans)

; This function processes an alist and computes all the calls of fns
; in names in the range of the alist and accumulates them onto ans.

  (cond ((null alist) ans)
        (t (all-calls-alist names (cdr alist)
                            (all-calls names (cdar alist) nil ans)))))

(defun termination-machine1 (tests calls ans)

; This function makes a tests-and-call with tests tests for every call
; in calls.  It accumulates them onto ans so that if called initially
; with ans=nil the result is a list of tests-and-call in the reverse
; order of the calls.

  (cond ((null calls) ans)
        (t (termination-machine1 tests
                                 (cdr calls)
                                 (cons (make tests-and-call
                                             :tests tests
                                             :call (car calls))
                                       ans)))))

(mutual-recursion

; This clique is identical to the ffnnamesp/ffnnamesp-lst clique, except that
; here we assume that every element of fns is a symbol.

(defun ffnnamesp-eq (fns term)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (ffnnamesp-eq fns (lambda-body (ffn-symb term)))
             (ffnnamesp-eq-lst fns (fargs term))))
        ((member-eq (ffn-symb term) fns) t)
        (t (ffnnamesp-eq-lst fns (fargs term)))))

(defun ffnnamesp-eq-lst (fns l)
  (if (null l)
      nil
    (or (ffnnamesp-eq fns (car l))
        (ffnnamesp-eq-lst fns (cdr l)))))

)

(defun member-eq-all (a lst)
  (or (eq lst :all)
      (member-eq a lst)))

(defconst *equality-aliases*

; This constant should be a subset of *definition-minimal-theory*, since we do
; not track the corresponding runes in simplify-tests and related code below.

  '(eq eql =))

(defun term-equated-to-constant (term)
  (case-match term
    ((rel x y)
     (cond ((or (eq rel 'equal)
                (member-eq rel *equality-aliases*))
            (cond ((quotep x) (mv y x))
                  ((quotep y) (mv x y))
                  (t (mv nil nil))))
           (t (mv nil nil))))
    (& (mv nil nil))))

; We now develop the code for eliminating needless tests in tests-and-calls
; records, leading to function simplify-tests-and-calls-lst.  See the comment
; there.  Term-equated-to-constant appears earlier, because it is used in
; related function simplify-clause-for-term-equal-const-1.

(defun term-equated-to-constant-in-termlist (lst)
  (cond ((endp lst)
         (mv nil nil))
        (t (mv-let
            (var const)
            (term-equated-to-constant (car lst))
            (cond (var (mv var const))
                  (t (term-equated-to-constant-in-termlist (cdr lst))))))))

(defun simplify-tests (var const tests)

; For a related function, see simplify-clause-for-term-equal-const-1.

  (cond ((endp tests)
         (mv nil nil))
        (t (mv-let (changedp rest)
                   (simplify-tests var const (cdr tests))
                   (mv-let (flg term)
                           (strip-not (car tests))
                           (mv-let (var2 const2)
                                   (term-equated-to-constant term)
                                   (cond ((and flg
                                               (equal var var2)
                                               (not (equal const const2)))
                                          (mv t rest))
                                         (changedp
                                          (mv t (cons (car tests) rest)))
                                         (t
                                          (mv nil tests)))))))))

(defun add-test-smart (test tests)
; For a related function, see add-literal-smart.
  (mv-let (term const)
          (term-equated-to-constant test)
          (cons test
                (cond
                 (term
                  (mv-let (changedp new-tests)
                          (simplify-tests term const tests)
                          (if changedp
                              new-tests
                              tests)))
                 (t tests)))))

; Essay on Choking on Loop$ Recursion

; Several system functions, e.g., termination-machine, termination-machines,
; termination-theorem-clauses, and putprop-recursivep-lst have changed so that
; they anticipate the possibility of recursive calls inside quoted lambda
; objects.  This is necessary to support recursion in loop$ statements.  But
; these system functions are sometimes called directly in user-authored books.
; We do not want to be responsible for correcting those books.  So our
; functions that deal with loop$ recursion -- at least, those of our functions
; that are sometimes used directly by users -- have been modified to check
; whether loop$ recursion is present and to cause a hard error.  We call this
; ``choking on loop$ recursion.''  However, a difficulty is that some of our
; functions do not take world as an argument and so cannot actually implement
; the check properly!  For example, loop$ recursion requires a singly-recursive
; defun with an xargs declaration of loop$-recursion t, but the old definition
; of termination-machine can't see the declarations.  Furthermore, if
; loop$-recursion t is declared, every lambda in the body must be well-formed
; and that is checked by chk-acceptable-defuns1 before termination-machine ever
; sees the definition.  But termination-machine doesn't take the world and so
; can't check well-formedness and thus it can't really explore the body of the
; quoted lambda object looking for recursive calls.  So our choke detector is
; conservative and does a tree-occur-eq looking for the fn symbol in the
; ``body'' of the evg.

; As a final twist, choke detection slows us down.  So functions outfitted with
; the choke detection have been given a new argument, loop$-recursion-checkedp,
; which if T means the choke detection is skipped because, supposedly, the
; caller has done all the necessary well-formedness checks.  This extra
; argument, of course, breaks books that call such system functions.  That's by
; design.  The regression will fail and we'll find them.  But rather than fix
; them properly -- i.e., rather than figuring out how that user's book ought to
; handle loop$ recursion -- we just add the loop$-recursion-checkedp argument
; and set it to NIL, meaning choke detection is run.

; Loop$-recursion, a different but similarly named flag, has the value declared
; in the :loop$-recursion xarg.  If non-nil it means loop$ recursion is
; permitted and present!  If NIL it means loop$ recursion is prohibited and
; doesn't occur.  But it is only valid if loop$ recursion has been checked.

; Note that loop$-recursion-checkedp does not mean that loop$ recursion is
; present!  It just means that the bodies have passed the tests in
; chk-acceptable-defuns1.  What this really means is that the function being,
; e.g., termination-machine, is being called from within our own source code,
; where we know definitions have been checked thoroughly before other
; processing occurs.  But a user might call these system functions and there we
; advise the user to call them with loop$-recursion-checkedp nil.  That forces
; the check.  Meanwhile, back in our own code, the choke check is never done
; and we just proceed.  Note also that if the similarly named flag
; loop$-recursion is t we know not only that loop$ recursion is allowed but
; that it actually happens somewhere in the body.

; Our convention is that any of our functions that involves loop$-recursion and
; is called in a user's book must have a loop$-recursion-checkedp argument that
; if nil means that the function must call the choke detector.  If a user book
; calls one of these functions without the proper number of arguments we will
; get a syntax error if the user's call is in a :program or :logic mode
; function.  But if it is in a raw function, no compile error may be detected.
; The result (at least in ccl) is often a runtime memory error and a print out
; of the call stack.  That print out will show (somewhere) the offending
; function which is called with insufficient arguments.

(mutual-recursion

(defun choke-on-loop$-recursion1 (fn term sysfn)
  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   ((flambdap (ffn-symb term))
    (or (choke-on-loop$-recursion1 fn (lambda-body (ffn-symb term)) sysfn)
        (choke-on-loop$-recursion1-lst fn (fargs term) sysfn)))
   ((and (loop$-scion-style (ffn-symb term))
         (quotep (fargn term 1))
         (consp (unquote (fargn term 1))))
; This is a loop$ scion call on a quoted cons.  So this might be a loop$ scion
; call on a quoted lambda.  But the lambda may not be well-formed and because
; we do not have access to world, we can't check.  So we just see whether fn
; occurs anywhere in the ``body'' of the ``lambda.''

    (cond ((tree-occur-eq fn (lambda-object-body (unquote (fargn term 1))))
           (er hard 'choke-on-loop$-recursion
               "It appears that the ACL2 system function ~x0 has been called ~
                inappropriately on a function body that engages in loop$ ~
                recursion.  In particular, ~x1 in the body of ~x2 looks like ~
                a call of a translated LOOP$ statement that recursively calls ~
                ~x2.  (We can't be sure because we do not have enough ~
                contextual information so we have been conservative in our ~
                defensive check!)  Recursion in quoted LAMBDA constants was ~
                disallowed when LOOP$ was first introduced but has since been ~
                allowed.  We suspect some user-managed book calls ~x0 without ~
                having been updated to anticipate the possibility of ~
                recursion inside quoted LAMBDA objects!"
               sysfn term fn))
          (t (choke-on-loop$-recursion1-lst fn (fargs term) sysfn))))
   (t (choke-on-loop$-recursion1-lst fn (fargs term) sysfn))))

(defun choke-on-loop$-recursion1-lst (fn terms sysfn)
  (cond ((endp terms) nil)
        (t (or (choke-on-loop$-recursion1 fn (car terms) sysfn)
               (choke-on-loop$-recursion1-lst fn (cdr terms) sysfn)))))
)

(defun choke-on-loop$-recursion (loop$-recursion-checkedp names body sysfn)

; See the Essay on Choking on Loop$ Recursion above.  We can skip the choke
; detector if loop$ recursion has already been exposed (i.e., removed) or if
; there is more than one fn in names (meaning this is a mutual-recursion which
; disallows loop$-recursion).  This function either causes a hard error or
; returns nil.

  (cond ((or loop$-recursion-checkedp
             (cdr names))
         nil)
        (t (choke-on-loop$-recursion1
            (car names)
            body
            sysfn))))

; Essay on the Measure Conjectures for Loop$ Recursion

; If a function, fn, with formals (v1 ... vn) and body fn-body contains
; recursive calls of fn in translated loop$ statements, those calls are hidden
; because they are in quoted lambda objects.  But the termination machine
; generated for fn must expose these hidden calls, along with ruling
; hypotheses, include the hypothesis explaining the iteration over the
; target(s).

; In this essay we show two generic examples, one for plain loop$s and one for
; fancy loop$s.

; Recall we has been guaranteed by chk-acceptable-defuns1: First, EVERY QUOTED
; LAMBDA OBJECT IN IT IS WELL-FORMED, so we can treat the bodies like terms.
; Second, the lambda provided for a plain loop has exactly one formal and the
; lambda for a fancy loop has two.  Third, all recursive calls of fn in quoted
; lambdas are in loop$ scions, so we don't have to look anywhere else.  Fourth,
; there is at least one loop$ scion containing a recursive call, so we know fn
; is recursive.  Also note that while we expect that almost all loop$ scion
; calls will be generated by translate from loop$ statements -- and thereby
; have very well-defined if complicated structural markings --we cannot count
; on that!  Termination analysis must work even for well-formed calls of loop$
; scions hand-written by the user.  So we do not look for translated loops,
; just loop$ scion calls on quoted lambdas.

; Dealing with Plain Loop$s

; The most general form of a :plain loop$ scion calls approved by
; chk-acceptable-defuns1 is:

; (sum$ '(lambda (e) <dcl> lam-body) target)

; where the <dcl> is optional.  Without loss of generality, assume lam-body has
; been beta reduced so there are no ACL2 lambda expressions in it.

; Suppose fn-body contains such a loop$ scion call ruled by hyps1, and that
; within lam-body there is an occurrence of (fn d1 ... dn) ruled by hyps2.
; Note that the only free variable in hyp2 and in the di is e.  But also
; realize that e might occur outside the lambda, i.e., as a formal of fn and
; thus in hyps1.  Let e' be a new variable that does not occur in hyps1, and
; let s be the substitution {e <-- e'}.  Then the measure conjecture generated
; for that recursive call in lam-body is:

; (implies (and hyps1
;               (member-equal e' target)
;               hyps2/s)
;          (rel (m d1 ... dn)/s (m v1 ... vn)))

; Note that the only free variable in hyp2 and in the di is e and we rename e
; to be e' to avoid conflating uses of e outside the lambda (i.e., in hyps1)
; from those inside.  We illustrate that problem in a separate section of this
; essay below.

; Note also that we must generate the measure conjectures arising from
; recursive calls in target as well!

; Dealing with Fancy Loop$s

; The most general form of a :fancy loop$ scion call approved by
; chk-acceptable-defuns1 is:

; (SUM$+ '(LAMBDA (gv iv) <dcl> lam-body)
;        globals
;        target)

; Again assume lam-body has been beta reduced.  Suppose that hyp1 rules the
; loop$ scion call and that within lam-body is a recursive call (fn d1 ... dn)
; ruled by hyps2.  Note that the only free vars in lam-body are gv and iv.  But
; gv is always bound to globals as the fancy loop$ scion iterates across
; target.  Meanwhile, iv might occur outside the lambda and must be renamed.
; So iv' be a new variable not occuring in hyps1 and let s be the substitution
; {gv <-- globals, iv <-- iv'}.  Then the measure conjecture generated for this
; call of (fn d1 ... dn) in lam-body is

; (implies (and hyps1
;               (member-equal e' target)
;               hyps2/s)
;          (rel (m d1 ... dn)/s (m v1 ... vn)))

; Note also that we must generate the measure conjectures for both globals and
; target.

; Caveat about the Beta Reduction Assumption:  In the implementation we do not
; actually beta reduce lam-body all at once but instead carry along a substitution
; and beta reduce as we explore lam-body for recursive calls.

; The Treachery of Variable Capture

; Below is an example of maximal variable confusion for a plain loop.  First we
; introduce some warranted functions that ought to be just stubbed out.

; (encapsulate nil
;   (defun$ hyp1 (x) (equal x 1))
;   (defun$ hyp2 (x) (equal x 1))
;   (defun$ hyp3 (x) (equal x 1))
;   (defun$ fn1 (x) x)
;   (defun$ fn2 (x) x)
;   (defun$ fn3 (x) x)
;   (defun$ fn4 (x) x)
;   (defun$ fn5 (x) x)
;   (defun$ fn6 (x) x)
;   (in-theory (disable hyp1 hyp2 hyp3 fn1 fn2 fn3 fn4 fn5 fn6)))

; The defun below will fail.  The column of comments renames the iteration
; variables as termination-machine-rec will, and exhibits the beta reduced
; versions of the corresponding let bindings and relevant terms on the line.

; (defun fee (e)
;   (declare (xargs :loop$-recursion t
;                   :measure (acl2-count e)))
;   (if (hyp1 e)
;       (let ((e (fn1 e)))
;         (loop$ for e in (fn2 e)                 ; nv0 in (fn2 (fn1 e))
;                sum
;                (let ((e (fn3 e)))               ; (e (fn3 nv0))
;                  (if (hyp2 e)                   ; (hyp2 (fn3 nv0))
;                      (loop$ for e in (fn4 e)    ; nv1 in (fn4 (fn3 nv0))
;                             sum
;                             (let ((e (fn5 e)))  ; (e (fn5 nv1))
;                               (if (hyp3 e)      ; (hyp3 (fn5 nv1))
;                                   (fee (fn6 e)) ; (fee (fn6 (fn5 nv1)))
;                                   0)))
;                      0))))
;       0))

; Here is the generated measure conjecture:

; (IMPLIES (AND (HYP1 E)
;               (MEMBER-EQUAL NV0 (FN2 (FN1 E)))
;               (HYP2 (FN3 NV0))
;               (MEMBER-EQUAL NV1 (FN4 (FN3 NV0)))
;               (HYP3 (FN5 NV1)))
;          (O< (ACL2-COUNT (FN6 (FN5 NV1)))
;              (ACL2-COUNT E))))

; Note how screwed up it would be if we used the user's names for the
; iteration variables, i.e., if we replaced NV0 and NV1 both by E.

; Enough said?

; An Example of a Fancy Loop$'s Measure Conjecture

; Execute the encapsulate above to get a bunch of disabled warranted stub-like
; functions.  Then consider:

; (defun fum (g x)
;   (declare (xargs :loop$-recursion t
;                   :measure (acl2-count x)))
;   (if (and (consp x)
;            (hyp1 g))
;       (loop$ for e1 in (fn1 x) as e2 in (fn2 x)
;              collect
;              (if (hyp2 (nth g e1))
;                  (fn3 (fum (fn4 g) (nth g e2)))
;                  nil))
;       x))

; The measure conjecture is:

; (IMPLIES (AND (AND (CONSP X)
;                    (HYP1 G))
;               (MEMBER-EQUAL NV0 (LOOP$-AS (LIST (FN1 X) (FN2 X))))
;               (HYP2 (NTH (CAR (LIST G)) (CAR NV0))))
;          (O< (ACL2-COUNT (NTH (CAR (LIST G)) (CADR NV0)))
;              (ACL2-COUNT X)))

; The (CAR (LIST G)) is, of course, immediately simplified to G so we get

; (IMPLIES (AND (AND (CONSP X)
;                    (HYP1 G))
;               (MEMBER-EQUAL NV0 (LOOP$-AS (LIST (FN1 X) (FN2 X))))
;               (HYP2 (NTH G (CAR NV0))))
;          (O< (ACL2-COUNT (NTH G (CADR NV0)))
;              (ACL2-COUNT X)))

(mutual-recursion

(defun all-loop$-scion-quote-lambdas (term alist)

; We collect every subterm of term/alist that is a call of a loop$ scion on a
; quoted lambda and that is not within another such call.

  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   ((flambda-applicationp term)
    (union-equal
     (all-loop$-scion-quote-lambdas-lst (fargs term) alist)
     (all-loop$-scion-quote-lambdas
      (lambda-body (ffn-symb term))
      (pairlis$ (lambda-formals (ffn-symb term))
                (sublis-var-lst alist
                                 (fargs term))))))
   ((and (loop$-scion-style (ffn-symb term))
         (quotep (fargn term 1))
         (consp (unquote (fargn term 1)))
         (eq (car (unquote (fargn term 1))) 'lambda))

; We pay the price of instantiatiating the loop$ scion term now with the alist
; even though it might not have any recursions in it.  C'est la vie.

    (list (sublis-var alist term)))
   (t (all-loop$-scion-quote-lambdas-lst (fargs term) alist))))

(defun all-loop$-scion-quote-lambdas-lst (terms alist)
  (cond ((endp terms) nil)
        (t (union-equal
            (all-loop$-scion-quote-lambdas (car terms) alist)
            (all-loop$-scion-quote-lambdas-lst (cdr terms) alist)))))

)

(mutual-recursion

(defun termination-machine-rec (loop$-recursion
                                names body alist tests
                                ruler-extenders avoid-vars)

; This function is only called if loop$-recursion-checkedp is t, i.e., we have
; run well-formedness checks on body.  The first argument above, the similarly
; named variable loop$-recursion, if t, means that names is a singleton list
; and that body actually exhibits loop$ recursion somewhere.

; It is admittedly odd that `names' is a plural noun (and when loop$-recursion
; is t, is a singleton list of function names) whereas `body' is singular (and
; is the body of the only function listed in names).  The reason is that when
; loop$-recursion is nil names may be a list of all the functions in a
; mutually-recursive clique with the one defined by body and a call of any of
; the functions in names constitutes recursion.

; This function builds a list of tests-and-call records for all calls in body
; of functions in names, but substituting alist into every term in the result.
; At the top level, body is the body of a function in names and alist is nil.
; Note that we don't need to know the function symbol to which the body
; belongs; all the functions in names are considered "recursive" calls.  Names
; is a list of all the mutually recursive fns in the clique.  Alist maps
; variables in body to actuals and is used in the exploration of lambda
; applications.

; For each recursive call in body a tests-and-call is returned whose tests are
; all the tests that "rule" the call and whose call is the call.  If a rules b
; then a governs b but not vice versa.  For example, in (if (g (if a b c)) d e)
; a governs b but does not rule b.  The reason for taking this weaker notion of
; governance is that we can show that the tests-and-calls are together
; sufficient to imply the tests-and-calls generated by induction-machine.  The
; notion of "rules" is extended by ruler-extenders; see :doc
; acl2-defaults-table and see :doc ruler-extenders.

; If loop$-recursion is non-nil and body is a loop$ scion call on a quoted
; lambda (sum$ '(lambda ...) lst) then we know that the lambda is well-formed
; (by the implicit loop$-recursion-checkedp = t mentioned above) and we look
; for recursive calls inside the body of that lambda.  Furthermore, we generate
; a new variable (i.e., not in avoid-vars), add it to avoid-vars, throw away
; alist and replace it with one that binds the locals of the lambda to the new
; variable, and add a ruling test that the value of this new variable is a
; member of the target, lst.

  (cond
   ((or (variablep body)
        (fquotep body))
    nil)
   ((flambda-applicationp body)
    (let ((lambda-body-result
           (termination-machine-rec loop$-recursion
                                    names
                                    (lambda-body (ffn-symb body))
                                    (pairlis$ (lambda-formals (ffn-symb body))
                                              (sublis-var-lst alist
                                                              (fargs body)))
                                    tests
                                    ruler-extenders
                                    avoid-vars)))
      (cond
       ((member-eq-all :lambdas ruler-extenders)
        (union-equal (termination-machine-rec-for-list loop$-recursion
                                                       names
                                                       (fargs body)
                                                       alist
                                                       tests
                                                       ruler-extenders
                                                       avoid-vars)
                     lambda-body-result))
       (t
        (append
         (termination-machine1
          (reverse tests)
          (all-calls-lst names
                         (fargs body)
                         alist
                         nil)
          (termination-machine-rec-for-list
           loop$-recursion
           names
           (all-loop$-scion-quote-lambdas-lst (fargs body) alist)
           alist
           tests
           ruler-extenders
           avoid-vars))
         lambda-body-result)))))
   ((eq (ffn-symb body) 'if)
    (let* ((inst-test (sublis-var alist

; Since (remove-guard-holders-weak x _) is provably equal to x, the machine we
; generate using it below is equivalent to the machine generated without it.
; It might be sound also to call possibly-clean-up-dirty-lambda-objects (i.e.,
; to call remove-guard-holders instead of remove-guard-holders-weak) so that
; guard holders are removed from quoted lambdas in argument positions with ilk
; :fn (or :fn?), but we don't expect to pay much of a price by playing it safe
; here and in induction-machine-for-fn1.

                                  (remove-guard-holders-weak (fargn body 1)

; Rather than pass (remove-guard-holders-lamp) to the following argument
; through all the recursive calls of termination-machine-rec, or passing it
; from the caller, we use nil.  That's simpler and it probably doesn't much
; matter in practice.  We similarly use nil in other calls of
; remove-guard-holders-weak in this function and in induction-machine-for-fn1.

                                                             nil)))
           (branch-result
            (append (termination-machine-rec loop$-recursion
                                             names
                                             (fargn body 2)
                                             alist
                                             (add-test-smart inst-test tests)
                                             ruler-extenders
                                             avoid-vars)
                    (termination-machine-rec loop$-recursion
                                             names
                                             (fargn body 3)
                                             alist
                                             (add-test-smart
                                              (dumb-negate-lit inst-test)
                                              tests)
                                             ruler-extenders
                                             avoid-vars))))
      (cond
       ((member-eq-all 'if ruler-extenders)
        (append (termination-machine-rec loop$-recursion
                                         names
                                         (fargn body 1)
                                         alist
                                         tests
                                         ruler-extenders
                                         avoid-vars)
                branch-result))
       (t
        (append
         (termination-machine1
          (reverse tests)
          (all-calls names (fargn body 1) alist nil)
          (termination-machine-rec-for-list
           loop$-recursion
           names
           (all-loop$-scion-quote-lambdas (fargn body 1) alist)
           alist
           tests
           ruler-extenders
           avoid-vars))
         branch-result)))))
   ((and (eq (ffn-symb body) 'return-last)
         (quotep (fargn body 1))
         (eq (unquote (fargn body 1)) 'mbe1-raw))

; It is sound to treat return-last as a macro for logic purposes.  We do so for
; (return-last 'mbe1-raw exec logic) both for induction and for termination.
; We could probably do this for any return-last call, but for legacy reasons
; (before introduction of return-last after v4-1) we restrict to 'mbe1-raw.

    (termination-machine-rec loop$-recursion
                             names
                             (fargn body 3) ; (return-last 'mbe1-raw exec logic)
                             alist
                             tests
                             ruler-extenders
                             avoid-vars))
   ((member-eq-all (ffn-symb body) ruler-extenders)
    (let ((rec-call (termination-machine-rec-for-list loop$-recursion
                                                      names (fargs body) alist
                                                      tests ruler-extenders
                                                      avoid-vars)))
      (if (member-eq (ffn-symb body) names)
          (cons (make tests-and-call
                      :tests (reverse tests)
                      :call (sublis-var alist body))
                rec-call)
          rec-call)))
   ((loop$-scion-style (ffn-symb body))
    (let ((style (loop$-scion-style (ffn-symb body)))

; Before we get too carried away with the possibility of loop$ recursion here,
; we need to remember to deal with normal recursion in this term!  This
; collects recursions in the globals and target expressions.

          (normal-ans (termination-machine1 (reverse tests)
                                            (all-calls names body alist nil)
                                            nil)))
      (cond
       ((and loop$-recursion
             (quotep (fargn body 1))
             (consp (unquote (fargn body 1)))
             (eq (car (unquote (fargn body 1))) 'lambda))

; Loop$-recursion may be present in this call of a loop$ scion.  (We can't just
; use ffnnamep to ask because it doesn't look inside of lambda objects that
; might be in the body of this one; furthermore, that information alone
; wouldn't help us since if a recursive call is buried several layers deep in
; loop$ scions we need to generate the newvars and ruling member tests on the
; way down.)  The well-formedness checks done by chk-acceptable-defuns1 ensures
; that every quoted lambda is well-formed, and that every loop$ scion call is
; on a quoted lambda of the right arity (1 or 2 depending on whether its a
; :plain or :fancy loop$ scion).  We need give special attention to those loop$
; scion calls whose quoted lambda contains a recursive call of the fn being
; defined.  And this may be one!

        (cond
         ((eq style :plain)
          (let* ((lamb (unquote (fargn body 1)))
                 (v (car (lambda-object-formals lamb)))

; While we generally follow the convention of calling
; possibly-clean-up-dirty-lambda-objects anytime we're removing guard holders
; we do not do so here because we don't want to think about the effect on
; termination machines, at least not until we see it hurt us.

                 (lamb-body (remove-guard-holders-weak
                             (lambda-object-body lamb)
                             nil))
                 (target (sublis-var alist (fargn body 2)))
                 (newvar (genvar v "NV" 0 avoid-vars))
                 (avoid-vars (cons newvar avoid-vars))
                 (inst-test `(MEMBER-EQUAL
                              ,newvar
                              ,(remove-guard-holders-weak target nil))))
            (append normal-ans
                    (termination-machine-rec loop$-recursion
                                             names
                                             lamb-body
; Note: The only free var in lamb-body is v, so we can ignore the subsitutions
; in alist!
                                             (list (cons v newvar))
                                             (add-test-smart inst-test tests)
                                             ruler-extenders
                                             avoid-vars)
                    (termination-machine-rec-for-list
                     loop$-recursion
                     names
                     (all-loop$-scion-quote-lambdas target alist)
                     alist
                     tests
                     ruler-extenders
                     avoid-vars))))
         ((eq style :fancy)
          (let* ((lamb (unquote (fargn body 1)))
                 (gvars (car (lambda-object-formals lamb)))
                 (ivars (cadr (lambda-object-formals lamb)))
                 (lamb-body (remove-guard-holders-weak
                             (lambda-object-body lamb)
                             nil))
                 (globals (sublis-var alist (fargn body 2)))
                 (target (sublis-var alist (fargn body 3)))
                 (newvar (genvar ivars "NV" 0 avoid-vars))
                 (avoid-vars (cons newvar avoid-vars))
                 (inst-test `(MEMBER-EQUAL
                              ,newvar
                              ,(remove-guard-holders-weak target nil))))
            (append normal-ans
                    (termination-machine-rec loop$-recursion
                                             names
                                             lamb-body
                                             (list (cons gvars globals)
                                                   (cons ivars newvar))
                                             (add-test-smart inst-test tests)
                                             ruler-extenders
                                             avoid-vars)
                    (termination-machine-rec-for-list
                     loop$-recursion
                     names
; The following collects the top-level loop$-scion calls on quoted lambdas in
; the globals and the target of a fancy loop$.
                     (all-loop$-scion-quote-lambdas-lst (cdr (fargs body)) alist)
                     alist
                     tests
                     ruler-extenders
                     avoid-vars))))
         (t normal-ans)))
       (t

; This is a loop$ scion call but not one that could have loop$ recursion in it,
; (except possibly in the non-:FN arguments) so we just return the normal
; answer.

        normal-ans))))
   (t (termination-machine1
       (reverse tests)
       (all-calls names body alist nil)
       (termination-machine-rec-for-list
        loop$-recursion
        names
        (all-loop$-scion-quote-lambdas body alist)
        alist
        tests
        ruler-extenders
        avoid-vars)))))

(defun termination-machine-rec-for-list
  (loop$-recursion names bodies alist tests ruler-extenders avoid-vars)
  (cond ((endp bodies) nil)
        (t (append (termination-machine-rec loop$-recursion
                                            names (car bodies) alist tests
                                            ruler-extenders avoid-vars)
                   (termination-machine-rec-for-list loop$-recursion
                                                     names
                                                     (cdr bodies)
                                                     alist tests
                                                     ruler-extenders
                                                     avoid-vars)))))
)

(defun termination-machine (loop$-recursion-checkedp
                            loop$-recursion
                            names formals body
                            alist tests ruler-extenders)

; See the Essay on Choking on Loop$ Recursion for an explanation of the first
; argument.  See termination-machine-rec for the spec of what this function
; does otherwise.

; Names is the list of all the functions defined in a mutually recursive
; clique, formals is the list of formals of one of those functions and body is
; the body of one of those functions.  We are only interested in formals when
; loop$-recursion-checkedp and loop$-recursion are t, in which case names is a
; singleton containing the name of single function being defined.  In that
; case, we use formals to initialize the list of all variables to avoid.  Note
; that bound variables (e.g., from LET statements) occurring in body will be
; eliminated by the on-the-fly beta reduction.

; Note: formals is irrelevant (as described above) if loop$-recursion-checkedp
; is nil.

  (prog2$
   (choke-on-loop$-recursion loop$-recursion-checkedp
                             names
                             body
                             'termination-machine)
   (termination-machine-rec loop$-recursion
                            names body alist tests ruler-extenders
                            (if (and loop$-recursion-checkedp
                                     loop$-recursion)

; We know names, formals-lst, and bodies are singleton lists and that loop$
; recursion is present.  In this case, we compute the list of all formals and
; all bound vars in the body of the fn being defined.  This is the initial list
; of variable names to avoid when generating newvars for the member-equal hyps
; implicitly ruling recursions hidden in quoted lambdas.

                                formals
                                nil))))

(defun termination-machines (loop$-recursion-checkedp
                             loop$-recursion
                             names arglists bodies ruler-extenders-lst)

; This function builds the termination machine for each function defined in
; names with the corresponding formals in arglists and body in bodies.  A list
; of machines is returned.

; Note: arglists is irrelevant (as implied by the comment in
; termination-machine) if loop$-recursion-checkedp is nil.  Otherwise, it
; should be in 1:1 correspondence with names and bodies.  This function chokes
; on unchecked loop$ recursion, but inherits the call of
; (choke-on-loop$-recursion loop$-recursion-checkedp ...) from
; termination-machine.

  (cond ((null bodies) nil)
        (t (cons (termination-machine loop$-recursion-checkedp
                                      loop$-recursion
                                      names (car arglists) (car bodies)
                                      nil nil
                                      (car ruler-extenders-lst))
                 (termination-machines loop$-recursion-checkedp
                                       loop$-recursion
                                       names (cdr arglists) (cdr bodies)
                                       (cdr ruler-extenders-lst))))))

; Function measure-clauses-for-clique was originally defined in defuns.lisp,
; but we need it here for termination-theorem-clauses.

(defun maybe-add-extra-info-lit (debug-info term clause wrld)
  (cond (debug-info
         (cons (fcons-term* 'not
                            (fcons-term* *extra-info-fn*
                                         (kwote debug-info)
                                         (kwote (untranslate term nil wrld))))
               clause))
        (t clause)))

(defun measure-clause-for-branch (name tc measure-alist rel debug-info wrld)

; Name is the name of some function, say f0, in a mutually recursive
; clique.  Tc is a tests-and-call in the termination machine of f0 and hence
; contains some tests and a call of some function in the clique, say,
; f1.  Measure-alist supplies the measures m0 and m1 for f0 and f1.
; Rel is the well-founded relation we are using.

; We assume that the 'formals for all the functions in the clique have
; already been stored in wrld.

; We create a set of clauses equivalent to

;    tests -> (rel m1' m0),

; where m1' is m1 instantiated as indicated by the call of f1.

  (let* ((f0 name)
         (m0 (cdr (assoc-eq f0 measure-alist)))
         (tests (access tests-and-call tc :tests))
         (call (access tests-and-call tc :call))
         (f1 (ffn-symb call))
         (m1-prime (subcor-var
                    (formals f1 wrld)
                    (fargs call)
                    (cdr (assoc-eq f1 measure-alist))))
         (concl (mcons-term* rel m1-prime m0))
         (clause (add-literal concl
                              (dumb-negate-lit-lst tests)
                              t)))
    (maybe-add-extra-info-lit debug-info call clause wrld)))

(defun split-initial-extra-info-lits (cl hyps-rev)
  (cond ((endp cl) (mv hyps-rev cl))
        ((extra-info-lit-p (car cl))
         (split-initial-extra-info-lits (cdr cl)
                                        (cons (car cl) hyps-rev)))
        (t (mv hyps-rev cl))))

(defun conjoin-clause-to-clause-set-extra-info1 (tags-rev cl0 cl cl-set
                                                          cl-set-all)

; Roughly speaking, we want to extend cl-set-all by adding cl = (revappend
; tags-rev cl0), where tags-rev is the reversed initial prefix of negated calls
; of *extra-info-fn*.  But the situation is a bit more complex:

; Cl is (revappend tags-rev cl0) and cl-set is a tail of cl-set-all.  Let cl1
; be the first member of cl-set, if any, such that removing its initial negated
; calls of *extra-info-fn* yields cl0.  We replace the corresponding occurrence
; of cl1 in cl-set-all by the result of adding tags-rev (reversed) in front of
; cl0, except that we drop each tag already in cl1; otherwise we return
; cl-set-all unchanged.  If there is no such cl1, then we return the result of
; consing cl on the front of cl-set-all.

  (cond
   ((endp cl-set)
    (cons cl cl-set-all))
   (t
    (mv-let
     (initial-extra-info-lits-rev cl1)
     (split-initial-extra-info-lits (car cl-set) nil)
     (cond
      ((equal cl0 cl1)
       (cond
        ((not tags-rev) ; seems unlikely
         cl-set-all)
        (t (cond
            ((subsetp-equal tags-rev initial-extra-info-lits-rev)
             cl-set-all)
            (t
             (append (take (- (length cl-set-all) (length cl-set))
                           cl-set-all)
                     (cons (revappend initial-extra-info-lits-rev
                                      (mv-let
                                       (changedp new-tags-rev)
                                       (set-difference-equal-changedp
                                        tags-rev
                                        initial-extra-info-lits-rev)
                                       (cond
                                        (changedp (revappend new-tags-rev cl0))
                                        (t cl))))
                           (cdr cl-set))))))))
      (t (conjoin-clause-to-clause-set-extra-info1 tags-rev cl0 cl (cdr cl-set)
                                                   cl-set-all)))))))

(defun conjoin-clause-to-clause-set-extra-info (cl cl-set)

; Cl, as well as each clause in cl-set, may start with zero or more negated
; calls of *extra-info-fn*.  Semantically (since *extra-info-fn* always returns
; T), we return the result of conjoining cl to cl-set, as with
; conjoin-clause-to-clause-set.  However, we view a prefix of negated
; *extra-info-fn* calls in a clause as a set of tags indicating a source of
; that clause, and we want to preserve that view when we conjoin cl to cl-set.
; In particular, if a member cl1 of cl-set agrees with cl except for the
; prefixes of negated calls of *extra-info-fn*, it is desirable for the merge
; to be achieved simply by adding the prefix of negated calls of
; *extra-info-fn* in cl to the prefix of such terms in cl1.  This function
; carries out that desire.

  (cond ((member-equal *t* cl) cl-set)
        (t (mv-let (tags-rev cl0)
                   (split-initial-extra-info-lits cl nil)
                   (conjoin-clause-to-clause-set-extra-info1
                    tags-rev cl0 cl cl-set cl-set)))))

(defun measure-clauses-for-fn1 (name t-machine measure-alist rel debug-info
                                     wrld)
  (cond ((null t-machine) nil)
        (t (conjoin-clause-to-clause-set-extra-info
            (measure-clause-for-branch name
                                       (car t-machine)
                                       measure-alist
                                       rel
                                       debug-info
                                       wrld)
            (measure-clauses-for-fn1 name
                                     (cdr t-machine)
                                     measure-alist
                                     rel
                                     debug-info
                                     wrld)))))

(defun measure-clauses-for-fn (name t-machine measure-alist mp rel
                                    measure-debug wrld)

; We form all of the clauses that are required to be theorems for the admission
; of name with the given termination machine and measures.  Mp is the "domain
; predicate" for the well-founded relation rel, or else mp is t meaning rel is
; well-founded on the universe.  (For example, mp is o-p when rel is o<.)  For
; the sake of illustration, suppose the defun of name is simply

; (defun name (x)
;   (declare (xargs :guard (guard x)))
;   (if (test x) (name (d x)) x))

; Assume mp and rel are o-p and o<.  Then we will create clauses equivalent
; to:

;    (o-p (m x))
; and
;    (test x) -> (o< (m (d x)) (m x)).

; Observe that the guard of the function is irrelevant!

; We return a set of clauses which are implicitly conjoined.

  (cond
   ((eq mp t)
    (measure-clauses-for-fn1 name t-machine measure-alist rel
                             (and measure-debug
                                  `(:measure (:relation ,name)))
                             wrld))
   (t (conjoin-clause-to-clause-set-extra-info
       (let ((mp-call (mcons-term* mp (cdr (assoc-eq name measure-alist)))))
         (maybe-add-extra-info-lit (and measure-debug
                                        `(:measure (:domain ,name)))
                                   mp-call
                                   (add-literal mp-call nil t)
                                   wrld))
       (measure-clauses-for-fn1 name t-machine measure-alist rel
                                (and measure-debug
                                     `(:measure (:relation ,name)))
                                wrld)))))

(defun conjoin-clause-sets-extra-info (cl-set1 cl-set2)

; Keep in sync with conjoin-clause-sets.

; It is unfortunate that each clause in cl-set2 is split into a prefix (of
; negated *extra-info-fn* calls) and the rest for EACH member of cl-set1.
; However, we expect the sizes of clause-sets to be relatively modest;
; otherwise presumably the simplifier would choke.  So even though we could
; preprocess by splitting cl-set2 into a list of pairs (prefix . rest), for now
; we'll avoid thus complicating the algorithm (which also could perhaps
; generate extra garbage as it reconstitutes cl-set2 from such pairs).

  (cond ((null cl-set1) cl-set2)
        (t (conjoin-clause-to-clause-set-extra-info
            (car cl-set1)
            (conjoin-clause-sets-extra-info (cdr cl-set1) cl-set2)))))

(defun conjoin-clause-sets+ (debug-info cl-set1 cl-set2)
  (cond (debug-info (conjoin-clause-sets-extra-info cl-set1 cl-set2))
        (t (conjoin-clause-sets cl-set1 cl-set2))))

(defun measure-clauses-for-clique (names t-machines measure-alist mp rel
                                         measure-debug wrld)

; We assume we can obtain from wrld the 'formals for each fn in names.

  (cond ((null names) nil)
        (t (conjoin-clause-sets+
            measure-debug
            (measure-clauses-for-fn (car names)
                                    (car t-machines)
                                    measure-alist mp rel measure-debug wrld)
            (measure-clauses-for-clique (cdr names)
                                        (cdr t-machines)
                                        measure-alist mp rel measure-debug
                                        wrld)))))

(defun termination-theorem-clauses (loop$-recursion-checkedp
                                    loop$-recursion
                                    names arglists bodies measure-alist mp rel
                                    ruler-extenders-lst wrld)

; Observe that arglist is only used in termination-machines, and in that
; function we observe that it is irrelevant if loop$-recursion-checkedp is nil.
; So that holds here too: arglists is irrelevant if loop$-recursion-checkedp is
; nil.  This function inherits the call of (choke-on-loop$-recursion
; loop$-recursion-checkedp ...)  from termination-machines.

  (let ((t-machines (termination-machines loop$-recursion-checkedp
                                          loop$-recursion
                                          names arglists bodies ruler-extenders-lst)))
    (measure-clauses-for-clique names t-machines
                                measure-alist
                                mp rel
                                nil ; measure-debug
                                wrld)))

(defun measure-alist? (names wrld)

; This function either returns an alist associating each name in names with its
; corresponding measure term, or else returns (:FAILED . bad-names) where
; bad-names is a list of all x in names such that x has a measure of the form
; (:? v1 ... vk).

; Warning: Do not be tempted simply to build the full alist, including
; "measures" that are calls of :?, followed by a call of strip-ffn-symbs to
; obtain a list L, followed by a check for assoc of :? into that list.  The
; following example shows that the assoc could cause an error, because L need
; not be an alist.

;   (set-bogus-mutual-recursion-ok t)
;   (skip-proofs (mutual-recursion
;                 (defun f1 (x) (declare (xargs :measure x)) x)
;                 (defun f2 (x) x)))
;   ; The following returns X.
;   (access justification
;           (getpropc 'f1 'justification)
;           :measure)

  (cond ((endp names) nil)
        (t (let* ((fn (car names))
                  (rest (measure-alist? (cdr names) wrld))
                  (bad-names (and (eq (car rest) :FAILED)
                                  (cdr rest)))
                  (just (getpropc fn 'justification nil wrld))
                  (m (assert$ just
                              (access justification just :measure)))
                  (bad (eq (ffn-symb m) :?)))
             (cond (bad-names (if bad
                                  (cons :FAILED (cons fn bad-names))
                                rest))
                   (bad (cons :FAILED (cons fn nil)))
                   (t (acons (car names) m rest)))))))

(defun ruler-extenders-lst (names wrld)
  (cond ((endp names) nil)
        (t (cons (let ((just (getpropc (car names) 'justification nil wrld)))
                   (assert$ just
                            (access justification just :ruler-extenders)))
                 (ruler-extenders-lst (cdr names) wrld)))))

(defun get-unnormalized-bodies (names wrld)
  (cond ((endp names) nil)
        (t (cons (getpropc (car names) 'unnormalized-body nil wrld)
                 (get-unnormalized-bodies (cdr names) wrld)))))

(defun termination-theorem (fn wrld)

; Warning: If you change the formals of this function, consider making a
; corresponding change to guard-or-termination-theorem-msg.

; This function either returns the termination theorem for fn or else returns a
; result (:FAILED . msg) where msg is a message providing a sentence that
; explains why there is no such a theorem.

  (declare (xargs :guard (and (plist-worldp wrld)
                              (symbolp fn)
                              (function-symbolp fn wrld)
                              (logicp fn wrld))))
  (let* ((names (getpropc fn 'recursivep nil wrld))
         (just (and names ; optimization
                    (getpropc fn 'justification nil wrld))))
    (cond
     ((null names)
      (cons :FAILED
            (msg "The function ~x0 is not recursive" fn)))
     ((assert$ just
               (access justification just :subversive-p))
      (cons :FAILED
            (msg "Note that ~x0 is ``subversive.'' See :DOC ~
                  subversive-recursions.  Thus, the termination theorem ~
                  proved when this function was admitted is considered local ~
                  to an enclosing non-trivial encapsulate form"
                 fn)))
     (t
      (let* ((mp (assert$ just
                          (access justification just :mp)))
             (rel (access justification just :rel))
             (measure-alist (measure-alist? names wrld)))
        (cond
         ((eq (car measure-alist) :FAILED)
          (cons :FAILED
                (let ((bad-names (cdr measure-alist)))
                  (assert$
                   bad-names
                   (cond
                    ((consp (cdr bad-names))
                     (msg "The measures specified for ~&0 (mutually recursive ~
                           with ~x1) are \"calls\" of :?, rather than true ~
                           measures"
                          bad-names
                          fn))
                    (t
                     (msg "The measure specified for ~&0~@1 is a \"call\" of ~
                           :?, rather than a true measure"
                          bad-names
                          (cond ((eq (car bad-names) fn)
                                 "")
                                (t
                                 (msg " (which is mutually recursive with ~x0)"
                                      fn))))))))))
         (t
          (let ((clauses
                 (termination-theorem-clauses
                  t ; loop$-recursion-checkedp
                  (if (cdr names)
                      nil
                      (getpropc (car names) 'loop$-recursion nil wrld))
                  names
; Formals, below, is relevant only if there's exactly one name and its
; loop$-recursion property is t.  But we just check the first and pay the price
; of fetching the formals even though we might not need them.

                  (if (cdr names) nil (list (formals (car names) wrld)))
                  (get-unnormalized-bodies names wrld)
                  measure-alist mp rel
                  (ruler-extenders-lst names wrld)
                  wrld)))
            (termify-clause-set clauses)))))))))

; Before completing the implementation of defun we implement support for the
; verify-guards event.  The idea is that one calls (verify-guards name) and we
; will generate the guard conditions for all the functions in the mutually
; recursive clique with name, prove them, and then exploit those proofs by
; resetting their symbol-class.  This process is optionally available as part
; of the defun event and hence we must define it before defun.

; But in fact, we define it here, to support the definition of guard-theorem.

; While reading this code it is best to think of ourselves as having completed
; defun.  Imagine a wrld in which a defun has just been done: the
; 'unnormalized-body is b, the unnormalized 'guard is g, the 'symbol-class is
; :ideal.  The user then calls (verify-guards name) and we want to prove that
; every guard encountered in the mutually recursive clique containing name is
; satisfied.

(defun eval-ground-subexpressions1-lst-lst (lst-lst ens wrld safe-mode gc-off
                                                    ttree hands-off-fns memo)
  (cond ((null lst-lst) (mv nil nil ttree memo))
        (t (mv-let
            (flg1 x ttree memo)
            (eval-ground-subexpressions1-lst (car lst-lst) ens wrld safe-mode
                                             gc-off ttree hands-off-fns memo)
            (mv-let
             (flg2 y ttree memo)
             (eval-ground-subexpressions1-lst-lst (cdr lst-lst) ens wrld
                                                  safe-mode gc-off ttree
                                                  hands-off-fns memo)
             (mv (or flg1 flg2)
                 (if (or flg1 flg2)
                     (cons x y)
                   lst-lst)
                 ttree
                 memo))))))

(defun eval-ground-subexpressions-lst-lst (lst-lst ens wrld state ttree)

; Note: This function does not support hands-off-fns but we could add that as a
; new formal and pass it instead of nil below.

  (mv-let (flg x ttree memo)
    (eval-ground-subexpressions1-lst-lst lst-lst ens wrld
                                         (f-get-global 'safe-mode state)
                                         (gc-off state)
                                         ttree
                                         nil ; hands-off-fns
                                         nil ; memo
                                         )
    (declare (ignore memo))
    (mv flg x ttree)))

(defun sublis-var-lst-lst (alist clauses)
  (cond ((null clauses) nil)
        (t (cons (sublis-var-lst alist (car clauses))
                 (sublis-var-lst-lst alist (cdr clauses))))))

(defun add-segments-to-clause (clause segments)
  (cond ((null segments) nil)
        (t (conjoin-clause-to-clause-set
            (disjoin-clauses clause (car segments))
            (add-segments-to-clause clause (cdr segments))))))

(defun simplify-clause-for-term-equal-const-1 (var const cl)

; This is the same as simplify-tests, but where cl is a clause: here we are
; considering their disjunction, rather than the disjunction of their negations
; (i.e., an implication where all elements are considered true).

  (cond ((endp cl)
         (mv nil nil))
        (t (mv-let (changedp rest)
                   (simplify-clause-for-term-equal-const-1 var const (cdr cl))
                   (mv-let (var2 const2)
                           (term-equated-to-constant (car cl))
                           (cond ((and (equal var var2)
                                       (not (equal const const2)))
                                  (mv t rest))
                                 (changedp
                                  (mv t (cons (car cl) rest)))
                                 (t
                                  (mv nil cl))))))))

(defun simplify-clause-for-term-equal-const (var const cl)

; See simplify-clause-for-term-equal-const.

  (mv-let (changedp new-cl)
          (simplify-clause-for-term-equal-const-1 var const cl)
          (declare (ignore changedp))
          new-cl))

(defun add-literal-smart (lit cl at-end-flg)

; This version of add-literal can remove literals from cl that are known to be
; false, given that lit is false.

  (mv-let (term const)
          (cond ((ffn-symb-p lit 'not)
                 (term-equated-to-constant (fargn lit 1)))
                (t (mv nil nil)))
          (add-literal lit
                       (cond (term (simplify-clause-for-term-equal-const
                                    term const cl))
                             (t cl))
                       at-end-flg)))

(mutual-recursion

(defun all-vars!1 (term wrld ans)

; We collect every symbol used as a variable in term, whether it's used freely
; or not.  We also collect all the symbols used as variables in well-formed
; LAMBDA objects, including their guards.

  (declare (xargs :guard (and (pseudo-termp term)
                              (symbol-listp ans))
                  :mode :program))
  (cond ((variablep term)
         (add-to-set-eq term ans))
        ((fquotep term)
         (cond
          ((well-formed-lambda-objectp (unquote term) wrld)
           (let ((obj (unquote term)))
             (all-vars!1 (lambda-object-body obj)
                         wrld
                         (all-vars!1 (lambda-object-guard obj)
                                     wrld
                                     (union-eq (lambda-object-formals (ffn-symb term))
                                               ans)))))
          (t ans)))
        ((flambdap (ffn-symb term))
         (all-vars!1-lst (fargs term)
                         wrld
                         (all-vars!1 (lambda-body (ffn-symb term))
                                     wrld
                                     (union-eq (lambda-formals (ffn-symb term))
                                               ans))))
        (t (all-vars!1-lst (fargs term) wrld ans))))

(defun all-vars!1-lst (lst wrld ans)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (symbol-listp ans))
                  :mode :program))
  (cond ((endp lst) ans)
        (t (all-vars!1-lst (cdr lst)
                           wrld
                           (all-vars!1 (car lst) wrld ans)))))

)

(defun all-vars!-of-fn (fn wrld)

; Warning: fn is either the name of a function defined in wrld or a well-formed
; LAMBDA object.  We return every symbol used somehow as a variable in fn,
; whether bound or free, including those occurring in the guard or body or
; quoted well-formed LAMBDA objects within either.  The only point of this list
; of variables is to allow us to genvar a new variable symbol that is not used
; as a variable in any way in fn.

  (cond
   ((symbolp fn)
    (all-vars!1
     (guard fn nil wrld)
     wrld
     (all-vars!1
      (getpropc fn 'unnormalized-body
                '(:error "See ALL-VARS!-OF-FN.")
                wrld)
      wrld
      (formals fn wrld))))
   (t (all-vars!1
       (lambda-object-guard fn)
       wrld
       (all-vars!1
        (lambda-object-body fn)
        wrld
        (lambda-object-formals fn))))))

; The following block of code culminates in the definition of
; special-conjectures, which generates Special Conjectures (a), (b), (c), (d),
; (e), (f), and (g) described in the Essay on Loop$.  Most of the development
; work below is on Special Conjectures (c).

(defun recover-type-spec-exprs1 (term)

; Term is possibly a nest that looks like this
; (return-last 'progn (check-dcl-guardian guard1 &)
;               (return-last 'progn (check-dcl-guardian guard2 &)
;                             ...
;                             body)).
; Each guardi was generated from a TYPE spec.  We return (guard1 guard2 ...).

  (case-match term
    (('RETURN-LAST ''PROGN ('CHECK-DCL-GUARDIAN guard &) rest)
     (cons guard (recover-type-spec-exprs1 rest)))
    (('CHECK-DCL-GUARDIAN guard &)
     (cons guard nil))
    (& nil)))

(defun recover-type-spec-exprs (term)
  (case-match term
    (('RETURN-LAST ''PROGN ('RETURN-LAST ''PROGN ('CHECK-DCL-GUARDIAN & &) &) &)
     (recover-type-spec-exprs1 (fargn term 2)))
    (('RETURN-LAST ''PROGN ('CHECK-DCL-GUARDIAN guard &) &)
     (list guard))
    (t nil)))

(defun terms-in-var (var terms)
  (cond
   ((endp terms) nil)
   ((occur var (car terms))
    (cons (car terms) (terms-in-var var (cdr terms))))
   (t (terms-in-var var (cdr terms)))))

(defun type-specs-for-var (var type-spec-exprs)
  (conjoin (terms-in-var var type-spec-exprs)))

(defun recover-fancy-targets (term)
  (case-match term
    (('CONS target rest)
     (cons target (recover-fancy-targets rest)))
    (& nil)))

(defun recover-deep-targets (term)

; Dig down into a loop$ scion nest representing a loop$ statement and recover
; the list of targets appearing the original loop$ statement, e.g., from (sum$
; ... (when$ ... (until$ ... target))) recover (list target), or in the case of
; a fancy nest, (target1 target2 ...).  Note also that the length of our answer
; is the number of iteration variables in the loop$ statement.  Note also that
; the length can be 1 even in the case of fancy loop$s.

  (let ((style (and (nvariablep term)
                    (not (fquotep term))
                    (loop$-scion-style (ffn-symb term)))))
    (cond
     ((null style)
      (cond ((and (nvariablep term)
                  (not (fquotep term))
                  (eq (ffn-symb term) 'LOOP$-AS))
             (recover-fancy-targets (fargn term 1)))
            (t (list term))))
     (t (recover-deep-targets
         (if (eq style :plain) (fargn term 2) (fargn term 3)))))))

(defun vars-specs-and-targets1 (vars type-spec-exprs targets)
  (cond
   ((endp vars) nil)
   (t (cons (list (car vars)
                  (type-specs-for-var (car vars) type-spec-exprs)
                  (car targets))
            (vars-specs-and-targets1 (cdr vars) type-spec-exprs (cdr targets))))))

(defun vars-specs-and-targets (scion-term wrld)

; This function is the workhorse for recognizing the need for Special
; Conjectures (c).

; Scion-term is a loop$ scion call of :plain or :fancy style.  Consider the
; loop$ statement from which scion-term arose:

; (loop$ for v1 of-type spec1 in/on/from-to-by target1
;         as v2 of-type spec2 in/on/from-to-by target2
;         ...
;         until ... when ... op ...)

; We return a list of triplets ((v1 spec1-expr target1) ...), listing every
; iteration variable in the loop$ statement that has an of-type specification.
; The speci-expr is the term expressing the type spec, not the type spec
; itself, e.g., (INTEGERP v1) not INTEGER.

; Note that the vi and speci we return are phrased in terms of the actual
; symbols used in the loop$ statement, not the formal(s) of the lambda object
; in the first argument of the scion-term, i.e., the v in (loop$ for v of-type
; (satisfies foop) on (tails lst) collect ...)  not the loop$-ivar in '(lambda
; (loop$-ivar) (let ((v loop$-ivar)) ...)).  So we have to dig into the
; translated lambda object.

; In addition, to recover the targets we have to dig down through UNTIL and
; WHEN terms.  I.e., the :plain scion-term corresponding to a loop$ might be:
; (sum$ ... (when$ ... (until$ ... target))).  Since every LAMBDA object in the
; nest of loop$ scions includes the same type specs, we could get these
; triplets from the innermost term rather than the outermost but it seems
; slightly simpler to do it this way.

; Keep this function in sync with both make-plain-loop$-lambda-object and
; make-fancy-loop$-lambda-object!

; Note on another way to do things:  This function must recognize every
; translated loop$ that uses either ... FROM i TO j ... or ON ... iteration
; because those are the cases that require Special Conjectures (c).
; We may find it too onerous to keep tracking that.  There is another
; way.  Abandon Special Conjecture (c) and instead change the translation of
; those loop$ statements to explicitly include THE terms.  For example,
; instead of translating

; (loop for x of-type spec on lst collect (foo x))

; to

; (collect$ (lambda$ (x) (declare (type spec x)) (foo x)) (tails lst))

; we could translate it to

; (prog2$ (the spec NIL)
;         (collect$ (lambda$ (x) (declare (type spec x)) (foo x)) (tails lst)))

; and instead of translating

; (loop$ for x of-type spec from i to j by k collect (foo x))

; to

; (collect$ (lambda$ (x) (declare (type spec x)) (foo x)) (from-to-by i j k))

; we could use

; (prog2$ (the spec (+ i k (* k (floor (- j i) k))))
;         (collect$ (lambda$ (x) (declare (type spec x)) (foo x))
;                   (from-to-by (the spec i)
;                               (the spec j)
;                               (the spec k))))

; (Of course, the collect$s would be properly tagged as loop$s as now.)

; This translation would obviate the need to recognize the translated terms
; corresponding to such loop$s.

  (cond
   ((and (for-loop$-operator-scionp (ffn-symb scion-term)
                                    *for-loop$-keyword-info*)
         (quotep (fargn scion-term 1))
         (well-formed-lambda-objectp
          (unquote (fargn scion-term 1))
          wrld))
    (let* ((targets (recover-deep-targets scion-term))
           (n (length targets))
           (fn (unquote (fargn scion-term 1))))
      (mv-let (style vars type-spec-exprs)
        (case-match fn
          (('LAMBDA ('LOOP$-IVAR)
                    ('DECLARE . edcls)
                    ('RETURN-LAST ''PROGN
                                  ('QUOTE ('LAMBDA$ ('LOOP$-IVAR) . &))
                                  (('LAMBDA (var) &) 'LOOP$-IVAR)))

; All :plain loop$s translate a scion call on a lambda object matching the
; pattern above, where the original iteration variable is var.  The edcls
; either contains a (TYPE spec LOOP$-IVAR) entry or it doesn't.  If it does,
; the recovered type expression, produced by get-guards2, is expressed in terms
; of LOOP$-IVAR and we need it to be in terms of var.  Recall that get-guards2
; returns a list of pseudo-terms which are not necessarily fully translated,
; but it is legal to perform a subst-var-lst on these pseudo-terms, as per the
; comment in translate-declaration-to-guard1-gen.

           (let ((type-spec (assoc-eq 'TYPE edcls)))
             (cond (type-spec
                    (mv :plain
                        (list var)
                        (list (conjoin
                               (subst-var-lst
                                var
                                'loop$-ivar
                                (get-guards2 `(,type-spec)
                                             '(types)
                                             t wrld nil nil))))))
                   (t (mv :plain (list var) (list *t*))))))
          (('LAMBDA '(LOOP$-GVARS LOOP$-IVARS)
                    ('DECLARE ('XARGS ':GUARD & ':SPLIT-TYPES 'T) . &)
                    ('RETURN-LAST
                     ''PROGN
                     ('QUOTE ('LAMBDA$ . &))
                     (('LAMBDA loop$-gvars-and-loop$-ivars
                               optionally-marked-body)
                      . &)))

; All :fancy loop$s translate to a scion call on a lambda object matching the
; pattern above. The type specs in a translated fancy LAMBDA object do not
; appear in DECLARE forms!  Instead, they are coded as CHECK-DCL-GUARDIAN
; expressions because they appear in a translated LET.  So we need a different
; way to collect them.  See recover-type-spec-exprs.

; Loop$-gvars-and-loop$-ivars is a list of symbols like (G1 G2 G3 L1 L2) where
; the Gi are the (three, in this case) global variables involved in this lambda
; and the Li are the (two) local variables.  We need to recover the names local
; variables, (L1 L2), because they are the original iteration variables.  We
; don't know how many globals there are, but we can figure it out!

           (cond
            ((<= n (length loop$-gvars-and-loop$-ivars))
             (mv :fancy
                 (first-n-ac n
                             (nthcdr
                              (- (length loop$-gvars-and-loop$-ivars) n)
                              loop$-gvars-and-loop$-ivars)
                             nil)
; Note:  None of the gvars have type specs!

                 (recover-type-spec-exprs optionally-marked-body)))
            (t (mv nil nil nil))))
          (& (mv nil nil nil)))
        (cond
         ((eq style nil) nil)
         (t (vars-specs-and-targets1 vars type-spec-exprs targets))))))
   (t nil)))

; This macro tests the extraction of locals and their type-specs from the
; lambdas generated by loop$.  See the er-let* just below for some
; sample calls and their expected returns.

; (defmacro tester (stmt)
;   `(mv-let (erp term bindings)
;      (translate11-loop$ ',stmt '(nil) nil nil nil nil 'tester (w state)
;                         (default-state-vars state))
;      (declare (ignore bindings))
;      (cond
;       (erp (er soft 'tester "~@0" term))
;       (t (value (vars-specs-and-targets
;                  (fargn term 3)
;                  (w state)))))))

; The form below should return (value t).

; (er-let*
;     ((test1
;       (tester
;        (loop$ for x in lst collect x)))
;      (test2
;       (tester
;        (loop$ for x of-type integer in lst collect x)))
;      (test3
;       (tester
;        (loop$ for x of-type (and integer (satisfies evenp)) in lst collect x)))
;      (test4
;       (tester
;        (loop$ for x of-type (and integer (satisfies evenp)) in lst
;               collect :guard (< x 45) x)))
;      (test5
;       (tester
;        (loop$ for x of-type integer in xlst as y in ylst collect (list x y))))
;      (test6
;       (tester
;        (loop$ for x in xlst as y of-type integer in ylst collect (list x y))))
;      (test7
;       (tester
;        (loop$ for x of-type symbol in xlst
;               as y of-type integer in ylst
;               as u in ulst
;               as z of-type rational in zlst
;               when (> y z)
;               collect :guard (> u (+ y z)) (list x y u z a b c))))
;      (test8
;       (tester
;        (loop$ for x of-type (and symbol (not (satisfies null))) in xlst
;               as y of-type (and integer (satisfies evenp)) in ylst
;               as u in ulst
;               as z of-type (and rational (satisfies posp)) in zlst
;               when (> y z)
;               collect :guard (> u (+ y z)) (list x y u z a b c)))))
;   (value (list (equal test1 '((X 'T LST)))
;                (equal test2 '((X (INTEGERP X) LST)))
;                (equal test3
;                       '((X (IF (INTEGERP X) (EVENP X) 'NIL)
;                            LST)))
;                (equal test4
;                       '((X (IF (INTEGERP X) (EVENP X) 'NIL)
;                            LST)))
;                (equal test5
;                       '((X (INTEGERP X) XLST) (Y 'T YLST)))
;                (equal test6
;                       '((X 'T XLST) (Y (INTEGERP Y) YLST)))
;                (equal test7
;                       '((X (SYMBOLP X) XLST)
;                         (Y (INTEGERP Y) YLST)
;                         (U 'T ULST)
;                         (Z (RATIONALP Z) ZLST)))
;                (equal test8
;                       '((X (IF (SYMBOLP X) (NOT (NULL X)) 'NIL)
;                            XLST)
;                         (Y (IF (INTEGERP Y) (EVENP Y) 'NIL)
;                            YLST)
;                         (U 'T ULST)
;                         (Z (IF (RATIONALP Z) (POSP Z) 'NIL)
;                            ZLST))))))

(defun special-conjectures-c2 (clause var type-expr target)
; See special-conjectures-c.
  (cond
   ((equal type-expr *t*) nil)
   (t (case-match target
        (('TAILS &)
         (conjoin-clause-to-clause-set
          (add-literal-smart
           (subst-var *nil* var type-expr)
           clause
           t)
          nil))
        (('FROM-TO-BY i j k)
         (conjoin-clause-to-clause-set
          (add-literal-smart
           (subst-var i var type-expr)
           clause
           t)
          (conjoin-clause-to-clause-set
           (add-literal-smart
            (subst-var j var type-expr)
            clause
            t)
           (conjoin-clause-to-clause-set
            (add-literal-smart
             (subst-var k var type-expr)
             clause
             t)
            (conjoin-clause-to-clause-set
             (add-literal-smart
              (subst-var
               `(BINARY-+ ,i
                          (BINARY-+
                           ,k
                           (BINARY-* ,k
                                     (FLOOR (BINARY-+ ,j (UNARY-- ,i))
                                            ,k))))
               var type-expr)
              clause
              t)
             nil)))))
        (& nil)))))

(defun special-conjectures-c1 (clause vars-specs-and-targets)
; See special-conjectures-c.
  (cond
   ((null vars-specs-and-targets) nil)
   (t (conjoin-clause-sets
       (special-conjectures-c2
        clause
        (car (car vars-specs-and-targets))
        (cadr (car vars-specs-and-targets))
        (caddr (car vars-specs-and-targets)))
       (special-conjectures-c1 clause
                               (cdr vars-specs-and-targets))))))

(defun special-conjectures-c (clause term wrld)

; If term is a loop$ scion term corresponding to the operator of a loop$
; statement, e.g., a call of sum$ or perhaps collect$+ but not a call of when$,
; we get the triplets (vari type-expri targeti) corresponding to the iteration
; variables, their type spec expressions, and their targets, and generate
; Special Conjectures (c) for each one, as a function of each target.

; For a (FROM-TO-BY i j k) target, the generated clauses insist that
; i, j, k, and (+ i (* k (floor (- j i) k)) k) each satisfy the type-expr.

; For a (TAILS lst) target, the generated clauses insist that NIL
; satisfies the type-expr.

; No other targets generate Special Conjectures (c).

  (special-conjectures-c1
   clause
   (vars-specs-and-targets term wrld)))

(defun special-loop$-scion-callp (term wrld)

; We recognize calls of loop$ scions on quoted LAMBDA objects that might have
; come from translations of loop$ statements, e.g.,
; (sum$ (quote (LAMBDA ...)) lst), or
; (when$+ (quote (LAMBDA ...)) globals lst), or
; (do$ measure-fn alist
;      (quote (lambda ...))
;      (quote (lambda ...))
;      xtr1 xtr2)

; Motivation: We generate special guard conjectures for each such a call,
; presuming that it WAS generated by a loop$ and that the loop$ is lying in
; wait in the raw CLTL code of the function whose guards are being verified.
; If the guard conjectures are ultimately verified then the corresponding loop
; will run in raw Lisp and we must be sure no errors will be caused.

; Nothing prevents the user from typing such calls, so we're being over
; protective here: there may be no loop$ in the raw Lisp.  C'est la vie.

; We do not build in much about what such calls look like except that we know
; certain function arguments are a quoted well-formed LAMBDA object of the right
; arity for the style of the loop$ scion.

  (case-match term
    (('do$ & & ('quote obj1) ('quote obj2) & &)
     (and (well-formed-lambda-objectp obj1 wrld)
          (well-formed-lambda-objectp obj2 wrld)
          (equal (length (lambda-object-formals obj1)) 1)
          (equal (length (lambda-object-formals obj2)) 1)))
    ((loop-scion ('quote obj) . &)
     (let ((style (loop$-scion-style loop-scion)))
; Style can't be :DO because we handled that above.
       (and style ; a :plain  or :fancy loop$ scion
            (and (well-formed-lambda-objectp obj wrld)
                 (equal (length (lambda-object-formals obj))
                        (if (eq style :plain) 1 2))))))
    (t nil)))

(mutual-recursion

(defun collect-warranted-fns (term ilk collect-p wrld)

; This function collects a list of function symbols having warrants that may be
; useful in simplifying the given term.

; At the top level collect-p is nil, meaning that we are not collecting
; function symbols.  Collection begins when entering a quoted constant that is
; in an argument position whose ilk is :fn or :expr.

  (declare (xargs :guard (and (plist-worldp wrld)
                              (termp term wrld))))
  (cond ((variablep term) nil)
        ((fquotep term)
         (let ((val (unquote term)))
           (cond ((eq ilk :FN)

; Note: The case-match below is a little odd.  If an ill-formed quoted lambda
; occurred here (car (last val)) might treat the formals as the body, or might
; treat the declare as the body.  But if it collects fns from that object they
; really will have warrants, even though they may completely irrelevant.

                  (cond ((case-match val
                           (('lambda . &) t)
                           (& nil))
                         (let ((body (car (last val))))
                           (and (pseudo-termp body)
                                (collect-warranted-fns body nil t wrld))))
                        ((and (symbolp val)
                              (get-warrantp val wrld))

; We use get-warrantp, above, to determine if val has a warrant function.
; Every function with a warrant is so marked in the :badge-userfn-structure of
; the badge-table.  All other functions known to apply$, e.g., primitives and
; boot functions, have no warrants.

                         (list val))
                        (t nil)))
                 ((eq ilk :EXPR)
                  (and (pseudo-termp val)
                       (collect-warranted-fns val nil t wrld)))
                 (t nil))))
        ((flambda-applicationp term)
         (union-equal
          (collect-warranted-fns (lambda-body (ffn-symb term)) nil collect-p
                                 wrld)
          (collect-warranted-fns-lst (fargs term) nil collect-p wrld)))
        ((member-eq (ffn-symb term) '(apply$ ev$))
         (collect-warranted-fns-lst
          (fargs term)
          (access apply$-badge
                  (executable-badge (ffn-symb term) wrld)
                  :ilks)
          collect-p wrld))
        (t (mv-let (badge warrantp)
             (get-badge-and-warrantp (ffn-symb term) wrld)
; If warrantp is t, there is a badge, not not vice versa.
             (cond
              (warrantp
               (let* ((ilks0 (access apply$-badge badge :ilks))
                      (ilks (if (eq ilks0 t) nil ilks0))
                      (fns (collect-warranted-fns-lst (fargs term) ilks
                                                      collect-p wrld)))
                 (cond (collect-p (add-to-set-equal (ffn-symb term) fns))
                       (t fns))))
              (t
               (collect-warranted-fns-lst (fargs term) nil collect-p
                                          wrld)))))))

(defun collect-warranted-fns-lst (lst ilks collect-p wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (term-listp lst wrld))))
  (cond ((endp lst) nil)
        (t (union-equal
            (collect-warranted-fns (car lst) (car ilks) collect-p wrld)
            (collect-warranted-fns-lst (cdr lst) (cdr ilks) collect-p wrld)))))
)

(defun collect-negated-warrants1 (lst clause)

; Lst is a list of function names, each of which is known to have a warrant
; function.

  (cond ((endp lst) clause)
        ((equal clause *true-clause*) clause)
        (t (collect-negated-warrants1
            (cdr lst)
            (add-literal (fcons-term* 'not
                                      (fcons-term* (warrant-name (car lst))))
                         clause

; It's perhaps a bit inefficient to add to the end every time, but that seems
; the most natural way to get the desired functionality (see the discussion
; about Special Conjecture (b) in the Essay on Loop$).

                         t)))))

(defun collect-negated-warrants (term wrld clause)
  (collect-negated-warrants1 (collect-warranted-fns term nil nil wrld)
                             clause))

(defun add-literals (cl1 cl2)

; Add each literal of cl1 to cl2, maintaining order but dropping redundancies
; and detecting tautologies.  We assume there are no redundancies or
; contradictions in cl1 or cl2 individually.

  (cond ((endp cl1) cl2)
        (t (add-literal (car cl1)
                        (add-literals (cdr cl1) cl2)
                        nil))))

(defun special-conjectures (clause term wrld newvar ttree)

; Clause is an evolving clause governing an occurrence of term with derivation
; ttree.  Term may or may not be a call of a special loop$ scionp.  If it is
; and newvar is non-nil, we generate and return the list of special loop$ guard
; clauses appropriate for term, together with ttree, (mv clauses ttree').  Else
; we return (mv nil ttree).  Newvar is the new variable used in the special for
; loop$ guard clauses.  Newvar is only non-nil when this function is called on
; functions or lambdas being defined.  Newvar is nil when we're generating
; guards for theorems and ordinary terms.

; Note: As of this writing, ttree is just passed through and returned; it is
; not used or modified.

; See the Essay on Loop$ for an explanation of Special Conjectures (a), (b),
; (c) for FOR loop$s and (d), (e), (f), and (g) for DO loop$s.

  (cond
   ((null newvar) (mv nil ttree))
   ((special-loop$-scion-callp term wrld)
    (let* ((style (loop$-scion-style (ffn-symb term)))
; We need both the warrants hypotheses as a clause by itself and we need its
; union with the incoming clause.
           (warrant-hyps (collect-negated-warrants term wrld nil))
           (warranted-clause (add-literals warrant-hyps clause)))
      (cond
       ((eq style :do)
        (let* ((m-fn (unquote (fargn term 1)))
               (initial-alist (fargn term 2))
               (do-fn (unquote (fargn term 3)))
               (do-fn-var (car (lambda-object-formals do-fn)))
               (do-fn-guard (lambda-object-guard do-fn))
               (fin-fn (unquote (fargn term 4)))
               (fin-fn-var (car (lambda-object-formals fin-fn)))
               (fin-fn-guard (lambda-object-guard fin-fn))

; Typically, do-fn-var and fin-fn-var, which are the names of formal parameter
; of the do fn lambda and the finally fn lambda, are the same, namely the
; symbol ALIST.  Furthermore, the guards of the two functions are terms in that
; formal.  

; (d) the initial alist satisfies the guard on do-fn.

               (special-conjecture-d
                (if (equal do-fn-guard *t*)
                    *true-clause*
                    (add-literal-smart
                     (subst-var initial-alist do-fn-var do-fn-guard)
                     warranted-clause
                     t)))
; The nested lambda expressions used in conjectures (e), (f), and (g) below are
; the fully translated form of

;  (let ((triple (true-list-fix (apply$ ',do-fn (list alist)))))
;    (let ((exit-flg (car triple))
;          (new-alist (caddr triple)))
;      (implies ... ...)))

; Note also that since there are no free variables in the conjecture other than
; alist, there is no point in including hypotheses from the surrounding
; context.  We do, however, include the warrant hypotheses.  Also note that
; there is always a guard on the do-fn and the fin-fn, namely, at least,
; (alistp alist), so we don't try to avoid generating the special conjectures
; involving trivial guards.

; (e) if the guard on do-fn is satisfied by some alist and running do-fn
;     produces an exit-flg of nil (and some new alist) then the guard on do-fn
;     is satisfied by that new alist.

               (special-conjecture-e
                (add-literal-smart
                 `((lambda (triple alist)
                     ((lambda (exit-flg new-alist alist)
                        (implies (if ,(subst-var 'alist
                                                 do-fn-var
                                                 do-fn-guard)
                                     (equal exit-flg 'nil)
                                     'nil)
                                 ,(subst-var 'new-alist
                                             do-fn-var
                                             do-fn-guard)))
                      (car triple)
                      (car (cdr (cdr triple)))
                      alist))
                   (true-list-fix (apply$ ',do-fn (cons alist 'nil)))
                   alist)
                 warrant-hyps
                 t))

; (f) if the guard on do-fn is satisfied on some alist and running do-fn
;     produces an exit-flg of :loop-finish (and some new alist) then the guard
;     on the finally-fn is satisfied by that new alist.  This conjecture can be
;     redundant if there is no finally clause.  But we don't detect that.  As
;     do loop$ translation stands now, there is always a non-trivial finally
;     lambda that is guarded at least by (alistp alist) and any type-specs from
;     the WITH clauses.  That lambda returns the nil value but a non-trivial
;     (but identity) alist on all the variables with type-specs.  The proof of
;     special conjecture (f) in this case is just a trivial but we think it is
;     easier to suffer the proof than to detect the triviality of the
;     non-trivial lambda we generate!  To fix this, change translate11-loop$!

               (special-conjecture-f
                (add-literal-smart
                 `((lambda (triple alist)
                     ((lambda (exit-flg new-alist alist)
                        (implies (if ,(subst-var 'alist
                                                 do-fn-var
                                                 do-fn-guard)
                                     (equal exit-flg ':loop-finish)
                                     'nil)
                                 ,(subst-var 'new-alist
                                             fin-fn-var
                                             fin-fn-guard)))
                      (car triple)
                      (car (cdr (cdr triple)))
                      alist))
                   (true-list-fix (apply$ ',do-fn (cons alist 'nil)))
                   alist)
                 warrant-hyps
                 t))

; (g) if the guard on do-fn is satisfied by alist and running do-fn produces an
;     exit flg of nil and (a some new alist) then the measure of the new alist
;     is smaller than that of alist.

               (special-conjecture-g
                (add-literal-smart
                 `((lambda (triple alist)
                     ((lambda (exit-flg new-alist alist)
                        (implies (if ,(subst-var 'alist
                                                 do-fn-var
                                                 do-fn-guard)
                                     (equal exit-flg 'nil)
                                     'nil)
                                 (l< (lex-fix (apply$ ',m-fn (cons new-alist 'nil)))
                                     (lex-fix (apply$ ',m-fn (cons alist 'nil))))))
                      (car triple)
                      (car (cdr (cdr triple)))
                      alist))
                   (true-list-fix (apply$ ',do-fn (cons alist 'nil)))
                   alist)
                 warrant-hyps
                 t)))
          (mv (append (if (equal special-conjecture-d *true-clause*)
                          nil
                          (list special-conjecture-d))
                      (if (equal special-conjecture-e *true-clause*)
                          nil
                          (list special-conjecture-e))
                      (if (equal special-conjecture-f *true-clause*)
                          nil
                          (list special-conjecture-f))
                      (if (equal special-conjecture-g *true-clause*)
                          nil
                          (list special-conjecture-g)))
              ttree)))
       (t ; style = :plain or :fancy
        (let* ((test-b (loop$-scion-restriction (ffn-symb term)))

; Test-b is either NIL or a monadic predicate like ACL2-NUMBERP that the
; output of the apply$ must satisfy.

               (fn (unquote (fargn term 1)))
               (globals (if (eq style :plain)
                            nil
                            (fargn term 2)))
               (lst (if (eq style :plain)
                        (fargn term 2)
                        (fargn term 3)))
               (var1 (car (lambda-object-formals fn)))
               (var2 (cadr (lambda-object-formals fn)))
               (fngp (lambda-object-guard fn))
               (subst (if (eq style :plain)
                          `((,var1 . ,newvar))
                          `((,var1 . ,globals)
                            (,var2 . ,newvar))))

; (a) every element of the target satisfies the guard of the body

               (special-conjecture-a
                (if (equal fngp *t*)
                    *true-clause*
                    (add-literal-smart
                     (sublis-var subst fngp)
                     (add-literal-smart
                      `(NOT (MEMBER-EQUAL ,newvar ,lst))
                      warranted-clause
                      t)
                     t)))

; (b) every element of the target satisfies the output restriction
;     of the operator

               (special-conjecture-b
                (if test-b
                    (add-literal-smart
                     `(,test-b
                       (APPLY$ ',fn
                               ,(if (eq style :plain)
                                    `(CONS ,newvar 'NIL)
                                    `(CONS ,globals
                                           (CONS ,newvar
                                                 'NIL)))))
                     (add-literal-smart
                      `(NOT (MEMBER-EQUAL ,newvar ,lst))
                      warranted-clause
                      t)
                     t)
                    *true-clause*))

; (c) the type-spec of each iteration var continues to hold at the
;     step BEYOND the last step!

               (special-conjectures-c
                (special-conjectures-c clause term wrld)))
          (mv (append (if (equal special-conjecture-a *true-clause*)
                          nil
                          (list special-conjecture-a))
                      (if (equal special-conjecture-b *true-clause*)
                          nil
                          (list special-conjecture-b))
                      special-conjectures-c
                      )
              ttree))))))
   (t (mv nil ttree))))

(defun make-lambda-application+ (formals body actuals)
  (let ((term (make-lambda-application formals body actuals)))
    (cond ((and (lambda-applicationp term)
                (equal (lambda-formals (ffn-symb term))
                       (fargs term)))
           (lambda-body (ffn-symb term)))
          (t term))))

(defun make-lambda-application+-lst (formals termlist args)
  (cond ((endp termlist) nil)
        (t (cons (make-lambda-application+ formals (car termlist) args)
                 (make-lambda-application+-lst formals (cdr termlist) args)))))

(defun split-env (env clause)

; Env is a list of terms of the form (stp (tbl-get 'st ...)) as constructed in
; (guard-clauses term ...) when term is such a stobj-let call, as recognized by
; parse-stobj-let-actual.  We return (mv env1 clause'), where -- viewed as a
; set -- env is partitioned into env1 and env2, where env2 contains each such
; tbl-get call that either occurs in another member of env or in clause, and
; clause' is the extension of clause by negating members of env2.  Informally,
; we are moving members of the input env into clause when they appear to be
; sufficiently relevant, a very informal heuristic notion that doesn't affect
; soundness, where the meaning of an (env clause) pair is the conjunction of
; the union of env with the set of negations of members of clause.

  (cond ((endp env)
         (mv nil clause))
        ((lambda-applicationp (car env))

; We could be more restrictive here in the lambda-application case, by moving
; (car env) into clause only if there is some call (tbl-get 'st ...) in (car
; env) for which some (possibly other) (tbl-get 'st ...) call, with the same
; st, occurs in clause.  But we'll go ahead an move every lambda application
; from env to clause.

         (mv-let (env1 clause1)
           (split-env (cdr env) clause)
           (mv (cons (car env1) env1)
               clause1)))
        (t (cond ((let ((accessor-call (fargn (car env) 1)))
                    (or (dumb-occur-lst accessor-call (cdr env))
                        (dumb-occur-lst accessor-call clause)))
                  (split-env (cdr env)
                             (add-literal (fcons-term* 'not (car env))
                                          clause
                                          nil)))
                 (t (mv-let (env1 clause1)
                      (split-env (cdr env) clause)
                      (mv (cons (car env1) env1)
                          clause1)))))))

(defun add-env-to-clause-set-1 (env cl-set)
  (cond ((endp cl-set) nil)
        (t (mv-let (tags-rev cl0)
             (split-initial-extra-info-lits (car cl-set) nil)
             (mv-let (env2 cl)
               (split-env env cl0)
               (declare (ignore env2))
               (cons (revappend tags-rev cl)
                     (add-env-to-clause-set-1 env (cdr cl-set))))))))

(defun add-env-to-clause-set (env cl-set)
  (cond ((null env) cl-set) ; optimization for common case
        (t (add-env-to-clause-set-1 env cl-set))))

(mutual-recursion

(defun guard-clauses (term debug-info stobj-optp clause wrld ttree newvar)

; See also guard-clauses+, which is a wrapper for guard-clauses that eliminates
; ground subexpressions.

; We return three results.  The first is a set of clauses whose conjunction
; establishes that all of the guards in term are satisfied.  We discuss the
; second result in the next paragraph.  The third result is a ttree justifying
; the simplification we do and extending ttree.  Stobj-optp indicates whether
; we are to optimize away stobj recognizers.  Call this with stobj-optp = t
; only when it is known that the term in question has been translated with full
; enforcement of the stobj rules.  Clause is the list of accumulated, negated
; tests passed so far on this branch, possibly enhanced by facts known about
; evaluation as discussed in the next paragraph.  Clause is maintained in
; reverse order, but reversed before we return it.

; The second result is a list of terms, which we think of as an "environment"
; or "env" for short.  To understand the environment result, consider what we
; are trying to do here.  A key goal is to guarantee that evaluation avoids
; Common Lisp errors.  To that end, when computing (guard-clauses term0
; ... clause0 ...), we permit each clause in the first result (which, again, is
; a set of clauses -- these are the guard proof obligations) to incorporate
; facts that are known to be true when evaluating term0 in a context where the
; negations of terms in clause0 are assumed true.  As of this writing, the
; facts that make it into an environment are generated for each stobj-table
; field accessor, say, (tbl-get 'st parent (create-st)): in each such case, the
; stobj recognizer is assumed to hold of that term, e.g., (stp (tbl-get 'st
; parent (create-st))) is returned in the environment.  This recognizer call
; indeed holds where evaluation occurs for term0 (under clause0), because of
; restrictions in translate on stobj-table field accessors and the invariant
; maintained on stobj-table fields, that each key 'st of the table is mapped to
; a stobj satisfying the recognizer of st.  It is thus sound to incorporate the
; environment into each clause in the clause-set returned as the first result,
; though we heurstically limit which parts of the environment; see
; add-env-to-clause-set and its subroutine, split-env.  It would be silly, for
; example, to add the hypothesis (stp (tbl-get 'st parent (create-st))) to the
; goal (i.e., the negation of that as a literal in the returned clause-set)
; when the guard proof obligation has nothing to do with that stobj-field
; access -- for example, when the goal is (implies (and (integer-listp x)
; (consp x)) (rationalp (car x))).

; We do not add the definition rune for *extra-info-fn* in ttree.  The caller
; should be content with failing to report that rune.  Prove-guard-clauses is
; ultimately the caller, and is happy not to burden the user with mention of
; that rune.

; In addition, if term is one of the special loop$ scions, e.g., sum, applied
; to a quoted well-formed function object, we generate the special loop$
; conjectures.  Search for ``special'' below for details.

; Note: Once upon a time, this function took an additional argument, alist, and
; was understood to be generating the guards for term/alist.  Alist was used to
; carry the guard generation process into lambdas.

  (cond
   ((variablep term) (mv nil nil ttree))
   ((fquotep term) (mv nil nil ttree))
   ((flambda-applicationp term)
    (mv-let
      (cl-set1 env1 ttree)
      (guard-clauses-lst (fargs term) debug-info stobj-optp clause wrld
                         ttree newvar)
      (mv-let
        (cl-set2 env2 ttree)
        (guard-clauses (lambda-body (ffn-symb term))
                       debug-info
                       stobj-optp

; We pass in the empty clause here, because we do not want it involved in
; wrapping up the lambda term that we are about to create.

                       nil
                       wrld ttree newvar)
        (let* ((formals (lambda-formals (ffn-symb term)))
               (args (remove-guard-holders-lst (fargs term) wrld))
               (term1 (make-lambda-application+
                       formals
                       (termify-clause-set cl-set2)
                       args))
               (cl (if (and (null (cdr cl-set2)) ; at most one clause
                            (ffn-symb-p term1 'if))

; In this case we prefer that the clause in cl-set2 remain flat.  This can help
; to avoid clutter.  See for example "The non-trivial part of the guard
; conjecture for DO-TBL" generated in the DO-TBL example in
; books/system/tests/stobj-table-tests-input.lsp.

                       (reverse (disjoin-clauses
                                 (make-lambda-application+-lst formals
                                                               (car cl-set2)
                                                               args)
                                 clause))
                     (reverse (add-literal-smart term1 clause nil))))
               (cl-set3 (if (equal cl *true-clause*)
                            cl-set1
                          (conjoin-clause-sets+
                           debug-info
                           cl-set1
                           (list cl))))
               (env3 (make-lambda-application+-lst formals env2 args))
               (env (union-equal env3 env1)))

; Maybe we shouldn't put all of env3 into the clause, instead making the lambda
; case of split-env more restrictive, as noted in a comment there.  But for
; now, at least, we'll add env3 as a hypothesis, in its entirety.  If later we
; decide to use of subset of env3 and a regression test fails, we'll learn
; something useful!

          (mv (add-env-to-clause-set env cl-set3)
              env
              ttree)))))
   ((eq (ffn-symb term) 'if)
    (let ((test (remove-guard-holders (fargn term 1) wrld)))
      (mv-let
        (cl-set1 env1 ttree)

; Note:  We generate guards from the original test, not the one with guard
; holders removed!

        (guard-clauses (fargn term 1) debug-info stobj-optp clause wrld
                       ttree newvar)
        (mv-let
          (cl-set2 env2 ttree)
          (guard-clauses (fargn term 2)
                         debug-info
                         stobj-optp

; But the additions we make to the two branches is based on the simplified
; test.

                         (add-literal-smart (dumb-negate-lit test)
                                            clause
                                            nil)
                         wrld ttree newvar)
          (mv-let
            (cl-set3 env3 ttree)
            (guard-clauses (fargn term 3)
                           debug-info
                           stobj-optp
                           (add-literal-smart test clause nil)
                           wrld ttree newvar)
            (mv (conjoin-clause-sets+
                 debug-info
                 cl-set1
                 (conjoin-clause-sets+ debug-info cl-set2 cl-set3))
                (cond
                 ((or env2 env3)
                  (let* ((env23 (intersection-equal env2 env3))
                         (env2a (if env23 ; optimization: perhaps uncommon case
                                    (set-difference-equal env2 env23)
                                  env2))
                         (env3a (if env23 ; optimization: perhaps uncommon case
                                    (set-difference-equal env3 env23)
                                  env3)))
                    (cond
                     ((or env2a env3a)
                      (add-to-set-equal
                       (fcons-term* 'if
                                    (fargn term 1)
                                    (conjoin env2a)
                                    (conjoin env3a))
                       (if env23
                           (union$ env1 env23 :test 'equal)
                         env1)))
                     (t ; as sets, env2 = env3 = env23 != {}
                      (union$ env1 env23 :test 'equal)))))
                 (t env1))
                ttree))))))
   ((eq (ffn-symb term) 'wormhole-eval)

; Because of translate, term is necessarily of the form

; (wormhole-eval '<name> '(lambda (<whs>) <body>) <name-dropper-term>)
; or
; (wormhole-eval '<name> '(lambda (     ) <body>) <name-dropper-term>)

; the only difference being whether the lambda has one or no formals.  The
; <body> of the lambda has been translated despite its occurrence inside a
; quoted lambda.  The <name-dropper-term> is always of the form 'NIL or a
; variable symbol or a PROG2$ nest of variable symbols and thus has a guard of
; T.  Furthermore, translate ensures that the free variables of the lambda are
; those of the <name-dropper-term>.  Thus, all the variables we encounter in
; <body> are variables known in the current context, except <whs>.  By the way,
; ``whs'' stands for ``wormhole status'' and if it is the lambda formal we know
; it occurs in <body>.

; The raw lisp macroexpansion of the first wormhole-eval form above is (modulo
; the name of var) essentially as follows.

; (let* ((<whs> (cdr (assoc-equal '<name> *wormhole-status-alist*)))
;        (val <body>))
;   (put-assoc-equal '<name> val *wormhole-status-alist*)
;   nil)

; We wish to make sure this form is Common Lisp compliant.  We know that
; *wormhole-status-alist* is an alist satisfying the guard of assoc-equal and
; put-assoc-equal.  The raw lisp macroexpansion of the second form of
; wormhole-eval is also like that above.  Thus, the only problematic form in
; either expansion is <body>, which necessarily mentions the variable symbol
; <whs> if it's mentioned in the lambda.  Furthermore, at runtime we know
; absolutely nothing about the last wormhole status of <name>.  So we need to
; generate a fresh variable symbol to use in place of <whs> in our guard
; clauses.

    (let* ((whs (car (lambda-formals (cadr (fargn term 2)))))
           (body (lambda-body (cadr (fargn term 2))))
           (name-dropper-term (fargn term 3))
           (new-var (if whs
                        (genvar whs (symbol-name whs) nil
                                (all-vars1-lst
                                 clause
                                 (all-vars name-dropper-term)))
                      nil))
           (new-body (if (eq whs new-var)
                         body
                       (subst-var new-var whs body))))
      (cond (new-var (mv-let (cl-set env ttree)

; In this case we discard env if new-var occurs in it.  To see why, imagine
; that we have an expression (foo (wormhole-eval ...) (wormhole-eval ...)).
; The calls of guard-clauses on the two wormhole-eval could generate env values
; about the same new-var whose conjunction could even be inconsistent!  We
; could keep members of env that don't mention new-var, but it seems a bit
; unlikely that we will encounter stobj-table field accessor expressions inside
; a wormhole-eval for which we need stobj recognizer hypotheses elsewhere in
; the parent term.

                       (guard-clauses new-body debug-info stobj-optp clause
                                      wrld ttree newvar)
                       (mv cl-set
                           (cond ((dumb-occur-var-lst new-var env) nil)
                                 (t env))
                           ttree)))
            (t (guard-clauses new-body debug-info stobj-optp clause
                              wrld ttree newvar)))))
   ((throw-nonexec-error-p term :non-exec nil)

; It would be sound to replace the test above by (throw-nonexec-error-p term
; nil nil).  However, through Version_4.3 we have always generated guard proof
; obligations for defun-nx, and indeed for any form (prog2$
; (throw-nonexec-error 'fn ...) ...).  So we restrict this special treatment to
; forms (prog2$ (throw-nonexec-error :non-exec ...) ...), as may be generated
; by calls of the macro, non-exec.  The corresponding translated term is of the
; form (return-last 'progn (throw-non-exec-error ':non-exec ...) targ3); then
; only the throw-non-exec-error call needs to be considered for guard
; generation, not targ3.

    (guard-clauses (fargn term 2) debug-info stobj-optp clause
                   wrld ttree newvar))

; At one time we optimized away the guards on (nth 'n MV) if n is an integerp
; and MV is bound in (former parameter) alist to a call of a multi-valued
; function that returns more than n values.  Later we changed the way mv-let is
; handled so that we generated calls of mv-nth instead of nth, but we
; inadvertently left the code here unchanged.  Since we have not noticed
; resulting performance problems, and since this was the only remaining use of
; alist when we started generating lambda terms as guards, we choose for
; simplicity's sake to eliminate this special optimization for mv-nth.

   (t

; Here we generate the conclusion clauses we must prove.  These clauses
; establish that the guard of the function being called is satisfied.  We first
; convert the guard into a set of clause segments, called the
; guard-concl-segments.

; We optimize stobj recognizer calls to true here.  That is, if the function
; traffics in stobjs (and is not non-executablep!), then it was so translated
; (except in cases handled by the throw-nonexec-error-p case above), and we
; know that all those stobj recognizer calls are true.  We similarly know that
; stobje-table field accesses return appropriate stobjs, and that knowledge is
; reflected in the env returned.

; Once upon a time, we normalized the 'guard first.  Is that important?

; We also generate the special loop$ conjectures as necessary.

    (let ((env-term (mv-let (tbl-get parent st st-creator)
                      (parse-stobj-let-actual term)
                      (declare (ignore st-creator))
                      (cond
                       ((and tbl-get
; Then check that this really is a stobj-table field access.
                             (not (member-eq tbl-get *stobjs-out-invalid*))
                             (equal (stobjs-out tbl-get wrld)
                                    (list *stobj-table-stobj*))
                             (equal (stobjs-in tbl-get wrld)
                                    (list nil parent *stobj-table-stobj*)))
                        (fcons-term* (get-stobj-recognizer st wrld)
                                     term))
                       (t nil))))
          (guard-concl-segments (clausify (guard (ffn-symb term)
                                                 stobj-optp
                                                 wrld)

; Warning: It might be tempting to pass in the assumptions of clause into the
; second argument of clausify.  That would be wrong!  The guard has not yet
; been instantiated and so the variables it mentions are not the same ones in
; clause!

                                          nil

; Should we expand lambdas here?  I say ``yes,'' but only to be conservative
; with old code.  Perhaps we should change the t to nil?

                                          t

; We use the sr-limit from the world, because we are above the level at which
; :hints or :guard-hints would apply.

                                          (sr-limit wrld))))
      (mv-let
        (cl-set1 env1 ttree)
        (guard-clauses-lst
         (cond
          ((and (eq (ffn-symb term) 'return-last)
                (quotep (fargn term 1)))
           (case (unquote (fargn term 1))
             (mbe1-raw

; Consider a call (mbe :logic logic :exec exec), which in translated form looks
; like (return-last 'mbe1-raw exec logic).  This macroexpands to exec in raw
; Common Lisp, so we treat this expression as just the :exec part for purposes
; of computing guard-clauses.

              (list (fargn term 2)))
             (ec-call1-raw

; Since (return-last 'ec-call1-raw ign (fn arg1 ... argk)) leads to the call
; (*1*fn arg1 ... argk) or perhaps (*1*fn$inline arg1 ... argk) in raw Common
; Lisp, we need only verify guards for the argi.  This omits producing the
; environment (second return value of guard-clauses) for (ec-call (tbl-get 'st
; ...)) where tbl-get is a stobj-table field accessor; but such terms would be
; rejected by translate so we don't expect to see them (and it's sound to miss
; this opportunity to generate environment terms).

              (fargs (fargn term 3)))
             (otherwise

; Consider the case that (fargn term 1) is not syntactically equal to 'mbe1-raw
; or 'ec-call1-raw but reduces to one of these.  Even then, return-last is a
; macro in Common Lisp, so we shouldn't produce the reduced obligations for
; either of the two cases above.  But this is a minor issue anyhow, because
; it's certainly safe to avoid those reductions, so in the worst case we would
; still be sound, even if producing excessively strong guard obligations.  (And
; because translate has accepted these terms, the environments produced are
; sound, i.e., stobj-field accesses produce the expected stobjs).

              (fargs term))))
          (t (fargs term)))
         debug-info stobj-optp clause wrld ttree newvar)
        (mv-let (cl-set2 ttree)
          (special-conjectures clause term wrld newvar ttree)
          (let ((env2 (if env-term
                          (add-to-set-equal env-term env1)
                        env1)))
            (let* ((guard-concl-segments-1
                    (add-each-literal-lst
                     (and guard-concl-segments ; optimization (nil for ec-call)
                          (sublis-var-lst-lst
                           (pairlis$
                            (formals (ffn-symb term) wrld)
                            (remove-guard-holders-lst (fargs term) wrld))
                           guard-concl-segments))))
                   (cl-set
                    (conjoin-clause-sets+
                     debug-info
                     (conjoin-clause-sets+
                      debug-info
                      cl-set1
                      (add-env-to-clause-set
                       env2
                       (add-segments-to-clause
                        (maybe-add-extra-info-lit debug-info term
                                                  (reverse clause) wrld)
                        guard-concl-segments-1)))
                     (add-env-to-clause-set env2 cl-set2))))
              (mv cl-set env2 ttree)))))))))

(defun guard-clauses-lst (lst debug-info stobj-optp clause wrld ttree newvar)
  (cond ((null lst) (mv nil nil ttree))
        (t (mv-let
             (cl-set1 env1 ttree)
             (guard-clauses (car lst) debug-info stobj-optp clause
                            wrld ttree newvar)
             (mv-let
               (cl-set2 env2 ttree)
               (guard-clauses-lst (cdr lst) debug-info stobj-optp clause
                                  wrld ttree newvar)
               (mv (conjoin-clause-sets+ debug-info cl-set1 cl-set2)
                   (union-equal env1 env2)
                   ttree))))))

)

(defun guard-clauses+ (term debug-info stobj-optp clause ens wrld safe-mode
                            gc-off ttree newvar)

; Ens may have the special value :do-not-simplify, in which case no
; simplification will take place in producing the guard clauses.

  (mv-let (clause-lst0 env0 ttree)
    (guard-clauses term debug-info stobj-optp clause wrld ttree newvar)
    (declare (ignore env0))
    (cond ((eq ens :DO-NOT-SIMPLIFY)
           (mv clause-lst0 ttree))
          (t (mv-let (flg clause-lst ttree memo)
               (eval-ground-subexpressions1-lst-lst
                clause-lst0 ens wrld safe-mode gc-off ttree
                *loop$-special-function-symbols*
                nil)
               (declare (ignore flg memo))
               (mv clause-lst ttree))))))

(defun guard-clauses-for-body (hyp-segments body debug-info stobj-optp ens
                                            wrld safe-mode gc-off ttree newvar)

; Hyp-segments is a list of clauses derived from the guard for body.  We
; generate the guard clauses for the unguarded body, body, under each of the
; different hyp segments.  We return a clause set and a ttree justifying all
; the simplification and extending ttree.

; Name is nil unless we are in a mutual-recursion, in which case it is the name
; of the function associated with the given body.

; Ens may have the special value :do-not-simplify, in which case no
; simplification will take place in producing the guard clauses.

  (cond
   ((null hyp-segments) (mv nil ttree))
   (t (mv-let
       (cl-set1 ttree)
       (guard-clauses+ body debug-info stobj-optp
                       (car hyp-segments)
                       ens wrld
                       safe-mode gc-off ttree newvar)
       (mv-let
        (cl-set2 ttree)
        (guard-clauses-for-body (cdr hyp-segments)
                                body debug-info stobj-optp ens wrld safe-mode
                                gc-off ttree newvar)
        (mv (conjoin-clause-sets+ debug-info cl-set1 cl-set2) ttree))))))

(defun normalize-ts-backchain-limit-for-defs (wrld)

; This function restricts the type-set backchain-limit to 1.  We have found
; that to be potentially very useful when normalizing a definition body (or
; rule) or a guard.  Specifically, Jared Davis sent the following example,
; which we ran in early Feb. 2016.

; (include-book "data-structures/list-defthms" :dir :system)
; (time$ (include-book "centaur/sv/top" :dir :system))

; When we experimented with restricting the type-set backchain limit during
; normalization of definitions bodies and guards, performance improved
; dramatically, as follows.  (All timings were done with profiling, which
; probably doesn't much matter.)

; ;;; old
; ; 1189.86 seconds realtime, 1189.45 seconds runtime
; ; (42,121,431,648 bytes allocated).

; ;;; new
; ; 91.64 seconds realtime, 91.38 seconds runtime
; ; (6,786,611,056 bytes allocated).

; Moreover, from profiling we saw that the time spent under normalize decreased
; from 1040 seconds to 4.69 seconds.

; We chose a type-set backchain-limit of 1 because the performance improvement
; was less than 1% when using a limit of 0, but the time increased by about 25%
; when using a limit of 2.

; This restriction of type-set backchain limits could be considered rather
; arbitrary, and the "everything" regression time didn't change significantly.
; But normalization is merely heuristic; and even though Jared's is just one
; example, and even though we might later improve type-set to avoid the
; blow-up, still it's easy to imagine that there could be other such examples.
; So we are making this change on 2/7/2016.

  (let ((limit (backchain-limit wrld :ts)))
    (if (eql limit 0)
        0
      1)))

(defun guard-clauses-for-fn1 (name debug-p ens wrld safe-mode gc-off ttree)

; Warning: name must be either the name of a function defined in wrld or a
; well-formed lambda object.  Remember: not every lambda object is well-formed.
; Use well-formed-lambda-objectp to check before calling this function!

; Given a function name or a well-formed lambda object we generate the clauses
; that establish that all the guards in both the unnormalized guard and
; unnormalized body are satisfied.  While processing the guard we assume
; nothing.  But we generate the guards for the unnormalized body under each of
; the possible guard-hyp-segments derived from the assumption of the normalized
; 'guard.  We return the resulting clause set and an extension of ttree
; justifying it.  The resulting ttree is 'assumption-free, provided the initial
; ttree is also.

; Notice that in the two calls of guard below, used while computing
; the guard conjectures for the guard of name itself, we use stobj-opt
; = nil.

; Ens may have the special value :do-not-simplify, in which case no
; simplification will take place in producing the guard clauses.

; Newvar is a variable symbol in the ``same'' package as fn seems to be (an odd
; concept for a LAMBDA object which may have many packages mentioned in it) but
; that is not used as a variable in any way in the formals, guard, or body of
; fn.  See all-vars!.  Newvar may be used in the so-called ``Special loop$
; conjectures.''

  (let ((newvar
         (genvar (cond ((symbolp name) name)
                       ((lambda-formals name) (car (lambda-formals name)))
                       (t 'APPLY$))
                 "NEWV"
                 nil
                 (all-vars!-of-fn name wrld)))
        (guard
         (if (symbolp name)
             (guard name nil wrld)
           (lambda-object-guard name)))
        (stobj-optp (not (and (symbolp name)
                              (eq (getpropc name 'non-executablep
                                            nil wrld)
                                  t)))))
    (mv-let
      (cl-set1 ttree)
      (guard-clauses+ guard
                      (and debug-p `(:guard (:guard ,name)))

; Observe that when we generate the guard clauses for the guard we optimize
; the stobj recognizers away.  We restrict to the case that the named function
; is executable, but as of this writing, the guard is always subjected to stobj
; single-threadedness restrictions, so we really don't need to make that
; restriction.  We may reconsider upon demand, but if we change the next
; argument to t, we should be careful to document that even non-executable
; functions have their guards translated for executability.

; Just to drive the point home that the stobj optimization is appropriate here:
; Note that the stobj recognizer is always conjoined with the guard, so that
; the guard is essentially the conjunction

;   (if (stobp <stobj>) <specified-guard> 'nil)

; So we actually have (stobp <stobj>) explicitly present when optimizing the
; guards on <specified-guard>.

                      stobj-optp
                      nil ens wrld safe-mode gc-off ttree newvar)
      (let ((unnormalized-body
             (if (symbolp name)
                 (getpropc name 'unnormalized-body
                           '(:error "See GUARD-CLAUSES-FOR-FN.")
                           wrld)
               (lambda-object-body name))))
        (mv-let
          (normal-guard ttree)
          (cond ((eq ens :do-not-simplify)
                 (mv guard nil))
                (t (normalize guard
                              t   ; iff-flg
                              nil ; type-alist
                              ens wrld ttree
                              (normalize-ts-backchain-limit-for-defs wrld))))
          (let ((hyp-segments

; Should we expand lambdas here?  I say ``yes,'' but only to be
; conservative with old code.  Perhaps we should change the t to nil?

                 (clausify (dumb-negate-lit normal-guard)
                           nil t (sr-limit wrld))))
            (mv-let
              (cl-set2 ttree)
              (guard-clauses-for-body hyp-segments
                                      unnormalized-body
                                      (and debug-p `(:guard (:body ,name)))

; Observe that when we generate the guard clauses for the body we optimize
; the stobj recognizers away, provided the named function is executable.

                                      stobj-optp
                                      ens wrld safe-mode gc-off ttree newvar)
              (mv-let (type-clauses ttree)
                (guard-clauses-for-body
                 hyp-segments
                 (fcons-term* 'insist
                              (if (symbolp name)
                                  (getpropc name 'split-types-term *t* wrld)
                                *t*))
                 (and debug-p `(:guard (:type ,name)))

; There seems to be no clear reason for setting stobj-optp here to t.  This
; decision could easily be reconsidered; we are being conservative here since
; as we write this comment in Oct. 2017, stobj-optp = nil has been probably
; been used here since the inception of split-types.

                 nil
                 ens wrld safe-mode gc-off ttree newvar)
                (let ((cl-set2
                       (if type-clauses ; optimization
                           (conjoin-clause-sets+ debug-p
                                                 type-clauses cl-set2)
                         cl-set2)))
                  (mv (conjoin-clause-sets+ debug-p
                                            cl-set1 cl-set2)
                      ttree))))))))))

(defun guard-clauses-for-fn1-lst (fns debug-p ens wrld safe-mode gc-off ttree)

; Fns here is a list of function names and/or well-formed lambda objects.
; Remember: not every lambda object is well-formed.  Use
; well-formed-lambda-objectp to check before calling this function!

  (cond ((endp fns) (mv nil ttree))
        (t (mv-let (cl-set1 ttree)
             (guard-clauses-for-fn1 (car fns) debug-p ens wrld safe-mode gc-off
                                    ttree)
             (mv-let (cl-set2 ttree)
               (guard-clauses-for-fn1-lst (cdr fns) debug-p ens wrld safe-mode
                                          gc-off ttree)
               (mv (conjoin-clause-sets+ debug-p cl-set1 cl-set2)
                   ttree))))))

(defun collect-well-formed-lambda-objects (fn wrld)

; Warning: name must be either the name of a function or theorem defined in
; wrld or a well-formed lambda object.  Remember: not every lambda object is
; well-formed.  Use well-formed-lambda-objectp to check before calling this
; function!  We return the list of all well-formed lambda objects in fn.

  (cond
   ((global-val 'boot-strap-flg wrld)

; We do not expect to find any well-formed lambda objects during the
; boot-strap.  Without this case, we get an error during "make proofs" when
; evaluating the form form (verify-guards observation1-cw) in
; boot-strap-pass-2-a.lisp, because of its use of wormholes.

    nil)
   (t
    (let* ((theorem (and (symbolp fn)
                         (getpropc fn 'theorem nil wrld)))
           (guard
            (if (symbolp fn)
                (if theorem
                    *t* ; just a trivial term without lambda objects
                  (guard fn nil wrld))
              (lambda-object-guard fn)))
           (unnormalized-body
            (if (symbolp fn)
                (or theorem
                    (getpropc fn 'unnormalized-body
                              '(:error "See COLLECT-WELL-FORMED-LAMBDA-OBJECTS")
                              wrld))
              (lambda-object-body fn)))
           (ans (collect-certain-lambda-objects-lst
                 :well-formed
                 (list guard unnormalized-body)
                 wrld nil)))

; If fn is a well-formed lambda object (i.e., a non-symbol in this context)
; then add it to the list because the collector above looks only for lambdas
; inside quotes.

      (if (symbolp fn)
          ans
        (cons fn ans))))))

(defun collect-well-formed-lambda-objects-lst (fns wrld)
  (cond ((endp fns) nil)
        (t (union-equal (collect-well-formed-lambda-objects (car fns) wrld)
                        (collect-well-formed-lambda-objects-lst (cdr fns) wrld)))))

(defun guard-clauses-for-fn (fn debug-p ens wrld safe-mode gc-off ttree)

; Warning: fn must be either the name of a function defined in wrld or a
; well-formed lambda object.  Remember: not every lambda object is well-formed.
; Use well-formed-lambda-objectp to check before calling this function!

; We generate the guard clauses for fn and all of the well-formed lambda
; objects in fn, including lambda objects within lambda objects.  We avoid
; generating guard clauses for any lambda object already on
; common-lisp-compliant-lambdas.  (Verify-guards will have already checked that
; fn itself -- whether a function symbol or lambda object -- is not already
; known to be compliant.)

  (guard-clauses-for-fn1-lst
   (cons fn (set-difference-equal
             (collect-well-formed-lambda-objects fn wrld)
             (global-val 'common-lisp-compliant-lambdas wrld)))
   debug-p ens wrld safe-mode gc-off ttree))

(defun guard-clauses-for-clique (names debug-p ens wrld safe-mode gc-off ttree)

; Given a mutually recursive clique of fns we generate all of the
; guard conditions for every function in the clique and return that
; set of clauses and a ttree extending ttree and justifying its
; construction.  The resulting ttree is 'assumption-free, provided the
; initial ttree is also.

; Ens may have the special value :do-not-simplify, in which case no
; simplification will take place in producing the guard clauses.

  (cond ((null names) (mv nil ttree))
        (t (mv-let
            (cl-set1 ttree)
            (guard-clauses-for-fn (car names) debug-p ens wrld safe-mode gc-off
                                  ttree)
            (mv-let
             (cl-set2 ttree)
             (guard-clauses-for-clique (cdr names) debug-p ens wrld safe-mode
                                       gc-off ttree)
             (mv (conjoin-clause-sets+ debug-p cl-set1 cl-set2) ttree))))))

; That completes the generation of the guard clauses.  We will prove
; them with prove.

(defun remove-built-in-clauses (cl-set ens oncep-override wrld state ttree)

; We return two results.  The first is a subset of cl-set obtained by deleting
; all built-in-clauseps and the second is the accumulated ttrees for the
; clauses we deleted.

  (cond
   ((null cl-set) (mv nil ttree))
   (t (mv-let
       (built-in-clausep ttree1)
       (built-in-clausep

; We added defun-or-guard-verification as the caller arg of the call of
; built-in-clausep below.  This addition is a little weird because there is no
; such function as defun-or-guard-verification; the caller argument is only
; used in trace reporting by forward-chaining.  If we wanted to be more precise
; about who is responsible for this call, we'd have to change a bunch of
; functions because this function is called by clean-up-clause-set which is in
; turn called by prove-termination, guard-obligation-clauses, and
; verify-valid-std-usage (which is used in the non-standard defun-fn1).  We
; just didn't think it mattered so much as to warrant changing all those
; functions.

        'defun-or-guard-verification
        (car cl-set) ens oncep-override wrld state)

; Ttree is known to be 'assumption free.

       (mv-let
        (new-set ttree)
        (remove-built-in-clauses (cdr cl-set) ens oncep-override wrld state
                                 (cons-tag-trees ttree1 ttree))
        (cond (built-in-clausep (mv new-set ttree))
              (t (mv (cons (car cl-set) new-set) ttree))))))))

(defun length-exceedsp (lst n)
  (cond ((null lst) nil)
        ((= n 0) t)
        (t (length-exceedsp (cdr lst) (1- n)))))

(defconst *half-length-initial-built-in-clauses*
  (floor (length *initial-built-in-clauses*)
         2))

(defun clean-up-clause-set (cl-set ens wrld ttree state)

; Warning: The set of clauses returned by this function only implies the input
; set.  They are thought to be equivalent only if the input set contains no
; tautologies.  See the caution in subsumption-replacement-loop.

; Note: ens can be nil or an enabled structure.  If ens is nil, then we
; consider only the rules specified by *initial-built-in-clauses* to be
; enabled.

; This function removes subsumed clauses from cl-set, does replacement (e.g.,
; if the set includes the clauses {~q p} and {q p} replace them both with {p}),
; and removes built-in clauses.  It returns two results, the cleaned up clause
; set and a ttree justifying the deletions and extending ttree.  The returned
; ttree is 'assumption free (provided the incoming ttree is also) because all
; necessary splitting is done internally.

; Bishop Brock has pointed out that it is unclear what is the best order in
; which to do these two checks.  Subsumption-replacement first and then
; built-in clauses?  Or vice versa?  We do a very trivial analysis here to
; order the two.  Bishop is not to blame for this trivial analysis!

; Suppose there are n clauses in the initial cl-set.  Suppose there are b
; built-in clauses.  The cost of the subsumption-replacement loop is roughly
; n*n and that of the built-in check is n*b.  Contrary to all common sense let
; us suppose that the subsumption-replacement loop eliminates redundant clauses
; at the rate, r, so that if we do the subsumption- replacement loop first at a
; cost of n*n we are left with n*r clauses.  Note that the worst case for r is
; 1 and the smaller r is, the better; if r were 1/100 it would mean that we
; could expect subsumption-replacement to pare down a set of 1000 clauses to
; just 10.  More commonly perhaps, r is just below 1, e.g., 99 out of 100
; clauses are unaffected.  To make the analysis possible, let's assume that
; built-in clauses crop up at the same rate!  So,

; n^2 + bnr   = cost of doing subsumption-replacement first  = sub-first

; bn + (nr)^2 = cost of doing built-in clauses first         = bic-first

; Observe that when r=1 the two costs are the same, as they should be.  But
; generally, r can be expected to be slightly less than 1.

; Here is an example.  Let n = 10, b = 100 and r = 99/100.  In this example we
; have only a few clauses to consider but lots of built in clauses, and we have
; a realistically low expectation of hits.  The cost of sub-first is 1090 but
; the cost of bic-first is 1098.  So we should do sub-first.

; On the other hand, if n=100, b=20, and r=99/100 we see sub-first costs 11980
; but bic-first costs 11801, so we should do built-in clauses first.  This is a
; more common case.

; In general, we should do built-in clauses first when sub-first exceeds
; bic-first.

; n^2 + bnr >= bn + (nr)^2  = when we should do built-in clauses first

; Solving we get:

; n > b/(1+r).

; Indeed, if n=50 and b=100 and r=99/100 we see the costs of the two equal
; at 7450.

  (cond
   ((let ((sr-limit (sr-limit wrld)))
      (and sr-limit (> (length cl-set) sr-limit)))
    (pstk
     (remove-built-in-clauses
      cl-set ens (match-free-override wrld) wrld state
      (add-to-tag-tree 'sr-limit t ttree))))
   ((length-exceedsp cl-set
                     (if ens
                         (global-val 'half-length-built-in-clauses wrld)
                       *half-length-initial-built-in-clauses*))
    (mv-let (cl-set ttree)
            (pstk
             (remove-built-in-clauses cl-set ens
                                      (match-free-override wrld)
                                      wrld state ttree))
            (mv (pstk
                 (subsumption-replacement-loop
                  (merge-sort-length cl-set) nil nil))
                ttree)))
   (t (pstk
       (remove-built-in-clauses
        (pstk
         (subsumption-replacement-loop
          (merge-sort-length cl-set) nil nil))
        ens (match-free-override wrld) wrld state ttree)))))

(defun guard-theorem (fn simp-p guard-debug wrld state)

; Warning: If you change the formals of this function, consider making a
; corresponding change to guard-or-termination-theorem-msg.

  (declare (xargs :stobjs state
                  :guard (and (plist-worldp wrld)
                              (symbolp fn)
                              (function-symbolp fn wrld)

; We can call guard-theorem for any :logic mode function, since it is perfectly
; reasonable to ask for the guard theorem even if the guards haven't been
; verified.  Of course, we only trust that the result is a theorem when the
; function is already guard-verified.

                              (logicp fn wrld))))
  (cond
   ((not (getpropc fn 'unnormalized-body nil wrld))
    *t*)
   (t
    (let ((names (or (getpropc fn 'recursivep nil wrld)
                     (list fn))))
      (mv-let (cl-set ttree)
        (guard-clauses-for-clique names
                                  guard-debug
                                  :DO-NOT-SIMPLIFY ; ens
                                  wrld
                                  (f-get-global 'safe-mode state)
                                  (gc-off state)
                                  nil)
; Note that ttree is assumption-free; see guard-clauses-for-clique.
        (let ((cl-set
               (cond (simp-p
                      (mv-let (cl-set ttree)
                        (clean-up-clause-set cl-set nil wrld ttree state)
                        (declare (ignore ttree)) ; assumption-free
                        cl-set))
                     (t cl-set))))
          (termify-clause-set cl-set)))))))

(defun guard-or-termination-theorem-msg (kwd args coda)
  (declare (xargs :guard (and (member-eq kwd '(:gthm :tthm))
                              (true-listp args))))
  (let ((fn (car args)))
    (mv-let (wrld called-fn)
      (case kwd
        (:gthm (mv (nth 3 args) 'guard-theorem))
        (:tthm (mv (nth 1 args) 'termination-theorem))
        (otherwise
         (mv (er hard! 'guard-or-termination-theorem-msg
                 "Implementation error!")
             nil)))
      (if (plist-worldp wrld)
          (msg "A call of ~x0 (or ~x1) can only be made on a :logic mode ~
              function symbol, but ~x2 is ~@3.~@4"
               kwd
               called-fn
               fn
               (cond ((not (symbolp fn))
                      "not a symbol")
                     ((not (function-symbolp fn wrld))
                      "not a function symbol in the current world")
                     (t ; (programp fn wrld)
                      "a :program mode function symbol"))
               coda)
        (msg "The second argument of the call ~x0 is not a valid logical world."
             (cons called-fn args))))))

(set-guard-msg guard-theorem
               (guard-or-termination-theorem-msg :gthm args coda))

(set-guard-msg termination-theorem
               (guard-or-termination-theorem-msg :tthm args coda))

(defun termination-theorem-fn-subst2 (old-nest wrld acc)

; See termination-theorem-fn-subst.  At the top level, wrld starts with
; 'formals properties; if these match up with old-nest (as described in
; termination-theorem-fn-subst.), then we return the resulting functional
; substitution mapping old function symbols to new.

  (cond ((endp old-nest)
         (and (not (eq (cadr (car wrld)) 'formals))
              acc))
        ((eq (cadr (car wrld)) 'formals)
         (and (eql (length (cddr (car wrld)))
                   (length (getpropc (car old-nest) 'formals nil wrld)))
              (instantiablep (car old-nest) wrld)
              (termination-theorem-fn-subst2 (cdr old-nest)
                                             (cdr wrld)
                                             (acons (car old-nest)
                                                    (car (car wrld))
                                                    acc))))
        (t nil)))

(defun termination-theorem-fn-subst1 (old-nest wrld)

; See termination-theorem-fn-subst.  Here we cdr down wrld until we find the
; first 'formals property (if any).

  (cond ((eq (cadr (car wrld)) 'formals)
         (termination-theorem-fn-subst2 (reverse old-nest) wrld nil))
        ((eq (car (car wrld)) 'event-landmark)
         nil)
        (t (termination-theorem-fn-subst1 old-nest (cdr wrld)))))

(defun termination-theorem-fn-subst (fn wrld)

; Fn is in the process of being defined recursively (or if not recursive, then
; we return nil).  Consecutive 'formals properties have been pushed on wrld for
; the function symbols currently being defined; in the case of a
; mutual-recursion, those properties are in reverse order from which the
; function symbols are introduced.  We are free to return nil; but we prefer,
; when possible, to return a functional substitution mapping the old functions
; to the new ones, respecting the order of definition within the respective (if
; any) mutual-recursions, but only when the input arities match up.

  (let ((old-nest (getpropc fn 'recursivep nil wrld)))
    (and old-nest
         (termination-theorem-fn-subst1 old-nest wrld))))

(defun@par translate-lmi (lmi normalizep ctx wrld state)

; Lmi is an object that specifies some instance of a theorem.  It may specify a
; substitution instance or a functional instantiation, or even some composition
; of such instances.  This function checks that lmi is meaningful and either
; causes an error or returns (as the value result of an error/value/state
; producing function) a list

; (thm constraints event-names new-entries)

; where:

; thm is a term, intuitively, the instance specified;

; constraints is a list of terms, intuitively a list of conjectures which must
; be proved in order to prove thm;

; event-names is a list of names to credit for avoiding certain proof
; obligations in the generation of the constraints; and

; new-entries is the list of new entries for the world global
; 'proved-functional-instances-alist, which we will place in a tag-tree and
; eventually using the name of the event currently being proved (if any).

; A lemma instance is (following :doc lemma-instance)

; (1) the name of a formula,
; (2) the rune of a corollary,
; (3) (:theorem formula),
; (4) (:instance lmi . substn),
; (5) (:functional-instance lmi . substn),
; (6) (:guard-theorem fn-symb) or (:guard-theorem fn-symb clean-up-flg)
;     for fn-symb a guard-verified function symbol, or
; (7) (:termination-theorem fn-symb) or (:termination-theorem! fn-symb)
;     for fn-symb a :logic mode function symbol,

; where lmi is another lemma instance and substn is a substitution of the
; appropriate type.

; Normalizep tells us whether to use the normalized body or the
; 'unnormalized-body when the lmi refers to a function definition.  We use the
; normalized body for :use hints, where added simplification can presumably
; only be helpful (and for backwards compatibility as we introduce normalizep
; in Version_2.7).  But we use the 'unnormalized-body for :by hints as a
; courtesy to the user, who probably is thinking of that rather than the
; normalized body when instantiating a definition.

  (let ((str "The object ~x0 is an ill-formed lemma instance because ~@1.  ~
              See :DOC lemma-instance.")
        (atomic-lmi-cars '(:theorem :termination-theorem :termination-theorem!
                                    :guard-theorem)))
    (cond
     ((atom lmi)
      (cond ((symbolp lmi)
             (let ((term (formula lmi normalizep wrld)))
               (cond (term (value@par (list term nil nil nil)))
                     (t (er@par soft ctx str
                          lmi
                          (msg "there is no formula associated with the name ~
                                ~x0"
                               lmi))))))
            (t (er@par soft ctx str lmi
                 "it is an atom that is not a symbol"))))
     ((and (member-eq (car lmi) atomic-lmi-cars)
           (not (and (true-listp lmi)
                     (or (= (length lmi) 2)
                         (and (member-eq (car lmi) '(:guard-theorem
                                                     :termination-theorem
                                                     :termination-theorem!))
                              (= (length lmi) 3))))))
      (er@par soft ctx str lmi
        (msg "this ~x0 lemma instance is not a true list of length 2~@1"
             (car lmi)
             (if (member-eq (car lmi) '(:guard-theorem
                                        :termination-theorem
                                        :termination-theorem!))
                 " or 3"
               ""))))
     ((eq (car lmi) :theorem)
      (er-let*@par
       ((term (translate@par (cadr lmi) t t t ctx wrld state))
        (term (value@par (remove-guard-holders term wrld))))
; known-stobjs = t (stobjs-out = t)
       (value@par (list term (list term) nil nil))))
     ((or (eq (car lmi) :instance)
          (eq (car lmi) :functional-instance))
      (cond
       ((and (true-listp lmi)
             (>= (length lmi) 2))
        (er-let*@par
         ((lst (translate-lmi@par (cadr lmi) normalizep ctx wrld state)))
         (let ((formula (car lst))
               (constraints (cadr lst))
               (event-names (caddr lst))
               (new-entries (cadddr lst))
               (substn (cddr lmi)))
           (cond
            ((eq (car lmi) :instance)
             (mv-let
               (extra-bindings-ok substn)
               (cond ((eq (car substn) :extra-bindings-ok)
                      (mv t (cdr substn)))
                     (t (mv nil substn)))
               (translate-lmi/instance@par formula constraints event-names
                                           new-entries extra-bindings-ok substn
                                           ctx wrld state)))
            (t (translate-lmi/functional-instance@par
                formula constraints event-names new-entries substn
                (global-val 'proved-functional-instances-alist wrld)
                ctx wrld state))))))
       (t (er@par soft ctx str lmi
            (msg "this ~x0 lemma instance is not a true list of length at ~
                  least 2"
                 (car lmi))))))
     ((eq (car lmi) :guard-theorem)
      (let ((fn (cadr lmi)))
        (cond ((not (and (symbolp fn)
                         (function-symbolp fn wrld)
                         (eq (symbol-class fn wrld)

; We can call guard-theorem for any :logic mode function.  However, we only
; trust that the result is a theorem when the function is already
; guard-verified.

                             :common-lisp-compliant)))
               (er@par soft ctx str lmi
                 (msg "~x0 is not a guard-verified function symbol in the ~
                       current ACL2 logical world"
                      fn)))
              (t
               (let ((term (guard-theorem fn
                                          (if (= (length lmi) 2)
                                              t
                                            (caddr lmi))
                                          nil wrld state)))
                 (value@par (list term nil nil nil)))))))
     ((member-eq (car lmi) '(:termination-theorem :termination-theorem!))
      (let ((fn (cadr lmi)))
        (cond ((not (and (symbolp fn)
                         (function-symbolp fn wrld)
                         (logicp fn (w state))))
               (er@par soft ctx str lmi
                 (msg "~x0 is not a :logic-mode function symbol in the ~
                       current ACL2 logical world"
                      fn)))
              (t
               (let ((term (termination-theorem fn wrld)))
                 (cond
                  ((and (consp term)
                        (eq (car term) :failed))
                   (cond ((eq (car lmi) :termination-theorem)
                          (er@par soft ctx str lmi
                            (msg "there is no termination theorem for ~x0.  ~
                                  ~@1"
                                 fn
                                 (cdr term))))
                         (t (value@par (list *t* nil nil nil)))))
                  ((and (cddr lmi)
                        (not (symbol-doublet-listp (caddr lmi))))
                   (er@par soft ctx str lmi
                     "the alleged functional substitution is not a list of ~
                      pairs of the form (symbol x)"))
                  ((cddr lmi)
                   (er-let*@par
                    ((alist (translate-functional-substitution@par
                             (caddr lmi) ctx wrld state)))
                    (cond
                     ((subsetp-eq (strip-cars alist)
                                  (getpropc fn 'recursivep nil wrld))
                      (value@par (list (sublis-fn-simple alist term)
                                       nil nil nil)))
                     (t (er@par soft ctx str lmi
                          "its functional substitution is illegal: the ~
                           function symbol~#1~[ ~&1 is~/s ~&1 are~] not ~
                           introduced with the function symbol ~x2"
                          lmi
                          (set-difference-eq (strip-cars alist)
                                             (getpropc fn 'recursivep nil
                                                       wrld))
                          fn)))))
                  (t (let* ((alist (termination-theorem-fn-subst fn wrld))
                            (term (cond
                                   (alist (sublis-fn-simple alist term))
                                   (t term))))
                       (value@par (list term nil nil nil))))))))))
     ((runep lmi wrld)
      (let ((term (and (not (eq (car lmi) :INDUCTION))
                       (corollary lmi wrld))))
        (cond (term (value@par (list term nil nil nil)))
              (t (er@par soft ctx str lmi
                   "there is no known formula associated with this rune")))))
     (t (er@par soft ctx str lmi
          "it is not a symbol, a rune in the current logical world, or a list ~
           whose first element is ~v2"
          (list* :INSTANCE :FUNCTIONAL-INSTANCE atomic-lmi-cars))))))

(defun@par translate-use-hint1 (arg ctx wrld state)

; Arg is a list of lemma instantiations and we return a list of the form (hyps
; constraints event-names new-entries); see translate-by-hint or translate-lmi
; for details.  In particular, hyps is a list of the instantiated theorems to
; be added as hypotheses and constraints is a list of the constraints that must
; be proved.

  (cond ((atom arg)
         (cond ((null arg) (value@par '(nil nil nil nil)))
               (t (er@par soft ctx
                    "The value of the :use hint must be a true list but your ~
                     list ends in ~x0.  See the :use discussion in :DOC hints."
                    arg))))
        (t (er-let*@par
            ((lst1 (translate-lmi@par (car arg) t ctx wrld state))
             (lst2 (translate-use-hint1@par (cdr arg) ctx wrld state)))
            (value@par (list (cons (car lst1) (car lst2))
                             (append (cadr lst1) (cadr lst2))
                             (union-eq (caddr lst1) (caddr lst2))
                             (union-equal (cadddr lst1) (cadddr lst2))))))))

(defun@par translate-use-hint (arg ctx wrld state)

; Nominally, the :use hint is followed by a list of lmi objects.
; However, if the :use hint is followed by a single lmi, we automatically
; make a singleton list out of the lmi, e.g.,

;   :use assoc-of-append
; is the same as
;   :use (assoc-of-append)
;
;   :use (:instance assoc-of-append (x a))
; is the same as
;   :use ((:instance assoc-of-append (x a)))

; This function either causes an error or returns (as the value component of
; an error/value/state triple) a list of the form
;    (lmi-lst (hyp1 ... hypn) cl k event-names new-entries),
; lmi-lst is the true-list of lmis processed, (hyp1 ... hypn) are the
; hypothesis theorems obtained, cl is a single clause that is the
; conjunction of the constraints, k is the number of conjuncts,
; event-names is a list of names to credit for avoiding certain proof
; obligations in the generation of the constraints, and new-entries is
; the list of new entries for the world global
; 'proved-functional-instances-alist.

; Note:  The subroutines of this function deal in answer pairs of the form
; ((hyp1 ... hypn) . constraints), where constraints is a list of all the
; constraint terms.  The conversion from that internal convention to the
; external one used in translated :use hints is made here.

; A Brief History of a Rapidly Changing Notation (Feb 28, 1990)

; Once upon a time, lemma instance had the form (assoc-of-append :x
; a).  We adopted the policy that if a substitution was going to be
; applied to a lemma, term, and x was in the domain of the
; substitution, then one wrote :x and wrote the substitution "flat",
; without parentheses around the variable/term pairs.  In general, :x
; meant "the variable symbol in term whose symbol name was "x"."  We
; enforced the restriction that there was at most one variable symbol
; in a stored formula with a given symbol name.

; At that time we denoted lemma instances with such notation as
; (assoc-of-append :x a :y b :z c).  Functional instances were not yet
; implemented.  But in order to disambiguate the use of a single
; lemma instance from the use of several atomic instances, e.g.,
;    :use (assoc-of-append :x a :y b :z c)
; versus
;    :use (assoc-of-append rev-rev)
; we relied on the idea that the domain elements of the substitution
; were keywords.

; The implementation of functional instantiation changed all that.
; First, we learned that the translation of a keyword domain element,
; e.g., :fn, into a function symbol could not be done in a way
; analogous to what we were doing with variables.  Which function is
; meant by :fn?  You might say, "the one with that symbol name in the
; target theorem being instantiated."  But there may be no such symbol
; in the target theorem; the user may want to instantiate :fn in some
; constraint being proved for that theorem's instantiation.  But then
; you might say "then search the constraint too for a suitable meaning
; for :fn."  Ah ha!  You can't compute the constraint until you know
; which functions are being instantiated.  So the general idea of
; using the target to translate keyword references just fails and it
; was necessary to come up with an unambiguous way of writing a
; substitution.  We temporarily adopted the idea that the "keywords"
; in flat substitutions might not be keywords at all.  E.g., you could
; write ACL2-NQTHM::X as a domain element.  That might have put into
; jeopardy their use to disambiguate :use hint.

; But simultaneously we adopted the idea that lemma instances are
; written as (:instance assoc-of-append ...) or (:functional-instance
; assoc-of-append ...).  This was done so lemma instances could be
; nested, to allow functional instances to then be instantiated.  But
; with the keyword at the beginning of a lemma instance it suddenly
; became possible to disambiguate :use hints:
;   :use (assoc-of-append rev-rev)
; can mean nothing but use two lemma instances because the argument to
; the use is not a lemma instance.

; So we were left with no compelling need to have keywords and flat
; substitutions and a lot of confusion if we did have keywords.  So we
; abandoned them in favor of the let-bindings like notation.

  (cond
   ((null arg)
    (er@par soft ctx
      "Implementation error:  Empty :USE hints should not be handled by ~
       translate-use-hint (for example, they are handled by ~
       translate-hint-settings."))
   (t (let ((lmi-lst (cond ((atom arg) (list arg))
                           ((or (member-eq (car arg)
                                           '(:instance
                                             :functional-instance
                                             :theorem
                                             :termination-theorem
                                             :termination-theorem!
                                             :guard-theorem))
                                (runep arg wrld))
                            (list arg))
                           (t arg))))
        (er-let*@par
         ((lst (translate-use-hint1@par lmi-lst ctx wrld state)))

; Lst is of the form ((hyp1 ... hypn) constraints event-names new-entries),
; where constraints is a list of constraint terms, implicitly conjoined.  We
; wish to return something of the form
; (lmi-lst (hyp1 ... hypn) constraint-cl k event-names new-entries)
; where constraint-cl is a clause that is equivalent to the constraints.

         (value@par (list lmi-lst
                          (car lst)
                          (add-literal (conjoin (cadr lst)) nil nil)
                          (length (cadr lst))
                          (caddr lst)
                          (cadddr lst))))))))

(defun convert-name-tree-to-new-name1 (name-tree char-lst sym)
  (cond ((atom name-tree)
         (cond ((symbolp name-tree)
                (mv (append (coerce (symbol-name name-tree) 'list)
                            (cond ((null char-lst) nil)
                                  (t (cons #\Space char-lst))))
                    name-tree))
               ((stringp name-tree)
                (mv (append (coerce name-tree 'list)
                            (cond ((null char-lst) nil)
                                  (t (cons #\Space char-lst))))
                    sym))
               (t (mv
                   (er hard 'convert-name-tree-to-new-name1
                       "Name-tree was supposed to be a cons tree of ~
                        symbols and strings, but this one contained ~
                        ~x0.  One explanation for this is that we ~
                        liberalized what a goal-spec could be and ~
                        forgot this function."
                       name-tree)
                   nil))))
        (t (mv-let (char-lst sym)
                   (convert-name-tree-to-new-name1 (cdr name-tree)
                                                   char-lst sym)
                   (convert-name-tree-to-new-name1 (car name-tree)
                                                   char-lst sym)))))

(defun convert-name-tree-to-new-name (name-tree wrld)

; A name-tree is just a cons tree composed entirely of strings
; and symbols.  We construct the symbol whose symbol-name is the
; string that contains the fringe of the tree, separated by
; spaces, and then we generate a new name in wrld. For example,
; if name-tree is '(("Guard Lemma for" . APP) . "Subgoal 1.3''") then we
; will return '|Guard Lemma for APP Subgoal 1.3''|, provided that is new.
; To make it new we'll start tacking on successive subscripts,
; as with gen-new-name.  The symbol we generate is interned in
; the same package as the first symbol occurring in name-tree,
; or in "ACL2" if no symbol occurs in name-tree.

  (mv-let (char-lst sym)
          (convert-name-tree-to-new-name1 name-tree
                                          nil
                                          'convert-name-tree-to-new-name)
          (gen-new-name (intern-in-package-of-symbol
                         (coerce char-lst 'string)
                         sym)
                        wrld)))

(defun@par translate-by-hint (name-tree arg ctx wrld state)

; A :BY hint must either be a single lemma instance, nil, or a new
; name which we understand the user intends will eventually become a
; lemma instance.  Nil means that we are to make up an appropriate
; new name from the goal-spec.  Note:  We can't really guarantee that
; the name we make up (or one we check for the user) is new because
; the same name may be made up twice before either is actually
; created.  But this is just a courtesy to the user anyway.  In the
; end, he'll have to get his names defthm'd himself.

; If arg is an lemma instance, then we return a list of the form (lmi-lst
; thm-cl-set constraint-cl k event-names new-entries), where lmi-lst is a
; singleton list containing the lmi in question, thm-cl-set is the set of
; clauses obtained from the instantiated theorem and which is to subsume the
; indicated goal, constraint-cl is a single clause which represents the
; conjunction of the constraints we are to establish, k is the number of
; conjuncts, event-names is a list of names to credit for avoiding certain
; proof obligations in the generation of the constraints, and new-entries will
; be used to update the world global 'proved-functional-instances-alist.

; If arg is a new name, then we return just arg itself (or the name
; generated).

  (cond ((or (and arg
                  (symbolp arg)
                  (formula arg t wrld))
             (consp arg))
         (er-let*@par
          ((lst (translate-lmi@par arg nil ctx wrld state)))

; Lst is (thm constraints event-names new-entries), where:  thm is a term;
; constraints is a list of terms whose conjunction we must prove; event-names
; is a list of names of events on whose behalf we already proved certain proof
; obligations arising from functional instantiation; and new-entries may
; eventually be added to the world global 'proved-functional-instances-alist so
; that the present event can contribute to avoiding proof obligations for
; future proofs.

          (value@par
           (list (list arg)
                 (car lst)
                 (add-literal (conjoin (cadr lst)) nil nil)
                 (length (cadr lst))
                 (caddr lst)
                 (cadddr lst)))))
        ((null arg)

; The name nil is taken to mean make up a suitable name for this subgoal.

         (value@par (convert-name-tree-to-new-name name-tree wrld)))
        ((and (symbolp arg)
              (not (keywordp arg))
              (not (equal *main-lisp-package-name* (symbol-package-name arg)))
              (new-namep arg wrld))

; The above checks are equivalent to chk-all-but-new-name and chk-just-
; new-name, but don't cause the error upon failure.  The error message
; that would otherwise be generated is confusing because the user isn't
; really trying to define arg to be something yet.

         (value@par arg))
        (t
         (er@par soft ctx
           "The :BY hint must be given a lemma-instance, nil, or a new name.  ~
            ~x0 is none of these.  See :DOC hints."
           arg))))

(defun@par translate-cases-hint (arg ctx wrld state)

; This function either causes an error or returns (as the value component of
; an error/value/state triple) a list of terms.

  (cond
   ((null arg)
    (er@par soft ctx "We do not permit empty :CASES hints."))
   ((not (true-listp arg))
    (er@par soft ctx
      "The value associated with a :CASES hint must be a true-list of terms, ~
       but ~x0 is not."
      arg))
   (t (translate-term-lst@par arg t t t ctx wrld state))))

(defun@par translate-case-split-limitations-hint (arg ctx wrld state)

; This function returns an error triple.  In the non-error case, the value
; component of the error triple is a two-element list that controls the
; case-splitting, in analogy to set-case-split-limitations.

  (declare (ignore wrld))
  #+acl2-par
  (declare (ignorable state))
  (cond ((null arg) (value@par '(nil nil)))
        ((and (true-listp arg)
              (equal (len arg) 2)
              (or (natp (car arg))
                  (null (car arg)))
              (or (natp (cadr arg))
                  (null (cadr arg))))
         (value@par arg))
        (t (er@par soft ctx
             "The value associated with a :CASE-SPLIT-LIMITATIONS hint must ~
              be either nil (denoting a list of two nils), or a true list of ~
              length two, each element which is either nil or a natural ~
              number; but ~x0 is not."
             arg))))

(defun@par translate-no-op-hint (arg ctx wrld state)
  (declare (ignore arg ctx wrld))
  #+acl2-par
  (declare (ignorable state))
  (value@par t))

(defun@par translate-error-hint (arg ctx wrld state)
  (declare (ignore wrld))
  (cond ((tilde-@p arg)
         (er@par soft ctx "~@0" arg))
        (t (er@par soft ctx
             "The :ERROR hint keyword was included among your hints, with ~
              value ~x0."
             arg))))

(defun@par translate-induct-hint (arg ctx wrld state)
  (cond ((eq arg nil) (value@par nil))
        (t (translate@par arg t t t ctx wrld state))))

; known-stobjs = t (stobjs-out = t)

; We now turn to :in-theory hints.  We develop here only enough to
; translate and check an :in-theory hint.  We develop the code for
; the in-theory event and the related deftheory event later.
; Some such code (e.g., eval-theory-expr) was developed earlier in
; support of install-event.

(defconst *built-in-executable-counterparts*

; Keep this in sync with cons-term1.

  '(acl2-numberp
    binary-* binary-+ unary-- unary-/ < car cdr
    char-code characterp code-char complex
    complex-rationalp
    #+:non-standard-analysis complexp
    coerce cons consp denominator equal
    #+:non-standard-analysis floor1
    if imagpart integerp
    intern-in-package-of-symbol numerator pkg-witness pkg-imports rationalp
    #+:non-standard-analysis realp
    realpart stringp symbol-name symbol-package-name symbolp
    #+:non-standard-analysis standardp
    #+:non-standard-analysis standard-part
    ;; #+:non-standard-analysis i-large-integer
    not))

(defconst *s-prop-theory*

; This constant is no longer used in the ACL2 system code -- generally (theory
; 'minimal-theory) is more appropriate -- but we leave it here for use by
; existing books.

; This constant is not well-named, since some of its functions are not
; propositional.  But we keep the name since this constant has been used in
; theory hints since nearly as far back as the inception of ACL2.

  (cons 'iff ; expanded in tautologyp
        *expandable-boot-strap-non-rec-fns*))

(defun new-disables (theory-tail runic-theory exception ens wrld)

; This function returns the base-symbols of runes in theory-tail that are
; enabled with respect to ens, other than the given exception.  Exception may
; be nil, in which case of course there will be no such exception, as noted in
; the comment below.

  (cond ((endp theory-tail) nil)
        ((and (enabled-runep (car theory-tail) ens wrld)
              (not (member-equal (car theory-tail) runic-theory)))
         (let ((sym (base-symbol (car theory-tail))))
           (if (eq sym exception) ; fails if exception is nil
               (new-disables (cdr theory-tail) runic-theory
                             exception ens wrld)
             (cons sym
                   (new-disables (cdr theory-tail) runic-theory
                                 exception ens wrld)))))
        (t (new-disables (cdr theory-tail) runic-theory
                         exception ens wrld))))

(defun some-new-disables-1 (theory-tail runic-theory ens wrld)

; Returns (mv allp runes), where runes consists of members of theory-tail that
; are enabled by ens and do not belong to runic-theory, and allp is true when
; runes consists of all of theory-tail (in which case the two are eq).

  (cond ((endp theory-tail) (mv t nil))
        (t (mv-let (allp rest)
             (some-new-disables-1 (cdr theory-tail) runic-theory ens wrld)
             (let ((addp (and (enabled-runep (car theory-tail) ens wrld)
                              (not (member-equal (car theory-tail) runic-theory)))))
               (cond ((and allp addp)
                      (mv t theory-tail))
                     (addp (mv nil (cons (car theory-tail) rest)))
                     (t (mv nil rest))))))))

(defun some-new-disables (theory-tail runic-theory ens wrld)

; Return a list of runes in theory-tail that are enabled (as per ens) and do
; not belong to runic-theory, unless all runes in theory-tail have those two
; properties, in which case return nil.

  (mv-let (allp runes)
    (some-new-disables-1 theory-tail runic-theory ens wrld)
    (cond (allp nil)
          (t runes))))

(defun some-new-enables-1 (theory-tail runic-theory ens wrld)

; See the analogous function some-new-disables-1.

  (cond ((endp theory-tail) (mv t nil))
        (t (mv-let (allp rest)
             (some-new-enables-1 (cdr theory-tail) runic-theory ens wrld)
             (let ((addp (and (not (enabled-runep (car theory-tail) ens wrld))
                              (member-equal (car theory-tail) runic-theory))))
               (cond ((and allp addp)
                      (mv t theory-tail))
                     (addp (mv nil (cons (car theory-tail) rest)))
                     (t (mv nil rest))))))))

(defun some-new-enables (theory-tail runic-theory ens wrld)

; See the analogous function some-new-disables.

  (mv-let (allp runes)
    (some-new-enables-1 theory-tail runic-theory ens wrld)
    (cond (allp nil)
          (t runes))))

(defun translate-in-theory-hint (expr chk-boot-strap-fns-flg ctx wrld state)

; We translate and evaluate expr and make sure that it produces a
; common theory.  We either cause an error or return the corresponding
; runic theory.

; Keep this definition in sync with minimal-theory and
; translate-in-theory-hint@par.

  (er-let* ((runic-value (eval-theory-expr expr ctx wrld state)))
    (let* ((warning-disabled-p (warning-disabled-p "Theory"))
           (ens (ens state)))
      (pprogn
       (cond
        ((or warning-disabled-p
             (f-get-global 'boot-strap-flg state)
             (not (and chk-boot-strap-fns-flg
                       (f-get-global 'verbose-theory-warning state))))
         state)
        (t
         (pprogn
          (let* ((definition-minimal-theory
                   (getpropc 'definition-minimal-theory 'theory
                             nil ; so, returns nil early in boot-strap
                             wrld))
                 (exception (and (not (simplifiable-mv-nth-p)) 'mv-nth))
                 (new-disables
                  (new-disables definition-minimal-theory runic-value
                                exception ens wrld)))
            (cond
             (new-disables
              (warning$ ctx ("Theory")
                        `("The :DEFINITION rule~#0~[ for the built-in ~
                           function ~&0 is~/s for the built-in functions ~&0 ~
                           are~] disabled by the theory expression ~x1, but ~
                           some expansions of ~#0~[its~/their~] calls may ~
                           still occur.  See :DOC theories-and-primitives."
                          (:doc theories-and-primitives)
                          (:new-disables ,new-disables)
                          (:rule-class :definition)
                          (:theory-expression ,expr))
                        new-disables
                        expr))
             (t state)))
          (let* ((executable-counterpart-minimal-theory
                  (getpropc 'executable-counterpart-minimal-theory
                            'theory
                            nil ; so, returns nil early in boot-strap
                            wrld))
                 (new-disables
                  (new-disables executable-counterpart-minimal-theory
                                runic-value nil ens wrld)))
            (cond
             (new-disables
              (warning$ ctx ("Theory")
                        `("The :EXECUTABLE-COUNTERPART rule~#0~[ for the ~
                           built-in function ~&0 is~/s for the built-in ~
                           functions ~&0 are~] disabled by the theory ~
                           expression ~x1, but some evaluations of ~
                           ~#0~[its~/their~] calls may still occur.  See :DOC ~
                           theories-and-primitives."
                          (:doc theories-and-primitives)
                          (:new-disables ,new-disables)
                          (:rule-class :executable-counterpart)
                          (:theory-expression ,expr))
                        new-disables
                        expr))
             (t state)))

; Below, we warn if the definition of any primitive is being disabled or
; enabled, with the exception that there is no warning if they are all
; transitioning from enabled to disabled or vice-versa.  (The preceding case
; already handles this for executable-counterparts.)  The exception covers the
; case that one transitions from some very small theory, e.g., (theory
; 'minimal-theory), back to a more "normal" theory, e.g., (theory
; 'ground-zero).  An entirely different way to handle primitives would be not
; to associate them with runes.  But as of this writing in Oct. 2017, those
; primitives have had 'runic-mapping-pairs properties for a long time, and we
; are nervous about either changing that or ignoring those properties when
; producing theories (see for example function-theory-fn1).

; Note that the code below doesn't warn when we enable a primitive that is
; already enabled.  For example, immediately after starting up ACL2, the event
; (in-theory (enable cons)) produces no warning, because the definition of cons
; was already enabled and warnings are based on the theory expression, as
; opposed to the theory it produces.  It might be feasible to let
; union-current-theory-fn warn when it encounters a primitive, much as we cause
; errors when theory functions encounter bad runes.  But that's really not the
; right thing to do; for example, for all we know a macro is generating the
; expression (set-different-theories ... (enable ...)), with no intention of
; enabling anything.

          (let* ((acl2-primitives-theory
                  (getpropc 'acl2-primitives 'theory
                            nil ; so, returns nil early in boot-strap
                            wrld))
                 (new-primitive-disables
                  (some-new-disables acl2-primitives-theory runic-value ens
                                     wrld))
                 (new-primitive-enables

; The following is nil if all definitions of primitives are disabled about to
; be enabled; see the discussion above.

                  (some-new-enables acl2-primitives-theory runic-value ens wrld)))
            (cond
             ((or new-primitive-disables new-primitive-enables)
              (warning$ ctx ("Theory")
                        `("There is no effect from disabling or enabling ~
                           :DEFINITION rules for primitive functions (see ~
                           :DOC primitive).  For the expression ~x0, the ~
                           attempt to ~@1 will therefore have no effect for ~
                           ~#2~[its definition~/their definitions~].  See ~
                           :DOC theories-and-primitives."
                          (:doc theories-and-primitives)
                          (:new-primitive-disables ,new-primitive-disables)
                          (:new-primitive-enables ,new-primitive-enables)
                          (:theory-expression ,expr))
                        expr
                        (cond
                         ((and new-primitive-disables new-primitive-enables)
                          (msg "disable ~&0 and enable ~&1"
                               (strip-base-symbols new-primitive-disables)
                               (strip-base-symbols new-primitive-enables)))
                         (new-primitive-disables
                          (msg "disable ~&0"
                               (strip-base-symbols new-primitive-disables)))
                         (t ; new-primitive-enables
                          (msg "enable ~&0"
                               (strip-base-symbols new-primitive-enables))))
                        (cond
                         ((or (and new-primitive-disables new-primitive-enables)
                              (cdr new-primitive-disables)
                              (cdr new-primitive-enables))
                          1)
                         (t 0))))
             (t state))))))
       (value runic-value)))))

#+acl2-par
(defun translate-in-theory-hint@par (expr chk-boot-strap-fns-flg ctx wrld
                                          state)

; We translate and evaluate expr and make sure that it produces a
; common theory.  We either cause an error or return the corresponding
; runic theory.

; Keep this definition in sync with minimal-theory and
; translate-in-theory-hint.

  (declare (ignorable chk-boot-strap-fns-flg)) ; suppress irrelevance warning
  (er-let*@par
   ((runic-value (eval-theory-expr@par expr ctx wrld state)))
   (let* ((warning-disabled-p (warning-disabled-p "Theory"))
          (ens (ens state)))
     (prog2$
      (cond
       ((or warning-disabled-p
            (f-get-global 'boot-strap-flg state)
            (not (and chk-boot-strap-fns-flg
                      (f-get-global 'verbose-theory-warning state))))
        nil)
       (t
        (progn$
         (let* ((definition-minimal-theory
                  (getpropc 'definition-minimal-theory 'theory
                            nil ; so, returns nil early in boot-strap
                            wrld))
                (exception (and (not (simplifiable-mv-nth-p)) 'mv-nth))
                (new-disables
                 (new-disables definition-minimal-theory runic-value
                               exception ens wrld)))
           (cond
            (new-disables
             (warning$@par ctx ("Theory")
               `("The :DEFINITION rule~#0~[ for the built-in function ~&0 ~
                  is~/s for the built-in functions ~&0 are~] disabled by the ~
                  theory expression ~x1, but some expansions of ~
                  ~#0~[its~/their~] calls may still occur.  See :DOC ~
                  theories-and-primitives."
                 (:doc theories-and-primitives)
                 (:new-disables ,new-disables)
                 (:rule-class :definition)
                 (:theory-expression ,expr))
               new-disables
               expr))
            (t nil)))
         (let* ((executable-counterpart-minimal-theory
                 (getpropc 'executable-counterpart-minimal-theory
                           'theory
                           nil ; so, returns nil early in boot-strap
                           wrld))
                (new-disables
                 (new-disables executable-counterpart-minimal-theory
                               runic-value nil ens wrld)))
           (cond
            (new-disables
             (warning$@par ctx ("Theory")
               `("The :EXECUTABLE-COUNTERPART rule~#0~[ for the built-in ~
                  function ~&0 is~/s for the built-in functions ~&0 are~] ~
                  disabled by the theory expression ~x1, but some evaluations ~
                  of ~#0~[its~/their~] calls may still occur.  See :DOC ~
                  theories-and-primitives."
                 (:doc theories-and-primitives)
                 (:new-disables ,new-disables)
                 (:rule-class :executable-counterpart)
                 (:theory-expression ,expr))
               new-disables
               expr))
            (t nil)))

; For the next case, see the correponding comment in
; translate-in-theory-hint@par.

         (let* ((acl2-primitives-theory
                 (getpropc 'acl2-primitives 'theory
                           nil ; so, returns nil early in boot-strap
                           wrld))
                (new-primitive-disables
                 (some-new-disables acl2-primitives-theory runic-value ens
                                    wrld))
                (new-primitive-enables
                 (some-new-enables acl2-primitives-theory runic-value ens wrld)))
           (cond
            ((or new-primitive-disables new-primitive-enables)
             (warning$@par ctx ("Theory")
               `("There is no effect from disabling or enabling :DEFINITION ~
                  rules for primitive functions (see :DOC primitive).  For ~
                  the expression ~x0, the attempt to ~@1 will therefore have ~
                  no effect for ~#2~[its definition~/their definitions~].  ~
                  See :DOC theories-and-primitives."
                 (:doc theories-and-primitives)
                 (:new-primitive-disables ,new-primitive-disables)
                 (:new-primitive-enables ,new-primitive-enables)
                 (:theory-expression ,expr))
               expr
               (cond
                ((and new-primitive-disables new-primitive-enables)
                 (msg "disable ~&0 and enable ~&1"
                      (strip-base-symbols new-primitive-disables)
                      (strip-base-symbols new-primitive-enables)))
                (new-primitive-disables
                 (msg "disable ~&0"
                      (strip-base-symbols new-primitive-disables)))
                (t ; new-primitive-enables
                 (msg "enable ~&0"
                      (strip-base-symbols new-primitive-enables))))
               (cond
                ((or (and new-primitive-disables new-primitive-enables)
                     (cdr new-primitive-disables)
                     (cdr new-primitive-enables))
                 1)
                (t 0))))
            (t nil))))))
      (value@par runic-value)))))

(defun non-function-symbols (lst wrld)
  (cond ((null lst) nil)
        ((function-symbolp (car lst) wrld)
         (non-function-symbols (cdr lst) wrld))
        (t (cons (car lst)
                 (non-function-symbols (cdr lst) wrld)))))

(defun collect-non-logic-mode (alist wrld)
  (cond ((null alist) nil)
        ((and (function-symbolp (caar alist) wrld)
              (logicp (caar alist) wrld))
         (collect-non-logic-mode (cdr alist) wrld))
        (t (cons (caar alist)
                 (collect-non-logic-mode (cdr alist) wrld)))))

(defun@par translate-bdd-hint1 (top-arg rest ctx wrld state)
  (cond
   ((null rest)
    (value@par nil))
   (t (let ((kwd (car rest)))
        (er-let*@par
         ((cdar-alist
           (case kwd
             (:vars
              (cond
               ((eq (cadr rest) t)
                (value@par t))
               ((not (true-listp (cadr rest)))
                (er@par soft ctx
                  "The value associated with :VARS in the :BDD hint must ~
                   either be T or a true list, but ~x0 is neither."
                  (cadr rest)))
               ((collect-non-legal-variableps (cadr rest))
                (er@par soft ctx
                  "The value associated with :VARS in the :BDD hint must ~
                   either be T or a true list of variables, but in the :BDD ~
                   hint ~x0, :VARS is associated with the following list of ~
                   non-variables:  ~x1."
                  top-arg
                  (collect-non-legal-variableps (cadr rest))))
               (t (value@par (cadr rest)))))
             (:prove
              (cond ((member-eq (cadr rest) '(t nil))
                     (value@par (cadr rest)))
                    (t (er@par soft ctx
                         "The value associated with ~x0 in the :BDD hint ~x1 ~
                          is ~x2, but it needs to be t or nil."
                         kwd top-arg (cadr rest)))))
             (:literal
              (cond ((member-eq (cadr rest) '(:conc :all))
                     (value@par (cadr rest)))
                    ((and (integerp (cadr rest))
                          (< 0 (cadr rest)))

; The user provides a 1-based index, but we want a 0-based index.

                     (value@par (1- (cadr rest))))
                    (t (er@par soft ctx
                         "The value associated with :LITERAL in a :BDD hint ~
                          must be either :CONC, :ALL, or a positive integer ~
                          (indicating the index, starting with 1, of a ~
                          hypothesis). The value ~x0 from the :BDD hint ~x1 ~
                          is therefore illegal."
                         (cadr rest) top-arg))))
             (:bdd-constructors
              (cond ((and (consp (cadr rest))
                          (eq (car (cadr rest)) 'quote)
                          (consp (cdr (cadr rest)))
                          (null (cddr (cadr rest))))
                     (er@par soft ctx
                       "The value associated with :BDD-CONSTRUCTORS must be a ~
                        list of function symbols.  It should not be quoted, ~
                        but the value supplied is of the form (QUOTE x)."))
                    ((not (symbol-listp (cadr rest)))
                     (er@par soft ctx
                       "The value associated with :BDD-CONSTRUCTORS must be a ~
                        list of symbols, but ~x0 ~ is not."
                       (cadr rest)))
                    ((all-function-symbolps (cadr rest) wrld)
                     (value@par (cadr rest)))
                    (t (er@par soft ctx
                         "The value associated with :BDD-CONSTRUCTORS must be ~
                          a list of :logic mode function symbols, but ~&0 ~
                          ~#0~[is~/are~] not."
                         (collect-non-logic-mode

; This is an odd construct, but its saves us from defining a new function since
; we use collect-non-logic-mode elsewhere anyhow.

                          (pairlis$ (cadr rest) nil)
                          wrld)))))
             (otherwise
              (er@par soft ctx
                "The keyword ~x0 is not a legal keyword for a :BDD hint.  The ~
                 hint ~x1 is therefore illegal.  See :DOC hints."
                (car rest) top-arg)))))
         (er-let*@par
          ((cdr-alist
            (translate-bdd-hint1@par top-arg (cddr rest) ctx wrld state)))
          (value@par (cons (cons kwd cdar-alist) cdr-alist))))))))

(defun@par translate-bdd-hint (arg ctx wrld state)

; Returns an alist associating each of the permissible keywords with a value.

  (cond
   ((not (keyword-value-listp arg))
    (er@par soft ctx
      "The value associated with a :BDD hint must be a list of the form (:kw1 ~
       val1 :kw2 val2 ...), where each :kwi is a keyword.  However, ~x0 does ~
       not have this form."
      arg))
   ((not (assoc-keyword :vars arg))
    (er@par soft ctx
      "The value associated with a :BDD hint must include an assignment for ~
       :vars, but ~x0 does not."
      arg))
   (t (translate-bdd-hint1@par arg arg ctx wrld state))))

(defun@par translate-nonlinearp-hint (arg ctx wrld state)
  (declare (ignore wrld))
  #+acl2-par
  (declare (ignorable state))
  (if (or (equal arg t)
          (equal arg nil))
      (value@par arg)
    (er@par soft ctx
      "The only legal values for a :nonlinearp hint are T and NIL, but ~x0 is ~
       neither of these."
      arg)))

(defun@par translate-backchain-limit-rw-hint (arg ctx wrld state)
  (declare (ignore wrld))
  (if (or (natp arg)
          (equal arg nil))
      (value@par arg)
    (er@par soft ctx
      "The only legal values for a :backchain-limit-rw hint are NIL and ~
       natural numbers, but ~x0 is neither of these."
      arg)))

(defun@par translate-no-thanks-hint (arg ctx wrld state)
  (declare (ignore ctx wrld))
  #+acl2-par
  (declare (ignorable state))
  (value@par arg))

(defun@par translate-reorder-hint (arg ctx wrld state)
  (declare (ignore wrld))
  #+acl2-par
  (declare (ignorable state))
  (if (and (pos-listp arg)
           (no-duplicatesp arg))
      (value@par arg)
    (er@par soft ctx
      "The value for a :reorder hint must be a true list of positive integers ~
       without duplicates, but ~x0 is not."
      arg)))

(defun arity-mismatch-msg (sym expected-arity wrld)

; This little function avoids code replication in
; translate-clause-processor-hint.  Expected-arity is either a number,
; indicating the expected arity, or of the form (list n), where n is the
; minimum expected arity.  We return the arity of sym (or its macro alias) if
; it is not as expected, and we return t if sym has no arity and is not a
; macro.  Otherwise we return nil.  So if sym is a macro, then we return nil
; even though there might be a mismatch (presumably to be detected by other
; means).

  (let* ((fn (or (deref-macro-name sym (macro-aliases wrld))
                 sym))
         (arity (arity fn wrld)))
    (cond
     ((null arity)
      (if (getpropc sym 'macro-body nil wrld)
          nil
        (msg "~x0 is neither a function symbol nor a macro name"
             sym)))
     ((and (consp expected-arity)
           (< arity (car expected-arity)))
      (msg "~x0 has arity ~x1 (expected arity of at least ~x2 for this hint ~
            syntax)"
           fn arity (car expected-arity)))
     ((and (integerp expected-arity)
           (not (eql expected-arity arity)))
      (msg "~x0 has arity ~x1 (expected arity ~x2 for this hint syntax)"
           fn arity expected-arity))
     (t nil))))

(defun macro-minimal-arity1 (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) 0)
        ((lambda-keywordp (car lst))
         0)
        (t (1+ (macro-minimal-arity1 (cdr lst))))))

(defun macro-minimal-arity (sym default wrld)
  (let ((args (getpropc sym 'macro-args default wrld)))
    (macro-minimal-arity1 (if (eq (car args) '&whole)
                              (cddr args)
                            args))))

(defun translate-clause-processor-hint/symbol-to-call (sym wrld)

; Sym is a symbol provided as a clause-processor hint, as an abbreviation for a
; suitable function call.  We return either a function call of the form (sym
; CLAUSE), (sym CLAUSE nil), or (sym CLAUSE nil st1 st2 ...), depending on the
; stobjs-out of sym, or else an error message suitable for a fmt ~@ directive.

  (declare (xargs :guard (and (symbolp sym)
                              (plist-worldp wrld))))
  (cond
   ((getpropc sym 'macro-body nil wrld)
    (case (macro-minimal-arity sym nil wrld)
      (0
       "it is the name of a macro that has no required arguments")
      (1
       (list sym 'CLAUSE))
      (2
       (list sym 'CLAUSE nil))
      (t "it is the name of a macro that has more than two required arguments")))
   (t
    (let ((stobjs-in (stobjs-in sym wrld))
          (stobjs-out (if (member-eq sym *stobjs-out-invalid*)
                          :none
                        (stobjs-out sym wrld))))
      (cond
       ((null stobjs-in)
        (cond
         ((function-symbolp sym wrld)
          "it is a function of no arguments")
         (t "it is not a function symbol or macro name")))
       ((or (car stobjs-in)
            (cadr stobjs-in))
        (msg "it is a function whose ~n0 input is a stobj"
             (list (if (car stobjs-in) 1 2))))
       ((member-eq nil (cddr stobjs-in))
        "it is function symbol with a non-stobj input other than the first two")
       ((eq stobjs-out :none) ; IF or RETURN-LAST; goofy hint
        "it is a function symbol whose output signature is unknown")
       ((or (car stobjs-out)
            (cadr stobjs-out))
        (msg "it is a function whose ~n0 output is a stobj"
             (list (if (car stobjs-out) 1 2))))
       ((member-eq nil (cddr stobjs-out))
        "it is a function symbol with a non-stobj output other than the first ~
         or second output")
       (t (list* sym 'CLAUSE (cdr stobjs-in))))))))

(defun@par translate-clause-processor-hint (form ctx wrld state)

; We are given the hint :clause-processor form.  We return an error triple
; whose value in the non-error case is a clause-processor-hint record
; consisting of the corresponding translated term (a legal call of a
; clause-processor), its associated stobjs-out, and a Boolean indicator of
; whether the term is a call of a verified clause processor.

; Each of the following cases shows legal hint syntax for a signature (or in
; the third case, a class of signatures).

; For signature ((cl-proc cl) => cl-list):
; :CLAUSE-PROCESSOR cl-proc
; :CLAUSE-PROCESSOR (:FUNCTION cl-proc)
; :CLAUSE-PROCESSOR (cl-proc CLAUSE)
;    or any form macroexpanding to (cl-proc &) with at most CLAUSE free

; For signature ((cl-proc cl hint) => cl-list):
; :CLAUSE-PROCESSOR (:FUNCTION cl-proc :HINT hint)
; :CLAUSE-PROCESSOR (cl-proc CLAUSE hint)
;    or any term macroexpanding to (cl-proc & &) with at most CLAUSE free

; For signature ((cl-proc cl hint stobj1 ... stobjk) =>
;                (mv erp cl-list stobj1 ... stobjk &optional summary-data)):
; :CLAUSE-PROCESSOR (:FUNCTION cl-proc :HINT hint)
; :CLAUSE-PROCESSOR (cl-proc CLAUSE hint stobj1 ... stobjk):
;    or any term macroexpanding to (cl-proc & & stobj1 ... stobjk)
;    where CLAUSE is the only legal non-stobj free variable

  #+acl2-par
  (declare (ignorable state))
  (let ((err-msg (msg "The form ~x0 is not a legal value for a ~
                       :clause-processor hint because ~@1.  See :DOC ~
                       clause-processor."
                      form)))
    (er-let*@par
     ((form
       (cond
        ((symbolp form)
         (let ((x (translate-clause-processor-hint/symbol-to-call form wrld)))
           (cond ((msgp x) (er@par soft ctx "~@0" err-msg x))
                 (t (value@par x)))))
        ((atom form)
         (er@par soft ctx "~@0" err-msg
           "it is an atom that is not a symbol"))
        ((not (true-listp form))
         (er@par soft ctx "~@0" err-msg
           "it is a cons that is not a true-listp"))
        (t (case-match form
             ((':function cl-proc)
              (cond
               ((symbolp cl-proc)
                (let ((msg (arity-mismatch-msg cl-proc 1 wrld)))
                  (cond (msg (er@par soft ctx "~@0" err-msg msg))
                        (t (value@par (list cl-proc 'clause))))))
               (t (er@par soft ctx "~@0" err-msg
                    "the :FUNCTION is not a symbol"))))
             ((':function cl-proc ':hint hint)
              (cond ((symbolp cl-proc)
                     (let ((msg
                            (arity-mismatch-msg cl-proc '(2) wrld)))
                       (cond
                        (msg (er@par soft ctx "~@0" err-msg msg))
                        (t (value@par
                            (list* cl-proc
                                   'clause
                                   hint
                                   (cddr (stobjs-in cl-proc wrld))))))))
                    (t (er@par soft ctx "~@0" err-msg
                         "the :FUNCTION is an atom that is not a symbol"))))
             (& (value@par form)))))))
     (mv-let@par
      (erp term bindings state)
      (translate1@par form
                      :stobjs-out ; form must be executable
                      '((:stobjs-out . :stobjs-out))
                      t ctx wrld state)
      (cond
       (erp (er@par soft ctx "~@0" err-msg
              "it was not successfully translated (see error message above)"))
       ((or (variablep term)
            (fquotep term)
            (flambda-applicationp term))
        (er@par soft ctx "~@0" err-msg
          "it is not (even after doing macroexpansion) a call of a function ~
           symbol"))
       (t
        (let ((verified-p
               (getpropc (ffn-symb term) 'clause-processor nil wrld)))

; If a verified clause processor has a well-formedness guarantee then the
; value of the property is the guarantee ((name fn thm-name1) . arity-alist);
; if it has no guarantee (but is a verified processor) the property is T.
; This guarantee (or t) is put into the :verified-p field of the resulting
; clause-processor-hint.

          (cond
           ((not (or verified-p
                     (assoc-eq (ffn-symb term)
                               (table-alist 'trusted-cl-proc-table
                                            wrld))))
            (er@par soft ctx "~@0" err-msg
              "it is not a call of a clause-processor function"))
           ((not (eq (fargn term 1) 'clause))
            (er@par soft ctx "~@0" err-msg
              "its first argument is not the variable, CLAUSE"))
           ((set-difference-eq (non-stobjps (all-vars term) t wrld)
                               '(clause))
            (er@par soft ctx "~@0" err-msg
              (msg "it contains the free variable~#0~[~/s~] ~&0, but the only ~
                    legal variable (not including stobjs) is ~x1"
                   (reverse
                    (set-difference-eq (non-stobjps (all-vars term) t wrld)
                                       '(clause)))
                   'clause)))

; #+ACL2-PAR note: Here, we could check that clause-processors do not modify
; state when waterfall-parallelism is enabled.  However, since performing the
; check in eval-clause-processor@par suffices, we do not perform the check
; here.

           (t (value@par (make clause-processor-hint
                               :term term
                               :stobjs-out (translate-deref :stobjs-out
                                                            bindings)
                               :verified-p verified-p)))))))))))

; We next develop code for :custom hints.  See the Essay on the Design of
; Custom Keyword Hints.

(defun@par translate-custom-keyword-hint (arg uterm2 ctx wrld state)

; We run the checker term for the associated custom keyword and handle
; any error it generates.  But if no error is generated, the
; translation of arg (the user-supplied value for the custom keyword)
; is arg itself.

; Why do we not allow non-trivial translation of custom keyword hint
; values?  The main reason is that custom keyword hints do not see the
; translated values of common standard hints so why should they expect
; to see the translated values of custom hints?  While the author of
; custom keyword :key1 might like its argument to be translated, he
; probably doesn't want to know about the translated form of other
; custom keyword values.  Finally, when custom keyword hints generate
; new hints, they cannot be expected to translate their values.  And
; if they didn't translate their values then after one round of custom
; hint evaluation we could have a mix of translated and untranslated
; hint values: standard hints would not be translated -- no user wants
; to know the internal form of lmi's or theories! -- and some custom
; hint values would be translated and others wouldn't.  Furthermore,
; it is impossible to figure out which are which.  The only solution
; is to keep everything in untranslated form.  Example:
; Let :key1, :key2, and :key3 be custom keywords and suppose the user
; wrote the hint

;    :key1 val1  :key2 val2 :in-theory (enable foo)

; If we allowed non-trivial translation of custom hints, then at
; translate-time we'd convert that to

;    :key1 val1' :key2 val2' :in-theory (enable foo)

; Note the mix.  Then at prove-time we'd run :key1's generator on
; val1' and the whole hint.  It might return

;                :key2 val2' :key3 val3 :in-theory (enable foo)

; Note the additional mix.  We can't tell what's untranslated and what
; isn't, unless we made custom hint authors translate all custom
; hints, even those they don't "own."

  (er-progn@par (xtrans-eval@par #-acl2-par uterm2
                                 #+acl2-par
                                 (serial-first-form-parallel-second-form@par
                                  uterm2
                                  (if (equal uterm2 '(value t)) t uterm2))
                                 (list (cons 'val arg)
                                       (cons 'world wrld)
                                       (cons 'ctx ctx))
                                 t ; trans-flg
                                 t ; ev-flg
                                 ctx
                                 state
                                 t)
                (value@par arg)))

(defun custom-keyword-hint (key wrld)

; If key is a custom keyword hint, we return (mv t ugterm ucterm); else
; (mv nil nil nil).  The terms are untranslated.

  (let ((temp (assoc-eq key (table-alist 'custom-keywords-table wrld))))
    (cond
     (temp
      (mv t (car (cdr temp)) (cadr (cdr temp))))
     (t (mv nil nil nil)))))

(defun remove-all-no-ops (key-val-lst)
  (cond ((endp key-val-lst) nil)
        ((eq (car key-val-lst) :no-op)
         (remove-all-no-ops (cddr key-val-lst)))
        (t (cons (car key-val-lst)
                 (cons (cadr key-val-lst)
                       (remove-all-no-ops (cddr key-val-lst)))))))

(defun remove-redundant-no-ops (key-val-lst)

; We return a keyword value list equivalent to key-val-lst but
; containing at most one :NO-OP setting on the front.  We don't even
; add that unless the hint would be empty otherwise.  The associated
; value is always T, no matter what the user wrote.

; (:INDUCT term :NO-OP T :IN-THEORY x :NO-OP NIL)
;   => (:INDUCT term :IN-THEORY x)

; (:NO-OP 1 :NO-OP 2) => (:NO-OP T)

  (cond
   ((assoc-keyword :no-op key-val-lst)
    (let ((temp (remove-all-no-ops key-val-lst)))
      (cond (temp temp)
            (t '(:no-op t)))))
   (t key-val-lst)))

(defun find-first-custom-keyword-hint (user-hints wrld)

; User-hints is a keyword value list of the form (:key1 val1 :key2
; val2 ...).  We look for the first :keyi in user-hints that is a
; custom keyword hint, and if we find it, we return (mv keyi vali
; uterm1 uterm2), where uterm1 is the untranslated generator for keyi
; and uterm2 is the untranslated checker.

  (cond
   ((endp user-hints) (mv nil nil nil nil))
   (t (mv-let (flg uterm1 uterm2)
              (custom-keyword-hint (car user-hints) wrld)
              (cond
               (flg
                (mv (car user-hints)
                    (cadr user-hints)
                    uterm1
                    uterm2))
               (t (find-first-custom-keyword-hint (cddr user-hints) wrld)))))))

(defconst *custom-keyword-max-iterations*
  100)

(defun@par custom-keyword-hint-interpreter1
  (keyword-alist max specified-id id clause wrld
                 stable-under-simplificationp hist pspv ctx state
                 keyword-alist0 eagerp)

; On the top-level call, keyword-alist must be known to be a keyword
; value list, e.g., (:key1 val1 ... keyn valn).  On subsequent calls,
; that is guaranteed.  This function returns an error triple
; (mv erp val state).  But a little more than usual is being passed
; back in the erp=t case.

; If erp is nil: val is either nil, meaning that the custom keyword
; hint did not apply or is a new keyword-alist to be used as the hint.
; That hint will be subjected to standard hint translation.

; If erp is t, then an error has occurred and the caller should abort
; -- UNLESS it passed in eagerp=t and the returned val is the symbol
; WAIT.  If eagerp is t we are trying to evaluate the custom keyword
; hint at pre-process time rather than proof time and don't have
; bindings for some variables.  In that case, an ``error'' is signaled
; with erp t but the returned val is the symbol WAIT, meaning it was
; impossible to eagerly evaluate this form.

  (cond
   ((equal specified-id id)

; This is the clause to which this hint applies.

    (mv-let
     (keyi vali uterm1 uterm2)
     (find-first-custom-keyword-hint keyword-alist wrld)
     (cond
      ((null keyi)

; There are no custom keyword hints in the list.  In this case,
; we're done and we return keyword-alist.

       (value@par keyword-alist))
      ((zp max)
       (er@par soft ctx
         "We expanded the custom keyword hints in ~x0 a total of ~x1 times ~
          and were still left with a hint containing custom keywords, namely ~
          ~x2."
         keyword-alist0
         *custom-keyword-max-iterations*
         keyword-alist))
      (t
       (let ((checker-bindings
              (list (cons 'val vali)
                    (cons 'world wrld)
                    (cons 'ctx ctx))))
         (er-progn@par
          (xtrans-eval@par #-acl2-par uterm2

; Parallelism wart: Deal with the following comment, which appears out of date
; as of 2/4/2012.
; The following change doesn't seem to matter when we run our tests.  However,
; we include it, because from looking at the code, David Rager perceives that
; it can't hurt and that it might help.  It may turn out that the change to
; translate-custom-keyword-hint (which performs a similar replacement),
; supersedes this change, because that occurs earlier in the call stack (before
; the waterfall).  David Rager suspects that the call to
; custom-keyword-hint-interpreter1@par is used inside the waterfall (perhaps
; when the custom keyword hint process it told to 'wait and deal with the hint
; later).  If that is the case, then this replacement is indeed necessary!

                           #+acl2-par
                           (serial-first-form-parallel-second-form@par
                            uterm2
                            (if (equal uterm2 '(value t)) t uterm2))
                           checker-bindings
                           t ; trans-flg = t
                           t ; ev-flg = t
                           ctx state t)

; We just evaluated the checker term and it did not cause an error.
; We ignore its value (though er-let* doesn't).

          (mv-let@par
           (erp val state)
           (xtrans-eval@par uterm1
                            (cond
                             (eagerp

; We are trying to evaluate the generator eagerly.  That means that
; our given values for some dynamic variables, CLAUSE,
; STABLE-UNDER-SIMPLIFICATIONP, HIST, and PSPV are bogus.  We thus
; don't pass them in and we tell xtrans-eval it doesn't really have to
; ev the term if it finds unbound vars.

                              (list* (cons 'keyword-alist keyword-alist)
                                     (cons 'id id)
;                                 (cons 'clause clause) ; bogus
;                                 (cons 'stable-under-simplificationp
;                                       stable-under-simplificationp)
;                                 (cons 'hist hist)
;                                 (cons 'pspv pspv)
                                     checker-bindings))
                             (t

; Otherwise, we want all the bindings:

                              (list* (cons 'keyword-alist keyword-alist)
                                     (cons 'id id)
                                     (cons 'clause clause) ; bogus
                                     (cons 'stable-under-simplificationp
                                           stable-under-simplificationp)
                                     (cons 'hist hist)
                                     (cons 'pspv pspv)
                                     checker-bindings)))
                            t              ; trans-flg
                            (if eagerp nil t) ; ev-flg
                            ctx
                            state
                            t)
           (cond
            (erp

; If an error was caused, there are two possibilities.  One is that
; the form actually generated an error.  But the other is that we were
; trying eager evaluation with insufficient bindings.  That second
; case is characterized by eagerp = t and val = WAIT.  In both cases,
; we just pass it up.

             (mv@par erp val state))

; If no error was caused, we check the return value for our invariant.

            ((not (keyword-value-listp val))
             (er@par soft ctx
               "The custom keyword hint ~x0 in the context below generated a ~
                result that is not of the form (:key1 val1 ... :keyn valn), ~
                where the :keyi are keywords. The context is ~y1, and the ~
                result generated was ~y2."
               keyi
               keyword-alist
               val))
            (t

; We now know that val is a plausible new keyword-alist and replaces
; the old one.

             (pprogn@par
              (cond
               ((f-get-global 'show-custom-keyword-hint-expansion state)
                (io?@par prove nil state
                         (keyi id  keyword-alist val)
                         (fms "~%(Advisory from ~
                               show-custom-keyword-hint-expansion:  The ~
                               custom keyword hint ~x0, appearing in ~@1, ~
                               transformed~%~%~Y23,~%into~%~%~Y43.)~%"
                              (list
                               (cons #\0 keyi)
                               (cons #\1 (tilde-@-clause-id-phrase id))
                               (cons #\2 (cons
                                          (string-for-tilde-@-clause-id-phrase id)
                                          keyword-alist))
                               (cons #\3 (term-evisc-tuple nil state))
                               (cons #\4 (cons
                                          (string-for-tilde-@-clause-id-phrase id)
                                          val)))
                              (proofs-co state)
                              state
                              nil)))
               (t (state-mac@par)))
              (custom-keyword-hint-interpreter1@par
               val
               (- max 1)
               specified-id
               id clause wrld stable-under-simplificationp
               hist pspv ctx state
               keyword-alist0 eagerp)))))))))))
   (t (value@par nil))))

(defun@par custom-keyword-hint-interpreter
  (keyword-alist specified-id
                 id clause wrld stable-under-simplificationp
                 hist pspv ctx state eagerp)

; Warning: If you change or rearrange the arguments of this function,
; be sure to change custom-keyword-hint-in-computed-hint-form and
; put-cl-id-of-custom-keyword-hint-in-computed-hint-form.

; This function evaluates the custom keyword hints in keyword-alist.
; It either signals an error or returns as the value component of its
; error triple a new keyword-alist.

; Eagerp should be set to t if this is an attempt to expand the custom
; keyword hints at pre-process time.  If eagerp = t, then it is
; assumed that CLAUSE, STABLE-UNDER-SIMPLIFICATIONP, HIST, and
; PSPV are bogus (nil).

; WARNING: This function should be called from an mv-let, not an
; er-let*!  The erroneous return from this function should be handled
; carefully when eagerp = t.  It is possible in that case that the
; returned value, val, of (mv t erp state), is actually the symbol
; WAIT.  This means that during the eager expansion of some custom
; keyword hint we encountered a hint that required the dynamic
; variables.  It is not strictly an error, i.e., the caller shouldn't
; abort.

  (custom-keyword-hint-interpreter1@par
   keyword-alist *custom-keyword-max-iterations* specified-id id clause wrld
   stable-under-simplificationp hist pspv ctx state keyword-alist eagerp))

(defun custom-keyword-hint-in-computed-hint-form (computed-hint-tuple)

; Note:  Keep this in sync with eval-and-translate-hint-expression.
; That function uses the AND test below but not the rest, because it
; is dealing with the term itself, not the tuple.

; We assume computed-hint-tuple is the internal form of a computed
; hint.  If it is a custom keyword hint, we return the non-nil keyword
; alist supplied by the user.  Otherwise, nil.

; A translated computed hint has the form
; (EVAL-AND-TRANSLATE-HINT-EXPRESSION name-tree stablep term) and we
; assume that computed-hint-tuple is of that form.  A custom keyword
; hint is coded as a computed hint, where term, above, is
; (custom-keyword-hint-interpreter '(... :key val ...) 'cl-id ...)
; We insist that the keyword alist is a quoted constant (we will
; return its evg).  We also insist that the cl-id is a quoted
; constant.

  (let ((term (nth 3 computed-hint-tuple)))
    (cond ((and (nvariablep term)
                (not (fquotep term))

; Parallelism blemish: we do not believe that the quoting below of
; "custom-keyword-hint-interpreter@par" is a problem (as compared to the serial
; case).  One can issue a tags search for 'custom-keyword-hint-interpreter, and
; find some changed comparisons.  We believe that Matt K. and David R. began to
; look into this, and we were not aware of any problems, so we have decided not
; to try to think it all the way through.

                (serial-first-form-parallel-second-form@par
                 (eq (ffn-symb term) 'custom-keyword-hint-interpreter)
                 (or (eq (ffn-symb term) 'custom-keyword-hint-interpreter)
                     (eq (ffn-symb term) 'custom-keyword-hint-interpreter@par)))
                (quotep (fargn term 1))
                (quotep (fargn term 2)))
           (cadr (fargn term 1)))
          (t nil))))

(defun@par put-cl-id-of-custom-keyword-hint-in-computed-hint-form
  (computed-hint-tuple cl-id)

; We assume the computed-hint-tuple is a computed hint tuple and has
; passed custom-keyword-hint-in-computed-hint-form.  We set the cl-id
; field to cl-id.  This is only necessary in order to fix the cl-id
; for :or hints, which was set for the goal to which the :or hint was
; originally attached.

  (let ((term (nth 3 computed-hint-tuple)))
    (list 'eval-and-translate-hint-expression
          (nth 1 computed-hint-tuple)
          (nth 2 computed-hint-tuple)
          (fcons-term* (serial-first-form-parallel-second-form@par
                        'custom-keyword-hint-interpreter
                        'custom-keyword-hint-interpreter@par)
                       (fargn term 1)
                       (kwote cl-id)
                       (fargn term 3)
                       (fargn term 4)
                       (fargn term 5)
                       (fargn term 6)
                       (fargn term 7)
                       (fargn term 8)
                       (fargn term 9)
                       (fargn term 10)
                       (fargn term 11)))))

(defun make-disjunctive-clause-id (cl-id i pkg-name)
  (change clause-id cl-id
          :case-lst
          (append (access clause-id cl-id :case-lst)
                  (list (intern$ (coerce (packn1 (list 'd i)) 'string)
                                 pkg-name)))
          :primes 0))

(defun make-disjunctive-goal-spec (str i pkg-name)
  (let ((cl-id (parse-clause-id str)))
    (string-for-tilde-@-clause-id-phrase
     (make-disjunctive-clause-id cl-id i pkg-name))))

(defun minimally-well-formed-or-hintp (val)
  (cond ((atom val)
         (equal val nil))
        (t (and (consp (car val))
                (true-listp (car val))
                (evenp (length (car val)))
                (minimally-well-formed-or-hintp (cdr val))))))

(defun split-keyword-alist (key keyword-alist)
  (cond ((endp keyword-alist) (mv nil nil))
        ((eq key (car keyword-alist))
         (mv nil keyword-alist))
        (t (mv-let (pre post)
                   (split-keyword-alist key (cddr keyword-alist))
                   (mv (cons (car keyword-alist)
                             (cons (cadr keyword-alist)
                                   pre))
                       post)))))

(defun distribute-other-hints-into-or1 (pre x post)
  (cond ((endp x) nil)
        (t (cons (append pre (car x) post)
                 (distribute-other-hints-into-or1 pre (cdr x) post)))))

(defun distribute-other-hints-into-or (keyword-alist)

; We know keyword-alist is a keyword alist, that there is exactly one :OR, and
; that the value, val, of that :OR is a true-list of non-empty
; true-lists, each of which is of even length.  We distribute the
; other hints into the :OR.  Thus, given:

; (:in-theory a :OR ((:use l1) (:use l2)) :do-not '(...))

; we return:

; ((:OR ((:in-theory a :use l1 :do-not '(...))
;        (:in-theory a :use l2 :do-not '(...)))))

  (mv-let (pre post)
          (split-keyword-alist :OR keyword-alist)
          (list :OR
                (distribute-other-hints-into-or1 pre
                                                 (cadr post)
                                                 (cddr post)))))

(defconst *hint-expression-basic-vars*
  '(id clause world stable-under-simplificationp hist pspv ctx state))

(defconst *hint-expression-override-vars*
  (cons 'keyword-alist *hint-expression-basic-vars*))

(defconst *hint-expression-backtrack-vars*
  (append '(clause-list processor)
          (remove1-eq 'stable-under-simplificationp
                      *hint-expression-basic-vars*)))

(defconst *hint-expression-all-vars*
  (union-equal *hint-expression-override-vars*
               (union-equal *hint-expression-backtrack-vars*
                            *hint-expression-basic-vars*)))

(defun@par translate-hint-expression (name-tree term hint-type ctx wrld state)

; Term can be either (a) a non-variable term or (b) a symbol.

; (a) We allow a hint of the form term, where term is a term single-threaded in
; state that returns a single non-stobj value or an error triple and contains
; no free vars other than ID, CLAUSE, WORLD, STABLE-UNDER-SIMPLIFICATIONP,
; HIST, PSPV, CTX, and STATE, except that if if hint-type is non-nil then there
; may be additional variables.
;
; If term is such a term, we return the translated hint:

; (EVAL-AND-TRANSLATE-HINT-EXPRESSION name-tree flg term')

; where term' is the translation of term and flg indicates whether
; STABLE-UNDER-SIMPLIFICATIONP occurs freely in it.

; (b) We also allow term to be a symbol denoting a 3, 4, or 7 argument function
; not involving state and returning a single value taking:

;     (i)   a clause-id, a clause, and world, or,
;     (ii)  a clause-id, a clause,     world, and
;           stable-under-simplificationp, or
;     (iii) a clause-id, a clause,     world,
;           stable-under-simplificationp, hist, pspv, and ctx.

; We ``translate'' such a function symbol into a call of the function on the
; appropriate argument variables.

; Here is a form that allows us to trace many of the functions related to
; translating hints.

; (trace$
;  (translate-hints+1)
;  (translate-hints+1@par)
;  (translate-hints2)
;  (translate-hints2@par)
;  (translate-hints1)
;  (apply-override-hints@par)
;  (apply-override-hints)
;  (translate-x-hint-value)
;  (translate-x-hint-value@par)
;  (translate-custom-keyword-hint)
;  (translate-custom-keyword-hint@par)
;  (custom-keyword-hint-interpreter@par)
;  (custom-keyword-hint-interpreter)
;  (translate-simple-or-error-triple)
;  (translate-simple-or-error-triple@par)
;  (xtrans-eval)
;  (xtrans-eval-with-ev-w)
;  (eval-and-translate-hint-expression)
;  (eval-and-translate-hint-expression@par)
;  (translate-hint-expression@par)
;  (translate-hint-expression)
;  (translate-hints1@par)
;  (waterfall)
;  (find-applicable-hint-settings1)
;  (find-applicable-hint-settings1@par)
;  (xtrans-eval@par)
;  (simple-translate-and-eval@par)
;  (simple-translate-and-eval)
;  (translate-hints)
;  (translate-hints+)
;  (thm-fn)
;  (formal-value-triple)
;  (formal-value-triple@par)
;  (eval-clause-processor)
;  (eval-clause-processor@par)
;  (apply-top-hints-clause@par)
;  (apply-top-hints-clause)
;  (waterfall-step1)
;  (waterfall-step1@par)
;  (waterfall-step)
;  (waterfall-step@par)
;  (translate1)
;  (translate1@par)
;  (translate)
;  (translate@par)
;  (translate-clause-processor-hint)
;  (translate-clause-processor-hint@par)
;  (translate1-cmp))

  (cond
   ((symbolp term)
    (cond ((and (function-symbolp term wrld)
                (or (equal (arity term wrld) 3)
                    (equal (arity term wrld) 4)
                    (equal (arity term wrld) 7))
                (all-nils (stobjs-in term wrld))
                (not (eq term 'return-last)) ; avoid taking stobjs-out
                (equal (stobjs-out term wrld) '(nil)))
           (value@par
            (cond
             ((equal (arity term wrld) 3)
              (list 'eval-and-translate-hint-expression
                    name-tree
                    nil
                    (formal-value-triple@par
                     *nil*
                     (fcons-term term '(id clause world)))))
             ((equal (arity term wrld) 4)
              (list 'eval-and-translate-hint-expression
                    name-tree
                    t
                    (formal-value-triple@par
                     *nil*
                     (fcons-term term
                                 '(id clause world
                                      stable-under-simplificationp)))))
             (t
              (list 'eval-and-translate-hint-expression
                    name-tree
                    t
                    (formal-value-triple@par
                     *nil*
                     (fcons-term term
                                 '(id clause world
                                      stable-under-simplificationp
                                      hist pspv ctx))))))))
          (t (er@par soft ctx
               "When you give a hint that is a symbol, it must be a function ~
                symbol of three, four or seven arguments (not involving STATE ~
                or other single-threaded objects) that returns a single ~
                value.  The allowable arguments are ID, CLAUSE, WORLD, ~
                STABLE-UNDER-SIMPLIFICATIONP, HIST, PSPV, and CTX. See :DOC ~
                computed-hints.  ~x0 is not such a symbol."
               term))))
   (t
    (er-let*@par
     ((tterm (translate-simple-or-error-triple@par term ctx wrld state)))
     (let ((vars (all-vars tterm)))
       (cond
        ((subsetp-eq vars
                     (case hint-type
                       (backtrack *hint-expression-backtrack-vars*)
                       (override *hint-expression-override-vars*)
                       (otherwise *hint-expression-basic-vars*)))
         (value@par
          (list 'eval-and-translate-hint-expression
                name-tree
                (if (member-eq 'stable-under-simplificationp vars) t nil)
                tterm)))
        ((and (not hint-type) ; optimization
              (subsetp-eq vars *hint-expression-all-vars*))
         (let ((backtrack-bad-vars (intersection-eq '(CLAUSE-LIST PROCESSOR)
                                                    vars))
               (override-bad-vars (intersection-eq '(KEYWORD-ALIST)
                                                   vars)))
           (mv-let
            (bad-vars types-string)
            (cond (backtrack-bad-vars
                   (cond (override-bad-vars
                          (mv (append backtrack-bad-vars override-bad-vars)
                              ":BACKTRACK hints or override-hints"))
                         (t (mv backtrack-bad-vars ":BACKTRACK hints"))))
                  (t (assert$
                      override-bad-vars ; see subsetp-eq call above
                      (mv override-bad-vars "override-hints"))))
            (er@par soft ctx
              "The hint expression ~x0 mentions ~&1.  But variable~#2~[ ~&2 ~
               is~/s ~&2 are~] legal only for ~@3.  See :DOC computed-hints."
              term vars bad-vars types-string))))
        (t
         (mv-let
          (type-string legal-vars extra-doc-hint)
          (case hint-type
            (backtrack (mv ":BACKTRACK hint"
                           *hint-expression-backtrack-vars*
                           " and see :DOC hints for a discussion of :BACKTRACK ~
                        hints"))
            (override (mv "override-hint"
                          *hint-expression-override-vars*
                          " and see :DOC override-hints"))
            (otherwise (mv "Computed"
                           *hint-expression-basic-vars*
                           "")))
          (er@par soft ctx
            "~@0 expressions may not mention any variable symbols other than ~
             ~&1.  See :DOC computed-hints~@2.  But the hint expression ~x3 ~
             mentions ~&4."
            type-string
            legal-vars
            extra-doc-hint
            term
            vars)))))))))

(defun@par translate-backtrack-hint (name-tree arg ctx wrld state)
  (translate-hint-expression@par name-tree arg 'backtrack ctx wrld state))

(defun@par translate-rw-cache-state-hint (arg ctx wrld state)
  (declare (ignore wrld))
  (cond ((member-eq arg *legal-rw-cache-states*)
         (value@par arg))
        (t (er@par soft ctx
             "Illegal :rw-cache-state argument, ~x0 (should be ~v1)"
             arg
             *legal-rw-cache-states*))))

(mutual-recursion@par

(defun@par translate-or-hint (name-tree str arg ctx wrld state)

; Arg is the value of the :OR key in a user-supplied hint settings,
; e.g., if the user typed: :OR ((:in-theory t1 :use lem1) (:in-theory
; t2 :use lem2)) then arg is ((:in-theory t1 :use lem1) (:in-theory t2
; :use lem2)).  The translated form of this is a list as long as arg
; in which each element of the translated list is a pair (orig
; . trans) where orig is what the user typed and trans is its
; translation as a hint-settings.  (For example, the two theory
; expressions, t1 and t2, will be expanded into full runic
; theories.)  We either cause an error or return (as the value
; component of an error/value/state triple) a list of such pairs.

; Note: str is the original goal-spec string to which this :OR was
; attached.

; Note: Unlike other hints, we do some additional translation of :OR
; hints on the output of this function!  See translate-hint.

  (cond ((atom arg)
         (if (null arg)
             (value@par nil)
           (er@par soft ctx "An :OR hint must be a true-list.")))
        (t (er-let*@par
            ((val (translate-hint@par name-tree
                                      (cons
                                       (make-disjunctive-goal-spec
                                        str
                                        (length arg)
                                        (current-package state))
                                       (car arg))
                                      nil ctx wrld state))
             (tl (translate-or-hint@par name-tree str (cdr arg) ctx wrld state)))

; Val is either a translated computed hint expression, whose car
; is eval-and-translate-hint-expression, or else it is a pair of
; the form (cl-id . hint-settings), where cl-id was derived from
; str.

            (cond
             ((eq (car val) 'eval-and-translate-hint-expression)
              (value@par (cons (cons (car arg) val)
                               tl)))
             (t

; If val is (cl-id . hint-settings), we just let val be hint-settings
; below, as the cl-id is being managed by the :OR itself.

              (let ((val (cdr val)))
                (value@par (cons (cons (car arg) val)
                                 tl)))))))))

(defun@par translate-hint-settings (name-tree str key-val-lst ctx wrld state)

; We assume that key-val-lst is a list of :keyword/value pairs, (:key1
; val1 ... :keyn valn), and that each :keyi is one of the acceptable
; hint keywords.  We convert key-val-lst to alist form, ((:key1 .
; val1') ... (:keyn . valn')), where each vali' is the translated form
; of vali.

; Str is the goal-spec string identifying the clause to which these
; hints are attached.

  (cond
   ((null key-val-lst) (value@par nil))
   ((and (eq (car key-val-lst) :use)
         (eq (cadr key-val-lst) nil))

; We allow empty :use hints, but we do not want to have to think about
; how to process them.

    (translate-hint-settings@par name-tree
                                 str
                                 (cddr key-val-lst) ctx wrld state))
   (t (er-let*@par
       ((val (translate-x-hint-value@par name-tree
                                         str
                                         (car key-val-lst) (cadr key-val-lst)
                                         ctx wrld state))
        (tl (translate-hint-settings@par name-tree
                                         str
                                         (cddr key-val-lst) ctx wrld state)))
       (value@par
        (cons (cons (car key-val-lst) val)
              tl))))))

(defun@par translate-x-hint-value (name-tree str x arg ctx wrld state)

; Str is the goal-spec string identifying the clause to which this
; hint was attached.

  (mv-let
   (flg uterm1 uterm2)
   (custom-keyword-hint x wrld)
   (declare (ignore uterm1))
   (cond
    (flg
     (translate-custom-keyword-hint@par arg uterm2 ctx wrld state))
    (t
     (case x
       (:expand
        (translate-expand-hint@par arg ctx wrld state))
       (:restrict
        (translate-restrict-hint@par arg ctx wrld state))
       (:hands-off
        (translate-hands-off-hint@par arg ctx wrld state))
       (:do-not-induct
        (translate-do-not-induct-hint@par arg ctx wrld state))
       (:do-not
        (translate-do-not-hint@par arg ctx state))
       (:use
        (translate-use-hint@par arg ctx wrld state))
       (:or
        (translate-or-hint@par name-tree str arg ctx wrld state))
       (:cases
        (translate-cases-hint@par arg ctx wrld state))
       (:case-split-limitations
        (translate-case-split-limitations-hint@par arg ctx wrld state))
       (:by
        (translate-by-hint@par name-tree arg ctx wrld state))
       (:induct
        (translate-induct-hint@par arg ctx wrld state))
       (:in-theory
        (translate-in-theory-hint@par arg t ctx wrld state))
       (:bdd
        (translate-bdd-hint@par arg ctx wrld state))
       (:clause-processor
        (translate-clause-processor-hint@par arg ctx wrld state))
       (:nonlinearp
        (translate-nonlinearp-hint@par arg ctx wrld state))
       (:no-op
        (translate-no-op-hint@par arg ctx wrld state))
       (:no-thanks
        (translate-no-thanks-hint@par arg ctx wrld state))
       (:reorder
        (translate-reorder-hint@par arg ctx wrld state))
       (:backtrack
        (translate-backtrack-hint@par name-tree arg ctx wrld state))
       (:backchain-limit-rw
        (translate-backchain-limit-rw-hint@par arg ctx wrld state))
       (:error

; We know this case never happens.  The error is caught and signaled
; early by translate-hint.  But we include it here to remind us that
; :error is a legal keyword.  In fact the semantics given here --
; which causes an immediate error -- is also consistent with the
; intended interpretation of :error.

        (translate-error-hint@par arg ctx wrld state))
       (:rw-cache-state
        (translate-rw-cache-state-hint@par arg ctx wrld state))
       (otherwise
        (mv@par
         (er hard 'translate-x-hint-value
             "The object ~x0 not recognized as a legal hint keyword. See :DOC ~
              hints."
             x)
         nil
         state)))))))

(defun replace-goal-spec-in-name-tree1 (name-tree goal-spec)
  (cond
   ((atom name-tree)
    (cond ((and (stringp name-tree)
                (parse-clause-id name-tree))
           (mv t goal-spec))
          (t (mv nil name-tree))))
   (t (mv-let
       (flg1 name-tree1)
       (replace-goal-spec-in-name-tree1 (car name-tree)
                                        goal-spec)
       (cond
        (flg1 (mv t (cons name-tree1 (cdr name-tree))))
        (t (mv-let (flg2 name-tree2)
                   (replace-goal-spec-in-name-tree1 (cdr name-tree)
                                                    goal-spec)
                   (mv flg2
                       (cons (car name-tree)
                             name-tree2)))))))))

(defun replace-goal-spec-in-name-tree (name-tree goal-spec)

; Name-trees are trees of strings and symbols used to generate
; meaningful names for :by hints.  Typically, a name tree will have at
; most one goal spec in it, e.g., (name . "Subgoal *1/3") or
; ("Computed hint auto-generated for " (name . "Subgoal *1/3")).  We
; search nametree for the first occurrence of a goal spec and replace
; that goal spec by the given one.  This is an entirely heuristic
; operation.

; Why do we do this?  Suppose an :OR hint is attached to a given goal
; spec and we have a name tree corresponding to that goal spec.  To process
; the :OR we will produce a copy of the goal and rename the goal spec
; by adding a "Dj" suffice.  We want to replace the original goal spec
; in the name-tree by this modified goal spec.

  (mv-let (flg new-name-tree)
          (replace-goal-spec-in-name-tree1 name-tree goal-spec)
          (cond
           (flg new-name-tree)
           (t (cons name-tree goal-spec)))))

(defun@par translate-hint (name-tree pair hint-type ctx wrld state)

; Pair is supposed to be a "hint", i.e., a pair of the form (str :key1
; val1 ...  :keyn valn).  We check that it is, that str is a string
; that parses to a clause-id, and that each :keyi is a legal hint
; keyword.  Then we translate pair into a pair of the form (cl-id .
; hint-settings), where cl-id is the parsed clause-id and
; hint-settings is the translated alist form of the key/val lst above.
; We try to eliminate custom keyword hints by eager expansion.  If we
; cannot eliminate all custom hints, we do check that the individual
; :keyi vali pairs are translatable (which, in the case of the custom
; hints among them, means we run their checkers) but we ignore the
; translations.  We then convert the entire hint into a computed hint.

; We return a standard error triple.  If no custom keyword hints
; appear (or if all custom hints could be eagerly eliminated), the
; value is (cl-id . hint-settings).  If an un-eliminable custom
; keyword hint appears, the value is the translated form of a computed
; hint -- with the original version of the hint appearing in it as a
; quoted constant.

; Thus, if the car of the returned value is the word
; 'eval-and-translate-hint-expression the answer is a translated
; computed hint, otherwise it is of the form (cl-id . hint-settings).

  (cond ((not (and (consp pair)
                   (stringp (car pair))
                   (keyword-value-listp (cdr pair))))
         (er@par soft ctx
           "Each hint is supposed to be a list of the form (str :key1 val1 ~
            ... :keyn valn), but a proposed hint, ~x0, is not.  See :DOC ~
            hints."
           pair))
        (t (let ((cl-id (parse-clause-id (car pair))))
             (cond
              ((null cl-id)
               (er@par soft ctx
                 "The object ~x0 is not a goal-spec.  See :DOC hints and :DOC ~
                  goal-spec."
                 (car pair)))
              ((assoc-keyword :error (cdr pair))

; If an :error hint was given, we immediately cause the requested error.
; Note that we thus allow :error hints to occur multiple times and just
; look at the first one.  If we get past this test, there are no
; :error hints.

               (translate-error-hint@par
                (cadr (assoc-keyword :error (cdr pair)))
                ctx wrld state))
              (t
               (mv-let
                (keyi vali uterm1 uterm2)
                (find-first-custom-keyword-hint (cdr pair) wrld)
                (declare (ignore vali uterm1 uterm2))
                (cond
                 (keyi

; There is a custom keyword among the keys.  One of two possibilities
; exists.  The first is that the hint can be expanded statically
; (``eagerly'') now.  The second is that the hint is truly sensitive
; to dynamically determined variables like the variables CLAUSE, HIST,
; STABLE-UNDER-SIMPLIFICATIONP, or PSPV and must consequently be
; treated essentially as a computed hint.  But there is no way to find
; out except by trying to evaluate it!  That is because even if this
; hint involves none of the dynamic variables it might be that the
; value it computes contains other custom keyword hints that do
; involve those variables.

; Note: Recall that the interpreter runs the checker on a val before
; it runs the generator.  So each generator knows that its val is ok.
; But generators do not know that all vals are ok.  That is, a
; generator cannot assume that a common hint has a well-formed val or
; that other custom hints have well-formed vals.

                  (mv-let@par
                   (erp val state)
                   (custom-keyword-hint-interpreter@par
                    (cdr pair)
                    cl-id
                    cl-id
                    NIL wrld NIL NIL NIL ctx state
                    t)

; The four NILs above are bogus values for the dynamic variables.  The
; final t is the eagerp flag which will cause the interpreter to
; signal the WAIT ``error'' if the expansion fails because of some
; unbound dynamic variable.

                   (cond
                    (erp
                     (cond
                      ((eq val 'WAIT)

; In this case, we must treat this as a computed hint so we will
; manufacture an appropriate one.  As a courtesy to the user, we will
; check that all the hints are translatable.  But we ignore the
; translations because there is no way to know whether they are
; involved in the actual hint that will be generated by the processing
; of these custom hints when the subgoal arises.

                       (er-let*@par
                        ((hint-settings
                          (translate-hint-settings@par
                           (replace-goal-spec-in-name-tree
                            name-tree
                            (car pair))
                           (car pair)
                           (cdr pair)
                           ctx wrld state)))

; Note: If you ever consider not ignoring the translated
; hint-settings, recognize how strange it is.  E.g., it may have
; duplicate conflicting bindings of standard keys and pairs
; binding custom keywords to their untranslated values, a data
; structure we never use.

                        (translate-hint-expression@par
                         name-tree

; Below we generate a standard computed hint that uses the
; interpreter.  Note that the interpreter is given the eagerp
; NIL flag.

                         (serial-first-form-parallel-second-form@par
                          `(custom-keyword-hint-interpreter
                            ',(cdr pair)
                            ',cl-id
                            ID CLAUSE WORLD STABLE-UNDER-SIMPLIFICATIONP
                            HIST PSPV CTX STATE 'nil)
                          `(custom-keyword-hint-interpreter@par
                            ',(cdr pair)
                            ',cl-id
                            ID CLAUSE WORLD STABLE-UNDER-SIMPLIFICATIONP
                            HIST PSPV CTX STATE 'nil))
                         hint-type ctx wrld state)))
                      (t (mv@par t nil state))))
                    (t

; In this case, we have eliminated all custom keyword hints
; eagerly and val is a keyword alist we ought to
; use for the hint.  We translate it from scratch.

                     (translate-hint@par name-tree
                                         (cons (car pair) val)
                                         hint-type ctx wrld state)))))
                 (t

; There are no custom keywords in the hint.

                  (let* ((key-val-lst (remove-redundant-no-ops (cdr pair)))

; By stripping out redundant :NO-OPs now we allow such lists as (:OR x
; :NO-OP T), whereas normally :OR would "object" to the presence of
; another hint.

                         (keys (evens key-val-lst))
                         (expanded-hint-keywords
                          (append
                           (strip-cars
                            (table-alist 'custom-keywords-table wrld))
                           *hint-keywords*)))
                    (cond
                     ((null keys)
                      (er@par soft ctx
                        "There is no point in attaching the empty list of ~
                          hints to ~x0.  We suspect that you have made a ~
                          mistake in presenting your hints.  See :DOC hints. ~
                          ~ If you really want a hint that changes nothing, ~
                          use ~x1."
                        (car pair)
                        (cons (car pair) '(:NO-OP T))))
                     ((not (subsetp-eq keys expanded-hint-keywords))
                      (er@par soft ctx
                        "The legal hint keywords are ~&0.  ~&1 ~
                          ~#1~[is~/are~] unrecognized.  See :DOC hints."
                        expanded-hint-keywords
                        (set-difference-eq keys expanded-hint-keywords)))
                     ((member-eq :computed-hint-replacement keys)

; If translate-hint is called correctly, then we expect this case not to arise
; for well-formed hints.  For example, in eval-and-translate-hint-expression we
; remove an appropriate use of :computed-hint-replacement.

                      (er@par soft ctx
                        "The hint keyword ~x0 has been used incorrectly.  ~
                          Its only appropriate use is as a leading hint ~
                          keyword in computed hints.  See :DOC computed-hints."
                        :computed-hint-replacement))
                     ((not (no-duplicatesp-equal keys))
                      (er@par soft ctx
                        "You have duplicate occurrences of the hint keyword ~
                          ~&0 in your hint.  While duplicate occurrences of ~
                          keywords are permitted by CLTL, the semantics ~
                          ignores all but the left-most.  We therefore ~
                          suspect that you have made a mistake in presenting ~
                          your hints."
                        (duplicates keys)))
                     ((and (assoc-keyword :OR (cdr pair))
                           (not (minimally-well-formed-or-hintp
                                 (cadr (assoc-keyword :OR (cdr pair))))))

; Users are inclined to write hints like this:

; ("Goal" :OR ((...) (...)) :in-theory e)

; as abbreviations for

; ("Goal" :OR ((... :in-theory e) (... :in-theory e)))

; We implement this abbreviation below.  But we have to know that the
; value supplied to the :OR is a list of non-empty true-lists of even
; lengths to ensure that we can append the other hints to it and still
; get reasonable translation errors in the presence of ill-formed
; hints.  If not, we cause an error now.  We check the rest of the
; restrictions on :OR after the transformation.

                      (er@par soft ctx
                        "The value supplied to an :OR hint must be a ~
                          non-empty true-list of non-empty true-lists of even ~
                          length, i.e., of the form ((...) ...).  But you ~
                          supplied the value ~x0."
                        (cdr pair)))
                     ((and (member-eq :induct keys)
                           (member-eq :use keys))
                      (er@par soft ctx
                        "We do not support the use of an :INDUCT hint with a ~
                          :USE hint.  When a subgoal with an :INDUCT hint ~
                          arises, we push it for proof by induction.  Upon ~
                          popping it, we interpret the :INDUCT hint to ~
                          determine the induction and we also install any ~
                          other non-:USE hints supplied.  On the other hand, ~
                          when a subgoal with a :USE hint arises, we augment ~
                          the formula with the additional hypotheses supplied ~
                          by the hint.  If both an :INDUCT and a :USE hint ~
                          were attached to the same subgoal we could either ~
                          add the hypotheses before induction, which is ~
                          generally detrimental to a successful induction, or ~
                          add them to each of the formulas produced by the ~
                          induction, which generally adds the hypotheses in ~
                          many more places than they are needed.  We ~
                          therefore do neither and cause this neat, ~
                          informative error.  You are encouraged to attach ~
                          the :INDUCT hint to the goal or subgoal to which ~
                          you want us to apply induction and then attach :USE ~
                          hints to the individual subgoals produced, as ~
                          necessary.  For what it is worth, :INDUCT hints get ~
                          along just fine with hints besides :USE.  For ~
                          example, an :INDUCT hint and an :IN-THEORY hint ~
                          would cause an induction and set the post-induction ~
                          locally enabled theory to be as specified by the ~
                          :IN-THEORY."))
                     ((and (member-eq :reorder keys)
                           (intersectp-eq '(:or :induct) keys))
                      (cond
                       ((member-eq :or keys)
                        (er@par soft ctx
                          "We do not support the use of a :REORDER hint with ~
                            an :OR hint.  The order of disjunctive subgoals ~
                            corresponds to the list of hints given by the :OR ~
                            hint, so you may want to reorder that list ~
                            instead."))
                       (t
                        (er@par soft ctx
                          "We do not support the use of a :REORDER hint with ~
                            an :INDUCT hint.  If you want this capability, ~
                            please send a request to the ACL2 implementors."))))
                     (t
                      (let ((bad-keys (intersection-eq
                                       `(:induct ,@*top-hint-keywords*)
                                       keys)))
                        (cond
                         ((and (< 1 (length bad-keys))
                               (not (and (member-eq :use bad-keys)
                                         (member-eq :cases bad-keys)
                                         (equal 2 (length bad-keys)))))
                          (er@par soft ctx
                            "We do not support the use of a~#0~[n~/~] ~x1 ~
                              hint with a~#2~[n~/~] ~x3 hint, since they ~
                              suggest two different ways of replacing the ~
                              current goal by new goals.  ~@4Which is it to ~
                              be?  To summarize:  A~#0~[n~/~] ~x1 hint ~
                              together with a~#2~[n~/~] ~x3 hint is not ~
                              allowed because the intention of such a ~
                              combination does not seem sufficiently clear."
                            (if (member-eq (car bad-keys) '(:or :induct))
                                0 1)
                            (car bad-keys)
                            (if (member-eq (cadr bad-keys) '(:or :induct))
                                0 1)
                            (cadr bad-keys)
                            (cond
                             ((and (eq (car bad-keys) :by)
                                   (eq (cadr bad-keys) :induct))
                              "The :BY hint suggests that the goal follows ~
                                 from an existing theorem, or is to be ~
                                 pushed.  However, the :INDUCT hint provides ~
                                 for replacement of the current goal by ~
                                 appropriate new goals before proceeding.  ")
                             (t ""))))
                         (t
                          (er-let*@par
                           ((hint-settings
                             (translate-hint-settings@par
                              (replace-goal-spec-in-name-tree
                               name-tree
                               (car pair))
                              (car pair)
                              (cond
                               ((assoc-keyword :or (cdr pair))
                                (distribute-other-hints-into-or
                                 (cdr pair)))
                               (t (cdr pair)))
                              ctx wrld state)))
                           (cond

; Hint-settings is of the form ((:key1 . val1) ...(:keyn . valn)).  If :key1 is
; :OR, we know n=1; translated :ORs always occur as singletons.  But in ((:OR
; . val1)), val1 is always a list of pairs.  If there is only one pair in that
; list, then we're dealing with an :OR with only one disjunct: hint-settings is
; of the form ((:OR (orig . hint-settings2))), where orig is what the user
; typed (see translate-or-hint).

                            ((and (consp hint-settings)
                                  (eq (caar hint-settings) :OR)
                                  (consp (cdr (car hint-settings)))
                                  (null (cddr (car hint-settings))))

; This is a singleton :OR, as above.  We just drop the :OR and the "orig" shown
; above to obtain the "hint-settings2" shown above.

                             (assert$
                              (null (cdr hint-settings))
                              (value@par
                               (let* ((pair ; (orig . hint-settings2)
                                       (cadr (car hint-settings)))
                                      (hint-settings2 (cdr pair)))
                                 (cons cl-id hint-settings2)))))
                            (t (value@par
                                (cons cl-id hint-settings))))))))))))))))))))
)

(defun@par translate-hint-expressions (name-tree terms hint-type ctx wrld state)

; This function translates a true-list of hint expressions.  It is used when a
; hint generates a new list of hints.

  (cond
   ((endp terms)
    (cond ((equal terms nil) (value@par nil))
          (t (er@par soft ctx
               "The value of the :COMPUTED-HINT-REPLACEMENT key must be NIL, ~
                T, or a true list of terms.  Your list ends in ~x0."
               terms))))
   (t (er-let*@par
       ((thint (translate-hint-expression@par name-tree (car terms)
                                              hint-type ctx wrld
                                              state))
        (thints (translate-hint-expressions@par name-tree (cdr terms)
                                                hint-type ctx wrld state)))
       (value@par (cons thint thints))))))

(defun@par check-translated-override-hint (hint uhint ctx state)
  (cond ((not (and (consp hint)
                   (eq (car hint)
                       'eval-and-translate-hint-expression)))
         (er@par soft ctx
             "The proposed override-hint, ~x0, was not a computed hint.  See ~
              :DOC override-hints."
             uhint))
        (t ; term is (caddr (cdr hint)); we allow any term here
         (value@par nil))))

(defun@par translate-hints1 (name-tree lst hint-type override-hints ctx wrld
                                       state)

; A note on the taxonomy of translated hints.  A "hint setting" is a pair of
; the form (key . val), such as (:DO-NOT-INDUCT . T) or (:USE . (lmi-lst
; (h1...hn) ...)).  (For example, see translate-use-hint for more about the
; shape of the latter.)  Lists of such pairs are called "hint settings."  A
; pair consisting of a clause-id and some hint-settings is called a
; "(translated) hint".  A list of such pairs is called "(translated) hints."

; Thus, following the :HINTS keyword to defthm, the user types "hints" (in
; untranslated form).  This function takes a lst, which is supposed be some
; hints, and translates it or else causes an error.

; Essay on the Handling of Override-hints

; When we translate an explicit (not computed) hint in the presence of at least
; one non-trivial override hint in the world, we append to the front of the
; hint-settings the list (:keyword-alist . x) (:name-tree . n), where x is the
; untranslated keyword-alist corresponding to hint-settings and n is the
; name-tree used for translation: so the hint is (goal-name (:keyword-alist
; . x) (:name-tree . n) (kwd1 . v1) ... (kwdk . vk)).  Later, when we select
; the hint with find-applicable-hint-settings, we will see (:keyword-alist . x)
; and apply the override-hints to x, and if the result of apply-override-hints
; is also x, then we will return ((kwd1 . v1) ... (kwdk . vk)); otherwise we
; will translate that result.  Note that in the special case that the original
; hint had at least one custom keyword hint but the ultimate resulting
; expansion was an explicit hint, the same technique will apply.  Also note
; that the keyword :keyword-alist is illegal for users, and would be flagged as
; such by translate-hint in translate-hints1; so we have full control over the
; use of :keyword-alist (and similarly for :name-tree).

; If however the resulting translated hint is a computed hint, i.e. a list
; whose car is 'eval-and-translate-hint-expression, then no modification is
; necessary; function find-applicable-hint-settings takes care to apply
; override-hints, by calling function eval-and-translate-hint-expression with
; the override-hints supplied.

; And how about backtrack hints?  Backtrack hints are computed hints, and
; receive the same treatment as described above, i.e. for computed hints
; selected by find-applicable-hint-settings -- namely, by passing the world's
; override-hints to eval-and-translate-hint-expression.

  (cond ((atom lst)
         (cond ((null lst) (value@par nil))
               (t (er@par soft ctx
                    "The :HINTS keyword is supposed to have a true-list as ~
                     its value, but ~x0 is not one.  See :DOC hints."
                    lst))))
        ((and (consp (car lst))
              (stringp (caar lst))
              (null (cdar lst)))
         (translate-hints1@par name-tree (cdr lst) hint-type override-hints ctx
                               wrld state))
        (t (er-let*@par
            ((hint (cond ((and (consp (car lst))
                               (stringp (caar lst)))
                          (translate-hint@par name-tree (car lst) hint-type ctx
                                              wrld state))
                         (t (translate-hint-expression@par
                             name-tree (car lst) hint-type ctx wrld state))))
             (rst (translate-hints1@par name-tree (cdr lst) hint-type
                                        override-hints ctx wrld state)))
            (er-progn@par
             (cond ((eq hint-type 'override)
                    (check-translated-override-hint@par hint (car lst) ctx state))
                   (t (value@par nil)))
             (value@par (cons (cond ((atom hint) hint) ; nil
                                    ((and (consp (car lst))
                                          (stringp (caar lst)))
                                     (cond (override-hints
                                            (list* (car hint) ; (caar lst)
                                                   (cons :KEYWORD-ALIST
                                                         (cdar lst))
                                                   (cons :NAME-TREE
                                                         name-tree)
                                                   (cdr hint)))
                                           (t hint)))
                                    ((eq (car hint)
                                         'eval-and-translate-hint-expression)
                                     hint)
                                    (t (er hard ctx
                                           "Internal error: Unexpected ~
                                            translation ~x0 for hint ~x1.  ~
                                            Please contact the ACL2 ~
                                            implementors."
                                           hint (car lst))))
                              rst)))))))

(defun@par warn-on-duplicate-hint-goal-specs (lst seen ctx state)
  (cond ((endp lst)
         (state-mac@par))
        ((and (consp (car lst))
              (stringp (caar lst)))
         (if (member-equal (caar lst) seen)
             (pprogn@par (warning$@par ctx ("Hints")
                           "The goal-spec ~x0 is explicitly associated with ~
                            more than one hint.  All but the first of these ~
                            hints may be ignored.  If you intended to give ~
                            all of these hints, combine them into a single ~
                            hint of the form (~x0 :kwd1 val1 :kwd2 val2 ...). ~
                            ~ See :DOC hints-and-the-waterfall."
                           (caar lst))
                         (warn-on-duplicate-hint-goal-specs@par (cdr lst) seen
                                                                ctx state))
           (warn-on-duplicate-hint-goal-specs@par (cdr lst)
                                                  (cons (caar lst) seen)
                                                  ctx state)))
        (t (warn-on-duplicate-hint-goal-specs@par (cdr lst) seen ctx state))))

(defun@par translate-hints2 (name-tree lst hint-type override-hints ctx wrld state)
  (cond ((warning-disabled-p "Hints")
         (translate-hints1@par name-tree lst hint-type override-hints ctx wrld
                               state))
        (t
         (er-let*@par ((hints (translate-hints1@par name-tree lst hint-type
                                                    override-hints ctx wrld
                                                    state)))
                      (pprogn@par (warn-on-duplicate-hint-goal-specs@par
                                   lst nil ctx state)
                                  (value@par hints))))))

(defun override-hints (wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (alistp (table-alist 'default-hints-table
                                                   wrld)))))
  (cdr (assoc-eq :override (table-alist 'default-hints-table wrld))))

(defun@par translate-hints (name-tree lst ctx wrld state)
  (translate-hints2@par name-tree lst nil (override-hints wrld) ctx wrld
                        state))

(defun@par translate-hints+1 (name-tree lst default-hints ctx wrld state)
  (cond
   ((not (true-listp lst))
    (er@par soft ctx
      "The :HINTS keyword is supposed to have a true-list as its value, but ~
       ~x0 is not one.  See :DOC hints."
      lst))
   (t
    (translate-hints@par name-tree (append lst default-hints) ctx wrld
                         state))))

(defun translate-hints+ (name-tree lst default-hints ctx wrld state)
  #-acl2-par
  (translate-hints+1 name-tree lst default-hints ctx wrld state)
  #+acl2-par
  (if (f-get-global 'waterfall-parallelism state)
      (cmp-to-error-triple
       (translate-hints+1@par name-tree lst default-hints ctx wrld state))
      (translate-hints+1 name-tree lst default-hints ctx wrld state)))

(defun translate-override-hints (name-tree lst ctx wrld state)
  #-acl2-par
  (translate-hints2 name-tree lst 'override
                    nil ; no override-hints are applied
                    ctx wrld state)
  #+acl2-par
  (if (f-get-global 'waterfall-parallelism state)
      (cmp-to-error-triple
       (translate-hints2@par name-tree lst 'override
                             nil ; no override-hints are applied
                             ctx wrld state))
    (translate-hints2 name-tree lst 'override
                      nil ; no override-hints are applied
                      ctx wrld state)))

(defun@par apply-override-hint1
  (override-hint cl-id clause hist pspv ctx wrld
                 stable-under-simplificationp clause-list processor
                 keyword-alist state)

; Apply the given override-hints to the given keyword-alist (for a hint) to
; obtain a resulting keyword alist.

  (let* ((tuple override-hint)
         (flg (cadr (cdr tuple)))
         (term (caddr (cdr tuple))))
    (er-let*@par
     ((new-keyword-alist
       (xtrans-eval@par
        term
        (list* (cons 'id cl-id)
               (cons 'clause clause)
               (cons 'hist hist)
               (cons 'pspv pspv)
               (cons 'ctx ctx)
               (cons 'world wrld)
               (cons 'clause-list clause-list)
               (cons 'processor processor)
               (cons 'keyword-alist keyword-alist)
               (if flg
                   (cons (cons 'stable-under-simplificationp
                               stable-under-simplificationp)
                         nil)
                 nil))

; #+ACL2-PAR note: we wish that we could have determined that the translation
; mentioned at the beginning of this function's definition was performed by
; translate-simple-or-error-triple@par (via a call to translate-hints+@par,
; which occurs before entering the waterfall).  However, in the case of
; override hints, the translation really occurs when the override hint is added
; (perhaps via a call to "set-override-hints").  As such, even though we would
; like to check the output signature of the override hint, there is no way to
; do so without retranslating.  We therefore disallow override hints whenever
; waterfall parallelism is enabled and waterfall-parallelism-hacks have not
; been enabled.

        nil ; trans-flg = nil because term is already translated
        t   ; ev-flg = t because we have bound all the vars
        ctx state t)))
     (cond
      ((not (keyword-value-listp new-keyword-alist))
       (er@par soft ctx
         "An override-hint, ~x0, has produced an illegal value from ~
          keyword-alist ~x1.  That value, ~x2, is illegal because it is not a ~
          keyword-value-listp, i.e., an alternating list of keywords and ~
          values."
         (untranslate term nil wrld)
         keyword-alist
         new-keyword-alist))
      (t

; If an override-hint generates a hint with a custom keyword that is sensitive
; to stable-under-simplificationp, then that keyword will not have been
; expanded away at hint translation time.  We deal with it now.  The following
; example from Ian Johnson failed before invoking
; custom-keyword-hint-interpreter here.

; (set-state-ok t)
; (defun blah (val stable-under-simplificationp state)
;   (declare (ignore val stable-under-simplificationp))
;   (value '(:in-theory (enable car-cons))))
; (add-custom-keyword-hint :test
;                          (blah val stable-under-simplificationp state))
; (defun ovrride (keyword-alist state)
;   (let ((ret (append keyword-alist (list :test t))))
;     (prog2$
;      (cw "HINTS ~x0 ~%" ret)
;      (if keyword-alist
;          (value ret)
;        (value nil)))))
; (add-override-hints (list '(ovrride keyword-alist state)))
; (thm (equal (* 4 (car (cons x x))) (* x 4))
;      :hints (("Goal" :in-theory (disable car-cons))))

       (mv-let@par
        (erp new-keyword-alist state)
        (custom-keyword-hint-interpreter@par
         new-keyword-alist
         cl-id
         cl-id
         clause wrld stable-under-simplificationp
         hist pspv ctx state
         nil)
        (cond
         (erp
          (er@par soft ctx
            "An override-hint applied to ~@0 has generated an illegal custom ~
             keyword hint, as reported above."
            (tilde-@-clause-id-phrase cl-id)))
         ((eq (car new-keyword-alist)
              :computed-hint-replacement)
          (er@par soft ctx
            "An override-hint, ~x0, has produced an illegal value from ~
             keyword-alist ~x1.  That value, ~x2, is illegal because it ~
             begins with the keyword :COMPUTED-HINT-REPLACEMENT; see :DOC ~
             override-hints."
            (untranslate term nil wrld)
            keyword-alist
            new-keyword-alist))
         ((assoc-keyword :error new-keyword-alist)
          (translate-error-hint@par
           (cadr (assoc-keyword :error new-keyword-alist))
           (msg "an override hint applied to ~@0"
                (tilde-@-clause-id-phrase cl-id))
           wrld state))
         (t
          (value@par new-keyword-alist)))))))))

(defun@par apply-override-hint
  (override-hint cl-id clause hist pspv ctx wrld
                 stable-under-simplificationp clause-list processor
                 keyword-alist state)
  #-acl2-par
  (apply-override-hint1 override-hint cl-id clause hist pspv ctx wrld
                        stable-under-simplificationp clause-list processor
                        keyword-alist state)
  #+acl2-par
  (cond ((and (f-get-global 'waterfall-parallelism state)
              (not (cdr (assoc-eq 'hacks-enabled
                                  (table-alist 'waterfall-parallelism-table
                                               (w state))))))
         (er@par soft ctx
           "Override-hints are not officially supported in ACL2(p).  If you ~
            wish to use override hints anyway, you can call ~x0. See :DOC ~
            set-waterfall-parallelism-hacks-enabled for more information."
           '(set-waterfall-parallelism-hacks-enabled t)))
        (t (apply-override-hint1@par override-hint cl-id clause hist pspv ctx
                                     wrld stable-under-simplificationp
                                     clause-list processor keyword-alist
                                     state))))

(defun@par apply-override-hints
  (override-hints cl-id clause hist pspv ctx wrld
                  stable-under-simplificationp clause-list processor
                  keyword-alist state)

; Apply the given override-hints to the given keyword-alist (for a hint) to
; obtain a resulting keyword alist.

  (cond
   ((endp override-hints)
    (value@par keyword-alist))
   (t
    (er-let*@par
     ((new-keyword-alist
       (apply-override-hint@par
        (car override-hints) cl-id clause hist pspv ctx wrld
        stable-under-simplificationp clause-list processor
        keyword-alist state)))
     (apply-override-hints@par
      (cdr override-hints) cl-id clause hist pspv ctx wrld
      stable-under-simplificationp clause-list processor
      new-keyword-alist state)))))

(defun@par eval-and-translate-hint-expression
  (tuple cl-id clause wrld stable-under-simplificationp hist pspv clause-list
         processor keyword-alist hint-type override-hints ctx state)

; Tuple is of the form (name-tree flg term), where term is a translated
; single-threaded error-triple producing term that mentions, at most, the
; variables ID, CLAUSE, CLAUSE-LIST, PROCESSOR, KEYWORD-ALIST, WORLD,
; STABLE-UNDER-SIMPLIFICATIONP, HIST, PSPV, CTX, and STATE; and flg is a flag
; indicating whether the variable STABLE-UNDER-SIMPLIFICATIONP occurs freely in
; term.  We eval term under the corresponding alist, obtaining a value val, and
; if val is non-erroneous and non-nil then we treat it as though it were a
; keyword-alist from an untranslated hint, i.e., (:key1 val1 ...), and
; translate it, using name-tree as the gensym name-tree for :bye hints.  We
; return the translated hint-settings or nil.

; The above description is inaccurate in three respects.  First, after the
; evaluation of term we restore proof related components of state.  Our
; intention is that the user have state so the computed hint can, say,
; translate terms and print error messages.  But we cannot prevent the user
; from abusing state and doing things like reading from files (which we can't
; undo) or changing the logical world with defun or defthm (which we can undo).
; So think of us as ignoring the state returned by the evaluation and reverting
; to the original one.

; Second, let's first remind ourselves that a computed hint gets to specify not
; just what the hint-settings is for this application but also gets to affect
; the hints that will be available later.  A computed hint can direct the
; system to (a) remove itself from the hints after the application, (b) leave
; itself in after the application, or (c) replace itself with a list of other
; hints.  This direction is provided by including the keyword
; :COMPUTED-HINT-REPLACEMENT and an associated value in the result, val, of the
; evaluation.

; The :COMPUTED-HINT-REPLACEMENT keyword and its value, chr, if provided, MUST
; BE THE FIRST two elements of val.

; The first paragraph is correct when val does not start with
; :COMPUTED-HINT-REPLACEMENT.  Otherwise, val is of the form
; (:COMPUTED-HINT-REPLACEMENT chr . keyword-alist) and this is what we do.  If
; keyword-alist is nil then we return (value nil).  Otherwise, we treat
; keyword-alist as an untranslated hint-settings and translate it.  We inspect
; chr to see whether it is (a) nil, (b) t, or (c) something else.  The first
; two mean the hint is to be (a) deleted or (b) preserved.  The last is
; understood as a list of terms to be be spliced into the hints in place of
; this one.  But these terms must be translated and so we do that.  Then we
; return (:COMPUTED-HINT-REPLACEMENT chr' . hint-settings), where chr' is the
; possibly translated chr and hint-settings' is the translated keyword-alist.
; It is left to our caller to interpret chr' and modify the hints
; appropriately.

; Finally the third inaccuracy of our initial description above is that it
; fails to account for override-hints.  We apply the given override-hints if
; the computed hint returns a keyword-value-alistp that is non-nil even after
; stripping off a (:COMPUTED-HINT-REPLACEMENT val) prefix.

  (let* ((name-tree (car tuple))
         (flg (cadr tuple))
         (term (caddr tuple))
         (custom-keyword-alist

; Keep this is sync with custom-keyword-hint-in-computed-hint-form.  This
; variable is set to nil if this is an undistinguished computed hint and is set
; to non-nil if it is a custom keyword hint in computed hint form.  The non-nil
; value is a hint keyword alist containing at least one custom keyword.

          (if (and (nvariablep term)
                   (not (fquotep term))
                   (serial-first-form-parallel-second-form@par
                    (eq (ffn-symb term) 'custom-keyword-hint-interpreter)
                    (or (eq (ffn-symb term)
                            'custom-keyword-hint-interpreter)
                        (eq (ffn-symb term)
                            'custom-keyword-hint-interpreter@par)))
                   (quotep (fargn term 1))
                   (quotep (fargn term 2)))
              (cadr (fargn term 1))
            nil)))

; The use of flg below might save a few conses.  We do this only because we
; can.  The real reason we have have the flg component in the computed hint
; tuple has to do with optimizing find-applicable-hint-settings.

    (er-let*@par
     ((val0 (xtrans-eval@par
             term
             (list* (cons 'id cl-id)
                    (cons 'clause clause)
                    (cons 'clause-list clause-list)
                    (cons 'processor processor)
                    (cons 'keyword-alist keyword-alist)
                    (cons 'world wrld)
                    (cons 'hist hist)
                    (cons 'pspv pspv)
                    (cons 'ctx ctx)
                    (if flg
                        (cons (cons 'stable-under-simplificationp
                                    stable-under-simplificationp)
                              nil)
                      nil))
             nil ; trans-flg = nil because term is already translated
             t   ; ev-flg = t because we have bound all the vars
             ctx state t)))
     (cond
      ((null val0)
       (value@par nil))
      (t
       (er-let*@par
        ((str (value@par (string-for-tilde-@-clause-id-phrase cl-id)))
         (chr-p

; This is a reasonable place to catch a non-keyword-alist result.  Before we
; had override-hints, we waited for the translate-hint call below.  But
; override-hints expect keyword-alists, so we do our checking earlier now.

          (cond ((keyword-value-listp val0)
                 (value@par (eq (car val0) :computed-hint-replacement)))
                (t
                 (er@par soft ctx
                   "A ~#0~[custom keyword~/computed~] hint for ~x1 has ~
                    produced a result that is not an alternating list of ~
                    keywords and values, (str :key1 val1 ... :keyn valn).  ~
                    That result, ~x2, is thus illegal."
                   (if custom-keyword-alist 0 1)
                   str
                   val0))))
         (chr
          (cond
           ((null chr-p) (value@par :irrelevant)) ; chr is not used
           (custom-keyword-alist
            (er@par soft
              (msg "a custom keyword hint for ~x0"
                   str)
              "The hint ~x0 produced a :COMPUTED-HINT-REPLACEMENT value as ~
               part of its result.  It is not permitted for custom keyword ~
               hints to produce such a value (only computed hints are allowed ~
               to do that).  The result produced was ~x1."
              (cons str
                    (cadr (fargn term 1)))
              val0))
           ((not (consp (cdr val0)))
            (er@par soft
              (msg
               "a computed hint for ~x0:  The computed hint ~% ~q1 produced ~
                the non-nil result~%~y2.  But this is an illegal value"
               str
               (untranslate term nil wrld)
               val0)
              "The :COMPUTED-HINT-REPLACEMENT keyword must be followed by a ~
               list whose first element is NIL, T, or a list of terms.  The ~
               remaining elements are to be keyword/value pairs."))
           ((or (eq (cadr val0) nil) (eq (cadr val0) t))
            (value@par (cadr val0)))
           (t
            (translate-hint-expressions@par
             (cons "Computed hint auto-generated for "
                   name-tree)
             (cadr val0)
             hint-type 'auto-generated-hint wrld state))))
         (val1 (value@par (if chr-p (cddr val0) val0))))
        (cond
         ((null val1)
          (value@par nil))
         (t
          (er-let*@par
           ((val (cond ((and (keyword-value-listp val1)
                             (assoc-keyword :ERROR val1))

; If the hint produced an :ERROR as one of the keys of its result, then rather
; than translate the whole hint we pick out the :ERROR msg and print it
; directly.

                        (translate-error-hint@par
                         (cadr (assoc-keyword :ERROR val1))
                         (msg "a ~#0~[custom keyword~/computed~] hint for ~x1"
                              (if custom-keyword-alist 0 1)
                              str)
                         wrld
                         state))
                       (t (apply-override-hints@par
                           override-hints cl-id clause hist pspv ctx wrld
                           stable-under-simplificationp clause-list processor
                           val1 state)))))
           (cond
            ((null val)
             (value@par nil))
            (t
             (er-let*@par
              ((temp

; Explanation of the call of translate-hint below: The val computed is supposed
; to be of the form (:key1 val1 ...) and we need to check that it really is and
; translate it into the internal form of a hint-settings.  We cons str onto the
; front of what we translate to create (str :key1 val1 ...) and then run it
; through the standard hint translator.  That string is used in the name
; generated by :by.  If no error occurs, we get back either
; (eval-and-translate-hint-expression ...)  or (cl-id . hint-settings).  The
; former is the translated form of a computed hint.  The latter contains the
; translated hint settings we seek.  We ignore the cl-id, which comes from the
; str we consed onto val.

; The msg below is the context of any error message generated by this
; translate-hint.  It will be printed followed by a colon.

                (translate-hint@par
                 name-tree
                 (cons str val)
                 hint-type
                 (msg
                  "a ~#0~[custom keyword~/computed~] hint for ~x1:  The ~
                   ~#0~[custom keyword~/computed~] hint ~%~#0~[~x2 ~
                   ~/~q2~]produced the non-nil result~%~y3.~@4Regarding this ~
                   value"
                  (if custom-keyword-alist 0 1)
                  str
                  (if custom-keyword-alist
                      custom-keyword-alist
                    (untranslate term nil wrld))
                  val0
                  (cond ((equal val val1) "")
                        (t (msg "In turn, override-hints transformed these ~
                                 hint-settings~#0~[ (without the leading ~
                                 :COMPUTED-HINT-REPLACEMENT value)~/~] into ~
                                 ~x1.  "
                                (if (equal val0 val1) 1 0)
                                val))))
                 wrld state))
               (temp1
                (cond
                 ((eq (car temp) 'eval-and-translate-hint-expression)
                  (eval-and-translate-hint-expression@par
                   (cdr temp)
                   cl-id clause wrld stable-under-simplificationp hist pspv
                   clause-list processor keyword-alist hint-type
                   nil ; we have already dealt with the override-hints
                   ctx state))
                 (t (value@par (cdr temp))))))
              (cond
               ((and chr-p
                     (not (eq (car temp1) :computed-hint-replacement)))

; What if chr-p and (eq (car temp1) :computed-hint-replacement)?  We take the
; value of the inner :computed-hint-replacement, but we could equally well take
; the outer value or cause an error instead.  We have simply chosen the
; simplest alternative to code.

                (value@par (list* :computed-hint-replacement
                                  chr
                                  temp1)))
               (t (value@par temp1)))))))))))))))

; Essay on Trust Tags (Ttags)

; Here we place the bulk of the code for handling trust tags (ttags).

; A trust tag (ttag) is a keyword that represents where to place responsibility
; for potentially unsafe operations.  For example, suppose we define a
; function, foo, that calls sys-call.  Any call of sys-call is potentially
; unsafe, in the sense that it can do things not normally expected during book
; certification, such as overwriting a file or a core image.  But foo's call of
; sys-call may be one that can be explained somehow as safe.  At any rate,
; translate11 allows this call of sys-call if there is an active trust tag
; (ttag), in the sense that the key :ttag is bound to a non-nil value in the
; acl2-defaults-table.  See :doc defttag for more on ttags, in particular, the
; ``TTAG NOTE'' mechanism for determining which files need to be inspected in
; order to validate the proper use of ttags.

; There is a subtlety to the handling of trust tags by include-book in the case
; of uncertified books.  Consider the following example.  We have two books,
; sub.lisp and top.lisp, but we will be considering two versions of sub.lisp,
; as indicated.

; sub.lisp
; (in-package "ACL2")
; ; (defttag :sub-ttag1) ; will be uncommented later
; (defun f (x) x)

; top.lisp
; (in-package "ACL2")
; (encapsulate
;  () ;; start lemmas for sub
;
;  (include-book "sub")
;  )

; Now take the following steps:

; In a fresh ACL2 session:
; (certify-book "sub")
; (u)
; (certify-book "top")

; Now edit sub.lisp by uncommenting the defttag form.  Then, in a fresh ACL2
; session:
; (certify-book "sub" 0 t :ttags :all)
; (u)
; (include-book "top")

; The (include-book "top") form will fail when the attempt is made to include
; the book "sub".  To see why, first consider what happens when a superior book
; "top" includes a subsidiary certified book "sub".  When include-book-fn1 is
; called in support of including "sub", the second call of
; chk-acceptable-ttags1 therein uses the certificate's ttags, stored in
; variable cert-ttags, to refine the state global 'ttags-allowed.  After that
; check and refinement, which prints ttag notes based on cert-ttags,
; ttags-allowed is bound to cert-ttags for the inclusion of "sub", with further
; ttag notes omitted during that inclusion.

; Returning to our example, the recertification of "sub" results in the
; addition of a ttag for "sub" that has not yet been noticed for "top".  So
; when we include "top", state global ttags-allowed is bound to nil, since that
; is the cert-ttags for "top".  When sub is encountered, its additional ttag is
; not allowed (because ttags-allowed is nil), and we get an error.

; In a way, this error is unfortunate; after all, top is uncertified, and we
; wish to allow inclusion of uncertified books (with a suitable warning).  But
; it seems non-trivial to re-work the scheme described above.  In particular,
; it seems that we would have to avoid binding ttags-allowed to nil when
; including "top", before we realize that "top" is uncertified.  (The check on
; sub-book checksums occurs after events are processed.)  We could eliminate
; this "barrier" under which we report no further ttag notes, but that could
; generate a lot of ttag notes -- even if we defer, we may be tempted to print
; a note for each defttag encountered in a different sub-book.

; That said, if the need is great enough for us to avoid the error described
; above, we'll figure out something.

; Finally, we note that trust tags are always in the "KEYWORD" package.  This
; simplifies the implementation of provisional certification.  Previously
; (after Version_4.3 but before the next release), Sol Swords sent an example
; in which the Complete operation caused an error, the reason being that an
; unknown package was being used in the post-alist in the certificate file.

(defmacro ttags-seen ()

; The following is a potentially useful utility, which we choose to include in
; the ACL2 sources rather than in community book books/hacking/hacker.lisp.
; Thanks to Peter Dillinger for his contribution.

  '(mv-let (col state)
           (fmt1 "~*0Warning: This output is minimally trustworthy (see :DOC ~
                  ~x1).~%"
                 `((#\0 "<no ttags seen>~%" "~q*" "~q*" "~q*"
                        ,(global-val 'ttags-seen (w state)))
                   (#\1 . ttags-seen))
                 0 (standard-co state) state ())
           (declare (ignore col))
           (value ':invisible)))

(defun active-book-name (wrld state)

; This returns the full book name (an absolute pathname ending in .lisp) of the
; book currently being included, if any.  Otherwise, this returns the full book
; name of the book currently being certified, if any.

  (or (car (global-val 'include-book-path wrld))
      (let ((x (f-get-global 'certify-book-info state)))
        (cond (x (let ((y (access certify-book-info x :full-book-name)))
                   (assert$ (stringp y) y)))))))

(defrec deferred-ttag-note
  (val active-book-name . include-bookp)
  t)

(defun fms-to-standard-co (str alist state evisc-tuple)

; Warning: This function is used for printing ttag notes, so do not change
; *standard-co*, not even to (standard-co state)!

  (declare (xargs :guard ; incomplete guard
                  (and (stringp str)
                       (character-alistp alist)
                       (standard-evisc-tuplep evisc-tuple))))
  (fms str alist *standard-co* state evisc-tuple))

(defun print-ttag-note (val active-book-name include-bookp deferred-p state)

; Active-book-name is nil or else satisfies chk-book-name.  If non-nil, we
; print it as "book x" where x omits the .lisp extension, since the defttag
; event might not be in the .lisp file.  For example, it could be in the
; expansion-alist in the book's certificate or, if the book is not certified,
; it could be in the .port file.

; If include-bookp is a cons, then its cdr satisfies chk-book-name.

  (flet ((book-name-root (book-name)
                         (subseq book-name 0 (- (length book-name) 5))))
    (pprogn
     (let* ((book-name (cond (active-book-name
                              (book-name-root active-book-name))
                             (t "")))
            (included (if include-bookp
                          " (for included book)"
                        ""))
            (str (if active-book-name
                     "TTAG NOTE~s0: Adding ttag ~x1 from book ~s2."
                   "TTAG NOTE~s0: Adding ttag ~x1 from the top level loop."))
            (bound (+ (length included)
                      (length str)
                      (length (symbol-package-name val))
                      2 ; for "::"
                      (length (symbol-name val))
                      (length book-name))))
       (mv-let (erp val state)
               (state-global-let*
                ((fmt-hard-right-margin bound set-fmt-hard-right-margin)
                 (fmt-soft-right-margin bound set-fmt-soft-right-margin))
                (pprogn (fms-to-standard-co str
                                            (list (cons #\0 included)
                                                  (cons #\1 val)
                                                  (cons #\2 book-name))
                                            state nil)
                        (cond (deferred-p state)
                              (t (newline *standard-co* state)))
                        (value nil)))
               (declare (ignore erp val))
               state))
     (cond ((and (consp include-bookp) ; (cons ctx full-book-name)
                 (not deferred-p))
            (warning$ (car include-bookp) ; ctx
                      "Ttags"
                      "The ttag note just printed to the terminal indicates a ~
                       modification to ACL2.  To avoid this warning, supply ~
                       an explicit :TTAGS argument when including the book ~
                       ~x0."
                      (book-name-root
                       (cdr include-bookp)) ; full-book-name
                      ))
           (t state)))))

(defun show-ttag-notes1 (notes state)
  (cond ((endp notes)
         (newline *standard-co* state))
        (t (pprogn (let ((note (car notes)))
                     (print-ttag-note
                      (access deferred-ttag-note note :val)
                      (access deferred-ttag-note note :active-book-name)
                      (access deferred-ttag-note note :include-bookp)
                      t
                      state))
                   (show-ttag-notes1 (cdr notes) state)))))

(defun show-ttag-notes-fn (state)
  (let* ((notes0 (f-get-global 'deferred-ttag-notes-saved state))
         (notes (remove-duplicates-equal notes0)))
    (cond (notes
           (pprogn (cond ((equal notes notes0)
                          state)
                         (t (fms-to-standard-co
                             "Note: Duplicates have been removed from the ~
                              list of deferred ttag notes before printing ~
                              them below.~|"
                             nil state nil)))
                   (show-ttag-notes1 (reverse notes) state)
                   (f-put-global 'deferred-ttag-notes-saved nil state)))
          (t (fms-to-standard-co
              "All ttag notes have already been printed.~|"
              nil state nil)))))

(defmacro show-ttag-notes ()
  '(pprogn (show-ttag-notes-fn state)
           (value :invisible)))

(defun set-deferred-ttag-notes (val state)
  (let ((ctx 'set-deferred-ttag-notes)
        (immediate-p (not val)))
    (cond
     ((member-eq val '(t nil))
      (pprogn
       (cond ((eq immediate-p
                  (eq (f-get-global 'deferred-ttag-notes state)
                      :not-deferred))
              (observation ctx
                           "No change; ttag notes are already ~@0being ~
                            deferred."
                           (if immediate-p
                               "not "
                             "")))
             ((and immediate-p
                   (consp (f-get-global 'deferred-ttag-notes state)))
              (pprogn (fms-to-standard-co
                       "Note: Enabling immediate printing mode for ttag ~
                        notes.  Below are the ttag notes that have been ~
                        deferred without being reported."
                       nil state nil)
                      (f-put-global 'deferred-ttag-notes-saved
                                    (f-get-global 'deferred-ttag-notes state)
                                    state)
                      (f-put-global 'deferred-ttag-notes
                                    nil
                                    state)
                      (show-ttag-notes-fn state)))
             (immediate-p
              (pprogn
               (observation ctx
                            "Enabling immediate printing mode for ttag notes.")
               (f-put-global 'deferred-ttag-notes
                             :not-deferred
                             state)
               (f-put-global 'deferred-ttag-notes-saved
                             nil
                             state)))
             (t
              (pprogn (fms-to-standard-co
                       "TTAG NOTE: Printing of ttag notes is being put into ~
                        deferred mode.~|"
                       nil state nil)
                      (f-put-global 'deferred-ttag-notes
                                    :empty
                                    state))))
       (value :invisible)))
     (t (er soft ctx
            "The only legal values for set-deferred-ttag-notes are ~x0 and ~
             ~x1. ~ The value ~x2 is thus illegal."
            t nil val)))))

(defun ttags-from-deferred-ttag-notes1 (notes)

; Notes is formed by pushing ttag notes, hence we want to consider the
; corresponding ttags in reverse order.  But we'll want to reverse this
; result.

  (cond ((endp notes) nil)
        (t (add-to-set-eq (access deferred-ttag-note (car notes) :val)
                          (ttags-from-deferred-ttag-notes1 (cdr notes))))))

(defun ttags-from-deferred-ttag-notes (notes)
  (reverse (ttags-from-deferred-ttag-notes1 notes)))

(defun print-deferred-ttag-notes-summary (state)
  (let ((notes (f-get-global 'deferred-ttag-notes state)))
    (cond
     ((null notes)
      (f-put-global 'deferred-ttag-notes :empty state))
     ((atom notes) ; :empty or :not-deferred
      state)
     (t (pprogn (f-put-global 'deferred-ttag-notes-saved notes state)
                (fms-to-standard-co
                 "TTAG NOTE: Printing of ttag notes has been deferred for the ~
                  following list of ttags:~|  ~y0.To print the deferred ttag ~
                  notes:  ~y1."
                 (list (cons #\0 (ttags-from-deferred-ttag-notes notes))
                       (cons #\1 '(show-ttag-notes)))
                 state nil)
                (f-put-global 'deferred-ttag-notes :empty state))))))

(defun notify-on-defttag (val active-book-name include-bookp state)

; Warning: Here we must not call observation or any other printing function
; whose output can be inhibited.  The tightest security for ttags is obtained
; by searching for "TTAG NOTE" strings in the output.

  (cond
   ((or (f-get-global 'skip-notify-on-defttag state)
        (eq include-bookp :quiet))
    state)
   ((and (null include-bookp)
         (equal val (ttag (w state))))
; Avoid some noise, e.g. in encapsulate when there is already an active ttag.
    state)
   ((eq (f-get-global 'deferred-ttag-notes state)
        :not-deferred)
    (print-ttag-note val active-book-name include-bookp nil state))
   ((eq (f-get-global 'deferred-ttag-notes state)
        :empty)
    (pprogn (print-ttag-note val active-book-name include-bookp nil state)
            (f-put-global 'deferred-ttag-notes nil state)))
   (t
    (pprogn
     (cond ((null (f-get-global 'deferred-ttag-notes state))
            (fms-to-standard-co
             "TTAG NOTE: Deferring one or more ttag notes until the current ~
              top-level command completes.~|"
             nil state nil))
           (t state))
     (f-put-global 'deferred-ttag-notes
                   (cons (make deferred-ttag-note
                               :val val
                               :active-book-name active-book-name
                               :include-bookp include-bookp)
                         (f-get-global 'deferred-ttag-notes state))
                   state)))))

(defun ttag-allowed-p (ttag ttags active-book-name acc)

; We are executing a defttag event (or more accurately, a table event that
; could correspond to a defttag event).  We return nil if the ttag is illegal,
; else t if no update to ttags is required, else a new, more restrictive value
; for ttags that recognizes the association of ttag with active-book-name.

  (cond ((endp ttags)
         nil)
        ((eq ttag (car ttags))
         (revappend acc
                    (cons (list ttag active-book-name)
                          (cdr ttags))))
        ((atom (car ttags))
         (ttag-allowed-p ttag (cdr ttags) active-book-name
                         (cons (car ttags) acc)))
        ((eq ttag (caar ttags))
         (cond ((or (null (cdar ttags))
                    (member-equal active-book-name (cdar ttags)))
                t)
               (t nil)))
        (t (ttag-allowed-p ttag (cdr ttags) active-book-name
                           (cons (car ttags) acc)))))

(defun chk-acceptable-ttag1 (val active-book-name ttags-allowed ttags-seen
                                 include-bookp ctx state)

; An error triple (mv erp pair state) is returned, where if erp is nil then
; pair is either of the form (ttags-allowed1 . ttags-seen1), indicating a
; refined value for ttags-allowed and an extended value for ttags-seen, else is
; nil, indicating no such update.  By a "refined value" above, we mean that if
; val is a symbol then it is replaced in ttags-allowed by (val
; active-book-name).  However, val may be of the form (symbol), in which case
; no refinement takes place, or else of the form (symbol . filenames) where
; filenames is not nil, in which case active-book-name must be a member of
; filenames or we get an error.  Active-book-name is nil, representing the top
; level, or a string, generally thought of as an absolute filename.

; This function must be called if we are to add a ttag.  In particular, it
; should be called under table-fn; it would be a mistake to call this only
; under defttag, since then one could avoid this function by calling table
; directly.

; This function is where we call notify-on-defttag, which prints strings that
; provide the surest way for someone to check that functions requiring ttags
; are being called in a way that doesn't subvert the ttag mechanism.

  (let* ((ttags-allowed0 (cond ((eq ttags-allowed :all)
                                t)
                               (t (ttag-allowed-p val ttags-allowed
                                                  active-book-name nil))))
         (ttags-allowed1 (cond ((eq ttags-allowed0 t)
                                ttags-allowed)
                               (t ttags-allowed0))))
    (cond
     ((not ttags-allowed1)
      (er soft ctx
          "The ttag ~x0 associated with ~@1 is not among the set of ttags ~
           permitted in the current context, specified as follows:~|  ~
           ~x2.~|See :DOC defttag.~@3"
          val
          (if active-book-name
              (msg "file ~s0" active-book-name)
            "the top level loop")
          ttags-allowed
          (cond
           ((null (f-get-global 'skip-notify-on-defttag state))
            "")
           (t
            (msg "  This error is unusual since it is occurring while ~
                  including a book that appears to have been certified, in ~
                  this case, the book ~x0.  Most likely, that book needs to ~
                  be recertified, though a temporary workaround may be to ~
                  delete its certificate (i.e., its .cert file).  Otherwise ~
                  see :DOC make-event-details, section ``A note on ttags,'' ~
                  for a possible explanation."
                 (f-get-global 'skip-notify-on-defttag state))))))
     (t
      (pprogn
       (notify-on-defttag val active-book-name include-bookp state)
       (let ((old-filenames (cdr (assoc-eq val ttags-seen))))
         (cond
          ((member-equal active-book-name old-filenames)
           (value (cons ttags-allowed1 ttags-seen)))
          (t
           (value (cons ttags-allowed1
                        (put-assoc-eq val
                                      (cons active-book-name old-filenames)
                                      ttags-seen)))))))))))

(defun chk-acceptable-ttag (val include-bookp ctx wrld state)

; See the comment in chk-acceptable-ttag1, which explains the result for the
; call of chk-acceptable-ttag1 below.

  (cond
   ((null val)
    (value nil))
   (t
    (chk-acceptable-ttag1 val
                          (active-book-name wrld state)
                          (f-get-global 'ttags-allowed state)
                          (global-val 'ttags-seen wrld)
                          include-bookp ctx state))))

(defun chk-acceptable-ttags2 (ttag filenames ttags-allowed ttags-seen
                                   include-bookp ctx state)
  (cond ((endp filenames)
         (value (cons ttags-allowed ttags-seen)))
        (t (er-let* ((pair (chk-acceptable-ttag1 ttag (car filenames)
                                                 ttags-allowed ttags-seen
                                                 include-bookp ctx state)))
                    (mv-let (ttags-allowed ttags-seen)
                            (cond ((null pair)
                                   (mv ttags-allowed ttags-seen))
                                  (t (mv (car pair) (cdr pair))))
                            (chk-acceptable-ttags2 ttag (cdr filenames)
                                                   ttags-allowed ttags-seen
                                                   include-bookp ctx
                                                   state))))))

(defun chk-acceptable-ttags1 (vals active-book-name ttags-allowed ttags-seen
                                   include-bookp ctx state)

; See chk-acceptable-ttag1 for a description of the value returned based on the
; given active-book-name, tags-allowed, and ttags-seen.  Except, for this
; function, an element of vals can be a pair (tag . filenames), in which case
; active-book-name is irrelevant, as it is replaced by each filename in turn.
; If every element of vals has that form then active-book-name is irrelevant.

  (cond ((endp vals)
         (value (cons ttags-allowed ttags-seen)))
        (t (er-let* ((pair
                      (cond ((consp (car vals))
                             (chk-acceptable-ttags2 (caar vals) (cdar vals)
                                                    ttags-allowed ttags-seen
                                                    include-bookp ctx state))
                            (t
                             (chk-acceptable-ttag1 (car vals) active-book-name
                                                   ttags-allowed ttags-seen
                                                   include-bookp ctx state)))))
                    (mv-let (ttags-allowed ttags-seen)
                            (cond ((null pair)
                                   (mv ttags-allowed ttags-seen))
                                  (t (mv (car pair) (cdr pair))))
                            (chk-acceptable-ttags1 (cdr vals) active-book-name
                                                   ttags-allowed ttags-seen
                                                   include-bookp ctx
                                                   state))))))

; Next we handle the table event.  We formerly did this in other-events.lisp,
; but in v2-9 we moved it here, in order to avoid a warning in admitting
; add-pc-command-1 that the *1* function for table-fn is undefined.

(defun chk-table-nil-args (op bad-arg bad-argn ctx state)

; See table-fn1 for representative calls of this weird little function.

  (cond (bad-arg
         (er soft ctx
             "Table operation ~x0 requires that the ~n1 argument to ~
              TABLE be nil.  Hence, ~x2 is an illegal ~n1 argument.  ~
              See :DOC table."
             op bad-argn bad-arg))
        (t (value nil))))

(defconst *badge-table-guard-msg*

; This constant isn't used until apply.lisp, where it is used in functions
; supporting badge-table-guard.  But if this defconst is placed in apply.lisp
; the build fails because *badge-table-guard-msg* is unbound.  Presumably this
; happens when we're checking table guards as we build.  There might well be a
; better place to put such a defconst, but it doesn't seem worth the trouble to
; figure that out.

  (msg "The attempt to change the :badge-userfn-structure of the badge-table ~
        failed because "
       nil))

(defun chk-table-guard (name key val ctx wrld ens state)

; This function returns an error triple.  In the non-error case, the value is
; nil except when it is a pair as described in chk-acceptable-ttag1, based on
; the current book being included (if any), the value of state global
; 'tags-allowed, and the value of world global 'ttags-seen.

  (cond
   ((and (eq name 'acl2-defaults-table)
         (eq key :include-book-dir-alist)
         (not (f-get-global 'modifying-include-book-dir-alist state)))
    (er soft ctx
        "Illegal attempt to set the :include-book-dir-alist field of the ~
         acl2-defaults-table.  This can only be done by calling ~v0."
        '(add-include-book-dir delete-include-book-dir)))
   ((and (eq name 'include-book-dir!-table)
         (not (f-get-global 'modifying-include-book-dir-alist state)))
    (er soft ctx
        "Illegal attempt to set the include-book-dir!-table.  This can only ~
         be done by calling ~v0."
        '(add-include-book-dir! delete-include-book-dir!)))
   ((and (eq name 'puff-included-books)
         (not (f-get-global 'modifying-include-book-dir-alist state)))

; It's a bit of a hack (maybe a major hack) to use
; modifying-include-book-dir-alist as a way of supporting the use of the
; puff-included-books table when checking redundancy of include-book events.
; But that works well; it's not used for very much else, it's set to t while
; using :puff, and anyhow :puff is really a hack too.  This way we avoid adding
; yet another state global.

    (er soft ctx
        "Illegal attempt to set the puff-included-books table.  This can only ~
         be done by calling :puff or :puff*."))
   (t (let* ((prop (getpropc name 'table-guard *t* wrld))
             (mvp (and (consp prop)
                       (eq (car prop) :mv)))
             (term (if mvp (cdr prop) prop)))
        (er-progn
         (mv-let
           (erp ev-result latches)
           (ev term
               (list (cons 'key key)
                     (cons 'val val)
                     (cons 'world wrld)
                     (cons 'ens ens)
                     (cons 'state (coerce-state-to-object state)))
               state
               (list (cons 'state (coerce-state-to-object state)))
               nil

; We need aokp to be true; otherwise defwarrant can run into the following
; problem.  The function badge-table-guard calls badger, which can call
; g2-justification which can call type-set, which can lead to a call of
; ancestors-check, which typically has an attachment, ancestors-check-builtin.

               t)
           (declare (ignore latches))
           (cond
            (erp (pprogn
                  (error-fms nil ctx (car ev-result) (cdr ev-result) state)
                  (er soft ctx
                      "The TABLE :guard for ~x0 on the key ~x1 and value ~x2 ~
                      could not be evaluated."
                      name key val)))
            ((if mvp (car ev-result) ev-result)
             (value nil))
            ((and mvp (cadr ev-result))
             (er soft ctx
                 "~@0"
                 (cadr ev-result)))
            (t (er soft ctx
                   "The TABLE :guard for ~x0 disallows the combination of key ~
                   ~x1 and value ~x2.  The :guard is ~x3.  See :DOC table."
                   name key val (untranslate term t wrld)))))
         (if (and (eq name 'acl2-defaults-table)
                  (eq key :ttag))
             (chk-acceptable-ttag val nil ctx wrld state)
           (value nil)))))))

(defun chk-table-guards-rec (name alist ctx pair wrld ens state)
  (if alist
      (er-let* ((new-pair (chk-table-guard name (caar alist) (cdar alist) ctx
                                           wrld ens state)))
               (if (and pair new-pair)
                   (assert$ (and (eq name 'acl2-defaults-table)
                                 (eq (caar alist) :ttag))
                            (er soft ctx
                                "It is illegal to specify the :ttag twice in ~
                                 the acl2-defaults-table."))
                 (chk-table-guards-rec name (cdr alist) ctx new-pair wrld ens
                                       state)))
    (value pair)))

(defun chk-table-guards (name alist ctx wrld ens state)

; Consider the case that name is 'acl2-defaults-table.  We do not allow a
; transition from a non-nil (ttag wrld) to a nil (ttag wrld) at the top level,
; but no such check will be made by chk-table-guard if :ttag is not bound in
; alist.  See chk-acceptable-ttag.

  (er-let* ((pair (cond ((and (eq name 'acl2-defaults-table)
                              (null (assoc-eq :ttag alist)))
                         (chk-acceptable-ttag nil nil ctx wrld state))
                        (t (value nil)))))
            (chk-table-guards-rec name alist ctx pair wrld ens state)))

(defun put-assoc-equal-fast (name val alist)

; If there is a large number of table events for a given table all with
; different keys, the use of assoc-equal to update the table (in table-fn1)
; causes a quadratic amount of cons garbage.  The following is thus used
; instead.

  (declare (xargs :guard (alistp alist)))
  (if (assoc-equal name alist)
      (put-assoc-equal name val alist)
    (acons name val alist)))

(defun global-set? (var val wrld old-val)
  (if (equal val old-val)
      wrld
    (global-set var val wrld)))

(defun cltl-def-memoize-partial (fn total wrld)

; Fn and total are function symbols, where we expect that with respect to the
; Essay on Memoization with Partial Functions (Memoize-partial), fn plays the
; role of the Common Lisp function fn1 to be used for computing the limiting
; value of the ACL2 function (with a "limit" or "clock" argument), fn0-limit.
; Thus, we are supporting an event (memoize fn :total total) or
; (memoize-partial (... (fn total ...) ...) ...).  This function returns the
; definition of total associated with fn in the table, partial-functions-table,
; or nil if there is no associated definition.

  (let* ((recp (getpropc total 'recursivep nil wrld))
         (table-key (car recp))
         (tuples (cdr (assoc-eq table-key
                                (table-alist 'partial-functions-table wrld))))
         (tuple (assoc-eq fn tuples)))
    (car (last tuple))))

(defun table-cltl-cmd (name key val op ctx wrld)

; WARNING: For the case that name is 'memoize-table, keep this in sync with
; memoize-fn.

  (let ((unsupported-str
         "Unsupported operation, ~x0, for updating table ~x1."))
    (case name
      (memoize-table
       (cond ((eq op :guard) nil)
             ((not (eq op :put))
              (er hard ctx unsupported-str op name))
             (val

; We store enough in the cltl-cmd so that memoize-fn can be called (by
; add-trip) without having to consult the world.  This is important because in
; the hons version of Version_3.3, hence before we stored the cl-defun and
; condition-defun in this cltl-cmd tuple, we saw an error in the following, as
; explained below.

; (defun foo (x) (declare (xargs :guard t)) x)
; (defun bar (x) (declare (xargs :guard t)) x)
; (progn (defun foo-memoize-condition (x)
;          (declare (xargs :guard t))
;          (eq x 'term))
;        (table memoize-table 'foo (list 'foo-memoize-condition 't 'nil))
;        (progn (defun h (x) x)
;               (defun bar (x) (cons x x))))

; Why did this cause an error?  The problem was that when restoring the world
; from after bar up to the inner progn (due to its protection by
; revert-world-on-error), memoize-fn was calling cltl-def-from-name on (w
; *the-live-state*), but this world did not contain enough information for that
; call.  (Note that set-w! calls find-longest-common-retraction with event-p =
; nil in that case, which is why we roll back to the previous command, not
; event.  We might consider rolling back to the previous event in all cases,
; not just when certifying or including a book.  But perhaps that's risky,
; since one can execute non-events like defuns-fn in the loop that one cannot
; execute in a book without a trust tag (or in make-event; hmmmm...).)

; See add-trip for a call of memoize-fn using the arguments indicated below.
; We have seen an error result due to revert-world-on-error winding back to a
; command landmark.  See set-w! for a comment about this, which explains how
; problem was fixed after Version_3.6.1.  However, we prefer to fix the problem
; here as well, by avoiding the call of cltl-def-from-name in memoize-fn that
; could be attempting to get a name during extend-world1 from a world not yet
; installed.  So we make that call here, just below, and store the result in
; the cltl-command tuple.

              (let* ((condition-fn (cdr (assoc-eq :condition-fn val)))
                     (condition-def (and condition-fn
                                         (not (eq condition-fn t))
                                         (cltl-def-from-name condition-fn
                                                             wrld)))
                     (condition (or (eq condition-fn t)          ; hence t
                                    (car (last condition-def)))) ; maybe nil
                     (total (cdr (assoc-eq :total val))))
                `(memoize ,key ; fn
                          ,condition
                          ,(cdr (assoc-eq :inline val))
                          ,(if total
                               (cltl-def-memoize-partial key total wrld)
                             (cltl-def-from-name key wrld)) ; cl-defun
                          ,(getpropc key 'formals t wrld) ; formals
                          ,(getpropc key 'stobjs-in t wrld) ; stobjs-in
                          ,(getpropc key 'stobjs-out t

; Normally we would avoid getting the stobjs-out of return-last.  But
; return-last is rejected for mamoization anyhow (by memoize-table-chk).

                                     wrld) ; stobjs-out
                          ,(and (symbolp condition)
                                condition
                                (not (eq condition t))
                                (cltl-def-from-name
                                 condition wrld)) ; condition-defun
                          ,(and (cdr (assoc-eq :commutative val)) t)
                          ,(cdr (assoc-eq :forget val))
                          ,(cdr (assoc-eq :memo-table-init-size val))
                          ,(cdr (assoc-eq :aokp val))
                          ,(cdr (assoc-eq :stats val))
                          ,(cdr (assoc-eq :invoke val)))))
             (t `(unmemoize ,key))))
      (badge-table *special-cltl-cmd-attachment-mark*)
      (t nil))))

(defun table-fn1 (name key val op term ctx wrld ens state event-form)

; Warning: If the table event ever generates proof obligations, remove it from
; the list of exceptions in install-event just below its "Comment on
; irrelevance of skip-proofs".

; This is just the rational version of table-fn, with key, val, op and
; term all handled as normal (evaluated) arguments.  The chart in
; table-fn explains the legal ops and arguments.

  (case op
    (:alist
     (er-progn
      (chk-table-nil-args :alist
                          (or key val term)
                          (cond (key '(2)) (val '(3)) (t '(5)))
                          ctx state)
      (value (table-alist name wrld))))
    (:get
     (er-progn
      (chk-table-nil-args :get
                          (or val term)
                          (cond (val '(3)) (t '(5)))
                          ctx state)
      (value
       (cdr (assoc-equal key
                         (getpropc name 'table-alist nil wrld))))))
    (:put
     (with-ctx-summarized
      (make-ctx-for-event event-form ctx)
      (let* ((tbl (getpropc name 'table-alist nil wrld))
             (old-pair (assoc-equal key tbl)))
        (er-progn
         (chk-table-nil-args :put term '(5) ctx state)
         (cond
          ((and (or old-pair
                    (eq name 'memoize-table)) ; see :doc redundant-events
                (equal val (cdr old-pair)))
           (stop-redundant-event ctx state))
          (t (er-let*
                 ((pair (chk-table-guard name key val ctx wrld ens state))
                  (wrld0 (value
                          (cond
                           ((eq name 'puff-included-books)
                            (global-set
                             'include-book-alist

; This setting is for use in the implementation of :puff, where the
; puff-included-books table records books that have been puffed.  We could
; consider setting 'include-book-alist-all as well, but since that is only used
; for certification and one can't certify on a puffled world, we don't bother.
; (If that changes, then be careful that val is also the right tuple to push
; onto the global value of 'include-book-alist-all.)

                             (cons val
                                   (global-val 'include-book-alist
                                               wrld))
                             wrld))
                           (t wrld))))
                  (wrld1 (cond
                          ((null pair)
                           (value wrld0))
                          (t (let ((ttags-allowed1 (car pair))
                                   (ttags-seen1 (cdr pair)))
                               (pprogn (f-put-global 'ttags-allowed
                                                     ttags-allowed1
                                                     state)
                                       (value (global-set?
                                               'ttags-seen
                                               ttags-seen1
                                               wrld0
                                               (global-val 'ttags-seen
                                                           wrld)))))))))
               (install-event
                name
                event-form
                'table
                0
                nil
                (table-cltl-cmd name key val op ctx wrld)
                nil ; theory-related events do their own checking
                nil
                (putprop name 'table-alist
                         (if old-pair
                             (put-assoc-equal key val tbl)
                           (acons key val tbl))
                         wrld1)
                state))))))))
    (:clear
     (with-ctx-summarized
      (make-ctx-for-event event-form ctx)
      (er-progn
       (chk-table-nil-args :clear
                           (or key term)
                           (cond (key '(2)) (t '(5)))
                           ctx state)
       (cond
        ((equal val (table-alist name wrld))
         (stop-redundant-event ctx state))
        ((not (alistp val))
         (er soft 'table ":CLEAR requires an alist, but ~x0 is not." val))
        (t
         (let ((val (if (duplicate-keysp val)
                        (reverse (clean-up-alist val nil))
                      val)))
           (er-let*
               ((wrld1
                 (er-let* ((pair (chk-table-guards name val ctx wrld ens
                                                   state)))
                   (cond
                    ((null pair)
                     (value wrld))
                    (t (let ((ttags-allowed1 (car pair))
                             (ttags-seen1 (cdr pair)))
                         (pprogn (f-put-global 'ttags-allowed
                                               ttags-allowed1
                                               state)
                                 (value (global-set? 'ttags-seen
                                                     ttags-seen1
                                                     wrld
                                                     (global-val
                                                      'ttags-seen
                                                      wrld))))))))))
             (install-event name event-form 'table 0 nil
                            (table-cltl-cmd name key val op ctx wrld)
                            nil ; theory-related events do their own checking
                            nil
                            (putprop name 'table-alist val wrld1)
                            state))))))))
    (:guard
     (cond
      ((eq term nil)
       (er-progn
        (chk-table-nil-args op
                            (or key val)
                            (cond (key '(2)) (t '(3)))
                            ctx state)
        (value (getpropc name 'table-guard *t* wrld))))
      (t
       (with-ctx-summarized
        (make-ctx-for-event event-form ctx)
        (er-progn
         (chk-table-nil-args op
                             (or key val)
                             (cond (key '(2)) (t '(3)))
                             ctx state)
         (mv-let (erp tterm bindings state)
           (translate1 term :stobjs-out
                       '((:stobjs-out . :stobjs-out))
                       '(state) ; known-stobjs
                       ctx wrld state)

; Note that since known-stobjs above is '(state), no stobj can be returned.
; Note that translate11 doesn't allow calls of stobj creators or fixers for
; execution even when there is an active trust tag.

           (cond
            (erp (silent-error state)) ; already printed any message
            (t
             (let ((stobjs-out (translate-deref :stobjs-out bindings)))
               (cond
                ((not (or (equal stobjs-out '(nil))
                          (equal stobjs-out '(nil nil))))
                 (er soft 'table
                     "The table :guard must return either one or two ~
                      values~@0, but ~x1 ~@2."
                     (if (all-nils stobjs-out)
                         ""
                       ", none of them STATE or stobjs")
                     term
                     (if (cdr stobjs-out)
                         (msg "has output signature"
                              (cons 'mv stobjs-out))
                       (assert$
; See comment above about stobj creators and fixers.
                        (eq (car stobjs-out) 'state)
                        (msg "returns STATE"
                             (car stobjs-out))))))
                (t

; Known-stobjs includes only STATE.  No variable other than STATE is treated
; as a stobj in tterm.  Below we check that the only vars mentioned besides
; STATE are KEY, VAL, WORLD, and ENS.  These could, in principle, be declared
; stobjs by the user.  But when we ev tterm in the future, we will always bind
; them to non-stobjs.

                 (let ((old-guard (getpropc name 'table-guard nil wrld)))
                   (cond
                    ((equal old-guard tterm)
                     (stop-redundant-event ctx state))
                    (old-guard
                     (er soft ctx
                         "It is illegal to change the :guard on a table after ~
                          it has been given an explicit :guard.  The :guard ~
                          of ~x0 is ~x1 and this can be changed only by ~
                          undoing the event that set it.  See :DOC table."
                         name
                         (untranslate (getpropc name 'table-guard nil
                                                wrld)
                                      t wrld)))
                    ((getpropc name 'table-alist nil wrld)

; At one time Matt wanted the option of setting the :val-guard of a
; non-empty table, but he doesn't recall why.  Perhaps we'll add such
; an option in the future if others express such a desire.

                     (er soft ctx
                         "It is illegal to set the :guard of the non-empty ~
                          table ~x0.  See :DOC table."
                         name))
                    (t
                     (let ((legal-vars '(key val world ens state))
                           (vars (all-vars tterm)))
                       (cond ((not (subsetp-eq vars legal-vars))
                              (er soft ctx
                                  "The only variables permitted in the :guard ~
                                   of a table are ~&0, but your guard uses ~
                                   ~&1.  See :DOC table."
                                  legal-vars (reverse vars)))
                             (t (install-event
                                 name
                                 event-form
                                 'table
                                 0
                                 nil
                                 (table-cltl-cmd name key val op ctx wrld)
                                 nil ; theory-related events do the check
                                 nil
                                 (putprop name
                                          'table-guard
                                          (if (cdr stobjs-out)
                                              (cons :mv tterm)
                                            tterm)
                                          wrld)
                                 state))))))))))))))))))
    (otherwise (er soft ctx
                   "Unrecognized table operation, ~x0.  See :DOC table."
                   op))))

(defun table-fn (name args state event-form)

; Warning: If this event ever generates proof obligations, remove it from the
; list of exceptions in install-event just below its "Comment on irrelevance of
; skip-proofs".

; This is an unusual "event" because it sometimes has no effect on
; STATE and thus is not an event!  In general this function applies
; an operation, op, to some arguments (and to the table named name).
; Ideally, args is of length four and of the form (key val op term).
; But when args is shorter it is interpreted as follows.

; args              same as args
; ()                (nil nil :alist nil)
; (key)             (key nil :get   nil)
; (key val)         (key val :put   nil)
; (key val op)      (key val op     nil)

; Key and val are both treated as forms and evaluated to produce
; single results (which we call key and val below).  Op and term are
; not evaluated.  A rational version of this function that takes key,
; val, op and term all as normal arguments is table-fn1.  The odd
; design of this function with its positional interpretation of op and
; odd treatment of evaluation is due to the fact that it represents
; the macroexpansion of a form designed primarily to be typed by the
; user.

; Op may be any of :alist, :get, :put, :clear, or :guard.  Each op
; enforces certain restrictions on the other three arguments.

; op         restrictions and meaning
; :alist     Key val and term must be nil.  Return the table as an
;            alist pairing keys to their non-nil vals.
; :get       Val and term must be nil.Return the val associated with
;            key.
; :put       Key and val satisfy :guard and term must be nil.  Store
;            val with key.
; :clear     Key and term must be nil.  Clear the table, setting it
;            to val if val is supplied (else to nil).  Note that val
;            must be an alist, and as with :put, the keys and entries
;            must satisfy the :guard.
; :guard     Key and val must be nil, term must be a term mentioning
;            only the variables KEY, VAL, and WORLD, and returning one
;            result.  The table must be empty.  Store term as the
;            table's :guard.

  (let* ((ctx (cons 'table name))
         (wrld (w state))
         (ens (ens state))
         (event-form (or event-form
                         `(table ,name ,@args)))
         (n (length args))
         (key-form (car args))
         (val-form (cadr args))
         (op (cond ((= n 2) :put)
                   ((= n 1) :get)
                   ((= n 0) :alist)
                   (t (caddr args))))
         (term (cadddr args)))
    (er-progn
     (cond ((not (symbolp name))
            (er soft ctx
                "The first argument to table must be a symbol, but ~
                 ~x0 is not.  See :DOC table."
                name))
           ((< 4 (length args))
            (er soft ctx
                "Table may be given no more than five arguments.  In ~
                 ~x0 it is given ~n1.  See :DOC table."
                event-form
                (1+ (length args))))
           (t (value nil)))
     (er-let* ((key-pair
                (simple-translate-and-eval
                 key-form
                 (if (eq name 'acl2-defaults-table)
                     nil
                     (list (cons 'world wrld)))
                 nil
                 (if (eq name 'acl2-defaults-table)
                     "In (TABLE ACL2-DEFAULTS-TABLE key ...), key"
                     "The second argument of TABLE")
                 ctx wrld state nil))
               (val-pair
                (simple-translate-and-eval
                 val-form
                 (if (eq name 'acl2-defaults-table)
                     nil
                     (list (cons 'world wrld)
                           (cons 'ens ens)))
                 nil
                 (if (eq name 'acl2-defaults-table)
                     "In (TABLE ACL2-DEFAULTS-TABLE key val ...), val"
                     "The third argument of TABLE")
                 ctx wrld state nil)))
              (table-fn1 name (cdr key-pair) (cdr val-pair) op term
                         ctx wrld ens state event-form)))))

(defun set-override-hints-fn (lst at-end ctx wrld state)
  (er-let*
   ((tlst (translate-override-hints 'override-hints lst ctx wrld
                                    state))
    (new (case at-end
           ((t)
            (value (append (override-hints wrld) tlst)))
           ((nil)
            (value (append tlst (override-hints wrld))))
           (:clear
            (value tlst))
           (:remove
            (let ((old (override-hints wrld)))
              (value (set-difference-equal old tlst))))
           (otherwise
            (er soft ctx
                "Unrecognized operation in ~x0: ~x1."
                'set-override-hints-fn at-end)))))
   (er-progn
    (table-fn 'default-hints-table (list :override (kwote new)) state nil)
    (table-fn 'default-hints-table (list :override) state nil))))
