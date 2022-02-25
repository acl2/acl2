; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book provides utilities for accessing the checkpoints after failure of
; the most recent proof attempt.

(in-package "ACL2")

(set-state-ok t)

(defun checkpoint-stack-from-gag-state-saved (top-p state)

; Top-p is true when we want top-level checkpoints, and is false (nil) when we
; want checkpoints under a top-level induction.

; This returns nil if there are no checkpoints available.  Otherwise it returns
; a stack of gag-info records, each corresponding to a checkpoint that was
; pushed onto that stack -- thus, the latest checkpoint comes first, and the
; list should be reversed if you want them in order that they appeared during
; the proof attempt.  To access an individual gag-info record, use the ACCESS
; macro as shown below in the function checkpoint-info-list.

  (declare (xargs :guard (and (f-boundp-global 'gag-state-saved state)
                              (or (null (f-get-global 'gag-state-saved state))
                                  (weak-gag-state-p
                                   (f-get-global 'gag-state-saved state))))))
  (let ((gag-state (f-get-global 'gag-state-saved state)))
    (cond ((null gag-state) :unavailable)
          (top-p (access gag-state gag-state :top-stack))
          (t (access gag-state gag-state :sub-stack)))))

(defun checkpoints-forcep (state)

; A non-nil return indicates that forcing took place (hence, the checkpoints
; aren't probably not the full failure story).

  (declare (xargs :guard (and (f-boundp-global 'gag-state-saved state)
                              (weak-gag-state-p
                               (f-get-global 'gag-state-saved state)))))
  (let ((gag-state (f-get-global 'gag-state-saved state)))
    (access gag-state gag-state :forcep)))

(defun weak-gag-info-lisp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        ((weak-gag-info-p (car x))
         (weak-gag-info-lisp (cdr x)))
        (t nil)))

(defun checkpoint-list-guard (top-p state)

; Here top-p can take the special value, :BOTH, when we want a guard that works
; for both the top-level checkpoint list and the not-top-level checkpoint list.

  (declare (xargs :guard t))
  (and (f-boundp-global 'gag-state-saved state)
       (or (null (f-get-global 'gag-state-saved state))
           (and (weak-gag-state-p
                 (f-get-global 'gag-state-saved state))
                (cond ((eq top-p :both)
                       (and (weak-gag-info-lisp
                             (checkpoint-stack-from-gag-state-saved nil state))
                            (weak-gag-info-lisp
                             (checkpoint-stack-from-gag-state-saved t state))))
                      (t
                       (weak-gag-info-lisp
                        (checkpoint-stack-from-gag-state-saved
                         top-p state))))))))

(defun checkpoint-info-list-rec (stack acc)

; Keep this in sync with checkpoint-list-rec, which provides just the list of
; checkpoint goals.  See also checkpoint-info-list.

  (declare (xargs :guard (weak-gag-info-lisp stack)))
  (cond
   ((endp stack) acc)
   (t (checkpoint-info-list-rec
       (cdr stack)
       (let ((gag-info (car stack)))
         (cons (list (cons :clause-id (access gag-info gag-info :clause-id))
                     (cons :clause (access gag-info gag-info :clause))
                     (cons :pushed (access gag-info gag-info :pushed)))
               acc))))))

(defun checkpoint-info-list (top-p state)

; This returns the clauses corresponding to the given stack of records (the
; reversing the stack).  Except, if there is no global information available
; for computing that result (i.e., state global gag-state-saved is nil), return
; :unavailable.

; Keep this in sync with checkpoint-list, which provides just the list of
; checkpoint goals.  Also keep this in sync with checkpoint-list-pretty.  The
; present function returns a list of alists, one per clause, each of which maps
; :clause-id and :clause to the clause-id and clause for a given checkpoint,
; respectively.  It also returns a low-level :pushed field, not yet documented.

  (declare (xargs :guard (checkpoint-list-guard top-p state)))
  (let ((stack (checkpoint-stack-from-gag-state-saved top-p state)))
    (cond ((eq stack :unavailable) :unavailable)
          (t (checkpoint-info-list-rec stack nil)))))

(defun checkpoint-list-rec (stack acc)

; Keep this in sync with checkpoint-info-list-rec, which provides lower-level
; information.  See also checkpoint-list.

  (declare (xargs :guard (weak-gag-info-lisp stack)))
  (cond
   ((endp stack) acc)
   (t (checkpoint-list-rec
       (cdr stack)
       (cons (access gag-info (car stack) :clause) acc)))))

(defun checkpoint-list (top-p state)

; This returns the clauses corresponding to the given stack of records (the
; reversing the stack).  Except, if there is no global information available
; for computing that result (i.e., state global gag-state-saved is nil), return
; :unavailable.

; Keep this in sync with checkpoint-list, which provides additional
; information.  Also keep this in sync with checkpoint-list-pretty.

  (declare (xargs :guard (checkpoint-list-guard top-p state)))
  (let ((stack (checkpoint-stack-from-gag-state-saved top-p state)))
    (cond ((eq stack :unavailable) :unavailable)
          (t (checkpoint-list-rec stack nil)))))

; The use of fms below is enough to push us to use program mode, but the uses
; of prettyify-clause and untranslate are reasons, too.
(program)

(defun checkpoint-list-pretty (top-p state)

; This returns the clauses corresponding to the given stack of records (the
; reversing the stack), but only after prettyifying them -- i.e., turning each
; clause into a goal such as one sees printed in prover output.  Except, if
; there is no global information available for computing that result (i.e.,
; state global gag-state-saved is nil), return :unavailable.

; Keep this in sync with checkpoint-list and checkpoint-info-list.

  (declare (xargs :guard ; perhaps only a partial guard
                  (checkpoint-list-guard top-p state)))
  (let ((clauses (checkpoint-list top-p state)))
    (cond ((eq clauses :unavailable) :unavailable)
          (t (prettyify-clause-lst clauses
                                   (let*-abstractionp state)
                                   (w state))))))

; The following display utilities are modified from comments defining versions
; of show-gag-info and other utilities in ACL2 source file prove.lisp.

(defun show-gag-info (info prettyify let*-abstractionp wrld state)
  (fms "~@0:~%~Q12~|"
       (list (cons #\0 (tilde-@-clause-id-phrase
                        (access gag-info info :clause-id)))
             (cons #\1 (let ((clause (access gag-info info :clause)))
                         (if prettyify
                             (prettyify-clause clause let*-abstractionp wrld)
                           clause)))
             (cons #\2 nil))
       (standard-co state) state nil))

(defun show-gag-stack-rec (stack prettyify let*-abstractionp wrld state)
  (if (endp stack)
      state
    (pprogn (show-gag-info (car stack) prettyify let*-abstractionp wrld state)
            (show-gag-stack-rec (cdr stack) prettyify let*-abstractionp wrld
                                state))))

(defun show-gag-stack (stack prettyify state)
  (cond ((null stack)
         (fms "[Empty]~|" nil (standard-co state) state nil))
        (t (show-gag-stack-rec (reverse stack)
                               prettyify
                               (let*-abstractionp state)
                               (w state)
                               state))))

(defun show-checkpoint-list-fn (prettyify state)
  (let ((gag-state (f-get-global 'gag-state-saved state)))
    (cond
     ((null gag-state)
      (fms "There are no checkpoints available to show.~|"
           nil (standard-co state) state nil))
     (t
      (let* ((top-stack (access gag-state gag-state :top-stack))
             (sub-stack (access gag-state gag-state :sub-stack))
             (standard-co (standard-co state)))
        (pprogn (fms "++++++ Top-level checkpoint list: ++++++~%"
                     nil standard-co state nil)
                (show-gag-stack top-stack prettyify state)
                (fms "++++++ Non-top-level checkpoint list: ++++++~%"
                     nil standard-co state nil)
                (show-gag-stack sub-stack prettyify state)
                (fms "++++++ Forced goals?: ~s0 ++++++~|"
                     (list (cons #\0
                                 (if (access gag-state gag-state :forcep)
                                     "Yes"
                                   "No")))
                     standard-co state nil)
                (fms "++++++ Abort?: ~@0 ++++++~|"
                     (let ((cause (access gag-state gag-state :abort-stack)))

; A non-nil value is a symbol giving the cause for aborting the proof, if any,
; which could be do-not-induct, empty-clause, or induction-depth-limit-exceeded
; (these have the obvious meanings).

                       (list (cons #\0
                                   (if (and cause (symbolp cause))
                                       (msg "Yes, ~s0" cause)
                                     "No"))))
                     standard-co state nil)))))))

(defmacro show-checkpoint-list (&optional prettyify)
  `(show-checkpoint-list-fn ,prettyify state))

