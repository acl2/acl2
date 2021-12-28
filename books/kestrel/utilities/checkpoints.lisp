; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book provides utilities for accessing the checkpoints after failure of
; the most recent proof attempt.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

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

(defxdoc checkpoint-list

; A wart, documented below, is that we get <GOAL> when aborting the proof to
; use induction on the original goal.  That's because this tool is built on the
; same code base that prints during proof attempts.  One might consider a
; variant of this tool that takes the original input as an argument, and if it
; finds <GOAL> (in the ACL2 package) in the top-stack, that is changed to the
; input (suitably translated or not).  But it might make more sense to store
; the original goal in the ACL2 gag-state structure, which would require a
; change to ACL2.

   :parents (kestrel-utilities prover-output)
   :short "Return prover key checkpoint clauses programmatically."
   :long "<p>Recall the key checkpoints printed at the end of a failed proof
 attempt.  Some are labeled ``Key checkpoint at the top level''; let us call
 these checkpoints ``top-level'', and denote others as ``not top-level''.  When
 the most recent proof attempt was one that failed, @('(checkpoint-list top-p
 state)') returns clauses corresponding to key checkpoints, as follows.  If
 @('top-p') is @('t'), then the list of top-level checkpoints is returned.
 Otherwise the list of checkpoints that are not top-level is returned.  In each
 case, the order of checkpoints is the same as would be found in the summary of
 a proof attempt; that is, their order agrees with the order in which they are
 generated during the proof attempt.</p>

 <p><b>Related tools.</b>  Note that each returned checkpoint is a clause, that
 is, a list of @(see term)s, implicitly disjoined.  For a similar utility that
 instead returns each checkpoint as an untranslated @(see term) such as one
 would see during a proof, see @(see checkpoint-list-pretty).  See also @(see
 show-checkpoint-list) for a related tool that displays checkpoints rather than
 returning them, and see @(see checkpoint-info-list) for a tool similar to
 @('checkpoint-list') that returns additional information.</p>

 <p>Examples may be found in the @(see community-books) file
 @('checkpoints-tests-input.lsp'), with corresponding output (using the @(tsee
 run-script) tool) in that same directory, in file
 @('checkpoints-tests-log.txt').</p>

 <p>Here are details to keep in mind.</p>

 <ul>

 <li>A return value of @(':UNAVAILABLE') indicates that no information on
 checkpoints is available, presumably because the most recent proof attempt
 succeeded.</li>

 <li>This utility produces the appropriate result even when inhibited
 @('SUMMARY') output (see @(see set-inhibit-output-lst)) suppresses the
 printing of key checkpoints in a proof attempt.</li>

 <li>Each forcing round (see @(see forcing-round)) is considered a new proof
 attempt for purposes of this tool.</li>

 <li>Suppose a proof attempt is aborted in favor of proving the original goal
 by induction, as typically indicated with the following prover output.

 @({
 We therefore abandon our previous work on this conjecture and
 reassign the name *1 to the original conjecture.
 })

 In that case, the unique top-level checkpoint is @('(<GOAL>)').  Moreover, all
 information stored for the proof attempt is based on the part of the attempt
 starting after returning to prove the original goal by induction; all
 checkpoints produced before that happens will be lost.  If that isn't what you
 want, consider using @(':')@(tsee otf-flg).</li>

 <li>The notion of ``most recent proof attempt'' includes proof attempts made
 during @(tsee make-event) expansion.</li>

 </ul>")

(defxdoc checkpoint-list-pretty
   :parents (kestrel-utilities prover-output)
   :short "Return prover key checkpoint goals programmatically."
   :long "<p>See @(see checkpoint-list) for relevant background and related
 utilities.  Here we explain only how @('checkpoint-list-pretty') differs from
 @('checkpoint-list').</p>

 <p>Recall that @('checkpoint-list') returns a list of clauses or the keyword
 @(':UNAVAILABLE').  The corresponding value @('(checkpoint-list-pretty top-p
 state)') is obtained by replacing each such clause by a corresponding
 untranslated @(see term), which is the goal displayed during output from the
 corresponding failed proof.  For a clause with only one member, that is simply
 the untranslation of that member.  Otherwise the clause is a list @('(t0
 ... tn)'), in which case the corresponding untranslated term is an implication
 @('(implies p q)') , where @('p') is formed by conjoining the untranslation
 the negations of the @('ti') for each @('i < n'), and @('q') is the
 untranslation of @('tn').</p>

 <p><b>Remarks.</b></p>

 <ul>

 <li>Untranslation is sensitive to @(tsee let*) abstraction; see @(see
 set-let*-abstractionp).</li>

 <li>Unlike functions @('checkpoint-list') and @('checkpoint-info-list'), which
 are @(see guard)-verified @(see logic)-mode functions,
 @('checkpoint-list-pretty') is a @(see program)-mode function.</li>

 </ul>")

(defxdoc checkpoint-info-list
   :parents (kestrel-utilities prover-output)
   :short "Return prover key checkpoint information programmatically."
   :long "<p>See @(see checkpoint-list) for relevant background and related
 utilities.  Here we explain only how @('checkpoint-info-list') differs from
 @('checkpoint-list').  The difference is that instead of a list of clauses,
 it returns a list of alists each of the following form.</p>

 @({
 ((:clause-id . clause-id)
  (:clause . clause)
  (:pushed . pushed))
 })

 <p>Here, @('clause-id') is the @(see clause-identifier) of the indicated
 clause.  The value of @('pushed') is left undocumented here (low-level
 technical note: it comes from the @(':pushed') field of the corresponding
 @('gag-info') record).</p>")

(defxdoc show-checkpoint-list
   :parents (kestrel-utilities prover-output)
   :short "Display prover key checkpoint information."
   :long "<p>See @(see checkpoint-list) for relevant background.  Evaluation of
 the macro call @('(show-checkpoint-list)') prints checkpoint clauses (as
 returned by @('checkpoint-list')) as well as related information.  An optional
 argument has default @('nil'); when it is not @('nil'), then the checkpoints
 are printed as untranslated terms, as described in the documentation for
 @(tsee checkpoint-list-pretty).  Whether printed as a clause or as an
 untranslated term, each checkpoint is printed with its @(see goal-spec), i.e.,
 the user-friendly goal name that one sees in prover output for a @(see
 clause-identifier).</p>

 <p>Also shown are whether or not at least one goal was @(see force)d during
 the failed proof and whether the proof was aborted, and (briefly) why.</p>")
