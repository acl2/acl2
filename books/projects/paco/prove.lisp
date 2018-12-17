(in-package "PACO")

; Section: THE WATERFALL

; The waterfall is a simple finite state machine (whose individual
; state transitions are very complicated).  Abstractly, each state
; contains a "processor" and transitions to one of two neighbor
; states, the "hit" state and the "miss" state.  Roughly speaking,
; when we are in a state we apply its processor to the input clause
; and obtain either a "hit" signal (and some new clauses) or "miss"
; signal.  We then transit to the appropriate state and continue.

; However, the "hit" state for every state is the top of the falls.


;  +<---------------------------------------+
;  |                                        |
; apply-hints-clause ---------------------->|
;  |                                        |
; simplify-clause ------------------------->|
;  |                                        |
; settled-down-clause---------------------->|
;  |                                        |
; ...                                       |
;  |                                        |
; induct-clause --------------------------->+
;  |
; UNPROVED

; We therefore represent a state s of the waterfall as a pair whose car
; is the processor for s and whose cdr is the miss state for s.  The hit
; state for every state is the constant state below, which includes, by
; successive cdrs, every state below it in the falls.

; Because the word "STATE" has a very different meaning in ACL2 than we have
; been using thus far in this discussion, we refer to the "states" of the
; waterfall as "ledges" and basically name them by the processors on each.

; Observe that the cdr of the 'simplify-clause ledge, for example, is the
; 'settled-down-clause ledge, etc.  That is, each ledge contains the
; ones below it.

; Note: To add a new processor to the waterfall you must add the
; appropriate entry to the *waterfall* and redefine
; apply-waterfall-process below.

; The waterfall builds a proof attempt, represented by

(defrec proof-attempt (process depth-to-go clause-id
                               input-clause input-hist input-pspv
                               output-signal . children))

; A proof attempt is a tree of proot-attempt nodes.  The process is
; one of the waterfall processes or else INDUCT.  The depth-to-go
; records how much recursion depth is left in the waterfall -- there
; is no reason to believe that repeated simplification will ultimately
; terminate.  Input-clause, input-hist and input-pspv record the input
; to the processor.  The world is always constant and is not part of
; the proof-attempt.  Output-signal records the output signal produced
; by the processor.  Finally, children is the recursively obtained
; list of proof-attempts for each child produced by the processor.

; The legal signals are HIT, MISS, ABORT or anything else.  The last
; indicates an error and is actually handled like an ABORT: further
; processing of the children is not pursued, but ongoing computations for the
; other higher- and peer-subgoals continues uninterrupted.

; About Hints: The pspv contains :hint-settings, which is an alist
; pairing clause ids with hint information.  To apply hints, we first
; determine whether there is a pair for the given clause id.  If there is,
; we may change the clause (i.e., adding a hypothesis as per a :USE
; hint).  We may change the :rewrite-constant in the pspv (i.e., to
; install a new enabled structure).  We also change the :hint-settings
; in the pspv, removing the hint just used.  We also change the hist,
; adding an APPLY-HINTS-CLAUSE entry.

; Here is a generic hint-settings

; ((id . ((:USE . (term1 term2 ... termk)) ; a list of terms to add as hyps
;         (:ENS . ens)                     ; a new enabled structure
;         (:INDUCT . term)                 ; a term to suggest an induction
;         ))
;  ...)

(defun apply-hints-clause1 (alist cl pspv)

; Here, alist is the alist pairing :keys to values.  That alist was
; paired in the hint-settings with the id of clause cl.  We apply that
; alist to cl and pspv, obtaining (mv cl' pspv').

  (cond
   ((endp alist) (mv cl pspv))
   (t (let ((key (car (car alist)))
            (val (cdr (car alist)))
            (rcnst (access prove-spec-var pspv :rewrite-constant)))
        (case key
          (:USE
           (apply-hints-clause1 (cdr alist)
                                (disjoin-clauses
                                 (dumb-negate-lit-lst val)
                                 cl)
                                pspv))
          (:IN-THEORY
           (apply-hints-clause1 (cdr alist)
                                cl
                                (change prove-spec-var pspv
                                        :rewrite-constant
                                        (change rewrite-constant
                                                rcnst
                                                :ens val))))
          (:INDUCT
           (apply-hints-clause1 (cdr alist)
                                cl
                                (change prove-spec-var pspv
                                        :induct-hint-val
                                        val)))
          (:HANDS-OFF
           (apply-hints-clause1 (cdr alist)
                                cl
                                (change prove-spec-var pspv
                                        :rewrite-constant
                                        (change rewrite-constant
                                                rcnst
                                                :fns-to-be-ignored val))))
          (:EXPAND
           (apply-hints-clause1 (cdr alist)
                                cl
                                (change prove-spec-var pspv
                                        :rewrite-constant
                                        (change rewrite-constant
                                                rcnst
                                                :expand-lst val))))
          (:DO-NOT
           (apply-hints-clause1 (cdr alist)
                                cl
                                (change prove-spec-var pspv
                                        :do-not-processes
                                        val)))
          (otherwise
           (apply-hints-clause1 (cdr alist) cl pspv)))))))

(defun apply-hints-clause (id cl hist pspv wrld)

; This is a standard waterfall processor.  In fact, it is the first
; processor in the waterfall.  As for all processors, the results are
; (mv signal cl-set hist-obj new-pspv).

; The idea here is to recognize whether id has an associated hint in
; the pspv and if so to apply the hint.  Typically a hint might change
; the clause and the pspv, e.g., adding hyps to one and deleting the
; hint from the other after modifying the :rewrite-constant.

  (declare (ignore hist wrld))
  (let ((temp
         (assoc-equal id (access prove-spec-var pspv :hint-settings))))
    (cond
     (temp
      (mv-let (new-cl new-pspv)
              (apply-hints-clause1
               (cdr temp)
               cl
               (change prove-spec-var pspv
                       :hint-settings
                       (remove1-equal temp
                                      (access prove-spec-var pspv
                                              :hint-settings))))
              (mv 'HIT (list new-cl) nil new-pspv)))
     (t (mv 'MISS nil nil nil)))))


; Here is the function that applies a waterfall processor.  Note that
; if the pspv contains an :induct-hint-val other than :DO-NOT-INDUCT,
; then every processor except induct-clause is a no-op.  If the hint
; is :DO-NOT-INDUCT we just take the natural course through the
; waterfall and fail when (if) we get to induction.  If an induction
; hint of T or a term was provided, we skip other processes and go
; straight to induction.

; This is another identity function used for nume tracking.  But it is
; not cut from the standard mold because it also prints a message
; about the just-completed waterfall process.

(defun apply-waterfall-process (process id cl hist pspv wrld)
  (cond
   ((member-eq process (access prove-spec-var pspv :do-not-processes))
    (mv 'miss nil nil nil))
   ((and (access prove-spec-var pspv :induct-hint-val)
         (not (equal (access prove-spec-var pspv :induct-hint-val)
                     :do-not-induct))
         (not (equal process 'induct-clause)))
    (mv 'miss nil nil nil))
   (t

; This is a weird call of my macro.  Push a new empty frame.  If the
; result is HIT, then print the stuff indicated and pop the frame with flg t
; else don't print and pop the frame with flg nil.
; The problem is that I don't have any assurance that the "printing" code
; prints instead of doing some arbitrary unsound raw lisp thing.

    (<apply-waterfall-process-id>
     (case process
       (apply-hints-clause
        (apply-hints-clause id cl hist pspv wrld))
       (simplify-clause
        (simplify-clause id cl hist pspv wrld))
       (settled-down-clause
        (settled-down-clause id cl hist pspv wrld))
       (eliminate-destructors-clause
        (eliminate-destructors-clause id cl hist pspv wrld))
       (induct-clause
        (induct-clause id cl hist pspv wrld))
       (otherwise
        (mv 'abort nil (list (cons :UNKNOWN-PROCESS process)) pspv)))))))

(defconst *waterfall*
  '(apply-hints-clause
    simplify-clause
    settled-down-clause
    eliminate-destructors-clause
    induct-clause
    ))

; Guide to the Waterfall Code: The top-level function is waterfall.
; It trickles down the ledges, trying each process until it comes to
; one that HITs.  When that happens, it calls waterfall-lst on the
; children.  That function computes the new clause id for each child
; and calls waterfall on each one.  The lex4 measure is used, but only
; the first 3 components are relevant.  The last is always 0; I didn't
; have lex3.

(mutual-recursion

(defun waterfall (ledge id cl hist pspv wrld nnn)
  (declare (xargs :measure (lex4 (nfix nnn) (acl2-count ledge) 0 0)
                  :hints (("Goal"
                           :in-theory (disable apply-waterfall-process)))))
  (cond
   ((or (endp ledge) (zp nnn))
    (make proof-attempt
          :process 'UNPROVED
          :depth-to-go nnn
          :clause-id id
          :input-clause cl
          :input-hist hist
          :input-pspv pspv
          :output-signal (if (zp nnn) 'TIMEOUT 'UNPROVED)
          :children nil))
   (t (mv-let (signal cl-set hist-alist new-pspv)
              (apply-waterfall-process (car ledge) id cl hist pspv wrld)
              (case signal
                (HIT
                 (let ((new-hist
                        (cons (make history-entry
                                    :processor (car ledge)
                                    :clause cl
                                    :alist hist-alist)
                              hist))

; Some hints are not inherited from their parents.  This is the place
; we reset the un-inherited hints.  At the moment, the only such hint
; is the :do-not one.  If that were inherited and the user, say,
; turned off simplify-clause for a given goal, it would stay off for
; all children until turned back on.

                       (new-pspv (change prove-spec-var new-pspv
                                         :do-not-processes nil)))
                   (make proof-attempt
                         :process (car ledge)
                         :depth-to-go nnn
                         :clause-id id
                         :input-clause cl
                         :input-hist hist
                         :input-pspv pspv
                         :output-signal 'HIT
                         :children (waterfall-lst id
                                                  cl-set
                                                  new-hist
                                                  new-pspv
                                                  wrld
                                                  (- nnn 1)))))
                (MISS (waterfall (cdr ledge) id cl hist pspv wrld nnn))
                (otherwise

; Typically the only other signal is ABORT, which means the proof has
; failed and the input-clause is an unproved subgoal.  But the signal
; might be an arbitrary "error message".

                 (let ((new-hist (cons (make history-entry
                                             :processor (car ledge)
                                             :clause cl
                                             :alist hist-alist)
                                       hist)))
                   (make proof-attempt
                         :process (car ledge)
                         :depth-to-go nnn
                         :clause-id id
                         :input-clause cl
                         :input-hist new-hist
                         :input-pspv pspv
                         :output-signal signal
                         :children nil))))))))

(defun waterfall-lst (id0 clauses hist pspv wrld nnn)
  (declare (xargs :measure
                  (lex4 (nfix nnn)
                        (acl2-count *waterfall*)
                        (acl2-count clauses)
                        0)))
  (cond
   ((endp clauses) nil)
   (t (cons (waterfall *waterfall*
                       (append id0 (list (len clauses)))
                       (car clauses) hist pspv wrld nnn)
            (waterfall-lst id0 (cdr clauses) hist pspv wrld nnn)))))
)

(mutual-recursion

(defun scan-proof-attempt1 (p errors subgoals)

; We explore a proof-attempt p and collect into errors every error signal
; or other anomaly and collect into subgoals every unproved
; subgoal.  Each new element is collected in a keyword pair:

; (:SUBGOAL id clause-as-formula)
; (:ERROR   signal)

; We return (mv errors subgoals).

  (cond ((endp p)
         (mv (cons '(:ERROR ILL-FORMED) errors)
             subgoals))
        ((eq (access proof-attempt p :process) 'UNPROVED)
         (mv errors
             (cons (list :SUBGOAL (access proof-attempt p :clause-id)
                         (prettyify-clause
                          (access proof-attempt p :input-clause)))
                   subgoals)))
        ((member (access proof-attempt p :process) *waterfall*)
         (cond ((eq (access proof-attempt p :output-signal) 'HIT)
                (scan-proof-attempt1-lst (access proof-attempt p :children)
                                         errors subgoals))
               (t (mv (cons (list :ERROR 'UDS
                                  (access proof-attempt p :output-signal))
                            errors)
                      subgoals))))
        (t (mv (cons (list :ERROR 'UDF
                           (access proof-attempt p :process))
                     errors)
               subgoals))))

(defun scan-proof-attempt1-lst (plst errors subgoals)
  (cond ((endp plst) (mv errors subgoals))
        (t (mv-let (errors subgoals)
                   (scan-proof-attempt1 (car plst) errors subgoals)
                   (scan-proof-attempt1-lst (cdr plst) errors subgoals)))))
)

(defun scan-proof-attempt (p)
  (mv-let (errors subgoals)
          (scan-proof-attempt1 p nil nil)
          (cond ((and (null errors) (null subgoals)) :QED)
                (t (list :FAILURE
                         (cons :ERRORS errors)
                         (cons :SUBGOALS subgoals))))))

(mutual-recursion

(defun condense-proof-attempt1 (p)
; We assume there are no errors in the scanned proof attempt.
  (cond
   ((consp p)
    (list* (access proof-attempt p :process)
           (list :SUBGOAL (access proof-attempt p :clause-id)
                 (prettyify-clause
                  (access proof-attempt p :input-clause)))
           (condense-proof-attempt1-lst (access proof-attempt p :children))))
   (t nil)))

(defun condense-proof-attempt1-lst (plst)
  (cond
   ((endp plst) nil)
   (t (cons (condense-proof-attempt1 (car plst))
            (condense-proof-attempt1-lst (cdr plst))))))

)

(defun condense-proof-attempt (p)
  (let ((temp (scan-proof-attempt p)))
    (cond ((eq temp :QED)
           (condense-proof-attempt1 p))
          ((and (consp temp)
                (null (cdr (assoc-eq :ERRORS (cdr temp)))))
           (condense-proof-attempt1 p))
          (t temp))))

(defun describe-proof-attempt (p d-level)
  (case d-level
    (0 (scan-proof-attempt p))
    (1 (condense-proof-attempt p))
    (otherwise p)))

; THE PROVER

(defun prove1 (term pspv wrld waterfall-depth)
  (waterfall *waterfall* nil (list term) nil pspv wrld waterfall-depth))

(defun make-initial-pspv (ens hint-settings)
  (make prove-spec-var
        :rewrite-constant
        (make rewrite-constant
              :expand-lst nil
              :terms-to-be-ignored-by-rewrite nil
              :top-clause nil
              :current-clause nil
              :ens ens
              :current-literal nil)
        :induct-hint-val nil
        :induction-hyp-terms nil
        :induction-concl-terms nil
        :do-not-processes nil
        :hint-settings hint-settings
        :global-ens ens))

; The following function is still the identity function.  But it is
; not cut from the standard mold.  After doing the standard nume
; tracking and evaluating body, it prints all the numes in the
; top-most frame of the nume stack.  It first converts them to runes.

(defun prove (term ens wrld hint-settings waterfall-depth)
  (<prove-id>
   (prove1 term
           (make-initial-pspv ens hint-settings)
           wrld waterfall-depth)))


