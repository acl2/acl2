; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
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

(defmacro install-new-pc-meta-or-macro (command-type raw-name name formals doc body)
  `(progn ,(pc-meta-or-macro-defun raw-name name formals doc body)
          (add-pc-command ,name ',command-type)))

(defun define-pc-meta-or-macro-fn (command-type raw-name formals body)
  (let ((name (make-official-pc-command raw-name)) )
    `(install-new-pc-meta-or-macro ,command-type ,raw-name ,name
                                   ,formals
                                   nil ; ,doc
                                   ,body)))

(defmacro define-pc-meta (raw-name formals &rest body)
  (define-pc-meta-or-macro-fn 'meta raw-name formals body))

(defmacro define-pc-macro (raw-name formals &rest body)
  (define-pc-meta-or-macro-fn 'macro raw-name formals body))

(defmacro define-pc-atomic-macro (raw-name formals &rest body)
  (define-pc-meta-or-macro-fn 'atomic-macro raw-name formals body))

(defmacro toggle-pc-macro (name &optional new-tp)
  (declare (xargs :guard (and (symbolp new-tp)
                              (or (null new-tp)
                                  (member-equal (symbol-name new-tp)
                                                '("MACRO" "ATOMIC-MACRO"))))))
  `(toggle-pc-macro-fn ',(make-official-pc-command name) ',new-tp state))

(defmacro define-pc-primitive (raw-name formals &rest body)

; Define-pc-primitive defines a new primitive for the proof-builder.  That
; primitive is always a function returning (mv pc-state state), where the
; (pc-value state-stack) has not been changed for state.

; Primitive command definitions should never look at the instruction field of
; the current state; see pc-primitive-defun-form.

; We generally rely in pc-single-step-primitive on the following property: a
; primitive leaves the top goal on the top of the :goals stack of the pc-state,
; adjusted as necessary, with its depends-on field reflecting all new subgoals
; added to that stack.  However, if the top goal is proved and no forced
; hypotheses are stored in the tag tree (see pc-single-step-primitive), then we
; may drop a proved goal.

  (let ((name (make-official-pc-command raw-name)))
    `(progn
       ,(pc-primitive-defun-form raw-name name formals
                                 nil ; doc
                                 body)
       (add-pc-command ,name 'primitive))))

(define-pc-primitive comment (&rest x)
  (declare (ignore x))
  (mv pc-state state))

(defun non-bounded-nums (nums lower upper)
  (declare (xargs :guard (and (rationalp lower)
                              (rationalp upper)
                              (true-listp nums))))
  (if (consp nums)
      (if (and (integerp (car nums))
               (<= lower (car nums))
               (<= (car nums) upper))
          (non-bounded-nums (cdr nums) lower upper)
        (cons (car nums)
              (non-bounded-nums (cdr nums) lower upper)))
    nil))

(defun delete-by-position (lst current-index nums)
  (declare (xargs :guard (and (true-listp nums)
                              (integerp current-index))))
  (if (consp lst)
      (if (member current-index nums)
          (delete-by-position (cdr lst) (1+ current-index) nums)
        (cons (car lst)
              (delete-by-position (cdr lst) (1+ current-index) nums)))
    nil))

(define-pc-primitive drop (&rest nums)
  (if nums
      (let ((bad-nums (non-bounded-nums nums 1 (length hyps))))
        (if bad-nums
            (print-no-change2 "The following are not in-range hypothesis numbers:  ~&0."
                              (list (cons #\0 bad-nums)))
          (mv (change-pc-state
               pc-state
               :goals
               (cons (change goal (car goals)
                             :hyps (delete-by-position hyps 1 nums))
                     (cdr goals)))
              state)))
    (if hyps
        (mv (change-pc-state
             pc-state
             :goals
             (cons (change goal (car goals)
                           :hyps nil)
                   (cdr goals)))
            state)
      (print-no-change2 "There are no hypotheses to drop!"))))

(define-pc-meta lisp (form)
  (cond ((not (f-get-global 'in-verify-flg state))
         (er soft 'acl2-pc::lisp
             "You may only invoke the proof-builder LISP command when ~
              you are inside the interactive loop."))
        ((and (symbolp form)
              (or (eq form t)
                  (eq form nil)
                  (keywordp form)))
         (value form))
        (t
         (mv-let (erp stobjs-out/vals state)

; If a user stobj changes when running this command, should we issue a warning?
; We take the position that this is much like calling some flavor of trans-eval
; directly, since an arbitrary form is evaluated.  But which flavor?  The
; user-stobjs-modified warnings are heuristic in nature, so we choose to avoid
; them here if we are under an LD call that avoids them, since we expect that
; the preponderance of proof-checker invocations of the :lisp command will be
; at the top level inside a verify call.

                 (trans-eval-default-warning form :lisp state t)
                 (let ((stobjs-out (car stobjs-out/vals))
                       (vals (cdr stobjs-out/vals)))
                 (if (equal stobjs-out *error-triple-sig*)
                     (mv (or erp (car vals)) (cadr vals) state)
                   (mv erp vals state)))))))

(define-pc-primitive fail-primitive ()
  (declare (ignore pc-state))
  (mv nil state))

(define-pc-macro fail (&optional hard)
  (if hard
      (value '(lisp (mv hard nil state)))
    (value 'fail-primitive)))

(define-pc-macro illegal (instr)
  (pprogn (print-no-change "Illegal interactive instruction, ~x0.~%  An instruction must be a ~
                            symbol or a proper list headed by a symbol."
                           (list (cons #\0 instr)))
          (value :fail)))

(defun chk-assumption-free-ttree-1 (ttree ctx)

  ;; Same as chk-assumption-free-ttree, but returns a value.

  (cond ((tagged-objectsp 'assumption ttree)
         (er hard ctx
             "The 'assumption ~x0 was found in the final ttree!"
             (car (tagged-objects 'assumption ttree))))
        ((tagged-objectsp 'fc-derivation ttree)
         (er hard ctx
             "The 'fc-derivation ~x0 was found in the final ttree!"
             (car (tagged-objects 'fc-derivation ttree))))
        (t t)))

(defun put-cdr-assoc-query-id (id val alist)
  (cond ((atom alist) (cons (cons id val) alist))
        ((eq id (caar alist)) (cons (cons id val) (cdr alist)))
        (t (cons (car alist)
                 (put-cdr-assoc-query-id id val (cdr alist))))))

(defun set-query-val (id val state)
  ;; If val is 'toggle, then a NIL default is changed to T and every
  ;; other default is changed to NIL.  Otherwise, VAL is the new default.
  (let ((alist (ld-query-control-alist state)))
    (set-ld-query-control-alist
     (put-cdr-assoc-query-id
      id
      (if (eq val 'toggle)
          (not (cdr-assoc-query-id id alist))
        val)
      alist)
     state)))

(defmacro query-on-exit (&optional (val 'toggle))
  `(set-query-val 'acl2-pc::exit ',val state))

(defun replay-query (state)
  ;; Returns a state-stack, T or NIL.  A T value means we should replay instructions
  ;; in order to create the state-stack.  A value of NIL means that we should exit
  ;; without creating the event (by making the state-stack nil).
  ;;    In fact, the only time we return other than the current
  ;; state-stack is if we're inside verify and
  ;; either the query flag is off or the response is other than "Y".
  (acl2-query 'acl2-pc::exit
              '("~%Do you want to submit this event?  Possible replies are:~%~
                         Y (Yes), R (yes and Replay commands), N (No, but exit), A (Abort exiting).~|~ "
                :y :y :r :r :n :n :a :a)
              nil state))

(define-pc-meta exit (&optional event-name rule-classes do-it-flg)

; We allow (exit .. nil ..) to indicate that information is to be picked up
; from the initial pc-state.

  (if (not (f-get-global 'in-verify-flg state))
      (er soft 'acl2-pc::exit
          "You may not invoke the EXIT command unless inside the ~
           interactive loop.")
    (if args ; so it's not just a command to exit
        (let* ((event-name-and-types-and-raw-term
                (event-name-and-types-and-raw-term state-stack))
               (event-name
                (or event-name
                    (car event-name-and-types-and-raw-term)))
               (instructions (instructions-of-state-stack state-stack nil)))
          (er-let* ((event-name
                     (if event-name
                         (value event-name)
                       (pprogn (io? proof-builder nil state
                                    nil
                                    (fms0 "Please supply an event name (or :A to ~
                                   abort)~%>> "))
                               (with-infixp-nil
                                (read-object *standard-oi* state))))))
            (if (eq event-name :a)
                (pprogn (io? proof-builder nil state
                             nil
                             (fms0 "~|Exit aborted.~%"))
                        (mv nil nil state))
              (if (null (goals t))
                  (let* ((rule-classes (if (consp (cdr args))
                                           rule-classes
                                         (if (and (consp args)
                                                  (eq (car args) nil))
                                             (cadr event-name-and-types-and-raw-term)
                                           '(:rewrite))))
                         (event-form `(defthm ,event-name
                                        ,(caddr event-name-and-types-and-raw-term)
                                        ,@(if (equal rule-classes '(:rewrite))
                                              nil
                                            (list :rule-classes rule-classes))
                                        :instructions ,instructions)))
                    (mv-let (erp stobjs-out/vals state)
                            (pprogn
                             (print-pc-defthm event-form state)
                             (mv-let (erp ans state)
                                     (cond (do-it-flg (value :y))
                                           ((eq event-name t) (value :n))
                                           (t (replay-query state)))
                                     (declare (ignore erp))
                                     (case ans
                                       (:y (trans-eval-default-warning
                                            event-form
                                            'acl2-pc::exit
                                            state
                                            t))
                                       (:r (pprogn (state-from-instructions
                                                    (caddr event-form)
                                                    event-name
                                                    rule-classes
                                                    instructions
                                                    '(signal value)
                                                    state)
                                                   (trans-eval-default-warning
                                                    event-form
                                                    'acl2-pc::exit
                                                    state
                                                    t)))
                                       (:a (mv t '(nil . t) state))
                                       (otherwise (mv t '(nil . nil) state)))))

; We assume here that if DEFTHM returns without error, then it succeeds.

                            (if (or erp (null (car stobjs-out/vals)))
                                (if (eq (cdr stobjs-out/vals) t)
                                    (pprogn (io? proof-builder nil state
                                                 nil
                                                 (fms0 "~|Exit aborted.~%"))
                                            (mv nil nil state))
                                  (mv *pc-complete-signal* nil state))
                              (mv *pc-complete-signal* event-name state))))

; Otherwise, we have an incomplete proof.

                (pprogn (io? proof-builder nil state
                             (instructions event-name-and-types-and-raw-term
                                           state-stack)
                             (fms0 "~%Not exiting, as there remain unproved ~
                                   goals:  ~&0.~%The original goal is:~%~ ~ ~ ~
                                   ~ ~y1~|  Here is the current instruction ~
                                   list, starting with the first:~%~ ~ ~ ~ ~
                                   ~y2~|"
                                   (list (cons #\0 (goal-names (goals t)))
                                         (cons #\1 (caddr event-name-and-types-and-raw-term))
                                         (cons #\2 instructions))))
                        (mv nil nil state))))))
      (pprogn (io? proof-builder nil state
                   nil
                   (fms0 "~|Exiting....~%"))
              (mv *pc-complete-signal* nil state)))))

(define-pc-meta undo (&optional n)
  (if (and args
           (not (and (integerp n)
                     (< 0 n))))
      (pprogn (print-no-change
               "The optional argument to undo must be a positive integer.")
              (mv nil nil state))
    (let ((m (min (or n 1) (1- (length state-stack)))))
      (if (null (cdr state-stack))
          (pprogn (print-no-change "Already at the start.")
                  (mv nil nil state))
        (pprogn (pc-assign old-ss state-stack)
                (io? proof-builder nil state
                     (state-stack m)
                     (fms0 "~|Undoing:  ~y0~|"
                           (list (cons #\0
                                       (access pc-state
                                               (car (nthcdr (1- m) state-stack))
                                               :instruction)))))
                (pc-assign state-stack
                           (nthcdr m state-stack))
                (if (consp (cdr (state-stack)))
                    state
                  (io? proof-builder nil state
                       nil
                       (fms0 "Back to the start.~%")))
                (mv nil t state))))))

(define-pc-meta restore ()
  (let ((old-ss (pc-value old-ss)))
    (if (null old-ss)
        (pprogn (io? proof-builder nil state
                     nil
                     (fms0 "~%Nothing to restore from!~%"))
                (mv nil nil state))
      (let ((saved-ss state-stack))
        (pprogn (pc-assign state-stack old-ss)
                (pc-assign old-ss saved-ss)
                (mv nil t state))))))

(defun print-commands (indexed-instrs state)
  (if (null indexed-instrs)
      state
    (if (null (caar indexed-instrs))
        (io? proof-builder nil state
             (indexed-instrs)
             (fms0 (car (cdar indexed-instrs))
                   (cdr (cdar indexed-instrs))))
      (pprogn (io? proof-builder nil state
                   (indexed-instrs)
                   (fms0 "~|~x0. ~y1~|"
                         (list (cons #\0 (caar indexed-instrs))
                               (cons #\1 (cdar indexed-instrs)))))
              (print-commands (cdr indexed-instrs) state)))))

(defun make-pretty-start-instr (state-stack)
  (let* ((triple (event-name-and-types-and-raw-term state-stack))
         (name (car triple))
         (types (cadr triple)))
    (if name
        (list "~|[started with (~x0 ~x1 ...)]~%"
              (cons #\0 name)
              (cons #\1 types))
      (list "~|<< no event name specified at start >>~%"))))

(defun raw-indexed-instrs (start-index finish-index state-stack)
  (declare (xargs :guard (and (integerp start-index)
                              (integerp finish-index)
                              (<= start-index finish-index)
                              (true-listp state-stack)
                              ;; It's tempting to add the following guard, but
                              ;; since state-stack keeps shrinking, it can get violated
                              ;; on recursive calls.
                              ;; (<= finish-index (length state-stack))
                              )))
  (if (< start-index finish-index)
      (cons (cons start-index (access pc-state (car state-stack) :instruction))
            (raw-indexed-instrs (1+ start-index) finish-index (cdr state-stack)))
    (if (cdr state-stack)
        (list (cons start-index (access pc-state (car state-stack) :instruction)))
      (list (cons nil (make-pretty-start-instr state-stack))))))

(define-pc-macro sequence-no-restore (instr-list)
  (value `(sequence ,instr-list nil nil nil nil t)))

(define-pc-macro skip ()
  (value '(sequence-no-restore nil)))

(defmacro define-pc-help (name args &rest body)
  `(define-pc-macro ,name ,args ,@(butlast body 1)
     (pprogn ,(car (last body))
             (value 'skip))))

(defun evisc-indexed-instrs-1 (name rev-indexed-instrs)
  (if (consp rev-indexed-instrs)
      (let ((instr (cdr (car rev-indexed-instrs))))
        (case-match instr
                    ((comm ':end x . &)
                     (if (and (eq comm (make-pretty-pc-command :comment))
                              (equal x name))
                         rev-indexed-instrs
                       (evisc-indexed-instrs-1 name (cdr rev-indexed-instrs))))
                    (& (evisc-indexed-instrs-1 name (cdr rev-indexed-instrs)))))
    nil))

(defun evisc-indexed-instrs-rec (rev-indexed-instrs)
  (if (consp rev-indexed-instrs)
      (let ((instr (cdr (car rev-indexed-instrs)))
            (evisc-cdr (evisc-indexed-instrs-rec (cdr rev-indexed-instrs))))
        (case-match instr
                    ((comm ':begin name . &)
                     (if (eq comm (make-pretty-pc-command :comment))
                         (let ((rst (evisc-indexed-instrs-1 name evisc-cdr)))
                           (if rst
                               (cons (cons (car (car rev-indexed-instrs))
                                           (cons "***HIDING***" instr))
                                     (cdr rst))
                             (cons (car rev-indexed-instrs)
                                   evisc-cdr)))
                       (cons (car rev-indexed-instrs)
                             evisc-cdr)))
                    (& (cons (car rev-indexed-instrs)
                             evisc-cdr))))
    nil))

(defun mark-unfinished-instrs (indexed-instrs)
  ;; any "begin" in here was not matched with an "end"
  (if (consp indexed-instrs)
      (let ((instr (cdr (car indexed-instrs))))
        (case-match instr
                    ((comm ':begin & . &)
                     (if (eq comm (make-pretty-pc-command :comment))
                         (cons (cons (car (car indexed-instrs))
                                     (cons "***UNFINISHED***" instr))
                               (mark-unfinished-instrs (cdr indexed-instrs)))
                       (cons (car indexed-instrs)
                             (mark-unfinished-instrs (cdr indexed-instrs)))))
                    (& (cons (car indexed-instrs)
                             (mark-unfinished-instrs (cdr indexed-instrs))))))
    nil))

(defun evisc-indexed-instrs (indexed-instrs)
  ;; for now, returns a new state stack in which we drop bookends
  ;; (comment (begin <name>) ...)
  ;; (comment (end <name>) ...)
  (mark-unfinished-instrs (reverse (evisc-indexed-instrs-rec (reverse indexed-instrs)))))

(define-pc-help commands (&optional n evisc-p)
  (if (and n (not (and (integerp n) (> n 0))))
      (io? proof-builder nil state
           (n)
           (fms0 "*** The first optional argument to the COMMANDS command must ~
                  be a positive integer, but ~x0 is not.~|"
                 (list (cons #\0 n))))
    (let* ((indexed-instrs (raw-indexed-instrs 1
                                               (if n
                                                   (min n (length state-stack))
                                                 (length state-stack))
                                               state-stack)))
      (print-commands (if evisc-p (evisc-indexed-instrs indexed-instrs) indexed-instrs)
                      state))))

(define-pc-macro comm (&optional n)
  (value (list 'commands n t)))

(defun promote-guts (pc-state goals hyps x y no-flatten-flg)
  (change-pc-state
   pc-state
   :goals
   (cons (change goal (car goals)
                 :hyps (append hyps
                               (if no-flatten-flg
                                   (list x)
                                 (flatten-ands-in-lit x)))
                 :conc y)
         (cdr goals))))

(define-pc-primitive promote (&optional do-not-flatten-flag)
  (if current-addr
      (print-no-change2 "You must be at the top ~
                         of the goal in order to promote the ~
                         antecedents of an implication. Try TOP first.")
    (case-match conc
                (('implies x y)
                 (mv (promote-guts pc-state goals hyps x y do-not-flatten-flag) state))
                (('if x y *t*)
                 (mv (promote-guts pc-state goals hyps x y do-not-flatten-flag) state))
                (& (print-no-change2 "The goal must be of the form ~x0 or ~x1."
                                     (list (cons #\0 '(IMPLIES P Q))
                                           (cons #\1 '(IF P Q T))))))))

(defun remove-by-indices (m indices lst)
  ;;  (declare (xargs :guard (null (non-bounded-nums indices m (length lst)))))
  ;; this was ok for the original entry, but it's not preserved
  (if (consp lst)
      (if (member-equal m indices)
          (remove-by-indices (1+ m) indices (cdr lst))
        (cons (car lst) (remove-by-indices (1+ m) indices (cdr lst))))
    nil))

;;; **** Should improve the following so that if form outputs a state or
;;; does return just one result, then fms0 isn't even called but instead
;;; an appropriate error message is printed.
(define-pc-macro print (form &optional without-evisc)

; NOTE: The saved-output mechanism described in the Essay on Saved-output won't
; work here, because there is no call of io?.  We can't call io? because form
; is arbitrary and hence we cannot check its variables.

  (let ((print-form `(fms0 "~|~y0~|" (list (cons #\0 ,form)))))
    (value `(lisp ,(if without-evisc
                       `(without-evisc ,print-form)
                     print-form)))))

(defun bounded-integer-listp (i j lst)
  ;; If i is a non-integer, then it's -infinity.
  ;; If j is a non-integer, then it's +infinity.
  (if (consp lst)
      (and (integerp (car lst))
           (if (integerp i)
               (if (integerp j)
                   (and (<= i (car lst))
                        (<= (car lst) j))
                 (<= i (car lst)))
             (<= (car lst) j)))
    (null lst)))

(defun fetch-term-and-cl (term addr cl)
  ;; Returns the subterm of TERM at address ADDR paired with a list
  ;; containing the tests governing that occurrence of the subterm plus
  ;; the literals of the input CL.  However, if CL is T then we simply
  ;; return (mv nil t) (see also below).
  ;; I've assumed that the address is a list of positive integers.  If
  ;; the address is not valid for diving into TERM according to ADDR,
  ;; then we return (mv nil t).  Notice that ADDR is expected to be in
  ;; the correct order, while CL is in reverse order and the extension
  ;; of CL returned in the second position is also in reverse order.
  ;; For the funny contrapositive subcase of IMPLIES, note that
  ;;    (implies (implies (and u (not x)) (equal y1 y2))
  ;;             (implies u (equal (implies y1 x) (implies y2 x))))
  ;; is a tautology.  However, the corresponding fact does not hold in
  ;; general for IF; it depends on x being boolean.
  (declare (xargs :guard (bounded-integer-listp 1 'infinity addr)))
  (cond ((eq cl t)
         (mv nil t))
        ((null addr)
         (mv term cl))
        ((or (variablep term) (fquotep term))
         ;; can't dive any further
         (mv nil t))
        ((and (integerp (car addr))
              (< 0 (car addr))
              (< (car addr) (length term)))
         (case-match term
                     (('if t1 t2 t3)
                      (cond ((= 1 (car addr))
                             (fetch-term-and-cl t1 (cdr addr) cl))
                            ((= 2 (car addr))
                             (fetch-term-and-cl t2 (cdr addr) (cons t1 cl)))
                            (t (fetch-term-and-cl t3 (cdr addr) (cons (dumb-negate-lit t1) cl)))))
                     (('implies t1 t2)
                      (cond ((= 1 (car addr))
                             (fetch-term-and-cl t1 (cdr addr) (cons (dumb-negate-lit t2) cl)))
                            (t
                             (fetch-term-and-cl t2 (cdr addr) (cons t1 cl)))))
                     (& (fetch-term-and-cl (nth (1- (car addr)) (fargs term)) (cdr addr) cl))))
        (t
         (mv nil t))))

(defun fetch-term (term addr)
  ;; causes hard error when appropriate
  (mv-let (term cl)
          (fetch-term-and-cl term addr nil)
          (if (eq cl t)
              (er hard 'fetch-term
                  "FETCH-TERM-AND-CL did not find a subterm of ~x0 at address ~x1."
                  term addr)
            term)))

(defun governors (term addr)
  (mv-let (term cl)
          (fetch-term-and-cl term addr nil)
          (declare (ignore term))
          ;; note that cl could be T rather than a list of governors
          cl))

;;;;;;!!!!!!! I should generalize the following to arbitrary equivalence stuff.
(defun term-id-iff (term address iff-flg)
  ;; The property we want is that if one substitutes an equivalent subterm
  ;; of TERM at the given address (equivalent modulo the flag returned by
  ;; this function, that is), then the resulting term is equivalent modulo
  ;; the IFF-FLG argument to the original TERM.  We assume that address is
  ;; a valid address for term.  (*** This should really be a guard.)
  (if (null address)
      iff-flg
    ;; so, the term is a function application
    (term-id-iff (nth (car address) term)
                 (cdr address)
                 (cond ((eq (ffn-symb term) (quote if))
                        (if (= (car address) 1)
                            t
                          iff-flg))
                       ((member-eq (ffn-symb term) (quote (implies iff not)))
                        t)
                       (t
                        nil)))))

;; The way abbreviations will work is as follows.  For input, an
;; abbreviation variable is to be thought of as a placeholder for
;; literal substitution (*before* translation!).  It was tempting to
;; think of abbreviation variables as standing for something else only
;; when they're in variable position, but the problem with that
;; approach is that we can't tell about the position until we've done
;; the translation (consider macro calls that look at the first
;; character, say, for example).  On a pragmatic (implementation)
;; level, it's hard to see how to implement a translator that
;; substitutes for abbreviation variables only when they're in
;; variable position, except by modifying translate.  On the other
;; hand, for untranslation the specification is only that
;; (trans (untrans x)) = x, where here translation is with respect
;; to abbreviations.  Notice though that this spec messes things
;; up, because if x is (quote &v) then untrans of that is still
;; (quote &v) but then trans would remove the &v, if we use sublis
;; to deal with abbreviations.

;; So, I think I'll implement abbreviations as follows.  There will
;; be a new "macro":

;; (defmacro ? (x)
;;   (cdr (assoc-eq x (abbreviations))))

;; Notice however that (abbreviations) generates a reference to
;; state, which isn't compatible with ? being a macro.  So, I'll
;; stub it out:

(defmacro ? (x)
  `(?-fn ',x))

(defstub ?-fn (x)
  t)

;; Now, translation will be followed by an appropriate substitution.
;; For convenience, abbreviations will be turned into an alist whose
;; pairs are of the form ((&-fn 'var) . term).

(defun abbreviations-alist (abbreviations)
  (if (consp abbreviations)
      (cons (cons (fcons-term* '?-fn (kwote (caar abbreviations)))
                  (cdar abbreviations))
            (abbreviations-alist (cdr abbreviations)))
    nil))

(mutual-recursion

(defun chk-?s (term ctx state)
  ;; There shouldn't be any ?-fns in term.
  (cond
   ((or (variablep term) (fquotep term))
    (value nil))
   ((eq (ffn-symb term) '?-fn)
    (case-match term
                ((& ('quote var))
                 (if (variablep var)
                     (er soft ctx "The variable ~x0 is not among the current abbreviations."
                         var)
                   (er soft ctx "Expected a variable in place of ~x0."
                       var)))
                (& (value (er hard ctx "Bad call of ?-FN, ~x0.  ?-FN must be called on the quotation of ~
                                        a variable."
                              term)))))
   ((flambdap (ffn-symb term))
    (er-progn (chk-?s (lambda-body (ffn-symb term)) ctx state)
              (chk-?s-lst (fargs term) ctx state)))
   (t (chk-?s-lst (fargs term) ctx state))))

(defun chk-?s-lst (term-lst ctx state)
  (if (consp term-lst)
      (er-progn (chk-?s (car term-lst) ctx state)
                (chk-?s-lst (cdr term-lst) ctx state))
    (value nil)))

)

(defun remove-?s (term abbreviations-alist ctx state)
  (let ((newterm (sublis-expr abbreviations-alist term)))
    (er-progn (chk-?s newterm ctx state)
              (value newterm))))

(defun translate-abb (x abbreviations ctx state)
  (mv-let
   (erp term state)
   (translate x t

; Since we only use this function in a logical context, we set
; logic-modep to t.

              t t ctx (w state) state)
   (if erp
       (mv erp term state)
     (remove-?s term (abbreviations-alist abbreviations) ctx state))))

(defmacro trans0 (x &optional abbreviations ctx)
  `(translate-abb ,x ,abbreviations ,(or ctx ''trans0) state))

(defun p-body (conc current-addr abbreviations state)
  (io? proof-builder nil state
       (abbreviations current-addr conc)
       (fms0 "~|~y0~|"
             (list (cons #\0 (untrans0 (fetch-term conc current-addr)
                                       (term-id-iff conc current-addr t)
                                       abbreviations))))))

(define-pc-help p ()
  (when-goals
   (p-body (conc t) (current-addr t) (abbreviations t) state)))

(define-pc-help pp ()
  (when-goals
   (io? proof-builder nil state
        (state-stack)
        (fms0 "~|~y0~|"
              (list (cons #\0 (fetch-term (conc t) (current-addr t))))))))

(defun take-by-indices (m indices lst)
  ;;  (declare (xargs :guard (null (non-bounded-nums indices m (length lst)))))
  ;; this was ok for the original entry, but it's not preserved
  (if (consp lst)
      (if (member-equal m indices)
          (cons (car lst) (take-by-indices (1+ m) indices (cdr lst)))
        (take-by-indices (1+ m) indices (cdr lst)))
    nil))

(defun print-hyps (indexed-hyps ndigits abbreviations state)
  (declare (xargs :guard (and (eqlable-alistp indexed-hyps)
                              (integerp ndigits)
                              (> ndigits 0))))
  (if (null indexed-hyps)
      state
    (pprogn (io? proof-builder nil state
                 (abbreviations ndigits indexed-hyps)
                 (fms0 "~c0. ~y1~|"
                       (list (cons #\0 (cons (caar indexed-hyps) ndigits))
                             (cons #\1 (untrans0 (cdar indexed-hyps) t abbreviations)))))
            (print-hyps (cdr indexed-hyps) ndigits abbreviations state))))

(defun some-> (lst n)
  ;; says whether some element of lst exceeds n
  (declare (xargs :guard (and (rational-listp lst)
                              (rationalp n))))
  (if lst
      (or (> (car lst) n)
          (some-> (cdr lst) n))
    nil))

(defun print-hyps-top (indexed-hyps abbreviations state)
  (declare (xargs :guard (eqlable-alistp indexed-hyps)))
  (if (null indexed-hyps)
      (io? proof-builder nil state
           nil
           (fms0 "~|There are no top-level hypotheses.~|"))
    (print-hyps indexed-hyps (if (some-> (strip-cars indexed-hyps) 9) 2 1)
                abbreviations state)))

(defun print-governors-top (indexed-hyps abbreviations state)
  (declare (xargs :guard (eqlable-alistp indexed-hyps)))
  (if (null indexed-hyps)
      (io? proof-builder nil state
           nil
           (fms0 "~|There are no governors.~|"))
    (print-hyps indexed-hyps (if (some-> (strip-cars indexed-hyps) 9) 2 1)
                abbreviations state)))

(defun pair-indices (seed indices lst)
  ;; Returns a list of indices paired with the corresponding (1-based) element of
  ;; lst when in range.  Seed is a starting integer; we do things this way
  ;; because we want the result sorted (and hence want to recurse on lst).
  (declare (xargs :guard (and (integerp seed)
                              (true-listp lst)
                              (bounded-integer-listp 1 (length lst) indices))))
  (if lst
      (let ((rest-lst
             (pair-indices (1+ seed) indices (cdr lst))))
        (if (member seed indices)
            (cons (cons seed (car lst))
                  rest-lst)
          rest-lst))
    nil))

(define-pc-macro hyps (&optional hyps-indices govs-indices)
  (when-goals-trip
   (let* ((hyps (hyps t))
          (len-hyps (length hyps))
          (govs (and govs-indices;; for efficiency
                     (governors (conc t) (current-addr t))))
          (len-govs (length govs))
          (abbs (abbreviations t))
          (hyps-indices (or hyps-indices
                            (null args))))
     (cond
      ((not (or (eq hyps-indices t) (bounded-integer-listp 1 len-hyps hyps-indices)))
       (pprogn
        (io? proof-builder nil state
             (len-hyps hyps-indices)
             (fms0 "~|Bad hypothesis-list argument to HYPS, ~X0n.  The ~
                    hypothesis-list argument should either be T or should be a ~
                    list of integers between 1 and the number of top-level ~
                    hypotheses, ~x1.~%"
                   (list (cons #\0 hyps-indices)
                         (cons #\n nil)
                         (cons #\1 len-hyps))))
        (value :fail)))
      ((not (or (eq govs-indices t) (bounded-integer-listp 1 len-govs govs-indices)))
       (pprogn
        (io? proof-builder nil state
             (len-govs govs-indices)
             (fms0 "~|Bad governors-list argument to HYPS,~%  ~X0n.~%The ~
                    governors-list argument should either be T or should be a ~
                    list of integers between 1 and the number of top-level ~
                    governors, ~x1."
                   (list (cons #\0 govs-indices)
                         (cons #\n nil)
                         (cons #\1 len-govs))))
        (value :fail)))
      ((and (null hyps-indices) (null govs-indices))
       (pprogn
        (io? proof-builder nil state
             nil
             (fms0 "~|You have specified no printing of either hypotheses or ~
                    governors!  Perhaps you should read the documentation for ~
                    the HYPS command.~|"))
        (value :fail)))
      (t
       (let ((hyps-to-print
              (if (eq hyps-indices t)
                  (count-off 1 hyps)
                (pair-indices 1 hyps-indices hyps)))
             (govs-to-print
              (if (eq govs-indices t)
                  (count-off 1 govs)
                (pair-indices 1 govs-indices govs))))
         (pprogn
          (if hyps-indices
              (pprogn
               (if (eq hyps-indices t)
                   (io? proof-builder nil state
                        nil
                        (fms0 "~|*** Top-level hypotheses:~|"))
                 (io? proof-builder nil state
                      nil
                      (fms0 "~|*** Specified top-level hypotheses:~|")))
               (print-hyps-top hyps-to-print abbs state))
            state)
          (if govs-indices
              (pprogn
               (if (eq govs-indices t)
                   (io? proof-builder nil state
                        nil
                        (fms0 "~|~%*** Governors:~|"))
                 (io? proof-builder nil state
                      nil
                      (fms0 "~|~%*** Specified governors:~|")))
               (print-governors-top govs-to-print abbs state))
            state)
          (value 'skip))))))))

(define-pc-primitive demote (&rest rest-args)
  (cond
   (current-addr
    (print-no-change2 "You must be at the top of the conclusion in order to ~
                       demote hypotheses. Try TOP first."))
   ((null hyps)
    (print-no-change2 "There are no top-level hypotheses."))
   (t
    (let ((badindices (non-bounded-nums rest-args 1 (length hyps))))
      (if badindices
          (print-no-change2 "The arguments to DEMOTE ~
                             must be indices of active top-level hypotheses, ~
                             but the following are not:  ~&0."
                            (list (cons #\0 badindices)))
        (mv (change-pc-state
             pc-state
             :goals
             (cons (change goal (car goals)
                           :hyps (if rest-args
                                     (remove-by-indices 1 rest-args hyps)
                                   nil)
                           :conc (make-implication
                                  (if rest-args
                                      (take-by-indices 1 rest-args hyps)
                                    hyps)
                                  conc))
                   (cdr goals)))
            state))))))

(defun pair-keywords (keywords lst)
  (declare (xargs :guard (and (keyword-listp keywords)
                              (keyword-value-listp lst))))
  ;; returns (mv alist rst)
  (if (consp keywords)
      (mv-let (alist rst)
              (pair-keywords (cdr keywords) lst)
              (let ((tail (assoc-keyword (car keywords) rst)))
                (if tail
                    (mv (cons (cons (car tail) (cadr tail)) alist)
                        ;; could use a remove1 version of the following, but who cares?
                        (remove-keyword (car keywords) rst))
                  (mv alist rst))))
    (mv nil lst)))

(defun null-pool (pool)
  (cond
   ((null pool) t)
   ((eq (access pool-element (car pool) :tag) 'being-proved-by-induction)
    (null-pool (cdr pool)))
   (t nil)))

(defun initial-pspv (term displayed-goal otf-flg ens wrld state splitter-output
                          orig-hints)

; This is close to being equivalent to a call (make-pspv ...).  However, the
; splitter-output is supplied as a parameter here.

  (change prove-spec-var *empty-prove-spec-var*
          :rewrite-constant
          (initial-rcnst-from-ens ens wrld state splitter-output)
          :user-supplied-term term
          :displayed-goal displayed-goal
          :otf-flg otf-flg
          :orig-hints orig-hints
          ))

(defun pc-prove (term displayed-goal hints otf-flg ens wrld ctx state)

; This is exactly the same as the ACL2 PROVE function, except that we allow
; :bye objects in the tag-tree, there is no checking of the load mode, and the
; warning above.

  (prog2$
   (initialize-brr-stack state)
   (er-let* ((ttree
              (let ((pspv (initial-pspv term displayed-goal otf-flg ens wrld
                                        state
                                        (splitter-output)
                                        hints))
                    (clauses (list (list term))))
                (if (f-get-global 'in-verify-flg state) ;interactive
                    (state-global-let*
                     ((saved-output-p t)
                      (saved-output-token-lst :all))
                     (pprogn (f-put-global 'saved-output-reversed nil state)
                             (push-current-acl2-world 'saved-output-reversed
                                                      state)
                             (prove-loop clauses pspv hints ens wrld ctx
                                         state)))
                  (prove-loop clauses pspv hints ens wrld ctx state)))))
            (er-progn
             (chk-assumption-free-ttree ttree ctx state)
             (value ttree)))))

(defun sublis-equal (alist tree)
  (declare (xargs :guard (alistp alist)))
  (let ((pair (assoc-equal tree alist)))
    (if pair
        (cdr pair)
      (if (atom tree)
          tree
        (cons (sublis-equal alist (car tree))
              (sublis-equal alist (cdr tree)))))))

(defun abbreviations-alist-? (abbreviations)
  ;; Same as abbreviations-alist, except that we assume that we
  ;; haven't translated yet, and hence we use ? instead of ?-fn
  ;; and we don't quote the variable.
  (if (consp abbreviations)
      (cons (cons (fcons-term* '? (caar abbreviations))
                  (cdar abbreviations))
            (abbreviations-alist-? (cdr abbreviations)))
    nil))

(defun find-?-fn (x)
  ;; x is not necessarily a term.  Heuristically though it's useful
  ;; to be able to find all (?-fn var) subexpressions of x.
  (if (atom x)
      nil
    (if (eq (car x) '?-fn)
        (list (cadr x))
      (union-equal (find-?-fn (car x))
                   (find-?-fn (cdr x))))))

(defun unproved-pc-prove-clauses (ttree)
  (reverse-strip-cdrs (tagged-objects :bye ttree) nil))

(defun prover-call (comm term-to-prove rest-args pc-state state)
  ;; We assume that the :otf-flg and :hints "hints" are locally inside
  ;; a variable called rest-args, which in fact are the arguments to the
  ;; instruction being processed.
  ;; Returns an error triple (mv erp-flg ttree state).
  (declare (xargs :guard (keywordp comm)))
  (let ((prover-call-abbreviations (access pc-state pc-state :abbreviations))
        (prover-call-wrld (w state)))
    (let ((prover-call-pc-ens (make-pc-ens (access pc-state pc-state :pc-ens)
                                           state)))
      (mv-let (prover-call-pairs prover-call-tail)
              (pair-keywords '(:otf-flg :hints) rest-args)
              (if prover-call-tail
                  (pprogn
                   (print-no-change
                    "The only keywords allowed in the arguments to the ~x0 command ~
                     are :otf-flg and :hints.  Your ~
                     instruction ~x1 violates this requirement."
                    (list (cons #\0 comm)
                          (cons #\1
                                (make-pretty-pc-instr (cons comm rest-args)))))
                   (mv t nil state))
                (mv-let (prover-call-erp prover-call-hints state)
                        (let ((un-?-hints
                               (sublis-equal
                                ;; *** someday I should do this all right
                                (abbreviations-alist-? prover-call-abbreviations)
                                (cdr (assoc-eq :hints prover-call-pairs)))))
                          (let ((?-exprs (find-?-fn un-?-hints)))
                            (if ?-exprs
                                (pprogn
                                 (print-no-change
                                  "You appear to have attempted to use the following ~
                                   abbreviation variable~#0~[~/~/s~], which however ~
                                   ~#0~[~/is~/are~] not among ~
                                   the current abbreviation variables (see SHOW-ABBREVIATIONS):  ~&1."
                                  (list (cons #\0 (zero-one-or-more (length ?-exprs)))
                                        (cons #\1 ?-exprs)))
                                 (mv t nil state))
                              (pprogn
                               (io? proof-builder nil state
                                    nil
                                    (fms0 "~|***** Now entering the theorem ~
                                           prover *****~|"))
                               (translate-hints+
                                'proof-builder
                                un-?-hints
                                (default-hints prover-call-wrld)
                                comm
                                prover-call-wrld
                                state)))))
                        (if prover-call-erp
                            (pprogn (print-no-change
                                     "Failed to translate hints successfully.")
                                    (mv t nil state))
                          (let ((prover-call-otf-flg (cdr (assoc-eq :otf-flg prover-call-pairs))))
                            (mv-let (prover-call-erp prover-call-ttree state)
                                    (pc-prove
                                     term-to-prove
                                     (untranslate term-to-prove t prover-call-wrld)
                                     prover-call-hints prover-call-otf-flg
                                     prover-call-pc-ens
                                     prover-call-wrld
                                     comm state)
                                    (pprogn (io? proof-builder nil state
                                                 nil
                                                 (fms0 "~%"))
                                            (if prover-call-erp
                                                (pprogn (print-no-change "Proof failed.")
                                                        (mv t nil state))
                                              (mv nil prover-call-ttree
                                                  state))))))))))))

(defun make-new-goals (cl-set goal-name start-index)
  ;; assumes that every member of CL-SET is a non-empty true list (should be a guard)
  (if (consp cl-set)
      (cons (make goal
                  :conc (car (last (car cl-set)))
                  :hyps (dumb-negate-lit-lst (butlast (car cl-set) 1))
                  :current-addr nil
                  :goal-name (cons goal-name start-index)
                  :depends-on 1)
            (make-new-goals (cdr cl-set) goal-name (1+ start-index)))
    nil))

(defun same-goal (goal1 goal2)
  (and (equal (access goal goal1 :hyps)
              (access goal goal2 :hyps))
       (equal (access goal goal1 :conc)
              (access goal goal2 :conc))))

(defun remove-byes-from-tag-tree (ttree)
  (remove-tag-from-tag-tree :bye ttree))

(define-pc-primitive prove (&rest rest-args)
  (cond
   (current-addr
    (print-no-change2 "The PROVE command should only be used at ~
                       the top.  Use (= T) if that is what you want."))
   ((not (keyword-value-listp rest-args))
    (print-no-change2 "The argument list for the PROVE command should ~
                       be empty or a list of even length with keywords in the odd ~
                       positions.  See the documentation for examples and details."))
   (t
    (mv-let
     (erp ttree state)
     (prover-call
      :prove (make-implication hyps conc) rest-args pc-state state)
     (cond
      (erp (mv nil state))
      (t
       (let* ((new-clauses
               (unproved-pc-prove-clauses ttree))
              (new-goals
               (make-new-goals new-clauses goal-name depends-on))
              (len-new-goals (length new-goals)))
         (cond
          ((and (equal len-new-goals 1)
                (same-goal (car new-goals)
                           (car goals)))
           (print-no-change2 "Exactly one new goal was created by your PROVE ~
                              command, and it has exactly the same hypotheses ~
                              and conclusion as did the current goal."))
          ((tagged-objects 'assumption ttree)

; See the comment in define-pc-primitive about leaving the top goal on the top
; of the :goals stack.

           (mv (change-pc-state
                pc-state
                :goals
                (cons (change goal (car goals)
                              :conc *t*
                              :depends-on (+ (access goal (car goals)
                                                     :depends-on)
                                             len-new-goals))
                      (append new-goals (cdr goals)))
                :local-tag-tree
                (remove-byes-from-tag-tree ttree))
               state))
          (t (mv (change-pc-state
                  pc-state
                  :goals
                  (append new-goals (cdr goals))
                  :local-tag-tree
                  (remove-byes-from-tag-tree ttree))
                 state))))))))))

(defun add-string-val-pair-to-string-val-alist-1 (key key1 val alist replace-p)

; Key is a string (typically a goal name) and key1 is a keyword (presumably a
; hint keyword).  Alist associates keys (strings) with keyword alists.
; Associate key1 with val in the keyword alist associated with key, unless key1
; is already bound in that keyword alist.  In that case, just return alist if
; replace-p is nil, else make the replacement.

  (cond ((null alist) (list (list key key1 val)))
        ((and (stringp (caar alist))
              (string-equal key (caar alist)))
         (if (assoc-keyword key1 (cdar alist))
             (if replace-p
                 (cons (list* (caar alist) key1 val
                              (remove-keyword key1 (cdar alist)))
                       (cdr alist))
               alist)
           (cons (list* (caar alist) key1 val (cdar alist))
                 (cdr alist))))
        (t (cons (car alist)
                 (add-string-val-pair-to-string-val-alist-1
                  key key1 val (cdr alist) replace-p)))))

(defun add-string-val-pair-to-string-val-alist (key key1 val alist)
  (add-string-val-pair-to-string-val-alist-1 key key1 val alist nil))

(defun add-string-val-pair-to-string-val-alist! (key key1 val alist)
  (add-string-val-pair-to-string-val-alist-1 key key1 val alist t))

(defconst *bash-skip-forcing-round-hints*
  '(("[1]Goal" :by nil)
    ("[1]Subgoal 1" :by nil)
    ("[1]Subgoal 2" :by nil)
    ("[1]Subgoal 3" :by nil)
    ("[1]Subgoal 4" :by nil)
    ("[1]Subgoal 5" :by nil)
    ("[1]Subgoal 6" :by nil)
    ("[1]Subgoal 7" :by nil)
    ("[1]Subgoal 8" :by nil)
    ("[1]Subgoal 9" :by nil)
    ("[1]Subgoal 10" :by nil)
    ("[1]Subgoal 11" :by nil)
    ("[1]Subgoal 12" :by nil)
    ("[1]Subgoal 13" :by nil)
    ("[1]Subgoal 14" :by nil)
    ("[1]Subgoal 15" :by nil)))

(define-pc-atomic-macro bash (&rest hints)
  (if (alistp hints)
      (value (list :prove :hints
                   (append
                    *bash-skip-forcing-round-hints*
                    (add-string-val-pair-to-string-val-alist
                     "Goal"
                     ;; only preprocess and simplify are allowed
                     :do-not
                     (list 'quote '(generalize eliminate-destructors
                                               fertilize
                                               eliminate-irrelevance))
                     (add-string-val-pair-to-string-val-alist!
                      "Goal"
                      :do-not-induct
                      'proof-builder
                      hints)))
                   :otf-flg t))
    (pprogn (print-no-change
             "A BASH instruction must be of the form~%~ ~ ~
              (:BASH (goal_name_1 ...) ... (goal_name_n ...)),~%and hence ~
              your instruction,~%~ ~ ~x0,~%is not legal."
             (list (cons #\0 (cons :bash hints))))
            (value :fail))))

(define-pc-primitive dive (n &rest rest-addr)
  (if (not (bounded-integer-listp 1 'infinity args))
      (print-no-change2 "The arguments to DIVE must all be positive integers.")
    (mv-let (subterm cl)
            (fetch-term-and-cl (fetch-term conc current-addr) args nil)
            (declare (ignore subterm))
            (if (eq cl t)
                (print-no-change2
                 "Unable to DIVE according to the address~%~ ~ ~y0."
                 (list (cons #\0 (cons n rest-addr))))
              (mv (change-pc-state pc-state
                                   :goals
                                   (cons (change goal (car goals)
                                                 :current-addr
                                                 (append (access goal (car goals) :current-addr)
                                                         args))
                                         (cdr goals)))
                  state)))))

; Keep this in sync with translate-in-theory-hint.

(define-pc-atomic-macro split ()
  (value '(:prove :hints
                  (("Goal"
                    :do-not-induct proof-builder
                    :do-not '(generalize eliminate-destructors
                                         fertilize eliminate-irrelevance)
                    :in-theory (theory 'minimal-theory))))))

(define-pc-primitive add-abbreviation (var &optional raw-term)
  (mv-let (erp term state)
          (if (cdr args)
              (trans0 raw-term abbreviations :add-abbreviation)
            (value (fetch-term conc current-addr)))
          (cond
           (erp (mv nil state))
           ((variablep var)
            (if (assoc-eq var abbreviations)
                (print-no-change2 "The abbreviation ~x0 has already been used, and stands for  ~x1."
                                  (list (cons #\0 var)
                                        (cons #\1 (untrans0 (cdr (assoc-eq var abbreviations))))))
              (mv (change-pc-state pc-state
                                   :abbreviations
                                   (cons (cons var term) abbreviations))
                  state)))
           (t
            (print-no-change2 "An abbreviation must be a variable, but ~x0 is not."
                              (list (cons #\0 var)))))))

(defun not-in-domain-eq (lst alist)
  (declare (xargs :guard (if (symbol-listp lst)
                             (alistp alist)
                           (symbol-alistp alist))))
  (if (consp lst)
      (if (assoc-eq (car lst) alist)
          (not-in-domain-eq (cdr lst) alist)
        (cons (car lst)
              (not-in-domain-eq (cdr lst) alist)))
    nil))

(define-pc-primitive remove-abbreviations (&rest vars)
  (if (null abbreviations)
      (print-no-change2 "There are currently no abbreviations.")
    (let ((badvars (and args (not-in-domain-eq vars abbreviations))))
      (if (and args badvars)
          (print-no-change2 "The variable~#0~[~/~/s~] ~&1 ~
                             ~#0~[~/is not currently an abbreviation variable~/~
                                    are not currently abbreviation variables~]."
                            (list (cons #\0 (zero-one-or-more (length badvars)))
                                  (cons #\1 badvars)))
        (mv (change-pc-state
             pc-state
             :abbreviations
             (if args
                 (remove1-assoc-eq-lst vars abbreviations)
               nil))
            state)))))

(defun print-abbreviations (vars abbreviations state)
  ;; Here abbreviations can contain junky pairs.
  (declare (xargs :guard (and (true-listp vars)
                              (symbol-alistp abbreviations))))
  (if (null vars)
      state
    (pprogn
     (io? proof-builder nil state
          nil
          (fms0 "~%"))
     (let ((pair (assoc-equal (car vars) abbreviations)))
       (if (null pair)
           ;; then this pair is junk
           (io? proof-builder nil state
                (vars)
                (fms0 "*** ~x0 does not abbreviate a term.~|"
                      (list (cons #\0 (car vars)))))
         (let ((untrans-1 (untrans0 (cdr pair)))
               (untrans-2 (untrans0 (cdr pair)
                                    nil
                                    (remove1-assoc-eq (car pair) abbreviations))))
           (pprogn
            (io? proof-builder nil state
                 (pair)
                 (fms0 "(? ~x0) is an abbreviation for:~%~ ~ "
                       (list (cons #\0 (car pair)))))
            (io? proof-builder nil state
                 (untrans-1)
                 (fms0 "~y0~|"
                       (list (cons #\0 untrans-1))
                       2))
            (if (equal untrans-1 untrans-2)
                state
              (pprogn
               (io? proof-builder nil state
                    nil
                    (fms0 "i.e. for~%~ ~ "))
               (io? proof-builder nil state
                    (untrans-2)
                    (fms0 "~y0~|"
                          (list (cons #\0 untrans-2))
                          2))))))))
     (print-abbreviations (cdr vars) abbreviations state))))

(define-pc-help show-abbreviations (&rest vars)
  (if (null (abbreviations t))
      (io? proof-builder nil state
           nil
           (fms0 "~|There are currently no abbreviations.~%"))
    (print-abbreviations (or vars (strip-cars (abbreviations t))) (abbreviations t) state)))

(defun drop-from-end (n l)
  (declare (xargs :guard (and (integerp n)
                              (not (< n 0))
                              (true-listp l)
                              (<= n (length l)))))
  (take (- (length l) n) l))

(define-pc-primitive up (&optional n)
  (let ((n (or n 1)))
    (cond ((null current-addr)
           (print-no-change2 "Already at the top."))
          ((not (and (integerp n) (> n 0)))
           (print-no-change2 "If UP is supplied with an argument, it must be ~
                              a positive integer or NIL, unlike ~x0."
                             (list (cons #\0 n))))
          ((<= n (length current-addr))
           (mv (change-pc-state pc-state
                                :goals
                                (cons (change goal (car goals)
                                              :current-addr
                                              (drop-from-end n current-addr))
                                      (cdr goals)))
               state))
          (t
           (print-no-change2 "Can only go up ~x0 level~#1~[~/~/s~]."
                             (list (cons #\0 (length current-addr))
                                   (cons #\1 (zero-one-or-more (length current-addr)))))))))

(define-pc-atomic-macro top ()
  (when-goals-trip
   (let ((current-addr (current-addr t)))
     (value (list :up (length current-addr))))))

(defmacro expand-address-recurse
  (&key (ans '(cons (car addr) rest-addr))
        (new-addr '(cdr addr))
        (new-raw-term '(nth (car addr) raw-term))
        (new-term '(nth (car addr) term))
        (new-iff-flg 'nil)
        (new-accumulated-addr-r '(cons (car addr) accumulated-addr-r)))
  `(mv-let (erp rest-addr)
           (expand-address
            ,new-addr ,new-raw-term ,new-term abbreviations ,new-iff-flg ,new-accumulated-addr-r
            wrld)
           (if erp
               (mv erp rest-addr)
             (mv nil ,ans))))

(defmacro dive-once-more-error ()
  '(mv "When diving to subterm ~x0 using address ~x1, ~
              the additional dive to ~x2 was impossible."
       (list (cons #\0 raw-term)
             (cons #\1 (reverse accumulated-addr-r))
             (cons #\2 (car addr)))))

(defun abbreviation-raw-term-p (x)
  (and (consp x)
       (eq (car x) '?)))

(defmacro addr-recur (pos b)
  `(if (integerp ,pos)
       (mv-let (addr new-term new-iff-flg not-flg)
           ,b
         (if (stringp addr)
             (mv addr nil nil nil)
           (mv (cons ,pos addr) new-term new-iff-flg not-flg)))
     (if (eq ,pos 'not)
         ,(case-match b
                      (('mv 'nil x y 'nil)
                       `(mv nil ,x ,y t))
                      (&
                       '(mv "a NOT term unexpected by the code; sorry" nil nil nil)))
       (mv ,pos nil nil nil))))

(defun or-addr (n term iff-flg)

; Warning: Keep this in sync with untranslate-or and its use in untranslate1.

; See and-addr, which has a corresponding spec except that it is applied to
; terms that untranslate as AND calls, where the present function is for OR
; instead.

  (case-match term
    (('if x1 x1 x2) ; see untranslate1
     (prog2$
      x1 ; otherwise we get a "not used" complaint
      (cond ((int= n 1)
             (mv "an ambiguous dive to first arg of an OR"
                 nil nil nil))
            ((int= n 2)
             (addr-recur 3
                         (or-addr (1- n) x2 iff-flg)))
            (t
             (mv "an index that is out of range"
                 nil nil nil)))))
    (('if x1 x2 *t*) ; see untranslate1
     (cond ((int= n 1)
            (cond ((ffn-symb-p x1 'not)
                   (mv '(1) x1 t t))
                  (t
                   (mv "an unexpected case of diving to first argument: for ~
                        an if-then-else term with THEN branch of nil, the ~
                        TEST was expected to be a call of NOT."
                       nil nil nil))))
           (t
            (addr-recur 2
                        (or-addr (1- n) x2 iff-flg)))))
    (('if x1 *t* x2) ; see untranslate1
     (cond ((int= n 1)
            (mv '(1) x1 t nil))
           (t
            (addr-recur 3
                        (or-addr (1- n) x2 iff-flg)))))
    (&
     (cond ((int= n 1) ; presumably in a recursive call of this function
            (mv nil term iff-flg nil))
           (t
            (mv "a non-IF term encountered when diving to the first argument ~
                 (perhaps because your DV argument was greater than the ~
                 number of disjuncts)."
                nil nil nil))))))

(defun and-addr (n term iff-flg)

; Warning: Keep this in sync with untranslate-and and its use in untranslate1.

; We assume that term has already been abbreviated.  To dive via n into the
; given translated term, which untranslates to an AND expression, we use the
; address returned by this function, dive-addr.  This value is the first in the
; multiple values that we return: (mv dive-addr new-term new-iff-flg
; finish-not-p), where new-term and new-iff-flg are the term after the dive by
; addr, and finish-not-p is t if an additional dive into a NOT call is required
; for the corresponding untranslated term so that the result matches up with
; using dive-addr on the translated term.  (That is, user should provide a next
; address of 1 after n so that the dive can be completed.  The new-term
; returned here "assumes" that this further dive has already been done.)

  (case-match term
    (('if x1 x2 *nil*)
     (cond ((int= n 1)
            (mv '(1) x1 t nil))
           (t
            (addr-recur 2
                        (and-addr (1- n) x2 iff-flg)))))
    (('if x1 *nil* x2)
     (cond ((int= n 1)
            (cond ((ffn-symb-p x1 'not)
                   (mv '(1) x1 t t))
                  (t
                   (mv "an unexpected case of diving to first argument: for ~
                        an if-then-else term with THEN branch of nil, the ~
                        TEST was expected to be a call of NOT"
                       nil nil nil))))
           (t
            (addr-recur 3
                        (and-addr (1- n) x2 iff-flg)))))
    (&
     (cond ((int= n 1) ; presumably in a recursive call of this function
            (mv nil term iff-flg nil))
           (t
            (mv "a non-IF term encountered when diving to the first argument ~
                 (perhaps because your DV argument was greater than the ~
                 number of conjuncts)"
                nil nil nil))))))

(table dive-into-macros-table nil nil
       :guard
       (and (symbolp key)
            (or (and (function-symbolp val world)

; We can call key using ev-fncall-w in expand-address, so we had better be sure
; that the guard of ev-fncall-w will be satisfied.

                     (equal (stobjs-in val world) '(nil nil nil nil))
                     (not (assoc-eq val *ttag-fns*))

; The following test is a bit too strong, since it fails to take into account
; temp-touchable-fns; see untouchable-fn-p.  However, this drawback seems quite
; minor and it certainly does not affect soundness.

                     (not (member-eq val (global-val 'untouchable-fns world))))
                (integerp val)
                (null val))))

(defmacro add-dive-into-macro (name val)
  `(table dive-into-macros-table ',name ',val))

(defmacro remove-dive-into-macro (name)
  `(table dive-into-macros-table ',name nil))

(defun dive-into-macros-table (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (table-alist 'dive-into-macros-table wrld))

(defun rassoc-eq-as-car (key alist)
  (cond ((endp alist) nil)
        ((eq key (car (cdr (car alist))))
         (car alist))
        (t (rassoc-eq-as-car key (cdr alist)))))

(defconst *ca<d^n>r-alist*

; This alist can be constructed as follows in raw Lisp.  Thus, it associates
; each legal cd..dr macro with the number of ds in its name.

; ? (loop for x in
; '(cadr           cdar          caar          cddr
;   caadr   cdadr  cadar  cddar  caaar  cdaar  caddr  cdddr
;   caaadr  cadadr caadar caddar
;   cdaadr  cddadr cdadar cdddar
;                                caaaar cadaar caaddr cadddr
;                                cdaaar cddaar cdaddr cddddr)
; collect (cons x (- (length (symbol-name x)) 2)))

  '((CADR . 2) (CDAR . 2) (CAAR . 2) (CDDR . 2)
    (CAADR . 3) (CDADR . 3) (CADAR . 3) (CDDAR . 3)
    (CAAAR . 3) (CDAAR . 3) (CADDR . 3) (CDDDR . 3)
    (CAAADR . 4) (CADADR . 4) (CAADAR . 4) (CADDAR . 4)
    (CDAADR . 4) (CDDADR . 4) (CDADAR . 4) (CDDDAR . 4)
    (CAAAAR . 4) (CADAAR . 4) (CAADDR . 4) (CADDDR . 4)
    (CDAAAR . 4) (CDDAAR . 4) (CDADDR . 4) (CDDDDR . 4)))

(defun car/cdr^n (n term)

; This function assumes that term is a nest of n or more nested calls of car
; and/or cdr, and returns the term obtained by stripping n such calls.

  (cond
   ((zp n) term)
   ((or (variablep term)
;       (fquotep term)
        (not (member-eq (car term) '(car cdr))))
    (er hard 'car/cdr^n
        "Illegal call: ~x0.~|If you encountered this call in the ~
         proof-builder, please contact the ACL2 implementors."
        `(car/cdr^n ,n ,term)))
   (t (car/cdr^n (1- n) (fargn term 1)))))

(defun expand-address (addr raw-term term abbreviations iff-flg
                            accumulated-addr-r wrld)

; This definition roughly parallels the definition of untranslate.  It normally
; returns (mv nil new-addr), where new-addr is an address appropriate for
; diving into term that corresponds (in a translated setting) to use of the
; given addr to dive into raw-term (in an untranslated setting).  However, this
; function can return (mv string fmt-alist) or (mv t hard-error) when there is
; an error.  We keep accumulated-addr-r as the raw address already traversed,
; in reverse order, only for error messages.

; It's tempting to have a guard of (equal raw-term (untrans0 term iff-flg
; abbreviations)).  We make some attempt to maintain this invariant.

  (cond ((or (null addr)
             (equal addr '(0)))
         (mv nil nil))
        ((abbreviation-raw-term-p raw-term)

; The car of addr should be 0 or 1, but we forgivingly strip off whatever it
; is.  By the way, it doesn't make a whole lot of sense for the cdr of addr to
; be anything other than nil (else why is dv being used?), but we won't enforce
; that here.

         (let ((pair (assoc-eq (cadr raw-term) abbreviations)))
           (if pair
               (expand-address (cdr addr) (cdr pair) term
                               (remove1-equal pair abbreviations)
                               iff-flg
                               (cons (car addr) accumulated-addr-r)
                               wrld)
             (mv t (er hard 'expand-address
                       "Found abbreviation variable ~x0 that is not in the ~
                        current abbreviations alist, ~x1."
                       (cadr raw-term) abbreviations)))))
        ((not (and (integerp (car addr))
                   (< 0 (car addr))))
         (mv "All members of an address must be positive integers (except ~
              that 0 is allowed in circumstances involving CASE, COND, and ~
              abbreviations, which do not apply here).  ~x0 violates this ~
              requirement."
             (list (cons #\0 (car addr)))))
        ((or (variablep raw-term)
             (fquotep raw-term)
             (not (< (car addr) (length raw-term))))
         (dive-once-more-error))
        ((flambda-applicationp term)

; Raw-term is of the form
;   (let ((var_0 term_0) ... (var_k-1 term_k-1)) body)
; and term is of the form
;   ((lambda (var_0 ... var_k-1) body') term_0' ... term_k-1')
; where body' and termi' are the translation of body through termi,
; respectively.  We cannot dive into the lambda, but we can dive into some
; term_i.  So the DV command must be of the form (DV 1 n 1 . rest) for
; 0<=n<=k-1, which tells us to apply (DV . rest) after diving to term_n, which
; corresponds to position n+1 of the translated term.

         (cond
          ((eql (car addr) 2)
            (mv "Unable to dive to the body of a LET, which is really part of ~
                 the function symbol of the translated LAMBDA term."
                nil))
          ((and (consp raw-term)
                (eq (car raw-term) 'let) ; so we assume raw-term is well-formed
                (>= (length addr) 3)
                (eql (car addr) 1)
                (natp (cadr addr))
                (< (cadr addr) (length (cadr raw-term)))
                (member (caddr addr) '(0 1)))
           (cond ((eql (caddr addr) 0)
                  (mv "Unable to dive to a variable of a LET."
                      nil))
                 (t
                  (expand-address-recurse
                   :ans (cons (1+ (cadr addr)) rest-addr)
                   :new-addr (cdddr addr)
                   :new-raw-term (nth 1 (nth (cadr addr) (nth 1 raw-term)))
                   :new-term (nth (1+ (car addr)) term)
                   :new-accumulated-addr-r (cons (1+ (car addr))
                                                 accumulated-addr-r)))))
          (t (mv "Unable to expand LAMBDA (LET) term."
                 nil))))
        ((atom raw-term)
         (mv t (er hard 'expand-address
                   "Surprise!  Found an unexpected raw-term atom, ~x0."
                   raw-term)))
        (t
         (let ((dive-fn
                (cdr (assoc-eq (car raw-term)
                               (dive-into-macros-table wrld)))))
           (cond
            (dive-fn
             (mv-let (erp val)
                     (ev-fncall-w dive-fn
                                  (list (car addr) raw-term term wrld)
                                  wrld nil nil t nil t)
                     (cond
                      ((or erp (stringp (car val)))
                       (mv (car val) (cdr val)))
                      (t (expand-address-recurse
                          :ans (append val rest-addr)
                          :new-iff-flg nil
                          :new-term (fetch-term term val))))))
            ((let ((pair (rassoc-eq-as-car (car raw-term)
                                           (untrans-table wrld))))
               (and pair
                    (eql (arity (car pair) wrld) 2)))

; E.g., (append a b c d) is (binary-append a (binary-append b (binary-append c
; d))), so diving 3 into this (to c) generates address (2 2 1), but diving 4
; generates address (2 2 2), not (2 2 2 1).

             (let* ((lst
                     (cond ((= (car addr) (1- (length raw-term)))
                            (make-list (1- (car addr)) :initial-element 2))
                           (t
                            (append (make-list (1- (car addr)) :initial-element 2)
                                    '(1)))))
                    (subterm (fetch-term term lst)))
               (if subterm
                   (expand-address-recurse
                    :ans (append lst rest-addr)
                    :new-iff-flg nil
                    :new-term subterm)
                 (dive-once-more-error))))
            (t
             (case
               (car raw-term)
               ((list list*)
                (let* ((lst0 (make-list (1- (car addr))
                                        :initial-element 2))
                       (lst (if (eq (car raw-term) 'list)
                                (append lst0 '(1))
                              lst0))
                       (subterm (fetch-term term lst)))
                  (if subterm
                      (expand-address-recurse
                       :ans (append lst rest-addr)
                       :new-iff-flg nil
                       :new-term subterm)
                    (dive-once-more-error))))
               (<=

; Note that (<= x y) translates to (not (< y x)).

                (cond
                 ((not (member (car addr) '(1 2)))
                  (dive-once-more-error))
                 ((= (car addr) 1)
                  (expand-address-recurse
                   :ans (cons 1 (cons 2 rest-addr))
                   :new-iff-flg nil
                   :new-term (nth 2 (nth 1 term))))
                 (t ; (= (car addr) 2)
                  (expand-address-recurse
                   :ans (cons 1 (cons 1 rest-addr))
                   :new-iff-flg nil
                   :new-term (nth 1 (nth 1 term))))))
               ((and or)
                (mv-let (and-or-addr new-term new-iff-flg finish-not-p)
                        (if (eq (car raw-term) 'and)
                            (and-addr (car addr)
                                      (abbreviate term abbreviations)
                                      iff-flg)
                          (or-addr (car addr)
                                   (abbreviate term abbreviations)
                                   iff-flg))
                        (cond
                         ((stringp and-or-addr)
                          (mv "The dive via address ~x0 brings us to the ~x4 ~
                               term~%~ ~ ~y1,~|~%which translates to~%~ ~ ~
                               ~y2.~|~%The requested dive into this ~x4 term ~
                               is problematic, because of ~@3.  Try using ~
                               DIVE instead (after using PP to find the ~
                               appropriate address)."
                              (list (cons #\0 (reverse accumulated-addr-r))
                                    (cons #\1 raw-term)
                                    (cons #\2 term)
                                    (cons #\3 and-or-addr)
                                    (cons #\4 (car raw-term)))))
                         (finish-not-p
                          (cond
                           ((and (cdr addr)
                                 (int= (cadr addr) 1))
                            (expand-address-recurse
                             :ans (append and-or-addr rest-addr)
                             :new-addr (cddr addr)
                             :new-term new-term
                             :new-iff-flg new-iff-flg
                             :new-accumulated-addr-r
                             (cons 1 (cons (car addr) accumulated-addr-r))))
                           (t
                            (mv "The dive via address ~x0 apparently brings ~
                                 us to the NOT term ~x1, which does not ~
                                 actually exist in the internal syntax of the ~
                                 current term, namely:~%~x2.  Try using DIVE ~
                                 instead (after using PP to find the ~
                                 appropriate address)."
                                (list (cons #\0 (reverse (cons (car addr)
                                                               accumulated-addr-r)))
                                      (cons #\1 (nth (car addr) raw-term))
                                      (cons #\2 term))))))
                         (t
                          (expand-address-recurse
                           :ans (append and-or-addr rest-addr)
                           :new-term new-term
                           :new-iff-flg new-iff-flg)))))
               (case

; For example,
;   (case a (b c) (d e) ((f g) h) (otherwise k))
; translates to
; (IF (EQL A 'B)
;     C
;     (IF (EQL A 'D)
;         E
;         (IF (MEMBER A '(F G)) H K))) .
; So, we can only dive to addresses of the form (n 1 ...)
; and (n 0 ...), though the latter cases aren't too interesting.
; In the example above,
; (2 1 ...) gets us to c, which should generate (2)
; (3 1 ...) gets us to e, which should generate (3 2)
; (4 1 ...) gets us to h, which should generate (3 3 2)
; (5 1 ...) gets us to k, which should generate (3 3 3).
; (2 0 ...) gets us to b, which should generate (1 2)
; (3 0 ...) gets us to d, which should generate (3 1 2)
; (4 0 ...) gets us to (f g), which should generate (3 3 1 2)
; (5 0 ...) gets us to "otherwise", which is an error

                 (cond
                  ((= (car addr) 1)
                   (mv "The dive via address ~x0 brings us to the CASE ~
                        term~%~ ~ ~x1,~%which corresponds to the translated ~
                        term~%~ ~ ~x2.~%A further dive to the first argument ~
                        doesn't really make sense here."
                       (list (cons #\0 (reverse accumulated-addr-r))
                             (cons #\1 raw-term)
                             (cons #\2 term))))
                  ((not (and (consp (cdr addr))
                             (member-equal (cadr addr) '(0 1))))
                   (mv "The dive via address ~x0 brings us to the CASE ~
                        term~%~ ~ ~x1,~%A further dive past argument number ~
                        ~x2 to the zeroth or first ``argument'' is required ~
                        at this point.~%"
                       (list (cons #\0 (reverse accumulated-addr-r))
                             (cons #\1 raw-term)
                             (cons #\2 (car addr)))))
                  ((and (= (cadr addr) 0)
                        (= (car addr) (1- (length raw-term))))
                   (mv "The dive via address ~x0 brings us to the CASE ~
                        term~%~ ~ ~x1,~%A further dive to the ``otherwise'' ~
                        expression is not allowed."
                       (list (cons #\0 (reverse accumulated-addr-r))
                             (cons #\1 raw-term))))
                  (t
                   (let* ((lst (if (= (cadr addr) 1)
                                   (if (= (car addr) (1- (length raw-term)))
                                       (make-list (- (car addr) 2) :initial-element 3)
                                     (append (make-list (- (car addr) 2)
                                                        :initial-element 3)
                                             '(2)))
                                 ;; otherwise (car addr) is 0 and
                                 ;; (car addr) < (1- (length raw-term))
                                 (append (make-list (- (car addr) 2)
                                                    :initial-element 3)
                                         '(1 2))))
                          (subterm (fetch-term term lst)))
                     (if subterm
                         (expand-address-recurse
                          :ans (append lst rest-addr)
                          :new-addr (cddr addr)
                          :new-raw-term (cadr (nth (1+ (car addr)) raw-term))
                          :new-term subterm
                          :new-iff-flg iff-flg
                          :new-accumulated-addr-r (cons (car addr) (cons (cadr addr) accumulated-addr-r)))
                       (mv t
                           (er hard 'expand-address
                               "Surprise!  Unable to dive into raw-term ~x0, which is term ~x1,
                           using list ~x2.  So far we have DV-ed using ~x3."
                               raw-term
                               term
                               lst
                               (reverse accumulated-addr-r))))))))
               (cond

; For example,
;   (cond (a b) (c d) (e f) (t g))
; translates to
;   (if a b (if c d (if e f g)))
; So, we can dive to addresses of the form (n 0 ...)
; and (n 1 ...).
; (1 0 ...) gets us to a, which should generate (1)
; (2 0 ...) gets us to c, which should generate (3 1)
; (3 0 ...) gets us to e, which should generate (3 3 1)
; (4 0 ...) gets us to t, which is not allowed.
; (1 1 ...) gets us to b, which should generate (2)
; (2 1 ...) gets us to d, which should generate (3 2)
; (3 1 ...) gets us to f, which should generate (3 3 2)
; (4 1 ...) gets us to g, which should generate (3 3 3)

                (cond
                 ((not (and (consp (cdr addr))
                            (member-equal (cadr addr) '(0 1))))
                  (mv "The dive via address ~x0 brings us to the COND term~%~ ~
                       ~ ~x1,~%A further dive past argument number ~x2 to the ~
                       zeroth or first ``argument'' is required at this ~
                       point.~%"
                      (list (cons #\0 (reverse accumulated-addr-r))
                            (cons #\1 raw-term)
                            (cons #\2 (car addr)))))
                 ((and (= (cadr addr) 0)
                       (= (car addr) (1- (length raw-term))))
                  (mv "The dive via address ~x0 brings us to the COND term~%~ ~
                       ~ ~x1,~%A further dive to the ``T'' expression is not ~
                       allowed."
                      (list (cons #\0 (reverse accumulated-addr-r))
                            (cons #\1 raw-term))))
                 (t
                  (let* ((lst (if (= (cadr addr) 1)
                                  (if (= (car addr) (1- (length raw-term)))
                                      (make-list (1- (car addr)) :initial-element 3)
                                    (append (make-list (1- (car addr))
                                                       :initial-element 3)
                                            '(2)))
                                ;; otherwise (cadr addr) is 0 and (car addr) < (1- (length raw-term))
                                (append (make-list (1- (car addr))
                                                   :initial-element 3)
                                        '(1))))
                         (subterm (fetch-term term lst)))
                    (if subterm
                        (expand-address-recurse
                         :ans (append lst rest-addr)
                         :new-addr (cddr addr)
                         :new-raw-term (cadr (nth (1+ (car addr)) raw-term))
                         :new-term subterm
                         :new-iff-flg iff-flg
                         :new-accumulated-addr-r (cons (car addr) (cons (cadr addr) accumulated-addr-r)))
                      (mv t
                          (er hard 'expand-address
                              "Surprise!  Unable to dive into raw-term ~x0, ~
                               which is term ~x1, using list ~x2.  So far we ~
                               have DV-ed using ~x3."
                              raw-term
                              term
                              lst
                              (reverse accumulated-addr-r))))))))
               (if
                   (expand-address-recurse
                    :new-iff-flg (if (= (car addr) 1) t iff-flg)))
               ((implies iff)
                (expand-address-recurse :new-iff-flg t))
               (t
                (let ((pair (and (consp raw-term)
                                 (assoc-eq (car raw-term) *ca<d^n>r-alist*))))
                  (cond
                   (pair
                    (expand-address-recurse
                     :ans (append (make-list (cdr pair)
                                             :initial-element 1)
                                  rest-addr)
                     :new-term (car/cdr^n (cdr pair) term)))
                   (t (expand-address-recurse))))))))))))

(defmacro dv-error (str alist)
  `(pprogn (print-no-change
            (string-append "Unable to perform the requested dive.~|~%" ,str)

; We could print the current term using ~xt in the string above, but that
; appears to be distracting in the error message.

            (cons (cons #\t current-term) ,alist))
           (mv t nil state)))

(define-pc-atomic-macro dv (&rest rest-args)
  (let* ((conc (conc t))
         (current-addr (current-addr t))
         (abbreviations (abbreviations t))
         (current-term (fetch-term conc current-addr))
         (term-id-iff (term-id-iff conc current-addr t)))
    (mv-let (erp addr)
            ;; If erp is not nil, then it's a string explaining why DV failed,
            ;; and then addr is a list of args for that string (except #\t is
            ;; associated with 'current-term).
            (expand-address rest-args
                            (untrans0 current-term
                                      term-id-iff
                                      abbreviations)
                            current-term
                            abbreviations
                            term-id-iff
                            nil
                            (w state))
            (if erp
                (dv-error erp addr)
              (mv nil (cons ':dive addr) state)))))

(mutual-recursion

(defun deposit-term (term addr subterm)

  ;; Puts subterm at address addr in term.  Assumes that error checking is
  ;; not necessary, i.e. that addr is given correctly relative to term,

  (cond ((null addr) subterm)
        (t
         (cons-term (ffn-symb term)
                    (deposit-term-lst (fargs term) (car addr) (cdr addr) subterm)))))

(defun deposit-term-lst (lst n addr subterm)

  ;; This simply puts (deposit-term term addr subterm) in place of the nth
  ;; element, term, of lst, but avoids consing up the unchanged tail.

  (cond ((= 1 n)
         (cons (deposit-term (car lst) addr subterm) (cdr lst)))
        (t (cons (car lst) (deposit-term-lst (cdr lst) (1- n) addr subterm)))))

)

;; Suppose that we want to make congruence-based substitution.  Here
;; is the plan.  Then (unless the congruence is equality) we need to
;; make sure that wherever the substitution is to be made, the
;; congruence relation is enough to preserve the geneqv at the current
;; subterm.  The following function actually returns a list of congruence
;; rules.

(defun geneqv-at-subterm (term addr geneqv pequiv-info ens wrld)

; Address is a valid address for the term, term.  This function returns a
; geneqv g such that if one substitutes a subterm u of term at the given
; address such that (g term u), resulting in a term term', then (geneqv term
; term').  As usual, we may return nil for to represent the geneqv for equal.

  (cond ((null addr)
         geneqv)
        (t
         (let ((child-geneqv0
                (nth (1- (car addr))

; It seems inefficient to compute the entire geneqv-lst, but we prefer not to
; write a separate function to obtain just the nth element of that list.

                     (geneqv-lst (ffn-symb term) geneqv ens wrld))))
           (mv-let
            (deep-pequiv-lst shallow-pequiv-lst)
            (pequivs-for-rewrite-args (ffn-symb term) geneqv pequiv-info wrld
                                      ens)
            (mv-let
             (pre-rev cur/post)
             (split-at-position (car addr) (fargs term) nil)
             (mv-let
              (child-geneqv child-pequiv-info)
              (geneqv-and-pequiv-info-for-rewrite
               (ffn-symb term)
               (car addr)
               pre-rev cur/post
               nil ; alist for cur/post (and, pre-rev in this case)
               geneqv child-geneqv0
               deep-pequiv-lst shallow-pequiv-lst
               wrld)
              (geneqv-at-subterm (car cur/post)
                                 (cdr addr)
                                 child-geneqv child-pequiv-info
                                 ens wrld))))))))

(defun geneqv-at-subterm-top (term addr ens wrld)
  (geneqv-at-subterm term addr *geneqv-iff* nil ens wrld))

;; In the following we want to know if every occurrence of old in term
;; is at a position at which substitution by something EQUIV to old
;; will guarantee a result that is GENEQV to term.

; (mutual-recursion
;
; (defun subst-expr1-okp (old term equiv geneqv ens wrld)
;   (cond ((equal term old)
;          (geneqv-refinementp equiv geneqv wrld))
;         ((variablep term) t)
;         ((fquotep term) t)
;         (t (subst-expr1-ok-listp old (fargs term)
;                                  (geneqv-lst (ffn-symb term) geneqv ens wrld)
;                                  equiv ens wrld))))
;
; (defun subst-expr1-ok-listp (old args equiv geneqv-lst ens wrld)
;   (cond ((null args) nil)
;         (t (and (subst-expr1-okp
;                  old (car args) equiv (car geneqv-lst) ens wrld)
;                 (subst-expr1-ok-listp
;                  old (cdr args) equiv (cdr geneqv-lst) ens wrld)))))
;
;
; )

;; **** Need to think about what happens if we, e.g., substitute T for X
;; inside (equal X T).  Probably that's OK -- but also, consider allowing
;; an equivalence relation as an argument.  One would have to check that
;; the relation is OK in at the current address, and then one would use
;; that relation instead of equal to create the proof obligation.  Also,
;; consider special handling for IFF in the case that it's (IFF ... T),
;; so that we can simulate pc-nqthm's PUSH command.

;; ****** give a warning if the term to be replaced doesn't occur in the
;; current subterm

;; The following are adapted from ACL2 definitions of subst-expr1 and
;; subst-expr1-lst.  Note that the parameter `new' has been dropped,
;; but the given and current equivalence relations have been added.

(defun maybe-truncate-current-address (addr term orig-addr acc state)
  ;; Truncates the current address if it tries to dive into a quotep.
  ;; Here orig-addr is the original address (used for the warning message)
  ;; and acc is the accumulated new address (in reverse order).
  (declare (xargs :guard (true-listp addr)))
  (if addr
      (cond
       ((variablep term)
        (mv (er hard 'maybe-truncate-current-address
                "Found variable with non-NIL address!")
            state))
       ((fquotep term)
        (let ((new-addr (reverse acc)))
          (pprogn (io? proof-builder nil state
                       (new-addr orig-addr)
                       (fms0 "~|NOTE:  truncating current address from ~x0 to ~
                              ~x1.  See explanation at end of help for X ~
                              command.~|"
                             (list (cons #\0 orig-addr)
                                   (cons #\1 new-addr))
                             0 nil))
                  (mv new-addr state))))
       (t
        (maybe-truncate-current-address
         (cdr addr) (nth (1- (car addr)) (fargs term))
         orig-addr (cons (car addr) acc) state)))
    (mv (reverse acc) state)))

(defun deposit-term-in-goal (given-goal conc current-addr new-term state)
  ;; state is passed in so that maybe-truncate-current-address can
  ;; print a warning message if appropriate
  (let ((new-conc (deposit-term conc current-addr new-term)))
    (if (quotep new-term)
        (mv-let (new-current-addr state)
                (maybe-truncate-current-address
                 current-addr new-conc current-addr nil state)
                (mv (change goal given-goal
                            :conc
                            new-conc
                            :current-addr
                            new-current-addr)
                    state))
      (mv (change goal given-goal
                  :conc
                  new-conc)
          state))))

(defun split-implies (term)
  ;; returns hyps and conc for term, e.g.
  ;; (implies x y) --> (mv (list x) y),
  ;; (implies x (implies (and y z)) w) --> (mv (list x y z) w), and
  ;; (foo 3) --> (mv nil (foo 3))
  (if (not (ffn-symb-p term 'implies))
      (mv nil term)
    (mv-let (h c)
            (split-implies (fargn term 2))
            (mv (append (flatten-ands-in-lit (fargn term 1)) h) c))))

(defun find-equivalence-hyp-term (term hyps target equiv w)
  ;; allows backchaining through IMPLIES
  (if (consp hyps)
      (mv-let (h c)
              (split-implies (car hyps))
              (if (or (variablep c)
                      (fquotep c)
                      (not (symbolp (ffn-symb c)))
                      (not (refinementp (ffn-symb c) equiv w)))
                  (find-equivalence-hyp-term term (cdr hyps) target equiv w)
                (let ((x (fargn c 1))
                      (y (fargn c 2)))
                  (or
                   (and (subsetp-equal h hyps)
                        (or (and (equal x term)
                                 (equal y target))
                            (and (equal y term)
                                 (equal x target))))
                   (find-equivalence-hyp-term term (cdr hyps) target equiv w)))))
    nil))

(define-pc-primitive equiv (x y &optional equiv)
  (mv-let
   (current-term governors)
   (fetch-term-and-cl conc current-addr nil)
   (cond
    ((eq governors t)
     (mv (er hard ':=
             "Found governors of T inside command ~x0!"
             (cons := args))
         state))
    (t
     (let* ((assumptions (append hyps governors))
            (w (w state))
            (pc-ens (make-pc-ens pc-ens state)))
       (mv-let
        (erp new-pc-state state)
        (er-let*
         ((old (trans0 x abbreviations :equiv))
          (new (trans0 y abbreviations :equiv))
          (equiv (if (null equiv)
                     (value 'equal)
                   (if (and (symbolp equiv)
                            (equivalence-relationp equiv w))
                       (value equiv)
                     (er soft :equiv
                         "The name ~x0 is not currently the name of an ACL2 ~
                          equivalence relation.~@1  The current list of ~
                          ACL2 equivalence relations is ~x2."
                         equiv
                         (let ((pair (and (symbolp equiv)
                                          (assoc-eq
                                           equiv
                                           (table-alist 'macro-aliases-table
                                                        w)))))
                           (if (and pair
                                    (equivalence-relationp (cdr pair) w))
                               (msg "  Perhaps you intended the corresponding ~
                                     function for which it is an ~
                                     ``alias''(see :DOC macro-aliases-table), ~
                                     ~x0."
                                    (cdr pair))
                             ""))
                         (getpropc 'equal 'coarsenings nil w))))))
         (if (find-equivalence-hyp-term old
                                        (flatten-ands-in-lit-lst assumptions)
                                        new equiv w)
             (mv-let (hitp new-current-term new-ttree)
                     (subst-equiv-expr1 equiv new old
                                        (geneqv-at-subterm-top conc current-addr pc-ens w)
                                        current-term pc-ens w state nil)
                     (if hitp
                         (mv-let
                          (new-goal state)
                          (deposit-term-in-goal
                           (car goals) conc current-addr new-current-term state)
                          (value (change-pc-state
                                  pc-state
                                  :local-tag-tree
                                  new-ttree
                                  :goals
                                  (cons new-goal (cdr goals)))))
                       (pprogn
                        (print-no-change
                         "The equivalence relation that you specified, namely ~x0, is ~
                          not appropriate at any occurrence of the ``old'' term ~x1 ~
                          inside the current term, and hence no substitution has ~
                          been made."
                         (list (cons #\0 equiv)
                               (cons #\1 x)))
                        (value nil))))
           (pprogn
            (print-no-change
             "The ~#2~[equivalence~/equality~] of the terms ~x0 and ~x1~#2~[ with respect ~
              to the equivalence relation ~x3~/~] is not known at the ~
              current subterm from the current hypotheses and governors."
             (list (cons #\0 x)
                   (cons #\1 y)
                   (cons #\2 (if (eq equiv 'equal) 1 0))
                   (cons #\3 equiv)))
            (value nil))))
        (if erp
            (print-no-change2 "EQUIV failed.")
          (mv new-pc-state state))))))))

(define-pc-primitive casesplit
  (expr &optional use-hyps-flag do-not-flatten-flag)
  (mv-let
   (erp term state)
   (trans0 expr abbreviations :casesplit)
   (if erp
       (print-no-change2 "~x0 failed."
                         (list (cons #\0 (cons :casesplit args))))
     (let ((claimed-term
            (if use-hyps-flag
                (mv-let
                 (current-term governors)
                 (fetch-term-and-cl conc current-addr nil)
                 (declare (ignore current-term))
                 (cond
                  ((eq governors t)
                   (er hard ':casesplit
                       "Found governors of T inside command ~x0!"
                       (cons :casesplit args)))
                  (governors
                   (fcons-term* 'implies (conjoin governors) term))
                  (t term)))
              term)))
       (mv (change-pc-state
            pc-state
            :goals
            (cons (change goal (car goals)
                          :hyps (append hyps
                                        (if do-not-flatten-flag
                                            (list claimed-term)
                                          (flatten-ands-in-lit claimed-term)))
                          :depends-on (1+ depends-on))
                  (cons (change goal (car goals)
                                :hyps (append
                                       hyps
                                       (if do-not-flatten-flag
                                           (list (dumb-negate-lit
                                                  claimed-term))
                                         (flatten-ands-in-lit
                                          (dumb-negate-lit claimed-term))))
                                :goal-name (cons goal-name depends-on)
                                :depends-on 1)
                        (cdr goals))))
           state)))))

;;(defconst *pc-catch-all-tag* :pc-catch-all-tag)

(define-pc-macro top? ()
  (when-goals-trip
   (if (current-addr t)
       (value 'top)
     (value 'skip))))

(define-pc-macro contrapose-last ()
  (when-goals-trip
   (let ((hyps (hyps)))
     (if (null hyps)
         (pprogn (print-no-change "CONTRAPOSE-LAST failed -- no top-level hypotheses!")
                 (value :fail))
       (value (list :contrapose (length hyps)))))))

(define-pc-macro drop-last ()
  (when-goals-trip
   (let ((hyps (hyps)))
     (if (null hyps)
         (pprogn (print-no-change "DROP-LAST failed -- no top-level hypotheses!")
                 (value :fail))
       (value (list :drop (length hyps)))))))

(define-pc-macro drop-conc ()
  (value `(do-strict top? contrapose-last drop-last)))

(define-pc-atomic-macro claim (expr &rest rest-args)
  (when-goals-trip
   (value
    (let ((rest-args-1 (if (and rest-args
                                (car rest-args)
                                (not (keywordp (car rest-args))))
                           (list* :hints :none (cdr rest-args))
                         rest-args)))
      (mv-let (pairs remaining-rest-args)
        (pair-keywords '(:do-not-flatten) rest-args-1)
        (let ((do-not-flatten-flag (cdr (assoc-eq :do-not-flatten pairs)))
              (temp (cadr (member-eq :hints rest-args-1))))
          (if (and temp (atom temp))
              `(protect
                (casesplit ,expr nil ,do-not-flatten-flag)
                change-goal
                drop-conc
                pro
                change-goal)
            `(protect
              (casesplit ,expr nil ,do-not-flatten-flag)
              change-goal
              drop-conc
              (prove ,@remaining-rest-args)))))))))

(define-pc-atomic-macro induct (&optional raw-term)
  (when-goals-trip
   (if (and (goals t)
            (current-addr t))
       (pprogn (print-no-change
                "You must be at the top of the goal in order to use the ~
                INDUCT command.  Try TOP first.")
               (value :fail))
     (let ((raw-term (or raw-term t)))
       (value `(prove :hints
                      (("Goal" :induct ,raw-term
                        :do-not-induct proof-builder
                        :do-not *do-not-processes*))))))))

(defun print-on-separate-lines (vals evisc-tuple chan state)
  (declare (xargs :guard (true-listp vals)))
  (if (null vals)
      (newline chan state)
    (pprogn (io? proof-builder nil state
                 (evisc-tuple chan vals)
                 (fms "~x0" (list (cons #\0 (car vals))) chan state
                      evisc-tuple))
            (print-on-separate-lines (cdr vals) evisc-tuple chan state))))

(define-pc-help goals ()
  (io? proof-builder nil state
       (state-stack)
       (when-goals
        (print-on-separate-lines (goal-names (goals t)) nil (proofs-co state)
                                 state))))

(defun modified-error-triple-for-sequence (erp val success-expr state)
  (mv-let (new-erp stobjs-out-and-vals state)
          (state-global-let*
           ((pc-erp erp)
            (pc-val val))
           (trans-eval-default-warning success-expr :sequence state t))

; Note: Success-expr is typically an expression involving STATE, which
; accesses erp and val via (@ erp) and (@ val).  It may modify STATE.
; It may, indeed, talk about single-threaded objects!  It may even
; modify them, leaving their modified values in the modified state.
; But it is expected to return at least two results, and the first two
; must not be stobjs.

          (let ((stobjs-out (car stobjs-out-and-vals))
                (vals (cdr stobjs-out-and-vals)))
            (if new-erp
                (mv new-erp nil state)
              (if (or (< (length stobjs-out) 2)
                      (car stobjs-out)
                      (cadr stobjs-out))
                  (pprogn (io? proof-builder nil state
                               (vals success-expr)
                               (fms0 "~|WARNING -- evaluation of ~
                                      `success-expr' argument to ~
                                      :SEQUENCE, ~x0, has been ~
                                      ignored because it returned a ~
                                      single-threaded object in one ~
                                      of its first two values or ~
                                      returned fewer than two values. ~
                                      The value(s) returned was ~
                                      (were):~%~ ~ ~x1.~%"
                                     (list (cons #\0 success-expr)
                                           (cons #\1 vals))))
                          (mv erp val state))
                (mv (car vals) (cadr vals) state))))))

(define-pc-meta sequence
  (instr-list &optional
              strict-flg protect-flg success-expr no-prompt-flg no-restore-flg)

  ;; Note:  the reason I use state globals instead of a lexical LET for
  ;; the success-expr argument is that I don't want to worry about the
  ;; translator failing because erp and val aren't declared ignored when
  ;; they should be.

  ;; This is the only place where the pc-prompt gets lengthened.
  ;; Also note that we always lengthen the prompt, but we only do the printing
  ;; if no-prompt-flg is nil AND pc-print-prompt-and-instr-flg is non-nil.
  (if (not (true-listp instr-list))
      (pprogn (print-no-change
               "The first argument to the SEQUENCE command must be ~
                a true list, but~%~ ~ ~x0~| is not."
               (list (cons #\0 instr-list)))
              (mv t nil state))
    (state-global-let*
     ((pc-prompt (string-append (pc-prompt-depth-prefix)
                                (pc-prompt))))
     (let ((saved-old-ss (old-ss))
           (saved-ss (state-stack)))
       (mv-let (erp val state)
               (pc-main-loop instr-list
                             (if strict-flg '(signal value) '(signal))
                             t
                             (and (null no-prompt-flg)
                                  (pc-print-prompt-and-instr-flg))
                             state)
               (mv-let (erp val state)
                       (if success-expr
                           (modified-error-triple-for-sequence erp val success-expr state)
                         (mv erp val state))
                       (if (and protect-flg
                                (or erp (null val)))
                           (pprogn (print-no-change
                                    "SEQUENCE failed, with protection on.  ~
                                     Reverting back to existing state of the ~
                                     proof-builder.~|")
                                   ;; **** consider improving message above, say by printing
                                   ;; entire instruction with appropriate evisceration
                                   (pc-assign state-stack saved-ss)
                                   (pc-assign old-ss saved-old-ss)
                                   (mv erp val state))
                         (pprogn (if no-restore-flg
                                     state
                                   (pc-assign old-ss saved-ss))
                                 (mv erp val state)))))))))

(define-pc-macro negate (&rest instr-list)
  (value (list :sequence instr-list nil nil
               '(mv nil
                    (if (or (f-get-global 'pc-erp state)
                            (null (f-get-global 'pc-val state)))
                        t
                      nil)))))

(define-pc-macro succeed (&rest instr-list)

  ;; I won't make this atomic, since I view this as just a sequencer
  ;; command that should ultimately "disappear" in favor of its arguments.

  (mv nil
      (list :sequence
            instr-list nil nil '(mv nil t))
      state))

(define-pc-macro do-all (&rest instr-list)
  (mv nil (list :sequence instr-list)
      state))

(define-pc-macro do-strict (&rest instr-list)
  (mv nil (list :sequence instr-list t)
      state))

(define-pc-macro do-all-no-prompt (&rest instr-list)
  (mv nil (list :sequence instr-list nil nil nil t t)
      state))

(define-pc-macro th (&optional hyps-indices govs-indices)
  (declare (ignore hyps-indices govs-indices))

  (when-goals-trip
   (value `(do-all-no-prompt (hyps ,@args)
                             (lisp (io? proof-builder nil state
                                        nil
                                        (fms0 "~%The current subterm is:~%")))
                             p))))

(define-pc-macro protect (&rest instr-list)
  (mv nil (list :sequence instr-list t t) state))

(defun extract-goal (name goals)
  ;; returns (goal rest-goals) if goal is found, else (nil ...).
  (if (consp goals)
      (if (equal (access goal (car goals) :goal-name) name)
          (mv (car goals) (cdr goals))
        (mv-let (goal rest-goals)
                (extract-goal name (cdr goals))
                (mv goal (cons (car goals) rest-goals))))
    (mv nil goals)))

(define-pc-primitive change-goal (&optional name end-flg)
  (cond
   ((null goals)
    (pprogn (print-all-goals-proved-message state)
            (mv nil state)))
   ((null (cdr goals))
    (print-no-change2 "The current goal is the only unproved goal."))
   ((null name)
    (pprogn (io? proof-builder nil state
                 (goals)
                 (fms0 "~|Now proving ~X0n.~%"
                       (list (cons #\0 (access goal (cadr goals) :goal-name))
                             (cons #\n nil))))
            (mv (change-pc-state pc-state
                                 :goals
                                 (if end-flg
                                     (cons (cadr goals)
                                           (append (cddr goals) (list (car goals))))
                                   (list* (cadr goals) (car goals) (cddr goals))))
                state)))
   ((equal name goal-name)
    (print-no-change2 "The current goal is already ~x0."
                      (list (cons #\0 name))))
   (t
    (mv-let (gl rest-goals)
            (extract-goal name (cdr goals))
            (if gl
                (mv (change-pc-state pc-state
                                     :goals
                                     (if end-flg
                                         (cons gl (append rest-goals (list (car goals))))
                                       (cons gl (cons (car goals) rest-goals))))
                    state)
              (print-no-change2 "There is no unproved goal named ~x0."
                                (list (cons #\0 name))))))))

(define-pc-macro cg (&optional name)
  (value `(change-goal ,name t)))

(defun change-by-position (lst index new)
  (declare (xargs :guard (and (true-listp lst)
                              (integerp index)
                              (<= 0 index)
                              (< index (length lst)))))
  (if (equal index 0)
      (cons new (cdr lst))
    (cons (car lst)
          (change-by-position (cdr lst) (1- index) new))))

(define-pc-primitive contrapose (&optional n)
  (let ((n (if args n 1)))
    (if hyps
        (if current-addr
            (print-no-change2 "You must be at the top of the conclusion to apply ~
                               the CONTRAPOSE command.  Try TOP first.")
          (if (and (integerp n) (< 0 n) (<= n (length hyps)))
              (mv (change-pc-state
                   pc-state
                   :goals
                   (cons (change goal (car goals)
                                 :hyps (change-by-position hyps (1- n) (dumb-negate-lit conc))
                                 :conc (dumb-negate-lit (nth (1- n) hyps)))
                         (cdr goals)))
                  state)
            (print-no-change2 "The argument to CONTRAPOSE must be a positive integer ~
                               that does not exceed the length of the list of top-level ~
                               hypotheses.  The argument ~x0 fails to meet this requirement."
                              (list (cons #\0 n)))))
      (print-no-change2 "There are no top-level hypotheses."))))

(define-pc-macro contradict (&optional n)
  (declare (ignore n))
  (value (cons :contrapose args)))

(define-pc-atomic-macro pro ()
  (value '(quiet (repeat promote))))

(define-pc-atomic-macro nx ()
  (when-goals-trip
   (let ((current-addr (current-addr t)))
     (if current-addr
         (value `(protect up ,(1+ (car (last current-addr)))))
       (pprogn (print-no-change "NX failed:  already at the top!")
               (value :fail))))))

(define-pc-atomic-macro bk ()
  (when-goals-trip
   (let ((current-addr (current-addr t)))
     (if current-addr
         (let ((n (car (last current-addr))))
           (if (equal n 1)
               (pprogn (print-no-change "BK failed:  already at the first argument!")
                       (value :fail))
             (value `(do-strict up ,(1- n)))))
       (pprogn (print-no-change "BK failed:  already at the top!")
               (value :fail))))))

(define-pc-help p-top ()
  (when-goals
   (let ((conc (conc t))
         (current-addr (current-addr t))
         (stars (intern$ "***" (f-get-global 'current-package state))))
     (io? proof-builder nil state
          (state-stack current-addr conc stars)
          (fms0 "~|~y0~|"
                (list (cons #\0
                            (untrans0
                             (deposit-term conc
                                           current-addr
                                           (list stars
                                                 (fetch-term conc current-addr)
                                                 stars))
                             t
                             (abbreviations t)))))))))

(define-pc-macro repeat (instr)
  (value `(succeed (repeat-rec ,instr))))

(define-pc-macro repeat-rec (instr)
  (value `(do-strict ,instr (repeat-rec ,instr))))

(defmacro define-pc-bind* (name &rest args)
  `(define-pc-meta ,name (&rest instr-list)
     (state-global-let*
      (,@args)
      (pc-main-loop instr-list nil t
                    (pc-print-prompt-and-instr-flg)
                    state))))

(define-pc-bind* quiet
  (inhibit-output-lst
   (union-eq '(prove proof-builder proof-tree warning observation)
             (f-get-global 'inhibit-output-lst state))))

(define-pc-bind* quiet!
  (print-clause-ids nil)
  (gag-mode nil)
  (inhibit-output-lst
   (if (member-eq 'error (f-get-global 'inhibit-output-lst state))
       *valid-output-names*
     (set-difference-eq *valid-output-names*
                        '(error)))))

(define-pc-bind* noise
  (gag-mode nil)
  (inhibit-output-lst '(proof-tree)))

(define-pc-bind* noise!
  (gag-mode nil)
  (inhibit-output-lst nil))

(defun find-equivalence-hyp-term-no-target (index term hyps equiv w)
  ;; Allows backchaining through IMPLIES.  Returns an appropriate target.
  ;; Thus we are being rather silly here computationally, since we have
  ;; to do the work twice after generating an :equiv command.  But so what?
  (if (consp hyps)
      (mv-let (h c)
              (split-implies (car hyps))
              (if (or (variablep c)
                      (fquotep c)
                      (not (symbolp (ffn-symb c)))
                      (not (refinementp (ffn-symb c) equiv w)))
                  (find-equivalence-hyp-term-no-target
                   (1+ index) term (cdr hyps) equiv w)
                (let* ((x (fargn c 1))
                       (y (fargn c 2))
                       (hyp-to-use (and (subsetp-equal h hyps)
                                        (or (and (equal x term)
                                                 y)
                                            (and (equal y term)
                                                 x)))))
                  (if hyp-to-use
                      (mv index hyp-to-use)
                    (find-equivalence-hyp-term-no-target
                     (1+ index) term (cdr hyps) equiv w)))))
    (mv nil nil)))

(define-pc-atomic-macro if-not-proved (goal-name cmd)

; Requires the current goal to be named goal-name if it isn't already proved.

  (if (member-equal goal-name (goal-names (goals t)))
      (if (equal goal-name (goal-name t))
          (value cmd)
        (mv-let
         (erp val state)
         (er soft 'if-not-proved
             "The proof-builder's atomic macro IF-NOT-PROVED requires the ~
              indicated goal to be the current goal.  However, the current ~
              goal is ~p0 while the first argument to IF-NOT-PROVED is ~p1."
             (goal-name t)
             goal-name)
         (declare (ignore erp val))
         (value 'fail)))
    (value :skip)))

(define-pc-atomic-macro = (&optional x y &rest rest-args)
  (when-goals-trip
   (let ((conc (conc t))
         (hyps (hyps t))
         (current-addr (current-addr t))
         (abbreviations (abbreviations t))
         (w (w state))
         (rest-args-1 (if (and rest-args
                               (car rest-args)
                               (not (keywordp (car rest-args))))
                          '(:hints :none)
                        rest-args)))
     (if (not (keyword-value-listp rest-args-1))
         (pprogn (print-no-change
                  "The ``rest-args'' arguments for the = command should be ~
                   empty or a list, either (i) containing one element, an ~
                   atom, or else (ii) of even length with keywords in the odd ~
                   positions.  Thus your command ~p0 is not legal.  See the ~
                   documentation for examples and details."
                  (list (cons #\0 (make-pretty-pc-instr (cons := args)))))
                 (value :fail))
       (mv-let
         (equiv-alist rest-args-1)
         (if (keyword-value-listp rest-args-1)
             (pair-keywords '(:equiv) rest-args-1)
           (mv nil rest-args-1))
         (let ((equiv (or (cdr (assoc-eq :equiv equiv-alist))
                          'equal)))
           (mv-let
             (current-term governors)
             (fetch-term-and-cl conc current-addr nil)
             (cond
              ((eq governors t)
               (value (er hard ':=
                          "Found governors of T inside command ~p0!"
                          (cons := args))))
              ((eq x :&)
               (pprogn (print-no-change
                        "We do not allow the first argument of the = command ~
                         to be the keyword :&, because no other symbol with ~
                         print-name & can be a term (and hence we use it to ~
                         represent the current subterm), but :& is a ~
                         legitimate term and -- we can't be really sure ~
                         whether you intended it to represent the term :& or ~
                         the current subterm.")
                       (value :fail)))
              ((not (member-eq equiv
                               (getpropc 'equal 'coarsenings nil w)))
               (pprogn
                (print-no-change
                 "The ``equivalence relation'' that you supplied, ~p0, is not ~
                  known to ACL2 as an equivalence relation.~@1"
                 (list (cons #\0 equiv)
                       (cons #\1
                             (let ((pair
                                    (and (symbolp equiv)
                                         (assoc-eq
                                          equiv
                                          (table-alist 'macro-aliases-table
                                                       w)))))
                               (if (and pair
                                        (equivalence-relationp (cdr pair) w))
                                   (msg "  Perhaps you intended the ~
                                         corresponding function for which it ~
                                         is an ``alias''(see :DOC ~
                                         macro-aliases-table), ~x0."
                                        (cdr pair))
                                 "")))))
                (value :fail)))
              ((null args)
               (mv-let (found-hyp new)
                 (find-equivalence-hyp-term-no-target
                  1 current-term
                  (flatten-ands-in-lit-lst (append hyps governors))
                  equiv w)
                 (if found-hyp
                     (pprogn
                      (io? proof-builder nil state
                           (found-hyp)
                           (fms0 "Using hypothesis #~x0.~%"
                                 (list (cons #\0 found-hyp))))
                      (value (list :equiv current-term new)))
                   (pprogn (print-no-change
                            "There is no hypothesis or governor that equates ~
                             the current term ~#0~[under the equivalence ~
                             relation ~p1 ~/~]with anything."
                            (list (cons #\0 (if (eq equiv 'equal) 1 0))
                                  (cons #\1 equiv)))
                           (value :fail)))))
              (t
               ;; so, we have a valid equivalence relation and at least one argument
               (mv-let
                 (rest-args-alist tail)
                 (pair-keywords '(:otf-flg :hints) rest-args-1)
                 (declare (ignore rest-args-alist))
                 (if tail
                     (pprogn
                      (print-no-change
                       "The only keywords allowed in the arguments to the = ~
                        command are :otf-flg, :hints, and :equiv.  Your ~
                        instruction ~p1 violates this requirement."
                       (list (cons #\1
                                   (make-pretty-pc-instr (cons := args)))))
                      (value :fail))
                   (er-let*
                       ((old (if (or (null (cdr args))
                                     (and (symbolp x)
                                          (eq (intern-in-keyword-package x) :&)))
                                 (value current-term)
                               (trans0 x abbreviations ':=)))
                        (new (if (null (cdr args))
                                 (trans0 x abbreviations ':=)
                               (trans0 y abbreviations ':=))))
                     (value (list :protect
                                  (list* :claim
                                         (if governors
                                             (fcons-term* 'implies (conjoin
                                                                    governors)
                                                          (list equiv old new))
                                           (list equiv old new))
                                         :do-not-flatten t
                                         rest-args-1)
                                  (list :equiv old new equiv)
                                  (list :if-not-proved
                                        (goal-name t)
                                        :drop-last)))))))))))))))

(define-pc-macro set-success (instr form)
  (value `(sequence (,instr) nil nil ,form)))

(define-pc-macro orelse (instr1 instr2)
  (value `(negate (do-strict (negate ,instr1) (negate ,instr2)))))

(defun applicable-rewrite-rules (current-term conc current-addr target-name-or-rune
                                              target-index ens wrld)

; Returns a list of sar records.  This list represents rules that can rewrite
; the current-term, each paired with the appropriate substitution and index,
; but filtered so that only those corresponding to target-name-or-rune are
; included (if non-NIL).  If target-index is NIL then we get all such rules;
; otherwise we get a list with at most one rule, namely the one corresponding
; to that index.

  (declare (xargs :guard (not (or (variablep current-term)
                                  (fquotep current-term)
                                  (flambdap (ffn-symb current-term))))))
  (applicable-rewrite-rules1
   current-term
   (geneqv-at-subterm-top conc current-addr ens wrld)
   (getpropc (ffn-symb current-term) 'lemmas nil wrld)
   1 target-name-or-rune target-index wrld))

(define-pc-help show-rewrites (&optional rule-id enabled-only-flg)
  (when-goals
   (let ((conc (conc t))
         (current-addr (current-addr t))
         (w (w state)))
     (let ((ens (make-pc-ens (pc-ens t) state))
           (current-term (fetch-term conc current-addr))
           (abbreviations (abbreviations t))
           (term-id-iff (term-id-iff conc current-addr t))
           (all-hyps (union-equal (hyps t) (governors conc current-addr))))
       (show-rewrites-linears-fn
        'show-rewrites rule-id enabled-only-flg ens current-term
        abbreviations term-id-iff all-hyps
        (geneqv-at-subterm-top conc current-addr ens w)
        nil state)))))

(define-pc-macro sr (&rest args)
  (value (cons :show-rewrites args)))

(define-pc-help show-linears (&optional rule-id enabled-only-flg)
  (when-goals
   (let ((conc (conc t))
         (current-addr (current-addr t))
         (w (w state)))
     (let ((ens (make-pc-ens (pc-ens t) state))
           (current-term (fetch-term conc current-addr))
           (abbreviations (abbreviations t))
           (term-id-iff (term-id-iff conc current-addr t)) ; irrelevant?
           (all-hyps (union-equal (hyps t) (governors conc current-addr))))
       (show-rewrites-linears-fn
        'show-linears rule-id enabled-only-flg ens current-term
        abbreviations term-id-iff all-hyps
        (geneqv-at-subterm-top conc current-addr ens w) ; irrelevant?
        nil state)))))

(define-pc-macro sls (&rest args)
  (value (cons :show-linears args)))

(define-pc-macro pl (&optional x)
  (cond (x (value `(lisp (pl ',x))))
        ((null (goals))
         (pprogn (print-all-goals-proved-message state)
                 (value 'skip)))
        (t (let* ((conc (conc t))
                  (current-addr (current-addr t))
                  (current-term (fetch-term conc current-addr)))
             (cond ((or (variablep current-term)
                        (fquotep current-term)
                        (flambda-applicationp current-term))
                    (er soft 'pl
                        "The current subterm is not the application of a ~
                         function symbol."))
                   (t (value `(lisp (pl ',(ffn-symb current-term))))))))))

(define-pc-macro pr (&optional x)
  (cond (x (value `(lisp (pr ',x))))
        ((null (goals))
         (pprogn (print-all-goals-proved-message state)
                 (value 'skip)))
        (t (let* ((conc (conc t))
                  (current-addr (current-addr t))
                  (current-term (fetch-term conc current-addr)))
             (cond ((or (variablep current-term)
                        (fquotep current-term)
                        (flambda-applicationp current-term))
                    (er soft 'pr
                        "The current subterm is not the application of a ~
                         function symbol."))
                   (t (value `(lisp (pr ',(ffn-symb current-term))))))))))

(define-pc-help show-type-prescriptions (&optional rule-id)
  (when-goals
   (let ((conc (conc t))
         (current-addr (current-addr t)))
     (let ((ens (make-pc-ens (pc-ens t) state))
           (current-term (fetch-term conc current-addr))
           (abbreviations (abbreviations t))
           (all-hyps (union-equal (hyps t) (governors conc current-addr))))
       (show-type-prescription-rules current-term rule-id abbreviations
                                     all-hyps ens state)))))

(define-pc-macro st (&rest args)
  (value (cons :show-type-prescriptions args)))

(defun translate-subst-abb1 (sub abbreviations state)
  ;; Here sub is a list of doublets (variable form)
  ;; and we return a triple (erp val state).  If the erp is non-nil then
  ;; we use it to decode the message returned in the value component.
  ;; We'll assume that #\s is bound to the original substitution.
  ;;   We should check somewhere else that sub is an alistp.
  ;; We have to pass in and return state because of the call to translate.
  (declare (xargs :guard (symbol-alistp sub)))
  (if (consp sub)
      (mv-let (erp term state)
              (trans0 (cadar sub) abbreviations 'translate-subst-abb1)
              (if erp
                  (mv "~|Translation error for ~x0 caused error in ~
                       translating ~xs.~|"
                      (list (cons #\0 (cadar sub)))
                      state)
                (mv-let (erp val state)
                        (translate-subst-abb1 (cdr sub) abbreviations state)
                        (if erp
                            (mv erp val state)
                          (mv nil (cons (cons (caar sub) term) val) state)))))
    (mv nil nil state)))

(defun single-valued-symbolp-alistp (alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (if alist
      (and (not (assoc-eq (caar alist) (cdr alist)))
           (single-valued-symbolp-alistp (cdr alist)))
    t))

(defun check-cars-are-variables (alist state)
  ;; return T if there's a problem
  (declare (xargs :guard (symbol-alistp alist)))
  (if alist
      (mv-let (erp val state)
              (trans0 (caar alist) nil)
              (if (or erp
                      (not (eq val (caar alist))))
                  (pprogn
                   (io? proof-builder nil state
                        (alist)
                        (fms0 "~|A substitution must be an alist whose CARs ~
                               are variables, but the entry ~x0 violates this ~
                               property.~|"
                              (list (cons #\0 (caar alist)))))
                   (mv t state))
                (check-cars-are-variables (cdr alist) state)))
    (mv nil state)))

(defun translate-subst-abb (sub abbreviations state)
  (cond
   ((not (true-listp sub))
    (pprogn (io? proof-builder nil state
                 (sub)
                 (fms0 "~|A substitution must be a true (nil-terminated) ~
                        list, but~%~x0 is not.~|"
                       (list (cons #\0 sub))))
            (mv t nil state)))
   ((not (and (symbol-alistp sub)
              (single-valued-symbolp-alistp sub)))
    (pprogn (io? proof-builder nil state
                 (sub)
                 (fms0 "~|A substitution must be an alist of pairs without ~
                        duplicate keys, but ~x0 is not.~|"
                       (list (cons #\0 sub))))
            (mv t nil state)))
   (t
    (mv-let (erp state)
            (check-cars-are-variables sub state)
            (if erp
                (mv t nil state)
              (mv-let (erp val state)
                      (translate-subst-abb1 sub abbreviations state)
                      (if erp
                          (pprogn (io? proof-builder nil state
                                       (val sub erp)
                                       (fms0 erp (cons (cons #\s sub) val)))
                                  (mv t nil state))
                        (mv nil val state))))))))

(defun make-rewrite-instr (lemma-id raw-subst instantiate-free)
  (list* (make-pretty-pc-command :rewrite)
         lemma-id
         (cond (instantiate-free (list raw-subst instantiate-free))
               (raw-subst (list raw-subst))
               (t nil))))

(define-pc-primitive rewrite (&optional rule-id raw-sub instantiate-free)

; Warning: Keep this in sync with the proof-builder apply-linear command.

  (mv-let
   (erp sub state)
   (translate-subst-abb raw-sub abbreviations state)
   (if erp
       (print-no-change2 "~x0 failed."
                         (list (cons #\0 (cons :rewrite args))))
     (let ((name (and (symbolp rule-id) rule-id))
           (rune (and (consp rule-id)
                      (member-eq (car rule-id) '(:rewrite :definition))
                      rule-id))
           (index (if (and (integerp rule-id) (< 0 rule-id))
                      rule-id
                    (if rule-id
                        nil
                      1)))
           (pc-ens (make-pc-ens pc-ens state))
           (w (w state))
           (current-term (fetch-term conc current-addr))
           (assumptions (union-equal hyps (governors conc current-addr))))
       (cond
        ((or (variablep current-term)
             (fquotep current-term)
             (flambdap (ffn-symb current-term)))
         (print-no-change2
          "It is only possible to apply rewrite rules to terms that are not ~
           variables, (quoted) constants, or applications of lambda ~
           expressions.  However, the current term is:~%~ ~ ~y0.~|"
          (list (cons #\0 current-term))))
        ((not (or name index rune))
         (print-no-change2
          "The rule-id argument to REWRITE must be a name, a positive ~
           integer, or a :rewrite or :definition rune, but ~x0 is none of ~
           these.~|"
          (list (cons #\0 rule-id))))
        (t
         (mv-let
          (flg hyps-type-alist ttree)
          (hyps-type-alist assumptions pc-ens w state)
          (declare (ignore ttree))
          (if flg
              (print-no-change2
               "Contradiction in the hypotheses!~%The S command should ~
                complete this goal.~|")
            (let ((app-rewrite-rules
                   (applicable-rewrite-rules
                    current-term conc current-addr (or name rune) index
                    pc-ens w)))
              (if (null app-rewrite-rules)
                  (if (and index (> index 1))
                      (print-no-change2
                       "There are fewer than ~x0 applicable rewrite rules.~%"
                       (list (cons #\0 index)))
                    (print-no-change2
                     "There are no applicable rewrite rules.~%"))
                (let* ((sar (car app-rewrite-rules))
                       (lemma (access sar sar :lemma))
                       (start-alist (access sar sar :alist))
                       (alist (append start-alist sub))
                       (rhs (access rewrite-rule lemma :rhs))
                       (lemma-hyps (access rewrite-rule lemma :hyps))
                       (lemma-rune (access rewrite-rule lemma :rune))
                       (lemma-name (base-symbol lemma-rune))
                       (lemma-id (if (cddr lemma-rune) lemma-rune lemma-name))
                       (non-free (union-eq (intersection-domains sub
                                                                 start-alist)
                                           (set-difference-eq
                                            (strip-cars sub)
                                            (append (all-vars rhs)
                                                    (all-vars1-lst lemma-hyps
                                                                   nil))))))
                  (if non-free
                      (print-no-change2
                       "The variable~#0~[~/~/s~] ~&1 supplied by the ~
                        substitution in this instruction ~#0~[~/is~/are~] not ~
                        free for instantiation in the current context.~|"
                       (list (cons #\0 (zero-one-or-more (length non-free)))
                             (cons #\1 non-free)))
                    (mv-let
                     (subst-hyps unify-subst ttree2)
                     (unrelieved-hyps lemma-rune lemma-hyps alist
                                      hyps-type-alist instantiate-free w
                                      state pc-ens nil)
                     (pprogn
                      (let ((extra-alist (alist-difference-eq unify-subst
                                                              alist)))
                        (if extra-alist
                            (io? proof-builder nil state
                                 (abbreviations extra-alist sub
                                                lemma-id)
                                 (fms0 "~|Rewriting with ~x0 under the ~
                                        following extension of the ~
                                        substitution generated by matching ~
                                        that rewrite rule with the current ~
                                        term~#1~[ (after extending it with ~
                                        the substitution ~x2 supplied in the ~
                                        instruction)~/~]:~|~x3.~|"
                                       (list (cons #\0 lemma-id)
                                             (cons #\1 (if sub 0 1))
                                             (cons #\2 sub)
                                             (cons #\3 (untranslate-subst-abb
                                                        extra-alist
                                                        abbreviations
                                                        state)))))
                          (io? proof-builder nil state
                               (lemma-id)
                               (fms0 "~|Rewriting with ~x0.~|"
                                     (list (cons #\0 lemma-id))))))
                      (let ((runes (all-runes-in-ttree ttree2 nil)))
                        (if runes
                            (io? proof-builder nil state
                                 (runes)
                                 (fms0 "~|--NOTE-- Using the following runes ~
                                        in addition to the indicated rule:~%  ~
                                        ~x0.~|"
                                       (list (cons #\0 runes))))
                          state))
                      (let ((new-goals
                             (make-new-goals-fixed-hyps subst-hyps
                                                        assumptions
                                                        goal-name
                                                        depends-on)))
                        (mv-let
                         (changed-goal state)
                         (deposit-term-in-goal
                          (car goals) conc current-addr
                          (sublis-var unify-subst
                                      (access rewrite-rule lemma :rhs))
                          state)
                         (mv
                          (change-pc-state
                           pc-state
                           :instruction
                           (make-rewrite-instr lemma-id raw-sub
                                               instantiate-free)
                           :goals
                           (cons (change goal changed-goal
                                         :depends-on
                                         (+ depends-on (length new-goals)))
                                 (append new-goals (cdr goals)))
                           :local-tag-tree
                           (push-lemma lemma-rune ttree2))
                          state)))))))))))))))))

(defun applicable-linear-rules (current-term target-name-or-rune
                                             target-index wrld)

; See applicable-rewrite-rules for the analogous function for rewrite rules.

  (declare (xargs :guard (not (or (variablep current-term)
                                  (fquotep current-term)
                                  (flambdap (ffn-symb current-term))))))
  (applicable-linear-rules1
   current-term
   (getpropc (ffn-symb current-term) 'linear-lemmas nil wrld)
   1 target-name-or-rune target-index))

(defun make-linear-instr (lemma-id raw-subst instantiate-free)
  (list* (make-pretty-pc-command :apply-linear)
         lemma-id
         (cond (instantiate-free (list raw-subst instantiate-free))
               (raw-subst (list raw-subst))
               (t nil))))

(define-pc-primitive apply-linear (&optional rule-id raw-sub instantiate-free)

; Warning: Keep this in sync with the proof-builder rewrite command.

  (mv-let
   (erp sub state)
   (translate-subst-abb raw-sub abbreviations state)
   (if erp
       (print-no-change2 "~x0 failed."
                         (list (cons #\0 (cons :rewrite args))))
     (let ((name (and (symbolp rule-id) rule-id))
           (rune (and (consp rule-id)
                      (member-eq (car rule-id) '(:linear))
                      rule-id))
           (index (if (and (integerp rule-id) (< 0 rule-id))
                      rule-id
                    (if rule-id
                        nil
                      1)))
           (pc-ens (make-pc-ens pc-ens state))
           (w (w state))
           (current-term (fetch-term conc current-addr))
           (assumptions (union-equal hyps (governors conc current-addr))))
       (cond
        ((or (variablep current-term)
             (fquotep current-term)
             (flambdap (ffn-symb current-term)))
         (print-no-change2
          "It is only possible to apply linear rules to terms that are not ~
           variables, (quoted) constants, or applications of lambda ~
           expressions.  However, the current term is:~%~ ~ ~y0.~|"
          (list (cons #\0 current-term))))
        ((not (or name index rune))
         (print-no-change2
          "The rule-id argument to REWRITE must be a name, a positive ~
           integer, or a :linear rune, but ~x0 is none of these.~|"
          (list (cons #\0 rule-id))))
        (t
         (mv-let
          (flg hyps-type-alist ttree)
          (hyps-type-alist assumptions pc-ens w state)
          (declare (ignore ttree))
          (if flg
              (print-no-change2
               "Contradiction in the hypotheses!~%The S command should ~
                complete this goal.~|")
            (let ((app-linear-rules
                   (applicable-linear-rules
                    current-term (or name rune) index w)))
              (if (null app-linear-rules)
                  (if (and index (> index 1))
                      (print-no-change2
                       "There are fewer than ~x0 applicable linear rules.~%"
                       (list (cons #\0 index)))
                    (print-no-change2 "There are no applicable linear rules.~%"))
                (let* ((sar (car app-linear-rules))
                       (lemma (access sar sar :lemma))
                       (start-alist (access sar sar :alist))
                       (alist (append start-alist sub))
                       (lemma-concl (access linear-lemma lemma :concl))
                       (lemma-hyps (access linear-lemma lemma :hyps))
                       (lemma-rune (access linear-lemma lemma :rune))
                       (lemma-name (base-symbol lemma-rune))
                       (lemma-id (if (cddr lemma-rune) lemma-rune lemma-name))
                       (non-free (union-eq (intersection-domains sub
                                                                 start-alist)
                                           (set-difference-eq
                                            (strip-cars sub)
                                            (append (all-vars lemma-concl)
                                                    (all-vars1-lst lemma-hyps
                                                                   nil))))))
                  (if non-free
                      (print-no-change2
                       "The variable~#0~[~/~/s~] ~&1 supplied by the ~
                        substitution in this instruction ~#0~[~/is~/are~] not ~
                        free for instantiation in the current context.~|"
                       (list (cons #\0 (zero-one-or-more (length non-free)))
                             (cons #\1 non-free)))
                    (mv-let
                     (subst-hyps unify-subst ttree2)
                     (unrelieved-hyps lemma-rune lemma-hyps alist
                                      hyps-type-alist instantiate-free w
                                      state pc-ens nil)
                     (pprogn
                      (let ((extra-alist (alist-difference-eq unify-subst
                                                              alist)))
                        (if extra-alist
                            (io? proof-builder nil state
                                 (abbreviations extra-alist sub
                                                lemma-id)
                                 (fms0 "~|Apply linear rule ~x0 under the ~
                                        following extension of the the ~
                                        substitution generated by matching ~
                                        that rule's trigger term with the ~
                                        current term ~#1~[ (after extending ~
                                        it with the substitution ~x2 supplied ~
                                        in the instruction)~/~]:  ~x3.~|"
                                       (list (cons #\0 lemma-id)
                                             (cons #\1 (if sub 0 1))
                                             (cons #\2 sub)
                                             (cons #\3 (untranslate-subst-abb
                                                        extra-alist
                                                        abbreviations
                                                        state)))))
                          (io? proof-builder nil state
                               (lemma-id)
                               (fms0 "~|Applying linear rule ~x0.~|"
                                     (list (cons #\0 lemma-id))))))
                      (let ((runes (all-runes-in-ttree ttree2 nil)))
                        (if runes
                            (io? proof-builder nil state
                                 (runes)
                                 (fms0 "~|--NOTE-- Using the following runes ~
                                        in addition to the indicated rule:~%  ~
                                        ~x0.~|"
                                       (list (cons #\0 runes))))
                          state))
                      (let ((new-goals
                             (make-new-goals-fixed-hyps subst-hyps
                                                        assumptions
                                                        goal-name
                                                        depends-on)))
                        (let ((changed-goal
                               (change goal (car goals)
                                       :hyps
                                       (append hyps
                                               (list
                                                (sublis-var unify-subst
                                                            lemma-concl)))
                                       :depends-on
                                       (+ depends-on (length new-goals)))))
                          (mv
                           (change-pc-state
                            pc-state
                            :instruction
                            (make-linear-instr lemma-id raw-sub
                                               instantiate-free)
                            :goals
                            (cons changed-goal
                                  (append new-goals (cdr goals)))
                            :local-tag-tree
                            (push-lemma lemma-rune ttree2))
                           state)))))))))))))))))

(define-pc-macro al (&rest args)
  (value (cons :apply-linear args)))

(define-pc-macro doc (&optional name)
  (let ((name (or name (make-official-pc-command 'doc))))
    (cond ((and (equal (assoc-eq :doc (ld-keyword-aliases state))
                       '(:DOC 1 XDOC))
                (function-symbolp 'colon-xdoc-initialized (w state)))
           (value `(lisp (if (colon-xdoc-initialized state)
                             (xdoc ',name)
                           (pprogn
                            (fms0 "Note: Using built-in :doc command.  To use ~
                                   :xdoc command, exit the proof-builder and ~
                                   run :doc in the top-level loop.~|~%")
                            (doc ',name))))))
          (t (value `(lisp (doc ',name)))))))

(define-pc-macro help (&optional name)
  (cond ((not (symbolp name))
         (pprogn
          (print-no-change "The argument for :HELP requires a symbol, but ~x0 ~
                            is not a symbol."
                           (list (cons #\0 name)))
          (value :fail)))
        (t (let ((name (if (equal (symbol-name name) "ALL")
                           'proof-builder-commands
                         (make-official-pc-command (or name 'help)))))
             (value `(doc ,name))))))

(defun pc-rewrite*-1
  (term type-alist geneqv iff-flg wrld rcnst old-ttree pot-lst normalize-flg
        rewrite-flg ens state repeat backchain-limit step-limit)

; This function may be called with a pot-lst of nil in the proof-builder, but
; need not be can figure out a good way to do linear there.  Also, note that
; rcnst can be anything (and is ignored) if rewrite-flg is not set.

  (mv-let (nterm old-ttree)
          (if normalize-flg
              (normalize term iff-flg type-alist ens wrld old-ttree
                         (backchain-limit wrld :ts))
            (mv term old-ttree))
          (sl-let (newterm ttree)
                  (if rewrite-flg
                      (let ((gstack nil))
                        (rewrite-entry
                         (rewrite nterm nil 'proof-builder)
                         :pequiv-info nil
                         :rdepth (rewrite-stack-limit wrld)
                         :step-limit step-limit
                         :obj '?
                         :fnstack nil
                         :ancestors nil
                         :simplify-clause-pot-lst pot-lst
                         :rcnst (change rewrite-constant rcnst
                                        :current-literal
                                        (make current-literal
                                              :atm nterm
                                              :not-flg nil))
                         :gstack gstack
                         :ttree old-ttree))
                    (mv 0 ; irrelevant step-limit
                        nterm old-ttree))
                  (declare (ignorable step-limit))
                  (cond
                   ((equal newterm nterm)
                    (mv step-limit newterm old-ttree state))
                   ((<= repeat 0)
                    (mv step-limit newterm ttree state))
                   (t
                    (pc-rewrite*-1 newterm type-alist geneqv iff-flg wrld rcnst
                                   ttree
                                   pot-lst normalize-flg rewrite-flg ens state
                                   (1- repeat) backchain-limit step-limit))))))

(defun pc-rewrite*
  (term type-alist geneqv iff-flg wrld rcnst old-ttree pot-lst normalize-flg
        rewrite-flg ens state repeat backchain-limit step-limit)
  (sl-let
   (newterm ttree state)
   (catch-step-limit
    (pc-rewrite*-1 term type-alist geneqv iff-flg wrld rcnst old-ttree pot-lst
                   normalize-flg rewrite-flg ens state repeat backchain-limit
                   step-limit))
   (cond ((eql step-limit -1)
          (mv step-limit term old-ttree state))
         (t
          (mv step-limit newterm ttree state)))))

(defun make-goals-from-assumptions (assumptions conc hyps current-addr goal-name start-index)
  (if assumptions
      (cons (make goal
                  :conc conc
                  :hyps (cons (dumb-negate-lit (car assumptions)) hyps)
                  :current-addr current-addr
                  :goal-name (cons goal-name start-index)
                  :depends-on 1)
            (make-goals-from-assumptions (cdr assumptions)
                                         conc hyps current-addr goal-name
                                         (1+ start-index)))
    nil))

(defun make-new-goals-from-assumptions (assumptions goal)
  (and assumptions
       (make-goals-from-assumptions
        assumptions
        (access goal goal :conc)
        (access goal goal :hyps)
        (access goal goal :current-addr)
        (access goal goal :goal-name)
        (access goal goal :depends-on))))

(defconst *default-s-repeat-limit* 10)

(defun hyps-type-alist-and-pot-lst (assumptions rcnst ens wrld state)

; Rcnst is a rewrite constant if we are to use linear arithmetic, else nil.

  (mv-let
    (flg type-alist ttree-or-fc-pair-lst)
    (hyps-type-alist assumptions ens wrld state)
    (cond
     ((or (not rcnst) ; see comment above
          flg)
      (mv flg type-alist nil ttree-or-fc-pair-lst))
     (t
      (mv-let
        (step-limit contradictionp pot-lst)
        (setup-simplify-clause-pot-lst
         (dumb-negate-lit-lst assumptions)
         nil ttree-or-fc-pair-lst type-alist rcnst wrld state
         *default-step-limit*)
        (declare (ignore step-limit))
        (cond
         (contradictionp
          (mv t nil nil
              (push-lemma
               *fake-rune-for-linear*
               (access poly contradictionp :ttree))))
         (t (mv nil type-alist pot-lst ttree-or-fc-pair-lst))))))))

(define-pc-primitive s (&rest args)
  (cond
   ((not (keyword-value-listp args))
    (print-no-change2
     "The argument list to S must be a KEYWORD-VALUE-LISTP, i.e. a list of ~
      the form (:kw-1 val-1 ... :kw-n val-n), where each of the arguments ~
      :kw-i is a keyword.  Your argument list ~x0 does not have this ~
      property.  Try (HELP S)."
     (list (cons #\0 args))))
   (t
    (let ((comm (make-official-pc-command 's))
          (w (w state))
          (current-term (fetch-term conc current-addr))
          (assumptions (union-equal hyps
                                    (flatten-ands-in-lit-lst
                                     (governors conc current-addr)))))
      (let ((pc-ens (make-pc-ens pc-ens state)))
        (mv-let
          (bcl-alist rst)
          (pair-keywords '(:backchain-limit :normalize :rewrite :repeat) args)
          (let* ((local-backchain-limit
                  (or (cdr (assoc-eq :backchain-limit bcl-alist)) 0))

; IF-normalization and rewriting will happen by default

                 (normalize
                  (let ((pair (assoc-eq :normalize bcl-alist)))
                    (if pair (cdr pair) t)))
                 (rewrite
                  (let ((pair (assoc-eq :rewrite bcl-alist)))
                    (if pair (cdr pair) t)))
                 (linear
                  (let ((pair (assoc-eq :linear bcl-alist)))
                    (if pair (cdr pair) rewrite)))
                 (repeat
                  (let ((pair (assoc-eq :repeat bcl-alist)))
                    (if pair
                        (if (equal (cdr pair) t)
                            *default-s-repeat-limit*
                          (cdr pair))
                      0))))
            (cond
             ((not (natp repeat))
              (print-no-change2
               "The :REPEAT argument provided to S (or a command that invoked ~
                S), which was ~x0, is illegal. ~ It must be T or a natural ~
                number."
               (list (cons #\0 repeat))))
             ((not (natp local-backchain-limit))
              (print-no-change2
               "The :BACKCHAIN-LIMIT argument provided to S (or a command ~
                that invoked S), which was ~x0, is illegal.  It must be NIL ~
                or a natural number."
               (list (cons #\0 local-backchain-limit))))
             ((not (or normalize rewrite))
              (print-no-change2 "You may not specify in the S command that ~
                                 neither IF normalization nor rewriting is to ~
                                 take place."))
             ((and (null rewrite)
                   (or (assoc-eq :backchain-limit bcl-alist)
                       (assoc-eq :repeat bcl-alist)
                       rst))
              (print-no-change2 "When the :REWRITE NIL option is specified, ~
                                 it is not allowed to provide arguments other ~
                                 than :NORMALIZE T.  The argument list ~x0 ~
                                 violates this requirement."
                                (list (cons #\0 args))))
             (t
              (mv-let
                (key-alist new-rst)
                (pair-keywords '(:in-theory :hands-off :expand) rst)
                (declare (ignore key-alist))
                (cond
                 (new-rst
                  (print-no-change2
                   "The arguments to the S command must all be &KEY ~
                    arguments, which should be among ~&0.  Your argument list ~
                    ~x1 violates this requirement."
                   (list (cons #\0 '(:rewrite :normalize :backchain-limit
                                              :repeat :in-theory :hands-off
                                              :expand))
                         (cons #\1 args))))
                 (t
                  (mv-let
                    (erp hint-settings state)
                    (translate-hint-settings
                     comm "Goal" rst
                     (if args (cons comm (car args)) comm)
                     w state)
                    (cond
                     (erp (print-no-change2 "S failed."))
                     (t
                      (let ((base-rcnst
                             (and rewrite
                                  (change
                                   rewrite-constant
                                   *empty-rewrite-constant*
                                   :current-enabled-structure pc-ens
                                   :force-info t))))
                        (mv-let
                          (flg hyps-type-alist pot-lst ttree)
                          (hyps-type-alist-and-pot-lst assumptions
                                                       (and linear base-rcnst)
                                                       pc-ens w state)
                          (cond
                           (flg
                            (cond
                             ((or (null current-addr) ; optimization
                                  (equal assumptions hyps)
                                  (mv-let (flg hyps-type-alist ttree)
                                    (hyps-type-alist hyps pc-ens w state)
                                    (declare (ignore hyps-type-alist
                                                     ttree))
                                    flg))
                              (pprogn
                               (io? proof-builder nil state
                                    nil
                                    (fms0 "~|Goal proved:  Contradiction in ~
                                           the hypotheses!~|"))
                               (mv (change-pc-state
                                    pc-state
                                    :goals
                                    (cond ((tagged-objects 'assumption ttree)

; See the comment in define-pc-primitive about leaving the top goal on the top
; of the :goals stack.

                                           (cons (change goal (car goals)
                                                         :conc *t*)
                                                 (cdr goals)))
                                          (t (cdr goals)))
                                    :local-tag-tree ttree)
                                   state)))
                             (t
                              (print-no-change2
                               "A contradiction was found in the current ~
                                context using both the top-level hypotheses ~
                                and the IF tests governing the current term, ~
                                but not using the top-level hypotheses alone. ~
                                ~ You may want to issue the TOP command and ~
                                then issue s-prop to prune some branches of ~
                                the conclusion."))))
                           (t
                            (mv-let
                              (erp local-rcnst state)
                              (if rewrite
                                  (load-hint-settings-into-rcnst
                                   hint-settings
                                   base-rcnst
                                   nil w 'acl2-pc::s state)
                                (value nil))
                              (pprogn
                               (if erp
                                   (io? proof-builder nil state
                                        nil
                                        (fms0 "~|Note: Ignoring the above ~
                                               theory invariant error.  ~
                                               Proceeding...~|"))
                                 state)
                               (if rewrite
                                   (maybe-warn-about-theory-from-rcnsts
                                    base-rcnst local-rcnst :s pc-ens w state)
                                 state)
                               (sl-let
                                (new-term new-ttree state)
                                (pc-rewrite*
                                 current-term
                                 hyps-type-alist
                                 (geneqv-at-subterm-top conc current-addr
                                                        pc-ens w)
                                 (term-id-iff conc current-addr t)
                                 w local-rcnst nil
                                 pot-lst normalize rewrite
                                 pc-ens state repeat local-backchain-limit
                                 (initial-step-limit w state))
                                (pprogn
                                 (f-put-global 'last-step-limit step-limit state)
                                 (if (equal new-term current-term)
                                     (print-no-change2
                                      "No simplification took place.")
                                   (pprogn
                                    (mv-let
                                      (new-goal state)
                                      (deposit-term-in-goal
                                       (car goals)
                                       conc current-addr new-term state)
                                      (mv (change-pc-state
                                           pc-state
                                           :goals
                                           (cons new-goal (cdr goals))
                                           :local-tag-tree new-ttree)
                                          state)))))))))))))))))))))))))))

;; The proof-builder's enabled state will be either the global enabled
;; state or else a local one.  The proof-builder command :IN-THEORY
;; takes zero or one arguments, the former specifying ``use the global
;; enabled state'' and the latter specifying ``create a local enabled
;; state from the current proof-builder enabled state by evaluating
;; the theory form that is given.''  This is an easy design to
;; implement:  we'll use NIL in the pc-ens component of the pc-state
;; to mean that we should use the global state, and otherwise we'll
;; store an enabled structure with a root name particular to Pc-ACL2.
;; A subtlety is that (in-theory (current-theory :here)) is not quite
;; equivalent to (in-theory).  The difference is that the former
;; stores a copy of the current global enabled state in the current
;; proof-builder state, and that's what will stay there even if the
;; global state is changed, while the latter stores NIL in the current
;; proof-builder state, which means that we'll use whatever is the
;; current global enabled state at the time.

;; I expect that this design will be pretty robust, in the sense that
;; it won't cause hard errors even when the user makes global changes
;; to the ACL2 world and then re-enters an interactive verification.
;; That's because the index-of-last-enabling component of an enabled
;; structure always protects it against inappropriate AREF1 calls
;; in ENABLED-NUMEP.

(defun build-pc-enabled-structure-from-ens (new-suffix ens)
  (let* ((new-name-root
          '(#\P #\C #\- #\E #\N #\A #\B
            #\L #\E #\D #\- #\A #\R #\R #\A #\Y #\-))
         (new-name (intern (coerce
                            (append new-name-root
                                    (explode-nonnegative-integer new-suffix
                                                                 10
                                                                 nil))
                            'string)
                           "ACL2"))
         (old-name (access enabled-structure ens :array-name))
         (old-alist (access enabled-structure ens :theory-array)))
    (change enabled-structure
            ens
            :theory-array
            (cons (list :header
                        :dimensions (dimensions old-name old-alist)
                        :maximum-length (maximum-length old-name old-alist)
                        :default (default old-name old-alist)
                        :name new-name)
                  (cdr old-alist))
            :array-name new-name
            :array-length (access enabled-structure ens :array-length)
            :array-name-root new-name-root
            :array-name-suffix new-suffix)))

(define-pc-primitive in-theory (&optional theory-expr)
  (let ((w (w state))
        (ens (ens state)))
    (if args
        (mv-let
         (erp hint-setting state)
         (translate-in-theory-hint theory-expr t 'acl2-pc::in-theory w
                                   state)
         (if erp
             (print-no-change2 "bad theory expression.")
           (let* ((new-suffix (pc-value next-pc-enabled-array-suffix))
                  (new-pc-ens1
                   (build-pc-enabled-structure-from-ens new-suffix ens)))
             (mv-let
              (erp new-pc-ens2 state)
              (load-theory-into-enabled-structure
               ;; this call compresses the appropriate array
               theory-expr hint-setting nil new-pc-ens1 nil nil w
               'acl2-pc::in-theory state)
              (cond
               (erp (print-no-change2 "bad theory expression."))
               (t
                (pprogn
                 (pc-assign next-pc-enabled-array-suffix (1+ new-suffix))
                 (maybe-warn-about-theory-simple
                  ens new-pc-ens2 :in-theory w state)
                 (mv (change-pc-state pc-state :pc-ens new-pc-ens2)
                     state))))))))
      (if (null pc-ens)
          (print-no-change2 "The proof-builder enabled/disabled state is ~
                             already set to agree with the global state, so ~
                             your IN-THEORY command is redundant.")
        (mv (change-pc-state pc-state :pc-ens nil)
            state)))))

(define-pc-atomic-macro s-prop (&rest names)
  (value `(s :in-theory ,(if names
                             `(union-theories ',names
                                              (theory 'minimal-theory))
                           '(theory 'minimal-theory)))))

(define-pc-atomic-macro x (&rest args)
  (value `(do-strict (expand t) (succeed (s ,@args)))))

;; It was tempting to use the rewrite command to implement expand, but
;; this didn't really allow for expanding to keep lambdas or for the
;; issue of how to deal with guards.  So I'll keep :definition rules
;; separate from :rewrite rules.

(define-pc-primitive expand (&optional
                             ;; nil means eliminate the lambda:
                             do-not-expand-lambda-flg)
  (let ((w (w state))
        (term (fetch-term conc current-addr)))
    (cond
     ((or (variablep term)
          (fquotep term))
      (print-no-change2
       "It is impossible to expand a variable or a constant."))
     ((and do-not-expand-lambda-flg
           (flambdap (ffn-symb term)))
      (print-no-change2
       "Expansion of lambda terms is disabled when do-not-expand-lambda-flg = ~
        t; see :DOC acl2-pc::expand."))
     (t
      (let* ((fn (ffn-symb term))
             (def-body (and (not (flambdap fn))
                            (def-body fn w)))
             (formals (and def-body (access def-body def-body :formals)))
             (equiv (and def-body (access def-body def-body :equiv)))
             (body (if (flambdap fn)
                       (lambda-body fn)
                     (and def-body
                          (latest-body (fcons-term fn formals)
                                       (access def-body def-body
                                               :hyp)
                                       (access def-body def-body
                                               :concl))))))
        (cond
         ((null body)
          (assert$ (not (flambdap fn)) ; else surprising null body for lambda
                   (print-no-change2
                    "Expansion failed.  Apparently function ~x0 is ~
                     constrained, not defined."
                    (list (cons #\0 fn)))))
         ((and (not (eq equiv 'equal)) ; optimization
               (not (flambdap fn))
               (not (geneqv-refinementp
                     equiv
                     (geneqv-at-subterm-top conc
                                            current-addr
                                            (make-pc-ens pc-ens state)
                                            w)
                     w)))
          (print-no-change2
           "Expansion failed: the equivalence relation for the definition ~
            rule ~x0 is ~x1, which is not sufficient to maintain in the ~
            current context."
           (list (cons #\0 (base-symbol (access def-body def-body :rune)))
                 (cons #\1 equiv))))
         (t
          (let ((new-term
                 (cond
                  (do-not-expand-lambda-flg ; hence not (flambdap fn)
                   (fcons-term (make-lambda formals body)
                               (fargs term)))
                  (t
                   (subcor-var (if (flambdap fn)
                                   (lambda-formals fn)
                                 formals)
                               (fargs term)
                               body)))))
            (mv-let (new-goal state)
              (deposit-term-in-goal
               (car goals) conc current-addr
               new-term
               state)
              (mv (change-pc-state
                   pc-state
                   :goals
                   (cons new-goal (cdr goals))
                   :local-tag-tree
                   (if (flambdap fn)
                       nil
                     (push-lemma? (access def-body def-body
                                          :rune)
                                  nil)))
                  state))))))))))

(define-pc-atomic-macro x-dumb ()
  (value `(expand t)))

;; **** consider unwinding the effect if there is no change
(define-pc-macro bookmark (tag &rest instr-list)
  (value `(do-all (comment :begin ,tag)
                  ,@instr-list
                  (comment :end ,tag))))

(defun change-last (lst val)
  (if (consp lst)
      (if (consp (cdr lst))
          (cons (car lst)
                (change-last (cdr lst) val))
        (list val))
    lst))

(defun assign-event-name-and-rule-classes (event-name rule-classes state)
  (let* ((state-stack (state-stack))
         (triple (event-name-and-types-and-raw-term state-stack))
         (old-event-name (car triple))
         (old-rule-classes (cadr triple))
         (old-raw-term (caddr triple)))
    (pc-assign state-stack
               (change-last state-stack
                            (change pc-state
                                    (car (last state-stack))
                                    :instruction
                                    (list :start
                                          (list (or event-name old-event-name)
                                                (or rule-classes old-rule-classes)
                                                old-raw-term)))))))

(defun save-fn (name ss-alist state)
  (pprogn
   (assign-event-name-and-rule-classes name nil state)
   (pc-assign
    ss-alist
    (put-assoc-eq name
                  (cons (state-stack) (old-ss))
                  ss-alist))))

(define-pc-macro save (&optional name do-it-flg)
  (cond
   ((not (symbolp name))
    (pprogn
     (print-no-change
      "The first argument supplied to ~x0 must be a symbol, but ~x1 is not a ~
       symbol.~@2"
      (list (cons #\0 :save)
            (cons #\1 name)
            (cons #\2
                  (cond ((and (consp name)
                              (eq (car name) 'quote)
                              (consp (cdr name))
                              (symbolp (cadr name))
                              (null (cddr name)))
                         (msg "  Perhaps you intended to submit the form ~x0."
                              `(:save ,(cadr name)
                                      ,@(and do-it-flg
                                             (list do-it-flg)))))
                        (t "")))))
     (value :fail)))
   (t
    (let ((name (or name (car (event-name-and-types-and-raw-term state-stack))))
          (ss-alist (ss-alist)))
      (if name
          (mv-let
           (erp reply state)
           (if (and (assoc-eq name ss-alist)
                    (null do-it-flg))
               (acl2-query 'acl2-pc::save
                           '("The name ~x0 is already associated with a ~
                              state-stack.  Do you really want to overwrite ~
                              that existing value?"
                             :y t :n nil)
                           (list (cons #\0 name))
                           state)
             (mv nil t state))
           (declare (ignore erp))
           (if reply
               (pprogn (save-fn name ss-alist state)
                       (value :succeed))
             (pprogn (print-no-change "save aborted.")
                     (value :fail))))
        (pprogn (print-no-change
                 "You can't SAVE with no argument, because you didn't ~
                  originally enter VERIFY using an event name.  Try (SAVE ~
                  <event_name>) instead.")
                (value :fail)))))))

(defmacro retrieve (&optional name)
  `(retrieve-fn ',name state))

(define-pc-macro retrieve ()
  (pprogn (print-no-change "RETRIEVE can only be used ouside the ~
                            interactive loop.  Please exit first.  To ~
                            save your state upon exit, use EX rather than EXIT.")
          (value :fail)))

(defun unsave-fn (name state)
  (pc-assign ss-alist
             (remove1-assoc-eq name (ss-alist))))

(defmacro unsave (name)
  `(unsave-fn ',name state))

(define-pc-help unsave (&optional name)
  (let ((name (or name (car (event-name-and-types-and-raw-term state-stack)))))
    (if (null name)
        (print-no-change "You must specify a name to UNSAVE, because you didn't ~
                          originally enter VERIFY using an event name.")
      (if (assoc-eq name (ss-alist))
          (pprogn (unsave-fn name state)
                  (io? proof-builder nil state
                       (name)
                       (fms0 "~|~x0 removed from saved state-stack alist.~%"
                             (list (cons #\0 name)))))
        (print-no-change "~|~x0 is does not have a value on the saved ~
                          state-stack alist.~%"
                         (list (cons #\0 name)))))))

(defun show-retrieved-goal (state-stack state)
  (let ((raw-term (caddr (event-name-and-types-and-raw-term state-stack))))
    (assert$ raw-term
             (fmt-abbrev "~|~%Resuming proof attempt for~|~y0."
                         (list (cons #\0 raw-term))
                         0
                         (proofs-co state)
                         state
                         "~%"))))

(defun retrieve-fn (name state)
  (let ((ss-alist (ss-alist)))
    (cond
     ((f-get-global 'in-verify-flg state)
      (er soft 'retrieve
          "You are apparently already inside the VERIFY interactive loop.  It is ~
           illegal to enter such a loop recursively."))
     ((null ss-alist)
      (pprogn (io? proof-builder nil state
                   nil
                   (fms0 "Sorry -- there is no saved interactive proof to ~
                          re-enter! Perhaps you meant (VERIFY) rather than ~
                          (RETRIEVE).~|"))
              (value :invisible)))
     ((null name)
      (if (equal (length ss-alist) 1)
          (retrieve-fn (caar ss-alist) state)
        (pprogn (io? proof-builder nil state
                     (ss-alist)
                     (fms0 "Please specify an interactive verification to ~
                            re-enter.  Your options are ~&0.~%(Pick one of the ~
                            above:) "
                           (list (cons #\0 (strip-cars ss-alist)))))
                (mv-let (erp val state)
                        (with-infixp-nil
                         (read-object *standard-oi* state))
                        (declare (ignore erp))
                        (retrieve-fn val state)))))
     ((not (symbolp name))
      (er soft 'retrieve
          "The argument supplied to ~x0 must be a symbol, but ~x1 is not a ~
           symbol.~@2"
          'retrieve
          name
          (cond ((and (consp name)
                      (eq (car name) 'quote)
                      (consp (cdr name))
                      (symbolp (cadr name))
                      (null (cddr name)))
                 (msg "  Perhaps you intended to submit the form ~x0."
                      `(retrieve ,(cadr name))))
                (t ""))))
     (t
      (let* ((ss-pair (cdr (assoc-eq name ss-alist)))
             (saved-ss (car ss-pair))
             (saved-old-ss (cdr ss-pair)))
        (if saved-ss
            (pprogn (pc-assign old-ss saved-old-ss)
                    (pc-assign state-stack saved-ss)
                    (show-retrieved-goal saved-ss state)
                    (verify))
          (pprogn (io? proof-builder nil state
                       (name)
                       (fms0 "~|Sorry -- There is no interactive proof saved ~
                              under the name ~x0.~|"
                             (list (cons #\0 name))))
                  (value :invisible))))))))

(defun print-all-goals (goals state)
  (if (null goals)
      state
    (pprogn (print-pc-goal (car goals))
            (print-all-goals (cdr goals) state))))

(define-pc-help print-all-goals ()
  (print-all-goals (goals t) state))

(defmacro print-conc (&optional acl2::goal)
  `(let ((goal ,(or goal '(car (access pc-state (car (state-stack)) :goals)))))
     (io? proof-builder nil state
          (goal)
          (if goal
              (fms0
               "~%-------  ~x3  -------~|~q0~|"
               (list
                (cons #\0 (untranslate (access goal goal :conc) t (w state)))
                (cons #\3 (access goal goal :goal-name))))
            (fms0 "~%No goal in CAR of state-stack.~|")))))

(defun print-all-concs (goals state)
  (declare (xargs :mode :program :stobjs state))
  (if (null goals)
      state
    (pprogn (print-conc (car goals))
            (print-all-concs (cdr goals) state))))

(define-pc-help print-all-concs ()
  (print-all-concs (acl2::goals t) state))

(defun gen-var-marker (x)
  (or (null x)
      (and (integerp x)
           (>= x 0))))

(defun translate-generalize-alist-1 (alist state-vars abbreviations state)
  ;; Takes an alist with doublets of the form (term var) and
  ;; returns an alist of the form (translated-term . var).
  ;; Returns an error triple.  However, no attempt is made in this
  ;; pass to generate new variable names for "variables" that are
  ;; actually natural numbers or NIL.  We'll wait to collect the new
  ;; variable names first.
  ;;    We'll wait to check for duplicate variables till after this phase.
  (cond
   ((null alist)
    (value nil))
   ((and (true-listp (car alist))
         (eql (length (car alist)) 2))
    (er-let*
     ((term (translate-abb
             (caar alist)
             abbreviations
             'translate-generalize-alist
             state))
      (var (if (gen-var-marker (cadar alist))
               (value (cadar alist))
             ;; I could call translate directly here
             (translate-abb
              (cadar alist)
              nil
              'translate-generalize-alist
              state))))
     (cond
      ((member-eq var state-vars)
       (er soft :generalize
           "The variable ~x0 already appears in the current goals of ~
            the proof-builder state, and hence is not legal as a ~
            generalization variable."
           var))
      ((or (variablep var) (gen-var-marker var))
       ;; The second disjunct above is actually subsumed by the first,
       ;; but I'll leave it in for clarity.
       (mv-let
        (erp val state)
        (translate-generalize-alist-1 (cdr alist) state-vars abbreviations state)
        (if erp
            (mv erp val state)
          (value (cons (cons term var) val)))))
      (t
       (er soft :generalize
           "The second element of each doublet ~
            given to the GENERALIZE command must be a variable or ~
            natural number, but ~x0 is neither."
           (cadar alist))))))
   (t
    (er soft :generalize
        "Each argument to the GENERALIZE command must be a list of ~
         length 2, but ~x0 is not."
        (car alist)))))

(defun non-gen-var-markers (alist)
  ;; gets all the non-gen-var-markers from the cdrs of alist
  (if (consp alist)
      (if (gen-var-marker (cdar alist))
          (non-gen-var-markers (cdr alist))
        (cons (cdar alist)
              (non-gen-var-markers (cdr alist))))
    nil))

(defun find-duplicate-generalize-entries (alist var)
  (declare (xargs :guard (true-listp alist)))
  (if alist
      (if (eq (cadar alist) var)
          (cons (car alist)
                (find-duplicate-generalize-entries (cdr alist) var))
        (find-duplicate-generalize-entries (cdr alist) var))
    nil))

(defun translate-generalize-alist-2 (alist avoid-list)
  (declare (xargs :guard (true-listp alist)))
  (if alist
      (if (gen-var-marker (cdar alist))
          (let ((new-var (genvar 'genvar "_" (cdar alist) avoid-list)))
            (cons (cons (caar alist) new-var)
                  (translate-generalize-alist-2 (cdr alist) (cons new-var avoid-list))))
        (cons (car alist)
              (translate-generalize-alist-2 (cdr alist) avoid-list)))
    nil))

(defun translate-generalize-alist (alist state-vars abbreviations state)
  (er-let*
   ((alist1 (translate-generalize-alist-1 alist state-vars abbreviations state)))
   (let ((new-vars (non-gen-var-markers alist1)))
     (if (no-duplicatesp-equal new-vars)
         (value (translate-generalize-alist-2 alist1 (append new-vars state-vars)))
       (let* ((bad-var (car (duplicates new-vars)))
              (dup-entries
               (find-duplicate-generalize-entries alist bad-var)))
         (if (cdr dup-entries)
             (er soft 'acl2-pc::generalize
                 "The pairs ~&0 have the same variable, ~x1, and hence your ~
                  GENERALIZE instruction is illegal."
                 dup-entries bad-var)
           (value (er hard 'acl2-pc::generalize
                      "Bad call to translate-generalize-alist on ~%  ~x0."
                      (list alist state-vars abbreviations)))))))))

(defun all-vars-goals (goals)
  (if (consp goals)
      (union-eq (all-vars (access goal (car goals) :conc))
                (union-eq (all-vars1-lst (access goal (car goals) :hyps) nil)
                          (all-vars-goals (cdr goals))))
    nil))

(defun pc-state-vars (pc-state)
  (union-eq (all-vars1-lst (strip-cdrs (access pc-state pc-state :abbreviations)) nil)
            (all-vars-goals (access pc-state pc-state :goals))))

(define-pc-primitive generalize (&rest args)
  (cond
   (current-addr
    (print-no-change2
     "Generalization may only be applied at the top of the current goal.  Try TOP first."))
   ((null args)
    (print-no-change2
     "GENERALIZE requires at least one argument."))
   (t
    (mv-let
     (erp alist state)
     (translate-generalize-alist
      args (pc-state-vars pc-state) abbreviations state)
     (if erp
         (print-no-change2 "GENERALIZE failed.")
       (mv (change-pc-state
            pc-state
            ;; perhaps we should also adjust abbreviations, but I think that's
            ;; too complicated (for the user) -- it's simpler to tell him that
            ;; abbreviations are to be taken literally
            :goals
            (cons (change goal (car goals)
                          :hyps (sublis-expr-lst alist
                                                 (access goal (car goals) :hyps))
                          :conc (sublis-expr alist
                                             (access goal (car goals) :conc)))
                  (cdr goals)))
           state))))))

(define-pc-atomic-macro use (&rest args)
  (value `(prove :hints
                 (("Goal" :use ,args
                   :do-not-induct proof-builder
                   :do-not *do-not-processes*))
                 :otf-flg t)))

(define-pc-atomic-macro clause-processor (&rest cl-proc-hints)
  (value `(:prove :hints
                  (("Goal"
                    :clause-processor (,@cl-proc-hints)
                    :do-not-induct proof-builder
                    :do-not *do-not-processes*))
                  :otf-flg t)))

(define-pc-macro cl-proc (&rest cl-proc-hints)
  (value `(:clause-processor ,@cl-proc-hints)))

(define-pc-atomic-macro retain (arg1 &rest rest-args)
  (declare (ignore arg1 rest-args))
  (when-goals-trip
   (let* ((hyps (hyps t))
          (bad-nums (non-bounded-nums args 1 (length hyps))))
     (if bad-nums
         (pprogn (print-no-change
                  "The following are not in-range hypothesis numbers:  ~&0."
                  (list (cons #\0 bad-nums)))
                 (mv t nil state))
       (let ((retained-hyps (set-difference-eq (fromto 1 (length hyps)) args)))
         (if retained-hyps
             (value (cons :drop retained-hyps))
           (pprogn (print-no-change "All hypotheses are to be retained.")
                   (mv t nil state))))))))

(define-pc-atomic-macro reduce (&rest hints)
  (if (alistp hints)
      (value (list :prove :hints
                   (add-string-val-pair-to-string-val-alist!
                    "Goal"
                    :do-not-induct
                    'proof-builder
                    hints)
                   :otf-flg t))
    (pprogn (print-no-change
             "A REDUCE instruction must be of the form~%~ ~ ~
              (:REDUCE (goal_name_1 ...) ... (goal_name_n ...)),~%and hence ~
              your instruction,~%~ ~ ~x0,~%is not legal."
             (list (cons #\0 (cons :reduce hints))))
            (value :fail))))

(define-pc-macro run-instr-on-goal (instr goal-name)
  (when-goals-trip
   (if (equal goal-name (goal-name t))
       (value instr)
     (value `(protect (change-goal ,goal-name) ,instr)))))

(defun run-instr-on-goals-guts (instr goal-names)
  (declare (xargs :guard (true-listp goal-names)))
  (if goal-names
      (cons `(run-instr-on-goal ,instr ,(car goal-names))
            (run-instr-on-goals-guts instr (cdr goal-names)))
    nil))

(define-pc-macro run-instr-on-new-goals (instr existing-goal-names
                                               &optional must-succeed-flg)
  (value (cons 'do-strict
               (run-instr-on-goals-guts
                (if must-succeed-flg instr (list :succeed instr))
                (set-difference-equal (goal-names (goals t))
                                      existing-goal-names)))))

(define-pc-macro then (instr &optional completion must-succeed-flg)
  (value (list 'do-strict
               instr
               (list 'run-instr-on-new-goals
                     (or completion :reduce)
                     (goal-names (goals t))
                     must-succeed-flg))))

(define-pc-macro nil ()
  (value 'exit))

;; OK, here's a plan for free variables.  When the user thinks that
;; maybe he wants to introduce a free variable, he declares the
;; variable to be free at the time he wants to introduce it.  What
;; this really does is to introduce an abbreviation &v for (hide x),
;; where x is that variable.  Then if later in the proof he wants to
;; instantiate x with trm, then what happens is that the
;; add-abbreviation command is changed so that &v instead abbreviates
;; (hide trm).  The instructions are then replayed (or not, if the
;; user wants to cheat at this point -- or perhaps there's a fast
;; heuristic test on suitability of the PUT).

(define-pc-atomic-macro free (var)
  (er-let* ((var (trans0 var nil :free)))
           (if (variablep var)
               (value `(add-abbreviation ,var (hide ,var)))
             (pprogn (print-no-change
                      "The FREE command requires an argument that is a variable, ~
                       which ~x0 is not."
                      (list (cons #\0 var)))
                     (value :fail)))))

(define-pc-macro replay (&optional n replacement-instr)
  ;; So that I can use instructions-of-state-stack, I'll make
  ;; n 1-bigger than it ought to be.
  (if (or (null n) (and (integerp n) (> n 0)))
      (let* ((len (length state-stack))
             (n (and n (min (1+ n) len)))
             (instrs (instructions-of-state-stack
                      (if n (take n state-stack) state-stack)
                      nil)))
        (value `(do-strict (undo ,(1- (or n len)))
                           ,@(if replacement-instr
                                 (cons replacement-instr (cdr instrs))
                               instrs))))
    (pprogn (print-no-change "The optional argument to the REPLAY command ~
                              must be a positive integer, but ~x0 is not!"
                             (list (cons #\0 n)))
            (value :fail))))

(defun instr-name (instr)
  ;; assumes that instr is an official (stored) instruction
  (if (atom instr)
      instr
    (car instr)))

(defun pc-free-instr-p (var pc-state)
  (let ((instr (access pc-state pc-state :instruction)))
    (and (eq (instr-name instr) :free)
         (eq (cadr instr) var))))

(defun find-possible-put (var state-stack)
  ;; ***** Should beef this up sometime with heuristics for catching
  ;; when GENERALIZE or PROVE, for example, makes var "non-free" after all.
  ;; Attempts to find index (for undoing) of FREE command that introduced var, and if
  ;; it can't, then returns nil.
  (if state-stack
      (if (pc-free-instr-p var (car state-stack))
          1
        (let ((n (find-possible-put var (cdr state-stack))))
          (and n (1+ n))))
    nil))

(define-pc-macro put (var expr)
  (let ((n (find-possible-put var state-stack)))
    (if n
        (value `(do-strict (replay ,n
                                   (add-abbreviation ,var ,expr))
                           (remove-abbreviations ,var)))
      (pprogn (print-no-change "There is no FREE command for ~x0."
                               (list (cons #\0 var)))
              (value :fail)))))

(define-pc-macro reduce-by-induction (&rest hints)
  (if (alistp hints)
      (value (cons :reduce
                   (add-string-val-pair-to-string-val-alist
                    "Goal"
                    :induct
                    t
                    hints)))
    (pprogn (print-no-change
             "A REDUCE-BY-INDUCTION instruction must be of the form~%~ ~ ~
              (:REDUCE-BY-INDUCTION (goal_name_1 ...) ... (goal_name_n ...)),~%and hence ~
              your instruction,~%~ ~ ~x0,~%is not legal."
             (list (cons #\0 (cons :reduce-by-induction hints))))
            (value :fail))))

(define-pc-macro r (&rest args)
  (value (cons :rewrite args)))

(define-pc-atomic-macro sl (&optional backchain-limit)
  (value (if backchain-limit
             `(s :backchain-limit ,backchain-limit
                 :in-theory (union-theories (theory 'minimal-theory)
                                            (set-difference-theories
                                             (current-theory :here)
                                             (function-theory :here))))
           `(s :in-theory (union-theories (theory 'minimal-theory)
                                          (set-difference-theories
                                           (current-theory :here)
                                           (function-theory :here)))))))

(define-pc-atomic-macro elim ()
  (value (list :prove :otf-flg t
               :hints
               '(("Goal" :do-not-induct proof-builder
                  :do-not (set-difference-eq *do-not-processes*
                                             '(eliminate-destructors)))))))

(define-pc-macro ex ()
  (value '(do-strict save exit)))

(defun save-fc-report-settings ()
  (declare (xargs :guard t))
  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let* ((data (wormhole-data whs))
             (criteria (cdr (assoc-eq :CRITERIA data)))
             (flyp (cdr (assoc-eq :REPORT-ON-THE-FLYP data))))
        (set-wormhole-data
         whs
         (put-assoc-eq :CRITERIA-SAVED criteria
                       (put-assoc-eq :REPORT-ON-THE-FLYP-SAVED flyp
                                     data)))))
   nil))

(defun restore-fc-report-settings ()
  (declare (xargs :guard t))
  (wormhole-eval
   'fc-wormhole
   '(lambda (whs)
      (let* ((data (wormhole-data whs))
             (criteria-saved (cdr (assoc-eq :CRITERIA-SAVED data)))
             (flyp-saved (cdr (assoc-eq :REPORT-ON-THE-FLYP-SAVED data))))
        (set-wormhole-data
         whs
         (put-assoc-eq :CRITERIA criteria-saved
                       (put-assoc-eq :REPORT-ON-THE-FLYP flyp-saved
                                     data)))))
   nil))

(define-pc-help type-alist (&optional concl-flg govs-flg fc-report-flg
                                      alistp)
  (when-goals
   (let ((conc (conc t))
         (current-addr (current-addr t))
         (w (w state))
         (govs-flg (if (cdr args) govs-flg (not concl-flg))))
     (prog2$
      (and fc-report-flg
           (prog2$ (save-fc-report-settings)
                   (prog2$ (wormhole-eval ; (set-fc-criteria t) without state
                            'fc-wormhole
                            '(lambda (whs)
                               (set-wormhole-data
                                whs
                                (put-assoc-eq :CRITERIA
                                              '((t t t))
                                              (wormhole-data whs))))
                            nil)
                           (set-fc-report-on-the-fly t))))
      (mv-let
       (flg hyps-type-alist ttree)
       (hyps-type-alist
        (cond (concl-flg
               (union-equal (hyps t)
                            (cond (govs-flg
                                   (add-to-set-equal
                                    (dumb-negate-lit conc)
                                    (governors conc current-addr)))
                                  (t (list (dumb-negate-lit conc))))))
              (govs-flg (union-equal (hyps t)
                                     (governors conc current-addr)))
              (t (hyps t)))
        (make-pc-ens (pc-ens t) state)
        w
        state)
       (declare (ignore ttree))
       (prog2$
        (and fc-report-flg (restore-fc-report-settings))
        (if flg
            (io? proof-builder nil state
                 nil
                 (fms0 "*** Contradiction in the hypotheses! ***~%The S ~
                        command should complete this goal.~|"))
          (io? proof-builder nil state
               (hyps-type-alist alistp w)
               (pprogn
                (fms0 "~|Current type-alist, including forward chaining:~%")
                (prog2$ (cond ((eq alistp :raw)
                               (cw "~x0~|" hyps-type-alist))
                              (alistp
                               (cw "~x0~|"
                                   (alist-to-doublets
                                    (decode-type-alist hyps-type-alist))))
                              (t (print-type-alist hyps-type-alist w nil)))
                        state))))))))))

(define-pc-macro print-main ()
  (value '(print (caddr (event-name-and-types-and-raw-term (state-stack))))))

(define-pc-macro pso ()
  (value '(lisp (pso))))

(define-pc-macro psog ()
  (value '(lisp (psog))))

(define-pc-macro pso! ()
  (value '(lisp (pso!))))

(define-pc-macro acl2-wrap (x)
  (value `(lisp ,x)))

(defmacro acl2-wrap (x)

; This is provided for compatibility with an interface of the same name,
; provided for evaluating forms in raw Lisp.

  x)

(define-pc-macro check-proved-goal (goal-name cmd)
  (if (member-equal goal-name (goal-names (goals)))
      (er soft 'check-proved
          "The command ~x0 failed to prove the goal ~x1."
          cmd
          goal-name)
    (value 'succeed)))

(define-pc-macro check-proved (x)
  (when-goals-trip
   (let ((goal-name (goal-name)))
     (value
      `(do-all
        ,x
        (quiet (check-proved-goal ,goal-name ,x)))))))

(define-pc-atomic-macro forwardchain (hypn &optional hints quiet-flg)
  (when-goals-trip
   (let* ((hyps (hyps))
          (len (length hyps)))
     (cond
      ((null hyps)
       (mv-let
         (erp val state)
         (er soft 'forwardchain
             "The are no top-level hypotheses.  Hence it makes no sense to ~
              forward chain here.")
         (declare (ignore erp val))
         (value 'fail)))
      ((and (integerp hypn)
            (< 0 hypn)
            (<= hypn len))
       (let ((hyp (nth (1- hypn) hyps)))
         (case-match hyp
           (('implies ant consequent)
            (let ((instr
                   `(protect
                     (claim ,consequent 0 :do-not-flatten t)
                     (drop ,hypn)
                     ;; Now prove the consequent, leaving the original goal
                     ;; unproved (as the new hypothesis is not necessarily
                     ;; expected to match the conclusion).
                     change-goal
                     (demote ,hypn)
                     (claim ,ant
                            ,@(if hints
                                  '(:hints hints)
                                nil))
                     (demote ,len)
                     (check-proved
                      (s :backchain-limit 0
                         :in-theory (theory 'minimal-theory))))))
              (if quiet-flg
                  (value (list 'quiet instr))
                (value instr))))
           (& (mv-let
                (erp val state)
                (er soft 'forwardchain
                    "The ~n0 hypothesis~|  ~x1~|is not of the form (implies x ~
                     y)."
                    (list hypn)
                    (untrans0 (nth (1- hypn) hyps) t (abbreviations)))
                (declare (ignore erp val))
                (value 'fail))))))
      (t (mv-let
           (erp val state)
           (er soft 'forwardchain
               "The index ~x0 is not a valid index into the hypothesis list.  ~
                The valid indices are the integers from 1 to ~x1."
               hypn len)
           (declare (ignore erp val))
           (value 'fail)))))))

(define-pc-atomic-macro bdd (&rest kw-listp)
  (let ((bdd-hint (if (assoc-keyword :vars kw-listp)
                      kw-listp
                    (list* :vars nil kw-listp))))
    (value `(:prove :hints
                    (("Goal" :bdd ,bdd-hint))))))

(define-pc-macro runes (&optional flg)
  (value `(print (merge-sort-runes
                  (all-runes-in-ttree (,(if flg 'tag-tree 'local-tag-tree))
                                      nil)))))

(define-pc-macro lemmas-used (&optional flg)
  (value `(runes ,flg)))

(defun goal-terms (goals)

; Initially terms is empty, and we return the list of terms represented by
; goals.

  (if (endp goals)
      nil
    (cons (make-implication (access goal (car goals) :hyps)
                            (access goal (car goals) :conc))
          (goal-terms (cdr goals)))))

(defun wrap1-aux1 (kept-goal-names all-goals kept-goals removed-goals)

; Initially, accumulators removed-goals and kept-goals are empty.  We partition
; all-goals into those goals whose names are in kept-goal-names and the rest,
; returning (mv kept-goals1 removed-goals1) where removed-goals1 and
; kept-goals1 extend removed-goals and kept-goals, respectively.  The goals in
; all-goals are returned in the same order as they appear in all-goals.

  (cond
   ((endp all-goals)
    (mv (reverse kept-goals) (reverse removed-goals)))
   ((member-equal (access goal (car all-goals) :goal-name)
                  kept-goal-names)
    (wrap1-aux1 kept-goal-names (cdr all-goals)
                (cons (car all-goals) kept-goals)
                removed-goals))
   (t
    (wrap1-aux1 kept-goal-names (cdr all-goals)
                kept-goals
                (cons (car all-goals) removed-goals)))))

(defun wrap1-aux2 (sym index goals kept-goals removed-goals)
  (if (endp goals)
      (mv (reverse kept-goals) (reverse removed-goals))
    (let* ((goal (car goals))
           (goal-name (access goal goal :goal-name)))
      (if (and (consp goal-name)
               (eq sym (car goal-name))
               (<= index (cdr goal-name)))
          (wrap1-aux2 sym index (cdr goals)
                      kept-goals
                      (cons (car goals) removed-goals))
        (wrap1-aux2 sym index (cdr goals)
                    (cons (car goals) kept-goals)
                    removed-goals)))))

(define-pc-primitive wrap1 (&optional kept-goal-names)
  (let* ((current-goal (car goals))
         (current-goal-name (access goal current-goal :goal-name)))
    (cond
     ((not (true-listp kept-goal-names))
      (print-no-change2
       "The (optional) argument to wrap1 must be a true list of goal names.  ~
        ~x0 is thus illegal."
       (list (cons #\0 kept-goal-names))))
     ((and (null kept-goal-names)
           (not (and (consp current-goal-name)
                     (symbolp (car current-goal-name))
                     (integerp (cdr current-goal-name)))))
      (print-no-change2
       "The current goal's name, ~x0, is not of the form (SYMBOL . N) for ~
        integer N."
       (list (cons #\0 current-goal-name))))
     (t
      (mv-let (kept-goals removed-goals)
        (if kept-goal-names
            (wrap1-aux1 kept-goal-names (cdr goals) nil nil)
          (wrap1-aux2 (car current-goal-name)
                      (cdr current-goal-name)
                      (cdr goals) nil nil))
        (pprogn
         (io? proof-builder nil state
              (current-goal-name removed-goals)
              (if removed-goals
                  (fms0 "~|Conjoining the following goals into the current ~
                         goal, ~x0:~|  ~X1n~%"
                        (list (cons #\0 current-goal-name)
                              (cons #\1 (goal-names removed-goals))
                              (cons #\n nil)))
                (fms0 "~|NOTE (wrap1): There are no goals to conjoin into the ~
                       current goal, but we proceed anyhow.~%")))
         (mv (change-pc-state
              pc-state
              :goals
              (cons (change goal current-goal
                            :conc (conjoin
                                   (goal-terms
                                    (cons current-goal removed-goals)))
                            :hyps nil
                            :current-addr nil)
                    kept-goals))
             state)))))))

(define-pc-atomic-macro wrap (&rest instrs)
  (cond
   ((null instrs)
    (pprogn (print-no-change
             "Wrap takes at least one argument.")
            (value :fail)))
   (t (let ((goal-names (goal-names (goals t))))
        (value
         `(sequence
           ((do-all ,@instrs)
            (quiet (wrap1 ,goal-names))
            (lisp (io? proof-builder nil state
                       ()
                       (let ((new-current-goal-name
                              (access goal (car (goals)) :goal-name))
                             (state-stack (state-stack)))
                         (when-goals
                          (fms0 (if (member-equal new-current-goal-name
                                                  ',goal-names)
                                    "~|~%NOTE: Created no new goals.  Current ~
                                     goal:~%  ~X0n~|"
                                  "~|~%NOTE: Created ONLY one new goal, which ~
                                   is the current goal:~%  ~X0n~|")
                                (list (cons #\0 new-current-goal-name)
                                      (cons #\n nil))))))))
           t nil nil t))))))

(define-pc-atomic-macro wrap-induct (&optional raw-term)
  (value (if raw-term
             `(wrap (induct ,raw-term))
           `(wrap induct))))

(define-pc-macro finish-error (instrs)
  (er soft 'finish
      "~%The following instruction list created at least one subgoal:~|~x0~|"
      instrs))

(define-pc-macro finish (&rest instrs)
  (value `(then (check-proved (do-strict ,@instrs))
                (finish-error ,instrs)
                t)))

(defun show-geneqv (x with-runes-p)
  (cond ((endp x) nil)
        (t (cons (if with-runes-p
                     (list (access congruence-rule (car x) :equiv)
                           (access congruence-rule (car x) :rune))
                   (access congruence-rule (car x) :equiv))
                 (show-geneqv (cdr x) with-runes-p)))))

(define-pc-macro geneqv (&optional with-runes-p)
  (value `(print (show-geneqv
                  (geneqv-at-subterm-top (conc)
                                         (current-addr)
                                         (make-pc-ens (pc-ens) state)
                                         (w state))
                  ',with-runes-p))))

; Support for :instructions as hints

(defun goals-to-clause-list (goals)
  (if (endp goals)
      nil
    (cons (append (dumb-negate-lit-lst (access goal (car goals) :hyps))
                  (list (access goal (car goals) :conc)))
          (goals-to-clause-list (cdr goals)))))

(defun proof-builder-clause-list (state)
  (goals-to-clause-list (goals)))

(defun ttree-to-summary-data (ttree)
  (and ttree ; optimization
       (mv-let (use-names by-names cl-proc-fns)
         (cl-proc-data-in-ttree ttree nil)
         (make-summary-data
          :runes (all-runes-in-ttree ttree nil)
          :use-names (append use-names (use-names-in-ttree ttree nil))
          :by-names (append by-names (by-names-in-ttree ttree nil))
          :clause-processor-fns cl-proc-fns))))

(defun proof-builder-cl-proc-1 (cl instr-list state)
  (let ((ctx 'proof-builder-cl-proc))
    (cond
     ((null cl)
      (er soft ctx
          "There is no legal way to prove a goal of NIL!"))
     ((not (true-listp instr-list))
      (er soft ctx
          "The value of the :INSTRUCTIONS hint must be a true ~
           (null-terminated) list.  The value ~x0 is thus illegal."
          instr-list))
     (t
      (let ((term (make-implication (dumb-negate-lit-lst (butlast cl 1))
                                    (car (last cl))))
            (wrld (w state))
            (new-pc-depth (1+ (pc-value pc-depth))))
        (er-let* ((new-inhibit-output-lst
                   (cond
                    ((and (consp instr-list)
                          (true-listp (car instr-list))
                          (eq (make-pretty-pc-command (caar instr-list))
                              :COMMENT)
                          (eq (cadar instr-list) 'inhibit-output-lst))
                     (cond ((eq (caddar instr-list) :same)
                            (value (f-get-global 'inhibit-output-lst state)))
                           (t (chk-inhibit-output-lst (caddar instr-list)
                                                      :instructions
                                                      state))))
                    (t (value (union-eq '(prove proof-tree proof-builder)
                                        (f-get-global 'inhibit-output-lst
                                                      state))))))
                  (outputp (value (not (subsetp-eq
                                        '(prove proof-builder proof-tree)
                                        new-inhibit-output-lst)))))
          (state-global-let*
           ((inhibit-output-lst new-inhibit-output-lst)
            (pc-output (f-get-global 'pc-output state)))
           (mv-let
             (erp clause-list state)
             (pprogn (pc-assign pc-depth new-pc-depth)
                     (cond (outputp
                            (io? prove nil state
                                 (new-pc-depth)
                                 (fms0 "~|~%[[~x0> Executing ~
                                            proof-builder instructions]]~%~%"
                                       (list (cons #\0 new-pc-depth)))))
                           (t state))
                     (pc-assign next-pc-enabled-array-suffix
                                (1+ (pc-value
                                     next-pc-enabled-array-suffix)))
                     (mv-let
                       (erp pc-val state)
                       (pc-main term
                                (untranslate term t wrld)
                                nil ; event-name
                                nil ; rule-classes
                                instr-list
                                '(signal value) ; quit-conditions
                                t ; pc-print-prompt-and-instr-flg, suitable for :pso
                                nil ; in-verify-flg
                                state)
                       (pprogn
                        (cond (outputp (io? prove nil state
                                            (new-pc-depth)
                                            (fms0 "~|~%[[<~x0 Completed ~
                                                 proof-builder ~
                                                 instructions]]~%"
                                                  (list (cons #\0 new-pc-depth)))))
                              (t state))
                        (cond ((or erp (null pc-val))
                               (let ((name (intern
                                            (concatenate
                                             'string
                                             "ERROR"
                                             (coerce (explode-atom new-pc-depth
                                                                   10)
                                                     'string))
                                            "KEYWORD")))
                                 (pprogn
                                  (io? error nil state
                                       (name)
                                       (fms0 "~%Saving proof-builder error ~
                                            state; see :DOC instructions.  To ~
                                            retrieve:~|~x0"
                                             (list (cons #\0 `(retrieve ,name)))))
                                  (save-fn name (ss-alist) state)
                                  (er soft ctx
                                      "The above :INSTRUCTIONS hint failed.  ~
                                     For a discussion of ``failed'', follow ~
                                     the link to the SEQUENCE command under ~
                                     :DOC proof-builder-commands."))))
                              (t (value (proof-builder-clause-list
                                         state)))))))
             (cond (erp (silent-error state))
                   (t (value (cons clause-list (state-stack)))))))))))))

(defun proof-builder-cl-proc (cl instr-list state)
  (mv-let (erp clause-list/state-stack state)
    (proof-builder-cl-proc-1 cl instr-list state)
    (cond (erp (mv erp clause-list/state-stack state nil))
          (t (mv erp
                 (car clause-list/state-stack)
                 state
                 (let ((state-stack (cdr clause-list/state-stack)))
                   (and (consp state-stack)
                        (ttree-to-summary-data
                         (access pc-state
                                 (car state-stack)
                                 :tag-tree)))))))))

#+acl2-loop-only
(define-trusted-clause-processor
  proof-builder-cl-proc
  nil)

#+acl2-loop-only
(add-custom-keyword-hint :instructions
                         (splice-keyword-alist
                          :instructions
                          (list :clause-processor
                                (list :function
                                      'proof-builder-cl-proc
                                      :hint
                                      (kwote val)))
                          keyword-alist))
