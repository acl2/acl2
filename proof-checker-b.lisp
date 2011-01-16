; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Sciences
; University of Texas at Austin
; Austin, TX 78712-1188 U.S.A.

(in-package "ACL2")

(defmacro install-new-pc-meta-or-macro (command-type raw-name name formals doc body)
  `(progn ,(pc-meta-or-macro-defun raw-name name formals doc body)
          (add-pc-command ,name ',command-type)))

(defun define-pc-meta-or-macro-fn (command-type raw-name formals body)
  (let ((name (make-official-pc-command raw-name)) )
    (mv-let
     (doc body)
     (remove-doc
      (case command-type
            (meta "  (meta)")
            (macro "  (macro)")
            (atomic-macro "  (atomic macro)")
            (otherwise ""))
      body)
     `(install-new-pc-meta-or-macro ,command-type ,raw-name ,name
                                    ,formals ,doc ,body))))

(defmacro define-pc-meta (raw-name formals &rest body)

  ":Doc-Section Proof-checker

  define a proof-checker meta command~/

  Built-in proof-checker meta commands include ~c[undo] and ~c[restore], and
  others (~c[lisp], ~c[exit], and ~c[sequence]); ~pl[proof-checker-commands].
  The advanced proof-checker user can define these as well.  See ACL2
  source file ~c[proof-checker-b.lisp] for examples, and contact the ACL2
  implementors if those examples do not provide sufficient
  documentation.~/~/"

  (define-pc-meta-or-macro-fn 'meta raw-name formals body))

(defmacro define-pc-macro (raw-name formals &rest body)

  ":Doc-Section Proof-checker

  define a proof-checker macro command~/
  ~bv[]
  Example:
  (define-pc-macro ib (&optional term)
    (value
     (if term
         `(then (induct ,term) bash)
       `(then induct bash))))
  ~ev[]
  The example above captures a common paradigm:  one attempts to prove
  the current goal by inducting and then simplifying the resulting
  goals.  (~pl[proof-checker-commands] for documentation of the
  command ~c[then], which is itself a pc-macro command, and commands
  ~c[induct] and ~c[bash].)  Rather than issuing ~c[(then induct bash)], or
  worse yet issuing ~c[induct] and then issuing ~c[bash] for each resulting
  goals, the above definition of ~c[ib] would let you issue ~c[ib] and get the
  same effect.~/

  ~bv[]
  General Form:
  (define-pc-macro cmd args doc-string dcl ... dcl body)
  ~ev[]
  where ~c[cmd] is the name of the pc-macro than you want to define,
  ~c[args] is its list of formal parameters.  ~c[Args] may include lambda-list
  keywords ~c[&optional] and ~c[&rest]; ~pl[macro-args], but note that
  here, ~c[args] may not include ~c[&key] or ~c[&whole].

  The value of ~c[body] should be an ACL2 ``error triple,'' i.e., have the
  form ~c[(mv erp xxx state)] for some ~c[erp] and ~c[xxx].  If ~c[erp] is
  ~c[nil], then ~c[xxx] is handed off to the proof-checker's instruction
  interpreter.  Otherwise, evaluation typically halts.  We may write
  more on the full story later if there is interest in reading it.~/"

  (define-pc-meta-or-macro-fn 'macro raw-name formals body))

(defmacro define-pc-atomic-macro (raw-name formals &rest body)
  (define-pc-meta-or-macro-fn 'atomic-macro raw-name formals body))

(defmacro toggle-pc-macro (name &optional new-tp)
  (declare (xargs :guard (and (symbolp new-tp)
                              (or (null new-tp)
                                  (member-equal (symbol-name new-tp)
                                                '("MACRO" "ATOMIC-MACRO"))))))

  ":Doc-Section Proof-checker

  change an ordinary macro command to an atomic macro, or vice-versa~/
  ~bv[]
  Example:
  (toggle-pc-macro pro)
  ~ev[]
  Change ~c[pro] from an atomic macro command to an ordinary one (or
  vice-versa, if ~c[pro] happens to be an ordinary macro command)~/

  ~bv[]
  General Form:
  (toggle-pc-macro name &optional new-tp)
  ~ev[]
  If name is an
  atomic macro command then this turns it into an ordinary one, and
  vice-versa.  However, if ~c[new-tp] is supplied and not ~c[nil], then it
  should be the new type (the symbol ~c[macro] or ~c[atomic-macro], in any
  package), or else there is no change."

  `(toggle-pc-macro-fn ',(make-official-pc-command name) ',new-tp state))

(defmacro define-pc-primitive (raw-name formals &rest body)
  ;; I want to store the instruction automatically unless it's stored explicitly.
  ;; What I'll do is store the instruction at the end, unless there's already
  ;; one stored.  So, I'll store NIL as a starting point.  To implement this simply,
  ;; I'll impose the invariant that primitive commands never look at the instruction
  ;; field of the current state.
  ;;    Note that if I put add-pc-command on the untouchables list, then I prevent
  ;; the user from defining new primitive commands.  That's good, because I have
  ;; no control over what they do, since state-stack is only modified in the case
  ;; by the single stepper, and I allow that.
  (let ((name (make-official-pc-command raw-name)))
    (mv-let
     (doc body)
     (remove-doc "  (primitive)" body)
     `(progn
        ,(pc-primitive-defun-form raw-name name formals doc body)
        (add-pc-command ,name 'primitive)))))

(define-pc-primitive comment (&rest x)

  "insert a comment~/
  ~bv[]
  Example:
  (comment now begin difficult final goal)~/

  General Form:
  (comment &rest x)
  ~ev[]
  This instruction makes no change in the state except to insert the
  ~c[comment] instruction.

  Some comments can be used to improve the display of commands; see
  documentation for ~c[comm]."

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

  "drop top-level hypotheses~/
  ~bv[]
  Examples:
  (drop 2 3) -- drop the second and third hypotheses
  drop       -- drop all top-level hypotheses~/

  General Forms:
  (drop n1 n2 ...) -- Drop the hypotheses with the indicated indices.

  drop             -- Drop all the top-level hypotheses.
  ~ev[]
  ~st[Remark:]  If there are no top-level hypotheses, then the instruction
  ~c[drop] will fail.  If any of the indices is out of range, i.e. is not
  an integer between one and the number of top-level hypotheses
  ~c[(inclusive)], then ~c[(drop n1 n2 ...)] will fail."

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

  "evaluate the given form in Lisp~/
  ~bv[]
  Example:
  (lisp (assign xxx 3))~/

  General Form:
  (lisp form)
  ~ev[]
  Evaluate ~c[form].  The ~c[lisp] command is mainly of interest for side
  effects.  See also ~c[print], ~c[skip], and ~c[fail].

  The rest of the documentation for ~c[lisp] is of interest only to
  those who use it in macro commands.  If the Lisp evaluation (by
  ~c[trans-eval]) of form returns an ``error triple'' of the form
  ~c[(mv erp ((NIL NIL STATE) . (erp-1 val-1 &)) state)], then the
  ~c[lisp] command returns the appropriate error triple
  ~bv[]
  (mv (or erp erp-1)
      val-1
      state) .
  ~ev[]
  Otherwise, the ~c[trans-eval] of form must return an ``error triple''
  of the form ~c[(mv erp (cons stobjs-out val) &)], and the ~c[lisp]
  command returns the appropriate error triple
  ~bv[]
  (mv erp
      val
      state).
  ~ev[]

  Note that the output signature of the form has been lost.  The user
  must know the signature in order to use the output of the ~c[lisp]
  command.  Trans-eval, which is undocumented except by comments in
  the ACL2 source code, has replaced, in ~c[val], any occurrence of
  the current state or the current values of stobjs by simple symbols
  such as ~c[REPLACED-STATE].  The actual values of these objects may
  be recovered, in principle, from the ~c[state] returned and the
  ~c[user-stobj-alist] within that state.  However, in practice, the
  stobjs cannot be recovered because the user is denied access to
  ~c[user-stobj-alist].  The moral is: do not try to write macro
  commands that manipulate stobjs.  Should the returned ~c[val]
  contain ~c[REPLACED-STATE] the value may simply be ignored and
  ~c[state] used, since that is what ~c[REPLACED-STATE] denotes."

  (cond ((not (f-get-global 'in-verify-flg state))
         (er soft 'acl2-pc::lisp
             "You may only invoke the proof-checker LISP command when ~
              you are inside the interactive loop."))
        ((and (symbolp form)
              (or (eq form t)
                  (eq form nil)
                  (keywordp form)))
         (value form))
        (t
         (mv-let (erp stobjs-out/vals state)
                 (trans-eval form :lisp state t)
                 (let ((stobjs-out (car stobjs-out/vals))
                       (vals (cdr stobjs-out/vals)))
                 (if (equal stobjs-out *error-triple-sig*)
                     (mv (or erp (car vals)) (cadr vals) state)
                   (mv erp vals state)))))))

(define-pc-primitive fail-primitive ()
  (declare (ignore pc-state))
  (mv nil state))

(define-pc-macro fail (&optional hard)

  "cause a failure~/
  ~bv[]
  Examples:
  fail
  (fail t)~/

  General Form:
  (fail &optional hard)
  ~ev[]
  This is probably only of interest to writers of macro commands.
  The only function of ~c[fail] is to fail to ``succeed''.

  The full story is that ~c[fail] and ~c[(fail nil)] simply return
  ~c[(mv nil nil state)], while ~c[(fail hard)] returns ~c[(mv hard nil state)] if
  ~c[hard] is not ~c[nil].  See also ~c[do-strict], ~c[do-all], and ~c[sequence]."

  (if hard
      (value '(lisp (mv hard nil state)))
    (value 'fail-primitive)))

(define-pc-macro illegal (instr)

  "illegal instruction~/
  ~bv[]
  Example:
  (illegal -3)~/

  General Form:
  (illegal instruction)
  ~ev[]
  Probably not of interest to most users; always ``fails'' since it
  expands to the ~c[fail] command.

  The ~c[illegal] command is used mainly in the implementation.  For
  example, the instruction ~c[0] is ``read'' as ~c[(illegal 0)], since ~c[dive]
  expects positive integers.~/"

  (pprogn (print-no-change "Illegal interactive instruction, ~x0.~%  An instruction must be a ~
                            symbol or a proper list headed by a symbol."
                           (list (cons #\0 instr)))
          (value :fail)))

(defun chk-assumption-free-ttree-1 (ttree ctx)

  ;; Same as chk-assumption-free-ttree, but returns a value.

  (cond ((tagged-object 'assumption ttree)
         (er hard ctx
             "The 'assumption ~x0 was found in the final ttree!"
             (tagged-object 'assumption ttree)))
        ((tagged-object 'fc-derivation ttree)
         (er hard ctx
             "The 'fc-derivation ~x0 was found in the final ttree!"
             (tagged-object 'fc-derivation ttree)))
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

  "exit the interactive proof-checker~/
  ~bv[]
  Examples:
  exit                        -- exit the interactive proof-checker
  (exit append-associativity) -- exit and create a defthm
                                 event named append-associativity~/

  General Forms:

  exit --  Exit without storing an event.

  (exit event-name &optional rule-classes do-it-flg)
  Exit, and store an event.
  ~ev[]
  The command ~c[exit] returns you to the ACL2 loop.  At a later time,
  ~c[(verify)] may be executed to get back into the same proof-checker
  state, as long as there hasn't been an intervening use of the
  proof-checker (otherwise see ~c[save]).

  When given one or more arguments as shown above, ~c[exit] still returns
  you to the ACL2 loop, but first, if the interactive proof is
  complete, then it attempts create a ~c[defthm] event with the specified
  ~c[event-name] and ~c[rule-classes] (which defaults to ~c[(:rewrite)] if not
  supplied).  The event will be printed to the terminal, and then
  normally the user will be queried whether an event should really be
  created.  However, if the final optional argument ~c[do-it-flg] is
  supplied and not ~c[nil], then an event will be made without a query.

  For example, the form
  ~bv[]
  (exit top-pop-elim (:elim :rewrite) t)
  ~ev[]
  causes a ~c[defthm] event named ~c[top-pop-elim] to be created with
  rule-classes ~c[(:elim :rewrite)], without a query to the user (because
  of the argument ~c[t]).

  ~st[Remark:] it is permitted for ~c[event-name] to be ~c[nil].  In that case,
  the name of the event will be the name supplied during the original call of
  ~c[verify].  (See the documentation for ~c[verify] and ~c[commands].)  Also
  in that case, if ~c[rule-classes] is not supplied then it defaults to the
  rule-classes supplied in the original call of ~c[verify].

  ~c[Comments] on ``success'' and ``failure''.  An ~c[exit] instruction will
  always ``fail'', so for example, if it appears as an argument of a
  ~c[do-strict] instruction then none of the later (instruction) arguments
  will be executed.  Moreover, the ``failure'' will be ``hard'' if an
  event is successfully created or if the instruction is simply ~c[exit];
  otherwise it will be ``soft''.  See the documentation for ~c[sequence]
  for an explanation of hard and soft ``failures''.  An obscure but
  potentially important fact is that if the ``failure'' is hard, then
  the error signal is a special signal that the top-level interactive
  loop can interpret as a request to exit.  Thus for example, a
  sequencing command that turns an error triple ~c[(mv erp val state)]
  into ~c[(mv t val state)] would never cause an exit from the interactive
  loop.

  If the proof is not complete, then ~c[(exit event-name ...)] will not
  cause an exit from the interactive loop.  However, in that case it
  will print out the original user-supplied goal (the one that was
  supplied with the call to ~c[verify]) and the current list of
  instructions."

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
          (er-let*
           ((event-name
             (if event-name
                 (value event-name)
               (pprogn (io? proof-checker nil state
                            nil
                            (fms0 "Please supply an event name (or :A to ~
                                   abort)~%>> "))
                       (state-global-let*
                        ((infixp nil))
                        (read-object *standard-oi* state))))))
           (if (eq event-name :a)
               (pprogn (io? proof-checker nil state
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
                                    (if do-it-flg
                                        (value :y)
                                      (replay-query state))
                                    (declare (ignore erp))
                                    (case ans
                                          (:y (trans-eval event-form
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
                                                      (trans-eval event-form
                                                                  'acl2-pc::exit
                                                                  state
                                                                  t)))
                                          (:a (mv t '(nil . t) state))
                                          (otherwise (mv t '(nil . nil) state)))))

; We assume here that if DEFTHM returns without error, then it succeeds.

                           (if (or erp (null (car stobjs-out/vals)))
                               (if (eq (cdr stobjs-out/vals) t)
                                   (pprogn (io? proof-checker nil state
                                                nil
                                                (fms0 "~|Exit aborted.~%"))
                                           (mv nil nil state))
                                 (mv *pc-complete-signal* nil state))
                             (mv *pc-complete-signal* event-name state))))

; Otherwise, we have an incomplete proof.

               (pprogn (io? proof-checker nil state
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
      (pprogn (io? proof-checker nil state
                   nil
                   (fms0 "~|Exiting....~%"))
              (mv *pc-complete-signal* nil state)))))

(define-pc-meta undo (&optional n)

  "undo some instructions~/
  ~bv[]
  Examples:
  (undo 7)
  undo~/

  General Forms:

  (undo n) -- Undo the last n instructions.  The argument n should be
              a positive integer.

  undo     -- Same as (undo 1).
  ~ev[]
  ~st[Remark:]  To remove the effect of an ~c[undo] command, use ~c[restore].
  See the documentation for details.

  ~st[Remark:]  If the argument ~c[n] is greater than the total number of
  interactive instructions in the current session, then ~c[(undo n)] will
  simply take you back to the start of the session.

  The ~c[undo] meta command always ``succeeds''; it returns
  ~c[(mv nil t state)] unless its optional argument is supplied and of
  the wrong type (i.e. not a positive integer) or there are no
  instructions to undo."

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
                (io? proof-checker nil state
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
                  (io? proof-checker nil state
                       nil
                       (fms0 "Back to the start.~%")))
                (mv nil t state))))))

(define-pc-meta restore ()

  "remove the effect of an UNDO command~/
  ~bv[]
  Example and General Form:
  restore
  ~ev[]~/
  
  ~c[Restore] removes the effect of an ~c[undo] command.  This always works as
  expected if ~c[restore] is invoked immediately after ~c[undo], without
  intervening instructions.  However, other commands may also interact
  with ~c[restore], notably ``sequencing'' commands such as ~c[do-all],
  ~c[do-strict], ~c[protect], and more generally, ~c[sequence].

  ~st[Remark:]  Another way to control the saving of proof-checker state is
  with the ~c[save] command; see the documentation for ~c[save].

  The ~c[restore] command always ``succeeds''; it returns
  ~c[(mv nil t state)]."

  (let ((old-ss (pc-value old-ss)))
    (if (null old-ss)
        (pprogn (io? proof-checker nil state
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
        (io? proof-checker nil state
             (indexed-instrs)
             (fms0 (car (cdar indexed-instrs))
                   (cdr (cdar indexed-instrs))))
      (pprogn (io? proof-checker nil state
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

  "``succeed'' without doing anything~/
  ~bv[]
  Example and General Form:
  skip
  ~ev[]~/

  Make no change in the state-stack, but ``succeed''.  Same as
  ~c[(sequence nil)]."

  (value '(sequence-no-restore nil)))

(defmacro define-pc-help (name args &rest body)

  ":Doc-Section Proof-checker
  define a macro command whose purpose is to print something~/
  ~bv[]
  Example:
  (define-pc-help pp () 
    (if (goals t)
        (io? proof-checker nil state
             (state-stack)
             (fms0 \"~~|~~y0~~|\"
                   (list (cons #\0 
                               (fetch-term (conc t)
                                           (current-addr t))))))
      (print-all-goals-proved-message state)))~/

  General Form:
  (define-pc-help name args &rest body)
  ~ev[]
  This defines a macro command named ~c[name], as explained further below.
  The ~c[body] should (after removing optional declarations) be a form
  that returns ~c[state] as its single value.   Typically, it will just
  print something.

  What ~c[(define-pc-help name args &rest body)] really does is to create
  a call of ~c[define-pc-macro] that defines ~c[name] to take arguments ~c[args],
  to have the declarations indicated by all but the last form in ~c[body],
  and to have a body that (via ~c[pprogn]) first executes the form in the
  last element of body and then returns a call to the command ~c[skip]
  (which will return ~c[(mv nil t state)])."

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

  "display instructions from the current interactive session~/
  ~bv[]
  Examples:
  commands
  (commands 10 t)~/

  General Forms:

  commands or (commands nil)
  Print out all the instructions (in the current state-stack) in
  reverse order, i.e. from the most recent instruction to the starting
  instruction.

  (commands n) [n a positive integer]
  Print out the most recent n instructions (in the current
  state-stack), in reverse order.

  (commands x abbreviate-flag)
  Same as above, but if abbreviate-flag is non-NIL, then do not
  display commands between ``matching bookends''.  See documentation
  for comm for an explanation of matching bookends.
  ~ev[]
  ~st[Remark]:  If there are more than ~c[n] instructions in the state-stack,
  then ~c[(commands n)] is the same as ~c[commands] (and also,
  ~c[(commands n abb)] is the same as ~c[(commands nil abb)])."

  (if (and n (not (and (integerp n) (> n 0))))
      (io? proof-checker nil state
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

  "display instructions from the current interactive session~/
  ~bv[]
  Examples:
  comm
  (comm 10)~/

  General Form:
  (comm &optional n)
  ~ev[]
  Prints out instructions in reverse order.  This is actually the same
  as ~c[(commands n t)] ~-[] or, ~c[(commands nil t)] if ~c[n] is not supplied.  As
  explained in the documentation for ~c[commands], the final argument of ~c[t]
  causes suppression of instructions occurring between so-called
  ``matching bookends,'' which we now explain.

  A ``begin bookend'' is an instruction of the form
  ~bv[]
  (COMMENT :BEGIN x . y).
  ~ev[]
  Similarly, an ``end bookend'' is an instruction of the form
  ~bv[]
  (COMMENT :END x' . y').
  ~ev[]
  The ``name'' of the first bookend is ~c[x] and the ``name'' of the
  second bookend is ~c[x'].  When such a pair of instructions occurs in
  the current state-stack, we call them ``matching bookends'' provided
  that they have the same name (i.e. ~c[x] equals ~c[x']) and if no other
  begin or end bookend with name ~c[x] occurs between them.  The idea now
  is that ~c[comm] hides matching bookends together with the instructions
  they enclose.  Here is a more precise explanation of this
  ``hiding''; probably there is no value in reading on!

  A ~c[comm] instruction hides bookends in the following manner.  (So does
  a ~c[comment] instruction when its second optional argument is supplied
  and non-~c[nil].)  First, if the first argument ~c[n] is supplied and not
  ~c[nil], then we consider only the last ~c[n] instructions from the
  state-stack; otherwise, we consider them all.  Now the resulting
  list of instructions is replaced by the result of applying the
  following process to each pair of matching bookends:  the pair is
  removed, together with everything in between the begin and end
  bookend of the pair, and all this is replaced by the ``instruction''
  ~bv[]
  (\"***HIDING***\" :COMMENT :BEGIN name ...)
  ~ev[]
  where ~c[(comment begin name ...)] is the begin bookend of the pair.
  Finally, after applying this process to each pair of matching
  bookends, each begin bookend of the form ~c[(comment begin name ...)]
  that remains is replaced by
  ~bv[]
  (\"***UNFINISHED***\" :COMMENT :BEGIN name ...) .
  ~ev[]"

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

  "move antecedents of conclusion's ~c[implies] term to top-level
  hypotheses~/
  ~bv[]
  Examples:
  promote
  (promote t)
  ~ev[]
  For example, if the conclusion is ~c[(implies (and x y) z)], then
  after execution of ~c[promote], the conclusion will be ~c[z] and the terms ~c[x]
  and ~c[y] will be new top-level hypotheses.~/
  ~bv[]
  General Form:
  (promote &optional do-not-flatten-flag)
  ~ev[]
  Replace conclusion of ~c[(implies hyps exp)] or ~c[(if hyps exp t)] with
  simply ~c[exp], adding ~c[hyps] to the list of top-level hypotheses.
  Moreover, if ~c[hyps] is viewed as a conjunction then each conjunct will
  be added as a separate top-level hypothesis.  An exception is that
  if ~c[do-not-flatten-flag] is supplied and not ~c[nil], then only one
  top-level hypothesis will be added, namely ~c[hyps].

  ~st[Remark]:  You must be at the top of the conclusion in order to use this
  command.  Otherwise, first invoke ~c[top]."

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

  "print the result of evaluating the given form~/
  ~bv[]
  Example:
  (print (append '(a b) '(c d)))
  Print the list (a b c d) to the terminal~/

  General Forms:
  (print form)
  (print form t)
  ~ev[]
  Prettyprints the result of evaluating form.  The evaluation of ~c[form]
  should return a single value that is not ~ilc[state] or a single-threaded
  object (~pl[stobj]).  The optional second argument causes printing to be done
  without elision (so-called ``evisceration''; ~pl[evisc-tuple]).

  If the form you want to evaluate does not satisfy the criterion
  above, you should create an appropriate call of the ~c[lisp] command
  instead.  Notice that this command always returns
  ~c[(mv nil nil state)] where the second result will always be
  ~c[REPLACED-STATE]."

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
  (io? proof-checker nil state
       (abbreviations current-addr conc)
       (fms0 "~|~y0~|"
             (list (cons #\0 (untrans0 (fetch-term conc current-addr)
                                       (term-id-iff conc current-addr t)
                                       abbreviations))))))

(define-pc-help p ()

  "prettyprint the current term~/
  ~bv[]
  Example and General Form:
  p
  ~ev[]~/

  Prettyprint the current term.  The usual user syntax is used, so
  that for example one would see ~c[(and x y)] rather than ~c[(if x y 'nil)].
  (See also ~c[pp].)  Also, abbreviations are inserted where appropriate;
  see ~c[add-abbreviation].

  The ``current term'' is the entire conclusion unless ~c[dive] commands
  have been given, in which case it may be a subterm of the
  conclusion.

  If all goals have been proved, a message saying so will be printed
  (as there will be no current ~c[term]!)."

  (when-goals
   (p-body (conc t) (current-addr t) (abbreviations t) state)))

(define-pc-help pp ()

  "prettyprint the current term~/
  ~bv[]
  Example and General Form:
  pp
  ~ev[]~/

  This is the same as ~c[p] (see its documentation), except that raw
  syntax (internal form) is used.  So for example, one would see
  ~c[(if x y 'nil)] rather than ~c[(and x y)].  Abbreviations are however
  still inserted, as with ~c[p].~/"

  (when-goals
   (io? proof-checker nil state
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
    (pprogn (io? proof-checker nil state
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
      (io? proof-checker nil state
           nil
           (fms0 "~|There are no top-level hypotheses.~|"))
    (print-hyps indexed-hyps (if (some-> (strip-cars indexed-hyps) 9) 2 1)
                abbreviations state)))

(defun print-governors-top (indexed-hyps abbreviations state)
  (declare (xargs :guard (eqlable-alistp indexed-hyps)))
  (if (null indexed-hyps)
      (io? proof-checker nil state
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

  "print the hypotheses~/
  ~bv[]
  Examples:
  hyps               -- print all (top-level) hypotheses
  (hyps (1 3) (2 4)) -- print hypotheses 1 and 3 and governors 2 and 4
  (hyps (1 3) t)     -- print hypotheses 1 and 3 and all governors~/

  General Form:
  (hyps &optional hyps-indices govs-indices)
  ~ev[]
  Print the indicated top-level hypotheses and governors.  (The notion
  of ``governors'' is defined below.)  Here, ~c[hyps-indices] and
  ~c[govs-indices] should be lists of indices of hypotheses and governors
  (respectively), except that the atom ~c[t] may be used to indicate that
  one wants all hypotheses or governors (respectively).

  The list of ``governors'' is defined as follows.  Actually, we
  define here the notion of the governors for a pair of the form
  ~c[<term], address>]; we're interested in the special case where the
  term is the conclusion and the address is the current address.  If
  the address is ~c[nil], then there are no governors, i.e., the list of
  governors is ~c[nil].  If the term is of the form ~c[(if x y z)] and the
  address is of the form ~c[(2 . rest)] or ~c[(3 . rest)], then the list of
  governors is the result of ~c[cons]ing ~c[x] or its negation (respectively)
  onto the list of governors for the pair ~c[<y, rest>] or the pair
  ~c[<z, rest>] (respectively).  If the term is of the form ~c[(implies x y)]
  and the address is of the form ~c[(2 . rest)], then the list of
  governors is the result of ~c[cons]ing ~c[x] onto the list of governors for
  the pair ~c[<y, rest>].  Otherwise, the list of governors for the pair
  ~c[<term, (n .  rest)>] is exactly the list of governors for the pair
  ~c[<argn, rest>] where ~c[argn] is the ~c[n]th argument of ~c[term].

  If all goals have been proved, a message saying so will be printed.
  (as there will be no current hypotheses or governors!).

  The ~c[hyps] command never causes an error.  It ``succeeds'' (in fact
  its value is ~c[t]) if the arguments (when supplied) are appropriate,
  i.e.  either ~c[t] or lists of indices of hypotheses or governors,
  respectively.  Otherwise it ``fails'' (its value is ~c[nil])."

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
        (io? proof-checker nil state
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
        (io? proof-checker nil state
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
        (io? proof-checker nil state
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
                   (io? proof-checker nil state
                        nil
                        (fms0 "~|*** Top-level hypotheses:~|"))
                 (io? proof-checker nil state
                      nil
                      (fms0 "~|*** Specified top-level hypotheses:~|")))
               (print-hyps-top hyps-to-print abbs state))
            state)
          (if govs-indices
              (pprogn
               (if (eq govs-indices t)
                   (io? proof-checker nil state
                        nil
                        (fms0 "~|~%*** Governors:~|"))
                 (io? proof-checker nil state
                      nil
                      (fms0 "~|~%*** Specified governors:~|")))
               (print-governors-top govs-to-print abbs state))
            state)
          (value 'skip))))))))

(define-pc-primitive demote (&rest rest-args)

  "move top-level hypotheses to the conclusion~/
  ~bv[]
  Examples:
  demote        -- demote all top-level hypotheses
  (demote 3 5)  -- demote hypotheses 3 and 5
  ~ev[]
  For example, if the top-level hypotheses are ~c[x] and ~c[y] and the
  conclusion is ~c[z], then after execution of ~c[demote], the conclusion will
  be ~c[(implies (and x y) z)] and there will be no (top-level)
  hypotheses.~/
  ~bv[]
  General Form:
  (demote &rest hyps-indices)
  ~ev[]
  Eliminate the indicated (top-level) hypotheses, but replace the
  conclusion ~c[conc] with ~c[(implies hyps conc)] where ~c[hyps] is the
  conjunction of the hypotheses that were eliminated.  If no arguments
  are supplied, then all hypotheses are demoted, i.e. ~c[demote] is the
  same as ~c[(demote 1 2 ... n)] where ~c[n] is the number of top-level
  hypotheses.

  ~st[Remark]:  You must be at the top of the conclusion in order to use
  this command.  Otherwise, first invoke ~c[top].  Also, ~c[demote] fails if
  there are no top-level hypotheses or if indices are supplied that
  are out of range.~/"

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
  (declare (xargs :guard (and (all-keywords-p keywords)
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

(defun initial-pspv (term displayed-goal otf-flg ens wrld)
  (change prove-spec-var *empty-prove-spec-var*
          :rewrite-constant (initial-rcnst-from-ens ens wrld)
          :user-supplied-term term
          :displayed-goal displayed-goal
          :otf-flg otf-flg))

(defun pc-prove (term displayed-goal hints otf-flg ens wrld ctx state)

; This is exactly the same as the ACL2 PROVE function, except that we allow
; :bye objects in the tag tree, there is no checking of the load mode, and the
; warning above.

  (prog2$
   (initialize-brr-stack state)
   (er-let* ((ttree
              (let ((pspv (initial-pspv term displayed-goal otf-flg ens wrld))
                    (clause (list (list term))))
                (if (f-get-global 'in-verify-flg state) ;interactive
                    (state-global-let*
                     ((saved-output-p t)
                      (saved-output-token-lst :all))
                     (pprogn (f-put-global 'saved-output-reversed nil state)
                             (prove-loop clause pspv hints ens wrld ctx state)))
                  (prove-loop clause pspv hints ens wrld ctx state)))))
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

(defun unproved-pc-prove-terms (ttree)
  (strip-cdrs (tagged-objects :bye ttree nil)))

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
                               (io? proof-checker nil state
                                    nil
                                    (fms0 "~|***** Now entering the theorem ~
                                           prover *****~|")) 
                               (translate-hints+
                                'proof-checker
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
                                    (pprogn (io? proof-checker nil state
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
  (cond ((null ttree) nil)
        ((eq ttree t)
         (er hard 'remove-byes-from-tag-tree
             "Found tag tree of T in REMOVE-BYES-FROM-TAG-TREE."))
        ((eq :bye (caar ttree))
         ;; then ttree is ((:bye ...)) and we could perhaps return ()
         ;; but we play it safe
         (remove-byes-from-tag-tree (cdr ttree)))
        ((symbolp (caar ttree))
         (cons (car ttree)
               (remove-byes-from-tag-tree (cdr ttree))))
        (t (cons-tag-trees
            (remove-byes-from-tag-tree (car ttree))
            (remove-byes-from-tag-tree (cdr ttree))))))

(define-pc-primitive prove (&rest rest-args)

  "call the ACL2 theorem prover to prove the current goal~/
  ~bv[]
  Examples:
  prove -- attempt to prove the current goal
  (prove :otf-flg t
         :hints ((\"Subgoal 2\" :by foo) (\"Subgoal 1\" :use bar)))
        -- attempt to prove the current goal, with the indicated hints
           and with OTF-FLG set~/

  General Form:
  (prove &rest rest-args)
  ~ev[]
  Attempt to prove the current goal, where ~c[rest-args] is as in the
  keyword arguments to ~c[defthm] except that only ~c[:hints] and ~c[:otf-flg] are
  allowed.  The command succeeds exactly when the corresponding ~c[defthm]
  would succeed, except that it is all right for some goals to be
  given ``bye''s.  Each goal given a ``bye'' will be turned into a new
  subgoal.  (~l[hints] for an explanation of ~c[:by] hints.)

  ~st[Remark:]  Use ~c[(= t)] instead if you are not at the top of the
  conclusion.  Also note that if there are any hypotheses in the
  current goal, then what is actually attempted is a proof of
  ~c[(implies hyps conc)], where ~c[hyps] is the conjunction of the
  top-level hypotheses and ~c[conc] is the goal's conclusion.

  ~st[Remark:]  It is allowed to use abbreviations in the hints."

  (cond
   (current-addr
    (print-no-change2 "The PROVE command should only be used at ~
                       the top.  Use (= T) if that is what you want."))
   ((not (keyword-value-listp rest-args))
    (print-no-change2 "The argument list for the PROVE command should ~
                       be empty or a list of even length with keywords in the odd ~
                       positions.  See the documentation for examples and details."))
   (t
    (mv-let (erp ttree state)
            (prover-call
             :prove (make-implication hyps conc) rest-args pc-state state)
            (if erp
                (mv nil state)
              (let* ((new-terms
                      (unproved-pc-prove-terms ttree))
                     (new-goals
                      (make-new-goals new-terms goal-name depends-on)))
                (if (and (equal (length new-terms)
                                1)
                         (same-goal (car new-goals)
                                    (car goals)))
                    (print-no-change2 "Exactly one new goal was created by your PROVE ~
                                       command, and it has exactly the same hypotheses ~
                                       and conclusion as did the current goal.")
                  (mv
                   (change-pc-state
                    pc-state
                    :goals
                    (append new-goals (cdr goals))
                    :local-tag-tree
                    (remove-byes-from-tag-tree ttree))
                   state))))))))

(defun add-string-val-pair-to-string-val-alist (key key1 val alist)

; Key is a string (typically a goal name) and key1 is a keyword (presumably a
; hint keyword).  Alist associates keys (strings) with keyword alists.
; Associate key1 with val in the keyword alist associated with key, unless key1
; is already bound in that keyword alist in which case just return alist.

  (cond ((null alist) (list (list key key1 val)))
        ((and (stringp (caar alist))
              (string-equal key (caar alist)))
         (if (assoc-keyword key1 (cdar alist))
             alist
           (cons (list* (caar alist) key1 val (cdar alist))
                 (cdr alist))))
        (t (cons (car alist)
                 (add-string-val-pair-to-string-val-alist
                  key key1 val (cdr alist))))))

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

  "call the ACL2 theorem prover's simplifier~/
  ~bv[]
  Examples:
  bash -- attempt to prove the current goal by simplification alone
  (bash (\"Subgoal 2\" :by foo) (\"Subgoal 1\" :use bar))
       -- attempt to prove the current goal by simplification alone,
          with the indicated hints~/

  General Form:
  (bash &rest hints)
  ~ev[]
  Call the theorem prover's simplifier, creating a subgoal for each
  resulting goal.

  Notice that unlike ~c[prove], the arguments to ~c[bash] are spread out, and
  are all hints.

  ~c[Bash] is similar to ~c[reduce] in that neither of these allows induction.
  But ~c[bash] only allows simplification, while ~c[reduce] allows processes
  ~c[eliminate-destructors], ~c[fertilize], ~c[generalize], and
  ~c[eliminate-irrelevance].

  ~st[Remark:]  All forcing rounds will be skipped (unless there are more
  than 15 subgoals generated in the first forcing round, an injustice
  that should be rectified, but might remain unless there is pressure to
  fix it)."

  (if (alistp hints)
      (value (list :prove :hints
                   (append
                    *bash-skip-forcing-round-hints*
                    (add-string-val-pair-to-string-val-alist
                     "Goal"
                     ;; only preprocess and simplify are allowed 
                     :do-not
                     (list 'quote '(generalize eliminate-destructors
                                               fertilize eliminate-irrelevance))
                     (add-string-val-pair-to-string-val-alist
                      "Goal"
                      :do-not-induct
                      'proof-checker
                      hints)))
                   :otf-flg t))
    (pprogn (print-no-change
             "A BASH instruction must be of the form~%~ ~ ~
              (:BASH (goal_name_1 ...) ... (goal_name_n ...)),~%and hence ~
              your instruction,~%~ ~ ~x0,~%is not legal."
             (list (cons #\0 (cons :bash hints))))
            (value :fail))))

(define-pc-primitive dive (n &rest rest-addr)

  "move to the indicated subterm~/
  ~bv[]
  Examples:
  (DIVE 1)    -- assign the new current subterm to be the first
                 argument of the existing current subterm
  (DIVE 1 2)  -- assign the new current subterm to be the result of
                 first taking the 1st argument of the existing
                 current subterm, and then the 2nd argument of that
  ~ev[]
  For example, if the current subterm is
  ~bv[]
  (* (+ a b) c),
  ~ev[]
  then after ~c[(dive 1)] it is
  ~bv[]
  (+ a b).
  ~ev[]
  If after that, then ~c[(dive 2)] is invoked, the new current subterm
  will be
  ~bv[]
  b.
  ~ev[]
  Instead of ~c[(dive 1)] followed by ~c[(dive 2)], the same current subterm
  could be obtained by instead submitting the single instruction
  ~c[(dive 1 2)].~/
  ~bv[]
  General Form:
  (dive &rest naturals-list)
  ~ev[]
  If ~c[naturals-list] is a non-empty list ~c[(n_1 ... n_k)] of natural
  numbers, let the new current subterm be the result of selecting the
  ~c[n_1]-st argument of the current subterm, and then the ~c[n_2]-th subterm
  of that, ..., finally the ~c[n_k]-th subterm.

  ~st[Remark:]  ~c[Dive] is related to the command ~c[pp], in that the diving
  is done according to raw (translated, internal form) syntax.  Use the
  command ~c[dv] if you want to dive according to the syntax displayed by
  the command ~c[p].  Note that ~c[(dv n)] can be abbreviated by simply ~c[n]."

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

  "split the current goal into cases~/
  ~bv[]
  Example:
  split
  ~ev[]
  For example, if the current goal has one hypothesis ~c[(or x y)] and a
  conclusion of ~c[(and a b)], then ~c[split] will create four new goals:
  ~bv[]
  one with hypothesis X and conclusion A
  one with hypothesis X and conclusion B
  one with hypothesis Y and conclusion A
  one with hypothesis Y and conclusion B.~/

  General Form:
  SPLIT
  ~ev[]
  Replace the current goal by subgoals whose conjunction is equivalent
  (primarily by propositional reasoning) to the original goal, where
  each such goal cannot be similarly split.

  ~st[Remark:]  The new goals will all have their hypotheses promoted; in
  particular, no conclusion will have a top function symbol of
  ~c[implies].  Also note that ~c[split] will fail if there is exactly one new
  goal created and it is the same as the existing current goal.

  The way ~c[split] really works is to call the ACL2 theorem prover with only
  simplification (and preprocessing) turned on, and with only a few built-in
  functions (especially, propositional ones) enabled, namely, the ones in the
  list ~c[(theory 'minimal-theory)].  However, because the prover is called,
  type-set reasoning can be used to eliminate some cases.  For example, if
  ~c[(true-listp x)] is in the hypotheses, then probably
  ~c[(true-listp (cdr x))] will be reduced to ~c[t]."

  (value '(:prove :hints
                  (("Goal"
                    :do-not-induct proof-checker
                    :do-not '(generalize eliminate-destructors
                                         fertilize eliminate-irrelevance)
                    :in-theory (theory 'minimal-theory))))))

(define-pc-primitive add-abbreviation (var &optional raw-term)

  "add an abbreviation~/

  Example:  ~c[(add-abbreviation v (* x y))] causes future occurrences of
  ~c[(* x y)] to be printed as ~c[(? v)], until (unless) a corresponding
  invocation of ~c[remove-abbreviations] occurs.  In this case we say that
  ~c[v] ``abbreviates'' ~c[(* x y)].~/
  ~bv[]
  General Form:
  (add-abbreviation var &optional raw-term)
  ~ev[]
  Let ~c[var] be an abbreviation for ~c[raw-term], if ~c[raw-term] is supplied,
  else for the current subterm.  Note that ~c[var] must be a variable that
  does not already abbreviate some term.

  A way to think of abbreviations is as follows.  Imagine that
  whenever an abbreviation is added, say ~c[v] abbreviates ~c[expr], an entry
  associating ~c[v] to ~c[expr] is made in an association list, which we will
  call ``~c[*abbreviations-alist*]''.  Then simply imagine that ~c[?] is a
  function defined by something like:
  ~bv[]
  (defun ? (v)
    (let ((pair (assoc v *abbreviations-alist*)))
      (if pair (cdr pair)
        (error ...))))
  ~ev[]
  Of course the implementation isn't exactly like that, since the
  ``constant'' ~c[*abbreviations-alist*] actually changes each time an
  ~c[add-abbreviation] instruction is successfully invoked.  Nevertheless,
  if one imagines an appropriate redefinition of the ``constant''
  ~c[*abbreviations-alist*] each time an ~c[add-abbreviation] is invoked, then
  one will have a clear model of the meaning of such an instruction.

  The effect of abbreviations on output is that before printing a
  term, each subterm that is abbreviated by a variable ~c[v] is first
  replaced by ~c[(? v)].

  The effect of abbreviations on input is that every built-in
  proof-checker command accepts abbreviations wherever a term is
  expected as an argument, i.e., accepts the syntax ~c[(? v)] whenever ~c[v]
  abbreviates a term.  For example, the second argument of
  ~c[add-abbreviation] may itself use abbreviations that have been defined
  by previous ~c[add-abbreviation] instructions.

  See also ~c[remove-abbreviations] and ~c[show-abbreviations]."

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

  "remove one or more abbreviations~/
  ~bv[]
  Examples:
  remove-abbreviations -- remove all abbreviations
  (remove-abbreviations v w)
                       -- assuming that V and W currently abbreviate
                          terms, then they are ``removed'' in the
                          sense that they are no longer considered to
                          abbreviate those terms~/

  General Forms:
  (remove-abbreviations &rest vars)
  ~ev[]
  If vars is not empty (i.e., not ~c[nil]), remove the variables in ~c[vars]
  from the current list of abbreviations, in the sense that each
  variable in ~c[vars] will no longer abbreviate a term.

  ~st[Remark:]  The instruction fails if at least one of the arguments
  fails to be a variable that abbreviates a term.

  See also the documentation for ~c[add-abbreviation], which contains a
  discussion of abbreviations in general, and ~c[show-abbreviations]."

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
                 (delete-assoc-eq-lst vars abbreviations)
               nil))
            state)))))

(defun print-abbreviations (vars abbreviations state)
  ;; Here abbreviations can contain junky pairs.
  (declare (xargs :guard (and (true-listp vars)
                              (symbol-alistp abbreviations))))
  (if (null vars)
      state
    (pprogn
     (io? proof-checker nil state
          nil
          (fms0 "~%"))
     (let ((pair (assoc-equal (car vars) abbreviations)))
       (if (null pair)
           ;; then this pair is junk
           (io? proof-checker nil state
                (vars)
                (fms0 "*** ~x0 does not abbreviate a term.~|"
                      (list (cons #\0 (car vars)))))
         (let ((untrans-1 (untrans0 (cdr pair)))
               (untrans-2 (untrans0 (cdr pair)
                                    nil
                                    (delete-assoc-eq (car pair) abbreviations))))
           (pprogn
            (io? proof-checker nil state
                 (pair)
                 (fms0 "(? ~x0) is an abbreviation for:~%~ ~ "
                       (list (cons #\0 (car pair)))))
            (io? proof-checker nil state
                 (untrans-1)
                 (fms0 "~y0~|"
                       (list (cons #\0 untrans-1))
                       2))
            (if (equal untrans-1 untrans-2)
                state
              (pprogn
               (io? proof-checker nil state
                    nil
                    (fms0 "i.e. for~%~ ~ "))
               (io? proof-checker nil state
                    (untrans-2)
                    (fms0 "~y0~|"
                          (list (cons #\0 untrans-2))
                          2))))))))
     (print-abbreviations (cdr vars) abbreviations state))))

(define-pc-help show-abbreviations (&rest vars)

  "display the current abbreviations~/
  ~bv[]
  Examples:
  (show-abbreviations v w)
     -- assuming that v and w currently abbreviate terms,
        then this instruction displays them together with
        the terms they abbreviate
  show-abbreviations
     -- display all abbreviations
  ~ev[]
  See also ~c[add-abbreviation] and ~c[remove-abbreviations].  In
  particular, the documentation for ~c[add-abbreviation] contains a
  general discussion of abbreviations.~/
  ~bv[]
  General Form:
  (show-abbreviations &rest vars)
  ~ev[]
  Display each argument in ~c[vars] together with the term it abbreviates
  (if any).  If there are no arguments, i.e. the instruction is simply
  ~c[show-abbreviations], then display all abbreviations together with the
  terms they abbreviate.

  If the term abbreviated by a variable, say ~c[v], contains a proper
  subterm that is also abbreviate by (another) variable, then both the
  unabbreviated term and the abbreviated term (but not using ~c[(? v)] to
  abbreviate the term) are displayed with together with ~c[v]."

  (if (null (abbreviations t))
      (io? proof-checker nil state
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

  "move to the parent (or some ancestor) of the current subterm~/
  ~bv[]
  Examples:  if the conclusion is (= x (* (- y) z)) and the
             current subterm is y, then we have:
  up or (up 1) -- the current subterm becomes (- y)
  (up 2)       -- the current subterm becomes (* (- y) z)
  (up 3)       -- the current subterm becomes the entire conclusion
  (up 4)       -- no change; can't go up that many levels~/

  General Form:
  (up &optional n)
  ~ev[]
  Move up ~c[n] levels in the conclusion from the current subterm, where ~c[n]
  is a positive integer.  If ~c[n] is not supplied or is ~c[nil], then move up
  1 level, i.e., treat the instruction as ~c[(up 1)].

  See also ~c[dive], ~c[top], ~c[nx], and ~c[bk]."

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

  "move to the top of the goal~/
  ~bv[]
  Example and General Form:
  top
  ~ev[]
  For example, if the conclusion is ~c[(= x (* (- y) z))] and the
  current subterm is ~c[y], then after executing ~c[top], the current subterm
  will be the same as the conclusion, i.e., ~c[(= x (* (- y) z))].~/

  ~c[Top] is the same as ~c[(up n)], where ~c[n] is the number of times one needs
  to execute ~c[up] in order to get to the top of the conclusion.  The ~c[top]
  command fails if one is already at the top of the conclusion.

  See also ~c[up], ~c[dive], ~c[nx], and ~c[bk]."
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
            (cond ((and (nvariablep x1)
                        (not (fquotep x1))
                        (eq (ffn-symb x1) 'not))
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
    (('if *t* x2 *nil*) ; see untranslate-and
     (addr-recur 2
                 (and-addr n x2 iff-flg)))
    (('if x1 x2 *nil*)
     (cond ((and iff-flg (equal x2 *t*)) ; see untranslate-and
            (addr-recur 1
                        (and-addr n x1 t)))
           ((int= n 1)
            (mv '(1) x1 t nil))
           (t
            (addr-recur 2
                        (and-addr (1- n) x2 iff-flg)))))
    (('if x1 *nil* x2)
     (cond ((int= n 1)
            (cond ((and (nvariablep x1)
                        (not (fquotep x1))
                        (eq (ffn-symb x1) 'not))
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
            (or (symbolp val) ; a function to call
                (integerp val)
                (null val))))

(defmacro add-dive-into-macro (name val)

  ":Doc-Section switches-parameters-and-modes

  associate ~il[proof-checker] diving function with macro name~/
  ~bv[]
  Examples:
  (add-dive-into-macro cat expand-address-cat)
  ~ev[]
  This feature is used so that the ~il[proof-checker]'s ~c[DV] command and
  numeric diving commands (e.g., ~c[3]) will dive properly into subterms.
  Please ~pl[dive-into-macros-table].~/~/"

  `(table dive-into-macros-table ',name ',val))

(defmacro remove-dive-into-macro (name)

  ":Doc-Section switches-parameters-and-modes

  removes association of ~il[proof-checker] diving function with macro name~/
  ~bv[]
  Example:
  (remove-dive-into-macro logand)
  ~ev[]
  This feature undoes the effect of ~ilc[add-dive-into-macro], which is used
  so that the ~il[proof-checker]'s ~c[DV] command and numeric diving commands
  (e.g., ~c[3]) will dive properly into subterms.  Please
  ~pl[add-dive-into-macro] and especially ~pl[dive-into-macros-table].~/~/"

  `(table dive-into-macros-table ',name nil))

(defun dive-into-macros-table (wrld)

  ":Doc-Section switches-parameters-and-modes

  right-associated function information for the ~il[proof-checker]~/
  ~bv[]
  Examples:
  ACL2 !>(dive-into-macros-table (w state))
  ((CAT . EXPAND-ADDRESS-CAT)
   (LXOR . EXPAND-ADDRESS-LXOR)
  ~ev[]
  This table associates macro names with functions used by the
  ~il[proof-checker]'s ~c[DV] and numeric diving commands (e.g., ~c[3]) in
  order to dive properly into subterms.  ~l[proof-checker], in particular the
  documentation for ~c[DV].

  This table can be extended easily.  ~l[add-dive-into-macro] and also
  ~pl[remove-dive-into-macro].

  The symbol associated with a macro should be a function symbol taking four
  arguments, in this order:
  ~bf[]
  ~c[car-addr] ; the first number in the list given to the ~il[proof-checker]'s
             ~c[DV] command
  ~c[raw-term] ; the untranslated term into which we will dive
  ~c[term]     ; the translated term into which we will dive
  ~c[wrld]     ; the current ACL2 logical ~il[world]
  ~ef[]
  The function will normally return a list of positive integers, representing
  the (one-based) address for diving into ~c[term] that corresponds to the
  single-address dive into ~c[raw-term] by ~c[car-address].  However, it can
  return ~c[(cons str alist)], where ~c[str] is a string suitable for ~ilc[fmt]
  and ~c[args] is the corresponding alist for ~ilc[fmt].

  Referring to the example above, ~c[expand-address-cat] would be such a
  function, which will be called on ~c[raw-term] values that are calls of
  ~c[cat].  See the distributed book ~c[books/misc/rtl-untranslate.lisp] for
  the definition of such a function.

  ~l[table] for a general discussion of tables.~/~/"

  (declare (xargs :guard (plist-worldp wrld)))
  (table-alist 'dive-into-macros-table wrld))

(defun expand-address (addr raw-term term abbreviations iff-flg accumulated-addr-r wrld)

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
                                  wrld nil t nil t)
                     (cond
                      ((or erp (stringp (car val)))
                       (mv (car val) (cdr val)))
                      (t (expand-address-recurse
                          :ans (append val rest-addr)
                          :new-iff-flg nil 
                          :new-term (fetch-term term val))))))
            ((or (eq (car term) 'list)
                 (let ((pair (rassoc-eq (car raw-term) (binop-table wrld))))
                   (and pair
                        (eql (arity (car pair) wrld) 2))))

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
               (list*
                (let* ((lst (make-list (1- (car addr)) :initial-element 2))
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
                               is problematic, because of ~s3.  Try using ~
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
                (mv-let
                 (fn guts)
                 (car-cdr-nest term)
                 (cond
                  (fn
                   (expand-address-recurse
                    :ans (append (make-list (- (length (symbol-name fn)) 2)
                                            :initial-element 1)
                                 rest-addr)
                    :new-term guts))
                  (t (expand-address-recurse))))))))))))

(defmacro dv-error (str alist)
  `(pprogn (print-no-change
            (string-append "Unable to perform the requested dive.~|~%" ,str)

; We could print the current term using ~xt in the string above, but that
; appears to be distracting in the error message.

            (cons (cons #\t current-term) ,alist))
           (mv t nil state)))

(define-pc-atomic-macro dv (&rest rest-args)

  "move to the indicated subterm~/
  ~bv[]
  Examples:
  (dv 1)    -- assign the new current subterm to be the first argument
               of the existing current subterm
  (dv 1 2)  -- assign the new current subterm to be the result of
               first taking the 1st argument of the existing
               current subterm, and then the 2nd argument of that
  ~ev[]
  For example, if the current subterm is
  ~bv[]
  (* (+ a b) c),
  ~ev[]
  then after ~c[(dv 1)] it is
  ~bv[]
  (+ a b).
  ~ev[]
  If after that, then ~c[(dv 2)] is invoked, the new current subterm
  will be
  ~bv[]
  b.
  ~ev[]
  Instead of ~c[(dv 1)] followed by ~c[(dv 2)], the same current subterm
  could be obtained by instead submitting the single instruction
  ~c[(dv 1 2)].~/
  ~bv[]
  General Form:
  (dv &rest naturals-list)
  ~ev[]
  If ~c[naturals-list] is a non-empty list ~c[(n_1 ... n_k)] of natural
  numbers, let the new current subterm be the result of selecting the
  ~c[n_1]-st argument of the current subterm, and then the ~c[n_2]-th subterm
  of that, ..., finally the ~c[n_k]-th subterm.

  ~st[Remark:]  ~c[(dv n)] may be abbreviated by simply ~c[n], so we could have
  typed ~c[1] instead of ~c[(dv 1)] in the first example above.

  ~st[Remark:]  See also ~c[dive], which is related to the command ~c[pp], in
  that the diving is done according to raw (translated, internal form)
  syntax.  Use the command ~c[dv] if you want to dive according to the
  syntax displayed by the command ~c[p].  Thus, the command ``~c[up]'' is the
  inverse of ~c[dive], not of ~c[dv].  The following example illustrates this
  point.
  ~bv[]
  ACL2 !>(verify (equal (* a b c) x))
  ->: p ; print user-level term
  (EQUAL (* A B C) X)
  ->: pp ; print internal-form (translated) term
  (EQUAL (BINARY-* A (BINARY-* B C)) X)
  ->: exit
  Exiting....
   NIL
  ACL2 !>(verify (equal (* a b c) x))
  ->: p
  (EQUAL (* A B C) X)
  ->: 1 ; same as (dv 1)
  ->: p ; print user-level term
  (* A B C)
  ->: pp ; print internal-form (translated) term
  (BINARY-* A (BINARY-* B C))
  ->: 3 ; dive to third argument of (* A B C)
  ->: p
  C
  ->: up ; go up one level in (BINARY-* A (BINARY-* B C))
  ->: p
  (* B C)
  ->: pp
  (BINARY-* B C)
  ->: 
  ~ev[]"

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

(defun geneqv-at-subterm (term addr geneqv ens wrld)
  ;; The property we want is that if one substitutes an equivalent
  ;; subterm of TERM at the given address (equivalent modulo the
  ;; generated equivalence relation returned by this function, that
  ;; is), then the resulting term is equivalent modulo geneqv to the
  ;; original TERM.  We assume that address is a valid address for
  ;; term.  (*** This should really be a guard.)  As usual, we may
  ;; return NIL for 'equal.
  (if (null addr)
      geneqv
    (geneqv-at-subterm
     (nth (1- (car addr)) (fargs term))
     (cdr addr)
     (nth (1- (car addr))
          ;; ***** seems inefficient to do all the computing just below
          (geneqv-lst (ffn-symb term) geneqv ens wrld))
     ens
     wrld)))

(defun geneqv-at-subterm-top (term addr ens wrld)
  (geneqv-at-subterm term addr *geneqv-iff* ens wrld))

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
          (pprogn (io? proof-checker nil state
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
  (if (or (variablep term)
          (fquotep term)
          (not (eq (ffn-symb term) 'implies)))
      (mv nil term)
    (mv-let (h c)
            (split-implies (fargn term 2))
            (mv (append (flatten-ands-in-lit (fargn term 1)) h) c))))

(defun equiv-refinementp (equiv1 equiv2 wrld)
  (member-eq equiv2
             (getprop equiv1 'coarsenings nil 'current-acl2-world wrld)))

(defun find-equivalence-hyp-term (term hyps target equiv w)
  ;; allows backchaining through IMPLIES
  (if (consp hyps)
      (mv-let (h c)
              (split-implies (car hyps))
              (if (or (variablep c)
                      (fquotep c)
                      (not (symbolp (ffn-symb c)))
                      (not (equiv-refinementp (ffn-symb c) equiv w)))
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

(defun flatten-ands-in-lit-lst (x)
  (if (endp x)
      nil
    (append (flatten-ands-in-lit (car x))
            (flatten-ands-in-lit-lst (cdr x)))))

(define-pc-primitive equiv (x y &optional equiv)

  "attempt an equality (or congruence-based) substitution~/
  ~bv[]
  Examples:
  (equiv (* x y) 3) -- replace (* x y) by 3 everywhere inside the
                       current subterm, if their equality is among the
                       top-level hypotheses or the governors
  (equiv x t iff)   -- replace x by t everywhere inside the current
                       subterm, where only propositional equivalence
                       needs to be maintained at each occurrence of x~/

  General form:
  (equiv old new &optional relation)
  ~ev[]
  Substitute new for old everywhere inside the current subterm,
  provided that either (relation old new) or (relation new old) is
  among the top-level hypotheses or the governors (possibly by way of
  backchaining and/or refinement; see below).  If relation is ~c[nil] or
  is not supplied, then it defaults to ~c[equal].  See also the command ~c[=],
  which is much more flexible.  Note that this command fails if no
  substitution is actually made.

  ~st[Remark:]  No substitution takes place inside explicit values.  So for
  example, the instruction ~c[(equiv 3 x)] will cause ~c[3] to be replaced by
  ~c[x] if the current subterm is, say, ~c[(* 3 y)], but not if the current
  subterm is ~c[(* 4 y)] even though ~c[4 = (1+ 3)].

  The following remarks are quite technical and mostly describe a
  certain weak form of ``backchaining'' that has been implemented for
  ~c[equiv] in order to support the ~c[=] command.  In fact neither the term
  ~c[(relation old new)] nor the term ~c[(relation new old)] needs to be
  ~st[explicitly] among the current ``assumptions'', i.e., the top-level
  hypothesis or the governors.  Rather, there need only be such an
  assumption that ``tells us'' ~c[(r old new)] or ~c[(r new old)], for ~st[some]
  equivalence relation ~c[r] that ~st[refines] ~c[relation].  Here, ``tells us''
  means that either one of the indicated terms is among those
  assumptions, or else there is an assumption that is an implication
  whose conclusion is one of the indicated terms and whose hypotheses
  (gathered up by appropriately flattening the first argument of the
  ~c[implies] term) are all among the current assumptions."

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
                   (if (equivalence-relationp equiv w)
                       (value equiv)
                     (er soft :equiv
                         "The name ~x0 is not currently the name of an ACL2 ~
                          equivalence relation.  The current list of ~
                          ACL2 equivalence relations is ~x1."
                         equiv
                         (getprop 'equal 'coarsenings nil
                                  'current-acl2-world w))))))
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

  "split into two cases~/
  ~bv[]
  Example:
  (casesplit (< x y)) -- assuming that we are at the top of the
                         conclusion, add (< x y) as a new top-level
                         hypothesis in the current goal, and create a
                         subgoal identical to the current goal except
                         that it has (not (< x y)) as a new top-level
                         hypothesis~/

  General Form:
  (casesplit expr &optional use-hyps-flag do-not-flatten-flag)
  ~ev[]
  When the current subterm is the entire conclusion, this instruction
  adds ~c[expr] as a new top-level hypothesis, and create a subgoal
  identical to the existing current goal except that it has the
  negation of ~c[expr] as a new top-level hypothesis.  See also ~c[claim].
  The optional arguments control the use of governors and the
  ``flattening'' of new hypotheses, as we now explain.

  The argument ~c[use-hyps-flag] is only of interest when there are
  governors.  (To read about governors, see the documentation for the
  command ~c[hyps]).  In that case, if ~c[use-hyps-flag] is not supplied or is
  ~c[nil], then the description above is correct; but otherwise, it is not
  ~c[expr] but rather it is ~c[(implies govs expr)] that is added as a new
  top-level hypothesis (and whose negation is added as a top-level
  hypothesis for the new goal), where ~c[govs] is the conjunction of the
  governors.

  If ~c[do-not-flatten-flag] is supplied and not ~c[nil], then that is
  all there is to this command.  Otherwise (thus this is the default),
  when the claimed term (first argument) is a conjunction (~c[and]) of
  terms and the ~c[claim] instruction succeeds, then each (nested)
  conjunct of the claimed term is added as a separate new top-level
  hypothesis.  Consider the following example, assuming there are no
  governors.
  ~bv[]
  (casesplit (and (and (< x y) (integerp a)) (equal r s)) t)
  ~ev[]
  Three new top-level hypotheses are added to the current goal, namely
  ~c[(< x y)], ~c[(integerp a)], and ~c[(equal r s)].  In that case, only
  one hypothesis is added to create the new goal, namely the negation
  of ~c[(and (< x y) (integerp a) (equal r s))].  If the negation of this
  term had been ~c[claim]ed, then it would be the other way around:  the
  current goal would get a single new hypothesis while the new goal
  would be created by adding three hypotheses.

  ~st[Remark:]  It is allowed to use abbreviations in the hints."

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

  "add a new hypothesis~/
  ~bv[]
  Examples:
  (claim (< x y))   -- attempt to prove (< x y) from the current
                       top-level hypotheses and if successful, then
                       add (< x y) as a new top-level hypothesis in
                       the current goal
  (claim (< x y)
         :otf-flg t
         :hints ((\"Goal\" :induct t)))
                    -- as above, but call the prover using the
                       indicated values for the otf-flg and hints
  (claim (< x y) 0) -- as above, except instead of attempting to
                       prove (< x y), create a new subgoal with the
                       same top-level hypotheses as the current goal
                       that has (< x y) as its conclusion
  (claim (< x y) :hints :none)
                    -- same as immediately above~/

  General Form:
  (claim expr &rest rest-args)
  ~ev[]
  This command creates a new subgoal with the same top-level
  hypotheses as the current goal but with a conclusion of ~c[expr].  If
  ~c[rest-args] is a non-empty list headed by a non-keyword, then there
  will be no proof attempted for the new subgoal.  With that possible
  exception, ~c[rest-args] should consist of keyword arguments.  The
  keyword argument ~c[:do-not-flatten] controls the ``flattening'' of new
  hypotheses, just as with the ~c[casesplit] command (as described in its
  documentation).  The remaining ~c[rest-args] are used with a call the
  ~c[prove] command on the new subgoal, except that if ~c[:hints] is a non-~c[nil]
  atom, then the prover is not called ~-[] rather, this is the same as
  the situation described above, where ~c[rest-args] is a non-empty list
  headed by a non-keyword.

  ~st[Remarks:]  (1) Unlike the ~c[casesplit] command, the ~c[claim]
  command is completely insensitive to governors. (2) It is allowed to
  use abbreviations in the hints.  (3) The keyword :~c[none] has the
  special role as a value of :~c[hints] that is shown clearly in an
  example above."

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

  "generate subgoals using induction~/
  ~bv[]
  Examples:
  induct, (induct t)
     -- induct according to a heuristically-chosen scheme, creating
        a new subgoal for each base and induction step
  (induct (append (reverse x) y))
     -- as above, but choose an induction scheme based on the term
        (append (reverse x) y) rather than on the current goal~/

  General Form:
  (induct &optional term)
  ~ev[]
  Induct as in the corresponding ~c[:induct] hint given to the theorem
  prover, creating new subgoals for the base and induction steps.  If
  term is ~c[t] or is not supplied, then use the current goal to determine
  the induction scheme; otherwise, use that term.

  ~st[Remark:]  As usual, abbreviations are allowed in the term.

  ~st[Remark:]  ~c[Induct] actually calls the ~c[prove] command with all
  processes turned off.  Thus, you must be at top of the goal for an ~c[induct]
  instruction."

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
                        :do-not-induct proof-checker
                        :do-not *do-not-processes*))))))))

(defun print-on-separate-lines (vals evisc-tuple chan state)
  (declare (xargs :guard (true-listp vals)))
  (if (null vals)
      (newline chan state)
    (pprogn (io? proof-checker nil state
                 (evisc-tuple chan vals)
                 (fms "~x0" (list (cons #\0 (car vals))) chan state
                      evisc-tuple))
            (print-on-separate-lines (cdr vals) evisc-tuple chan state))))

(define-pc-help goals ()

  "list the names of goals on the stack~/
  ~bv[]
  Example and General Form:
  goals
  ~ev[]~/

  ~c[Goals] lists the names of all goals that remain to be proved.  They
  are listed in the order in which they appear on the stack of
  remaining goals, which is relevant for example to the effect of a
  ~c[change-goal] instruction."

  (io? proof-checker nil state
       (state-stack)
       (when-goals
        (print-on-separate-lines (goal-names (goals t)) nil (proofs-co state)
                                 state))))

(defun modified-error-triple-for-sequence (erp val success-expr state)
  (mv-let (new-erp stobjs-out-and-vals state)
          (state-global-let*
           ((erp erp)
            (val val))
           (trans-eval success-expr :sequence state t))

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
                  (pprogn (io? proof-checker nil state
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
                                           (cons #\2 vals))))
                          (mv erp val state))
                (mv (car vals) (cadr vals) state))))))

(define-pc-meta sequence
  (instr-list &optional
              strict-flg protect-flg success-expr no-prompt-flg no-restore-flg)

  ;; Note:  the reason I use state globals instead of a lexical LET for
  ;; the success-expr argument is that I don't want to worry about the
  ;; translator failing because erp and val aren't declared ignored when
  ;; they should be.

  "run the given list of instructions according to a multitude of
  options~/
  ~bv[]
  Example:
  (sequence (induct p prove) t)
  ~ev[]
  See also the definitions of commands ~c[do-all], ~c[do-strict], ~c[protect], and
  ~c[succeed].~/

  ~bv[]
  General Form:
  (sequence
   instruction-list
   &optional
   strict-flg protect-flg success-expr no-prompt-flg no-restore-flg)
  ~ev[]
  Each instruction in the list ~c[instruction-list] is run, and the
  instruction ``succeeds'' if every instruction in ~c[instruction-list]
  ``succeeds''.  However, it might ``succeed'' even if some
  instructions in the list ``fail''; more generally, the various
  arguments control a number of aspects of the running of the
  instructions.  All this is explained in the paragraphs below.  First
  we embark on a general discussion of the instruction interpreter,
  including the notions of ``succeed'' and ``fail''.

  ~st[Remark:]  The arguments are ~st[not] evaluated, except (in a sense) for
  ~c[success-expr], as described below.

  Each primitive and meta instruction can be thought of as returning
  an error triple (in the standard ACL2 sense), say ~c[(erp val state)].
  An instruction (primitive or meta) ``succeeds'' if ~c[erp] is ~c[nil] and
  ~c[val] is not ~c[nil]; otherwise it ``fails''.  (When we use the words
  ``succeed'' or ``fail'' in this technical sense, we'll always
  include them in double quotes.)  If an instruction ``fails,'' we say
  that that the failure is ``soft'' if ~c[erp] is ~c[nil]; otherwise the
  failure is ``hard''.  The ~c[sequence] command gives the user control
  over how to treat ``success'' and ``failure'' when sequencing
  instructions, though we have created a number of handy macro
  commands for this purpose, notably ~c[do-all], ~c[do-strict] and ~c[protect].

  Here is precisely what happens when a ~c[sequence] instruction is run.
  The instruction interpreter is run on the instructions supplied in
  the argument ~c[instruction-list] (in order).  The interpreter halts the
  first time there is a hard ``failure.'' except that if ~c[strict-flg] is
  supplied and not ~c[nil], then the interpreter halts the first time
  there is any ``failure.''  The error triple ~c[(erp val state)] returned
  by the ~c[sequence] instruction is the triple returned by the last
  instruction executed (or, the triple ~c[(nil t state)] if
  ~c[instruction-list] is ~c[nil]), except for the following provision.  If
  ~c[success-expr] is supplied and not ~c[nil], then it is evaluated with the
  state global variables ~c[erp] and ~c[val] (in ACL2 package) bound to the
  corresponding components of the error triple returned (as described
  above).  At least two values should be returned, and the first two
  of these will be substituted for ~c[erp] and ~c[val] in the triple finally
  returned by ~c[sequence].  For example, if ~c[success-expr] is ~c[(mv erp val)],
  then no change will be made to the error triple, and if instead it
  is ~c[(mv nil t)], then the ~c[sequence] instruction will ``succeed''.

  That concludes the description of the error triple returned by a
  ~c[sequence] instruction, but it remains to explain the effects of the
  arguments ~c[protect-flg] and ~c[no-prompt-flg].

  If ~c[protect-flg] is supplied and not ~c[nil] and if also the instruction
  ``fails'' (i.e., the error component of the triple is not ~c[nil] or the
  value component is ~c[nil]), then the state is reverted so that the
  proof-checker's state (including the behavior of ~c[restore]) is set
  back to what it was before the ~c[sequence] instruction was executed.
  Otherwise, unless ~c[no-restore-flg] is set, the state is changed so
  that the ~c[restore] command will now undo the effect of this ~c[sequence]
  instruction (even if there were nested calls to ~c[sequence]).

  Finally, as each instruction in ~c[instruction-list] is executed, the
  prompt and that instruction will be printed, unless the global state
  variable ~c[print-prompt-and-instr-flg] is unbound or ~c[nil] and the
  parameter ~c[no-prompt-flg] is supplied and not ~c[nil]."

  ;; This is the only place where the pc-prompt gets lengthened.
  ;; Also note that we always lengthen the prompt, but we only do the printing
  ;; if no-prompt-flg is nil AND print-prompt-and-instr-flg is non-nil.
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
                                  (print-prompt-and-instr-flg))
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
                                     proof-checker.~|")
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

  "run the given instructions, and ``succeed'' if and only if they ``fail''~/

  Example:
  (negate prove)~/
  ~bv[]
  General form:
  (negate &rest instruction-list)
  ~ev[]
  Run the indicated instructions exactly in the sense of ~c[do-all], and
  ``succeed'' if and only if they ``fail''.

  ~st[Remark:]  ~c[Negate] instructions will never produce hard ``failures''."

  (value (list :sequence instr-list nil nil
               '(mv nil
                    (if (or (f-get-global 'erp state)
                            (null (f-get-global 'val state)))
                        t
                      nil)))))

(define-pc-macro succeed (&rest instr-list)

  ;; I won't make this atomic, since I view this as just a sequencer
  ;; command that should ultimately "disappear" in favor of its arguments.

  "run the given instructions, and ``succeed''~/
  ~bv[]
  Example:
  (succeed induct p prove)~/

  General Form:
  (succeed &rest instruction-list)
  ~ev[]
  Run the indicated instructions until there is a hard ``failure'',
  and ``succeed''.  (See the documentation for ~c[sequence] for an
  explanation of ``success'' and ``failure''.)"

  (mv nil
      (list :sequence
            instr-list nil nil '(mv nil t))
      state))

(define-pc-macro do-all (&rest instr-list)

  "run the given instructions~/
  ~bv[]
  Example:
  (do-all induct p prove)~/

  General Form:
  (do-all &rest instruction-list)
  ~ev[]
  Run the indicated instructions until there is a hard ``failure''.
  The instruction ``succeeds'' if and only if each instruction in
  ~c[instruction-list] does.  (See the documentation for ~c[sequence] for an
  explanation of ``success'' and ``failure.'')  As each instruction is
  executed, the system will print the usual prompt followed by that
  instruction, unless the global state variable
  ~c[print-prompt-and-instr-flg] is ~c[nil].

  ~st[Remark:]  If ~c[do-all] ``fails'', then the failure is hard if and only
  if the last instruction it runs has a hard ``failure''.

  Obscure point:  For the record, ~c[(do-all ins_1 ins_2 ... ins_k)] is
  the same as ~c[(sequence (ins_1 ins_2 ... ins_k))]."

  (mv nil (list :sequence instr-list)
      state))

(define-pc-macro do-strict (&rest instr-list)

  "run the given instructions, halting once there is a ``failure''~/
  ~bv[]
  Example:
  (do-strict induct p prove)~/

  General Form:
  (do-strict &rest instruction-list)
  ~ev[]
  Run the indicated instructions until there is a (hard or soft)
  ``failure''.  In fact ~c[do-strict] is identical in effect to ~c[do-all],
  except that ~c[do-all] only halts once there is a hard ``failure''.  See
  the documentation for ~c[do-all]."

  (mv nil (list :sequence instr-list t)
      state))

(define-pc-macro do-all-no-prompt (&rest instr-list)

  "run the given instructions, halting once there is a ``failure''~/
  ~bv[]
  Example:
  (do-all-no-prompt induct p prove)~/

  General Form:
  (do-all-no-prompt &rest instruction-list)
  ~ev[]
  ~c[Do-all-no-prompt] is the same as ~c[do-all], except that the prompt and
  instruction are not printed each time, regardless of the value of
  ~c[print-prompt-and-instr-flg].  Also, restoring is disabled.  See the
  documentation for ~c[do-all]."

  (mv nil (list :sequence instr-list nil nil nil t t)
      state))

(define-pc-macro th (&optional hyps-indices govs-indices)

  "print the top-level hypotheses and the current subterm~/
  ~bv[]
  Examples:
  th               -- print all (top-level) hypotheses and the current
                      subterm
  (th (1 3) (2 4)) -- print hypotheses 1 and 3 and governors 2 and 4,
                      and the current subterm
  (th (1 3) t)     -- print hypotheses 1 and 3 and all governors, and
                      the current subterm~/

  General Form:
  (th &optional hyps-indices govs-indices)
  ~ev[]
  Print hypotheses and the current subterm.  The printing of
  hypotheses (and perhaps governors) are controlled as in the ~c[hyps]
  command; see its documentation.

  Historical note:  The name ~c[th] is adapted from the Gypsy Verification
  Environment, where ~c[th] abbreviates the command ~c[theorem], which
  says to print information on the current goal."

  (declare (ignore hyps-indices govs-indices))

  (when-goals-trip
   (value `(do-all-no-prompt (hyps ,@args)
                             (lisp (io? proof-checker nil state
                                        nil
                                        (fms0 "~%The current subterm is:~%")))
                             p))))

(define-pc-macro protect (&rest instr-list)

  "run the given instructions, reverting to existing state upon
  failure~/
  ~bv[]
  Example:
  (protect induct p prove)~/

  General Form:
  (protect &rest instruction-list)
  ~ev[]
  ~c[Protect] is the same as ~c[do-strict], except that as soon as an
  instruction ``fails'', the state-stack reverts to what it was before
  the ~c[protect] instruction began, and ~c[restore] is given the same meaning
  that it had before the ~c[protect] instruction began.  See the
  documentation for ~c[do-strict]."

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

  "change to another goal.~/
  ~bv[]
  Examples:
  (change-goal (main . 1)) -- change to the goal (main . 1)
  change-goal              -- change to the next-to-top goal~/

  General Form:
  (change-goal &optional goal-name end-flg)
  ~ev[]
  Change to the goal with the name ~c[goal-name], i.e. make it the
  current goal.  However, if ~c[goal-name] is ~c[nil] or is not supplied, then
  it defaults to the next-to-top goal, i.e., the second goal in the
  stack of goals.  If ~c[end-flg] is supplied and not ~c[nil], then move the
  current goal to the end of the goal stack; else merely swap it with
  the next-to-top goal.  Also see documentation for ~c[cg]."

  (cond
   ((null goals)
    (pprogn (print-all-goals-proved-message state)
            (mv nil state)))
   ((null (cdr goals))
    (print-no-change2 "The current goal is the only unproved goal."))
   ((null name)
    (pprogn (io? proof-checker nil state
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

  "change to another goal.~/
  ~bv[]
  Examples:
  (cg (main . 1)) -- change to the goal (main . 1)
  cg              -- change to the next-to-top goal~/

  General Form:
  (CG &OPTIONAL goal-name)
  ~ev[]
  Same as ~c[(change-goal goal-name t)], i.e. change to the indicated
  and move the current goal to the end of the goal stack."

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

  "switch a hypothesis with the conclusion, negating both~/
  ~bv[]
  Example:
  (contrapose 3)~/

  General Form:
  (contrapose &optional n)
  ~ev[]
  The (optional) argument ~c[n] should be a positive integer that does
  not exceed the number of hypotheses.  Negate the current conclusion
  and make it the ~c[n]th hypothesis, while negating the current ~c[n]th
  hypothesis and making it the current conclusion.  If no argument is
  supplied then the effect is the same as for ~c[(contrapose 1)].

  ~st[Remark:] By ``negate'' we mean an operation that replaces ~c[nil] by
  ~c[t], ~c[x] by ~c[nil] for any other explicit value ~c[x], ~c[(not x)] by
  ~c[x], and any other ~c[x] by ~c[(not x)]."

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

  "same as ~c[contrapose]~/

  see documentation for ~c[contrapose]~/ "

  (declare (ignore n))
  (value (cons :contrapose args)))

(define-pc-atomic-macro pro ()

  "repeatedly apply promote~/
  ~bv[]
  Example and General Form:
  pro
  ~ev[]~/

  Apply the ~c[promote] command until there is no change.  This command
  ``succeeds'' exactly when at least one call of ~c[promote] ``succeeds''.
  In that case, only a single new proof-checker state will be
  created."

  (value '(quiet (repeat promote))))

(define-pc-atomic-macro nx ()

  "move forward one argument in the enclosing term~/
  ~bv[]
  Example and General Form:
  nx
  ~ev[]
  For example, if the conclusion is ~c[(= x (* (- y) z))] and the
  current subterm is ~c[x], then after executing ~c[nx], the current
  subterm will be ~c[(* (- y) z)].~/

  This is the same as ~c[up] followed by ~c[(dive n+1)], where ~c[n] is the
  position of the current subterm in its parent term in the
  conclusion.  Thus in particular, the ~c[nx] command fails if one is
  already at the top of the conclusion.

  See also ~c[up], ~c[dive], ~c[top], and ~c[bk]."

  (when-goals-trip
   (let ((current-addr (current-addr t)))
     (if current-addr
         (value `(protect up ,(1+ (car (last current-addr)))))
       (pprogn (print-no-change "NX failed:  already at the top!")
               (value :fail))))))

(define-pc-atomic-macro bk ()

  "move backward one argument in the enclosing term~/
  ~bv[]
  Example and General Form:
  bk
  ~ev[]
  For example, if the conclusion is ~c[(= x (* (- y) z))] and the current
  subterm is ~c[(* (- y) z)], then after executing ~c[bk], the current subterm
  will be ~c[x].~/

  Move to the previous argument of the enclosing term.

  This is the same as ~c[up] followed by ~c[(dive n-1)], where ~c[n] is the
  position of the current subterm in its parent term in the
  conclusion.  Thus in particular, the ~c[nx] command fails if one is
  already at the top of the conclusion.

  See also ~c[up], ~c[dive], ~c[top], and ~c[bk]."

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

  "prettyprint the conclusion, highlighting the current term~/
  ~bv[]
  Example and General Form:
  p-top
  ~ev[]
  For example, if the conclusion is ~c[(equal (and x (p y)) (foo z))] and
  the current subterm is ~c[(p y)], then ~c[p-top] will print
  ~c[(equal (and x (*** (p y) ***)) (foo z))].~/

  Prettyprint the the conclusion, highlighting the current term.  The
  usual user syntax is used, as with the command ~c[p] (as opposed to ~c[pp]).
  This is illustrated in the example above, where one would ~c[*not*] see
  ~c[(equal (if x (*** (p y) ***) 'nil) (foo z))].

  ~st[Remark] (obscure): In some situations, a term of the form ~c[(if x t y)]
  occurring inside the current subterm will not print as ~c[(or x y)], when
  ~c[x] isn't a call of a boolean primitive.  There's nothing incorrect about
  this, however."

  (when-goals
   (let ((conc (conc t))
         (current-addr (current-addr t))
         (stars (intern$ "***" (f-get-global 'current-package state))))
     (io? proof-checker nil state
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

  "repeat the given instruction until it ``fails''~/
  ~bv[]
  Example:
  (repeat promote)~/

  General Form:
  (repeat instruction)
  ~ev[]
  The given ~c[instruction] is run repeatedly until it ``fails''.

  ~st[Remark:]  There is nothing here in general to prevent the instruction
  from being run after all goals have been proved, though this is
  indeed the case for primitive instructions."

  (value `(succeed (repeat-rec ,instr))))

(define-pc-macro repeat-rec (instr)

  "auxiliary to ~c[repeat]~/

  See documentation for ~c[repeat].~/ "

  (value `(do-strict ,instr (repeat-rec ,instr))))

(defmacro define-pc-bind (name args &optional doc-string declare-form)
  (mv-let (doc-string declare-form)
          (if (and (null declare-form)
                   (not (stringp doc-string)))
              (mv nil doc-string)
            (mv doc-string declare-form))
          `(define-pc-meta ,name (&rest instr-list)
             ,@ (and doc-string (list doc-string))
             ,@(and declare-form (list declare-form))
             (state-global-let*
              (,args)
              (pc-main-loop instr-list nil t (print-prompt-and-instr-flg) state)))))

;; ****** Fix the documentation and code below once I can turn off
;; prover IO.
(define-pc-bind quiet
  (inhibit-output-lst
   (union-eq '(prove proof-checker proof-tree warning observation)
             (f-get-global 'inhibit-output-lst state)))

  "run instructions without output~/
  ~bv[]
  Example:
  (quiet induct prove)~/

  General Form:
  (quiet &rest instruction-list)
  ~ev[]
  Run the ~c[instruction-list] through the top-level loop with no output.

  See also ~c[noise]."
)

(define-pc-bind noise (inhibit-output-lst nil)

  "run instructions with output~/
  ~bv[]
  Example:
  (noise induct prove)~/

  General Form:
  (noise &rest instruction-list)
  ~ev[]
  Run the ~c[instruction-list] through the top-level loop with output.

  In fact, having output is the default.  ~c[Noise] is useful inside a
  surrounding call of ~c[quiet], when one temporarily wants output.  For
  example, if one wants to see output for a ~c[prove] command immediately
  following an ~c[induct] command but before an ~c[s] command, one may want to
  submit an instruction like ~c[(quiet induct (noise prove) s)].  See also
  ~c[quiet].")

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
                      (not (equiv-refinementp (ffn-symb c) equiv w)))
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
             "The proof-checker's atomic macro IF-NOT-PROVED requires the ~
              indicated goal to be the current goal.  However, the current ~
              goal is ~p0 while the first argument to IF-NOT-PROVED is ~p1."
             (goal-name t)
             goal-name)
         (declare (ignore erp val))
         (value 'fail)))
    (value :skip)))

(define-pc-atomic-macro = (&optional x y &rest rest-args)

  "attempt an equality (or equivalence) substitution~/
  ~bv[]
  Examples:
  =     -- replace the current subterm by a term equated to it in
           one of the hypotheses (if such a term exists)
  (= x) -- replace the current subterm by x, assuming that the prover
           can show that they are equal
  (= (+ x y) z)
        -- replace the term (+ x y) by the term z inside the current
           subterm, assuming that the prover can prove
           (equal (+ x y) z) from the current top-level hypotheses
           or that this term or (equal z (+ x y)) is among the
           current top-level hypotheses or the current governors
  (= & z)
        -- exactly the same as above, if (+ x y) is the current
           subterm
  (= (+ x y) z :hints :none)
        -- same as (= (+ x y) z), except that a new subgoal is
           created with the current goal's hypotheses and governors
           as its top-level hypotheses and (equal (+ x y) z) as its
           conclusion
  (= (+ x y) z 0)
        -- exactly the same as immediately above
  (= (p x)
     (p y)
     :equiv iff
     :otf-flg t
     :hints ((\"Subgoal 2\" :BY FOO) (\"Subgoal 1\" :use bar)))
        -- same as (= (+ x y) z), except that the prover uses
           the indicated values for otf-flg and hints, and only
           propositional (iff) equivalence is used (however, it
           must be that only propositional equivalence matters at
           the current subterm)~/

  General Form:
  (= &optional x y &rest keyword-args)
  ~ev[]
  If terms ~c[x] and ~c[y] are supplied, then replace ~c[x] by ~c[y] inside the
  current subterm if they are ``known'' to be ``equal''.  Here
  ``known'' means the following:  the prover is called as in the ~c[prove]
  command (using ~c[keyword-args]) to prove ~c[(equal x y)], except that a
  keyword argument ~c[:equiv] is allowed, in which case ~c[(equiv x y)] is
  proved instead, where ~c[equiv] is that argument.  (See below for how
  governors are handled.)

  Actually, ~c[keyword-args] is either a single non-keyword or is a list
  of the form ~c[((kw-1 x-1) ... (kw-n x-n))], where each ~c[kw-i] is one of
  the keywords ~c[:equiv], ~c[:otf-flg], ~c[:hints].  Here ~c[:equiv] defaults to
  ~c[equal] if the argument is not supplied or is ~c[nil], and otherwise
  should be the name of an ACL2 equivalence relation.  ~c[:Otf-flg] and
  ~c[:hints] give directives to the prover, as explained above and in the
  documentation for the ~c[prove] command; however, no prover call is made
  if ~c[:hints] is a non-~c[nil] atom or if ~c[keyword-args] is a single
  non-keyword (more on this below).

  ~em[Remarks on defaults]

     (1) If there is only one argument, say ~c[a], then ~c[x] defaults to the
  current subterm, in the sense that ~c[x] is taken to be the current
  subterm and ~c[y] is taken to be ~c[a].

     (2) If there are at least two arguments, then ~c[x] may be the symbol
  ~c[&], which then represents the current subterm.  Thus, ~c[(= a)] is
  equivalent to ~c[(= & a)].  (Obscure point:  actually, ~c[&] can be in any
  package, except the keyword package.)

     (3) If there are no arguments, then we look for a top-level
  hypothesis or a governor of the form ~c[(equal c u)] or ~c[(equal u c)],
  where ~c[c] is the current subterm.  In that case we replace the current
  subterm by ~c[u].

  As with the ~c[prove] command, we allow goals to be given ``bye''s in
  the proof, which may be generated by a ~c[:hints] keyword argument in
  ~c[keyword-args].  These result in the creation of new subgoals.

  A proof is attempted unless the ~c[:hints] argument is a non-~c[nil]
  atom other than :~c[none], or unless there is one element of
  ~c[keyword-args] and it is not a keyword.  In that case, if there are
  any hypotheses in the current goal, then what is attempted is a
  proof of the implication whose antecedent is the conjunction of the
  current hypotheses and governors and whose conclusion is the
  appropriate ~c[equal] term.

  ~st[Remarks:]  (1) It is allowed to use abbreviations in the hints.
  (2) The keyword :~c[none] has the special role as a value of
  :~c[hints] that is shown clearly in an example above.  (3) If there
  are governors, then the new subgoal has as additional hypotheses the
  current governors."

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
                               (getprop 'equal 'coarsenings nil
                                        'current-acl2-world w)))
               (pprogn (print-no-change
                        "The ``equivalence relation'' that you supplied, ~p0, is
                      not known to ACL2 as an equivalence relation."
                        (list (cons #\0 equiv)))
                       (value :fail)))
              ((null args)
               (mv-let (found-hyp new)
                 (find-equivalence-hyp-term-no-target
                  1 current-term
                  (flatten-ands-in-lit-lst (append hyps governors))
                  equiv w)
                 (if found-hyp
                     (pprogn
                      (io? proof-checker nil state
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

  "run the first instruction; if (and only if) it ``fails'', run the
  second~/
  ~bv[]
  Example:
  (orelse top (print \"Couldn't move to the top\"))~/

  General form:
  (orelse instr1 instr2)
  ~ev[]
  Run the first instruction.  Then if it ``fails'', run the second
  instruction also; otherwise, stop after the first.

  This instruction ``succeeds'' if and only if either ~c[instr1]
  ``succeeds'', or else ~c[instr2] ``succeeds''.  If it ``fails'', then
  the failure is soft."

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
   (getprop (ffn-symb current-term) 'lemmas nil 'current-acl2-world wrld)
   1 target-name-or-rune target-index wrld))

(define-pc-help show-rewrites (&optional rule-id enabled-only-flg)

  "display the applicable rewrite rules~/
  ~bv[]
  Example:
  show-rewrites~/

  General Form:
  (show-rewrites &optional rule-id enabled-only-flg)
  ~ev[]
  Display rewrite rules whose left-hand side matches the current subterm.  This
  command shows how the ~c[rewrite] command can be applied.  If ~c[rule-id] is
  supplied and is a name (non-~c[nil] symbol) or a rune, then only the
  corresponding rewrite rule(s) will be displayed, while if ~c[rule-id] is a
  positive integer ~c[n], then only the ~c[n]th rule that would be in the list
  is displayed.  In each case, the display will point out when a rule is
  currently disabled (in the interactive environment), except that if
  ~c[enabled-only-flg] is supplied and not ~c[nil], then disabled rules will
  not be displayed at all.  Finally, among the free variables of any rule (those
  occurring in the rule that do not occur in the left-hand side of its
  conclusion), those that would remain free if the rule were applied will be
  displayed.  See also the documentation for ~c[rewrite]."

  (when-goals
   (let ((conc (conc t))
         (current-addr (current-addr t))
         (w (w state)))
     (let ((ens (make-pc-ens (pc-ens t) state))
           (current-term (fetch-term conc current-addr))
           (abbreviations (abbreviations t))
           (term-id-iff (term-id-iff conc current-addr t))
           (all-hyps (union-equal (hyps t) (governors conc current-addr))))
       (show-rewrites-fn rule-id enabled-only-flg ens current-term
                         abbreviations term-id-iff all-hyps
                         (geneqv-at-subterm-top conc current-addr ens w)
                         nil state)))))

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
                   (io? proof-checker nil state
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
    (pprogn (io? proof-checker nil state
                 (sub)
                 (fms0 "~|A substitution must be a true (null-terminated) ~
                        list, but~%~x0 is not.~|"
                       (list (cons #\0 sub))))
            (mv t nil state)))
   ((not (and (symbol-alistp sub)
              (single-valued-symbolp-alistp sub)))
    (pprogn (io? proof-checker nil state
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
                          (pprogn (io? proof-checker nil state
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

  "apply a rewrite rule~/
  ~bv[]
  Examples:
  (rewrite reverse-reverse)
     -- apply the rewrite rule `reverse-reverse'
  (rewrite (:rewrite reverse-reverse))
     -- same as above
  (rewrite 2)
     -- apply the second rewrite rule, as displayed by show-rewrites
  rewrite
     -- apply the first rewrite rule, as displayed by show-rewrites
  (rewrite transitivity-of-< ((y 7)))
     -- apply the rewrite rule transitivity-of-< with the substitution
        that associates 7 to the ``free variable'' y
  (rewrite foo ((x 2) (y 3)) t)
     -- apply the rewrite rule foo by substituting 2 and 3 for free
        variables x and y, respectively, and also binding all other
        free variables possible by using the current context
        (hypotheses and governors)~/

  General Form:
  (rewrite &optional rule-id substitution instantiate-free)
  ~ev[]
  Replace the current subterm with a new term by applying a rewrite
  rule.  The replacement will be done according to the information provided by
  the ~c[show-rewrites] (~c[sr]) command.

  If ~c[rule-id] is a positive integer ~c[n], then the ~c[n]th rewrite
  rule as displayed by ~c[show-rewrites] is the one that is applied.  If
  ~c[rule-id] is ~c[nil] or is not supplied, then it is treated as the number
  1.  Otherwise, ~c[rule-id] should be either a rune of or name of a
  rewrite rule.  If a name is supplied, then any rule of that name may
  be used.  We say more about this, and describe the other optional arguments,
  below.

  Consider first the following example.  Suppose that the current subterm is
  ~c[(reverse (reverse y))] and that there is a rewrite rule called
  ~c[reverse-reverse] of the form
  ~bv[]
  (implies (true-listp x)
           (equal (reverse (reverse x)) x)) .
  ~ev[]
  Then the instruction ~c[(rewrite reverse-reverse)] would cause the current
  subterm to be replaced by ~c[y] and would create a new goal with conclusion
  ~c[(true-listp y)].  An exception is that if the top-level hypotheses imply
  ~c[(true-listp y)] using only ``trivial reasoning''
  (more on this below), then no new goal is created.

  If the ~c[rule-id] argument is a number or is not supplied, then the system
  will store an instruction of the form ~c[(rewrite name ...)], where ~c[name]
  is the name of a rewrite rule; this is in order to make it easier to replay
  instructions when there have been changes to the history.  Actually, instead
  of the name (whether the name is supplied or calculated), the system stores
  the ~il[rune] if there is any chance of ambiguity.  (Formally, ``ambiguity''
  here means that the rune being applied is of the form
  ~c[(:rewrite name . index)], where index is not ~c[nil].)

  Speaking in general, then, a ~c[rewrite] instruction works as follows:

  First, a rewrite rule is selected according to the arguments of the
  ~c[rewrite] instruction.  The selection is made as explained under ``General
  Form'' above.

  Next, the left-hand side of the rule is matched with the current subterm,
  i.e., a substitution ~c[unify-subst] is found such that if one instantiates
  the left-hand side of the rule with ~c[unify-subst], then one obtains the
  current subterm.  If this match fails, then the instruction fails.

  Next, an attempt is made to relieve (discharge) the hypotheses, much as the
  theorem prover relieves hypotheses except that there is no call to the
  rewriter.  First, the substitution ~c[unify-subst] is extended with the
  ~c[substitution] argument, which may bind free variables
  (~pl[free-variables]).  Each hypothesis of the ~il[rewrite] rule is then
  considered in turn, from first to last.  For each hypothesis, first the
  current substitution is applied, and then the system checks whether the
  hypothesis is ``clearly'' true in the current context.  If there are
  variables in the hypotheses of the rewrite rule that are not bound by the
  current substitution, then a weak attempt is made to extend that substitution
  so that the hypothesis is present in the current context (see the
  documentation for the proof-checker ~c[hyps] command under
  ~il[proof-checker-commands]), much as would be done by the theorem prover's
  rewriter.

  If in the process above there are free variables, but the proof-checker can
  see how to bind them to relieve all hypotheses, then it will do so in both
  the ~c[show-rewrites] (~c[sr]) and ~c[rewrite] commands.  But normally, if
  even one hypothesis remains unrelieved, then no automatic extension of the
  substitution is made.  Except, if ~c[instantiate-free] is not ~c[nil], then
  that extension to the substitution is kept.

  Finally, the instruction is applied as follows.  The current subterm is
  replaced by applying the final substitution described above to the right-hand
  side of the selected rewrite rule.  And, one new subgoal is created for each
  unrelieved hypothesis of the rule, whose top-level hypotheses are the
  governors and top-level hypotheses of the current goal and whose conclusion
  and current subterm are the instance, by that same final substitution, of
  that unrelieved hypothesis.

  ~st[Remark:]  The substitution argument should be a list whose elements
  have the form ~c[(variable term)], where ~c[term] may contain
  abbreviations."

  (mv-let
   (erp sub state)
   (translate-subst-abb raw-sub abbreviations state)
   (if erp
       (print-no-change2 "~x0 failed."
                         (list (cons #\0 (cons :rewrite args))))
     (let ((name (and (symbolp rule-id) rule-id))
           (rune (and (consp rule-id)
                      (equal (car rule-id) :rewrite)
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
          "The rule-id argument to REWRITE must be a ~
           name, a positive integer, or a rewrite ~
           rule rune, but ~x0 is none of these.~|"
          (list (cons #\0 rule-id))))
        (t
         (mv-let
          (flg hyps-type-alist ttree)
          (hyps-type-alist assumptions pc-ens w state)
          (declare (ignore ttree))
          (if flg
              (print-no-change2
               "Contradiction in the hypotheses!~%~
                The S command should complete this goal.~|")
            (let ((app-rewrite-rules
                   (applicable-rewrite-rules
                    current-term conc current-addr (or name rune) index
                    pc-ens w)))
              (if (null app-rewrite-rules)
                  (if (and index (> index 1))
                      (print-no-change2
                       "There are fewer than ~x0 applicable rewrite rules.~%"
                       (list (cons #\0 index)))
                    (print-no-change2 "There are no applicable rewrite rules.~%"))
                (let* ((sar (car app-rewrite-rules))
                       (lemma (access sar sar :lemma))
                       (start-alist (access sar sar :alist))
                       (alist (append start-alist sub))
                       (rhs (access rewrite-rule lemma :rhs))
                       (lemma-hyps (access rewrite-rule lemma :hyps))
                       (lemma-rune (access rewrite-rule lemma :rune))
                       (lemma-name (cadr lemma-rune))
                       (lemma-id (if (cddr lemma-rune) lemma-rune lemma-name))
                       (non-free (union-eq (intersection-domains sub start-alist)
                                           (set-difference-eq
                                            (strip-cars sub)
                                            (append (all-vars rhs)
                                                    (all-vars1-lst lemma-hyps nil))))))
                  (if non-free
                      (print-no-change2
                       "The variable~#0~[~/~/s~] ~&1 supplied by the substitution in ~
                        this instruction ~#0~[~/is~/are~] not free for instantiation ~
                        in the current context.~|"
                       (list (cons #\0 (zero-one-or-more (length non-free)))
                             (cons #\1 non-free)))
                    (mv-let (subst-hyps unify-subst ttree2)
                            (unrelieved-hyps lemma-rune lemma-hyps alist
                                             hyps-type-alist instantiate-free w
                                             state pc-ens nil)
                            (pprogn
                             (let ((extra-alist (alist-difference-eq unify-subst alist)))
                               (if extra-alist
                                   (io? proof-checker nil state
                                        (abbreviations extra-alist sub
                                                       lemma-id)
                                        (fms0 "~|Rewriting with ~x0 under the ~
                                               following extension of the the ~
                                               substitution generated by ~
                                               matching that rewrite rule with ~
                                               the current term ~#1~[ (after ~
                                               extending it with the ~
                                               substitution ~x2 supplied in ~
                                               the instruction)~/~]:  ~x3.~|"
                                              (list (cons #\0 lemma-id)
                                                    (cons #\1 (if sub 0 1))
                                                    (cons #\2 sub)
                                                    (cons #\3 (untranslate-subst-abb
                                                               extra-alist
                                                               abbreviations
                                                               state)))))
                                 (io? proof-checker nil state
                                      (lemma-id)
                                      (fms0 "~|Rewriting with ~x0.~|"
                                            (list (cons #\0 lemma-id))))))
                             (let ((runes (all-runes-in-ttree ttree2 nil)))
                               (if runes
                                   (io? proof-checker nil state
                                        (runes)
                                        (fms0 "~|--NOTE-- Using the following ~
                                               runes in addition to the ~
                                               indicated rewrite rule:~%  ~
                                               ~x0.~|"
                                              (list (cons #\0 runes))))
                                 state))
                             (let ((new-goals
                                    (make-new-goals-fixed-hyps subst-hyps
                                                               assumptions
                                                               goal-name
                                                               depends-on)))
                               (mv-let
                                (new-goal state)
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
                                  (cons (change goal new-goal
                                                :depends-on (+ depends-on (length new-goals)))
                                        (append new-goals (cdr goals)))
                                  :local-tag-tree
                                  (push-lemma lemma-rune ttree2))
                                 state)))))))))))))))))

(defun pc-help-fn (name state)
  ;; Adapted in part from doc-fn.
  (declare (xargs :guard (and (symbolp name)
                              (equal (symbol-package-name name) "ACL2-PC"))))
  (let ((name (if (equal (symbol-name name) "ALL")
                  'proof-checker-commands
                name)))
    (cond
     ((not (or (eq name 'proof-checker-commands)
               (pc-command-type name)))
      (pprogn (io? proof-checker nil state
                   (name)
                   (fms0 "~%*** Undefined command, ~x0.~%"
                         (list (cons #\0 (make-pretty-pc-command name)))))
              (value :invisible)))
     (t
      (let ((channel (proofs-co state))
            (doc-tuple (access-doc-string-data-base name state)))
        (cond ((null doc-tuple)
               (pprogn
                (io? proof-checker nil state
                     (channel name)
                     (fms "No help is available for ~s0.~|"
                          (list (cons #\0 (symbol-name name)))
                          channel state nil))
                (value nil)))
              (t (state-global-let*
                  ((print-doc-start-column nil))
                  (pprogn (print-doc (cons (if (eq name 'proof-checker-commands)
                                               name
                                             (intern-in-keyword-package name))
                                           (cdr doc-tuple))
                                     0
                                     (doc-prefix state)
                                     (doc-markup-table state)
                                     (doc-char-subst-table state)
                                     (doc-fmt-alist state)
                                     channel state)
                          (print-doc doc-tuple 1 (doc-prefix state)
                                     (doc-markup-table state)
                                     (doc-char-subst-table state)
                                     (doc-fmt-alist state)
                                     channel state)
                          (newline channel state)
                          (end-doc channel state))))))))))

(defmacro state-only (triple)
  `(mv-let (erp val state)
           ,triple
           (declare (ignore erp val))
           state))

(define-pc-help help (&optional instr)

  "proof-checker help facility~/
  ~bv[]
  Examples:

  (help all)     -- list all proof-checker commands
  (help rewrite) -- partial documentation on the rewrite command; the
                    rest is available using more or more!

  (help! rewrite) -- full documentation on the rewrite command

  help, help!     -- this documentation (in part, or in totality,
                     respectively)~/

  General Forms:
  (help &optional command)
  (help! &optional command)
  more
  more!
  ~ev[]
  The proof checker supports the same kind of documentation as does
  ACL2 proper.  The main difference is that you need to type
  ~bv[]
  (help command)
  ~ev[]
  in a list rather than ~c[:doc command].  So, to get all the
  documentation on ~c[command], type ~c[(help! command)] inside the
  interactive loop, but to get only a one-line description of the
  command together with some examples, type ~c[(help command)].  In the
  latter case, you can get the rest of the help by typing ~c[more!]; or
  type ~c[more] if you don't necessarily want all the rest of the help at
  once.  (Then keep typing ~c[more] if you want to keep getting more of
  the help for that command.)

  An exception is ~c[(help all)], which prints the documentation topic
  ~c[proof-checker-commands], to show you all possible proof-checker commands.
  So for example, when you see ~c[ACL2-PC::USE] in that list, you can then
  submit ~c[(help use)] or ~c[(help! use)] to get documentation for the
  proof-checker ~c[use] command.

  But summarizing for other than the case of ~c[all]:  as with ACL2, you can
  type either of the following:
  ~bv[]
  more, more!
  -- to obtain more (or, all the rest of) the documentation last
     requested by help (or, outside the proof-checker's loop, :doc)
  ~ev[]
  It has been arranged that the use of ~c[(help command)] will tell you
  just about everything you could want to know about ~c[command], almost
  always by way of examples.  For more details about a command, use
  ~c[help!], ~c[more], or ~c[more!].

  We use the word ``command'' to refer to the name itself, e.g.
  ~c[rewrite].  We use the word ``instruction'' to refer to an input to
  the interactive system, e.g. ~c[(rewrite foo)] or ~c[(help split)].  Of
  course, we allow commands with no arguments as instructions in many
  cases, e.g. ~c[rewrite].  In such cases, ~c[command] is treated identically
  to ~c[(command)]."

  (let ((comm (make-official-pc-command (if args
                                            (if (consp instr) (car instr) instr)
                                          'help))))
    (state-only (pc-help-fn comm state))))

(defun pc-help!-fn (name state)
  ;; Adapted in part from doc-fn.
  (declare (xargs :guard (and (symbolp name)
                              (equal (symbol-package-name name) "ACL2-PC"))))
  (cond
   ((equal (symbol-name name) "ALL")
    (pc-help-fn name state))
   ((not (pc-command-type name))
    (pprogn (io? proof-checker nil state
                 (name)
                 (fms0 "~%*** Undefined command, ~x0.~%"
                       (list (cons #\0 (make-pretty-pc-command name)))))
            (value :invisible)))
   (t
    (let ((channel (proofs-co state))
          (doc-tuple (access-doc-string-data-base name state)))
      (cond ((null doc-tuple)
             (pprogn
              (io? proof-checker nil state
                   (channel name)
                   (fms "No help is available for ~s0.~|"
                        (list (cons #\0 (symbol-name name)))
                        channel state nil))
              (value nil)))
            (t (state-global-let*
                ((print-doc-start-column nil))
                (pprogn (print-doc (cons (intern-in-keyword-package name)
                                         (cdr doc-tuple))
                                   0 (doc-prefix state)
                                   (doc-markup-table state)
                                   (doc-char-subst-table state)
                                   (doc-fmt-alist state)
                                   channel state)
                        (print-doc doc-tuple 1 (doc-prefix state)
                                   (doc-markup-table state)
                                   (doc-char-subst-table state)
                                   (doc-fmt-alist state)
                                   channel state)
                        (princ-prefix (doc-prefix state) channel state)
                        (newline channel state)
                        (more-fn t state)))))))))

(define-pc-help help! (&optional instr)

  "proof-checker help facility~/

  Same as ~c[help], except that the entire help message is printed without
  any need to invoke ~c[more!] or ~c[more].~/

  Invoke ~c[help] for documentation about the proof-checker help facility."

  (let ((comm (make-official-pc-command (if instr
                                            (if (consp instr) (car instr) instr)
                                          'help))))
    (state-only (pc-help!-fn comm state))))

(define-pc-macro help-long (&rest args)

  "same as ~c[help!]~/

  See the documentation for ~c[help!].~/

  ~c[Help-long] has been included in addition to ~c[help!] for historical
  reasons.  (Such a command is included in Pc-Nqthm)."

  (value (cons 'help! args)))

(define-pc-help more ()

  "proof-checker help facility~/

  Continues documentation of last proof-checker command visited with
  ~c[help].~/

  Invoke ~c[help] for documentation about the proof-checker help
  facility."

  (state-only (more-fn 0 state)))

(define-pc-help more! ()

  "proof-checker help facility~/

  Continues documentation of last proof-checker command visited with
  ~c[help], until all documentation on that command is printed out.~/

  Invoke ~c[help] for documentation about the proof-checker help facility."

  (state-only (more-fn t state)))

(defun pc-rewrite*
  (term type-alist geneqv iff-flg wrld rcnst old-ttree pot-lst normalize-flg
        rewrite-flg ens state repeat backchain-limit)
  ;; *** I'm only calling this with pot-lst set to nil for now, but if I
  ;; can figure out a good way to do linear stuff in the proof-checker,
  ;; I may change that.  Also, note that rcnst can be anything (and is ignored) if rewrite-flg
  ;; is not set.
  (cond ((f-big-clock-negative-p state)
         (mv t nil state))
        (t
         (mv-let (nterm old-ttree)
                 (if normalize-flg
                     (normalize term iff-flg type-alist ens wrld old-ttree)
                   (mv term old-ttree))
                 (mv-let (newterm ttree)
                         (if rewrite-flg
                             (let ((gstack nil))
                               (rewrite-entry
                                (rewrite nterm nil 'proof-checker)
                                :rdepth (rewrite-stack-limit wrld)
                                :obj '?
                                :fnstack nil
                                :ancestors nil
                                :simplify-clause-pot-lst pot-lst
                                :rcnst (change rewrite-constant rcnst
                                               :current-literal
                                               (make current-literal
                                                     :not-flg nil
                                                     :atm nterm))
                                :gstack gstack
                                :ttree old-ttree))
                           (mv nterm old-ttree))
                         (cond
                          ((equal newterm nterm)
                           (mv newterm old-ttree state))
                          ((<= repeat 0) ;****perhaps should cause error in this case
                           (mv newterm ttree state))
                          (t
                           (pc-rewrite* newterm type-alist geneqv iff-flg wrld rcnst
                                        ttree
                                        pot-lst normalize-flg rewrite-flg ens state
                                        (1- repeat) backchain-limit))))))))

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

(define-pc-primitive s (&rest args)

  "simplify the current subterm~/
  ~bv[]
  Examples:
  S  -- simplify the current subterm
  (S :backchain-limit 2 :normalize t :expand (append x z))
     -- simplify the current subterm, but during the rewriting
        process first ``normalize'' it by pushing IFs to the
        top-level, and also force the term (append x z) to be
        expanded during the rewriting process~/

  General Form:
  (s &key rewrite normalize backchain-limit repeat in-theory hands-off
          expand)
  ~ev[]
  Simplify the current subterm according to the keyword parameters
  supplied.  First if-normalization is applied (unless the ~c[normalize]
  argument is ~c[nil]), i.e., each subterm of the form
  ~c[(f ... (if test x y) ...)]  is replaced by the term
  ~c[(if test (f ... x ...) (f ... y ...))]  except, of course, when
  ~c[f] is ~c[if] and the indicated ~c[if] subterm is in the second or
  third argument position.  Then rewriting is applied (unless the
  rewrite argument is ~c[nil]).  Finally this pair of actions is
  repeated ~-[] until the rewriting step causes no change in the term.
  A description of each parameter follows.
  ~bv[]
  :rewrite -- default t
  ~ev[]
  When non-~c[nil], instructs the system to use ACL2's rewriter (or,
  something close to it) during simplification.
  ~bv[]
  :normalize -- default t
  ~ev[]
  When non-~c[nil], instructs the system to use if-normalization (as
  described above) during simplification.
  ~bv[]
  :backchain-limit -- default 0
  ~ev[]
  Sets the number of recursive calls to the rewriter that are
  allowed for backchaining.  Even with the default of 0, some
  reasoning is allowed (technically speaking, type-set reasoning is
  allowed) in the relieving of hypotheses.  The value should be
  ~c[nil] or a non-negative integer, and limits backchaining only
  for rewriting, not for type-set reasoning.
  ~bv[]
  :repeat -- default 0
  ~ev[]
  Sets the number of times the current term is to be rewritten.  If
  this value is ~c[t], then the default is used (as specified by the
  constant ~c[*default-s-repeat-limit*]).
  ~bv[]
  :in-theory, :hands-off, :expand
  ~ev[]
  These have their usual meaning; ~pl[hints].

  ~st[Remark:]  if conditional rewrite rules are used that cause case splits
  because of the use of ~c[force], then appropriate new subgoals will be
  created, i.e., with the same current subterm (and address) but with
  each new (forced) hypothesis being negated and then used to create a
  corresponding new subgoal.  In that case, the current goal will have
  all such new hypotheses added to the list of top-level hypotheses."

  (if (not (keyword-value-listp args))
      (print-no-change2
       "The argument list to S must be a KEYWORD-VALUE-LISTP, i.e. a list of ~
        the form (:kw-1 val-1 ... :kw-n val-n), where each of the arguments ~
        :kw-i is a keyword.  Your argument list ~x0 does not have this ~
        property.  Try (HELP S)."
       (list (cons #\0 args)))
    (let ((comm (make-official-pc-command 's))
          (w (w state))
          (current-term (fetch-term conc current-addr))
          (assumptions (union-equal hyps (governors conc current-addr))))
      (let ((pc-ens (make-pc-ens pc-ens state)))
        (mv-let
         (bcl-alist rst)
         (pair-keywords '(:backchain-limit :normalize :rewrite :repeat) args)
         (let ((local-backchain-limit
                (or (cdr (assoc-eq :backchain-limit bcl-alist)) 0))

; IF-normalization and rewriting will happen by default

               (normalize
                (let ((pair (assoc-eq :normalize bcl-alist)))
                  (if pair (cdr pair) t)))
               (rewrite
                (let ((pair (assoc-eq :rewrite bcl-alist)))
                  (if pair (cdr pair) t)))
               (repeat
                (let ((pair (assoc-eq :repeat bcl-alist)))
                  (if pair
                      (if (equal (cdr pair) t)
                          *default-s-repeat-limit*
                        (cdr pair))
                    0))))
           (cond
            ((not (or normalize rewrite))
             (print-no-change2 "You may not specify in the S command that ~
                                neither IF normalization nor rewriting is to ~
                                take place."))
            ((and (null rewrite)
                  (or (assoc-eq :backchain-limit bcl-alist)
                      (assoc-eq :repeat bcl-alist)
                      rst))
             (print-no-change2 "When the :REWRITE NIL option is specified, it ~
                                is not allowed to provide arguments other than ~
                                :NORMALIZE T.  The argument list ~x0 violates ~
                                this requirement."
                               (list (cons #\0 args))))
            (t
             (mv-let
              (key-alist new-rst)
              (pair-keywords '(:in-theory :hands-off :expand) rst)
              (declare (ignore key-alist))
              (if new-rst
                  (print-no-change2
                   "The arguments to the S command must all be &KEY arguments, ~
                    which should be among ~&0.  Your argument list ~x1 ~
                    violates this requirement."
                   (list (cons #\0 '(:rewrite :normalize :backchain-limit
                                              :repeat :in-theory :hands-off
                                              :expand))
                         (cons #\1 args)))
                (mv-let
                 (erp hint-settings state)
                 (translate-hint-settings
                  comm "Goal" rst
                  (if args (cons comm (car args)) comm)
                  w state)
                 (if erp
                     (print-no-change2 "S failed.")
                   (mv-let
                    (flg hyps-type-alist ttree)
                    (hyps-type-alist assumptions pc-ens w state)
                    (if flg
                        (if (or (null current-addr) ; optimization
                                (equal assumptions hyps)
                                (mv-let (flg hyps-type-alist ttree)
                                        (hyps-type-alist hyps pc-ens w state)
                                        (declare (ignore hyps-type-alist
                                                         ttree))
                                        flg))
                            (pprogn
                             (io? proof-checker nil state
                                  nil
                                  (fms0 "~|Goal proved:  Contradiction in the ~
                                         hypotheses!~|"))
                             (mv (change-pc-state
                                  pc-state
                                  :goals (cdr goals)
                                  :local-tag-tree ttree)
                                 state))
                          (print-no-change2
                           "A contradiction was found in the current context ~
                            using both the top-level hypotheses and the IF ~
                            tests governing the current term, but not using ~
                            the top-level hypotheses alone.  You may want to ~
                            issue the TOP command and then issue s-prop to ~
                            prune some branches of the conclusion."))
                      (let* ((base-rcnst
                              (and rewrite
                                   (change
                                    rewrite-constant
                                    *empty-rewrite-constant*
                                    :current-enabled-structure pc-ens
                                    :force-info t))))
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
                              (io? proof-checker nil state
                                   nil
                                   (fms0 "~|Note: Ignoring the above theory ~
                                          invariant error.  Proceeding...~|"))
                            state)
                          (if rewrite
                              (maybe-warn-about-theory-from-rcnsts
                               base-rcnst local-rcnst :s pc-ens w state)
                            state)
                          (mv-let (new-term new-ttree state)
                                  (pc-rewrite*
                                   current-term
                                   hyps-type-alist
                                   (geneqv-at-subterm-top conc current-addr
                                                          pc-ens w)
                                   (term-id-iff conc current-addr t)
                                   w local-rcnst nil nil normalize rewrite
                                   pc-ens state repeat local-backchain-limit)
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
                                          state))))))))))))))))))))))

;; The proof-checker's enabled state will be either the global enabled
;; state or else a local one.  The proof-checker command :IN-THEORY
;; takes zero or one arguments, the former specifying ``use the global
;; enabled state'' and the latter specifying ``create a local enabled
;; state from the current proof-checker enabled state by evaluating
;; the theory form that is given.''  This is an easy design to
;; implement:  we'll use NIL in the pc-ens component of the pc-state
;; to mean that we should use the global state, and otherwise we'll
;; store an enabled structure with a root name particular to Pc-ACL2.
;; A subtlety is that (in-theory (current-theory :here)) is not quite
;; equivalent to (in-theory).  The difference is that the former
;; stores a copy of the current global enabled state in the current
;; proof-checker state, and that's what will stay there even if the
;; global state is changed, while the latter stores NIL in the current
;; proof-checker state, which means that we'll use whatever is the
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

  "set the current proof-checker theory~/
  ~bv[]
  Example:
  (in-theory 
     (union-theories (theory 'minimal-theory) '(true-listp binary-append)))~/

  General Form:
  (in-theory &optional atom-or-theory-expression)
  ~ev[]
  If the argument is not supplied, then this command sets the
  current proof-checker theory (see below for explanation) to agree
  with the current ACL2 theory.  Otherwise, the argument should be a
  theory expression, and in that case the proof-checker theory is set
  to the value of that theory expression.

  The current proof-checker theory is used in all calls to the ACL2 theorem
  prover and rewriter from inside the proof-checker.  Thus, the most recent
  ~c[in-theory] instruction in the current ~c[state-stack] has an effect in the
  proof-checker totally analogous to the effect caused by an ~c[in-theory] hint
  or event in ACL2.  All ~c[in-theory] instructions before the last are
  ignored, because they refer to the current theory in the ACL2 ~ilc[state],
  not to the existing proof-checker theory.  For example:
  ~bv[]
     ACL2 !>:trans1 (enable bar)
      (UNION-THEORIES (CURRENT-THEORY :HERE)
                      '(BAR))
     ACL2 !>:trans1 (CURRENT-THEORY :HERE)
      (CURRENT-THEORY-FN :HERE WORLD)
     ACL2 !>
  ~ev[]
  Thus ~c[(in-theory (enable bar))] modifies the current theory of the current
  ACL2 world.  So for example, suppose that ~c[foo] is disabled outside the
  proof checker and you execute the following instructions, in this order.
  ~bv[]
     (in-theory (enable foo))
     (in-theory (enable bar))
  ~ev[]  
  Then after the second of these, ~c[bar] will be enabled in the proof-checker,
  but ~c[foo] will be disabled.  The reason is that
  ~c[(in-theory (enable bar))] instructs the proof-checker to modify the
  current theory (from outside the proof-checker, not from inside the
  proof-checker) by enabling ~c[bar].

  Note that ~c[in-theory] instructions in the proof-checker have no effect
  outside the proof-checker's interactive loop.

  If the most recent ~c[in-theory] instruction in the current state of the
  proof-checker has no arguments, or if there is no ~c[in-theory]
  instruction in the current state of the proof-checker, then the
  proof-checker will use the current ACL2 theory.  This is true even
  if the user has interrupted the interactive loop by exiting and
  changing the global ACL2 theory.  However, if the most recent
  ~c[in-theory] instruction in the current state of the proof-checker had
  an argument, then global changes to the current theory will have no
  effect on the proof-checker state."

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
          (print-no-change2 "The proof-checker enabled/disabled state is ~
                             already set to agree with the global state, so ~
                             your IN-THEORY command is redundant.")
        (mv (change-pc-state pc-state :pc-ens nil)
            state)))))

(define-pc-atomic-macro s-prop (&rest names)

  "simplify propositionally~/
  ~bv[]
  Example:
  s-prop~/

  General Form:
  (s-prop &rest names)
  ~ev[]
  Simplify, using the default settings for ~c[s] (which include
  if-normalization and rewriting without real backchaining), but with respect
  to a theory in which only basic functions and rules (the ones in
  ~c[(theory 'minimal-theory)]), together with the names (or parenthesized
  names) in the ~c[&rest] argument ~c[names], are enabled.

  See also the documentation for ~c[s]."

  (value `(s :in-theory ,(if names
                             `(union-theories ',names
                                              (theory 'minimal-theory))
                           '(theory 'minimal-theory)))))

(define-pc-atomic-macro x (&rest args)

  "expand and (maybe) simplify function call at the current subterm~/
  ~bv[]
  Examples:
  x --  expand and simplify.
  ~ev[]
  For example, if the current subterm is (append a b), then after ~c[x]
  the current subterm will probably be (cons (car a) (append (cdr a)
  b)) if (consp a) and (true-listp a) are among the top-level
  hypotheses and governors.  If there are no top-level hypotheses and
  governors, then after ~c[x] the current subterm will probably be:
  ~bv[]
  (if (true-listp x)
      (if x
          (cons (car x) (append (cdr x) y))
        y)
    (apply 'binary-append (list x y))).~/

  General Form:
  (X &key
     rewrite normalize backchain-limit in-theory hands-off expand)
  ~ev[]
  Expand the function call at the current subterm, and simplify
  using the same conventions as with the ~c[s] command (see documentation
  for ~c[s]).

  Unlike ~c[s], it is permitted to set both ~c[:rewrite] and ~c[:normalize] to
  ~c[nil], which will result in no simplification; see ~c[x-dumb].

  ~st[Remark] (obscure):  On rare occasions the current address may be
  affected by the use of ~c[x].  For example, suppose we have the
  definition
  ~bv[]
  (defun g (x) (if (consp x) x 3))
  ~ev[]
  and then we enter the proof-checker with
  ~bv[]
  (verify (if (integerp x) (equal (g x) 3) t)) .
  ~ev[]
  Then after invoking the instruction ~c[(dive 2 1)], so that the
  current subterm is ~c[(g x)], followed by the instruction ~c[x], we would
  expect the conclusion to be ~c[(if (integerp x) (equal 3 3) t)].
  However, the system actually replaces ~c[(equal 3 3)] with ~c[t] (because we
  use the ACL2 term-forming primitives), and hence the conclusion is actually
  ~c[(if (integerp x) t t)].  Therefore, the current address is put at ~c[(2)]
  rather than ~c[(2 1)].  In such cases, a warning ``~c[NOTE]'' will be printed
  to the terminal.

  The other primitive commands to which the above ``truncation'' note
  applies are ~c[equiv], ~c[rewrite], and ~c[s]."

  (value `(do-strict (expand t) (succeed (s ,@args)))))

;; It was tempting to use the rewrite command to implement expand, but
;; this didn't really allow for expanding to keep lambdas or for the
;; issue of how to deal with guards.  So I'll keep :definition rules
;; separate from :rewrite rules.

(defun remove-trivial-lits-raw (lst type-alist alist wrld ens ttree)
  ;; Removes trivially true lits from lst.  However, we don't touch elements
  ;; of lst that contain free variables (elements of free).
  ;; We apply the substitution at this point because we need to
  ;; know whether a lit contains a free variable (one not bound
  ;; by alist) that might get bound later, thus changing its truth
  ;; value.
  (if (consp lst)
      (mv-let (rest-list ttree)
              (remove-trivial-lits-raw (cdr lst) type-alist alist wrld ens ttree)
              (let ((new-lit (sublis-var alist (car lst))))
                (if (free-varsp (car lst) alist)
                    (mv (cons (car lst) rest-list) ttree)
                  (mv-let (knownp nilp nilp-ttree)
                          (known-whether-nil new-lit type-alist
                                             ens (ok-to-force-ens ens) wrld ttree)
                          (if (and knownp (not nilp))
                              (mv rest-list nilp-ttree)
                            (mv (cons (car lst) rest-list) ttree))))))
    (mv nil ttree)))

(define-pc-primitive expand (&optional
                             ;; nil means eliminate the lambda:
                             do-not-expand-lambda-flg)

  "expand the current function call without simplification~/
  ~bv[]
  Examples:
  expand -- expand and do not simplify.
  ~ev[]
  For example, if the current subterm is ~c[(append a b)], then after
  ~c[(expand t)] the current subterm will be the term:
  ~bv[]
  (if (true-listp x)
      (if x
          (cons (car x) (append (cdr x) y))
        y)
    (apply 'binary-append (list x y)))
  ~ev[]
  regardless of the top-level hypotheses and the governors.~/

  ~bv[]
  General Form:
  (expand &optional do-not-expand-lambda-flg)
  ~ev[]
  Expand the function call at the current subterm, and do not
  simplify.  The options have the following meanings:
  ~bv[]
  do-not-expand-lambda-flg:   default is nil; otherwise, the result
                              should be a lambda expression

  ~ev[]
  See also ~c[x], which allows simplification."

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
        t."))
     (t
      (let* ((fn (ffn-symb term))
             (def-body (and (not (flambdap fn))
                            (def-body fn w)))
             (formals (access def-body def-body :formals))
             (body (if (flambdap fn)
                       (lambda-body fn)
                     (and def-body
                          (latest-body (fcons-term fn formals)
                                       (access def-body def-body
                                               :hyp)
                                       (access def-body def-body
                                               :concl))))))
        (if (null body)
            (prog2$ (if (flambdap fn)
                        (er hard 'acl2-pc::expand
                            "Found null body for lambda in term ~x0~|Please ~
                             contact the ACL2 implementors."
                            term)
                      t)
                    (print-no-change2
                     "Expansion failed.  Apparently function ~x0 is ~
                      constrained, not defined."
                     (list (cons #\0 fn))))
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
                        state)))))))))

(define-pc-atomic-macro x-dumb ()

  "expand function call at the current subterm, without simplifying~/
  ~bv[]
  General Form:
  x-dumb:  expand without simplification.
  ~ev[]~/
  Same as ~c[(expand t new-goals-flg keep-all-guards-flg)].  See
  documentation for ~c[expand].

  See also ~c[x], which allows simplification."

  (value `(expand t)))

;; **** consider unwinding the effect if there is no change
(define-pc-macro bookmark (tag &rest instr-list)

  "insert matching ``bookends'' comments~/
  ~bv[]
  Example:
  (bookmark final-goal)~/

  General Form:
  (bookmark name &rest instruction-list)
  ~ev[]
  Run the instructions in ~c[instruction-list] (as though this were a
  call of ~c[do-all]; see the documentation for ~c[do-all]), but first insert
  a begin bookend with the given name and then, when the instructions
  have been completed, insert an end bookend with that same name.  See
  the documentation of ~c[comm] for an explanation of bookends and how
  they can affect the display of instructions."

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

  "save the proof-checker state (state-stack)~/
  ~bv[]
  Example:
  (save lemma3-attempt)~/

  General Form:
  (save &optional name do-it-flg)
  ~ev[]
  Saves the current proof-checker state by ``associating'' it with
  the given name.  Submit ~c[(retrieve name)] to Lisp to get back to this
  proof-checker state.  If ~c[verify] was originally supplied with an
  event name, then the argument can be omitted in favor of that name
  as the default.

  ~st[Remark] that if a ~c[save] has already been done with the indicated name
  (or the default event name), then the user will be queried regarding
  whether to go ahead with the save ~-[] except, if ~c[do-it-flg] is
  supplied and not ~c[nil], then there will be no query and the ~c[save] will
  be effected.

  See also the documentation for ~c[retrieve] and ~c[unsave]."

  (let ((name (or name (car (event-name-and-types-and-raw-term state-stack))))
        (ss-alist (ss-alist)))
    (if name
        (mv-let (erp reply state)
                (if (and (assoc-eq name ss-alist)
                         (null do-it-flg))
                    (acl2-query 'acl2-pc::save
                                '("The name ~x0 is already associated with a state-stack.  Do ~
                                    you really want to overwrite that existing value?"
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
      (pprogn (print-no-change "You can't SAVE with no argument, because you didn't ~
                                originally enter VERIFY using an event name.  Try ~
                                (SAVE <event_name>) instead.")
              (value :fail)))))

(defmacro retrieve (&optional name)

  ":Doc-Section Proof-checker

  re-enter a (specified) ~il[proof-checker] state~/
  ~bv[]
  Examples:
  (retrieve associativity-of-permutationp)
  retrieve~/

  General Form:
  (retrieve &optional name)
  ~ev[]
  ~l[acl2-pc::retrieve], or use ~c[(help retrieve)] inside the
  interactive ~il[proof-checker] loop.  Also ~pl[unsave]."

  `(retrieve-fn ',name state))

(define-pc-macro retrieve ()

  "re-enter the proof-checker~/
  ~bv[]
  Examples:
  (retrieve associativity-of-permutationp)
  retrieve~/

  General Form:
  (retrieve &optional name)
  ~ev[]
  Must be used from ~c[outside] the interactive proof-checker loop.  If
  name is supplied and not ~c[nil], this causes re-entry to the
  interactive proof-checker loop in the state at which ~c[save] was last
  executed for the indicated name.  (See documentation for ~c[save].)  If
  ~c[name] is ~c[nil] or is not supplied, then the user is queried regarding
  which proof-checker state to re-enter.  The query is omitted,
  however, if there only one proof-checker state is present that was
  saved with ~c[save], in which case that is the one that is used.  See
  also ~c[unsave]."

  (pprogn (print-no-change "RETRIEVE can only be used ouside the ~
                            interactive loop.  Please exit first.  To ~
                            save your state upon exit, use EX rather than EXIT.")
          (value :fail)))

(defun unsave-fn (name state)
  (pc-assign ss-alist
             (delete-assoc-eq name (ss-alist))))

(defmacro unsave (name)
  ":Doc-Section Proof-checker

  remove a ~il[proof-checker] state~/
  ~bv[]
  Example:
  (unsave assoc-of-append)~/

  General Form:
  (unsave name)
  ~ev[]
  Eliminates the association of a ~il[proof-checker] state with ~c[name].
  ~l[unsave] or ~pl[acl2-pc::unsave].

  Also ~pl[acl2-pc::save] and ~pl[retrieve]."

  `(unsave-fn ',name state))

(define-pc-help unsave (&optional name)

  "remove a proof-checker state~/
  ~bv[]
  Example:
  (unsave assoc-of-append)~/

  General Form:
  (unsave &optional name)
  ~ev[]
  Eliminates the association of a proof-checker state with ~c[name], if
  ~c[name] is supplied and not ~c[nil].  The name may be ~c[nil] or not supplied,
  in which case it defaults to the event name supplied with the
  original call to ~c[verify] (if there is one ~-[] otherwise, the
  instruction ``fails'' and there is no change).  The ACL2 function
  ~c[unsave] may also be executed outside the interactive loop, with the
  same syntax.

  See also documentation for ~c[save] and ~c[retrieve]."

  (let ((name (or name (car (event-name-and-types-and-raw-term state-stack)))))
    (if (null name)
        (print-no-change "You must specify a name to UNSAVE, because you didn't ~
                          originally enter VERIFY using an event name.")
      (if (assoc-eq name (ss-alist))
          (pprogn (unsave-fn name state)
                  (io? proof-checker nil state
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
      (er soft 'verify
          "You are apparently already inside the VERIFY interactive loop.  It is ~
           illegal to enter such a loop recursively."))
     ((null ss-alist)
      (pprogn (io? proof-checker nil state
                   nil
                   (fms0 "Sorry -- there is no saved interactive proof to ~
                          re-enter! Perhaps you meant (VERIFY) rather than ~
                          (RETRIEVE).~|"))
              (value :invisible)))
     ((null name)
      (if (equal (length ss-alist) 1)
          (retrieve-fn (caar ss-alist) state)
        (pprogn (io? proof-checker nil state
                     (ss-alist)
                     (fms0 "Please specify an interactive verification to ~
                            re-enter.  Your options are ~&0.~%(Pick one of the ~
                            above:) "
                           (list (cons #\0 (strip-cars ss-alist)))))
                (mv-let (erp val state)
                        (state-global-let*
                         ((infixp nil))
                         (read-object *standard-oi* state))
                        (declare (ignore erp))
                        (retrieve-fn val state)))))
     (t
      (let* ((ss-pair (cdr (assoc-eq name ss-alist)))
             (saved-ss (car ss-pair))
             (saved-old-ss (cdr ss-pair)))
        (if saved-ss
            (pprogn (pc-assign old-ss saved-old-ss)
                    (pc-assign state-stack saved-ss)
                    (show-retrieved-goal saved-ss state)
                    (verify))
          (pprogn (io? proof-checker nil state
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

  "print all the (as yet unproved) goals~/

  Example and General Form:
  print-all-goals~/

  Prints all the goals that remain to be proved, in a pleasant
  format.  See also the proof-checker command ~c[print-all-concs]."

  (print-all-goals (goals t) state))

(defmacro print-conc (&optional acl2::goal)
  `(let ((goal ,(or goal '(car (access pc-state (car (state-stack)) :goals)))))
     (io? proof-checker nil state
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

  "print all the conclusions of (as yet unproved) goals~/

  Example and General Form:
  print-all-concs~/

  Prints all the conclusions of goals that remain to be proved, in a
  pleasant format.  See also the proof-checker command
  ~c[print-all-goals]."

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
            the proof-checker state, and hence is not legal as a ~
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

  "perform a generalization~/
  ~bv[]
  Example:
  (generalize 
   ((and (true-listp x) (true-listp y)) 0)
   ((append x y) w))~/

  General Form:
  (generalize &rest substitution)
  ~ev[]
  Generalize using the indicated substitution, which should be a
  non-empty list.  Each element of that list should be a two-element
  list of the form ~c[(term variable)], where ~c[term] may use abbreviations.
  The effect of the instruction is to replace each such term in the
  current goal by the corresponding variable.  This replacement is
  carried out by a parallel substitution, outside-in in each
  hypothesis and in the conclusion.  More generally, actually, the
  ``variable'' (second) component of each pair may be ~c[nil] or a number,
  which causes the system to generate a new name of the form ~c[_] or ~c[_n],
  with ~c[n] a natural number; more on this below.  However, when a
  variable is supplied, it must not occur in any goal of the current
  proof-checker state.

  When the ``variable'' above is ~c[nil], the system will treat it as the
  variable ~c[|_|] if that variable does not occur in any goal of the
  current proof-checker state.  Otherwise it treats it as ~c[|_0|], or
  ~c[|_1|], or ~c[|_2|], and so on, until one of these is not among the
  variables of the current proof-checker state.  If the ``variable''
  is a non-negative integer ~c[n], then the system treats it as ~c[|_n|]
  unless that variable already occurs among the current goals, in
  which case it increments n just as above until it obtains a new
  variable.

  ~st[Remark:]  The same variable may not occur as the variable component of
  two different arguments (though ~c[nil] may occur arbitrarily many
  times, as may a positive integer)."

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

  "use a lemma instance~/
  ~bv[]
  Example:
  (USE true-listp-append
       (:instance assoc-of-append (x a) (y b) (z c)))
  -- Add two top-level hypotheses, one the lemma called
     true-listp-append, and the other an instance of the lemma called
     assoc-of-append by the substitution in which x is assigned a, y
     is assigned b, and z is assigned c.~/

  General Form:
  (use &rest args)
  ~ev[]
  Add the given lemma instances to the list of top-level hypotheses.
  ~l[hints] for the syntax of ~c[:use] hints in ~c[defthm], which is
  essentially the same as the syntax here (see the example above).

  This command calls the ~c[prove] command, and hence should only be used
  at the top of the conclusion."

  (value `(prove :hints
                 (("Goal" :use ,args
                   :do-not-induct proof-checker
                   :do-not *do-not-processes*))
                 :otf-flg t)))

(define-pc-atomic-macro clause-processor (&rest cl-proc-hints)

  "use a clause-processor~/
  ~bv[]
  Example:
  (cl-proc :function
           note-fact-clause-processor
          :hint
          '(equal a a))
  -- Invoke the indicated clause processor function with the indicated hint
  argument (see the beginning of file
  ~c[books/clause-processors/basic-examples.lisp].~/

  General Form:
  (cl-proc &rest cl-proc-args)
  ~ev[]
  Invoke a clause-processor as indicated by cl-proc-args, which is a list of
  arguments that can serve as the value of a ~c[:]~ilc[clause-processor] hint;
  ~pl[hints].

  This command calls the ~c[prove] command, and hence should only be used
  at the top of the conclusion."

  (value `(:prove :hints
                  (("Goal"
                    :clause-processor (,@cl-proc-hints)
                    :do-not-induct proof-checker
                    :do-not *do-not-processes*))
                  :otf-flg t)))

(define-pc-macro cl-proc (&rest cl-proc-hints)

  "same as ~c[clause-processor]~/

  See the documentation for ~ilc[proof-checker] command ~c[clause-processor],
  which is identical to ~c[cl-proc].~/~/"

  (value `(:clause-processor ,@cl-proc-hints)))

(defun fromto (i j)
  (declare (xargs :guard (and (rationalp i) (rationalp j))))
  (if (< j i)
      nil
    (cons i (fromto (1+ i) j))))

(define-pc-atomic-macro retain (arg1 &rest rest-args)

  "drop all ~st[but] the indicated top-level hypotheses~/
  ~bv[]
  Example:
  (RETAIN 2 3) -- keep the second and third hypotheses, and drop
                  the rest~/

  General Form:
  (retain &rest args)
  ~ev[]
  Drop all top-level hypotheses ~st[except] those with the indicated
  indices.

  There must be at least one argument, and all must be in range (i.e.
  integers between one and the number of top-level hypotheses,
  inclusive)."

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

  "call the ACL2 theorem prover's simplifier~/
  ~bv[]
  Examples:
  reduce -- attempt to prove the current goal without using induction
  (reduce (\"Subgoal 2\" :by foo) (\"Subgoal 1\" :use bar))
         -- attempt to prove the current goal without using
            induction, with the indicated hints~/

  General Form:
  (reduce &rest hints)
  ~ev[]
  Attempt to prove the current goal without using induction, using the
  indicated hints (if any).  A subgoal will be created for each goal
  that would have been pushed for proof by induction in an ordinary
  proof.

  Notice that unlike ~c[prove], the arguments to ~c[reduce] are spread out,
  and are all hints.

  ~c[Reduce] is similar to ~c[bash] in that neither of these allows induction.
  But ~c[bash] only allows simplification, while ~c[reduce] allows processes
  ~c[eliminate-destructors], ~c[fertilize], ~c[generalize], and
  ~c[eliminate-irrelevance].

  ~st[Remark:]  Induction will be used to the extent that it is ordered
  explicitly in the hints."

  (if (alistp hints)
      (value (list :prove :hints
                   (add-string-val-pair-to-string-val-alist
                    "Goal"
                    :do-not-induct
                    'proof-checker
                    hints)
                   :otf-flg t))
    (pprogn (print-no-change
             "A REDUCE instruction must be of the form~%~ ~ ~
              (:REDUCE (goal_name_1 ...) ... (goal_name_n ...)),~%and hence ~
              your instruction,~%~ ~ ~x0,~%is not legal."
             (list (cons #\0 (cons :reduce hints))))
            (value :fail))))

(define-pc-macro run-instr-on-goal (instr goal-name)

  "auxiliary to THEN~/

  See documentation for ~c[then].~/ "

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

  "auxiliary to ~c[then]~/

  See documentation for ~c[then].~/ "

  (value (cons 'do-strict
               (run-instr-on-goals-guts
                (if must-succeed-flg instr (list :succeed instr))
                (set-difference-equal (goal-names (goals t))
                                      existing-goal-names)))))

(define-pc-macro then (instr &optional completion must-succeed-flg)

  "apply one instruction to current goal and another to new subgoals~/
  ~bv[]
  Example:
  (then induct prove)~/

  General Form:
  (then first-instruction &optional completion must-succeed-flg)
  ~ev[]
  Run ~c[first-instruction], and then run ~c[completion] (another
  instruction) on each subgoal created by ~c[first-instruction].  If
  ~c[must-succeed-flg] is supplied and not ~c[nil], then halt at the first
  ``failure'' and remove the effects of the invocation of ~c[completion] that
  ``failed''.

  The default for completion is ~c[reduce]."

  (value (list 'do-strict
               instr
               (list 'run-instr-on-new-goals
                     (or completion :reduce)
                     (goal-names (goals t))
                     must-succeed-flg))))

(defun print-help-separator (state)
  (io? proof-checker nil state
       nil
       (fms0 "~%==============================~%")))

(defun print-pc-help-rec (lst state)
  (declare (xargs :guard (true-listp lst)))
  (if (null lst)
      (value t)
    (mv-let
     (erp val state)
     (doc!-fn (car lst) state)
     (declare (ignore erp val))
     (pprogn
      (print-help-separator state)
      (print-pc-help-rec (cdr lst) state)))))

(defun print-all-pc-help-fn (filename state)
  (mv-let (chan state)
          (open-output-channel filename :character state)
          (state-global-let*
           ((proofs-co chan)
            (standard-co chan))
           (pprogn (io? proof-checker nil state
                        nil
                        (fms0 "~|***** Complete documentation of proof-checker ~
                               commands *****~%"))
                   (print-help-separator state)
                   (print-pc-help-rec
                    (merge-sort-alpha-< (caddr (access-doc-string-data-base
                                                'pc-acl2 state)))
                    state)))))

(defmacro print-all-pc-help (&optional filename)
  `(print-all-pc-help-fn ,(or filename "pc-help.out") state))

(define-pc-macro nil ()

  "used for interpreting ~c[control-d]~/

  ~bv[]
  Example and General form:
  nil
  ~ev[]
  (or, ~c[control-d]).~/

  The whole point of this command is that in some Lisps (including
  akcl), if you type ~c[control-d] then it seems, on occasion, to get
  interpreted as ~c[nil].  Without this command, one seems to get into an
  infinite loop."

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

  "create a ``free variable''~/
  ~bv[]
  Example:
  (free x)~/

  General Form:
  (free var)
  ~ev[]
  Mark ~c[var] as a ``free variable''.  Free variables are only of
  interest for the ~c[put] command; see its documentation for an
  explanation."

  (er-let* ((var (trans0 var nil :free)))
           (if (variablep var)
               (value `(add-abbreviation ,var (hide ,var)))
             (pprogn (print-no-change
                      "The FREE command requires an argument that is a variable, ~
                       which ~x0 is not."
                      (list (cons #\0 var)))
                     (value :fail)))))

(define-pc-macro replay (&optional n replacement-instr)

  "replay one or more instructions~/
  ~bv[]
  Examples:
  REPLAY     -- replay all instructions in the current session
                (i.e., state-stack)
  (REPLAY 5) -- replay the most recent 5 instructions
  (REPLAY 5
          (COMMENT deleted dive command here))
             -- replace the 5th most recent instruction with the
                indicated comment instruction, and then replay it
                followed by the remaining 4 instructions~/

  General Form:
  (REPLAY &OPTIONAL n replacement-instruction)
  ~ev[]
  Replay the last ~c[n] instructions if ~c[n] is a positive integer; else ~c[n]
  should be ~c[nil] or not supplied, and replay all instructions.
  However, if ~c[replacement-instruction] is supplied and not ~c[nil], then
  before the replay, replace the ~c[nth] instruction (from the most
  recent, as shown by ~c[commands]) with ~c[replacement-instruction].

  If this command ``fails'', then the ~c[restore] command will revert the
  state-stack to its value present before the ~c[replay] instruction was
  executed."

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

  "substitute for a ``free variable''~/
  ~bv[]
  Example:
  (put x 17)~/

  General Form:
  (put var expr)
  ~ev[]
  Substitute ~c[expr] for the ``free variable'' ~c[var], as explained below.

  A ``free variable'' is, for our purposes, a variable ~c[var] such that
  the instruction ~c[(free var)] has been executed earlier in the
  state-stack.  What ~c[(free var)] really does is to let ~c[var] be an
  abbreviation for the term ~c[(hide var)] (see documentation for
  ~c[add-abbreviation]).  What ~c[(put var expr)] really does is to unwind the
  state-stack, replacing that ~c[free] instruction with the instruction
  ~c[(add-abbreviation var expr)], so that future references to ~c[(? var)]
  become reference to ~c[expr] rather than to ~c[(hide var)], and then to
  replay all the other instructions that were unwound.  Because ~c[hide]
  was used, the expectation is that in most cases, the instructions
  will replay successfully and ~c[put] will ``succeed''.  However, if any
  replayed instruction ``fails'', then the entire replay will abort
  and ``fail'', and the state-stack will revert to its value before
  the ~c[put] instruction was executed.

  If ~c[(put var expr)] ``succeeds'', then ~c[(remove-abbreviation var)] will
  be executed at the end.

  ~st[Remark]:  The ~c[restore] command will revert the state-stack to its
  value present before the ~c[put] instruction was executed."

  (let ((n (find-possible-put var state-stack)))
    (if n
        (value `(do-strict (replay ,n
                                   (add-abbreviation ,var ,expr))
                           (remove-abbreviations ,var)))
      (pprogn (print-no-change "There is no FREE command for ~x0."
                               (list (cons #\0 var)))
              (value :fail)))))

(define-pc-macro reduce-by-induction (&rest hints) 

  "call the ACL2 prover without induction, after going into
  induction~/
  ~bv[]
  Examples:
  reduce-by-induction
    -- attempt to prove the current goal after going into induction,
       with no further inductions

  (reduce-by-induction (\"Subgoal 2\" :by foo) (\"Subgoal 1\" :use bar))
    -- attempt to prove the current goal after going into induction,
       with no further inductions, using the indicated hints~/

  General Form:
  (reduce-by-induction &rest hints)
  ~ev[]
  A subgoal will be created for each goal that would have been
  pushed for proof by induction in an ordinary proof, except that the
  proof begins with a top-level induction.

  Notice that unlike ~c[prove], the arguments to ~c[reduce-by-induction] are
  spread out, and are all hints.  See also ~c[prove], ~c[reduce], and ~c[bash].

  ~st[Remark]:  Induction and the various processes will be used to the
  extent that they are ordered explicitly in the ~c[:induct] and ~c[:do-not]
  hints."

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

(define-pc-macro sr (&rest args)

  "same as SHOW-REWRITES~/
  ~bv[]
  Example:
  sr~/

  General Form:
  (sr &optional rule-id)
  ~ev[]
  See the documentation for ~c[show-rewrites], as ~c[sr] and ~c[show-rewrites]
  are identical."

  (value (cons :show-rewrites args)))

(define-pc-macro r (&rest args)

  "same as rewrite~/
  ~bv[]
  Example:
  (r 3)~/

  ~ev[]
  See the documentation for ~c[rewrite], as ~c[r] and ~c[rewrite] are identical."

  (value (cons :rewrite args)))

(define-pc-atomic-macro sl (&optional backchain-limit)

  "simplify with lemmas~/
  ~bv[]
  Examples:
  sl
  (sl 3)~/

  General Form:
  (sl &optional backchain-limit)
  ~ev[]
  Simplify, but with all function definitions disabled
  (~pl[function-theory] in the top-level ACL2 loop), except for a
  few basic functions (the ones in ~c[(theory 'minimal-theory)]).  The
  ~c[backchain-limit] has a default of 0, but if is supplied and
  not ~c[nil], then it should be a nonnegative integer; see the
  documentation for ~c[s].

  WARNING: This command completely ignores ~c[in-theory] commands that are
  executed inside the proof-checker."

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

  "call the ACL2 theorem prover's elimination process~/
  ~bv[]
  Example and General Form:
  elim
  ~ev[]~/

  Upon running the ~c[elim] command, the system will create a subgoal will
  be created for each goal that would have been pushed for proof by
  induction in an ordinary proof, where ~st[only] elimination is used; not
  even simplification is used!"

  (value (list :prove :otf-flg t
               :hints
               '(("Goal" :do-not-induct proof-checker
                  :do-not (set-difference-eq *do-not-processes*
                                             '(eliminate-destructors)))))))

(define-pc-macro ex ()

  "exit after possibly saving the state~/
  ~bv[]
  Example and General Form:
  ex
  ~ev[]~/

  Same as ~c[exit], except that first the instruction ~c[save] is executed.

  If ~c[save] queries the user and is answered negatively, then the exit
  is aborted."

  (value '(do-strict save exit)))

(define-pc-help type-alist (&optional concl-flg govs-flg)

  "display the type-alist from the current context~/
  ~bv[]
  Examples:
  (type-alist t t) ; display type-alist based on both conclusion and governors
  type-alist       ; same as (type-alist nil t) -- governors only
  (type-alist nil) ; same as (type-alist nil t) -- governors only
  (type-alist t)   ; same as (type-alist t nil) -- conclusion only
  (type-alist nil nil) ; display type-alist without considering
                       ; conclusion or governors~/

  General Form:
  (type-alist &optional concl-flg govs-flg)
  ~ev[]
  where if ~c[govs-flg] is omitted, it defaults to ~c[(not concl-flg)].

  Display the current assumptions as a type-alist.  Note that this
  display includes the result of forward chaining.

  There are two basic reasons contemplated for using this command.

  1. The theorem prover has failed (either outside the proof-checker or using a
  proof-checker command such as ~c[bash] or ~c[reduce] and you want to
  debug by getting an idea of what the prover knows about the context.~bq[]

  a. You really are interested in the context for the current term.  Include
  hypotheses and governors (i.e., accounting for tests of surrounding
  ~c[if]-expressions that must be true or false) but not the current conclusion
  (which the theorem prover's heuristics would generally ignore for contextual
  information).  Command:~nl[]
  ~c[(type-alist nil t)] ; equivalently, ~c[type-alist] or ~c[(type-alist nil)]

  b. You are not thinking in particular about the current term; you just want
  to get an idea of the context that the prover would build at the top-level,
  for forward-chaining.  Incorporate the conclusion but not the governors.
  Command:~nl[]
  ~c[(type-alist t nil)] ; equivalently, ~c[(type-alist t)]~eq[]

  2. You intend to use one of the ~il[proof-checker-commands] that does
  simplification, such as ~c[s] or ~c[x], and you want to see the context.
  Then include the surrounding ~c[if]-term governors but not the goal's
  conclusion.  Command:~nl[]
  ~c[(type-alist nil t)] ; equivalently, ~c[type-alist] or ~c[(type-alist nil)]

  ~l[type-set] (also ~pl[type-prescription]) for information about
  ACL2's type system, which can assist in understanding the output of the
  ~c[type-alist] command."

  (when-goals
   (let ((conc (conc t))
         (current-addr (current-addr t))
         (w (w state))
         (govs-flg (if (cdr args) govs-flg (not concl-flg))))
     (mv-let (flg hyps-type-alist ttree)
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
       (if flg
           (io? proof-checker nil state
                nil
                (fms0 "*** Contradiction in the hypotheses! ***~%The S command ~
                  should complete this goal.~|"))
         (io? proof-checker nil state
              (hyps-type-alist w)
              (pprogn
               (fms0 "~|Current type-alist, including forward chaining:~%")
               (prog2$ (print-type-alist hyps-type-alist w)
                       state))))))))

(define-pc-help print-main ()

  "print the original goal~/
  ~bv[]
  Example and General Form:
  print-main
  ~ev[]~/

  Print the goal as originally entered."

  (print-pc-goal (car (access pc-state (car (last state-stack)) :goals))))

(define-pc-macro pso ()

  "print the most recent proof attempt from inside the proof-checker~/
  ~bv[]
  Example and General Form:
  pso
  ~ev[]~/

  Print the most recent proof attempt from inside the proof-checker assuming
  you are in ~ilc[gag-mode] or have saved output (~pl[set-saved-output]).  This
  includes all calls to the prover, including for example ~il[proof-checker]
  commands ~c[induct], ~c[split], and ~c[bash], in addition to ~c[prove].  So
  for example, you can follow ~c[(quiet prove)] with ~c[pso] to see the proof,
  including ~il[proof-tree] output, if it failed.

  See also documentation for related ~il[proof-checker] commands ~c[psog] and
  ~c[pso!]."

  (value '(lisp (pso))))

(define-pc-macro psog ()

  "print the most recent proof attempt from inside the proof-checker~/
  ~bv[]
  Example and General Form:
  psog
  ~ev[]~/

  Print the most recent proof attempt from inside the proof-checker, including
  goal names, assuming you are in ~ilc[gag-mode] or have saved output
  (~pl[set-saved-output]).  This includes all calls to the prover, including
  for example ~il[proof-checker] commands ~c[induct], ~c[split], and ~c[bash],
  in addition to ~c[prove].  So for example, you can follow ~c[(quiet prove)]
  with ~c[psog] to see the proof, including ~il[proof-tree] output, if it
  failed.

  See also documentation for related ~il[proof-checker] commands ~c[pso] and
  ~c[pso!]."

  (value '(lisp (psog))))

(define-pc-macro pso! ()

  "print the most recent proof attempt from inside the proof-checker~/
  ~bv[]
  Example and General Form:
  pso!
  ~ev[]~/

  Print the most recent proof attempt from inside the proof-checker, including
  ~il[proof-tree] output, assuming you are in ~ilc[gag-mode] or have saved output
  (~pl[set-saved-output]).  This includes all calls to the prover, including
  for example ~il[proof-checker] commands ~c[induct], ~c[split], and ~c[bash],
  in addition to ~c[prove].  So for example, you can follow ~c[(quiet prove)]
  with ~c[pso!] to see the proof, including ~il[proof-tree] output, if it
  failed.

  See also documentation for related ~il[proof-checker] commands ~c[pso] and
  ~c[psog]."

  (value '(lisp (pso!))))

(define-pc-macro acl2-wrap (x)

  "same as ~c[(lisp x)]~/
  ~bv[]
  Example:
  (acl2-wrap (pe :here))~/

  General Form:
  (acl2-wrap form)
  ~ev[]
  Same as ~c[(lisp form)].  This is provided for interface tools that
  want to be able to execute the same form in raw Lisp, in the
  proof-checker, or in the ACL2 top-level loop ~c[(lp)]."

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

  "forward chain from an implication in the hyps~/
  ~bv[]
  Example:
  (forwardchain 2) ; Second hypothesis should be of the form
                   ; (IMPLIES hyp concl), and the result is to replace
                   ; that hypothesis with concl.
  ~/
  General Forms:
  (forwardchain hypothesis-number)
  (forwardchain hypothesis-number hints)
  (forwardchain hypothesis-number hints quiet-flg)
  ~ev[]

  This command replaces the hypothesis corresponding to given index,
  which should be of the form ~c[(IMPLIES hyp concl)], with its
  consequent ~c[concl].  In fact, the given hypothesis is dropped, and
  the replacement hypothesis will appear as the final hypothesis after
  this command is executed.

  The prover must be able to prove the indicated hypothesis from the
  other hypotheses, or else the command will fail.  The ~c[:hints]
  argument is used in this prover call, and should have the usual
  syntax of hints to the prover.

  Output is suppressed if ~c[quiet-flg] is supplied and not ~c[nil]."

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

  "prove the current goal using bdds~/
  ~bv[]
  Examples:
  bdd
  (bdd :vars nil :bdd-constructors (cons) :prove t :literal :all)
  ~ev[]
  ~/
  The general form is as shown in the latter example above, but with
  any keyword-value pairs omitted and with values as described for the
  ~c[:]~ilc[bdd] hint; ~pl[hints].

  This command simply calls the theorem prover with the indicated bdd
  hint for the top-level goal.  Note that if ~c[:prove] is ~c[t] (the
  default), then the proof will succeed entirely using bdds or else
  it will fail immediately.  ~l[bdd]."

  (let ((bdd-hint (if (assoc-keyword :vars kw-listp)
                      kw-listp
                    (list* :vars nil kw-listp))))
    (value `(:prove :hints
                    (("Goal" :bdd ,bdd-hint))))))

(define-pc-macro runes (&optional flg)

  "print the runes (definitions, lemmas, ...) used~/
  ~bv[]
  Examples and general forms:
  (runes t)   ; print all ~il[rune]s used during this interactive proof
  (runes nil) ; print all ~il[rune]s used by the most recent command
  (runes)     ; same as (runes nil)
  runes       ; same as (runes nil)
  ~ev[]~/
  This command does not change the ~il[proof-checker] state.  Rather, it
  simply reports runes (~pl[rune]) that have participated in the interactive
  proof.

  Note that ~c[(runes nil)] will show the ~il[rune]s used by the most recent
  primitive or macro command (as displayed by ~c[:comm])."

  (value `(print (merge-sort-runes
                  (all-runes-in-ttree (,(if flg 'tag-tree 'local-tag-tree))
                                      nil)))))

(define-pc-macro lemmas-used (&optional flg)

  "print the runes (definitions, lemmas, ...) used~/

  This is just an alias for ~c[runes].~/~/"

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

  "combine goals into a single goal~/

  ~bv[]
  Examples:
  ; Keep (main . 1) and (main . 2) if they exist, as well as the current goal;
  ; and for each other goal, conjoin it into the current goal and delete it:
  (wrap1 ((main . 1) (main . 2)))

  ; As explained below, conjoin all subsequent siblings of the current goal
  ; into the current goal, and then delete them:
  (wrap1)~/

  General Form:
  (wrap1 &optional kept-goal-names)
  ~ev[]
  If ~c[kept-goal-names] is not ~c[nil], the current goal is replaced by
  conjoining it with all goals other than the current goal and those indicated
  by ~c[kept-goal-names], and those other goals are deleted.  If
  ~c[kept-goal-names] is omitted, then the the current goal must be of the form
  ~c[(name . n)], and the goals to conjoin into the current goal (and delete)
  are those with names of the form ~c[(name . k)] for ~c[k] >= ~c[n].

  NOTE: ~c[Wrap1] always ``succeeds'', even if there are no other goals to
  conjoin into the current goal (a message is printed in that case), and it
  always leaves you with no hypotheses at the top of the current goal's
  conclusion (as though ~c[top] and ~c[demote] had been executed, if
  necessary).

  Also see proof-checker documentation for ~c[wrap]
  (~pl[proof-checker-commands])."

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
         (io? proof-checker nil state
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

  "execute the indicated instructions and combine all the new goals~/
  ~bv[]
  Example:
  (wrap induct) ; induct, then replace first new goal by the conjunction of all
                ; the new goals, and drop all new goals after the first~/

  General Form:
  (wrap &rest instrs)
  ~ev[]
  First the instructions in ~c[instrs] are executed, as in ~c[do-all].  If this
  ``fails'' then no additional action is taken.  Otherwise, the current goal
  after execution of ~c[instrs] is conjoined with all ``new'' goals, in the
  sense that their names are not among the names of goals at the time
  ~c[instrs] was begun.  This conjunction becomes the new current goal and
  those ``new'' goals are dropped.

  See the code for the proof-checker command wrap-induct for an example of the
  use of ~c[wrap]."

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
            (lisp (io? proof-checker nil state
                       (state-stack)
                       (let ((new-current-goal-name
                              (access goal (car (goals)) :goal-name)))
                         (when-goals
                          (fms0 (if (member-equal new-current-goal-name
                                                  ',goal-names)
                                    "~|~%NOTE: Created no new goals.  Current ~
                                    goal:~%  ~X0n~|"
                                  "~|~%NOTE: Created ONLY one new goal, which is ~
                                  the current goal:~%  ~X0n~|")
                                (list (cons #\0 new-current-goal-name)
                                      (cons #\n nil))))))))
           t nil nil t))))))

(define-pc-atomic-macro wrap-induct (&optional raw-term)

  "same as induct, but create a single goal~/
  ~bv[]
  Examples:
  wrap-induct
  (wrap-induct t)
  (wrap-induct (append (reverse x) y))~/

  General Form:
  (wrap-induct &optional term)
  ~ev[]
  The ~c[wrap-induct] command is identical to the ~ilc[proof-checker]
  ~c[induct] command, except that only a single goal is created:  the
  conjunction of the base and induction steps.

  Note:  The output will generally indicate that more than goal has been
  created, e.g.:
  ~bv[]
  Creating two new goals:  (MAIN . 1) and (MAIN . 2).
  ~ev[]
  However, ~c[wrap-induct] always creates a unique goal (when it succeeds).  A
  subsequent message clarifies this, for example:
  ~bv[]
  NOTE: Created ONLY one new goal, which is the current goal:
    (MAIN . 1)
  ~ev[]"

  (value (if raw-term
             `(wrap (induct ,raw-term))
           `(wrap induct))))

(define-pc-macro finish-error (instrs)
  (er soft 'finish
      "~%The following instruction list created at least one subgoal:~|~x0~|"
      instrs))

(define-pc-macro finish (&rest instrs)

  "require completion of instructions; save error if inside ~c[:]~ilc[hints]~/
  ~bv[]
  Example:
  (finish induct prove bash)~/

  General Form:
  (finish &rest instructions)
  ~ev[]
  Run the indicated instructions, stopping at the first failure.  If there is
  any failure, or if any new goals are created and remain at the end of the
  indicated instructions, then consider the call of ~c[finish] to be a
  failure.  ~l[proof-checker-commands] and visit the documentation for
  ~c[sequence] for a discussion of the notion of ``failure'' for proof-checker
  commands."

  (value `(then (check-proved (do-strict ,@instrs))
                (finish-error ,instrs)
                t)))

; Support for :instructions as hints

(defun goals-to-clause-list (goals)
  (if (endp goals)
      nil
    (cons (append (dumb-negate-lit-lst (access goal (car goals) :hyps))
                  (list (access goal (car goals) :conc)))
          (goals-to-clause-list (cdr goals)))))

(defun proof-checker-clause-list (state)
  (goals-to-clause-list (goals)))

(defun proof-checker-cl-proc (cl instr-list state)
  (let ((ctx 'proof-checker-cl-proc))
    (cond
     ((null cl)
      (er soft ctx
          "There is no legal way to prove a goal of NIL!"))
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
                    (t (value (union-eq '(prove proof-tree proof-checker)
                                        (f-get-global 'inhibit-output-lst
                                                      state))))))
                  (outputp (value (not (subsetp-eq
                                        '(prove proof-checker proof-tree)
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
                                            proof-checker instructions]]~%~%"
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
                              t ; print-prompt-and-instr-flg, suitable for :pso
                              state)
                     (pprogn
                      (cond (outputp (io? prove nil state
                                          (new-pc-depth)
                                          (fms0 "~|~%[[<~x0 Completed ~
                                                 proof-checker ~
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
                                     (fms0 "~%Saving proof-checker error ~
                                            state; see :DOC instructions.  To ~
                                            retrieve:~|~x0"
                                           (list (cons #\0 `(retrieve ,name)))))
                                (save-fn name (ss-alist) state)
                                (er soft ctx
                                    "The above :INSTRUCTIONS hint failed.  ~
                                     For a discussion of ``failed'', follow ~
                                     the link to the SEQUENCE command under ~
                                     :DOC proof-checker-commands."))))
                            (t (value (proof-checker-clause-list
                                       state)))))))
            (cond (erp (silent-error state))
                  (t (value clause-list)))))))))))

#+acl2-loop-only
(define-trusted-clause-processor
  proof-checker-cl-proc
  nil)

#+acl2-loop-only
(add-custom-keyword-hint :instructions
                         (splice-keyword-alist
                          :instructions
                          (list :clause-processor
                                (list :function
                                      'proof-checker-cl-proc
                                      :hint
                                      (kwote val)))
                          keyword-alist))
