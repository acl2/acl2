(in-package "PACO")

; I chose to code Paco without considering how it would track and
; report which rules it was using.  That decision allows the term
; manipulation functionality to be the primary consideration in the
; code.  As for how Paco would report what it was doing, my vision has
; always been to superimpose some kind of dependency-tracking ``after
; the fact,'' ideally with a meta-facility like tracing or compiling
; that secretly changes behavior without changing functionality.

; This is a first cut at such a module for Paco.  It is not quite
; post-facto, as this is an early file in the source sequence.  But I
; have managed to hide virtually all of Paco's dependency tracking and
; output features here.

; In this file I define fourteen macros, each with a name starting with
; "<" and ending with ">", e.g., <rewrite-id>.  Each macro is an
; an ``identity macro'' in the sense that (<rewrite-id> term) is equal
; to term.  These macros expand in such a way as to evaluate term -- which
; is often an expression returning a multiple value -- and keep track of
; which rules it is using.  To do this, the rules are squirrelled away in
; a wormhole.

; On a first reading of the Paco sources, I strongly recommend not to
; read any further through this file!  Just understand that
; (<rewrite-id> term) is the same as term when you read the rest of
; the sources.  Then, when you understand how Paco works, you might
; want to revisit this file and see how I make that happen.

; The rest of this rather long comment attempts to explain WHY I do
; dependency tracking this way and then HOW it actually works.  But you
; do not need to know this on an initial study of Paco.

; But I would like to obtain a rudimentary rule tracking/reporting
; mechanism via a ``meta'' facility akin to tracing.  Consider the
; factorial function.  We define it without regard for any kind of
; tracking/recording of the intermediate results.  (Fact 3) returns 6
; and we do not know ``how'' it computed 6.  But we can install a
; trace on fact -- after the fact, so to speak -- and then see that
; (fact 3) gave rise to (fact 2) which computed 2, etc.

; My vision -- not yet fully realized and arguably impossible in light
; of the full exploration of this note -- is that I can define the
; Paco rewriter or type-set mechanism or prover and get it to do the
; necessary term manipulation to make it a ``theorem prover'' and
; then, after the fact, install some kind of ``rule trace'' that
; allows me to see what rules it is using.

; My attempt to understand this took the form of two earlier files, called
; io-hack1 and io-hack2, in which I doctored the pristine Paco sources with
; tracking code written in raw Lisp and sprinkled around the Paco code
; where ever necessary.  I just grabbed any Paco code I wanted to modify,
; copied it into io-hack1, modified it with raw Lisp, and loaded the io-hack
; into raw Lisp after Paco had been loaded, thus redefining the ``official''
; Paco code.  Then I studied the raw Lisp to look for patterns
; and abstractions that would make it more regular.  After doing this twice
; (io-hack1 and followed by io-hack2) I realized I could do it using wormholes
; and macros without actually redefining the Paco code -- if I defined the
; macros first.  The macros admittedly anticipate the term manipulation code
; I will write, right down to the variable names my code will use!  So it is
; not very automated.  But at least I've partitioned the entire dependency
; tracking code into this one place.

; Now, let me illustrate the basic problem and discuss some possible
; approaches.  The following is a pretty standard Paco idiom for using
; a rule: check if it is enabled, apply the rule to obtain some new
; term, test some heuristic condition, and return either the new term
; or the original one.

; (cond ((enabled-numep (access rule x :nume) ens)    ;;; [1]
;        (let ((new-term (apply-rule x term)))
;          (cond ((heuristicp new-term term)
;                 new-term)
;                (t term))))
;       (t term))

; The Nqthm approach Boyer and I adopted was analogous to the
; following.  We had a secret stack, here called the ``nume stack'',
; composed of frames.  Each frame contains the numes that have been
; used so far on behalf of the current subgoal.  The basic operations
; on the nume stack are to push a new frame, push a nume into the top
; frame, pop and discard a frame (in the event that the work is
; abandoned) or pop and union a frame into the one below it (in the
; event that the work contributes a new term).  The code above can be
; annotated with in raw Lisp using these concepts.  The annotations
; are shown in upper case.

; (cond ((enabled-numep (access rule x :nume) ens)    ;;; [2]
;        (PUSH-NUME-FRAME (ACCESS RULE X :NUME))
;        (let ((new-term (apply-rule x term)))
;          (cond ((heuristicp new-term term)
;                 (POP-NUME-FRAME T)
;                 new-term)
;                (t
;                 (POP-NUME-FRAME NIL)
;                 term))))
;       (t term))

; Upon entering the block of code in which the nume might be used, we
; push a new frame containing the nume.  Upon exiting, we pop the
; frame and either union it into its caller or discard it, depending
; on whether the rule application was successful.

; The ACL2 approach used by Kaufmann and me was to make all term
; manipulation functions return two results: the manipulated term and
; a trace of rules used.  These traces, actually ACL2's ``ttrees'',
; are explicitly passed around and combined or discarded
; appropriately.  Here is the above code fragment in the ACL2 style:

; (cond ((enabled-numep (access rule x :nume) ens)    ;;; [3]
;        (MV-let (new-term numes)
;                (apply-rule x term)
;                (cond ((heuristicp new-term term)
;                       (MV new-term (ADD-TO-SET (ACCESS RULE X :NUME) NUMES)))
;                      (t (MV term NIL)))))
;       (t (MV term NIL)))

; This snippet of code is deceptive because it doesn't really drive
; home the fact that the whole system has to be written to use
; multiple values.  But this is maximally flexible because everything
; is done explicitly.

; In my view, [1] is the clearest from the logical perspective.  It
; just says how we manipulate the term.  What I would like is to
; incant some trace-like magic with reference to [1] and obtain [2] or
; [3].  In principle, it doesn't matter to me which way we go.  But if
; the ``magic'' transforms [1] into the ACL2-style [3], then all
; routines which called the original snippet would have to be
; transformed to handle the multiple values, their callers would have
; to be transformed, etc.  For that reason, I think it is easier to
; shoot for [2], where the tracing does not change the functionality
; of the snippet (as long as one views it without looking at the
; nume-stack).  This can be implemented locally.

; Another question I have considered is what the ``magic'' looks like.
; I see no way, even with the simple idiom [1], to obtain [2] from [1]
; with no additional typing.  That is, (track-rules [1]) cannot be
; implemented because I do not think, in general, we can automatically
; distinguish the exits upon which the rule was used from the exits
; upon which it was not.

; I can imagine implementing the no-op macros WON and LOST so that I
; could rewrite [1] as

; (cond ((enabled-numep (access rule x :nume) ens)    ;;; [1']
;        (let ((new-term (apply-rule x term)))
;          (cond ((heuristicp new-term term)
;                 (WON new-term))
;                (t (LOST term)))))
;       (t term))

; Here the idea is that enabled-numep secretly pushes a nume frame if
; it succeeds.  Thereafter, we are obliged to pop it with either WON
; or LOST which do the obvious secret pops.

; I don't like the asymmetry between implicit pushes and explicit pops.

; But there are more serious problem.  The simple idiom of [1] is too simple.
; It is not uncommon to see
; (and (enabled-numep ...)
;      (some-other-conditionp ...))
; governing the use of the rule.  In this case, if the enabled-numep
; secretly pushes a frame, we have to secretly pop it without ever entering
; the block where the rule is used.

; Another complication is that we sometimes do things like call
; enabled-numep inside a function that ``collects candidates'' but
; doesn't actually use the rules.  We pass the candidates to some
; other function, which weighs their merits and decides which one to
; choose, knowing the corresponding rule is enabled.  This is where
; the ACL2 style [3] shines.  By explicitly collecting the
; dependencies with the candidates, we can pass those dependencies
; back up whenever we select the candidate to use.  Put another way,
; idiom [1] is misleading because it suggests the tracking can be done
; with lexical scope but it is dynamic scope that is important.

; Finally, I believe it is inherently impossible to recognize whether
; a given rule was actually used.  For example, a type-prescription
; rule might fire but actually contribute nothing to the already known
; type-set.  That is, we might know the term is an positive integer
; and the rule might tell us that it is an integer.  Or, the first
; rule might tell us a term is a true-listp and the second rule might
; tell us it is NIL.  Was the first rule used?  The proof would have
; proceeded exactly the same had it been disabled, so evidently not.
; It is certainly the case in ACL2 that we sometimes do not report the
; use of a rule we ``used'' because we realize we could have reached
; the same conclusion without it, e.g., when the final type-set is
; *ts-unknown*.  When looked at this way, the whole issue is so
; ill-specified that it is difficult to pin down even what I mean when
; I say I'm looking for an automatic way to track dependencies.

; To be more specific, what do we want to track in induction?  Recall
; how induction in ACL2 works.  We typically do an induction that is
; suggested by some function symbol appearing in the goal clause.
; That induction is justified by the argument used to admit the
; suggesting function's definition.  Call that function symbol suggfn.
; But recall that we also have induction rules, that cause other,
; arbitrary, function symbols to suggest inductions justified by other
; symbols.  So g might occur in the goal clause and an induction rule,
; rule, might link g to suggfn.  Furthermore, rule might be applicable
; only if we can establish certain hypotheses (with type-set).

; So WHY do we want dependencies?  Is it to allow us to construct or
; describe a formal proof?  Or is it so that we can inform the user of
; every fact in the database that has led us to the proof we allege
; can be constructed?  If we only care about the former, it is
; sufficient to collect only suggfn.  Regardless of how we came to it,
; its suggestion is the induction we did and that induction is
; logically justified by suggfn's admission.  But if we want to inform
; the user of everything in the database that is steering us toward
; this proof, we are obliged not only to report suggfn and rule but
; the rules used to relieve the hypotheses of rule.

; The latter can only be done with the explicit involvement of the
; theorem proving code.  I see no way to recover the heuristic
; information leading to the suggestion of suggfn without modifying
; the basic sources.  Such a modification would consist of collecting
; the dependencies used to reach the suggfn and putting them in the
; induction candidate.  Such dependencies would be collected for all
; the suggested candidates and then when the winning candidate is
; finally chosen, we could extract from it the rules used to lead us
; to it.

; But note the fundamental violation of the tracing premise I'm pursuing,
; i.e., that dependency information can be obtained by some meta-level
; tracking device: I just proposed to collect the dependencies used to
; reach suggfn and PUT THEM INTO A DATA STRUCTURE being manipulated by
; the theorem prover.  This is what ACL2 does and I see no way around
; it!  It's as avoidable as it is only because most of the time ACL2
; does not do too much search.  But here we see the prover collecting
; all possible suggestions, using type-set reasoning to help it, and
; then choosing among them long after any kind of dynamic tracking
; information will have been lost.

; Punchline:  I've reached two conclusions.

; First, Paco will collect only enough information to justify the
; logical soundness of its proof, e.g., suggfn, not rule and its
; type-set supporters.  That is because the code already puts the
; suggesting term into the candidate.  (That is probably unnecessary
; and is a vestige of the ACL2 origins of Paco; but unlike rule and
; the type information, at least we know locally (lexically) what
; suggfn is so it is no big deal.  Tracking the type rules used in an
; arbitrary call of type-set is non-local.)

; Second, we made the right decision in ACL2, to make dependency
; tracking an explicit part of the code.  While the ubiquitous
; presence of ttrees and multiple values is ugly, there are times when
; it is necessary.  If I were to re-do ACL2, I would consider more
; transparent idioms for tracking dependencies (sort of like the
; nearly-transparent idioms ACL2 uses to track ``errors'' with er-let*
; and value).  But I would accept upfront that I dependency tracking
; is part of my responsibility.

;-----------------------------------------------------------------
; Section:  Mapping Numes to Runes

; The map below is an ACL2-style enabled structure and is accessed by
; ACL2's enabled-numep not Paco's.  The map is defined in Paco's
; database.lisp file, where I transfer ACL2 rules to Paco's world.
; Paco rules only contain numes (to minimize the traffic when
; different processors are communicating state) and this code converts
; them to runes.

(defun nume-to-rune (nume map)

  (declare (xargs :mode :program))
; Look up nume in the map and return the corresponding rune.  If nume is
; not a nume, return nil.

  (let ((temp (if (and (integerp nume)
                       (<= 0 nume))
                  (acl2::enabled-numep nume map)
                nil)))
    (if (consp temp) temp nil)))

(defun numes-to-runes (numes map)
  (declare (xargs :mode :program))
  (cond ((endp numes) nil)
        (t (let ((rune (nume-to-rune (car numes) map)))
             (cond (rune (cons rune (numes-to-runes (cdr numes) map)))
                   (t (numes-to-runes (cdr numes) map)))))))

;-----------------------------------------------------------------
; Section:  Turning Clauses into Formulas

; This is a rudimentary ``printer'' for clauses, turning ((not p) (not q) r)
; into the more attractive (implies (and p q) r).

(defun make-not (term)
  (cond ((and (consp term)
              (eq (car term) 'NOT))
         (cadr term))
        (t (list 'NOT term))))

(defun make-not-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (make-not (car lst))
                 (make-not-lst (cdr lst))))))

(defun prettyify-clause (cl)
  (cond ((endp cl) nil)
        ((endp (cdr cl)) (car cl))
        ((endp (cddr cl))
         `(implies ,(make-not (car cl)) ,(cadr cl)))
        (t `(implies (and ,@(make-not-lst (all-but-last cl)))
                     ,(car (last cl))))))

;-----------------------------------------------------------------
; Section:  The Nume Tracker

; This section should be ignored for a long time.  It uses one of the
; most obscure and strange aspects of ACL2, namely wormholes, to
; implement a macro that allows me to track the use of rules without
; cluttering my code.

; I create a wormhole named nume-stack into which I squirrel away
; the nume stack.  I then implement the basic operations on that
; stack, as described above.

; The wormhole status of the nume-stack will be (:ENTER . stack).

(defun reset-nume-stack nil
  (wormhole-eval 'nume-stack
                 '(lambda ()
                    (make-wormhole-status nil :ENTER nil))
                 nil))

(defun push-nume-frame (nume)
  (wormhole-eval 'nume-stack
                 '(lambda (whs)
                    (set-wormhole-data whs
                                       (cons (if nume
                                                 (list nume)
                                                 nil)
                                             (wormhole-data whs))))
                 nil))

(defun push-nume (nume)
  (if nume
      (wormhole-eval 'nume-stack
                     '(lambda (whs)
                        (set-wormhole-data whs
                                           (cons (cons nume (car (wormhole-data whs)))
                                                 (cdr (wormhole-data whs)))))
                     nil)
      nil))

(defun pop-nume-frame-nil ()
  (wormhole-eval 'nume-stack
                 '(lambda (whs)
                    (set-wormhole-data whs
                                       (cdr (wormhole-data whs))))
                 nil))

(defun pop-nume-frame-t ()
  (wormhole-eval 'nume-stack
                 '(lambda (whs)
                    (set-wormhole-data whs
                                       (cons (union-equal (car (wormhole-data whs))
                                                          (cadr (wormhole-data whs)))
                                             (cddr (wormhole-data whs)))))
                 nil))

; And here is the basic macro that annotates a piece of code with
; nume stack handling.  See the example after the macro.

(defmacro with-nume-tracking (vars body nume test)
  (let* ((vars (if (symbolp vars)
                   (list vars)
                 vars))
         (binder
          (cond ((and (consp vars)
                      (endp (cdr vars)))
                 `(let ((,(car vars) ,body))))
                (t `(mv-let ,vars ,body))))
         (ans (cond ((and (consp vars)
                          (endp (cdr vars)))
                     (car vars))
                    (t `(mv ,@vars)))))
    (cond
     ((eq nume :RESET) ; ignore the test
      `(prog2$ (reset-nume-stack) ,body))
     ((eq nume :NO-FRAME) ; push nothing but eval the test
      `(,@binder (prog2$ ,test ,ans)))
     ((eq test t) ; unconditional push nume
      `(prog2$ (push-nume ,nume) ,body))
     (t `(prog2$ (push-nume-frame ,nume)
                 (,@binder
                  (prog2$ (if ,test
                              (pop-nume-frame-t)
                            (pop-nume-frame-nil))
                          ,ans)))))))

; Given all of the foregoing, the form

; (with-nume-tracking (x y z)                      ; vars
;                     <body>                       ; body
;                     (access rule r :nume)        ; nume
;                     (not (equal y *ts-unknown))) ; test


; where <body> is a form that returns 3 values, i.e., (mv x y z), is
; logically equivalent to <body>.

; However, before <body> is evaluated, a new frame is pushed onto a
; secret stack, called the ``nume stack'' and this frame contains the
; nume produced by (access rule r :nume).  Then <body> is evaluated
; and returns (mv x y z).  Then the test, in this case (not (equal y
; *ts-unknown*)), is evaluated and if it is non-nil, the top-most
; frame of the nume stack is popped and unioned into the frame below
; it.  If, on the other hand, the test evaluates to nil, the frame is
; popped and discarded.

; There are a handful of special cases signaled by special values of
; nume and test and implemented above in the defmacro.

; If the nume is :RESET, we reset the nume stack to nil.

; If the nume is :NO-FRAME, we do not push a frame and we do not pop
; one afterwards.

; If the test is t, we do not bother to create a new frame and just
; push the given nume into the current top frame.

; To avoid cluttering the code with such forms, I tend to define
; macros with names like <foo-id> and then write (<foo-id> <body>).
; These expressions are logically equivalent to <body> but track
; the numes as described.

(defmacro <scons-term-id> (body)
  `(with-nume-tracking (hitp val) ,body
                       (fn-nume :executable-counterpart fn wrld)
                       t))

(defmacro <type-set-id> (body)
  `(with-nume-tracking (ans-ts) ,body
                       (access recognizer-tuple recog-tuple :nume)
                       (not (ts= ans-ts *ts-unknown*))))

(defmacro <assume-true-false-id> (body)
  `(with-nume-tracking (mbt mbf tta fta) ,body
                       (access recognizer-tuple recog-tuple :nume)
                       t))

(defmacro <type-set-with-rule-id> (body)
  `(with-nume-tracking (ans-ts ans-type-alist) ,body
                       (access type-prescription tp :nume)
                       (not (ts= ans-ts *ts-unknown*))))

(defmacro <reduce-id> (body)
  `(with-nume-tracking (tuple) ,body
                       :NO-FRAME
                       (and tuple
                            (not (push-nume
                                  (access recognizer-tuple tuple :nume))))))

(defmacro <rewrite-id> (body)
  `(with-nume-tracking (new-term) ,body
                       (fn-nume :executable-counterpart fn wrld)
                       t))

(defmacro <rewrite-with-lemmas1-id> (body)
  `(with-nume-tracking (hitp new-term) ,body
                       (access rewrite-rule (car lemmas) :nume)
                       hitp))


(defmacro <built-in-clausep2-id> (body)
  `(with-nume-tracking (ans) ,body
                       (access built-in-clause (car bic-lst) :nume)
                       t))

(defmacro <convert-type-set-to-term-lst-id> (body)
  `(with-nume-tracking (ans) ,body
                       (access type-set-inverter-rule (car rules) :nume)
                       t))

(defmacro <apply-generalize-rule-id> (body)
  `(with-nume-tracking (flg term) ,body
                       (access generalize-rule gen-rule :nume)
                       t))

(defmacro <apply-instantiated-elim-rule-id> (body)
  `(with-nume-tracking (new-cl elim-vars) ,body
                       (access elim-rule rule :nume)
                       t))

(defmacro <induct-clause-id> (body)
  `(with-nume-tracking (signal clauses hist-obj pspv) ,body
                       (fn-nume :induction
                                (ffn-symb
                                 (access candidate
                                         winning-candidate
                                         :induction-term))
                                wrld)
                       t))

(defun apply-waterfall-process-msg-and-pop-nume-frame-t (acl2::state)
  (declare (xargs :mode :program
                  :stobjs (acl2::state)))
  (prog2$
   (LET ((process  (nth 0 (@ wormhole-input)))
         (id       (nth 1 (@ wormhole-input)))
         (cl       (nth 2 (@ wormhole-input)))
         (clauses  (nth 3 (@ wormhole-input)))
         (hist-obj (nth 4 (@ wormhole-input)))
         (NAMES
          (REMOVE-DUPLICATES-EQUAL
           (STRIP-CADRS
            (NUMES-TO-RUNES
             (car (wormhole-data (@ wormhole-status)))
             (@ ACL2::NUME-TO-RUNE-MAP))))))
     (CW
      "Subgoal ~x0~%~
            ~q1~
            ~@2 ~x3 goal~#4~[~/s~]~#5~[~/, using ~&6~].~%~%"
      ID
      (PRETTYIFY-CLAUSE CL)
      (CASE PROCESS
        (APPLY-HINTS-CLAUSE "Apply hints to produce")
        (SIMPLIFY-CLAUSE "Simplify to produce")
        (SETTLED-DOWN-CLAUSE "This clause has settled down to")
        (ELIMINATE-DESTRUCTORS-CLAUSE
         "Eliminate destructors to produce")
        (INDUCT-CLAUSE
         (CONS "Induct according to ~xa to produce"
               (LIST
                (CONS #\a
                      (CAR (CDR (ASSOC :SUGGESTORS
                                       hist-obj
                                       )))))))
        (OTHERWISE "Apply unknown process to produce"))
      (LEN clauses)
      (IF (AND (NOT (ENDP clauses))
               (ENDP (CDR clauses)))
          0 1)
      (IF (ENDP NAMES) 0 1)
      NAMES))
   (er-progn
    (assign wormhole-status
            (set-wormhole-data (@ wormhole-status)
                               (cons (union-equal (car (wormhole-data (@ wormhole-status)))
                                                  (cadr (wormhole-data (@ wormhole-status))))
                                     (cddr (wormhole-data (@ wormhole-status))))))
    (value :q))))

(defmacro <apply-waterfall-process-id> (body)
  `(prog2$
    (push-nume-frame nil)
    (mv-let
     (signal clauses hist-obj pspv)
     ,body
     (cond
      ((eq signal 'hit)
       (prog2$
        (wormhole
         'nume-stack
         '(lambda (whs) whs)
         (list process id cl clauses hist-obj)
         '(apply-waterfall-process-msg-and-pop-nume-frame-t acl2::state)
         :ld-prompt nil
         :ld-verbose nil
         :ld-pre-eval-print nil)
        (mv signal clauses hist-obj pspv)))
      (t (prog2$
          (pop-nume-frame-nil)
          (mv signal clauses hist-obj pspv)))))))

(defun prove-summary-msg (acl2::state)
  (declare (xargs :mode :program
                  :stobjs (acl2::state)))
  (prog2$
   (cw "~x0~%"
       (CONS 'SUMMARY
             (NUMES-TO-RUNES
              (CAR (wormhole-data (@ wormhole-status)))
              (@ ACL2::NUME-TO-RUNE-MAP))))
   (value :q)))

(defmacro <prove-id> (body)
  `(let ((proof-attempt
          (with-nume-tracking (proof-attempt) ,body :RESET t)))
     (prog2$
      (wormhole 'nume-stack
                '(lambda (whs) whs)
                nil
                '(prove-summary-msg acl2::state)
                :ld-prompt nil
                :ld-verbose nil
                :ld-pre-eval-print nil)
      proof-attempt)))

