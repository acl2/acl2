; ACL2 Version 8.0 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2017, Regents of the University of Texas

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

; Rockwell Addition: A major change is the provision of non-executable
; functions.  These are typically functions that use stobjs but which
; are translated as though they were theorems rather than definitions.
; This is convenient (necessary?) for specifying some stobj
; properties.  These functions will have executable-counterparts that
; just throw.  These functions will be marked with the property
; non-executablep.

(defconst *mutual-recursion-ctx-string*
  "( MUTUAL-RECURSION ( DEFUN ~x0 ...) ...)")

(defun translate-bodies1 (non-executablep names bodies bindings
                                          known-stobjs-lst ctx wrld state-vars)

; Non-executablep should be t or nil, to indicate whether or not the bodies are
; to be translated for execution.  In the case of a function introduced by
; defproxy, non-executablep will be nil.

  (cond ((null bodies) (trans-value nil))
        (t (mv-let
            (erp x bindings2)
            (translate1-cmp (car bodies)
                            (if non-executablep t (car names))
                            (if non-executablep nil bindings)
                            (car known-stobjs-lst)
                            (if (and (consp ctx)
                                     (equal (car ctx)
                                            *mutual-recursion-ctx-string*))
                                (msg "( MUTUAL-RECURSION ... ( DEFUN ~x0 ...) ~
                                      ...)"
                                     (car names))
                              ctx)
                            wrld state-vars)
            (cond
             ((and erp
                   (eq bindings2 :UNKNOWN-BINDINGS))

; We try translating in some other order.  This attempt isn't complete; for
; example, the following succeeds, but it fails if we switch the first two
; definitions.  But it's cheap and better than nothing; without it, the
; unswitched version would fail, too.  If this becomes an issue, consider the
; potentially quadratic algorithm of first finding one definition that
; translates successfully, then another, and so on, until all have been
; translated.

; (set-state-ok t)
; (set-bogus-mutual-recursion-ok t)
; (program)
; (mutual-recursion
;  (defun f1 (state)
;    (let ((state (f-put-global 'last-m 1 state)))
;      (f2 state)))
;  (defun f2 (state)
;    (let ((state (f-put-global 'last-m 1 state)))
;      (f3 state)))
;  (defun f3 (state)
;    state))

              (trans-er-let*
               ((y (translate-bodies1 non-executablep
                                      (cdr names)
                                      (cdr bodies)
                                      bindings
                                      (cdr known-stobjs-lst)
                                      ctx wrld state-vars))
                (x (translate1-cmp (car bodies)
                                   (if non-executablep t (car names))
                                   (if non-executablep nil bindings)
                                   (car known-stobjs-lst)
                                   (if (and (consp ctx)
                                            (equal (car ctx)
                                                   *mutual-recursion-ctx-string*))
                                       (msg "( MUTUAL-RECURSION ... ( DEFUN ~x0 ...) ~
                                      ...)"
                                            (car names))
                                     ctx)
                                   wrld state-vars)))
               (trans-value (cons x y))))
             (erp (mv erp x bindings2))
             (t (let ((bindings bindings2))
                  (trans-er-let*
                   ((y (translate-bodies1 non-executablep
                                          (cdr names)
                                          (cdr bodies)
                                          bindings
                                          (cdr known-stobjs-lst)
                                          ctx wrld state-vars)))
                   (trans-value (cons x y))))))))))

(defun chk-non-executable-bodies (names arglists bodies non-executablep ctx
                                        state)

; Note that bodies are in translated form.

  (cond ((endp bodies)
         (value nil))
        (t (let ((name (car names))
                 (body (car bodies))
                 (formals (car arglists)))

; The body should generally be a translated form of (prog2$
; (throw-nonexec-error 'name (list . formals)) ...), as laid down by
; defun-nx-fn.  But we make an exception for defproxy, i.e. (eq non-executablep
; :program), since it won't be true in that case and we don't care that it be
; true, as we have a program-mode function that does a throw.

             (cond ((throw-nonexec-error-p body
                                           (and (not (eq non-executablep
                                                         :program))
                                                name)
                                           formals)
                    (chk-non-executable-bodies
                     (cdr names) (cdr arglists) (cdr bodies)
                     non-executablep ctx state))
                   (t (er soft ctx
                          "The body of a defun that is marked :non-executable ~
                           (perhaps implicitly, by the use of defun-nx) must ~
                           be of the form (prog2$ (throw-nonexec-error ...) ~
                           ...)~@1.  The definition of ~x0 is thus illegal.  ~
                           See :DOC defun-nx."
                          (car names)
                          (if (eq non-executablep :program)
                              ""
                            " that is laid down by defun-nx"))))))))

(defun translate-bodies (non-executablep names arglists bodies known-stobjs-lst
                                         reclassifying-all-programp
                                         ctx wrld state)

; Translate the bodies given and return a pair consisting of their translations
; and the final bindings from translate.  Note that non-executable :program
; mode functions need to be analyzed for stobjs-out, because they are proxies
; (see :DOC defproxy) for encapsulated functions that may replace them later,
; and we need to guarantee to callers that those stobjs-out do not change with
; such replacements.

  (declare (xargs :guard (true-listp bodies)))
  (mv-let (erp lst bindings)
          (translate-bodies1 (eq non-executablep t) ; not :program
                             names bodies
                             (pairlis$ names names)
                             known-stobjs-lst
                             ctx wrld
                             (default-state-vars t

; For the application of verify-termination to a function that has already
; been admitted, we avoid failure due to an untouchable function or variable.

                               :temp-touchable-fns
                               (or reclassifying-all-programp
                                   (f-get-global 'temp-touchable-fns
                                                 state))
                               :temp-touchable-vars
                               (or reclassifying-all-programp
                                   (f-get-global 'temp-touchable-vars
                                                 state))))
          (er-progn
           (cond (erp ; erp is a ctx, lst is a msg
                  (er soft erp "~@0" lst))
                 (non-executablep
                  (chk-non-executable-bodies names arglists lst
                                             non-executablep ctx state))
                 (t (value nil)))
           (cond ((eq non-executablep t)
                  (value (cons lst (pairlis-x2 names '(nil)))))
                 (t (value (cons lst bindings)))))))

; The next section develops our check that mutual recursion is
; sensibly used.

(defun chk-mutual-recursion-bad-names (lst names bodies)
  (cond ((null lst) nil)
        ((ffnnamesp names (car bodies))
         (chk-mutual-recursion-bad-names (cdr lst) names (cdr bodies)))
        (t
         (cons (car lst)
               (chk-mutual-recursion-bad-names (cdr lst) names (cdr bodies))))))

(defconst *chk-mutual-recursion-string*
  "The definition~#0~[~/s~] of ~&1 ~#0~[does~/do~] not call any of ~
   the other functions being defined via ~
   mutual recursion.  The theorem prover ~
   will perform better if you define ~&1 ~
   without the appearance of mutual recursion.  See ~
  :DOC set-bogus-mutual-recursion-ok to get ~
   ACL2 to handle this situation differently.")

(defun chk-mutual-recursion1 (names bodies warnp ctx state)
  (cond
   ((and warnp
         (warning-disabled-p "mutual-recursion"))
    (value nil))
   (t
    (let ((bad (chk-mutual-recursion-bad-names names names bodies)))
      (cond ((null bad) (value nil))
            (warnp
             (pprogn
              (warning$ ctx ("mutual-recursion")
                        *chk-mutual-recursion-string*
                        (if (consp (cdr bad)) 1 0)
                        bad)
              (value nil)))
            (t (er soft ctx
                   *chk-mutual-recursion-string*
                   (if (consp (cdr bad)) 1 0)
                   bad)))))))

(defun chk-mutual-recursion (names bodies ctx state)

; We check that names has at least 1 element and that if it has
; more than one then every body calls at least one of the fns in
; names.  The idea is to ensure that mutual recursion is used only
; when "necessary."  This is not necessary for soundness but since
; mutually recursive fns are not handled as well as singly recursive
; ones, it is done as a service to the user.  In addition, several
; error messages and other user-interface features exploit the presence
; of this check.

  (cond ((null names)
         (er soft ctx
             "It is illegal to use MUTUAL-RECURSION to define no functions."))
        ((null (cdr names)) (value nil))
        (t
         (let ((bogus-mutual-recursion-ok
                (cdr (assoc-eq :bogus-mutual-recursion-ok
                               (table-alist 'acl2-defaults-table (w state))))))
           (if (eq bogus-mutual-recursion-ok t)
               (value nil)
             (chk-mutual-recursion1 names bodies
                                    (eq bogus-mutual-recursion-ok :warn)
                                    ctx state))))))

; We now develop put-induction-info.

(mutual-recursion

(defun ffnnamep-mod-mbe (fn term)

; We determine whether the function fn (possibly a lambda-expression) is used
; as a function in term', the result of expanding mbe calls (and equivalent
; calls) in term.  Keep this in sync with the ffnnamep nest.  Unlike ffnnamep,
; we assume here that fn is a symbolp.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (ffnnamep-mod-mbe fn (lambda-body (ffn-symb term)))
             (ffnnamep-mod-mbe-lst fn (fargs term))))
        ((eq (ffn-symb term) fn) t)
        ((and (eq (ffn-symb term) 'return-last)
              (quotep (fargn term 1))
              (eq (unquote (fargn term 1)) 'mbe1-raw))
         (ffnnamep-mod-mbe fn (fargn term 3)))
        (t (ffnnamep-mod-mbe-lst fn (fargs term)))))

(defun ffnnamep-mod-mbe-lst (fn l)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-listp l))))
  (if (null l)
      nil
    (or (ffnnamep-mod-mbe fn (car l))
        (ffnnamep-mod-mbe-lst fn (cdr l)))))

)

; Here is how we set the recursivep property.

; Rockwell Addition:  The recursivep property has changed.  Singly
; recursive fns now have the property (fn) instead of fn.

(defun putprop-recursivep-lst (names bodies wrld)

; On the property list of each function symbol is stored the 'recursivep
; property.  For nonrecursive functions, the value is implicitly nil but no
; value is stored (see comment below).  Otherwise, the value is a true-list of
; fn names in the ``clique.''  Thus, for singly recursive functions, the value
; is a singleton list containing the function name.  For mutually recursive
; functions the value is the list of every name in the clique.  This function
; stores the property for each name and body in names and bodies.

; WARNING: We rely on the fact that this function puts the same names into the
; 'recursivep property of each member of the clique, in our handling of
; being-openedp.  Moreover, we rely in function termination-theorem-fn-subst
; (and its supporting functions) that the properties are placed in the order in
; which the names are defined: (mutual-recursion (defun name1 ...) (defun name2
; ... ...)) pushes a property for name1 onto a world with property for name2,
; etc.

  (cond ((int= (length names) 1)
         (cond ((ffnnamep-mod-mbe (car names) (car bodies))
                (putprop (car names) 'recursivep names wrld))
               (t

; Until we started using the 'def-bodies property to answer most questions
; about recursivep (see macro recursivep), it was a good idea to put a
; 'recursivep property of nil in order to avoid having getprop walk through an
; entire association list looking for 'recursivep.  Now, this less-used
; property is just in the way.

                wrld)))
        (t (putprop-x-lst1 names 'recursivep names wrld))))

; Formerly, we defined termination-machines and some of its supporting
; functions here.  But we moved them to history-management.lisp in order to
; support the definition of termination-theorem-clauses.

; We next develop the function that guesses measures when the user has
; not supplied them.

(defun proper-dumb-occur-as-output (x y)

; We determine whether the term x properly occurs within the term y, insisting
; in addition that if y is an IF expression then x occurs properly within each
; of the two output branches.

; For example, X does not properly occur in X or Z.  It does properly occur in
; (CDR X) and (APPEND X Y).  It does properly occur in (IF a (CDR X) (CAR X))
; but not in (IF a (CDR X) 0) or (IF a (CDR X) X).

; This function is used in always-tested-and-changedp to identify a formal to
; use as the measured formal in the justification of a recursive definition.
; We seek a formal that is tested on every branch and changed in every
; recursion.  But if (IF a (CDR X) X) is the new value of X in some recursion,
; then it is not really changed, since if we distributed the IF out of the
; recursive call we would see a call in which X did not change.

  (cond ((equal x y) nil)
        ((variablep y) nil)
        ((fquotep y) nil)
        ((eq (ffn-symb y) 'if)
         (and (proper-dumb-occur-as-output x (fargn y 2))
              (proper-dumb-occur-as-output x (fargn y 3))))
        (t (dumb-occur-lst x (fargs y)))))

(defun always-tested-and-changedp (var pos t-machine)

; Is var involved in every tests component of t-machine and changed
; and involved in every call, in the appropriate argument position?
; In some uses of this function, var may not be a variable symbol
; but an arbitrary term.

  (cond ((null t-machine) t)
        ((and (dumb-occur-lst var
                              (access tests-and-call
                                      (car t-machine)
                                      :tests))
              (let ((argn (nth pos
                               (fargs (access tests-and-call
                                              (car t-machine)
                                              :call)))))

; If argn is nil then it means there were not enough args to get the one at
; pos.  This can happen in a mutually recursive clique where not all clique
; members have the same arity.

                (and argn
                     (proper-dumb-occur-as-output var argn))))
         (always-tested-and-changedp var pos (cdr t-machine)))
        (t nil)))

(defun guess-measure (name defun-flg args pos t-machine ctx wrld state)

; T-machine is a termination machine, i.e., a lists of tests-and-call.  Because
; of mutual recursion, we do not know that the call of a tests-and-call is a
; call of name; it may be a call of a sibling of name.  We look for the first
; formal that is (a) somehow tested in every test and (b) somehow changed in
; every call.  Upon finding such a var, v, we guess the measure (acl2-count v).
; But what does it mean to say that v is "changed in a call" if we are defining
; (foo x y v) and see a call of bar?  We mean that v occurs in an argument to
; bar and is not equal to that argument.  Thus, v is not changed in (bar x v)
; and is changed in (bar x (mumble v)).  The difficulty here of course is that
; (mumble v) may not be being passed as the new value of v.  But since this is
; just a heuristic guess intended to save the user the burden of typing
; (acl2-count x) a lot, it doesn't matter.

; If we fail to find a measure we cause an error.

; Pos is initially 0 and is the position in the formals list of the first
; variable listed in args.  Defun-flg is t if we are guessing a measure on
; behalf of a function definition and nil if we are guessing on behalf of a
; :definition rule.  It affects only the error message printed.

  (cond ((null args)
         (cond
          ((null t-machine)

; Presumably guess-measure was called here with args = NIL, for example if
; :set-bogus-mutual-recursion allowed it.  We pick a silly measure that will
; work.  If it doesn't work (hard to imagine), well then, we'll find out when
; we try to prove termination.

           (value (mcons-term* (default-measure-function wrld) *0*)))
          (t
           (er soft ctx
               "No ~#0~[:MEASURE~/:CONTROLLER-ALIST~] was supplied with the ~
                ~#0~[definition of~/proposed :DEFINITION rule for~] ~x1.  Our ~
                heuristics for guessing one have not made any suggestions.  ~
                No argument of the function is tested along every branch of ~
                the relevant IF structure and occurs as a proper subterm at ~
                the same argument position in every recursive call.  You must ~
                specify a ~#0~[:MEASURE.  See :DOC defun.~/:CONTROLLER-ALIST. ~
                ~ See :DOC definition.~@2~]  Also see :DOC ruler-extenders ~
                for how to affect how much of the IF structure is explored by ~
                our heuristics."
               (if defun-flg 0 1)
               name
               (cond
                (defun-flg "")
                (t "  In some cases you may wish to use the :CONTROLLER-ALIST ~
                    from the original (or any previous) definition; this may ~
                    be seen by using :PR."))))))
        ((always-tested-and-changedp (car args) pos t-machine)
         (value (mcons-term* (default-measure-function wrld) (car args))))
        (t (guess-measure name defun-flg (cdr args) (1+ pos)
                          t-machine ctx wrld state))))

(defun guess-measure-alist (names arglists measures t-machines ctx wrld state)

; We either cause an error or return an alist mapping the names in
; names to their measures (either user suggested or guessed).

; Warning: The returned alist, a, should have the property that (strip-cars a)
; is equal to names.  We rely on that property in put-induction-info.

  (cond ((null names) (value nil))
        ((equal (car measures) *no-measure*)
         (er-let* ((m (guess-measure (car names)
                                     t
                                     (car arglists)
                                     0
                                     (car t-machines)
                                     ctx wrld state)))
                  (er-let* ((alist (guess-measure-alist (cdr names)
                                                        (cdr arglists)
                                                        (cdr measures)
                                                        (cdr t-machines)
                                                        ctx wrld state)))
                           (value (cons (cons (car names) m)
                                        alist)))))
        (t (er-let* ((alist (guess-measure-alist (cdr names)
                                                 (cdr arglists)
                                                 (cdr measures)
                                                 (cdr t-machines)
                                                 ctx wrld state)))
                    (value (cons (cons (car names) (car measures))
                                 alist))))))

; We now embark on the development of prove-termination, which must
; prove the justification theorems for each termination machine and
; the measures supplied/guessed.

; Moved remove-built-in-clauses and clean-up-clause-set to
; history-management.lisp.

; Formerly, we defined measure-clauses-for-clique and some of its supporting
; functions here.  But we moved them to history-management.lisp in order to
; support the definition of termination-theorem-clauses.

(defun tilde-*-measure-phrase1 (alist wrld)
  (cond ((null alist) nil)
        (t (cons (msg (cond ((null (cdr alist)) "~p1 for ~x0.")
                            (t "~p1 for ~x0"))
                      (caar alist)
                      (untranslate (cdar alist) nil wrld))
                 (tilde-*-measure-phrase1 (cdr alist) wrld)))))

(defun tilde-*-measure-phrase (alist wrld)

; Let alist be an alist mapping function symbols, fni, to measure terms, mi.
; The fmt directive ~*0 will print the following, if #\0 is bound to
; the output of this fn:

; "m1 for fn1, m2 for fn2, ..., and mk for fnk."

; provided alist has two or more elements.  If alist contains
; only one element, it will print just "m1."

; Note the final period at the end of the phrase!  In an earlier version
; we did not add the period and saw a line-break between the ~x1 below
; and its final period.

; Thus, the following fmt directive will print a grammatically correct
; sentence ending with a period: "For the admission of ~&1 we will use
; the measure ~*0"

  (list* "" "~@*" "~@* and " "~@*, "
         (cond
          ((null (cdr alist))
           (list (cons "~p1."
                       (list (cons #\1
                                   (untranslate (cdar alist) nil wrld))))))
          (t (tilde-*-measure-phrase1 alist wrld)))
         nil))

(defun find-?-measure (measure-alist)
  (cond ((endp measure-alist) nil)
        ((let* ((entry (car measure-alist))
                (measure (cdr entry)))
           (and (consp measure)
                (eq (car measure) :?)
                entry)))
        (t (find-?-measure (cdr measure-alist)))))

(defun prove-termination (names t-machines measure-alist mp rel hints otf-flg
                                bodies measure-debug ctx ens wrld state ttree)

; Given a list of the functions introduced in a mutually recursive clique,
; their t-machines, the measure-alist for the clique, a domain predicate mp on
; which a certain relation, rel, is known to be well-founded, a list of hints
; (obtained by joining all the hints in the defuns), and a world in which we
; can find the 'formals of each function in the clique, we prove the theorems
; required by the definitional principle.  In particular, we prove that each
; measure is an o-p and that in every tests-and-call in the t-machine of each
; function, the measure of the recursive calls is strictly less than that of
; the incoming arguments.  If we fail, we cause an error.

; This function produces output describing the proofs.  It should be the first
; output-producing function in the defun processing on every branch through
; defun.  It always prints something and leaves you in a clean state ready to
; begin a new sentence, but may leave you in the middle of a line (i.e., col >
; 0).

; If we succeed we return two values, consed together as "the" value in this
; error/value/state producing function.  The first value is the column produced
; by our output.  The second value is a ttree in which we have accumulated all
; of the ttrees associated with each proof done.

; This function is specially coded so that if t-machines is nil then it is a
; signal that there is only one element of names and it is a non-recursive
; function.  In that case, we short-circuit all of the proof machinery and
; simply do the associated output.  We coded it this way to preserve the
; invariant that prove-termination is THE place the defun output is initiated.

; This function increments timers.  Upon entry, any accumulated time is charged
; to 'other-time.  The printing done herein is charged to 'print-time and the
; proving is charged to 'prove-time.

  (mv-let
   (cl-set cl-set-ttree)
   (cond ((and (not (ld-skip-proofsp state))
               t-machines)
          (clean-up-clause-set
           (measure-clauses-for-clique names
                                       t-machines
                                       measure-alist
                                       mp rel measure-debug
                                       wrld)
           ens
           wrld ttree state))
         (t (mv nil ttree)))
   (cond
    ((and (not (ld-skip-proofsp state))
          (find-?-measure measure-alist))
     (let* ((entry (find-?-measure measure-alist))
            (fn (car entry))
            (measure (cdr entry)))
       (er soft ctx
           "A :measure of the form (:? v1 ... vk) is only legal when the ~
            defun is redundant (see :DOC redundant-events) or when skipping ~
            proofs (see :DOC ld-skip-proofsp).  The :measure ~x0 supplied for ~
            function symbol ~x1 is thus illegal."
           measure fn)))
    (t
     (er-let*
      ((cl-set-ttree (accumulate-ttree-and-step-limit-into-state
                      cl-set-ttree :skip state)))
      (pprogn
       (increment-timer 'other-time state)
       (let ((displayed-goal (prettyify-clause-set cl-set
                                                   (let*-abstractionp state)
                                                   wrld))
             (simp-phrase (tilde-*-simp-phrase cl-set-ttree)))
         (mv-let
          (col state)
          (cond
           ((ld-skip-proofsp state)
            (mv 0 state))
           ((null t-machines)
            (io? event nil (mv col state)
                 (names)
                 (fmt "Since ~&0 is non-recursive, its admission is trivial."
                      (list (cons #\0 names))
                      (proofs-co state)
                      state
                      nil)
                 :default-bindings ((col 0))))
           ((null cl-set)
            (io? event nil (mv col state)
                 (measure-alist wrld rel names)
                 (fmt "The admission of ~&0 ~#0~[is~/are~] trivial, using ~@1 ~
                       and the measure ~*2"
                      (list (cons #\0 names)
                            (cons #\1 (tilde-@-well-founded-relation-phrase
                                       rel wrld))
                            (cons #\2 (tilde-*-measure-phrase
                                       measure-alist wrld)))
                      (proofs-co state)
                      state
                      (term-evisc-tuple nil state))
                 :default-bindings ((col 0))))
           (t
            (io? event nil (mv col state)
                 (cl-set-ttree displayed-goal simp-phrase measure-alist wrld
                               rel names)
                 (fmt "For the admission of ~&0 we will use ~@1 and the ~
                       measure ~*2  The non-trivial part of the measure ~
                       conjecture~#3~[~/, given ~*4,~] is~@5~%~%Goal~%~Q67."
                      (list (cons #\0 names)
                            (cons #\1 (tilde-@-well-founded-relation-phrase
                                       rel wrld))
                            (cons #\2 (tilde-*-measure-phrase
                                       measure-alist wrld))
                            (cons #\3 (if (nth 4 simp-phrase) 1 0))
                            (cons #\4 simp-phrase)
                            (cons #\5 (if (tagged-objectsp 'sr-limit
                                                           cl-set-ttree)
                                          " as follows (where the ~
                                           subsumption/replacement limit ~
                                           affected this analysis; see :DOC ~
                                           case-split-limitations)."
                                        ""))
                            (cons #\6 displayed-goal)
                            (cons #\7 (term-evisc-tuple nil state)))
                      (proofs-co state)
                      state
                      nil)
                 :default-bindings ((col 0)))))
          (pprogn
           (increment-timer 'print-time state)
           (cond
            ((null cl-set)

; If the io? above did not print because 'event is inhibited, then col is nil.
; Just to keep ourselves sane, we will set it to 0.

             (value (cons (or col 0) cl-set-ttree)))
            (t
             (mv-let
              (erp ttree state)
              (prove (termify-clause-set cl-set)
                     (make-pspv ens wrld state
                                :displayed-goal displayed-goal
                                :otf-flg otf-flg)
                     hints ens wrld ctx state)
              (cond (erp
                     (let ((erp-msg
                            (cond
                             ((subsetp-eq
                               '(summary error)
                               (f-get-global 'inhibit-output-lst state))

; This case is an optimization, in order to avoid the computations below, in
; particular of termination-machines.  Note that erp-msg is potentially used in
; error output -- see the (er soft ...) form below -- and it is also
; potentially used in summary output, when print-summary passes to
; print-failure the first component of the error triple returned below.

                              nil)
                             (t
                              (msg
                               "The proof of the measure conjecture for ~&0 ~
                                has failed.~@1"
                               names
                               (if (equal
                                    t-machines
                                    (termination-machines
                                     names bodies
                                     (make-list (length names)
                                                :initial-element
                                                :all)))
                                   ""
                                 (msg "~|**NOTE**:  The use of declaration ~
                                       ~x0 would change the measure ~
                                       conjecture, perhaps making it easier ~
                                       to prove.  See :DOC ruler-extenders."
                                      '(xargs :ruler-extenders :all))))))))
                       (mv-let
                        (erp val state)
                        (er soft ctx "~@0~|" erp-msg)
                        (declare (ignore erp val))
                        (mv (msg "~@0  " erp-msg) nil state))))
                    (t
                     (mv-let (col state)
                             (io? event nil (mv col state)
                                  (names)
                                  (fmt "That completes the proof of the ~
                                        measure theorem for ~&1.  Thus, we ~
                                        admit ~#1~[this function~/these ~
                                        functions~] under the principle of ~
                                        definition."
                                       (list (cons #\1 names))
                                       (proofs-co state)
                                       state
                                       nil)
                                  :default-bindings ((col 0)))
                             (pprogn
                              (increment-timer 'print-time state)
                              (value
                               (cons
                                (or col 0)
                                (cons-tag-trees
                                 cl-set-ttree ttree)))))))))))))))))))

; When we succeed in proving termination, we will store the
; justification properties.

(defun putprop-justification-lst (measure-alist subset-lst mp rel
                                                ruler-extenders-lst
                                                subversive-p wrld)

; Each function has a 'justification property.  The value of the property
; is a justification record.

  (cond ((null measure-alist) wrld)
        (t (putprop-justification-lst
            (cdr measure-alist) (cdr subset-lst) mp rel (cdr ruler-extenders-lst)
            subversive-p
            (putprop (caar measure-alist)
                     'justification
                     (make justification
                           :subset

; The following is equal to (all-vars (cdar measure-alist)), but since we
; already have it available, we use it rather than recomputing this all-vars
; call.

                           (car subset-lst)
                           :subversive-p subversive-p
                           :mp mp
                           :rel rel
                           :measure (cdar measure-alist)
                           :ruler-extenders (car ruler-extenders-lst))
                     wrld)))))

(defun union-equal-to-end (x y)

; This is like union-equal, but where a common element is removed from the
; second argument instead of the first.

  (cond ((intersectp-equal x y)
         (append x (set-difference-equal y x)))
        (t (append x y))))

(defun cross-tests-and-calls3 (tacs tacs-lst)
  (cond ((endp tacs-lst) nil)
        (t
         (let ((tests1 (access tests-and-calls tacs :tests))
               (tests2 (access tests-and-calls (car tacs-lst) :tests)))
           (cond ((some-element-member-complement-term tests1 tests2)
                  (cross-tests-and-calls3 tacs (cdr tacs-lst)))
                 (t (cons (make tests-and-calls
                                :tests (union-equal-to-end tests1 tests2)
                                :calls (union-equal
                                        (access tests-and-calls tacs
                                                :calls)
                                        (access tests-and-calls (car tacs-lst)
                                                :calls)))
                          (cross-tests-and-calls3 tacs (cdr tacs-lst)))))))))

(defun cross-tests-and-calls2 (tacs-lst1 tacs-lst2)

; See cross-tests-and-calls.

  (cond ((endp tacs-lst1) nil)
        (t (append (cross-tests-and-calls3 (car tacs-lst1) tacs-lst2)
                   (cross-tests-and-calls2 (cdr tacs-lst1) tacs-lst2)))))

(defun cross-tests-and-calls1 (tacs-lst-lst acc)

; See cross-tests-and-calls.

  (cond ((endp tacs-lst-lst) acc)
        (t (cross-tests-and-calls1 (cdr tacs-lst-lst)
                                   (cross-tests-and-calls2 (car tacs-lst-lst)
                                                           acc)))))

(defun sublis-tests-rev (test-alist acc)

; Each element of test-alist is a pair (test . alist) where test is a term and
; alist is either an alist or the atom :no-calls, which we treat as nil.  Under
; that interpretation, we return the list of all test/alist, in reverse order
; from test-alist.

  (cond ((endp test-alist) acc)
        (t (sublis-tests-rev
            (cdr test-alist)
            (let* ((test (caar test-alist))
                   (alist (cdar test-alist))
                   (inst-test (cond ((or (eq alist :no-calls)
                                         (null alist))
                                     test)
                                    (t (sublis-expr alist test)))))
              (cons inst-test acc))))))

(defun all-calls-test-alist (names test-alist acc)
  (cond ((endp test-alist) acc)
        (t (all-calls-test-alist
            names
            (cdr test-alist)
            (let* ((test (caar test-alist))
                   (alist (cdar test-alist)))
              (cond ((eq alist :no-calls)
                     acc)
                    (t
                     (all-calls names test alist acc))))))))

(defun cross-tests-and-calls (names top-test-alist top-calls tacs-lst-lst)

; We are given a list, tacs-lst-lst, of lists of non-empty lists of
; tests-and-calls records.  Each such record represents a list of tests
; together with a corresponding list of calls.  Each way of selecting elements
; <testsi, callsi> in the ith member of tacs-lst-lst can be viewed as a "path"
; through tacs-lst-lst (see also discussion of a matrix, below).  We return a
; list containing a tests-and-calls record formed for each path: the tests, as
; the union of the tests of top-test-alist (viewed as a list of entries
; test/alist; see sublis-tests-rev) and the testsi; and the calls, as the union
; of the top-calls and the callsi.

; We can visualize the above discussion by forming a sort of matrix as follows.
; The columns (which need not all have the same length) are the elements of
; tacs-lst-lst; typically, for some call of a function in names, each column
; contains the tests-and-calls records formed from an argument of that call
; using induction-machine-for-fn1.  A "path", as discussed above, is formed by
; picking one record from each column.  The order of records in the result is
; probably not important, but it seems reasonable to give priority to the
; records from the first argument by starting with all paths containing the
; first record of the first argument; and so on.

; Note that the records are in the desired order for each list in tacs-lst-lst,
; but are in reverse order for top-test-alist, and also tacs-lst-lst is in
; reverse order, i.e., it corresponds to the arguments of some function call
; but in reverse argument order.

; For any tests-and-calls record: we view the tests as their conjunction, we
; view the calls as specifying substitutions, and we view the measure formula
; as the implication specifying that the substitutions cause an implicit
; measure to go down, assuming the tests.  Logically, we want the resulting
; list of tests-and-calls records to have the following properties.

; - Coverage: The disjunction of the tests is provably equivalent to the
;   conjunction of the tests in top-test-alist.

; - Disjointness: The conjunction of any two tests is provably equal to nil.

; - Measure: Each measure formula is provable.

; We assume that each list in tacs-lst-lst has the above three properties, but
; with top-test-alist being the empty list (that is, with conjunction of T).

; It's not clear as of this writing that Disjointness is necessary.  The others
; are critical for justifying the induction schemes that will ultimately be
; generated from the tests-and-calls records.

; (One may imagine an alternate approach that avoids taking this sort of cross
; product, by constructing induction schemes with inductive hypotheses of the
; form (implies (and <conjoined_path_of_tests> <calls_for_that_path>)).  But
; then the current tests-and-calls data structure and corresponding heuristics
; would have to be revisited.)

  (let ((full-tacs-lst-lst
         (append tacs-lst-lst
                 (list
                  (list (make tests-and-calls
                              :tests (sublis-tests-rev top-test-alist nil)
                              :calls (all-calls-test-alist names
                                                           top-test-alist
                                                           top-calls)))))))
    (cross-tests-and-calls1
     (cdr full-tacs-lst-lst)
     (car full-tacs-lst-lst))))

(mutual-recursion

(defun induction-machine-for-fn1 (names body alist test-alist calls
                                        ruler-extenders merge-p)

; At the top level, this function builds a list of tests-and-calls for the
; given body of a function in names, a list of all the mutually recursive fns
; in a clique.  Note that we don't need to know the function symbol to which
; the body belongs; all the functions in names are considered "recursive"
; calls.  As we recur, we are considering body/alist, with accumulated tests
; consisting of test/a for test (test . a) in test-alist (but see :no-calls
; below, treated as the nil alist), and accumulated calls (already
; instantiated).

; To understand this algorithm, let us first consider the case that there are
; no lambda applications in body, which guarantees that alist will be empty on
; every recursive call, and ruler-extenders is nil.  We explore body,
; accumulating into the list of tests (really, test-alist, but we defer
; discussion of the alist aspect) as we dive: for (if x y z), we accumulate x
; as we dive into y, and we accumulate the negation of x as we dive into z.
; When we hit a term u for which we are blocked from diving further (because we
; have encountered other than an if-term, or are diving into the first argument
; of an if-term), we collect up all the tests, reversing them to restore them
; to the order in which they were encountered from the top, and we collect up
; all calls of functions in names that are subterms of u or of any of the
; accumulated tests.  From the termination analysis we know that assuming the
; collected tests, the arguments for each call are suitably smaller than the
; formals of the function symbol of that call, where of course, for a test only
; the tests superior to it are actually necessary.

; There is a subtle aspect to the handling of the tests in the above algorithm.
; To understand it, consider the following example.  Suppose names is (f), p is
; a function symbol, 'if is in ruler-extenders, and body is:
;  (if (consp x)
;      (if (if (consp x)
;              (p x)
;            (p (f (cons x x))))
;          x
;        (f (cdr x)))
;    x)
; Since 'if is in ruler-extenders, termination analysis succeeds because the
; tests leading to (f (cons x x)) are contradictory.  But with the naive
; algorithm described above, when we encounter the term (f (cdr x)) we would
; create a tests-and-calls record that collects up the call (f (cons x x)); yet
; clearly (cons x x) is not smaller than the formal x under the default measure
; (acl2-count x), even assuming (consp x) and (not (p (f (cons x x)))).

; Thus it is unsound in general to collect all the calls of a ruling test when
; 'if is among the ruler-extenders.  But we don't need to do so anyhow, because
; we will collect suitable calls from the first argument of an 'if test as we
; dive into it, relying on cross-tests-and-calls to incorporate those calls, as
; described below.  We still have to note the test as we dive into the true and
; false branches of an IF call, but that test should not contribute any calls
; when the recursion bottoms out under one of those branches.

; A somewhat similar issue arises with lambda applications in the case that
; :lambdas is among the ruler-extenders.  Consider the term ((lambda (x) (if
; <test> <tbr> <fbr>)) <arg>).  With :lambdas among the ruler-extenders, we
; will be diving into <arg>, and not every call in <arg> may be assumed to be
; "smaller" than the formals as we are exploring the body of the lambda.  So we
; need to collect up the combination of <test> and an alist binding lambda
; formals to actuals (in this example, binding x to <arg>, or more generally,
; the instantiation of <arg> under the existing bindings).  That way, when the
; recursion bottoms out we can collect calls explicitly in that test (unless
; 'if is in ruler-extenders, as already described), instantiating them with the
; associated alist.  If we instead had collected up the instantiated test, we
; would also have collected all calls in <arg> above when bottoming out in the
; lambda body, and that would be a mistake (as discussed above, since not every
; call in arg is relevant).

; So when the recursion bottoms out, some tests should not contribute any
; calls, and some should be instantiated with a corresponding alist.  As we
; collect a test when we recur into the true or false branch of an IF call, we
; thus actually collect a pair consisting of the test and a corresponding
; alist, signifying that for every recursive call c in the test, the actual
; parameter list for c/a is known to be "smaller" than the formals.  If
; ruler-extenders is the default, then all calls of the instantiated test are
; known to be "smaller", so we pair the instantiated test with nil.  But if 'if
; is in the ruler-extenders, then we do not want to collect any calls of the
; test -- as discussed above, cross-tests-and-calls will take care of them --
; so we pair the instantiated test with the special indicator :no-calls.

; The merge-p argument concerns the question of whether exploration of a term
; (if test tbr fbr) should create two tests-and-calls records even if there are
; no recursive calls in tbr or fbr.  For backward compatibility, the answer is
; "no" if we are exploring according to the conventional notion of "rulers".
; But now imagine a function body that has many calls of 'if deep under
; different arguments of some function call.  If we create separate records as
; in the conventional case, the induction scheme may explode when we combine
; these cases with cross-tests-and-calls -- it will be as though we clausified
; even before starting the induction proof proper.  But if we avoid such a
; priori case-splitting, then during the induction proof, it is conceivable
; that many of these potential separate cases could be dispatched with
; rewriting, thus avoiding so much case splitting.

; So if merge-p is true, then we avoid creating tests-and-calls records when
; both branches of an IF term have no recursive calls.  We return (mv flag
; tests-and-calls-lst), where if merge-p is true, then flag is true exactly
; when a call of a function in names has been encountered.  For backward
; compatibility, merge-p is false except when we the analysis has taken
; advantage of ruler-extenders.  If merge-p is false, then the first returned
; value is irrelevant.

; Note: Perhaps some calls of reverse can be omitted, though that might ruin
; some regressions.  Our main concern for replayability has probably been the
; order of the tests, not so much the order of the calls.

  (cond
   ((or (variablep body)
        (fquotep body)
        (and (not (flambda-applicationp body))
             (not (eq (ffn-symb body) 'if))
             (not (and (eq (ffn-symb body) 'return-last)
                       (quotep (fargn body 1))
                       (eq (unquote (fargn body 1)) 'mbe1-raw)))
             (not (member-eq-all (ffn-symb body) ruler-extenders))))
    (mv (and merge-p ; optimization
             (ffnnamesp names body))
        (list (make tests-and-calls
                    :tests (sublis-tests-rev test-alist nil)
                    :calls (reverse
                            (all-calls names body alist
                                       (all-calls-test-alist
                                        names
                                        (reverse test-alist)
                                        calls)))))))
   ((flambda-applicationp body)
    (cond
     ((member-eq-all :lambdas ruler-extenders) ; other case is easier to follow
      (mv-let (flg1 temp1)
              (induction-machine-for-fn1 names
                                         (lambda-body (ffn-symb body))
                                         (pairlis$
                                          (lambda-formals (ffn-symb body))
                                          (sublis-var-lst alist (fargs body)))
                                         nil ; test-alist
                                         nil ; calls
                                         ruler-extenders

; The following example shows why we use merge-p = t when ruler-extenders
; includes :lambdas.

; (defun app (x y)
;   ((lambda (result)
;      (if (our-test result)
;          result
;        0))
;    (if (endp x)
;        y
;      (cons (car x)
;            (app (cdr x) y)))))

; If we do not use t, then we wind up crossing two base cases from the lambda
; body with two from the arguments, which seems like needless explosion.

                                         t)
              (mv-let (flg2 temp2)
                      (induction-machine-for-fn1-lst names
                                                     (fargs body)
                                                     alist
                                                     ruler-extenders
                                                     nil ; acc
                                                     t ; merge-p
                                                     nil) ; flg
                      (mv (or flg1 flg2)
                          (cross-tests-and-calls
                           names
                           test-alist
                           calls

; We cons the lambda-body's contribution to the front, since we want its tests
; to occur after those of the arguments to the lambda application (because the
; lambda body occurs lexically last in a LET form, so this will make the most
; sense to the user).  Note that induction-machine-for-fn1-lst returns its
; result in reverse of the order of arguments.  Thus, the following cons will
; be in the reverse order that is expected by cross-tests-and-calls.

                           (cons temp1 temp2))))))
     (t ; (not (member-eq-all :lambdas ruler-extenders))

; We just go straight into the body of the lambda, with the appropriate alist.
; But we modify calls, so that every tests-and-calls we build will contain all
; of the calls occurring in the actuals to the lambda application.

      (mv-let
       (flg temp)
       (induction-machine-for-fn1 names
                                  (lambda-body (ffn-symb body))
                                  (pairlis$
                                   (lambda-formals (ffn-symb body))
                                   (sublis-var-lst alist (fargs body)))
                                  test-alist
                                  (all-calls-lst names (fargs body) alist
                                                 calls)
                                  ruler-extenders
                                  merge-p)
       (mv (and merge-p ; optimization
                (or flg
                    (ffnnamesp-lst names (fargs body))))
           temp)))))
   ((and (eq (ffn-symb body) 'return-last)
         (quotep (fargn body 1))
         (eq (unquote (fargn body 1)) 'mbe1-raw))

; See the comment in termination-machine about it being sound to treat
; return-last as a macro.

    (induction-machine-for-fn1 names
                               (fargn body 3)
                               alist
                               test-alist
                               calls
                               ruler-extenders
                               merge-p))
   ((eq (ffn-symb body) 'if)
    (let ((test

; Since (remove-guard-holders x) is provably equal to x, the machine we
; generate using it below is equivalent to the machine generated without it.

           (remove-guard-holders (fargn body 1))))
      (cond
       ((member-eq-all 'if ruler-extenders) ; other case is easier to follow
        (mv-let
         (tst-flg tst-result)
         (induction-machine-for-fn1 names
                                    (fargn body 1) ; keep guard-holders
                                    alist
                                    test-alist
                                    calls
                                    ruler-extenders
                                    t)
         (let ((inst-test (sublis-var alist test))
               (merge-p (or merge-p

; If the test contains a recursive call then we prefer to merge when computing
; the induction machines for the true and false branches, to avoid possible
; explosion in cases.

                            tst-flg)))
           (mv-let
            (tbr-flg tbr-result)
            (induction-machine-for-fn1 names
                                       (fargn body 2)
                                       alist
                                       (cons (cons inst-test :no-calls)
                                             nil) ; tst-result has the tests
                                       nil ; calls, already in tst-result
                                       ruler-extenders
                                       merge-p)
            (mv-let
             (fbr-flg fbr-result)
             (induction-machine-for-fn1 names
                                        (fargn body 3)
                                        alist
                                        (cons (cons (dumb-negate-lit inst-test)
                                                    :no-calls)
                                              nil) ; tst-result has the tests
                                        nil ; calls, already in tst-result
                                        ruler-extenders
                                        merge-p)
             (cond ((and merge-p
                         (not (or tbr-flg fbr-flg)))
                    (mv tst-flg tst-result))
                   (t
                    (mv (or tbr-flg fbr-flg tst-flg)
                        (cross-tests-and-calls
                         names
                         nil ; top-test-alist
                         nil ; calls are already in tst-result

; We put the branch contributions on the front, since their tests are to wind
; up at the end, in analogy to putting the lambda body on the front as
; described above.

                         (list (append tbr-result fbr-result)
                               tst-result))))))))))
       (t ; (not (member-eq-all 'if ruler-extenders))
        (mv-let
         (tbr-flg tbr-result)
         (induction-machine-for-fn1 names
                                    (fargn body 2)
                                    alist
                                    (cons (cons test alist)
                                          test-alist)
                                    calls
                                    ruler-extenders
                                    merge-p)
         (mv-let
          (fbr-flg fbr-result)
          (induction-machine-for-fn1 names
                                     (fargn body 3)
                                     alist
                                     (cons (cons (dumb-negate-lit test)
                                                 alist)
                                           test-alist)
                                     calls
                                     ruler-extenders
                                     merge-p)
          (cond ((and merge-p
                      (not (or tbr-flg fbr-flg)))
                 (mv nil
                     (list (make tests-and-calls
                                 :tests
                                 (sublis-tests-rev test-alist nil)
                                 :calls
                                 (all-calls names test alist
                                            (reverse
                                             (all-calls-test-alist
                                              names
                                              (reverse test-alist)
                                              calls)))))))
                (t
                 (mv (or tbr-flg fbr-flg)
                     (append tbr-result fbr-result))))))))))
   (t ; (member-eq-all (ffn-symb body) ruler-extenders) and not lambda etc.
    (mv-let (merge-p args)

; The special cases just below could perhaps be nicely generalized to any call
; in which at most one argument contains calls of any name in names.  We found
; that we needed to avoid merge-p=t on the recursive call in the prog2$ case
; (where no recursive call is in the first argument) when we introduced
; defun-nx after Version_3.6.1, since the resulting prog2$ broke community book
; books/tools/flag.lisp, specifically event (FLAG::make-flag flag-pseudo-termp
; ...), because the :normalize nil kept the prog2$ around and merge-p=t then
; changed the induction scheme.

; Warning: Do not be tempted to skip the call of cross-tests-and-calls in the
; special cases below for mv-list, prog2$ and arity 1.  It is needed in order
; to handle :no-calls (used above).

            (cond ((and (eq (ffn-symb body) 'mv-list)
                        (not (ffnnamesp names (fargn body 1))))
                   (mv merge-p (list (fargn body 2))))
                  ((and (eq (ffn-symb body) 'return-last)
                        (quotep (fargn body 1))
                        (eq (unquote (fargn body 1)) 'progn)
                        (not (ffnnamesp names (fargn body 2))))
                   (mv merge-p (list (fargn body 3))))
                  ((null (cdr (fargs body)))
                   (mv merge-p (list (fargn body 1))))
                  (t (mv t (fargs body))))
            (let* ((flg0 (member-eq (ffn-symb body) names))
                   (calls (if flg0
                              (cons (sublis-var alist body) calls)
                            calls)))
              (mv-let
               (flg temp)
               (induction-machine-for-fn1-lst names
                                              args
                                              alist
                                              ruler-extenders
                                              nil ; acc
                                              merge-p
                                              nil) ; flg
               (mv (or flg0 flg)
                   (cross-tests-and-calls
                    names
                    test-alist
                    calls
                    temp))))))))

(defun induction-machine-for-fn1-lst (names bodies alist ruler-extenders acc
                                            merge-p flg)

; The resulting list corresponds to bodies in reverse order.

  (cond ((endp bodies) (mv flg acc))
        (t (mv-let (flg1 ans1)
                   (induction-machine-for-fn1 names (car bodies) alist
                                              nil ; tests
                                              nil ; calls
                                              ruler-extenders
                                              merge-p)
                   (induction-machine-for-fn1-lst
                    names (cdr bodies) alist ruler-extenders
                    (cons ans1 acc)
                    merge-p
                    (or flg1 flg))))))
)

(defun simplify-tests-and-calls (tc)

; For an example of the utility of removing guard holders, note that lemma
; STEP2-PRESERVES-DL->NOT2 in community book
; books/workshops/2011/verbeek-schmaltz/sources/correctness.lisp has failed
; when we did not do so.

  (let* ((tests0 (remove-guard-holders-lst
                  (access tests-and-calls tc :tests))))
    (mv-let
     (var const)
     (term-equated-to-constant-in-termlist tests0)
     (let ((tests
            (cond (var (mv-let (changedp tests)
                               (simplify-tests var const tests0)
                               (declare (ignore changedp))
                               tests))
                  (t tests0))))

; Through Version_7.1 we returned nil when (null tests), with the comment:
; "contradictory case".  However, that caused a bad error when a caller
; expected a tests-and-calls record, as in the following example.

;   (skip-proofs (defun foo (x)
;                  (declare (xargs :measure (acl2-count x)))
;                  (identity
;                   (cond ((zp x) 17)
;                         (t (foo (1- x)))))))

; We now see no particular reason why special handling is necessary in this
; case.  Of course, the ultimate induction scheme may allow a proof of nil; for
; the example above, try (thm nil :hints (("Goal" :induct (foo x)))).  But
; everything we are doing here is presumably sound, so we expect a skip-proofs
; to be to blame for nil tests, as in the example above.

       (make tests-and-calls
             :tests tests
             :calls (remove-guard-holders-lst
                     (access tests-and-calls tc :calls)))))))

(defun simplify-tests-and-calls-lst (tc-list)

; We eliminate needless tests (not (equal term (quote const))) that clutter the
; induction machine.  To see this function in action:

; (skip-proofs (defun foo (x)
;                (if (consp x)
;                    (case (car x)
;                      (0 (foo (nth 0 x)))
;                      (1 (foo (nth 1 x)))
;                      (2 (foo (nth 2 x)))
;                      (3 (foo (nth 3 x)))
;                      (otherwise (foo (cdr x))))
;                  x)))

; (thm (equal (foo x) yyy))

  (cond ((endp tc-list)
         nil)
        (t (cons (simplify-tests-and-calls (car tc-list))
                 (simplify-tests-and-calls-lst (cdr tc-list))))))

(defun induction-machine-for-fn (names body ruler-extenders)

; We build an induction machine for the function in names with the given body.
; We claim the soundness of the induction schema suggested by this machine is
; easily seen from the proof done by prove-termination.  See
; termination-machine.

; Note: The induction machine built for a clique of more than 1
; mutually recursive functions is probably unusable.  We do not know
; how to do inductions on such functions now.

  (mv-let (flg ans)
          (induction-machine-for-fn1 names
                                     body
                                     nil ; alist
                                     nil ; tests
                                     nil ; calls
                                     ruler-extenders
                                     nil); merge-p
          (declare (ignore flg))
          (simplify-tests-and-calls-lst ans)))

(defun induction-machines (names bodies ruler-extenders-lst)

; This function builds the induction machine for each function defined
; in names with the corresponding body in bodies.  A list of machines
; is returned.  See termination-machine.

; Note: If names has more than one element we return nil because we do
; not know how to interpret the induction-machines that would be
; constructed from a non-trivial clique of mutually recursive
; functions.  As a matter of fact, as of this writing,
; induction-machine-for-fn constructs the "natural" machine for
; mutually recursive functions, but there's no point in consing them
; up since we can't use them.  So all that machinery is
; short-circuited here.

  (cond ((null (cdr names))
         (list (induction-machine-for-fn names (car bodies)
                                         (car ruler-extenders-lst))))
        (t nil)))

(defun putprop-induction-machine-lst (names bodies ruler-extenders-lst
                                            subversive-p wrld)

; Note:  If names has more than one element we do nothing.  We only
; know how to interpret induction machines for singly recursive fns.

  (cond ((cdr names) wrld)
        (subversive-p wrld)
        (t (putprop (car names)
                    'induction-machine
                    (car (induction-machines names bodies
                                             ruler-extenders-lst))
                    wrld))))

(defun quick-block-initial-settings (formals)
  (cond ((null formals) nil)
        (t (cons 'un-initialized
                 (quick-block-initial-settings (cdr formals))))))

(defun quick-block-info1 (var term)
  (cond ((eq var term) 'unchanging)
        ((dumb-occur var term) 'self-reflexive)
        (t 'questionable)))

(defun quick-block-info2 (setting info1)
  (case setting
        (questionable 'questionable)
        (un-initialized info1)
        (otherwise
         (cond ((eq setting info1) setting)
               (t 'questionable)))))

(defun quick-block-settings (settings formals args)
  (cond ((null settings) nil)
        (t (cons (quick-block-info2 (car settings)
                                    (quick-block-info1 (car formals)
                                                       (car args)))
                 (quick-block-settings (cdr settings)
                                       (cdr formals)
                                       (cdr args))))))

(defun quick-block-down-t-machine (name settings formals t-machine)
  (cond ((null t-machine) settings)
        ((not (eq name
                  (ffn-symb (access tests-and-call (car t-machine) :call))))
         (er hard 'quick-block-down-t-machine
             "When you add induction on mutually recursive functions don't ~
              forget about QUICK-BLOCK-INFO!"))
        (t (quick-block-down-t-machine
            name
            (quick-block-settings
             settings
             formals
             (fargs (access tests-and-call (car t-machine) :call)))
            formals
            (cdr t-machine)))))

(defun quick-block-info (name formals t-machine)

; This function should be called a singly recursive function, name, and
; its termination machine.  It should not be called on a function
; in a non-trivial mutually recursive clique because the we don't know
; how to analyze a call to a function other than name in the t-machine.

; We return a list in 1:1 correspondence with the formals of name.
; Each element of the list is either 'unchanging, 'self-reflexive,
; or 'questionable.  The list is used to help quickly decide if a
; blocked formal can be tolerated in induction.

  (quick-block-down-t-machine name
                              (quick-block-initial-settings formals)
                              formals
                              t-machine))


(defun putprop-quick-block-info-lst (names t-machines wrld)

; We do not know how to compute quick-block-info for non-trivial
; mutually-recursive cliques.  We therefore don't do anything for
; those functions.  If names is a list of length 1, we do the
; computation.  We assume we can find the formals of the name in wrld.

  (cond ((null (cdr names))
         (putprop (car names)
                  'quick-block-info
                  (quick-block-info (car names)
                                    (formals (car names) wrld)
                                    (car t-machines))
                  wrld))
        (t wrld)))

(defmacro big-mutrec (names)

; All mutual recursion nests with more than the indicated number of defuns will
; be processed by installing intermediate worlds, for improved performance.  We
; have seen an improvement of roughly two orders of magnitude in such a case.
; The value below is merely heuristic, chosen with very little testing; we
; should feel free to change it.

  `(> (length ,names) 20))

(defun get-sig-fns1 (ee-lst)
  (cond ((endp ee-lst)
         nil)
        (t (let ((ee-entry (car ee-lst)))
             (cond ((and (eq (car ee-entry) 'encapsulate)
                         (cddr ee-entry)) ; pass-2
                    (append (get-sig-fns1 (cdr ee-lst)) ; usually nil
                            (strip-cars (cadr ee-entry))))
                   (t
                    (get-sig-fns1 (cdr ee-lst))))))))

(defun get-sig-fns (wrld)
  (get-sig-fns1 (global-val 'embedded-event-lst wrld)))

(defun selected-all-fnnames-lst (formals subset actuals acc)
  (cond ((endp formals) acc)
        (t (selected-all-fnnames-lst
            (cdr formals) subset (cdr actuals)
            (if (member-eq (car formals) subset)
                (all-fnnames1 nil (car actuals) acc)
              acc)))))

(defun subversivep (fns t-machine formals-and-subset-alist wrld)

; See subversive-cliquep for conditions (1) and (2).

  (cond ((endp t-machine) nil)
        (t (or
; Condition (1):
            (intersectp-eq fns
                           (instantiable-ancestors
                            (all-fnnames-lst (access tests-and-call
                                                     (car t-machine)
                                                     :tests))
                            wrld
                            nil))
; Condition (2):
            (let* ((call (access tests-and-call
                                 (car t-machine)
                                 :call))
                   (entry
                    (assoc-eq (ffn-symb call)
                              formals-and-subset-alist))
                   (formals (assert$ entry (cadr entry)))
                   (subset (cddr entry))
                   (measured-call-args-ancestors
                    (instantiable-ancestors
                     (selected-all-fnnames-lst formals subset
                                               (fargs call) nil)
                     wrld
                     nil)))
              (intersectp-eq fns measured-call-args-ancestors))
; Recur:
            (subversivep fns (cdr t-machine) formals-and-subset-alist wrld)))))

(defun subversive-cliquep (fns t-machines formals-and-subset-alist wrld)

; Here, fns is a list of functions introduced in an encapsulate.  If we are
; using the [Front] rule (from the Structured Theory paper) to move some
; functions forward, then fns is the list of ones that are NOT moved: they all
; use the signature functions somehow.  T-machines is a list of termination
; machines for some clique of functions defined within the encapsulate.  The
; clique is subversive if some function defined in the clique has a subversive
; t-machine.

; Intuitively, a t-machine is subversive if its admission depended on
; properties of the witnesses for signature functions.  That is, the definition
; uses signature functions in a way that affects the termination argument.

; Technically a t-machine is subversive if some tests-and-call record in it has
; either of the following properties:

; (1) a test mentions a function in fns

; (2) an argument of a call in a measured position mentions a function in fns.

; Observe that if a clique is not subversive then every test and argument to
; every recursive call uses functions defined outside the encapsulate.  If we
; are in a top-level encapsulate, then a non-subversive clique is a ``tight''
; clique wrt the set S of functions in the initial world of the encapsulate,
; where ``tight'' is defined by the Structured Theory paper, i.e.: for every
; subterm u of a ruler or recursive call in the clique, all function symbols of
; u belong to S (but now we restrict to measured positions in recursive
; calls).

  (cond ((endp t-machines) nil)
        (t (or (subversivep fns (car t-machines) formals-and-subset-alist wrld)
               (subversive-cliquep fns (cdr t-machines)
                                   formals-and-subset-alist wrld)))))

(defun prove-termination-non-recursive (names bodies mp rel hints otf-flg
                                              big-mutrec ctx ens wrld state)

; This function separates out code from put-induction-info.

  (er-progn
   (cond
    (hints
     (let ((bogus-defun-hints-ok
            (cdr (assoc-eq :bogus-defun-hints-ok
                           (table-alist 'acl2-defaults-table
                                        (w state))))))
       (cond
        ((eq bogus-defun-hints-ok :warn)
         (pprogn
          (warning$ ctx "Non-rec"
                    "Since ~x0 is non-recursive your supplied :hints will be ~
                     ignored (as these are used only during termination ~
                     proofs).  Perhaps either you meant to supply ~
                     :guard-hints or the body of the definition is incorrect."
                    (car names))
          (value nil)))
        (bogus-defun-hints-ok ; t
         (value nil))
        (t ; bogus-defun-hints-ok = nil, the default
         (er soft ctx
             "Since ~x0 is non-recursive it is odd that you have supplied ~
              :hints (which are used only during termination proofs).  We ~
              suspect something is amiss, e.g., you meant to supply ~
              :guard-hints or the body of the definition is incorrect.  To ~
              avoid this error, see :DOC set-bogus-defun-hints-ok."
             (car names))))))
    (t (value nil)))
   (er-let*
    ((wrld1 (update-w big-mutrec wrld))
     (pair (prove-termination names nil nil mp rel nil otf-flg bodies nil
                              ctx ens wrld1 state nil)))

; We know that pair is of the form (col . ttree), where col is the column
; the output state is in.

    (value (list (car pair)
                 wrld1
                 (cdr pair))))))

(defun prove-termination-recursive (names arglists measures t-machines
                                          mp rel hints otf-flg bodies
                                          measure-debug
                                          ctx ens wrld state)

; This function separates out code from put-induction-info.

; First we get the measures for each function.  That may cause an error if we
; couldn't guess one for some function.

  (er-let* ((measure-alist (guess-measure-alist names arglists
                                                measures
                                                t-machines
                                                ctx wrld state))
            (hints (if hints ; hints and default-hints already translated
                       (value hints)
                     (let ((default-hints (default-hints wrld)))
                       (if default-hints ; not yet translated
                           (translate-hints
                            (cons "Measure Lemma for" (car names))
                            default-hints ctx wrld state)
                         (value hints)))))
            (pair (prove-termination names
                                     t-machines
                                     measure-alist
                                     mp
                                     rel
                                     hints
                                     otf-flg
                                     bodies
                                     measure-debug
                                     ctx
                                     ens
                                     wrld
                                     state
                                     nil)))

; Ok, we have managed to prove termination!  Pair is a pair of the form (col .
; ttree), where col tells us what column the printer is in and ttree describes
; the proofs done.

    (value (list* (car pair) measure-alist (cdr pair)))))

(defun put-induction-info-recursive (names arglists col ttree measure-alist
                                           t-machines ruler-extenders-lst
                                           bodies mp rel wrld state)

; This function separates out code from put-induction-info.

; We have proved termination.  Col tells us what column the printer is in and
; ttree describes the proofs done.  We now store the 'justification of each
; function, the induction machine for each function, and the quick-block-info.

  (let* ((subset-lst

; Below, we rely on the fact that this subset-lst corresponds, in order, to
; names.  See the warnings comment in guess-measure-alist.

          (collect-all-vars (strip-cdrs measure-alist)))
         (sig-fns (get-sig-fns wrld))
         (subversive-p (and sig-fns
                            (subversive-cliquep
                             sig-fns
                             t-machines
                             (pairlis$ names
                                       (pairlis$ arglists
                                                 subset-lst))
                             wrld)))
         (wrld2
          (putprop-induction-machine-lst
           names bodies ruler-extenders-lst subversive-p wrld))
         (wrld3
          (putprop-justification-lst measure-alist
                                     subset-lst
                                     mp rel
                                     ruler-extenders-lst
                                     subversive-p wrld2))
         (wrld4 (putprop-quick-block-info-lst names
                                              t-machines
                                              wrld3)))

; We are done.  We will return the final wrld and the ttree describing
; the proofs we did.

    (value
     (list* col
            wrld4
            (push-lemma
             (cddr (assoc-eq rel
                             (global-val
                              'well-founded-relation-alist
                              wrld4)))
             ttree)
            subversive-p))))

(defun maybe-warn-or-error-on-non-rec-measure (name ctx wrld state)

  (let ((bogus-defun-hints-ok
         (cdr (assoc-eq :bogus-defun-hints-ok
                        (table-alist 'acl2-defaults-table wrld)))))
    (cond
     ((eq bogus-defun-hints-ok :warn)
      (pprogn
       (warning$ ctx "Non-rec"
                 "Since ~x0 is non-recursive your supplied :measure will be ~
                  ignored (as the :measure is used only during termination ~
                  proofs)."
                 name)
       (value nil)))
     (bogus-defun-hints-ok ; t
      (value nil))
     (t ; bogus-defun-hints-ok = nil, the default
      (er soft ctx
          "It is illegal to supply a measure for a non-recursive function, as ~
           has been done for ~x0.  To avoid this error, see :DOC ~
           set-bogus-measure-ok."
          name)))))

(defun put-induction-info (names arglists measures ruler-extenders-lst bodies
                                 mp rel hints otf-flg big-mutrec measure-debug
                                 ctx ens wrld state)

; WARNING: This function installs a world.  That is safe at the time of this
; writing because this function is only called by defuns-fn0, which is only
; called by defuns-fn, where that call is protected by a revert-world-on-error.

; We are processing a clique of mutually recursive functions with the names,
; arglists, measures, ruler-extenders-lst, and bodies given.  All of the above
; lists are in 1:1 correspondence.  The hints is the result of appending
; together all of the hints provided.  Mp and rel are the domain predicate and
; well-founded relation to be used.  We attempt to prove the admissibility of
; the recursions.  We cause an error if any proof fails.  We put a lot of
; properties under the function symbols, namely:

;    recursivep                     all fns in names
;    justification                  all recursive fns in names
;    induction-machine              the singly recursive fn in name*
;    quick-block-info               the singly recursive fn in name*
;    symbol-class :ideal            all fns in names

; *If names consists of exactly one recursive fn, we store its
; induction-machine and its quick-block-info, otherwise we do not.

; If no error occurs, we return a triple consisting of the column the printer
; is in, the final value of wrld and a tag-tree documenting the proofs we did.

; Note: The function could be declared to return 5 values, but we would rather
; use the standard state and error primitives and so it returns 3 and lists
; together the three "real" answers.

  (let ((wrld1 (putprop-recursivep-lst names bodies wrld)))

; The put above stores a note on each function symbol as to whether it is
; recursive or not.  An important question arises: have we inadvertently
; assumed something axiomatically about inadmissible functions?  We say no.
; None of the functions in question have bodies yet, so the simplifier doesn't
; care about properties such as 'recursivep.  However, we make use of this
; property below to decide if we need to prove termination.

    (cond ((and (null (cdr names))
                (null (getpropc (car names) 'recursivep nil wrld1)))

; If only one function is being defined and it is non-recursive, we can quit.
; But we have to store the symbol-class and we have to print out the admission
; message with prove-termination so the rest of our processing is uniform.

           (er-progn
            (cond ((equal (car measures) *no-measure*)
                   (value nil))
                  (t (maybe-warn-or-error-on-non-rec-measure (car names) ctx
                                                             wrld state)))
            (prove-termination-non-recursive names bodies mp rel hints otf-flg
                                             big-mutrec ctx ens wrld1 state)))
          (t

; Otherwise we first construct the termination machines for all the
; functions in the clique.

           (let ((t-machines
                  (termination-machines names bodies ruler-extenders-lst)))

; Next we get the measures for each function.  That may cause an error
; if we couldn't guess one for some function.

             (er-let*
              ((wrld1 (update-w

; Sol Swords sent an example in which a clause-processor failed during a
; termination proof.  That problem goes away if we install the world, which we
; do by making the following binding.  This seems particularly important now
; that raw-ev-fncall calls chk-raw-ev-fncall to ensure that the world is
; (essentially) installed.

                       t ; formerly big-mutrec
                       wrld1))
               (triple (prove-termination-recursive
                        names arglists measures t-machines mp rel hints
                        otf-flg bodies measure-debug ctx ens wrld1 state)))
              (let* ((col (car triple))
                     (measure-alist (cadr triple))
                     (ttree (cddr triple)))
                (put-induction-info-recursive
                 names arglists col ttree measure-alist t-machines
                 ruler-extenders-lst bodies mp rel wrld1 state))))))))

; We next worry about storing the normalized bodies.

(defun destructure-definition (term install-body ens wrld ttree)

; Term is a translated term that is the :corollary of a :definition rule.  If
; install-body is non-nil then we intend to update the 'def-bodies
; property; and if moreover, install-body is :normalize, then we want to
; normalize the resulting new body.  Ens is an enabled structure if
; install-body is :normalize; otherwise ens is ignored.

; We return (mv hyps equiv fn args body new-body ttree) or else nils if we fail
; to recognize the form of term.  Hyps results flattening the hypothesis of
; term, when a call of implies, into a list of hypotheses.  Failure can be
; detected by checking for (null fn) since nil is not a legal fn symbol.

  (mv-let
   (hyps equiv fn-args body)
   (case-match term
     (('implies hyp (equiv fn-args body))
      (mv (flatten-ands-in-lit hyp)
          equiv
          fn-args
          body))
     ((equiv fn-args body)
      (mv nil
          equiv
          fn-args
          body))
     (& (mv nil nil nil nil)))
   (let ((equiv (if (member-eq equiv *equality-aliases*)
                    'equal
                  equiv))
         (fn (and (consp fn-args) (car fn-args))))
     (cond
      ((and fn
            (symbolp fn)
            (not (member-eq fn

; Hide is disallowed in chk-acceptable-definition-rule.

                            '(quote if)))
            (equivalence-relationp equiv wrld))
       (mv-let (body ttree)
               (cond ((eq install-body :NORMALIZE)
                      (normalize (remove-guard-holders body)
                                 nil ; iff-flg
                                 nil ; type-alist
                                 ens
                                 wrld
                                 ttree
                                 (normalize-ts-backchain-limit-for-defs wrld)))
                     (t (mv body ttree)))
               (mv hyps
                   equiv
                   fn
                   (cdr fn-args)
                   body
                   ttree)))
      (t (mv nil nil nil nil nil nil))))))

(defun member-rewrite-rule-rune (rune lst)

; Lst is a list of :rewrite rules.  We determine whether there is a
; rule in lst with the :rune rune.

  (cond ((null lst) nil)
        ((equal rune (access rewrite-rule (car lst) :rune)) t)
        (t (member-rewrite-rule-rune rune (cdr lst)))))

(defun replace-rewrite-rule-rune (rune rule lst)

; Lst is a list of :rewrite rules and one with :rune rune is among them.
; We replace that rule with rule.

  (cond ((null lst) nil)
        ((equal rune (access rewrite-rule (car lst) :rune))
         (cons rule (cdr lst)))
        (t (cons (car lst) (replace-rewrite-rule-rune rune rule (cdr lst))))))

; We massage the hyps with this function to speed rewrite up.

(defun preprocess-hyp (hyp)

; In nqthm, this function also replaced (not (zerop x)) by
; ((numberp x) (not (equal x '0))).

; Lemma replace-consts-cp-correct1 in community book
; books/clause-processors/replace-defined-consts.lisp failed after we added
; calls of mv-list to the macroexpansion of mv-let calls in Version_4.0, which
; allowed lemma replace-const-corr-replace-const-alists-list to be applied:
; there was a free variable in the hypothesis that had no longer been matched
; when mv-list was introduced.  So we have decided to add the calls of
; remove-guard-holders below to take care of such issues.

  (case-match hyp
    (('atom x)
     (list (mcons-term* 'not (mcons-term* 'consp
                                          (remove-guard-holders x)))))
    (& (list (remove-guard-holders hyp)))))

(defun preprocess-hyps (hyps)
  (cond ((null hyps) nil)
        (t (append (preprocess-hyp (car hyps))
                   (preprocess-hyps (cdr hyps))))))

(defun add-definition-rule-with-ttree (rune nume clique controller-alist
                                            install-body term ens wrld ttree)

; We make a :rewrite rule of subtype 'definition (or 'abbreviation)
; and add it to the 'lemmas property of the appropriate fn.  This
; function is defined the way it is (namely, taking term as an arg and
; destructuring it rather than just taking term in pieces) because it
; is also used as the function for adding a user-supplied :REWRITE
; rule of subclass :DEFINITION.

  (mv-let
    (hyps equiv fn args body ttree)
    (destructure-definition term install-body ens wrld ttree)
    (let* ((vars-bag (all-vars-bag-lst args nil))
           (abbreviationp (and (null hyps)
                               (null clique)

; Rockwell Addition:  We have changed the notion of when a rule is an
; abbreviation.  Our new concern is with stobjs and lambdas.

; If fn returns a stobj, we don't consider it an abbreviation unless
; it contains no lambdas.  Thus, the updaters are abbreviations but
; lambda-nests built out of them are not.  We once tried the idea of
; letting a lambda in a function body disqualify the function as an
; abbreviation, but that made FLOOR no longer an abbreviation and some
; of the fp proofs failed.  So we made the question depend on stobjs
; for compatibility's sake.

                               (abbreviationp
                                (not (all-nils

; We call getprop rather than calling stobjs-out, because this code may run
; with fn = return-last, and the function stobjs-out causes an error in that
; case.  We don't mind treating return-last as an ordinary function here.

                                      (getpropc fn 'stobjs-out '(nil) wrld)))
                                vars-bag
                                body)))
           (rule
            (make rewrite-rule
                  :rune rune
                  :nume nume
                  :hyps (preprocess-hyps hyps)
                  :equiv equiv
                  :lhs (mcons-term fn args)
                  :var-info (cond (abbreviationp (not (null vars-bag)))
                                  (t (var-counts args body)))
                  :rhs body
                  :subclass (cond (abbreviationp 'abbreviation)
                                  (t 'definition))
                  :heuristic-info
                  (cond (abbreviationp nil)
                        (t (cons clique controller-alist)))

; Backchain-limit-lst does not make much sense for definitions.

                  :backchain-limit-lst nil)))
      (let ((wrld0 (if (eq fn 'hide)
                       wrld
                     (putprop fn 'lemmas
                              (cons rule (getpropc fn 'lemmas nil wrld))
                              wrld))))
        (cond (install-body
               (mv (putprop fn
                            'def-bodies
                            (cons (make def-body
                                        :nume nume
                                        :hyp (and hyps (conjoin hyps))
                                        :concl body
                                        :equiv equiv
                                        :rune rune
                                        :formals args
                                        :recursivep clique
                                        :controller-alist controller-alist)
                                  (getpropc fn 'def-bodies nil wrld))
                            wrld0)
                   ttree))
              (t (mv wrld0 ttree)))))))

(defun add-definition-rule (rune nume clique controller-alist install-body term
                                 ens wrld)
  (mv-let (wrld ttree)
          (add-definition-rule-with-ttree rune nume clique controller-alist
                                          install-body term ens wrld nil)
          (declare (ignore ttree))
          wrld))

#+:non-standard-analysis
(defun listof-standardp-macro (lst)

; If the guard for standardp is changed from t, consider changing
; the corresponding calls of mcons-term* to fcons-term*.

  (if (consp lst)
      (if (consp (cdr lst))
          (mcons-term*
           'if
           (mcons-term* 'standardp (car lst))
           (listof-standardp-macro (cdr lst))
           *nil*)
        (mcons-term* 'standardp (car lst)))
    *t*))

(defun putprop-body-lst (names arglists bodies normalizeps
                               clique controller-alist
                               #+:non-standard-analysis std-p
                               ens wrld installed-wrld ttree)

; Rockwell Addition:  A major change is the handling of PROG2$ and THE
; below.

; We store the body property for each name in names.  It is set to the
; normalized body.  Normalization expands some nonrecursive functions, namely
; those on *expandable-boot-strap-non-rec-fns*, which includes old favorites
; like EQ and ATOM.  In addition, we eliminate all the RETURN-LASTs and THEs
; from the body.  This can be seen as just an optimization of expanding nonrec
; fns.

; We add a definition rule equating the call of name with its normalized body.

; We store the unnormalized body under the property 'unnormalized-body.

; We return two results: the final wrld and a ttree justifying the
; normalization, which is an extension of the input ttree.

; Essay on the Normalization of Bodies

; We normalize the bodies of functions to speed up type-set and rewriting.  But
; there are some subtle issues here.  Let term be a term and let term' be its
; normalization.  We will ignore iff-flg and type-alist here.  First, we claim
; that term and term' are equivalent.  Thus, if we are allowed to add the axiom
; (fn x) = term then we may add (fn x) = term' too.  But while term and term'
; are equivalent they are not interchangeable from the perspective of defun
; processing.  For example, as nqthm taught us, the measure conjectures
; generated from term' may be inadequate to justify the admission of a function
; whose body is term.  A classic example is (fn x) = (if (fn x) t t), where the
; normalized body is just t.  The Historical Plaque below contains a proof that
; if (fn x) = term' is admissible then there exists one and only one function
; satisfying (fn x) = term.  Thus, while the latter definition may not actually
; be admissible it at least will not get us into trouble and in the end the
; issue vis-a-vis admissibility seems to be the technical one of exactly how we
; wish to define the Principle of Definition.

; Historical Plaque from Nqthm

; The following extensive comment used to guard the definition of
; DEFN0 in nqthm and is placed here partly as a nostalgic reminder of
; decades of work and partly because it has some good statistics in it
; that we might still want to look at.

;   This function is FUNCALLed and therefore may not be made a MACRO.

;   The list of comments on this function do not necessarily describe
;   the code below.  They have been left around in reverse chronology
;   order to remind us of the various combinations of preprocessing
;   we have tried.

;   If we ever get blown out of the water while normalizing IFs in a
;   large defn, read the following comment before abandoning
;   normalization.

;   18 August 1982.  Here we go again!  At the time of this writing
;   the preprocessing of defns is as follows, we compute the
;   induction and type info on the translated body and store under
;   sdefn the translated body.  This seems to slow down the system a
;   lot and we are going to change it so that we store under sdefn
;   the result of expanding boot strap nonrec fns and normalizing
;   IFs.  As nearly as we can tell from the comments below, we have
;   not previously tried this.  According to the record, we have
;   tried expanding all nonrec fns, and we have tried expanding boot
;   strap fns and doing a little normalization.  The data that
;   suggests this will speed things up is as follows.  Consider the
;   first call of SIMPLIFY-CLAUSE in the proof of PRIME-LIST-TIMES
;   -LIST.  The first three literals are trivial but the fourth call
;   of SIMPLIFY-CLAUSE1 is on (NOT (PRIME1 C (SUB1 C))).  With SDEFNs
;   not expanded and normalized -- i.e., under the processing as it
;   was immediately before the current change -- there are 2478 calls
;   of REWRITE and 273 calls of RELIEVE-HYPS for this literal.  With
;   all defns preprocessed as described here those counts drop to
;   1218 and 174.  On a sample of four theorems, PRIME-LIST-TIMES-
;   LIST, PRIME-LIST-PRIME-FACTORS, FALSIFY1-FALSIFIES, and ORDERED-
;   SORT, the use of normalized and expanded sdefns saves us 16
;   percent of the conses over the use of untouched sdefns, reducing
;   the cons counts for those theorems from 880K to 745K.  It seems
;   unlikely that this preprocessing will blow us out of the water on
;   large defns.  For the EV used in UNSOLV and for the 386L M with
;   subroutine call this new preprocessing only marginally increases
;   the size of the sdefn.  It would be interesting to see a function
;   that blows us out of the water.  When one is found perhaps the
;   right thing to do is to so preprocess small defns and leave big
;   ones alone.

;   17 December 1981.  Henceforth we will assume that the very body
;   the user supplies (modulo translation) is the body that the
;   theorem-prover uses to establish that there is one and only one
;   function satisfying the definition equation by determining that
;   the given body provides a method for computing just that
;   function.  This prohibits our "improving" the body of definitions
;   such as (f x) = (if (f x) a a) to (f x) = a.

;   18 November 1981.  We are sick of having to disable nonrec fns in
;   order to get large fns processed, e.g., the interpreter for our
;   386L class.  Thus, we have decided to adopt the policy of not
;   touching the user's typein except to TRANSLATE! it.  The
;   induction and type analysis as well as the final SDEFN are based
;   on the translated typein.

;   Before settling with the preprocessing used below we tried
;   several different combinations and did provealls.  The main issue
;   was whether we should normalize sdefns.  Unfortunately, the
;   incorporation of META0-LEMMAS was also being experimented with,
;   and so we do not have a precise breakdown of who is responsible
;   for what.  However, below we give the total stats for three
;   separate provealls.  The first, called 1PROVEALL, contained
;   exactly the code below -- except that the ADD-DCELL was given the
;   SDEFN with all the fn names replaced by *1*Fns instead of a fancy
;   TRANSLATE-TO-INTERLISP call.  Here are the 1PROVEALL stats.
;   Elapsed time = 9532.957, CPU time = 4513.88, GC time = 1423.261,
;   IO time = 499.894, CONSes consumed = 6331517.

;   We then incorporated META0-LEMMAS.  Simultaneously, we tried
;   running the RUN fns through DEFN and found that we exploded.  The
;   expansion of nonrec fns and the normalization of IFs before the
;   induction analysis transformed functions of CONS-COUNT 300 to
;   functions of CONS-COUNT exceeding 18K.  We therefore decided to
;   expand only BOOT-STRAP fns -- and not NORMALIZE-IFS for the
;   purposes of induction analysis.  After the induction and type
;   analyses were done, we put down an SDEFN with some trivial IF
;   simplification performed -- e.g., IF X Y Y => Y and IF bool T F
;   => bool -- but not a NORMALIZE-IFs version.  We then ran a
;   proveall with CANCEL around as a META0-LEMMA.  The result was
;   about 20 percent slower than the 1PROVEALL and used 15 percent
;   more CONSes.  At first this was attributed to CANCEL.  However,
;   we then ran two simultaneous provealls, one with META0-LEMMAS set
;   to NIL and one with it set to ((1CANCEL . CORRECTNESS-OF-CANCEL)).
;   The result was that the version with CANCEL available used
;   slightly fewer CONSes than the other one -- 7303311 to 7312505
;   That was surprising because the implementation of META0-LEMMAS
;   uses no CONSes if no META0-LEMMAS are available, so the entire 15
;   percent more CONSes had to be attributed to the difference in the
;   defn processing.  This simultaneous run was interesting for two
;   other reasons.  The times -- while still 20 percent worse than
;   1PROVEALL -- were one half of one percent different, with CANCEL
;   being the slower.  That means having CANCEL around does not cost
;   much at all -- and the figures are significant despite the slop
;   in the operating system's timing due to thrashing because the two
;   jobs really were running simultaneously.  The second interesting
;   fact is that CANCEL can be expected to save us a few CONSes
;   rather than cost us.

;   We therefore decided to return the DEFN0 processing to its
;   original state.  Only we did it in two steps.  First, we put
;   NORMALIZE-IFs into the pre-induction processing and into the
;   final SDEFN processing.  Here are the stats on the resulting
;   proveall, which was called PROVEALL-WITH-NORM-AND-CANCEL but not
;   saved.  Elapsed time = 14594.01, CPU time = 5024.387, GC time =
;   1519.932, IO time = 593.625, CONSes consumed = 6762620.

;   While an improvement, we were still 6 percent worse than
;   1PROVEALL on CONSes.  But the only difference between 1PROVEALL
;   and PROVEALL-WITH-NORM-AND-CANCEL -- if you discount CANCEL which
;   we rightly believed was paying for itself -- was that in the
;   former induction analyses and type prescriptions were being
;   computed from fully expanded bodies while in the latter they were
;   computed from only BOOT-STRAP-expanded bodies.  We did not
;   believe that would make a difference of over 400,000 CONSes, but
;   had nothing else to believe.  So we went to the current state,
;   where we do the induction and type analyses on the fully expanded
;   and normalized bodies -- bodies that blow us out of the water on
;   some of the RUN fns.  Here are the stats for
;   PROVEALL-PROOFS.79101, which was the proveall for that version.
;   Elapsed time = 21589.84, CPU time = 4870.231, GC time = 1512.813,
;   IO time = 554.292, CONSes consumed= 6356282.

;   Note that we are within 25K of the number of CONSes used by
;   1PROVEALL.  But to TRANSLATE-TO-INTERLISP all of the defns in
;   question costs 45K.  So -- as expected -- CANCEL actually saved
;   us a few CONSes by shortening proofs.  It takes only 18 seconds
;   to TRANSLATE-TO-INTERLISP the defns, so a similar argument does
;   not explain why the latter proveall is 360 seconds slower than
;   1PROVEALL.  But since the elapsed time is over twice as long, we
;   believe it is fair to chalk that time up to the usual slop
;   involved in measuring cpu time on a time sharing system.

;   We now explain the formal justification of the processing we do
;   on the body before testing it for admissibility.

;   We do not work with the body that is typed in by the user but
;   with an equivalent body' produced by normalization and the
;   expansion of nonrecursive function calls in body.  We now prove
;   that if (under no assumptions about NAME except that it is a
;   function symbol of the correct arity) (a) body is equivalent to
;   body' and (b) (name . args) = body' is accepted under our
;   principle of definition, then there exists exactly one function
;   satisfying the original equation (name . args) = body.

;   First observe that since the definition (name . args) = body' is
;   accepted by our principle of definition, there exists a function
;   satisfying that equation.  But the accepted equation is
;   equivalent to the equation (name .  args) = body by the
;   hypothesis that body is equivalent to body'.

;   We prove that there is only one such function by induction.
;   Assume that the definition (name . args) = body has been accepted
;   under the principle of definition.  Suppose that f is a new name
;   and that (f . args) = bodyf, where bodyf results from replacing
;   every use of name as a function symbol in body with f.  It
;   follows that (f . args) = bodyf', where bodyf' results from
;   replacing every use of name as a function symbol in body' with f.
;   We can now easily prove that (f . args) = (name . args) by
;   induction according to the definition of name. Q.E.D.

;   One might be tempted to think that if the defn with body' is
;   accepted under the principle of definition then so would be the
;   defn with body and that the use of body' was merely to make the
;   implementation of the defn principle more powerful.  This is not
;   the case.  For example

;        (R X) = (IF (R X) T T)

;   is not accepted by the definitional principle, but we would
;   accept the body'-version (R X) = T, and by our proof, that
;   function uniquely satisfies the equation the user typed in.

;   One might be further tempted to think that if we changed
;   normalize so that (IF X Y Y) = Y was not applied, then the two
;   versions were inter-acceptable under the defn principle.  This is
;   not the case either.  The function

;        (F X) = (IF (IF (X.ne.0) (F X-1) F) (F X-1) T)

;   is not accepted under the principle of defn.  Consider its
;   normalized body.

  (cond ((null names) (mv wrld ttree))
        (t (let* ((fn (car names))
                  (args (car arglists))
                  (body (car bodies))
                  (normalizep (car normalizeps))
                  (rune (fn-rune-nume fn nil nil installed-wrld))
                  (nume (fn-rune-nume fn t nil installed-wrld)))
             (let* ((eqterm (fcons-term* 'equal
                                         (fcons-term fn args)
                                         body))
                    (term #+:non-standard-analysis
                          (if (and std-p (consp args))
                              (fcons-term*
                               'implies
                               (listof-standardp-macro args)
                               eqterm)
                            eqterm)
                          #-:non-standard-analysis
                          eqterm)
                    #+:non-standard-analysis
                    (wrld (if std-p
                              (putprop fn 'constrainedp t
                                       (putprop fn 'constraint-lst (list term) wrld))
                            wrld)))
                (mv-let
                 (wrld ttree)
                 (add-definition-rule-with-ttree
                  rune nume clique controller-alist
                  (if normalizep :NORMALIZE t) ; install-body
                  term ens
                  (putprop fn
                           'unnormalized-body
                           body
                           wrld)
                  ttree)
                (putprop-body-lst (cdr names)
                                  (cdr arglists)
                                  (cdr bodies)
                                  (cdr normalizeps)
                                  clique controller-alist
                                  #+:non-standard-analysis std-p
                                  ens
                                  wrld installed-wrld ttree)))))))

; We now develop the facility for guessing the type-prescription of a defuned
; function.  When guards were part of the logic, the first step was to guess
; the types implied by the guard.  We no longer have to do that, but the
; utility written for it is used elsewhere and so we keep it here.

; Suppose you are trying to determine the type implied by term for some
; variable x.  The key trick is to normalize the term and replace every true
; output by x and every nil output by a term with an empty type-set.  Then take
; the type of that term.  For example, if term is (if (if p q) r nil) then it
; normalizes to (if p (if q (if r t nil) nil) nil) and so produces the
; intermediate term (if p (if q (if r x e ) e ) e ), where x is the formal in
; whose type we are interested and e is a new variable assumed to be of empty
; type.

(defun type-set-implied-by-term1 (term tvar fvar)

; Term is a normalized propositional term.  Tvar and fvar are two variable
; symbols.  We return a normalized term equivalent to (if term tvar fvar)
; except we drive tvar and fvar as deeply into term as possible.

  (cond ((variablep term)
         (fcons-term* 'if term tvar fvar))
        ((fquotep term)
         (if (equal term *nil*) fvar tvar))
        ((eq (ffn-symb term) 'if)
         (fcons-term* 'if
                      (fargn term 1)
                      (type-set-implied-by-term1 (fargn term 2) tvar fvar)
                      (type-set-implied-by-term1 (fargn term 3) tvar fvar)))
        (t

; We handle all non-IF applications here, even lambda applications.
; Once upon a time we considered driving into the body of a lambda.
; But that introduces a free var in the body, namely fvar (or whatever
; the new variable symbol is) and there are no guarantees that type-set
; works on such a non-term.

           (fcons-term* 'if term tvar fvar))))

(defun type-set-implied-by-term (var not-flg term ens wrld ttree)

; Given a variable and a term, we determine a type set for the
; variable under the assumption that the term is non-nil.  If not-flg
; is t, we negate term before using it.  This function is not used in
; the guard processing but is needed in the compound-recognizer work.

; The ttree returned is 'assumption-free (provided the initial ttree
; is also).

  (let* ((new-var (genvar 'genvar "EMPTY" nil (all-vars term)))
         (type-alist (list (list* new-var *ts-empty* nil))))
    (mv-let (normal-term ttree)
            (normalize term t nil ens wrld ttree
                       (backchain-limit wrld :ts))
            (type-set
             (type-set-implied-by-term1 normal-term
                                        (if not-flg new-var var)
                                        (if not-flg var new-var))
             nil nil type-alist ens wrld ttree nil nil))))

(defun putprop-initial-type-prescriptions (names wrld)

; Suppose we have a clique of mutually recursive fns, names.  Suppose
; that we can recover from wrld both the formals and body of each
; name in names.

; This function adds to the front of each 'type-prescriptions property
; of the names in names an initial, empty guess at its
; type-prescription.  These initial rules are unsound and are only the
; starting point of our iterative guessing mechanism.  Oddly, the
; :rune and :nume of each rule is the same!  We use the
; *fake-rune-for-anonymous-enabled-rule* for the rune and the nume
; nil.  We could create the proper runes and numes (indeed, we did at
; one time) but those runes then find their way into the ttrees of the
; various guesses (and not just the rune of the function being typed
; but also the runes of its clique-mates).  By adopting this fake
; rune, we prevent that.

; The :term and :hyps we create for each rule are appropriate and survive into
; the final, accurate guess.  But the :basic-ts and :vars fields are initially
; empty here and are filled out by the iteration.

  (cond
   ((null names) wrld)
   (t (let ((fn (car names)))
        (putprop-initial-type-prescriptions
         (cdr names)
         (putprop fn
                  'type-prescriptions
                  (cons (make type-prescription
                              :rune *fake-rune-for-anonymous-enabled-rule*
                              :nume nil
                              :term (mcons-term fn (formals fn wrld))
                              :hyps nil
                              :backchain-limit-lst nil
                              :basic-ts *ts-empty*
                              :vars nil
                              :corollary *t*)
                        (getpropc fn 'type-prescriptions nil wrld))
                  wrld))))))

; We now turn to the problem of iteratively guessing new
; type-prescriptions.  The root of this guessing process is the
; computation of the type-set and formals returned by a term.

(defun map-returned-formals-via-formals (formals pockets returned-formals)

; Formals is the formals list of a lambda expression, (lambda formals
; body).  Pockets is a list in 1:1 correspondence with formals.  Each
; pocket in pockets is a set of vars.  Finally, returned-formals is a
; subset of formals.  We return the set of vars obtained by unioning
; together the vars in those pockets corresponding to those in
; returned-formals.

; This odd little function is used to help determine the returned
; formals of a function defined in terms of a lambda-expression.
; Suppose foo is defined in terms of ((lambda formals body) arg1 ...
; argn) and we wish to determine the returned formals of that
; expression.  We first determine the returned formals in each of the
; argi.  That produces our pockets.  Then we determine the returned
; formals of body -- note however that the formals returned by body
; are not the formals of foo but the formals of the lambda.  The
; returned formals of body are our returned-formals.  This function
; can then be used to convert the returned formals of body into
; returned formals of foo.

  (cond ((null formals) nil)
        ((member-eq (car formals) returned-formals)
         (union-eq (car pockets)
                   (map-returned-formals-via-formals (cdr formals)
                                                     (cdr pockets)
                                                     returned-formals)))
        (t (map-returned-formals-via-formals (cdr formals)
                                             (cdr pockets)
                                             returned-formals))))

(defun map-type-sets-via-formals (formals ts-lst returned-formals)

; This is just like the function above except instead of dealing with
; a list of lists which are unioned together we deal with a list of
; type-sets which are ts-unioned.

  (cond ((null formals) *ts-empty*)
        ((member-eq (car formals) returned-formals)
         (ts-union (car ts-lst)
                   (map-type-sets-via-formals (cdr formals)
                                              (cdr ts-lst)
                                              returned-formals)))
        (t (map-type-sets-via-formals (cdr formals)
                                      (cdr ts-lst)
                                      returned-formals))))

(defun vector-ts-union (ts-lst1 ts-lst2)

; Given two lists of type-sets of equal lengths we ts-union
; corresponding elements and return the resulting list.

  (cond ((null ts-lst1) nil)
        (t (cons (ts-union (car ts-lst1) (car ts-lst2))
                 (vector-ts-union (cdr ts-lst1) (cdr ts-lst2))))))

(defun map-cons-tag-trees (lst ttree)

; Cons-tag-tree every element of lst into ttree.

  (cond ((null lst) ttree)
        (t (map-cons-tag-trees
            (cdr lst)
            (cons-tag-trees (car lst) ttree)))))

(defun type-set-and-returned-formals-with-rule1
  (alist rule-vars type-alist ens wrld basic-ts vars-ts vars ttree)

; See type-set-with-rule1 for a slightly simpler version of this.

; Note: This function is really just a loop that finishes off the
; computation done by type-set-and-returned-formals-with-rule, below.
; It would be best not to try to understand this function until you
; have read that function and type-set-and-returned-formals.

; Alist maps variables in a type-prescription to terms.  The context in which
; those terms occur is described by type-alist.  Rule-vars is the list of :vars
; of the rule.

; The last four arguments are accumulators that will become four of the
; answers delivered by type-set-and-returned-formals-with-rule, i.e.,
; a basic-ts, the type-set of a set of vars, the set of vars, and the
; justifying ttree.  We assemble these four answers by sweeping over
; alist, considering each var and its image term.  If the var is not
; in the rule-vars, we go on.  If the var is in the rule-vars, then
; its image is a possible value of the term for which we are computing
; a type-set.  If its image is a variable, we accumulate it and its
; type-set into vars and vars-ts.  If its image is not a variable, we
; accumulate its type-set into basic-ts.

; The ttree returned is 'assumption-free (provided the initial ttree
; is also).

  (cond
   ((null alist) (mv basic-ts vars-ts vars type-alist ttree))
   ((member-eq (caar alist) rule-vars)
    (mv-let (ts ttree)
            (type-set (cdar alist) nil nil type-alist ens wrld ttree nil nil)
            (let ((variablep-image (variablep (cdar alist))))
              (type-set-and-returned-formals-with-rule1
               (cdr alist) rule-vars
               type-alist ens wrld
               (if variablep-image
                   basic-ts
                   (ts-union ts basic-ts))
               (if variablep-image
                   (ts-union ts vars-ts)
                   vars-ts)
               (if variablep-image
                   (add-to-set-eq (cdar alist) vars)
                   vars)
               ttree))))
   (t
    (type-set-and-returned-formals-with-rule1
     (cdr alist) rule-vars
     type-alist ens wrld
     basic-ts
     vars-ts
     vars
     ttree))))

(defun type-set-and-returned-formals-with-rule (tp term type-alist ens wrld
                                                   ttree)

; This function is patterned after type-set-with-rule, which the
; reader might understand first.

; The ttree returned is 'assumption-free (provided the initial ttree
; and type-alist are also).

  (cond
   ((enabled-numep (access type-prescription tp :nume) ens)
    (mv-let
     (unify-ans unify-subst)
     (one-way-unify (access type-prescription tp :term)
                    term)
     (cond
      (unify-ans
       (with-accumulated-persistence
        (access type-prescription tp :rune)
        (basic-ts vars-ts vars type-alist ttree)
        (not (and (ts= basic-ts *ts-unknown*)
                  (ts= vars-ts *ts-empty*)
                  (null vars)))
        (let* ((backchain-limit (backchain-limit wrld :ts))
               (type-alist (extend-type-alist-with-bindings
                            unify-subst nil nil type-alist nil ens wrld nil nil
                            nil backchain-limit)))
          (mv-let
           (relieve-hyps-ans type-alist ttree)
           (type-set-relieve-hyps (access type-prescription tp :rune)
                                  term
                                  (access type-prescription tp :hyps)
                                  (access type-prescription tp
                                          :backchain-limit-lst)
                                  nil
                                  nil
                                  unify-subst
                                  type-alist
                                  nil ens wrld nil ttree
                                  nil nil backchain-limit 1)
           (cond
            (relieve-hyps-ans

; Subject to the conditions in ttree, we now know that the type set of term is
; either in :basic-ts or else that term is equal to the image under unify-subst
; of some var in the :vars of the rule.  Our charter is to return five results:
; basic-ts, vars-ts, vars, type-alist and ttree.  We do that with the
; subroutine below.  It sweeps over the unify-subst, considering each vi and
; its image, ai.  If ai is a variable, then it accumulates ai into the returned
; vars (which is initially nil below) and the type-set of ai into vars-ts
; (which is initially *ts-empty* below).  If ai is not a variable, it
; accumulates the type-set of ai into basic-ts (which is initially :basic-ts
; below).

             (type-set-and-returned-formals-with-rule1
              unify-subst
              (access type-prescription tp :vars)
              type-alist ens wrld
              (access type-prescription tp :basic-ts)
              *ts-empty*
              nil
              (push-lemma
               (access type-prescription tp :rune)
               ttree)))
            (t

; We could not establish the hyps of the rule.  Thus, the rule tells us
; nothing about term.

             (mv *ts-unknown* *ts-empty* nil type-alist ttree)))))))
      (t

; The :term of the rule does not unify with our term.

       (mv *ts-unknown* *ts-empty* nil type-alist ttree)))))
   (t

; The rule is disabled.

      (mv *ts-unknown* *ts-empty* nil type-alist ttree))))

(defun type-set-and-returned-formals-with-rules
  (tp-lst term type-alist ens w ts vars-ts vars ttree)

; See type-set-with-rules for a simpler model of this function.  We
; try to apply each type-prescription in tp-lst, "conjoining" the
; results into an accumulating type-set, ts, and vars (and its
; associated type-set, vars-ts).  However, if a rule fails to change
; the accumulating answers, we ignore it.

; However, we cannot really conjoin two type-prescriptions and get a
; third.  We do, however, deduce a valid conclusion.  A rule
; essentially gives us a conclusion of the form (or basic-ts
; var-equations), where basic-ts is the proposition that the term is
; of one of several given types and var-equations is the proposition
; that the term is one of several given vars.  Two rules therefore
; tell us (or basic-ts1 var-equations1) and (or basic-ts2
; var-equations2).  Both of these propositions are true.  From them we
; deduce the truth
; (or (and basic-ts1 basic-ts2)
;     (or var-equations1 var-equations2)).
; Note that we conjoin the basic type-sets but we disjoin the vars.  The
; validity of this conclusion follows from the tautology
; (implies (and (or basic-ts1 var-equations1)
;               (or basic-ts2 var-equations2))
;          (or (and basic-ts1 basic-ts2)
;              (or var-equations1 var-equations2))).
; It would be nice if we could conjoin both sides, but that's not valid.

; Recall that we actually must also return the union of the type-sets
; of the returned vars.  Since the "conjunction" of two rules leads us
; to union the vars together we just union their types together too.

; The ttree returned is 'assumption free provided the initial ttree and
; type-alist are also.

  (cond
   ((null tp-lst)
    (mv-let
     (ts1 ttree1)
     (type-set term nil nil type-alist ens w ttree nil nil)
     (let ((ts2 (ts-intersection ts1 ts)))
       (mv ts2 vars-ts vars (if (ts= ts2 ts) ttree ttree1)))))
   (t (mv-let
       (ts1 vars-ts1 vars1 type-alist1 ttree1)
       (type-set-and-returned-formals-with-rule (car tp-lst) term
                                                type-alist ens w ttree)
       (let* ((ts2 (ts-intersection ts1 ts))
              (unchangedp (and (ts= ts2 ts)
                               (equal type-alist type-alist1))))

; If the type-set established by the new rule doesn't change (i.e.,
; narrow) what we already know, we simply choose to ignore the new
; rule.  If it does change, then ts2 is smaller and we have to union
; together what we know about the vars and report the bigger ttree.

         (type-set-and-returned-formals-with-rules
          (cdr tp-lst)
          term type-alist1 ens w
          ts2
          (if unchangedp
              vars-ts
              (ts-union vars-ts1 vars-ts))
          (if unchangedp
              vars
              (union-eq vars1 vars))
          (if unchangedp
              ttree
              ttree1)))))))

(mutual-recursion

(defun type-set-and-returned-formals (term type-alist ens wrld ttree)

; Term is the if-normalized body of a defined function.  The
; 'type-prescriptions property of that fn (and all of its peers in its mutually
; recursive clique) may or may not be nil.  If non-nil, it may contain many
; enabled rules.  (When guards were part of the logic, we computed the type-set
; of a newly defined function twice, once before and once after verifying its
; guards.  So during the second pass, a valid rule was present.)  Among the
; rules is one that is possibly unsound and represents our current guess at the
; type.  We compute, from that guess, a "basic type-set" for term and a list of
; formals that might be returned by term.  An odd aspect of this ttree is that
; it will probably include the rune of the very rule we are trying to create,
; since its use in this process is essentially as an induction hypothesis.

; This function returns four results.  The first is the basic type-set
; computed, the second is another type-set which we call the variables
; type-set, and the third is the set of returned formals.  Those three results
; satisfy the claim made below.  Informally, we view the second result as the
; union of the type-sets of the returned formals.  The fourth result is a ttree
; justifying all the type-set reasoning done so far, accumulated onto the
; initial ttree.  The ttree returned is 'assumption-free provided the initial
; ttree and type-alist are also.

; The function works by walking through the if structure of the body, using the
; normal assume-true-false to construct the governing type-alist for each
; branch.  Upon arriving at a leaf term we compute the result.  If the term is
; a quote or a call to an ACL2 primitive, we just use type-set.  If the term is
; a call of a defun'd function, we interpret its type-prescription.

; CLAIM.  Consider an input term and type-alist, as well as the return values
; (mv bts vts vars ttree).  Assume that the variables of term satisfy the
; requirements of the type-alist.  Then either term satisfies the type-set bts,
; or else term is equal to some v in vars, in which case term satisfies vts.
; (Moreover, the returned ttree is an extension of the input ttree that
; justifies these conclusions, but we do not remark further on that ttree.)

; (Remark.  If we care to be a bit pedantic, then we may formulate the Claim in
; terms of first-order logic as follows.  A type-alist ta and a type-set ts
; naturally give rise to first-order formulas phi_ta(x1,...xn) and phi_ts(x),
; respectively.  The Claim says that the following is a theorem of the theory
; corresponding to the given world, wrld, where the given term has variables
; x1, ..., xn, vars is {v1,...,vk}, and ta is the given type-alist:

;   phi_ta(x1,...,xn)
;   ->
;   phi_bts(term) \/ (phi_vts(term) & (term = v1 \/ ... \/ term = vk)).

; End of Remark.)

; Historical Plaque from Nqthm.

; In nqthm, the root of the guessing process was DEFN-TYPE-SET, which was
; mutually recursive with DEFN-ASSUME-TRUE-FALSE.  The following comment could
; be found at the entrance to the guessing process:


;   *************************************************************
;   THIS FUNCTION WILL BE COMPLETELY UNSOUND IF TYPE-SET IS EVER
;   REACHABLE FROM WITHIN IT.  IN PARTICULAR, BOTH THE TYPE-ALIST AND
;   THE TYPE-PRESCRIPTION FOR THE FN BEING PROCESSED ARE SET TO ONLY
;   PARTIALLY ACCURATE VALUES AS THIS FN COMPUTES THE REAL TYPE-SET.
;   *************************************************************

; We now believe that this dreadful warning is an overstatement of the case.
; It is true that in nqthm the type-alist used in DEFN-TYPE-SET would cause
; trouble if it found its way into TYPE-SET, because it bound vars to "defn
; type-sets" (pairs of type-sets and variables) instead of to type-sets.  But
; the fear of the inaccurate TYPE-PRESCRIPTIONs above is misplaced we think.
; We believe that if one guesses a type-prescription and then confirms that it
; accurately describes the function body, then the type-prescription is
; correct.  Therefore, in ACL2, far from fencing type-set away from
; "defun-type-set" we use it explicitly.  This has the wonderful advantage that
; we do not duplicate the type-set code (which is even worse in ACL2 than it
; was in nqthm).

  (cond
   ((variablep term)

; Consider the following historical comment.

;   Term is a formal variable.  We compute its type-set under
;   type-alist.  If it is completely unrestricted, then we will say that
;   formal is sometimes returned.  Otherwise, we will say that it is not
;   returned.  Once upon a time we always said it was returned.  But the
;   term (if (integerp x) (if (< x 0) (- x) x) 0) as occurs in
;   integer-abs, then got the type-set "nonnegative integer or x" which
;   meant that it effectively had the type-set unknown.

; Thus, in Version_8.0 and many preceding versions, for the variable, term, we
; heuristically returned (mv *ts-empty* ts (list term) ttree) when the type of
; term was completely unrestricted (i.e., equal to *ts-unknown*), and otherwise
; we returned (mv ts *ts-empty* nil ttree).  We then realized that we could
; defer this choice until popping up to the top level (by introducing function
; type-set-and-returned-formals-top), which strengthened the resulting type
; prescription in some cases.  Here is an example, where previously the
; generated type-prescription was trivial -- :args foo reported that the Type
; is "built-in (or unrestricted)" -- but now it's as expected -- the reported
; Type is (EQUAL (F1 X Y) X).

;   (defund f1 (x y)
;     (if (integerp x)
;         (if (consp y)
;             (f1 x (cdr y))
;           x)
;       x))

; Observe that the code below satisfies our Claim, since if term satisfies the
; requirements of type-alist, then it satisfies the computed type-set, by
; correctness of the function, type-set.

    (mv-let (ts ttree)
            (type-set term nil nil type-alist ens wrld ttree nil nil)
            (mv *ts-empty* ts (list term) ttree)))
   ((fquotep term)

; Term is a constant.  We return a basic type-set consisting of the type-set of
; term.  Our Claim holds, again by correctness of type-set.

    (mv-let (ts ttree)
            (type-set term nil nil type-alist ens wrld ttree nil nil)
            (mv ts *ts-empty* nil ttree)))
   ((flambda-applicationp term)

; Let term be ((lambda (...u...) body) ...arg...).  Let the formals in term be
; x1, ..., xn.  We compute a basic type-set, bts, some returned vars, vars, and
; a variable type-set, vts, for a lambda application as follows.

; (1) For each argument, arg, obtain bts-arg, vts-arg, and vars-arg, which are
; the basic type-set, the variable type-set, and the returned variables with
; respect to the given type-alist.

; (2) Build a new type-alist, type-alist-body, by binding the formals of the
; lambda, (...u...), to the types of its arguments (...arg...) computed with
; respect to the given type-alist.

; (3) Obtain bts-body, vts-body, and vars-body, by recursively processing body
; under type-alist-body.

; (4) Create a preliminary bts by unioning bts-body and those of the bts-args
; in positions that are sometimes returned, as specified by vars-body.

; (5) Create the final vars by unioning together those of the vars-args in
; positions that are sometimes returned, as specified by vars-body.

; (6) Union together the variable type-sets computed for those final vars with
; respect to type-alist, to create a preliminary vts.

; (7) Create the final bts and vts by intersecting each of the preliminary bts
; and vts (from (4) and (6)) with the union of bts-body and vts-body.

; We prove the Claim by induction on the term.  We may assume:

; (a) The hypothesis of the Claim holds for the given term and type-alist: that
; is, the variables of term satisfy the requirements of type-alist.

; For convenience we assume that the formals of the lambda are disjoint from
; the free variables of the given term; otherwise, just rename them and observe
; that the results are unchanged by that renaming.  Now consider the following
; assertion.

; (*) Each free variable u of body is equal to the corresponding actual, arg.

; By beta-reduction, term is provably equal to body/s where s is the
; substitution mapping each formal u of the lambda to the corresponding actual,
; arg.  With that motivation, we will feel free below to view term as equal to
; body under the assumption, (*), since of course the following is valid for
; any property P: (forall (u) (u=arg -> P(body))) <-> P(body/s).

; By (a), each free variable xi of term satisfies its type-set computed from
; the given type-alist.  Therefore the type-sets are valid that are computed
; for each argument, arg, with respect to that type-alist.  Thus:

; (b) The hypothesis of the Claim holds for body and body-type-alist under the
; assumption (*).

; We apply the inductive hypothesis to (b) and obtain:

; (c) The Claim holds under assumption (*) for the triple calculated for body
; with respect to type-alist-body: bts-body, vts-body, and vars-body.

; It follows from (c) that term satisfies bts-body or vts-body; so the
; intersection in (7) with the union of these two types is harmless.
; Therefore, it suffices to prove the Claim for the bts, vts, and vars computed
; in (4) through (6) above.  That is, it suffices to show, assuming validity of
; the given type-alist, that either term satisfies bts, or else term satisfies
; vts and is equal to some variable in vars.  It therefore suffices to assume
; (*) and (by (b)) the validity of body-type-alist, and show that either body
; satisfies bts or else body satisfies vts and is equal to some variable in
; vars.

; So assume (*); thus by (c), either body satisfies bts-body, or else body is
; equal to some variable in vars-body.  In the former case we are done, so
; assume that body is equal to some variable, u, in vars-body.  Then by (*),
; body is equal to the corresponding arg (that is: u is a formal of the lambda
; being applied, and arg is the corresponding actual).  By the inductive
; hypothesis together with (4) and (5), either arg has type bts or else arg is
; equal to some variable in vars.  Since body is equal to arg, then body has
; type bts or else body is equal to some variable in vars.  By (6) and (a), if
; body is equal to some variable in vars then body has type vts, which
; concludes the proof of the Claim.

    (mv-let (bts-args vts-args vars-args ttree-args)
      (type-set-and-returned-formals-lst (fargs term)
                                         type-alist
                                         ens wrld)
      (mv-let (bts-body vts-body vars-body ttree)
        (type-set-and-returned-formals
         (lambda-body (ffn-symb term))
         (zip-variable-type-alist
          (lambda-formals (ffn-symb term))
          (pairlis$ (vector-ts-union bts-args vts-args)
                    ttree-args))
         ens wrld ttree)
        (let* ((bts (ts-union bts-body
                              (map-type-sets-via-formals
                               (lambda-formals (ffn-symb term))
                               bts-args
                               vars-body)))
               (vars (map-returned-formals-via-formals
                      (lambda-formals (ffn-symb term))
                      vars-args
                      vars-body))
               (ts-and-ttree-lst
                (type-set-lst vars nil nil type-alist nil ens wrld
                              nil nil (backchain-limit wrld :ts)))
               (vts0

; Below we make unconventional use of map-type-sets-via-formals.  Its first and
; third arguments are equal and thus every element of its second argument will
; be ts-unioned into the answer.  This is just a hackish way to union together
; the type-sets of all the returned formals.

                (map-type-sets-via-formals
                 vars
                 (strip-cars ts-and-ttree-lst)
                 vars))
               (ts1 (ts-union bts-body vts-body)))
          (mv (ts-intersection bts ts1)
              (ts-intersection vts0 ts1)
              vars
              (map-cons-tag-trees (strip-cdrs ts-and-ttree-lst)
                                  ttree))))))
   ((eq (ffn-symb term) 'if)

; If by type-set reasoning we can see which way the test goes, we can clearly
; focus on that branch.  So now we consider (if t1 t2 t3) where we don't know
; which way t1 will go.  We compute the union of the respective components of
; the answers for t2 and t3.  In general, the type-set of any instance of this
; if will be at most the union of the type-sets of the instances of t2 and t3.
; (In the instance, t1' might be decidable and a smaller type-set could be
; produced.)

    (mv-let
     (must-be-true
      must-be-false
      true-type-alist
      false-type-alist
      ts-ttree)
     (assume-true-false (fargn term 1)
                        nil nil nil type-alist ens wrld
                        nil nil nil)

; Observe that ts-ttree does not include ttree.  If must-be-true and
; must-be-false are both nil, ts-ttree is nil and can thus be ignored.

     (cond
      (must-be-true

; Probably it would be sound to return (mv *ts-empty* *ts-empty* nil
; (cons-tag-trees ts-ttree ttree)).  Since the context is contradictory.  But
; this hasn't been an issue as far as we know, so we'll avoid making an
; airtight soundness argument until the need arises.

       (type-set-and-returned-formals (fargn term 2)
                                      true-type-alist ens wrld
                                      (cons-tag-trees ts-ttree ttree)))
      (must-be-false
       (type-set-and-returned-formals (fargn term 3)
                                      false-type-alist ens wrld
                                      (cons-tag-trees ts-ttree ttree)))
      (t (mv-let
          (basic-ts2 formals-ts2 formals2 ttree)
          (type-set-and-returned-formals (fargn term 2)
                                         true-type-alist
                                         ens wrld ttree)
          (mv-let
           (basic-ts3 formals-ts3 formals3 ttree)
           (type-set-and-returned-formals (fargn term 3)
                                          false-type-alist
                                          ens wrld ttree)
           (mv (ts-union basic-ts2 basic-ts3)
               (ts-union formals-ts2 formals-ts3)
               (union-eq formals2 formals3)
               ttree)))))))
   (t
    (let* ((fn (ffn-symb term))
           (recog-tuple
            (most-recent-enabled-recog-tuple fn
                                             (global-val 'recognizer-alist wrld)
                                             ens)))
      (cond
       (recog-tuple
        (mv-let (ts ttree1)
                (type-set (fargn term 1) nil nil type-alist ens wrld ttree nil
                          nil)
                (mv-let (ts ttree)
                        (type-set-recognizer recog-tuple ts ttree1 ttree)
                        (mv ts *ts-empty* nil ttree))))
       (t
        (type-set-and-returned-formals-with-rules
         (getpropc (ffn-symb term) 'type-prescriptions nil wrld)
         term type-alist ens wrld
         *ts-unknown* *ts-empty* nil ttree)))))))

(defun type-set-and-returned-formals-lst
  (lst type-alist ens wrld)
  (cond
   ((null lst) (mv nil nil nil nil))
   (t (mv-let (basic-ts returned-formals-ts returned-formals ttree)
              (type-set-and-returned-formals (car lst)
                                             type-alist ens wrld nil)
              (mv-let (ans1 ans2 ans3 ans4)
                      (type-set-and-returned-formals-lst (cdr lst)
                                                         type-alist
                                                         ens wrld)
                      (mv (cons basic-ts ans1)
                          (cons returned-formals-ts ans2)
                          (cons returned-formals ans3)
                          (cons ttree ans4)))))))

)

(defun type-set-and-returned-formals-top (term ens wrld ttree)
  (mv-let (basic-type-set returned-vars-type-set returned-vars ttree)
    (type-set-and-returned-formals term nil ens wrld ttree)
    (cond ((ts= returned-vars-type-set -1)
           (mv basic-type-set returned-vars ttree))
          (t
           (mv (ts-union basic-type-set returned-vars-type-set)
               nil
               ttree)))))

(defun guess-type-prescription-for-fn-step (name body ens wrld ttree)

; This function takes one incremental step towards the type- prescription of
; name in wrld.  Body is the normalized body of name.  We assume that the
; current guess for a type-prescription for name is the car of the
; 'type-prescriptions property.  That is, initialization has occurred and every
; iteration keeps the current guess at the front of the list.

; We get the type-set of and formals returned by body.  We convert the two
; answers into a new type-prescription and replace the current car of the
; 'type-prescriptions property.

; We return the new world and an 'assumption-free ttree extending ttree.

  (let* ((ttree0 ttree)
         (old-type-prescriptions
          (getpropc name 'type-prescriptions nil wrld))
         (tp (car old-type-prescriptions)))
    (mv-let (new-basic-type-set new-returned-vars ttree)
      (type-set-and-returned-formals-top body ens wrld ttree)
      (cond ((ts= new-basic-type-set *ts-unknown*)

; Ultimately we will delete this rule.  But at the moment we wish merely to
; avoid contaminating the ttree of the ongoing process by whatever we've
; done to derive this.

             (mv (putprop name
                          'type-prescriptions
                          (cons (change type-prescription tp
                                        :basic-ts *ts-unknown*
                                        :vars nil)
                                (cdr old-type-prescriptions))
                          wrld)
                 ttree0))
            (t
             (mv (putprop name
                          'type-prescriptions
                          (cons (change type-prescription tp
                                        :basic-ts new-basic-type-set
                                        :vars new-returned-vars)
                                (cdr old-type-prescriptions))
                          wrld)
                 ttree))))))

(defconst *clique-step-install-interval*

; This interval represents how many type prescriptions are computed before
; installing the resulting intermediate world.  The value below is merely
; heuristic, chosen with very little testing; we should feel free to change it.

  30)

(defun guess-and-putprop-type-prescription-lst-for-clique-step
  (names bodies ens wrld ttree interval state)

; Given a list of function names and their normalized bodies
; we take one incremental step toward the final type-prescription of
; each fn in the list.  We return a world containing the new
; type-prescription for each fn and a ttree extending ttree.

; Note: During the initial coding of ACL2 the iteration to guess
; type-prescriptions was slightly different from what it is now.  Back
; then we used wrld as the world in which we computed all the new
; type-prescriptions.  We returned those new type-prescriptions to our
; caller who determined whether the iteration had repeated.  If not,
; it installed the new type-prescriptions to generate a new wrld' and
; called us on that wrld'.

; It turns out that that iteration can loop indefinitely.  Consider the
; mutually recursive nest of foo and bar where
; (defun foo (x) (if (consp x) (not (bar (cdr x))) t))
; (defun bar (x) (if (consp x) (not (foo (cdr x))) nil))

; Below are the successive type-prescriptions under the old scheme:

; iteration    foo type      bar type
;   0             {}            {}
;   1             {T NIL}       {NIL}
;   2             {T}           {T NIL}
;   3             {T NIL}       {NIL}
;  ...            ...           ...

; Observe that the type of bar in round 1 is incomplete because it is
; based on the incomplete type of foo from round 0.  This kind of
; incompleteness is supposed to be closed off by the iteration.
; Indeed, in round 2 bar has got its complete type-set.  But the
; incompleteness has now been transferred to foo: the round 2
; type-prescription for foo is based on the incomplete round 1
; type-prescription of bar.  Isn't this an elegant example?

; The new iteration computes the type-prescriptions in a strict linear
; order.  So that the round 1 type-prescription of bar is based on the
; round 1 type-prescription of foo.

  (cond ((null names) (mv wrld ttree state))
        (t (mv-let
            (erp val state)
            (update-w (int= interval 0) wrld)
            (declare (ignore erp val))
            (mv-let
             (wrld ttree)
             (guess-type-prescription-for-fn-step
              (car names)
              (car bodies)
              ens wrld ttree)
             (guess-and-putprop-type-prescription-lst-for-clique-step
              (cdr names)
              (cdr bodies)
              ens
              wrld
              ttree
              (if (int= interval 0)
                  *clique-step-install-interval*
                (1- interval))
              state))))))

(mutual-recursion

(defun guarded-termp (x w)

; We assume that x is a termp in some world whose theory extends that of the
; world, w.  Here we check that in addition, x is a termp in w by checking that
; all function symbols are defined in w.

  (declare (xargs :guard (and (pseudo-termp x)
                              (plist-worldp w))))
  (cond ((atom x) t)
        ((eq (car x) 'quote)
         t)
        ((not (mbt (true-listp x))) nil)
        ((not (mbt (pseudo-term-listp (cdr x)))) nil)
        (t (if (symbolp (car x))
               (not (eq (getpropc (car x) 'formals t w) t))
             (and (guarded-termp (caddr (car x)) w)
                  (guarded-term-listp (cdr x) w))))))

(defun guarded-term-listp (lst w)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (plist-worldp w))))
  (cond ((endp lst) (equal lst nil))
        (t (and (guarded-termp (car lst) w)
                (guarded-term-listp (cdr lst) w)))))

)

(defun conjoin-type-prescriptions (tp1 tp2 ens wrld)

; Tp1 and tp2 are each a runic type-prescription record or an atom,
; representing the unknown type-prescription.  However, tp2 need not have a
; valid :corollary field.

; If tp1 and tp2 are both records, then they both have the same rune.  If tp1
; is an atom, it is nil; if tp2 is an atom, it is a nume.  We return either nil
; or a type-prescription record implied by the conjunction of tp1 and tp2.  If
; tp1 is a record then it was supplied by some cert-data.  If tp2 is a record
; then it is a valid type prescription in wrld (other than perhaps the
; :corollary field, as noted above); thus, we prefer to return a modification
; of tp2 rather than of tp1, so that we don't have to change the :nume field.

  (cond
   ((null tp1)
    (cond
     ((consp tp2)
      (mv-let (corollary ttree)
        (convert-type-prescription-to-term tp2 ens wrld)
        (mv (change type-prescription tp2
                    :corollary corollary)
            ttree)))
     (t (mv nil nil))))
   (t ; tp1 is a runic type-prescription record
    (assert$
     (and (null (access type-prescription tp1 :hyps))
          (null (access type-prescription tp1 :backchain-limit-lst)))
     (cond
      ((atom tp2) ; tp2 is a nume
       (cond
        ((guarded-termp (access type-prescription tp1 :corollary)
                        wrld)
         (mv (change type-prescription tp1
                     :nume tp2)
             (push-lemma *fake-rune-for-cert-data* nil)))
        (t
         (mv-let (corollary ttree)
           (convert-type-prescription-to-term tp1 ens wrld)
           (mv (change type-prescription tp1
                       :nume tp2
                       :corollary corollary)
               (push-lemma *fake-rune-for-cert-data* ttree))))))
      (t ; tp1 and tp2 are both runic type-prescription records
       (assert$

; Sanity check that both tp1 and tp2 are runic type-prescriptions for the same
; function symbol, differing at most in their :basic-ts, :vars, and :corollary.

        (and (null (access type-prescription tp2 :hyps))
             (null (access type-prescription tp2 :backchain-limit-lst))
             (equal (access type-prescription tp1 :term)
                    (access type-prescription tp2 :term))
             (equal (access type-prescription tp1 :rune)
                    (access type-prescription tp2 :rune)))
        (let ((basic-ts1 (access type-prescription tp1 :basic-ts))
              (basic-ts2 (access type-prescription tp2 :basic-ts)))
          (cond
           ((and (ts-subsetp basic-ts1 basic-ts2)
                 (guarded-termp (access type-prescription tp1 :corollary)
                                wrld)) ; common case
            (mv (change type-prescription tp1
                        :nume (access type-prescription tp2 :nume))

; Even though we are only using tp1 to give us the corollary, that corollary
; could have originally been computed using some rules (in a call of
; convert-type-prescription-to-term), so we credit the cert-data in which that
; computed type-prescription, tp1, was stored.

                (push-lemma *fake-rune-for-cert-data* nil)))
           ((ts-subsetp basic-ts2 basic-ts1) ; tp2 is stronger
            (mv-let (corollary ttree)
              (convert-type-prescription-to-term tp2 ens wrld)
              (mv (change type-prescription tp2
                          :corollary corollary)
                  ttree)))
           (t ; need to intersect the two :basic-ts fields
            (let* ((vars1 (access type-prescription tp1 :vars))
                   (vars2 (access type-prescription tp2 :vars))
                   (tp (cond
                        ((equal vars1 vars2)
                         (change type-prescription tp2
                                 :basic-ts
                                 (ts-intersection basic-ts1 basic-ts2)))
                        (t

; If the :term is none of the :vars of either tp1 or tp2, then its type must be
; the :basic-ts of tp1 and also the :basic-ts of tp2.

                         (change type-prescription tp2
                                 :basic-ts
                                 (ts-intersection basic-ts1 basic-ts2)
                                 :vars (union-eq vars1 vars2))))))
              (mv-let (corollary ttree)
                (convert-type-prescription-to-term tp ens wrld)
                (mv (change type-prescription tp
                            :corollary corollary)
                    ttree)))))))))))))

; Essay on Cert-data

; In February 2016, Jared Davis requested on behalf of Centaur Technology
; Inc. that we avoid recomputing runic type-prescriptions when including
; certified books.  There were two problems: type-prescription rules from an
; earlier included book were sometimes causing horrendous slowdowns in those
; computations while including a later book; and, we can lose nice
; type-prescriptions that were inferred during the proof (first) pass of
; certify-book using local rules, where a similar problem can occur with
; encapsulate.

; In March 2016 we solved these problems by introducing "cert-data" structures,
; which can be stored in certificates or in the state global variable
; 'cert-data.  Cert-data stores information on runic type-prescriptions, but
; some day we might put results from translate or other information that could
; be expensive to recompute.

; The following processes support the effective re-use of runic type
; prescriptions.

; (1) When including a certified book, all functions defined at the top level
;     (i.e., not inside sub-books) get their runic type-prescriptions (if any)
;     from the .cert file -- more specifically, from the value of state global
;     'cert-data, which is bound to the value from the .cert file.

; (2) Runic type-prescriptions are saved after pass1 of certify-book and
;     encapsulate.  For each :logic-mode defun processed in the second pass at
;     the top level (not in an included sub-book), an "intersection" is taken
;     of the runic type-prescription from the first pass and the computed runic
;     type-prescription computed in the usual way.  Note that since a function
;     can be defined locally in a locally included book during the first pass
;     but in a later defun at the top level in the second pass (which was
;     redundant in the first pass), we even save some runic type-prescriptions
;     from functions introduced during the first pass that were not introduced
;     at the top level.

;     Clearly each such rune is a logical consequence of the first pass; hence,
;     by conservativity, it is a logical consequence of the second pass.  Note
;     that we may need to recompute the :corollary, which otherwise might not
;     be a term of the theory produced by the second pass.

; (3) The runic type-prescription written to a .cert file is the one that
;     exists after the second pass.  We save such a rule for every function
;     that could be introduced when including the book, which includes the
;     top-level portcullis functions and every function introduced by the book
;     (even those not processed during pass 2).  Function
;     newly-defined-top-level-fns provides this information; happily, even
;     before we added support for cert-data, that function was already called
;     under certify-book-fn to compute a list of function symbols to pass to
;     write-expansion-file.

; Now we elaborate on these processes.

; Note that including an already-certified book gives you the specific type
; prescription from the .cert file.  If however a book B1 includes another book
; B2 only locally, then the type-prescription computed for B1 might be stronger
; than that from B2, because of our "intersection" of rules in (2) above.

; Suppose we are to determine the runic type-prescription for a given defun.
; If state global 'cert-data has value nil, then we just do the usual iterative
; calculation.  Otherwise we are to use that cert-data; but how do we know that
; we should do the "intersection" operation because we are in the pass 2 case,
; described in (2) above?  We bind key :pass1 to t in the value of state global
; 'cert-data during the second pass (meaning, cert-data is from pass 1).  If
; necessary we could have non-nil values that provide more information than t,
; for example, 'acl2::certify-book or 'acl2::encapsulate.  We don't bother to
; bind :pass1 to nil for other than pass 2; we simply don't bind :pass1.

; In (2) above we describe the saving of runic type-prescriptions to use during
; the second pass.  In the case of certify-book, however, we do this only for
; the part of the world not in the retraction after pass 1, since there is no
; need to save information for defuns already processed before starting pass 2.

; Why do we need the "intersection" operation described in (2) above?  That is,
; why not just pick either the runic type-prescription from the first pass or
; compute one for the second pass?  The answer is that either may be weaker
; than desired, as illustrated by the following two examples.  (These examples
; are for encapsulate, but certify-book has the same issue.)

; (2a) First, here is an example showing that the second pass can do a better
; job computing the runic type-prescription than the first pass.  (To see the
; empty 'type-prescriptions we would get for FOO on the first pass, change
; (encapsulate () ...) to (progn ...).)

; (encapsulate
;   ()
;   (local (include-book "rtl/rel9/support/support/lnot" :dir :system))

; ; Because of the following in-theory event, the cert-data from the first pass
; ; associates no runic type-prescription with FOO.

;   (local (in-theory nil))
;   (defun fl (x)
;     (declare (xargs :guard (real/rationalp x)))
;     (floor x 1))
;   (defun bits (x i j)
;     (declare (xargs :guard (and (natp x) (natp i) (natp j))
;                     :verify-guards nil))
;     (mbe :logic (if (or (not (integerp i))
;                         (not (integerp j)))
;                     0
;                     (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
;          :exec (if (< i j)
;                    0
;                    (logand (ash x (- j))
;                            (1- (ash 1 (1+ (- i j))))))))
;   (defun lnot (x n)
;     (declare (xargs :guard (and (natp x) (integerp n) (< 0 n))
;                     :verify-guards nil))
;     (if (natp n)
;         (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
;         0))
;   (defun foo (x n)
;     (lnot x n)))

; ; Using cert-data from the first pass only:
; ; (assert-event (null (getpropc 'foo 'type-prescriptions)))

; ; Computing the runic type-prescription in the second pass:
; (assert-event
;  (equal (decode-type-set
;          (access type-prescription
;                  (car (last (getpropc 'foo 'type-prescriptions)))
;                  :basic-ts))
;         '*ts-rational*)

; What we actually get, now, is *ts-integer*, because that's the :basic-ts for
; the runic type-prescription of lnot (and also of binary-logand, bits, and fl)
; from the locally included book, saved from the first pass.

; (2b) To obtain an example showing that the first pass can do a better job
; computing the runic type-prescription than the second pass, simply omit
; (in-theory nil) from the example above.  The second pass still gives us
; *ts-rational, as above; but if we change (encapsulate () ...) to (progn ...),
; we see:

; (assert-event
;  (equal (decode-type-set
;          (access type-prescription
;                  (car (last (getpropc 'foo 'type-prescriptions)))
;                  :basic-ts))
;         '*ts-non-negative-integer*))

; Let's turn now to our handling of a few thorny issues.

; Suppose we are certifying a book with an encapsulate that locally defines a
; function, f, such that later in the book is a different, non-local definition
; of f.  At the end of pass 1 of certify-book we will store a runic type
; prescription for the second definition.  Then during pass 2 of certify-book,
; might we make a mistake by associating that type-prescription with the first
; (local) definition of f?  No, because local definitions are skipped during
; pass 2.  But for robustness, we pass a value for cert-data to
; process-embedded-events, which binds state global cert-data to that value.
; Thus, we override the global cert-data when we process an encapsulate.

; The expansion phase of make-event introduces definitions that are in effect
; local.  As in the preceding paragraph, we need to avoid applying the global
; cert-data to such definitions.  This problem is solved primarily by arranging
; that protected-eval, via protect-system-state-globals, binds state global
; cert-data to nil.  An additional binding of cert-data to nil is made before
; calling make-event-fn2-lst, which handles :OR forms and thus can throw away
; earlier values.  In such a case, the runic type-prescription will be
; recomputed during include-book, but we think that such an exception is
; tolerable.

; We are careful to not use cert-data for non-trivial encapsulates.  It might
; well be possible to do so correctly, but we would need to be very careful to
; track constraints properly; it seems easy to have a soundness bug due to
; recording insufficient constraints in pass 2 to justify deductions made from
; stronger constraints in pass 1.

; A runic type-prescription rule may contain symbols not present in the
; certification world, as shown below.  A similar issue applies to the
; :expansion-alist field of the certificate, which is addressed by finding the
; problematic package names with pkg-names introducing hidden defpkg forms.  We
; use that same solution for cert-data.  The following example shows how this
; works.  First, let's look at a couple of books; notice the package definition
; that is to be made in the certification world of the first book.

;   $ cat sub.lisp
;   ; (defpkg "FOO" nil)
;   ; (certify-book "sub" 1)
;
;   (in-package "ACL2")
;
;   (defun f2 (x) x)
;   $ cat top.lisp
;   (in-package "ACL2")
;
;   (include-book "sub")
;
;   (defmacro my-def ()
;     `(defun f (,(intern$ "X" "FOO")) ,(intern$ "X" "FOO")))
;
;   (my-def)
;   $

; After certification of both books, the :CERT-DATA field of top.cert has the
; following value.

;   ((:TYPE-PRESCRIPTION (F 0 (3413 F FOO::X)
;                           (NIL)
;                           ((FOO::X) :TYPE-PRESCRIPTION F)
;                           EQUAL (F FOO::X)
;                           FOO::X)))

; Thus, a hidden defpkg is generated (here we abbreviate the directory as
; <dir>).

;   :BEGIN-PORTCULLIS-CMDS
;   (DEFPKG "FOO" NIL NIL
;           ("<dir>/sub.lisp")
;           T)
;   :END-PORTCULLIS-CMDS

(defun cert-data-val (fn cert-data-entry)

; Cert-data-entry is (cdr (assoc-eq key cert-data)) for some key.

  (let ((pair (and cert-data-entry ; optimization
                   (hons-get fn cert-data-entry))))
    (cdr pair)))

(defun cleanse-type-prescriptions (names type-prescriptions-lst def-nume
                                         rmp-cnt ens wrld installed-wrld
                                         cert-data-tp ttree)

; Names is a clique of function symbols.  Type-prescriptions-lst is in
; 1:1 correspondence with names and gives the value in wrld of the
; 'type-prescriptions property for each name.  (We provide this just
; because our caller happens to be holding it.)  This function should
; be called when we have completed the guessing process for the
; type-prescriptions for names.  This function does two sanitary
; things: (a) it deletes the guessed rule if its :basic-ts is
; *ts-unknown*, and (b) in the case that the guessed
; rule is kept, it is given the rune and nume described by the Essay
; on the Assignment of Runes and Numes by DEFUNS.  It is assumed that
; def-nume is the nume of (:DEFINITION fn), where fn is the car of
; names.  We delete *ts-unknown* rules just to save type-set the
; trouble of relieving their hyps or skipping them.

; Rmp-cnt (which stands for "runic-mapping-pairs count") is the length of the
; 'runic-mapping-pairs entry for the functions in names (all of which have the
; same number of mapping pairs).  We increment our def-nume by rmp-cnt on each
; iteration.

; This function knows that the defun runes for each name are laid out
; as follows, where i is def-nume:

; i   (:definition name)                                   ^
; i+1 (:executable-counterpart name)
; i+2 (:type-prescription name)           ; rmp-cnt=3 or 4
; i+3 (:induction name)                   ; optional       v

; Furthermore, we know that the nume of the :definition rune for the kth
; (0-based) name in names is def-nume+(k*rmp-cnt); that is, we assigned
; numes to the names in the same order as the names appear in names.

  (cond
   ((null names) (mv wrld ttree))
   (t
    (let* ((fn (car names))
           (lst (car type-prescriptions-lst))
           (tp1 (cert-data-val fn cert-data-tp))
           (tp2 ; still can have unset :corollary field
            (cond
             ((ts= *ts-unknown* (access type-prescription (car lst)
                                        :basic-ts))

; We bind tp2 to a nume in this case; see conjoin-type-prescriptions.

              (+ 2 def-nume))
             (t (change type-prescription
                        (car lst)
                        :rune (list :type-prescription fn)
                        :nume (+ 2 def-nume))))))
      (mv-let (new-tp ttree1)
        (conjoin-type-prescriptions tp1 tp2 ens installed-wrld)
        (let ((ttree2 (cons-tag-trees ttree1 ttree)))
          (mv-let
            (wrld ttree3)
            (cond
             ((null new-tp)
              (mv (putprop fn 'type-prescriptions (cdr lst) wrld)
                  ttree))
             (t (mv (putprop fn 'type-prescriptions
                             (cons new-tp (cdr lst))
                             wrld)
                    ttree2)))
            (cleanse-type-prescriptions (cdr names)
                                        (cdr type-prescriptions-lst)
                                        (+ rmp-cnt def-nume)
                                        rmp-cnt ens wrld installed-wrld
                                        cert-data-tp ttree3))))))))

(defun guess-and-putprop-type-prescription-lst-for-clique
  (names bodies def-nume ens wrld ttree big-mutrec cert-data-tp state)

; We assume that in wrld we find 'type-prescriptions for every fn in
; names.  We compute new guesses at the type-prescriptions for each fn
; in names.  If they are all the same as the currently stored ones we
; quit.  Otherwise, we store the new guesses and iterate.  Actually,
; when we quit, we cleanse the 'type-prescriptions as described above.
; We return the final wrld and a ttree extending ttree.  Def-nume is
; the nume of (:DEFINITION fn), where fn is the first element of names
; and is used in the cleaning up to install the proper numes in the
; generated rules.

  (let ((old-type-prescriptions-lst
         (getprop-x-lst names 'type-prescriptions wrld)))
    (mv-let (wrld1 ttree state)
            (guess-and-putprop-type-prescription-lst-for-clique-step
             names bodies ens wrld ttree *clique-step-install-interval* state)
            (er-progn
             (update-w big-mutrec wrld1)
             (cond ((equal old-type-prescriptions-lst
                           (getprop-x-lst names 'type-prescriptions wrld1))
                    (mv-let
                     (wrld2 ttree)
                     (cleanse-type-prescriptions
                      names
                      old-type-prescriptions-lst
                      def-nume
                      (length (getpropc (car names) 'runic-mapping-pairs nil
                                        wrld))
                      ens
                      wrld
                      wrld1
                      cert-data-tp
                      ttree)
                     (er-progn

; Warning:  Do not use set-w! here, because if we are in the middle of a
; top-level include-book, that will roll the world back to the start of that
; include-book.  We have found that re-installing the world omits inclusion of
; the compiled files for subsidiary include-books (see description of bug fix
; in :doc note-2-9 (bug fixes)).

                      (update-w big-mutrec wrld t)
                      (update-w big-mutrec wrld2)
                      (mv wrld2 ttree state))))
                   (t
                    (guess-and-putprop-type-prescription-lst-for-clique
                     names
                     bodies
                     def-nume ens wrld1 ttree big-mutrec cert-data-tp
                     state)))))))

(defun get-normalized-bodies (names wrld)

; Return the normalized bodies for names in wrld.

; WARNING: We ignore the runes and hyps for the normalized bodies returned.  So
; this function is probably only of interest when names are being introduced,
; where the 'def-bodies properties have been placed into wrld but no new
; :definition rules with non-nil :install-body fields have been proved for
; names.

  (cond ((endp names) nil)
        (t (cons (access def-body
                         (def-body (car names) wrld)
                         :concl)
                 (get-normalized-bodies (cdr names) wrld)))))

(defun cert-data-pair (fn cert-data-entry)

; Cert-data-entry is (cdr (assoc-eq key cert-data)) for some key.

  (and cert-data-entry ; optimization
       (hons-get fn cert-data-entry)))

(defun cert-data-entry-pair (key state)

; Key is :type-prescription or any other keyword that can be associated in a
; cert-data structure with a fast-alist.

  (let ((cert-data (f-get-global 'cert-data state)))
    (and cert-data ; optimization
         (assoc-eq key cert-data))))

(defun cert-data-putprop-type-prescription-lst-for-clique
    (cert-data-entry names def-nume rmp-cnt ttree ens wrld installed-wrld
                     changedp)

; Rmp-cnt (which stands for "runic-mapping-pairs count") is the length of the
; 'runic-mapping-pairs entry for the functions in names (all of which have the
; same number of mapping pairs).  We increment our def-nume by rmp-cnt on each
; iteration, as is done in cleanse-type-prescriptions.  Changedp is initially
; nil, but as we recur it becomes t if we ever extend wrld (with a putprop
; call).

  (cond
   ((endp names)
    (mv wrld
        (if changedp
            (push-lemma *fake-rune-for-cert-data* ttree)
          ttree)))
   (t (let* ((fn (car names))
             (cert-data-pair (cert-data-pair fn cert-data-entry)))
        (cond
         ((null cert-data-pair)
          (cert-data-putprop-type-prescription-lst-for-clique
           cert-data-entry
           (cdr names)
           (+ rmp-cnt def-nume)
           rmp-cnt
           ttree
           ens
           wrld ; no change; also ok, (putprop fn 'type-prescriptions nil wrld)
           installed-wrld
           changedp))
         (t
          (let ((cert-data-tp (cdr cert-data-pair)))
            (mv-let (corollary ttree1)
              (if (or (null cert-data-tp)
                      (guarded-termp (access type-prescription cert-data-tp
                                             :corollary)
                                     installed-wrld))
                  (mv nil nil) ; nothing to do
                (convert-type-prescription-to-term cert-data-tp ens

; We use the installed world (the one before cleansing started) for efficient
; handling of large mutual recursion nests.

                                                   installed-wrld))
              (cert-data-putprop-type-prescription-lst-for-clique
               cert-data-entry
               (cdr names)
               (+ rmp-cnt def-nume)
               rmp-cnt
               (cons-tag-trees ttree1 ttree)
               ens
               (putprop fn 'type-prescriptions
                        (list (if corollary
                                  (change type-prescription cert-data-tp
                                          :nume (+ 2 def-nume)
                                          :corollary corollary)
                                (change type-prescription cert-data-tp
                                        :nume (+ 2 def-nume))))
                        wrld)
               installed-wrld
               t)))))))))

(defun putprop-type-prescription-lst (names subversive-p def-nume ens wrld
                                            ttree state)

; Names is a list of mutually recursive fns being introduced.  We assume that
; for each fn in names we can obtain from wrld the 'formals and the normalized
; body (from 'def-bodies).  Def-nume must be the nume assigned (:DEFINITION
; fn), where fn is the first element of names.  See the Essay on the Assignment
; of Runes and Numes by DEFUNS.  We compute type-prescriptions for each fn in
; names and store them.  We return the new wrld and a ttree extending ttree
; justifying what we've done.

; This function knows that HIDE should not be given a
; 'type-prescriptions property.

; Historical Plaque for Versions Before 1.8

; In 1.8 we "eliminated guards from the ACL2 logic."  Prior to that guards were
; essentially hypotheses on the definitional equations.  This complicated many
; things, including the guessing of type-prescriptions.  After a function was
; known to be Common Lisp compliant we could recompute its type-prescription
; based on the fact that we knew that every subfunction in it would return its
; "expected" type.  Here is a comment from that era, preserved for posterity.

;   On Guards: In what way is the computed type-prescription influenced
;   by the changing of the 'guards-checked property from nil to t?

;   The key is illustrated by the following fact: type-set returns
;   *ts-unknown* if called on (+ x y) with gc-flg nil but returns a
;   subset of *ts-acl2-number* if called with gc-flg t.  To put this into
;   context, suppose that the guard for (fn x y) is (g x y) and that it
;   is not known by type-set that (g x y) implies that both x and y are
;   acl2-numberps.  Suppose the body of fn is (+ x y).  Then the initial
;   type-prescription for fn, computed when the 'guards-checked property
;   is nil, will have the basic-type-set *ts-unknown*.  After the guards
;   have been checked the basic type-set will be *ts-acl2-number*.

  (cond
   ((and (consp names)
         (eq (car names) 'hide)
         (null (cdr names)))
    (mv wrld ttree state))
   (subversive-p

; We avoid storing a runic type-prescription rule for any subversive function,
; because our fixed-point algorithm assumes the the definition provably
; terminates, which may not be the case for subversive functions.

; Below is a series of two examples.  The first is the simpler of the two, and
; shows the basic problem.  It succeeds in Version_3.4.

;   (encapsulate
;    ()
;
;    (defun h (x) (declare (ignore x)) t)
;
;    (in-theory (disable (:type-prescription h)))
;
;    (local (in-theory (enable (:type-prescription h))))
;
;    (encapsulate (((f *) => *))
;                 (local (defun f (x) (cdr x)))
;                 (defun g (x)
;                   (if (consp x) (g (f x)) (h x))))
;
;    (defthm atom-g
;      (atom (g x))
;      :rule-classes nil)
;    )
;
;  (defthm contradiction nil
;    :hints (("Goal" :use ((:instance
;                           (:functional-instance
;                            atom-g
;                            (f identity)
;                            (g (lambda (x)
;                                 (if (consp x) x t))))
;                           (x '(a b))))))
;    :rule-classes nil)

; Our first solution was to erase type-prescription rules for subversive
; functions after the second pass through the encapsulate.  While that dealt
; with the example above -- atom-g was no longer provable -- the problem was
; that the type-prescription rule can be used to normalize a non-subversive
; (indeed, non-recursive) definition later in the same encapsulate, before the
; type-prescription rule has been erased.  The second example shows how that
; works:

;  (encapsulate
;   ()
;
;   (defun h (x) (declare (ignore x)) t)
;
;   (in-theory (disable (:type-prescription h)))
;
;   (local (in-theory (enable (:type-prescription h))))
;
;   (encapsulate (((f *) => *))
;                (local (defun f (x) (cdr x)))
;                (defun g (x)
;                  (if (consp x) (g (f x)) (h x)))
;                (defun k (x)
;                  (g x)))
;
;  ; The following in-theory event is optional; it emphasizes that the problem is
;  ; with the use of the bogus type-prescription for g in normalizing the body of
;  ; k, not with the direct use of a type-prescription rule in subsequent
;  ; proofs.
;   (in-theory (disable (:type-prescription k) (:type-prescription g)))
;
;   (defthm atom-k
;     (atom (k x))
;     :rule-classes nil)
;   )
;
;  (defthm contradiction nil
;    :hints (("Goal" :use ((:instance
;                           (:functional-instance
;                            atom-k
;                            (f identity)
;                            (g (lambda (x)
;                                 (if (consp x) x t)))
;                            (k (lambda (x)
;                                 (if (consp x) x t))))
;                           (x '(a b))))))
;    :rule-classes nil)

    (mv wrld ttree state))
   (t
    (let ((cert-data-entry-pair
           (cert-data-entry-pair :type-prescription state))
          (cert-data-pass1
           (cert-data-entry-pair :pass1 state)))

; A non-nil value for cert-data-entry-pair is a fast-alist.  If cert-data-pass1
; is true then we are in pass 2 of encapsulate or certify-book; otherwise we
; are including a certified book.  Since redefinition is possible, we avoid the
; temptation to check that no name in names has a non-nil 'type-prescriptions
; property.

      (cond
       ((and cert-data-entry-pair
             (not cert-data-pass1)) ; including a certified book
        (mv-let
          (wrld ttree)
          (cert-data-putprop-type-prescription-lst-for-clique
           (cdr cert-data-entry-pair)
           names
           def-nume
           (length (getpropc (car names) 'runic-mapping-pairs nil wrld))
           ttree ens wrld wrld nil)
          (mv wrld ttree state)))
       (t (let ((bodies (get-normalized-bodies names wrld))
                (big-mutrec (big-mutrec names)))
            (er-let* ((wrld1 (update-w big-mutrec
                                       (putprop-initial-type-prescriptions
                                        names wrld))))
              (guess-and-putprop-type-prescription-lst-for-clique
               names
               bodies
               def-nume
               ens
               wrld1
               ttree
               big-mutrec
               (cdr cert-data-entry-pair)
               state)))))))))

; So that finishes the type-prescription business.  Now to level-no...

(defun putprop-level-no-lst (names wrld)

; We compute the level-no properties for all the fns in names, assuming they
; have no such properties in wrld (i.e., we take advantage of the fact that
; when max-level-no sees a nil 'level-no it acts like it saw 0).  Note that
; induction and rewriting do not use heuristics for 'level-no, so it seems
; reasonable not to recompute the 'level-no property when adding a :definition
; rule with non-nil :install-body value.  We assume that we can get the
; 'recursivep and the 'def-bodies property of each fn in names from wrld.

  (cond ((null names) wrld)
        (t (let ((maximum (max-level-no (body (car names) t wrld) wrld)))
             (putprop-level-no-lst (cdr names)
                                   (putprop (car names)
                                            'level-no
                                            (if (getpropc (car names)
                                                          'recursivep nil wrld)
                                                (1+ maximum)
                                              maximum)
                                            wrld))))))


; Next we put the primitive-recursive-defun property

(defun primitive-recursive-argp (var term wrld)

; Var is some formal of a recursively defined function.  Term is the actual in
; the var position in a recursive call in the definition of the function.
; I.e., we are recursively replacing var by term in the definition.  Is this
; recursion in the p.r. schema?  Well, that is impossible to tell by just
; looking at the recursion, because we need to know that the tests governing
; the recursion are also in the scheme.  In fact, we don't even check that; we
; just rely on the fact that the recursion was justified and so some governing
; test does the job.  So, ignoring tests, what is a p.r. function?  It is one
; in which every formal is replaced either by itself or by an application of a
; (nest of) primitive recursive destructors to itself.  The primitive recursive
; destructors recognized here are all unary function symbols with level-no 0
; (e.g., car, cdr, nqthm::sub1, etc) as well as terms of the form (+ & -n) and
; (+ -n &), where -n is negative.

; A consequence of this definition (before we turned 1+ into a macro) is that
; 1+ is a primitive recursive destructor!  Thus, the classic example of a
; terminating function not in the classic p.r. scheme,
; (fn x y) = (if (< x y) (fn (1+ x) y) 0)
; is now in the "p.r." scheme.  This is a crock!

; Where is this notion used?  The detection that a function is "p.r." is made
; after its admittance during the defun principle.  The appropriate flag is
; stored under the property 'primitive-recursive-defunp.  This property is only
; used (as of this writing) by induction-complexity1, where we favor induction
; candidates suggested by non-"p.r." functions.  Thus, the notion of "p.r." is
; entirely heuristic and only affects which inductions we choose.

; Why don't we define it correctly?  That is, why don't we only recognize
; functions that recurse via car, cdr, etc.?  The problem is the
; introduction of the "NQTHM" package, where we want NQTHM::SUB1 to be a p.r.
; destructor -- even in the defn of NQTHM::LESSP which must happen before we
; prove that NQTHM::SUB1 decreases according to NQTHM::LESSP.  The only way to
; fix this, it seems, would be to provide a world global variable -- perhaps a
; new field in the acl2-defaults-table -- to specify which function symbols are
; to be considered p.r. destructors.  We see nothing wrong with this solution,
; but it seems cumbersome at the moment.  Thus, we adopted this hackish notion
; of "p.r." and will revisit the problem if and when we see counterexamples to
; the induction choices caused by this notion.

  (cond ((variablep term) (eq var term))
        ((fquotep term) nil)
        (t (let ((fn (ffn-symb term)))
             (case
              fn
              (binary-+
               (or (and (nvariablep (fargn term 1))
                        (fquotep (fargn term 1))
                        (rationalp (cadr (fargn term 1)))
                        (< (cadr (fargn term 1)) 0)
                        (primitive-recursive-argp var (fargn term 2) wrld))
                   (and (nvariablep (fargn term 2))
                        (fquotep (fargn term 2))
                        (rationalp (cadr (fargn term 2)))
                        (< (cadr (fargn term 2)) 0)
                        (primitive-recursive-argp var (fargn term 1) wrld))))
              (otherwise
               (and (symbolp fn)
                    (fargs term)
                    (null (cdr (fargs term)))
                    (= (get-level-no fn wrld) 0)
                    (primitive-recursive-argp var (fargn term 1) wrld))))))))

(defun primitive-recursive-callp (formals args wrld)
  (cond ((null formals) t)
        (t (and (primitive-recursive-argp (car formals) (car args) wrld)
                (primitive-recursive-callp (cdr formals) (cdr args) wrld)))))

(defun primitive-recursive-callsp (formals calls wrld)
  (cond ((null calls) t)
        (t (and (primitive-recursive-callp formals (fargs (car calls)) wrld)
                (primitive-recursive-callsp formals (cdr calls) wrld)))))

(defun primitive-recursive-machinep (formals machine wrld)

; Machine is an induction machine for a singly recursive function with
; the given formals.  We return t iff every recursive call in the
; machine has the property that every argument is either equal to the
; corresponding formal or else is a primitive recursive destructor
; nest around that formal.

  (cond ((null machine) t)
        (t (and
            (primitive-recursive-callsp formals
                                        (access tests-and-calls
                                                (car machine)
                                                :calls)
                                        wrld)
            (primitive-recursive-machinep formals (cdr machine) wrld)))))

(defun putprop-primitive-recursive-defunp-lst (names wrld)

; The primitive-recursive-defun property of a function name indicates
; whether the function is defined in the primitive recursive schema --
; or, to be precise, in a manner suggestive of the p.r. schema.  We do
; not actually check for syntactic adherence to the rules and this
; property is of heuristic use only.  See the comment in
; primitive-recursive-argp.

; We say a defun'd function is p.r. iff it is not recursive, or else it
; is singly recursive and every argument position of every recursive call
; is occupied by the corresponding formal or else a nest of primitive
; recursive destructors around the corresponding formal.

; Observe that our notion doesn't include any inspection of the tests
; governing the recursions and it doesn't include any check of the
; subfunctions used.  E.g., the function that collects all the values of
; Ackermann's functions is p.r. if it recurses on cdr's.

  (cond ((null names) wrld)
        ((cdr names) wrld)
        ((primitive-recursive-machinep (formals (car names) wrld)
                                       (getpropc (car names)
                                                 'induction-machine nil wrld)
                                       wrld)
         (putprop (car names)
                  'primitive-recursive-defunp
                  t
                  wrld))
        (t wrld)))

; Onward toward defuns...  Now we generate the controller-alists.

(defun make-controller-pocket (formals vars)

; Given the formals of a fn and a measured subset, vars, of formals,
; we generate a controller-pocket for it.  A controller pocket is a
; list of t's and nil's in 1:1 correspondence with the formals, with
; t in the measured slots.

  (cond ((null formals) nil)
        (t (cons (if (member (car formals) vars)
                     t
                     nil)
                 (make-controller-pocket (cdr formals) vars)))))

(defun make-controller-alist1 (names wrld)

; Given a clique of recursive functions, we return the controller alist built
; for the 'justification.  A controller alist is an alist that maps fns in the
; clique to controller pockets.  The controller pockets describe the measured
; arguments in a justification.  We assume that all the fns in the clique have
; been justified (else none would be justified).

; This function should not be called on a clique consisting of a single,
; non-recursive fn (because it has no justification).

  (cond ((null names) nil)
        (t (cons (cons (car names)
                       (make-controller-pocket
                        (formals (car names) wrld)
                        (access justification
                                (getpropc (car names)
                                          'justification
                                          '(:error
                                            "See MAKE-CONTROLLER-ALIST1.")
                                          wrld)
                                :subset)))
                 (make-controller-alist1 (cdr names) wrld)))))

(defun make-controller-alist (names wrld)

; We store a controller-alists property for every recursive fn in names.  We
; assume we can get the 'formals and the 'justification for each fn from wrld.
; If there is a fn with no 'justification, it means the clique consists of a
; single non-recursive fn and we store no controller-alists.  We generate one
; controller pocket for each fn in names.

; The controller-alist associates a fn in the clique to a controller pocket.  A
; controller pocket is a list in 1:1 correspondence with the formals of the fn
; with a t in slots that are controllers.  The controllers assigned for the fns
; in the clique by a given controller-alist were used jointly in the
; justification of the clique.

  (and (getpropc (car names) 'justification nil wrld)
       (make-controller-alist1 names wrld)))

(defun max-nume-exceeded-error (ctx)
  (er hard ctx
      "ACL2 assumes that no nume exceeds ~x0.  It is very surprising that ~
       this bound is about to be exceeded.  We are causing an error because ~
       for efficiency, ACL2 assumes this bound is never exceeded.  Please ~
       contact the ACL2 implementors with a request that this assumption be ~
       removed from enabled-numep."
      (fixnum-bound)))

(defun putprop-defun-runic-mapping-pairs1 (names def-nume tp-flg ind-flg wrld)

; Names is a list of function symbols.  For each fn in names we store some
; runic mapping pairs.  We always create (:DEFINITION fn) and (:EXECUTABLE-
; COUNTERPART fn).  If tp-flg is t, we create (:TYPE-PRESCRIPTION fn).  If
; ind-flg is t we create (:INDUCTION fn).  However, ind-flg is t only if tp-flg
; is t (that is, tp-flg = nil and ind-flg = t never arises).  Thus, we may
; store 2 (tp-flg = nil; ind-flg = nil), 3 (tp-flg = t; ind-flg = nil), or 4
; (tp-flg = t; ind-flg = t) runes.  As of this writing, we never call this
; function with tp-flg nil but ind-flg t and the function is not prepared for
; that possibility.

; WARNING: Don't change the layout of the runic-mapping-pairs without
; considering all the places that talk about the Essay on the Assignment of
; Runes and Numes by DEFUNS.

  (cond ((null names) wrld)
        (t (putprop-defun-runic-mapping-pairs1
            (cdr names)
            (+ 2 (if tp-flg 1 0) (if ind-flg 1 0) def-nume)
            tp-flg
            ind-flg
            (putprop
             (car names) 'runic-mapping-pairs
             (list* (cons def-nume (list :DEFINITION (car names)))
                    (cons (+ 1 def-nume)
                          (list :EXECUTABLE-COUNTERPART (car names)))
                    (if tp-flg
                        (list* (cons (+ 2 def-nume)
                                     (list :TYPE-PRESCRIPTION (car names)))
                               (if ind-flg
                                   (list (cons (+ 3 def-nume)
                                               (list :INDUCTION (car names))))
                                 nil))
                      nil))
             wrld)))))

(defun putprop-defun-runic-mapping-pairs (names tp-flg wrld)

; Essay on the Assignment of Runes and Numes by DEFUNS

; Names is a clique of mutually recursive function names.  For each
; name in names we store a 'runic-mapping-pairs property.  Each name
; gets either four (tp-flg = t) or two (tp-flg = nil) mapping pairs:

; ((n   . (:definition name))
;  (n+1 . (:executable-counterpart name))
;  (n+2 . (:type-prescription name))        ; only if tp-flg
;  (n+3 . (:induction name)))               ; only if tp-flg and name is
;                                           ;  recursively defined

; where n is the next available nume.  Important aspects to this
; include:
; * Fn-rune-nume knows where the :definition and :executable-counterpart
;   runes are positioned.
; * Several functions (e.g. augment-runic-theory) exploit the fact
;   that the mapping pairs are ordered ascending.
; * function-theory-fn1 knows that if the token of the first rune in
;   the 'runic-mapping-pairs is not :DEFINITION then the base symbol
;   is not a function symbol.
; * Get-next-nume implicitly exploits the fact that the numes are
;   consecutive integers -- it adds the length of the list to
;   the first nume to get the next available nume.
; * Cleanse-type-prescriptions knows that the same number of numes are
;   consumed by each function in a DEFUNS.  We have consistently used
;   the formal parameter def-nume when we were enumerating numes for
;   definitions.
; * Convert-theory-to-unordered-mapping-pairs1 knows that if the first rune in
;   the list is a :definition rune, then the length of this list is 4 if and
;   only if the list contains an :induction rune, in which case that rune is
;   last in the list.

; In short, don't change the layout of this property unless you
; inspect every occurrence of 'runic-mapping-pairs in the system!
; (Even that won't find the def-nume uses.)  Of special note is the
; fact that all non-constrained function symbols are presumed to have
; the same layout of 'runic-mapping-pairs as shown here.  Constrained
; symbols have a nil 'runic-mapping-pairs property.

; We do not allocate the :type-prescription or :induction runes or their numes
; unless tp-flg is non-nil.  This way we can use this same function to
; initialize the 'runic-mapping-pairs for primitives like car and cdr, without
; wasting runes and numes.  We like reusing this function for that purpose
; because it isolates the place we create the 'runic-mapping-pairs for
; functions.

  (let ((next-nume (get-next-nume wrld)))
    (prog2$ (or (<= (the-fixnum next-nume)
                    (- (the-fixnum (fixnum-bound))
                       (the-fixnum (* (the-fixnum 4)
                                      (the-fixnum (length names))))))
                (max-nume-exceeded-error 'putprop-defun-runic-mapping-pairs))
            (putprop-defun-runic-mapping-pairs1
             names
             next-nume
             tp-flg
             (and tp-flg
                  (getpropc (car names) 'recursivep nil wrld))
             wrld))))

; NOTE: Several functions formerly defined here in support of guard
; verification have been moved to history-management.lisp, to support the
; definition of guard-theorem.

; We have to collect every subroutine mentioned by any member of the clique and
; check that its guards have been checked.  We cause an error if not.  Once we
; have checked that all the subroutines have had their guards checked, we
; generate the guard clauses for the new functions.

(defun print-verify-guards-msg (names col state)

; Note that names is either a singleton list containing a theorem name
; or is a mutually recursive clique of function names.

; This function increments timers.  Upon entry, the accumulated time
; is charged to 'other-time.  The time spent in this function is
; charged to 'print-time.

  (cond
   ((ld-skip-proofsp state) state)
   (t
    (pprogn
     (increment-timer 'other-time state)
     (mv-let (col state)
             (io? event nil (mv col state)
                  (col names)
                  (fmt1 "~&0 ~#0~[is~/are~] compliant with Common Lisp.~|"
                        (list (cons #\0 names))
                        col
                        (proofs-co state)
                        state nil)
                  :default-bindings ((col 0)))
             (declare (ignore col))
             (increment-timer 'print-time state))))))

(defun collect-ideals (names wrld acc)
  (cond ((null names) acc)
        ((eq (symbol-class (car names) wrld) :ideal)
         (collect-ideals (cdr names) wrld (cons (car names) acc)))
        (t (collect-ideals (cdr names) wrld acc))))

(defun collect-non-ideals (names wrld)
  (cond ((null names) nil)
        ((eq (symbol-class (car names) wrld) :ideal)
         (collect-non-ideals (cdr names) wrld))
        (t (cons (car names) (collect-non-ideals (cdr names) wrld)))))

(defun collect-non-common-lisp-compliants (names wrld)
  (cond ((null names) nil)
        ((eq (symbol-class (car names) wrld) :common-lisp-compliant)
         (collect-non-common-lisp-compliants (cdr names) wrld))
        (t (cons (car names)
                 (collect-non-common-lisp-compliants (cdr names) wrld)))))

(defun all-fnnames1-exec (flg x acc)

; Keep this in sync with all-fnnames1.  Also see the comment about
; all-fnnames1-exec in put-invariant-risk before modifying this function.

  (cond (flg ; x is a list of terms
         (cond ((null x) acc)
               (t (all-fnnames1-exec nil (car x)
                                     (all-fnnames1-exec t (cdr x) acc)))))
        ((variablep x) acc)
        ((fquotep x) acc)
        ((flambda-applicationp x)
         (all-fnnames1-exec nil (lambda-body (ffn-symb x))
                            (all-fnnames1-exec t (fargs x) acc)))
        ((eq (ffn-symb x) 'return-last)
         (cond ((equal (fargn x 1) '(quote mbe1-raw))
                (all-fnnames1-exec nil (fargn x 2) acc))
               ((and (equal (fargn x 1) '(quote ec-call1-raw))
                     (nvariablep (fargn x 3))
                     (not (fquotep (fargn x 3)))
                     (not (flambdap (ffn-symb (fargn x 3)))))
                (all-fnnames1-exec t (fargs (fargn x 3)) acc))
               (t (all-fnnames1-exec t
                                     (fargs x)
                                     (add-to-set-eq (ffn-symb x) acc)))))
        (t
         (all-fnnames1-exec t (fargs x)
                            (add-to-set-eq (ffn-symb x) acc)))))

(defmacro all-fnnames-exec (term)
  `(all-fnnames1-exec nil ,term nil))

(defun chk-common-lisp-compliant-subfunctions-cmp (names0 names terms wrld str
                                                          ctx)

; See chk-common-lisp-compliant-subfunctions.

  (cond ((null names) (value-cmp nil))
        (t (let ((bad (collect-non-common-lisp-compliants
                       (set-difference-eq (all-fnnames-exec (car terms))
                                          names0)
                       wrld)))
             (cond
              (bad
               (er-cmp ctx "The ~@0 for ~x1 calls the function~#2~[ ~&2~/s ~
                            ~&2~], the guards of which have not yet been ~
                            verified.  See :DOC verify-guards."
                       str (car names) bad))
              (t (chk-common-lisp-compliant-subfunctions-cmp
                  names0 (cdr names) (cdr terms)
                  wrld str ctx)))))))

(defun chk-common-lisp-compliant-subfunctions (names0 names terms wrld str ctx
                                                      state)

; Assume we are defining (or have defined) names with bodies or guards of terms
; (1:1 correspondence).  We wish to make the definitions
; :common-lisp-compliant.  Then we insist that every function used in terms
; other than names0 be :common-lisp-compliant.  Str is a string used in our
; error message and is "guard", "split-types expression", "body" or "auxiliary
; function".  Note that this function is used by chk-acceptable-defuns and by
; chk-acceptable-verify-guards and chk-stobj-field-descriptor.  In the first
; usage, names have not been defined yet; in the other two they have.  So be
; careful about using wrld to get properties of names.

  (cmp-to-error-triple (chk-common-lisp-compliant-subfunctions-cmp
                        names0 names terms wrld str ctx)))

(defun chk-acceptable-verify-guards-formula-cmp (name x ctx wrld state-vars)
  (mv-let (erp term bindings)
    (translate1-cmp x
                    :stobjs-out
                    '((:stobjs-out . :stobjs-out))
                    t ; known-stobjs
                    ctx wrld state-vars)
    (declare (ignore bindings))
    (cond
     ((and erp (null name)) ; erp is a ctx and val is a msg
      (mv-let (erp2 term2 bindings)
        (translate1-cmp x t nil t ctx wrld state-vars)
        (declare (ignore bindings term2))
        (cond
         (erp2 ; translation for formulas fails, so rely on previous error
          (mv erp term))
         (t (er-cmp ctx
                    "The guards for the given formula cannot be verified it ~
                     has the wrong syntactic form for evaluation, perhaps due ~
                     to multiple-value or stobj restrictions.  See :DOC ~
                     verify-guards.")))))
     (erp
      (er-cmp ctx
              "The guards for ~x0 cannot be verified because its formula has ~
               the wrong syntactic form for evaluation, perhaps due to ~
               multiple-value or stobj restrictions.  See :DOC verify-guards."
              (or name x)))
     ((collect-non-common-lisp-compliants (all-fnnames-exec term)
                                          wrld)
      (er-cmp ctx
              "The formula ~#0~[named ~x1~/~x1~] contains a call of the ~
               function~#2~[ ~&2~/s ~&2~], the guards of which have not yet ~
               been verified.  See :DOC verify-guards."
              (if name 0 1)
              (or name x)
              (collect-non-common-lisp-compliants (all-fnnames-exec term)
                                                  wrld)))
     (t
      (value-cmp (cons :term term))))))

(defun chk-acceptable-verify-guards-formula (name x ctx wrld state)
  (cmp-to-error-triple
   (chk-acceptable-verify-guards-formula-cmp name x ctx wrld
                                             (default-state-vars t))))

(defun chk-acceptable-verify-guards-cmp (name rrp ctx wrld state-vars)

; We check that name is acceptable input for verify-guards.  Normally rrp
; ("return redundant p") is t.  In that case, we return either the list of
; names in the clique of name (if name and every peer in the clique is :ideal
; and every subroutine of every peer is :common-lisp-compliant), the symbol
; 'redundant (if name and every peer is :common-lisp-compliant), or cause an
; error.  But if rrp is nil then instead of returning 'redundant -- thus, name
; is :common-lisp-compliant -- we return the list of names in the clique of
; name, as in the :ideal case, but subject to the check for
; :common-lisp-compliant subfunctions that we do in the :ideal case.

; One might wonder when two peers in a clique can have different symbol-classes,
; e.g., how is it possible (as implied above) for name to be :ideal but for one
; of its peers to be :common-lisp-compliant or :program?  Redefinition.  For
; example, the clique could have been admitted as :logic and then later one
; function in it redefined as :program.  Because redefinition invalidates the
; system, we could do anything in this case.  What we choose to do is to cause
; an error and say you can't verify the guards of any of the functions in the
; nest.

  (er-let*-cmp
   ((symbol-class
     (cond ((symbolp name)
            (value-cmp (symbol-class name wrld)))
           (t
            (er-cmp ctx
                    "~x0 is not a symbol.  See :DOC verify-guards."
                    name)))))
   (cond
    ((and rrp
          (eq symbol-class :common-lisp-compliant))
     (value-cmp 'redundant))
    ((getpropc name 'theorem nil wrld)

; Theorems are of either symbol-class :ideal or :common-lisp-compliant.

     (er-progn-cmp
      (chk-acceptable-verify-guards-formula-cmp
       name
       (getpropc name 'untranslated-theorem nil wrld)
       ctx wrld state-vars)
      (value-cmp (list name))))
    ((function-symbolp name wrld)
     (case symbol-class
       (:program
        (er-cmp ctx
                "~x0 is in :program mode.  Only :logic mode functions can ~
                 have their guards verified.  See :DOC verify-guards."
                name))
       ((:ideal :common-lisp-compliant)
        (let* ((recp (getpropc name 'recursivep nil wrld))
               (names (cond
                       ((null recp)
                        (list name))
                       (t recp)))
               (bad-names (if (eq symbol-class :ideal)
                              (collect-non-ideals names wrld)
                            (collect-programs names wrld))))
          (cond (bad-names
                 (er-cmp ctx
                         "One or more of the mutually-recursive peers of ~x0 ~
                          ~#1~[was not defined in :logic mode~/either was not ~
                          defined in :logic mode or has already had its ~
                          guards verified~].  The offending function~#2~[ ~
                          is~/s are~] ~&2.  We thus cannot verify the guards ~
                          of ~x0.  This situation can arise only through ~
                          redefinition."
                         name
                         (if (eq symbol-class :ideal) 1 0)
                         bad-names))
                (t
                 (er-progn-cmp
                  (chk-common-lisp-compliant-subfunctions-cmp
                   names names
                   (guard-lst names nil wrld)
                   wrld "guard" ctx)
                  (chk-common-lisp-compliant-subfunctions-cmp
                   names names
                   (getprop-x-lst names 'unnormalized-body wrld)
                   wrld "body" ctx)
                  (value-cmp names))))))
       (otherwise ; the symbol-class :common-lisp-compliant is handled above
        (er-cmp ctx
                "Implementation error: Unexpected symbol-class, ~x0, for the ~
                 function symbol ~x1."
                symbol-class name))))
    (t (let ((fn (deref-macro-name name (macro-aliases wrld))))
         (er-cmp ctx
                 "~x0 is not a theorem name or a function symbol in the ~
                  current ACL2 world.  ~@1"
                 name
                 (cond ((eq fn name) "See :DOC verify-guards.")
                       (t (msg "Note that ~x0 is a macro-alias for ~x1.  ~
                                Consider calling verify-guards with argument ~
                                ~x1 instead, or use verify-guards+.  See :DOC ~
                                verify-guards, see :DOC verify-guards+, and ~
                                see :DOC macro-aliases-table."
                               name fn)))))))))

(defun chk-acceptable-verify-guards (name rrp ctx wrld state)
  (cmp-to-error-triple
   (chk-acceptable-verify-guards-cmp name rrp ctx wrld
                                     (default-state-vars t))))

(defun guard-obligation-clauses (x guard-debug ens wrld state)

; X is either a list of names corresponding to a defun, mutual-recursion nest,
; or defthm, or else of the form (:term . y) where y is a translated term.
; Returns a set of clauses justifying the guards for y in the latter case, else
; x, together with an assumption-free tag-tree justifying that set of clauses.
; (Do not view this as an error triple!)

  (mv-let (cl-set cl-set-ttree)
    (cond ((and (consp x)
                (eq (car x) :term))
           (mv-let (cl-set cl-set-ttree)
             (guard-clauses+
              (cdr x)
              (and guard-debug :top-level)
              nil ;stobj-optp = nil
              nil ens wrld
              (f-get-global 'safe-mode state)
              (gc-off state)
              nil)
             (mv cl-set cl-set-ttree)))
          ((and (consp x)
                (null (cdr x))
                (getpropc (car x) 'theorem nil wrld))
           (mv-let (cl-set cl-set-ttree)
             (guard-clauses+
              (getpropc (car x) 'theorem nil wrld)
              (and guard-debug (car x))
              nil ;stobj-optp = nil
              nil ens wrld
              (f-get-global 'safe-mode state)
              (gc-off state)
              nil)
             (mv cl-set cl-set-ttree)))
          (t (guard-clauses-for-clique
              x
              (cond ((null guard-debug) nil)
                    ((cdr x) 'mut-rec)
                    (t t))
              ens
              wrld
              (f-get-global 'safe-mode state)

; It is important to turn on guard-checking here.  If we avoid this binding,
; then we can get a hard Lisp error as follows, because a call of
; eval-ground-subexpressions from guard-clauses-for-fn should have failed (due
; to a guard violation) but didn't.  (Since guard-clauses-for-fn isn't called
; in the two cases above for :term and 'theorem, we aren't aware of needing to
; take this extra care in those cases.)

; (set-guard-checking nil)
; (defun foo (x)
;   (declare (xargs :guard (consp x)))
;   (cons x (car 3)))
; (set-guard-checking t)
; (foo '(a b))

; Note that we do not need to bind to :all, since for calls of a guard-verified
; function such as foo, above, t and :all behave the same: if the guard holds
; at the top, then it holds through all evaluation, including recursive calls.

              nil ; gc-off
              nil)))

; Cl-set-ttree is 'assumption-free.

    (mv-let (cl-set cl-set-ttree)
      (clean-up-clause-set cl-set ens wrld cl-set-ttree state)

; Cl-set-ttree is still 'assumption-free.

      (mv cl-set cl-set-ttree))))

(defun guard-obligation (x rrp guard-debug ctx state)
  (let* ((wrld (w state))
         (namep (and (symbolp x)
                     (not (keywordp x))
                     (not (defined-constant x wrld)))))
    (er-let*-cmp
     ((y
       (cond (namep (chk-acceptable-verify-guards-cmp
                     x rrp ctx wrld (default-state-vars t)))
             (t (chk-acceptable-verify-guards-formula-cmp
                 nil x ctx wrld (default-state-vars t))))))
     (cond
      ((and namep (eq y 'redundant))
       (value-cmp :redundant))
      (t (mv-let (cl-set cl-set-ttree)
                 (guard-obligation-clauses y guard-debug (ens state) wrld
                                           state)
                 (value-cmp (list* y cl-set cl-set-ttree))))))))

(defun prove-guard-clauses-msg (names cl-set cl-set-ttree displayed-goal
                                      verify-guards-formula-p state)
  (let ((simp-phrase (tilde-*-simp-phrase cl-set-ttree)))
    (cond
     ((null cl-set)
      (fmt "The guard conjecture for ~#0~[~&1~/the given term~] is trivial to ~
            prove~#2~[~/, given ~*3~].~@4"
           (list (cons #\0 (if names 0 1))
                 (cons #\1 names)
                 (cons #\2 (if (nth 4 simp-phrase) 1 0))
                 (cons #\3 simp-phrase)
                 (cons #\4 (if verify-guards-formula-p "~|" "  ")))
           (proofs-co state)
           state
           nil))
     (t
      (pprogn
       (fms "The non-trivial part of the guard conjecture for ~#0~[~&1~/the ~
             given term~]~#2~[~/, given ~*3,~] is~%~%Goal~%~Q45."
            (list (cons #\0 (if names 0 1))
                  (cons #\1 names)
                  (cons #\2 (if (nth 4 simp-phrase) 1 0))
                  (cons #\3 simp-phrase)
                  (cons #\4 displayed-goal)
                  (cons #\5 (or (term-evisc-tuple nil state)
                                (and (gag-mode)
                                     (let ((tuple
                                            (gag-mode-evisc-tuple state)))
                                       (cond ((eq tuple t)
                                              (term-evisc-tuple t state))
                                             (t tuple)))))))
            (proofs-co state)
            state
            nil)
       (mv 0 ; don't care
           state))))))

(defun verify-guards-formula-fn (x rrp guard-debug state)
  (er-let* ((tuple (cmp-to-error-triple
                    (guard-obligation x rrp guard-debug 'verify-guards-formula
                                      state))))
    (cond ((eq tuple :redundant)
           (value :redundant))
          (t
           (let ((names (car tuple))
                 (displayed-goal (prettyify-clause-set (cadr tuple)
                                                       (let*-abstractionp
                                                        state)
                                                       (w state)))
                 (cl-set-ttree (cddr tuple)))
             (mv-let (col state)
               (prove-guard-clauses-msg (if (and (consp names)
                                                 (eq (car names) :term))
                                            nil
                                          names)
                                        (cadr tuple) cl-set-ttree
                                        displayed-goal t state)
               (declare (ignore col))
               (value :invisible)))))))

(defmacro verify-guards-formula (x &key rrp guard-debug &allow-other-keys)
  `(verify-guards-formula-fn ',x ',rrp ',guard-debug state))

(defun prove-guard-clauses (names hints otf-flg guard-debug ctx ens wrld state)

; Names is either a clique of mutually recursive functions or else a singleton
; list containing a theorem name.  We generate and attempt to prove the guard
; conjectures for the formulas in names.  We generate suitable output
; explaining what we are doing.  This is an error/value/state producing
; function that returns a pair of the form (col . ttree) when non-erroneous.
; Col is the column in which the printer is left.  We always output something
; and we always leave the printer ready to start a new sentence.  Ttree is a
; tag-tree describing the proof.

; This function increments timers.  Upon entry, any accumulated time
; is charged to 'other-time.  The printing done herein is charged
; to 'print-time and the proving is charged to 'prove-time.

  (cond
   ((ld-skip-proofsp state) (value '(0 . nil)))
   (t
    (mv-let
      (cl-set cl-set-ttree state)
      (pprogn (io? event nil state
                   (names)
                   (fms "Computing the guard conjecture for ~&0....~|"
                        (list (cons #\0 names))
                        (proofs-co state)
                        state
                        nil))
              (mv-let (cl-set cl-set-ttree)
                (guard-obligation-clauses names guard-debug ens wrld state)
                (mv cl-set cl-set-ttree state)))

; Cl-set-ttree is 'assumption-free.

      (pprogn
       (increment-timer 'other-time state)
       (let ((displayed-goal (prettyify-clause-set cl-set
                                                   (let*-abstractionp state)
                                                   wrld)))
         (mv-let
           (col state)
           (io? event nil (mv col state)
                (names cl-set cl-set-ttree displayed-goal)
                (prove-guard-clauses-msg names cl-set cl-set-ttree
                                         displayed-goal nil state)
                :default-bindings ((col 0)))
           (pprogn
            (increment-timer 'print-time state)
            (cond
             ((null cl-set)
              (value (cons col cl-set-ttree)))
             (t
              (mv-let (erp ttree state)
                (prove (termify-clause-set cl-set)
                       (make-pspv ens wrld state
                                  :displayed-goal displayed-goal
                                  :otf-flg otf-flg)
                       hints
                       ens wrld ctx state)
                (cond
                 (erp
                  (mv-let
                    (erp1 val state)
                    (er soft ctx
                        "The proof of the guard conjecture for ~&0 has ~
                         failed.  You may wish to avoid specifying a guard, ~
                         or to supply option :VERIFY-GUARDS ~x1 with the ~
                         :GUARD.~@2~|"
                        names
                        nil
                        (if guard-debug
                            ""
                          "  Otherwise, you may wish to specify :GUARD-DEBUG ~
                           T; see :DOC verify-guards."))
                    (declare (ignore erp1))
                    (mv (msg
                         "The proof of the guard conjecture for ~&0 has ~
                          failed; see the discussion above about ~&1.  "
                         names
                         (if guard-debug
                             '(:VERIFY-GUARDS)
                           '(:VERIFY-GUARDS :GUARD-DEBUG)))
                        val
                        state)))
                 (t
                  (mv-let (col state)
                    (io? event nil (mv col state)
                         (names)
                         (fmt "That completes the proof of the guard theorem ~
                               for ~&0.  "
                              (list (cons #\0 names))
                              (proofs-co state)
                              state
                              nil)
                         :default-bindings ((col 0)))
                    (pprogn
                     (increment-timer 'print-time state)
                     (value
                      (cons (or col 0)
                            (cons-tag-trees
                             cl-set-ttree
                             ttree))))))))))))))))))

(defun maybe-remove-invariant-risk (names wrld new-wrld)
  (cond ((endp names) new-wrld)
        (t (let ((new-wrld
                  (if (and (getpropc (car names) 'invariant-risk nil wrld)
                           (equal (guard (car names) t wrld) *t*))
                      (putprop (car names) 'invariant-risk nil new-wrld)
                    new-wrld)))
             (maybe-remove-invariant-risk (cdr names) wrld new-wrld)))))

(defun verify-guards-fn1 (names hints otf-flg guard-debug ctx state)

; This function is called on a clique of mutually recursively defined
; fns whose guards have not yet been verified.  Hints is a properly
; translated hints list.  This is an error/value/state producing
; function.  We cause an error if some subroutine of names has not yet
; had its guards checked or if we cannot prove the guards.  Otherwise,
; the "value" is a pair of the form (wrld .  ttree), where wrld results
; from storing symbol-class :common-lisp-compliant for each name and
; ttree is the ttree proving the guards.

; Note: In a series of conversations started around 13 Jun 94, with Bishop
; Brock, we came up with a new proposal for the form of guard conjectures.
; However, we have decided to delay the experimentation with this proposal
; until we evaluate the new logic of Version 1.8.  But, the basic idea is this.
; Consider two functions, f and g, with guards a and b, respectively.  Suppose
; (f (g x)) occurs in a context governed by q.  Then the current guard
; conjectures are
; (1) q -> (b x)      ; guard for g holds on x
; (2) q -> (a (g x))  ; guard for f holds on (g x)

; Note that (2) contains (g x) and we might need to know that x satisfies the
; guard for g here.  Another way of putting it is that if we have to prove both
; (1) and (2) we might imagine forward chaining through (1) and reformulate (2)
; as (2') q & (b x) -> (a (g x)).

; Now in the days when guards were part of the logic, this was a pretty
; compelling idea because we couldn't get at the definition of (g x) in (2)
; without establishing (b x) and thus formulation (2) forced us to prove
; (1) all over again during the proof of (2).  But it is not clear whether
; we care now, because the smart user will define (g x) to "do the right thing"
; for any x and thus f will approve of (g x).  So it is our expectation that
; this whole issue will fall by the wayside.  It is our utter conviction of
; this that leads us to write this note.  Just in case...

; ++++++++++++++++++++++++++++++
;
; Date: Sun, 2 Oct 94 17:31:10 CDT
; From: kaufmann (Matt Kaufmann)
; To: moore
; Subject: proposal for handling generalized booleans
;
; Here's a pretty simple idea, I think, for handling generalized Booleans.  For
; the rest of this message I'll assume that we are going to implement the
; about-to-be-proposed handling of guards.  This proposal doesn't address
; functions like member, which could be thought of as returning generalized
; booleans but in fact are completely specified (when their guards are met).
; Rather, the problem we need to solve is that certain functions, including EQUAL
; and RATIONALP, only specify the propositional equivalence class of the value
; returned, and no more.  I'll call these "problematic functions" for the rest of
; this note.
;
; The fundamental ideas of this proposal are  as follows.
;
; ====================
;
;  (A) Problematic functions are completely a non-issue except for guard
; verification.  The ACL2 logic specifies Boolean values for functions that are
; specified in dpANS to return generalized Booleans.
;
;  (B) Guard verification will generate not only the current proof obligations,
; but also appropriate proof obligations to show that for all values returned by
; relevant problematic functions, only their propositional equivalence class
; matters.  More on this later.
;
;  (C) If a function is problematic, it had better only be used in propositional
; contexts when used in functions or theorems that are intended to be
; :common-lisp-compliant.  For example, consider the following.
;
;  (defun foo (x y z)
;   (if x
;       (equal y z)
;     (cons y z)))
;
; This is problematic, and we will never be able to use it in a
; :common-lisp-compliant function or formula for other than its propositional
; value (unfortunately).
;
; ====================
;
; Elaborating on (B) above:
;
; So for example, if we're verifying guards on
;
;  (... (foo (rationalp x) ...) ...)
;
; then there will be a proof obligation to show that under the appropriate
; hypotheses (from governing IF tests),
;
;  (implies (and a b)
;          (equal (foo a ...) (foo b ...)))
;
; Notice that I've assumed that a and b are non-NIL.  The other case, where a and
; b are both NIL, is trivial since in that case a and b are equal.
;
; Finally, most of the time no such proof obligation will be generated, because
; the context will make it clear that only the propositional equivalence class
; matters.  In fact, for each function we'll store information that gives
; ``propositional arguments'' of the function:  arguments for which we can be
; sure that only their propositional value matters.  More on this below.
;
; ====================
;
; Here are details.
;
; ====================
;
; 1. Every function will have a ``propositional signature,'' which is a list of
; T's and NIL's.  The CAR of this list is T when the function is problematic.
; The CDR of the list is in 1-1 correspondence with the function's formals (in
; the same order, of course), and indicates whether the formal's value only
; matters propositionally for the value of the function.
;
; For example, the function
;
;  (defun bar (x y z)
;   (if x
;       (equal y z)
;     (equal y nil)))
;
; has a propositional signature of (T T NIL NIL).  The first T represents the
; fact that this function is problematic.  The second T represents the fact that
; only the propositional equivalence class of X is used to compute the value of
; this function.  The two NILs say that Y and Z may have their values used other
; than propositionally.
;
; An argument that corresponds to a value of T will be called a ``propositional
; argument'' henceforth.  An OBSERVATION will be made any time a function is
; given a propositional signature that isn't composed entirely of NILs.
;
;  (2) Propositional signatures will be assigned as follows, presumably hung on
; the 'propositional-signature property of the function.  We intend to ensure
; that if a function is problematic, then the CAR of its propositional signature
; is T.  The converse could fail, but it won't in practice.
;
; a. The primitives will have their values set using a fixed alist kept in sync
; with *primitive-formals-and-guards*, e.g.:
;
;  (defconst *primitive-propositional-signatures*
;   '((equal (t nil nil))
;     (cons (nil nil nil))
;     (rationalp (t nil))
;     ...))
;
; In particular, IF has propositional signature (NIL T NIL NIL):  although IF is
; not problematic, it is interesting to note that its first argument is a
; propositional argument.
;
; b. Defined functions will have their propositional signatures computed as
; follows.
;
; b1. The CAR is T if and only if some leaf of the IF-tree of the body is the
; call of a problematic function.  For recursive functions, the function itself
; is considered not to be problematic for the purposes of this algorithm.
;
; b2. An argument, arg, corresponds to T (i.e., is a propositional argument in
; the sense defined above) if and only if for every subterm for which arg is an
; argument of a function call, arg is a propositional argument of that function.
;
; Actually, for recursive functions this algorithm is iterative, like the type
; prescription algorithm, in the sense that we start by assuming that every
; argument is propositional and iterate, continuing to cut down the set of
; propositional arguments until it stabilizes.
;
; Consider for example:
;
;  (defun atom-listp (lst)
;   (cond ((atom lst) (eq lst nil))
;         (t (and (atom (car lst))
;                 (atom-listp (cdr lst))))))
;
; Since EQ returns a generalized Boolean, ATOM-LISTP is problematic.  Since
; the first argument of EQ is not propositional, ATOM-LISTP has propositional
; signature (T NIL).
;
; Note however that we may want to replace many such calls of EQ as follows,
; since dpANS says that NULL really does return a Boolean [I guess because it's
; sort of synonymous with NOT]:
;
;  (defun atom-listp (lst)
;   (cond ((atom lst) (null lst))
;         (t (and (atom (car lst))
;                 (atom-listp (cdr lst))))))
;
; Now this function is not problematic, even though one might be nervous because
; ATOM is, in fact, problematic.  However, ATOM is in the test of an IF (because
; of how AND is defined).  Nevertheless, the use of ATOM here is of issue, and
; this leads us to the next item.
;
;  (3) Certain functions are worse than merely problematic, in that their value
; may not even be determined up to propositional equivalence class.  Consider for
; example our old favorite:
;
;  (defun bad (x)
;   (equal (equal x x) (equal x x)))
;
; In this case, we can't really say anything at all about the value of BAD, ever.
;
; So, every function is checked that calls of problematic functions in its body
; only occur either at the top-level of its IF structure or in propositional
; argument positions.  This check is done after the computation described in (2)b
; above.
;
; So, the second version of the definition of ATOM-LISTP above,
;
;  (defun atom-listp (lst)
;   (cond ((atom lst) (null lst))
;         (t (and (atom (car lst))
;                 (atom-listp (cdr lst))))))
;
; is OK in this sense, because both calls of ATOM occur in the first argument of
; an IF call, and the first argument of IF is propositional.
;
; Functions that fail this check are perfectly OK as :ideal functions; they just
; can't be :common-lisp-compliant.  So perhaps they should generate a warning
; when submitted as :ideal, pointing out that they can never be
; :common-lisp-compliant.
;
; -- Matt

  (let ((wrld (w state))
        (ens (ens state)))
    (er-let*
     ((pair (prove-guard-clauses names hints otf-flg guard-debug ctx ens wrld
                                 state)))

; Pair is of the form (col . ttree)

     (let* ((col (car pair))
            (ttree1 (cdr pair))
            (wrld1 (maybe-remove-invariant-risk names wrld wrld))
            (wrld2 (putprop-x-lst1 names 'symbol-class
                                   :common-lisp-compliant wrld1)))
       (pprogn
        (print-verify-guards-msg names col state)
        (value (cons wrld2 ttree1)))))))

(defun verify-guards-fn (name state hints otf-flg guard-debug event-form)

; Important Note:  Don't change the formals of this function without
; reading the *initial-event-defmacros* discussion in axioms.lisp.

  (when-logic
   "VERIFY-GUARDS"
   (with-ctx-summarized
    (make-ctx-for-event event-form
                        (cond ((and (null hints)
                                    (null otf-flg))
                               (msg "( VERIFY-GUARDS ~x0)"
                                    name))
                              (t (cons 'verify-guards name))))
    (let ((wrld (w state))
          (event-form (or event-form
                          (list* 'verify-guards
                                 name
                                 (append
                                  (if hints
                                      (list :hints hints)
                                    nil)
                                  (if otf-flg
                                      (list :otf-flg otf-flg)
                                    nil)))))
          (assumep (or (eq (ld-skip-proofsp state) 'include-book)
                       (eq (ld-skip-proofsp state) 'include-book-with-locals)
                       (eq (ld-skip-proofsp state) 'initialize-acl2))))
      (er-let*
       ((names (chk-acceptable-verify-guards name t ctx wrld state)))
       (cond
        ((eq names 'redundant)
         (stop-redundant-event ctx state))
        (t (enforce-redundancy
            event-form ctx wrld
            (er-let*
             ((hints (if assumep
                         (value nil)
                       (translate-hints+
                        (cons "Guard Lemma for" name)
                        hints
                        (default-hints wrld)
                        ctx wrld state)))
              (pair (verify-guards-fn1 names hints otf-flg guard-debug ctx
                                       state)))

; pair is of the form (wrld1 . ttree)

             (er-progn
              (chk-assumption-free-ttree (cdr pair) ctx state)
              (install-event name
                             event-form
                             'verify-guards
                             0
                             (cdr pair)
                             nil
                             nil
                             nil
                             (car pair)
                             state)))))))))))

; That completes the implementation of verify-guards.  We now return
; to the development of defun itself.

; Here is the short-cut used when we are introducing :program functions.
; The super-defun-wart operations are not so much concerned with the
; :program defun-mode as with system functions that need special treatment.

; The wonderful super-defun-wart operations should not, in general, mess with
; the primitive state accessors and updaters.  They have to do with a
; boot-strapping problem that is described in more detail in STATE-STATE in
; axioms.lisp.

; The following table has gives the proper STOBJS-IN and STOBJS-OUT
; settings for the indicated functions.

; Warning: If you ever change this table so that it talks about stobjs other
; than STATE, then reconsider oneify-cltl-code.  These functions assume that if
; stobjs-in from this table is non-nil then special handling of STATE is
; required; or, at least, they did before Version_2.6.

(defconst *super-defun-wart-table*

;         fn                     stobjs-in       stobjs-out

  '((COERCE-STATE-TO-OBJECT      (STATE)         (NIL))
    (COERCE-OBJECT-TO-STATE      (NIL)           (STATE))
    (USER-STOBJ-ALIST            (STATE)         (NIL))
    (UPDATE-USER-STOBJ-ALIST     (NIL STATE)     (STATE))
    (BIG-CLOCK-NEGATIVE-P        (STATE)         (NIL))
    (DECREMENT-BIG-CLOCK         (STATE)         (STATE))
    (STATE-P                     (STATE)         (NIL))
    (OPEN-INPUT-CHANNEL-P        (NIL NIL STATE) (NIL))
    (OPEN-OUTPUT-CHANNEL-P       (NIL NIL STATE) (NIL))
    (OPEN-INPUT-CHANNEL-ANY-P    (NIL STATE)     (NIL))
    (OPEN-OUTPUT-CHANNEL-ANY-P   (NIL STATE)     (NIL))
    (READ-CHAR$                  (NIL STATE)     (NIL STATE))
    (PEEK-CHAR$                  (NIL STATE)     (NIL))
    (READ-BYTE$                  (NIL STATE)     (NIL STATE))
    (READ-OBJECT                 (NIL STATE)     (NIL NIL STATE))
    (READ-ACL2-ORACLE            (STATE)         (NIL NIL STATE))
    (READ-ACL2-ORACLE@PAR        (STATE)         (NIL NIL))
    (READ-RUN-TIME               (STATE)         (NIL STATE))
    (READ-IDATE                  (STATE)         (NIL STATE))
    (LIST-ALL-PACKAGE-NAMES      (STATE)         (NIL STATE))
    (PRINC$                      (NIL NIL STATE) (STATE))
    (WRITE-BYTE$                 (NIL NIL STATE) (STATE))
    (PRINT-OBJECT$-SER           (NIL NIL NIL STATE) (STATE))
    (GET-GLOBAL                  (NIL STATE)     (NIL))
    (BOUNDP-GLOBAL               (NIL STATE)     (NIL))
    (MAKUNBOUND-GLOBAL           (NIL STATE)     (STATE))
    (PUT-GLOBAL                  (NIL NIL STATE) (STATE))
    (GLOBAL-TABLE-CARS           (STATE)         (NIL))
    (T-STACK-LENGTH              (STATE)         (NIL))
    (EXTEND-T-STACK              (NIL NIL STATE) (STATE))
    (SHRINK-T-STACK              (NIL STATE)     (STATE))
    (AREF-T-STACK                (NIL STATE)     (NIL))
    (ASET-T-STACK                (NIL NIL STATE) (STATE))
    (32-BIT-INTEGER-STACK-LENGTH (STATE)         (NIL))
    (EXTEND-32-BIT-INTEGER-STACK (NIL NIL STATE) (STATE))
    (SHRINK-32-BIT-INTEGER-STACK (NIL STATE)     (STATE))
    (AREF-32-BIT-INTEGER-STACK   (NIL STATE)     (NIL))
    (ASET-32-BIT-INTEGER-STACK   (NIL NIL STATE) (STATE))
    (OPEN-INPUT-CHANNEL          (NIL NIL STATE) (NIL STATE))
    (OPEN-OUTPUT-CHANNEL         (NIL NIL STATE) (NIL STATE))
    (GET-OUTPUT-STREAM-STRING$-FN (NIL STATE)    (NIL NIL STATE))
    (CLOSE-INPUT-CHANNEL         (NIL STATE)     (STATE))
    (CLOSE-OUTPUT-CHANNEL        (NIL STATE)     (STATE))
    (SYS-CALL-STATUS             (STATE)         (NIL STATE))))

(defun project-out-columns-i-and-j (i j table)
  (cond
   ((null table) nil)
   (t (cons (cons (nth i (car table)) (nth j (car table)))
            (project-out-columns-i-and-j i j (cdr table))))))

(defconst *super-defun-wart-binding-alist*
  (project-out-columns-i-and-j 0 2 *super-defun-wart-table*))

(defconst *super-defun-wart-stobjs-in-alist*
  (project-out-columns-i-and-j 0 1 *super-defun-wart-table*))

(defun super-defun-wart-bindings (bindings)
  (cond ((null bindings) nil)
        (t (cons (or (assoc-eq (caar bindings)
                               *super-defun-wart-binding-alist*)
                     (car bindings))
                 (super-defun-wart-bindings (cdr bindings))))))

(defun store-stobjs-ins (names stobjs-ins w)
  (cond ((null names) w)
        (t (store-stobjs-ins (cdr names) (cdr stobjs-ins)
                             (putprop (car names) 'stobjs-in
                                      (car stobjs-ins) w)))))

(defun store-super-defun-warts-stobjs-in (names wrld)

; Store the built-in stobjs-in values of the super defuns among names, if any.

  (cond
   ((null names) wrld)
   ((assoc-eq (car names) *super-defun-wart-stobjs-in-alist*)
    (store-super-defun-warts-stobjs-in
     (cdr names)
     (putprop (car names) 'stobjs-in
              (cdr (assoc-eq (car names) *super-defun-wart-stobjs-in-alist*))
              wrld)))
   (t (store-super-defun-warts-stobjs-in (cdr names) wrld))))

(defun collect-old-nameps (names wrld)
  (cond ((null names) nil)
        ((new-namep (car names) wrld)
         (collect-old-nameps (cdr names) wrld))
        (t (cons (car names) (collect-old-nameps (cdr names) wrld)))))

(defun put-invariant-risk1 (new-fns body-fns wrld)
  (cond
   ((endp body-fns) wrld)
   (t (let ((risk-fn

; Risk-fn can be :built-in or a function symbol; see put-invariant-risk.

             (getpropc (car body-fns) 'invariant-risk nil wrld)))
        (cond (risk-fn (putprop-x-lst1 new-fns 'invariant-risk risk-fn wrld))
              (t (put-invariant-risk1 new-fns (cdr body-fns) wrld)))))))

(defun stobjs-guard-only-lst (lst wrld)

; See stobjs-guard-only.  Here we do an unnecessary check that the arglist
; consists of a single variable, simply as an optimization that can avoid the
; world lookup done by stobj-recognizer-p.

  (cond ((endp lst) t)
        (t (and (let ((term (car lst)))
                  (and (nvariablep term)
                       (symbolp (ffn-symb term))
                       (fargs term) ; not nil
                       (null (cdr (fargs term)))
                       (variablep (fargn term 1))
                       (stobj-recognizer-p (ffn-symb term) wrld)))
                (stobjs-guard-only-lst (cdr lst) wrld)))))

(defun stobjs-guard-only (guard wrld)

; This function recognizes when guard is a conjunction of stobj recognizer
; calls.  There are an implicit function and its stobjs-out that we could pass
; in explicitly, but we only call this for executable functions, so there is no
; need to consider the stobjs-out; we already check elsewhere that the guard is
; well-formed, which guarantees that if a term is a call of a stobj recognizer,
; then it must be called on a declared stobj name.

  (stobjs-guard-only-lst (flatten-ands-in-lit guard) wrld))

(defun remove-guard-t (names guards wrld acc)
  (cond ((endp names) acc)
        (t (remove-guard-t (cdr names)
                           (cdr guards)
                           wrld
                           (if (or (equal (car guards) *t*)
                                   (stobjs-guard-only (car guards)
                                                      wrld))
                               acc
                             (cons (car names) acc))))))

(defun put-invariant-risk (names bodies non-executablep symbol-class guards
                                 wrld)

; We want to avoid the following situation: the raw Lisp version of some
; function occurring in bodies leads to an ill-guarded function call that
; causes an ACL2 invariant to become false.

; Each updater f with non-t type or array type that is introduced by defstobj
; or defabsstobj gets an 'invariant-risk property of f.  A built-in function
; may get an 'invariant-risk property; see initialize-invariant-risk.  The
; present function, put-invariant-risk, propagates these 'invariant-risk
; properties up through callers.

; When we call all-fnnames1-exec below, we are ignoring :logic code from mbe
; calls.  To see that this is sound, first note that we are determining when
; there is a risk of bypassing guard checks that would avoid invariant
; violations.  If we are executing :logic code from an mbe call, then we must
; be in the *1* code for a :logic mode function, since :program mode functions
; always execute the :exec code of an mbe call (see oneify), as does raw Lisp
; code.  But invariants are checked (in particular, by checking guards for live
; stobj manipulation) when making *1* calls of :logic mode functions.  There is
; actually one other case that all-fnnames1-exec ignores function symbols in
; the call tree: it does not collect function symbol F from (ec-call (F ...)).
; But in this case, *1*F or *1*F$INLINE is called, and if there is a non-nil
; 'invariant-risk property for F or F$INLINE (respectively), then we trust that
; oneify has laid down suitable *1* code for F (or F$INLINE) to preserve
; invariants, so there is no risk to bypassing guards in the evaluation of
; bodies.

  (cond ((or non-executablep
             (null (get-register-invariant-risk-world wrld)))
         wrld)
        (t (let ((new-fns (if (eq symbol-class :common-lisp-compliant)
                              (remove-guard-t names guards wrld nil)
                            names)))
             (cond
              ((null new-fns) ; optimization
               wrld)
              (t (put-invariant-risk1 new-fns
                                      (all-fnnames1-exec t bodies nil)
                                      wrld)))))))

(defun defuns-fn-short-cut (names docs pairs guards measures split-types-terms
                                  bodies non-executablep ctx wrld state)

; This function is called by defuns-fn when the functions to be defined are
; :program.  It short cuts the normal put-induction-info and other such
; analysis of defuns.  The function essentially makes the named functions look
; like primitives in the sense that they can be used in formulas and they can
; be evaluated on explicit constants but no axioms or rules are available about
; them.  In particular, we do not store 'def-bodies, type-prescriptions, or
; any of the recursion/induction properties normally associated with defuns and
; the prover will not execute them on explicit constants.

; We do take care of the documentation database.

; Like defuns-fn0, this function returns a pair consisting of the new world and
; a tag-tree recording the proofs that were done.

  (declare (ignore docs pairs))
  (er-progn
   (cond
    ((and (null (cdr names))                                 ; single function
          (not (equal (car measures) *no-measure*))          ; explicit measure
          (not (ffnnamep-mod-mbe (car names) (car bodies)))) ; not recursive

; Warning: Keep the test just above in sync with putprop-recursivep-lst, in the
; sense that a measure is legal only for a singly-recursive function or a list
; of at least two functions.

     (maybe-warn-or-error-on-non-rec-measure (car names) ctx wrld state))
    (t (value nil)))
   (let* ((boot-strap-flg (global-val 'boot-strap-flg wrld))
          (wrld0 (cond (non-executablep (putprop-x-lst1 names 'non-executablep
                                                        non-executablep
                                                        wrld))
                       (t wrld)))
          (wrld1 (if boot-strap-flg
                     wrld0
                   (putprop-x-lst2 names 'unnormalized-body bodies wrld0)))
          (wrld2 (put-invariant-risk
                  names
                  bodies
                  non-executablep
                  :program ; symbol-class
                  guards
                  (putprop-x-lst2-unless
                   names 'guard guards *t*
                   (putprop-x-lst2-unless
                    names 'split-types-term split-types-terms *t*
                    (putprop-x-lst1
                     names 'symbol-class :program wrld1))))))
     (value (cons wrld2 nil)))))

; Now we develop the output for the defun event.

(defun print-defun-msg/collect-type-prescriptions (names wrld)

; This function returns two lists, a list of names in names with
; trivial type-prescriptions (i.e., NIL 'type-prescriptions property)
; and an alist that pairs names in names with the term representing
; their (non-trivial) type prescriptions.

  (cond
   ((null names) (mv nil nil))
   (t (mv-let (fns alist)
              (print-defun-msg/collect-type-prescriptions (cdr names) wrld)
              (let ((lst (getpropc (car names) 'type-prescriptions nil wrld)))
                (cond
                 ((null lst)
                  (mv (cons (car names) fns) alist))
                 (t (mv fns
                        (cons
                         (cons (car names)
                               (untranslate
                                (access type-prescription (car lst) :corollary)
                                t wrld))
                         alist)))))))))

(defun print-defun-msg/type-prescriptions1 (alist simp-phrase col state)

; See print-defun-msg/type-prescriptions.  We print out a string of
; phrases explaining the alist produced above.  We return the final
; col and state.  This function used to be a tilde-* phrase, but
; you cannot get the punctuation after the ~xt commands.

  (cond ((null alist) (mv col state))
        ((null (cdr alist))
         (fmt1 "the type of ~xn is described by the theorem ~Pt0.  ~#p~[~/We ~
                used ~*s.~]~|"
               (list (cons #\n (caar alist))
                     (cons #\t (cdar alist))
                     (cons #\0 (term-evisc-tuple nil state))
                     (cons #\p (if (nth 4 simp-phrase) 1 0))
                     (cons #\s simp-phrase))
               col
               (proofs-co state)
               state nil))
        ((null (cddr alist))
         (fmt1 "the type of ~xn is described by the theorem ~Pt0 ~
                and the type of ~xm is described by the theorem ~Ps0.~|"
               (list (cons #\n (caar alist))
                     (cons #\t (cdar alist))
                     (cons #\0 (term-evisc-tuple nil state))
                     (cons #\m (caadr alist))
                     (cons #\s (cdadr alist)))
               col
               (proofs-co state)
               state nil))
        (t
         (mv-let (col state)
                 (fmt1 "the type of ~xn is described by the theorem ~Pt0, "
                       (list (cons #\n (caar alist))
                             (cons #\t (cdar alist))
                             (cons #\0 (term-evisc-tuple nil state)))
                       col
                       (proofs-co state)
                       state nil)
                 (print-defun-msg/type-prescriptions1 (cdr alist) simp-phrase
                                                      col state)))))

(defun print-defun-msg/type-prescriptions (names ttree wrld col state)

; This function prints a description of each non-trivial
; type-prescription for the functions names.  It assumes that at the
; time it is called, it is printing in col.  It returns the final col,
; and the final state.

  (let ((simp-phrase (tilde-*-simp-phrase ttree)))
    (mv-let
      (fns alist)
      (print-defun-msg/collect-type-prescriptions names wrld)
      (cond
       ((null alist)
        (fmt1
         "  We could deduce no constraints on the type of ~#0~[~&0.~/any of ~
          the functions in the clique.~]~#1~[~/  However, in normalizing the ~
          definition~#0~[~/s~] we used ~*2.~]~%"
         (list (cons #\0 names)
               (cons #\1 (if (nth 4 simp-phrase) 1 0))
               (cons #\2 simp-phrase))
         col
         (proofs-co state)
         state nil))
       (fns
        (mv-let
          (col state)
          (fmt1
           "  We could deduce no constraints on the type of ~#f~[~vf,~/any of ~
            ~vf,~] but we do observe that "
           (list (cons #\f fns))
           col
           (proofs-co state)
           state nil)
          (print-defun-msg/type-prescriptions1 alist simp-phrase col state)))
       (t
        (mv-let
          (col state)
          (fmt1
           "  We observe that " nil col (proofs-co state)
           state nil)
          (print-defun-msg/type-prescriptions1 alist simp-phrase
                                               col state)))))))

(defun simple-signaturep (fn wrld)

; A simple signature is one in which no stobjs are involved and the
; output is a single value.

  (and (all-nils (stobjs-in fn wrld))

; We call getprop rather than calling stobjs-out, because this code may run
; with fn = return-last, and the function stobjs-out causes an error in that
; case.  We don't mind treating return-last as an ordinary function here.

       (null (cdr (getpropc fn 'stobjs-out '(nil) wrld)))))

(defun all-simple-signaturesp (names wrld)
  (cond ((endp names) t)
        (t (and (simple-signaturep (car names) wrld)
                (all-simple-signaturesp (cdr names) wrld)))))

(defun print-defun-msg/signatures1 (names wrld state)
  (cond
   ((endp names) state)
   ((not (simple-signaturep (car names) wrld))
    (pprogn
     (fms "~x0 => ~x1."
          (list
           (cons #\0
                 (cons (car names)
                       (prettyify-stobj-flags (stobjs-in (car names) wrld))))
           (cons #\1 (prettyify-stobjs-out

; We call getprop rather than calling stobjs-out, because this code may run
; with fn = return-last, and the function stobjs-out causes an error in that
; case.  We don't mind treating return-last as an ordinary function here.

                      (getpropc (car names) 'stobjs-out '(nil) wrld))))
          (proofs-co state)
          state
          nil)
     (print-defun-msg/signatures1 (cdr names) wrld state)))
   (t (print-defun-msg/signatures1 (cdr names) wrld state))))

(defun print-defun-msg/signatures (names wrld state)
  (cond ((all-simple-signaturesp names wrld)
         state)
        ((cdr names)
         (pprogn
          (fms "The Non-simple Signatures" nil (proofs-co state) state nil)
          (print-defun-msg/signatures1 names wrld state)
          (newline (proofs-co state) state)))
        (t (pprogn
            (print-defun-msg/signatures1 names wrld state)
            (newline (proofs-co state) state)))))


(defun print-defun-msg (names ttree wrld col state)

; Once upon a time this function printed more than just the type
; prescription message.  We've left the function here to handle that
; possibility in the future.  This function returns the final state.

; This function increments timers.  Upon entry, the accumulated time
; is charged to 'other-time.  The time spent in this function is
; charged to 'print-time.

  (cond ((ld-skip-proofsp state)
         state)
        (t
         (io? event nil state
              (names ttree wrld col)
              (pprogn
               (increment-timer 'other-time state)
               (mv-let (erp ttree state)
                 (accumulate-ttree-and-step-limit-into-state ttree :skip state)
                 (declare (ignore erp))
                 (mv-let (col state)
                   (print-defun-msg/type-prescriptions names ttree
                                                       wrld col state)
                   (declare (ignore col))
                   (pprogn
                    (print-defun-msg/signatures names wrld state)
                    (increment-timer 'print-time state)))))))))

(defun get-ignores (lst)
  (cond ((null lst) nil)
        (t (cons (ignore-vars
                  (fourth (car lst)))
                 (get-ignores (cdr lst))))))

(defun get-ignorables (lst)
  (cond ((null lst) nil)
        (t (cons (ignorable-vars
                  (fourth (car lst)))
                 (get-ignorables (cdr lst))))))

(defun irrelevant-vars (dcls)
  (cond ((null dcls) nil)
        ((eq (caar dcls) 'irrelevant)
         (append (cdar dcls) (irrelevant-vars (cdr dcls))))
        (t  (irrelevant-vars (cdr dcls)))))

(defun get-irrelevants (lst)
  (cond ((null lst) nil)
        (t (cons (irrelevant-vars
                  (fourth (car lst)))
                 (get-irrelevants (cdr lst))))))

(defun chk-all-stobj-names (lst msg ctx wrld state)

; Cause an error if any element of lst is not a legal stobj name in wrld.

  (cond ((endp lst) (value nil))
        ((not (stobjp (car lst) t wrld))
         (er soft ctx
             "Every name used as a stobj (whether declared explicitly via the ~
              :STOBJ keyword argument or implicitly via *-notation) must have ~
              been previously defined as a single-threaded object with ~
              defstobj or defabsstobj.  ~x0 is used as stobj name ~#1~[~/in ~
              ~@1 ~]but has not been defined as a stobj."
             (car lst)
             msg))
        (t (chk-all-stobj-names (cdr lst) msg ctx wrld state))))

(defun get-declared-stobj-names (edcls ctx wrld state)

; Each element of edcls is the cdr of a DECLARE form.  We look for the
; ones of the form (XARGS ...) and find the first :stobjs keyword
; value in each such xargs.  We know there is at most one :stobjs
; occurrence in each xargs by chk-dcl-lst.  We union together all the
; values of that keyword, after checking that each value is legal.  We
; return the list of declared stobj names or cause an error.

; Keep this in sync with get-declared-stobjs (which does not do any checking
; and returns a single value).

  (cond ((endp edcls) (value nil))
        ((eq (caar edcls) 'xargs)
         (let* ((temp (assoc-keyword :stobjs (cdar edcls)))
                (lst (cond ((null temp) nil)
                           ((null (cadr temp)) nil)
                           ((atom (cadr temp))
                            (list (cadr temp)))
                           (t (cadr temp)))))
           (cond
            (lst
             (cond
              ((not (symbol-listp lst))
               (er soft ctx
                   "The value specified for the :STOBJS xarg ~
                          must be a true list of symbols and ~x0 is ~
                          not."
                   lst))
              (t (er-progn
                  (chk-all-stobj-names lst
                                       (msg "... :stobjs ~x0 ..."
                                            (cadr temp))
                                       ctx wrld state)
                  (er-let*
                    ((rst (get-declared-stobj-names (cdr edcls)
                                                    ctx wrld state)))
                    (value (union-eq lst rst)))))))
            (t (get-declared-stobj-names (cdr edcls) ctx wrld state)))))
        (t (get-declared-stobj-names (cdr edcls) ctx wrld state))))

(defun get-stobjs-in-lst (lst defun-mode ctx wrld state)

; Lst is a list of ``fives'' as computed in chk-acceptable-defuns.
; Each element is of the form (fn args "doc" edcls body).  We know the
; args are legal arg lists, but nothing else.

; Unless we cause an error, we return a list in 1:1 correspondence
; with lst containing the STOBJS-IN flags for each fn.  This involves
; three steps.  First we recover from the edcls the declared :stobjs.
; We augment those with STATE, if STATE is in formals, which is always
; implicitly a stobj, if STATE is in the formals.  We confirm that all
; the declared stobjs are indeed stobjs in wrld.  Then we compute the
; stobj flags using the formals and the declared stobjs.

  (cond ((null lst) (value nil))
        (t (let ((fn (first (car lst)))
                 (formals (second (car lst))))
             (er-let* ((dcl-stobj-names
                        (get-declared-stobj-names (fourth (car lst))
                                                  ctx wrld state))
                       (dcl-stobj-namesx
                        (cond ((and (member-eq 'state formals)
                                    (not (member-eq 'state dcl-stobj-names)))
                               (er-progn
                                (cond
                                 ((and (eq defun-mode :logic)
                                       (function-symbolp fn wrld))

; In this case, we skip the polite check that state can be a formal without
; declaring it a stobj.  This way, verify-termination can succeed in the case
; that the original :program mode definition was evaluated in a world with
; state-ok but the current definition is not.

                                  (value nil))
                                 (t (chk-state-ok ctx wrld state)))
                                (value (cons 'state dcl-stobj-names))))
                              (t (value dcl-stobj-names)))))

                 (cond
                  ((not (subsetp-eq dcl-stobj-namesx formals))
                   (er soft ctx
                       "The stobj name~#0~[ ~&0 is~/s ~&0 are~] ~
                        declared but not among the formals of ~x1.  ~
                        This generally indicates some kind of ~
                        typographical error and is illegal.  Declare ~
                        only those stobj names listed in the formals. ~
                        The formals list of ~x1 is ~x2."
                       (set-difference-equal dcl-stobj-namesx formals)
                       fn
                       formals))
                  (t (er-let* ((others (get-stobjs-in-lst (cdr lst)
                                                          defun-mode
                                                          ctx wrld state)))

; Note: Wrld is irrelevant below because dcl-stobj-namesx is not T so
; we simply look for the formals that are in dcl-stobj-namesx.

                       (value
                        (cons (compute-stobj-flags formals
                                                   dcl-stobj-namesx
                                                   wrld)
                              others))))))))))

(defun chk-stobjs-out-bound (names bindings ctx state)
  (cond ((null names) (value nil))
        ((translate-unbound (car names) bindings)
         (er soft ctx
             "Translate failed to determine the output signature of ~
              ~x0." (car names)))
        (t (chk-stobjs-out-bound (cdr names) bindings ctx state))))

(defun store-stobjs-out (names bindings w)
  (cond ((null names) w)
        (t (store-stobjs-out
            (cdr names)
            bindings
            (putprop (car names) 'stobjs-out
                     (translate-deref (car names)
                                      bindings) w)))))

(defun unparse-signature (x)

; Suppose x is an internal form signature, i.e., (fn formals stobjs-in
; stobjs-out).  Then we return an external version of it, e.g., ((fn
; . stobjs-in) => (mv . stobjs-out)).  This is only used in error
; reporting.

  (let* ((fn (car x))
         (pretty-flags1 (prettyify-stobj-flags (caddr x)))
         (output (prettyify-stobjs-out (cadddr x))))
    `((,fn ,@pretty-flags1) => ,output)))

(defun chk-defun-mode (defun-mode ctx state)
  (cond ((eq defun-mode :program)
         (value nil))
        ((eq defun-mode :logic)

; We do the check against the value of state global 'program-fns-with-raw-code
; in redefinition-renewal-mode, so that we do it only when reclassifying.

         (value nil))
        (t (er soft ctx
               "The legal defun-modes are :program and :logic.  ~x0 is ~
                not a recognized defun-mode."
               defun-mode))))

(defun scan-to-cltl-command (wrld)

; Scan to the next binding of 'cltl-command or to the end of this event block.
; Return either nil or the global-value of cltl-command for this event.

  (declare (xargs :guard (plist-worldp wrld)))
  (cond ((endp wrld) nil)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value))
         nil)
        ((and (eq (caar wrld) 'cltl-command)
              (eq (cadar wrld) 'global-value))
         (cddar wrld))
        (t (scan-to-cltl-command (cdr wrld)))))

(defconst *xargs-keywords*

; Keep this in sync with :doc xargs.

  '(:guard :guard-hints :guard-debug
           :hints :measure :measure-debug
           :ruler-extenders :mode :non-executable :normalize
           :otf-flg #+:non-standard-analysis :std-hints
           :stobjs :verify-guards :well-founded-relation
           :split-types))

(defun plausible-dclsp1 (lst)

; We determine whether lst is a plausible cdr for a DECLARE form.  Ignoring the
; order of presentation and the number of occurrences of each element
; (including 0), we ensure that lst is of the form (... (TYPE ...) ... (IGNORE
; ...) ... (IGNORABLE ...) ... (IRRELEVANT ...) ... (XARGS ... :key val ...)
; ...)  where the :keys are our xarg keys (members of *xargs-keywords*).

  (declare (xargs :guard t))
  (cond ((atom lst) (null lst))
        ((and (consp (car lst))
              (true-listp (car lst))
              (or (member-eq (caar lst) '(type ignore ignorable irrelevant))
                  (and (eq (caar lst) 'xargs)
                       (keyword-value-listp (cdar lst))
                       (subsetp-eq (evens (cdar lst)) *xargs-keywords*))))
         (plausible-dclsp1 (cdr lst)))
        (t nil)))

(defun plausible-dclsp (lst)

; We determine whether lst is a plausible thing to include between the formals
; and the body in a defun, e.g., a list of doc strings and DECLARE forms.  We
; do not insist that the DECLARE forms are "perfectly legal" -- for example, we
; would approve (DECLARE (XARGS :measure m1 :measure m2)) -- but they are
; well-enough formed to permit us to walk through them with the fetch-from-dcls
; functions below.

; Note: This predicate is not actually used by defuns but is used by
; verify-termination in order to guard its exploration of the proposed dcls to
; merge them with the existing ones.  After we define the predicate we define
; the exploration functions, which assume this fn as their guard.  The
; exploration functions below are used in defuns, in particular, in the
; determination of whether a proposed defun is redundant.

  (declare (xargs :guard t))
  (cond ((atom lst) (null lst))
        ((stringp (car lst)) (plausible-dclsp (cdr lst)))
        ((and (consp (car lst))
              (eq (caar lst) 'declare)
              (plausible-dclsp1 (cdar lst)))
         (plausible-dclsp (cdr lst)))
        (t nil)))

; The above function, plausible-dclsp, is the guard and the role model for the
; following functions which explore plausible-dcls and either collect all the
; "fields" used or delete certain fields.

(defun dcl-fields1 (lst)
  (declare (xargs :guard (plausible-dclsp1 lst)))
  (cond ((endp lst) nil)
        ((member-eq (caar lst) '(type ignore ignorable))
         (add-to-set-eq (caar lst) (dcl-fields1 (cdr lst))))
        (t (union-eq (evens (cdar lst)) (dcl-fields1 (cdr lst))))))

(defun dcl-fields (lst)

; Lst satisfies plausible-dclsp, i.e., is the sort of thing you would find
; between the formals and the body of a DEFUN.  We return a duplicate-free list
; of all the "field names" used in lst, where 'comment indicates a string.  Our
; answer is a subset of the union of the values of '(comment type ignore
; ignorable irrelevant) and *xargs-keywords*.

  (declare (xargs :guard (plausible-dclsp lst)))
  (cond ((endp lst) nil)
        ((stringp (car lst))
         (add-to-set-eq 'comment (dcl-fields (cdr lst))))
        (t (union-eq (dcl-fields1 (cdar lst))
                     (dcl-fields (cdr lst))))))

(defun strip-keyword-list (fields lst)

; Lst is a keyword-value-listp, i.e., (:key1 val1 ...).  We remove any key/val
; pair whose key is in fields.

  (declare (xargs :guard (and (symbol-listp fields)
                              (keyword-value-listp lst))))
  (cond ((endp lst) nil)
        ((member-eq (car lst) fields)
         (strip-keyword-list fields (cddr lst)))
        (t (cons (car lst)
                 (cons (cadr lst)
                       (strip-keyword-list fields (cddr lst)))))))

(defun strip-dcls1 (fields lst)
  (declare (xargs :guard (and (symbol-listp fields)
                              (plausible-dclsp1 lst))))
  (cond ((endp lst) nil)
        ((member-eq (caar lst) '(type ignore ignorable irrelevant))
         (cond ((member-eq (caar lst) fields) (strip-dcls1 fields (cdr lst)))
               (t (cons (car lst) (strip-dcls1 fields (cdr lst))))))
        (t
         (let ((temp (strip-keyword-list fields (cdar lst))))
           (cond ((null temp) (strip-dcls1 fields (cdr lst)))
                 (t (cons (cons 'xargs temp)
                          (strip-dcls1 fields (cdr lst)))))))))

(defun strip-dcls (fields lst)

; Lst satisfies plausible-dclsp.  Fields is a list as returned by dcl-fields,
; i.e., a subset of the union of the values of '(comment type ignore ignorable
; irrelevant) and *xargs-keywords*.  We copy lst deleting any part of it that
; specifies a value for one of the fields named, where 'comment denotes a
; string.  The result satisfies plausible-dclsp.

  (declare (xargs :guard (and (symbol-listp fields)
                              (plausible-dclsp lst))))
  (cond ((endp lst) nil)
        ((stringp (car lst))
         (cond ((member-eq 'comment fields) (strip-dcls fields (cdr lst)))
               (t (cons (car lst) (strip-dcls fields (cdr lst))))))
        (t (let ((temp (strip-dcls1 fields (cdar lst))))
             (cond ((null temp) (strip-dcls fields (cdr lst)))
                   (t (cons (cons 'declare temp)
                            (strip-dcls fields (cdr lst)))))))))

(defun fetch-dcl-fields2 (field-names kwd-list acc)
  (declare (xargs :guard (and (symbol-listp field-names)
                              (keyword-value-listp kwd-list))))
  (cond ((endp kwd-list)
         acc)
        (t (let ((acc (fetch-dcl-fields2 field-names (cddr kwd-list) acc)))
             (if (member-eq (car kwd-list) field-names)
                 (cons (cadr kwd-list) acc)
               acc)))))

(defun fetch-dcl-fields1 (field-names lst)
  (declare (xargs :guard (and (symbol-listp field-names)
                              (plausible-dclsp1 lst))))
  (cond ((endp lst) nil)
        ((member-eq (caar lst) '(type ignore ignorable irrelevant))
         (if (member-eq (caar lst) field-names)
             (cons (cdar lst) (fetch-dcl-fields1 field-names (cdr lst)))
           (fetch-dcl-fields1 field-names (cdr lst))))
        (t (fetch-dcl-fields2 field-names (cdar lst)
                             (fetch-dcl-fields1 field-names (cdr lst))))))

(defun fetch-dcl-fields (field-names lst)
  (declare (xargs :guard (and (symbol-listp field-names)
                              (plausible-dclsp lst))))
  (cond ((endp lst) nil)
        ((stringp (car lst))
         (if (member-eq 'comment field-names)
             (cons (car lst) (fetch-dcl-fields field-names (cdr lst)))
           (fetch-dcl-fields field-names (cdr lst))))
        (t (append (fetch-dcl-fields1 field-names (cdar lst))
                   (fetch-dcl-fields field-names (cdr lst))))))

(defun fetch-dcl-field (field-name lst)

; Lst satisfies plausible-dclsp, i.e., is the sort of thing you would find
; between the formals and the body of a DEFUN.  Field-name is either in the
; list (comment type ignore ignorable irrelevant) or is one of the symbols in
; the list *xargs-keywords*.  We return the list of the contents of all fields
; with that name.  We assume we will find at most one specification per XARGS
; entry for a given keyword.

; For example, if field-name is :GUARD and there are two XARGS among the
; DECLAREs in lst, one with :GUARD g1 and the other with :GUARD g2 we return
; (g1 g2).  Similarly, if field-name is TYPE and lst contains (DECLARE (TYPE
; INTEGER X Y)) then our output will be (... (INTEGER X Y) ...) where the ...
; are the other TYPE entries.

  (declare (xargs :guard (and (symbolp field-name)
                              (plausible-dclsp lst))))
  (fetch-dcl-fields (list field-name) lst))

(defun set-equalp-eq (lst1 lst2)
  (declare (xargs :guard (and (true-listp lst1)
                              (true-listp lst2)
                              (or (symbol-listp lst1)
                                  (symbol-listp lst2)))))
  (and (subsetp-eq lst1 lst2)
       (subsetp-eq lst2 lst1)))

(defun non-identical-defp-chk-measures (name new-measures old-measures
                                             justification)
  (cond
   ((equal new-measures old-measures)
    nil)
   (t

; We could try harder, by translating the new measure and seeing if the set of
; free variables is the same as the old measured subset.  But as Sandip Ray
; points out, it might be odd for the new "measure" to be allowed when in fact
; we have proved nothing about it!  Also, the new measure would have to be
; translated in order to get its free variables, and we prefer not to pay that
; price (though perhaps it's quite minor).  Bottom line: we see no reason for
; anyone to expect a definition to be redundant with an earlier one that has a
; different measure.

    (let ((old-measured-subset
           (assert$
            justification

; Old-measured-subset is used only if chk-measure-p is true.  In that case, if
; the existing definition is non-recursive then we treat the measured subset as
; nil.

            (access justification justification :subset))))
      (cond
       ((and (consp new-measures)
             (null (cdr new-measures))
             (let ((new-measure (car new-measures)))
               (or (equal new-measure (car old-measures))
                   (and (true-listp new-measure)
                        (eq (car new-measure) :?)
                        (arglistp (cdr new-measure))
                        (set-equalp-eq old-measured-subset
                                       (cdr new-measure))))))
        nil)
       (old-measures
        (msg "the proposed and existing definitions for ~x0 differ on their ~
              measures.  The existing measure is ~x1.  The new measure needs ~
              to be specified explicitly with :measure (see :DOC xargs), ~
              either to be identical to the existing measure or to be a call ~
              of :? on the measured subset; for example, ~x2 will serve as ~
              the new :measure."
             name
             (car old-measures)
             (cons :? old-measured-subset)))
       (t
        (msg "the existing definition for ~x0 does not have an explicitly ~
              specified measure.  Either remove the :measure declaration from ~
              your proposed definition, or else specify a :measure that ~
              applies :? to the existing measured subset, for example, ~x1."
             name
             (cons :? old-measured-subset))))))))

(defun non-identical-defp (def1 def2 chk-measure-p wrld)

; This predicate is used in recognizing redundant definitions.  In our intended
; application, def2 will have been successfully processed and def1 is merely
; proposed, where def1 and def2 are each of the form (fn args ...dcls... body)
; and everything is untranslated.  Two such tuples are "identical" if their
; fns, args, bodies, types, stobjs, guards, and (if chk-measure-p is true)
; measures are equal -- except that the new measure can be (:? v1 ... vk) if
; (v1 ... vk) is the measured subset for the old definition.  We return nil if
; def1 is thus redundant with ("identical" to) def2.  Otherwise we return a
; message suitable for printing using " Note that ~@k.".

; Note that def1 might actually be syntactically illegal, e.g., it might
; specify two different :measures.  But it is possible that we will still
; recognize it as identical to def2 because the args and body are identical.
; Thus, the syntactic illegality of def1 might not be discovered if def1 is
; avoided because it is redundant.  This happens already in redundancy checking
; in defthm: a defthm event is redundant if it introduces an identical theorem
; with the same name -- even if the :hints in the new defthm are ill-formed.
; The idea behind redundancy checking is to allow books to be loaded even if
; they share some events.

; Should we do any checks here related to the :subversive-p field of the
; justification for def2?  The concern is that def2 (the old definition) is
; subversive but local, and def1 (the new definition) is not subversive and is
; non-local.  But the notion of "subversive" is handled just as well in pass2
; as in pass1, so ultimately def1 will be marked correctly on its
; subversiveness.

  (let* ((justification (and chk-measure-p ; optimization
                             (getpropc (car def2) 'justification nil wrld)))
         (all-but-body1 (butlast (cddr def1) 1))
         (all-but-body2 (butlast (cddr def2) 1))

; We insist on the syntactic identity of the :ruler-extenders, and then check
; that the default ruler-extenders in the two cases do not ruin the equality of
; the two ruler-extenders.  Default ruler-extenders may ruin that equality only
; if both definitions have no explicit ruler-extenders.

         (ruler-extenders1-lst (fetch-dcl-field :ruler-extenders
                                                all-but-body1))
         (ruler-extenders2-lst (fetch-dcl-field :ruler-extenders
                                                all-but-body2)))
    (cond
     ((and justification
           (or (not (equal ruler-extenders1-lst ruler-extenders2-lst))
               (and (null ruler-extenders1-lst)
                    (not (equal (access justification
                                        justification
                                        :ruler-extenders)
                                (default-ruler-extenders wrld))))))
      (msg "the proposed and existing definitions for ~x0 differ on their ~
            ruler-extenders (see :DOC ruler-extenders).  The proposed ~
            ruler-extenders value does not match the existing ruler-extenders ~
            for ~x0, namely, ~x1."
           (car def1)
           (access justification justification :ruler-extenders)))
     ((equal def1 def2) ; optimization
      nil)
     ((not (eq (car def1) (car def2))) ; check same fn (can this fail?)
      (msg "the name of the new event, ~x0, differs from the name of the ~
            corresponding existing event, ~x1."
           (car def1) (car def2)))
     ((not (equal (cadr def1) (cadr def2))) ; check same args
      (msg "the proposed argument list for ~x0, ~x1, differs from the ~
            existing argument list, ~x2."
           (car def1) (cadr def1) (cadr def2)))
     ((not (equal (car (last def1)) (car (last def2)))) ; check same body
      (msg "the proposed body for ~x0,~|~%~p1,~|~%differs from the existing ~
            body,~|~%~p2.~|~%"
           (car def1) (car (last def1)) (car (last def2))))
     ((not (equal (fetch-dcl-field :non-executable all-but-body1)
                  (fetch-dcl-field :non-executable all-but-body2)))
      (msg "the proposed and existing definitions for ~x0 differ on their ~
                :non-executable declarations."
           (car def1)))
     ((flet ((normalize-value
              (x)
              (cond ((equal x '(nil))
                     nil)
                    ((or (equal x '(t))
                         (null x))
                     t)
                    (t (er hard 'non-identical-defp
                           "Internal error: Unexpected value when ~
                                processing :normalize xargs keyword, ~x0.  ~
                                Please contact the ACL2 implementors."
                           x)))))
            (not (equal (normalize-value
                         (fetch-dcl-field :normalize all-but-body1))
                        (normalize-value
                         (fetch-dcl-field :normalize all-but-body2)))))
      (msg "the proposed and existing definitions for ~x0 differ on the ~
                values supplied by :normalize declarations."
           (car def1)))
     ((not (let ((stobjs1 (fetch-dcl-field :stobjs all-but-body1))
                 (stobjs2 (fetch-dcl-field :stobjs all-but-body2)))
             (or (equal stobjs1 stobjs2) ; optimization

; Quoting :doc xargs: "The only exception to this rule is state: whether you
; include it or not, state is always treated as a single-threaded object."
; If the two definitions are identical except for how state is declared as a
; stobj, then since the old definition was acceptable, so is the new one.

                 (equal (remove1-eq 'state stobjs1)
                        (remove1-eq 'state stobjs2)))))

; We insist that the :STOBJS of the two definitions be identical.  Vernon
; Austel pointed out the following bug.

; Define a :program mode function with a non-stobj argument.
;          (defun stobjless-fn (stobj-to-be)
;            (declare (xargs :mode :program))
;            stobj-to-be)
; Use it in the definition of another :program mode function.
;          (defun my-callee-is-stobjless (x)
;            (declare (xargs :mode :program))
;            (stobjless-fn x))
; Then introduce a the argument name as a stobj:
;          (defstobj stobj-to-be
;            (a-field :type integer :initially 0))
; And reclassify the first function into :logic mode.
;          (defun stobjless-fn (stobj-to-be)
;            (declare (xargs :stobjs stobj-to-be))
;            stobj-to-be)
; If you don't notice the different use of :stobjs then the :program
; mode function my-callee-is-stobjless [still] treats the original
; function as though its argument were NOT a stobj!  For example,
; (my-callee-is-stobjless 3) is a well-formed :program mode term
; that treats 3 as a stobj.

      (msg "the proposed and existing definitions for ~x0 differ on their ~
                :stobj declarations."
           (car def1)))
     ((not (equal (fetch-dcl-field 'type all-but-body1)
                  (fetch-dcl-field 'type all-but-body2)))

; Once we removed the restriction that the type and :guard fields of the defs
; be equal.  But imagine that we have a strong guard on foo in our current ACL2
; session, but that we then include a book with a much weaker guard.  (Horrors!
; What if the new guard is totally unrelated!?)  If we didn't make the tests
; below, then presumably the guard on foo would be unchanged by this
; include-book.  Suppose that in this book, we have verified guards for a
; function bar that calls foo.  Then after including the book, it will look as
; though correctly guarded calls of bar always generate only correctly guarded
; calls of foo, but now that foo has a stronger guard than it did when the book
; was certified, this might not always be the case.

      (msg "the proposed and existing definitions for ~x0 differ on their ~
                type declarations."
           (car def1)))
     ((let* ((guards1 (fetch-dcl-field :guard all-but-body1))
             (guards1-trivial-p (or (null guards1) (equal guards1 '(t))))
             (guards2 (fetch-dcl-field :guard all-but-body2))
             (guards2-trivial-p (or (null guards2) (equal guards2 '(t)))))

; See the comment above on type and :guard fields.  Here, we comprehend the
; fact that omission of a guard is equivalent to :guard t.  Of course, it is
; also equivalent to :guard 't and even to :guard (not nil), but we see no need
; to be that generous with our notion of redundancy.

        (cond ((and guards1-trivial-p guards2-trivial-p)
               nil)
              ((not (equal guards1 guards2))
               (msg "the proposed and existing definitions for ~x0 differ ~
                         on their :guard declarations."
                    (car def1)))

; So now we know that the guards are equal and non-trivial.  If the types are
; non-trivial too then we need to make sure that the combined order of guards
; and types for each definition are in agreement.  The following example shows
; what can go wrong without that check.

; (encapsulate
;  ()
;  (local (defun foo (x)
;           (declare (xargs :guard (consp x)))
;           (declare (xargs :guard (consp (car x))))
;           x))
;  (defun foo (x)
;    (declare (xargs :guard (consp (car x))))
;    (declare (xargs :guard (consp x)))
;    x))
;
; (foo 3) ; hard raw Lisp error!

              ((not (equal (fetch-dcl-fields '(type :guard) all-but-body1)
                           (fetch-dcl-fields '(type :guard)
                                             all-but-body2)))
               (msg "although the proposed and existing definitions for ~
                         ~x0 agree on the their type and :guard declarations, ~
                         they disagree on the combined orders of those ~
                         declarations.")))))
     ((let ((split-types1 (fetch-dcl-field :split-types all-but-body1))
            (split-types2 (fetch-dcl-field :split-types all-but-body2)))
        (or (not (eq (all-nils split-types1) (all-nils split-types2)))

; Catch the case of illegal values in the proposed definition.

            (not (boolean-listp split-types1))
            (and (member-eq nil split-types1)
                 (member-eq t split-types1))))
      (msg "the proposed and existing definitions for ~x0 differ on their ~
                :split-types declarations."
           (car def1)))
     ((not chk-measure-p)
      nil)
     ((null justification)

; The old definition (def2) was non-recursive.  Then since the names and bodies
; are identical (as checked above), the new definition (def1) is also
; non-recursive.  In this case we don't care about the measures; see the
; comment above about "syntactically illegal".

      nil)
     (t
      (non-identical-defp-chk-measures
       (car def1)
       (fetch-dcl-field :measure all-but-body1)
       (fetch-dcl-field :measure all-but-body2)
       justification)))))

(defun identical-defp (def1 def2 chk-measure-p wrld)

; This function is probably obsolete -- superseded by non-identical-defp -- but
; we leave it here for reference by comments.

  (not (non-identical-defp def1 def2 chk-measure-p wrld)))

(defun redundant-or-reclassifying-defunp0 (defun-mode symbol-class
                                            ld-skip-proofsp chk-measure-p def
                                            wrld)

; See redundant-or-reclassifying-defunp.  This function has the same behavior
; as that one, except in this one, if parameter chk-measure-p is nil, then
; measure checking is suppressed.

  (cond ((function-symbolp (car def) wrld)
         (let* ((wrld1 (decode-logical-name (car def) wrld))
                (name (car def))
                (val (scan-to-cltl-command (cdr wrld1)))
                (chk-measure-p
                 (and chk-measure-p

; If we are skipping proofs, then we do not need to check the measure.  Why
; not?  One case is that we are explicitly skipping proofs (with skip-proofs,
; rebuild, set-ld-skip-proofsp, etc.; or, inclusion of an uncertified book), in
; which case all bets are off.  Otherwise we are including a certified book,
; where the measured subset was proved correct.  This observation satisfies our
; concern, which is that the current redundant definition will ultimately
; become the actual definition because the earlier one is local.

                      (not ld-skip-proofsp)

; A successful redundancy check may require that the untranslated measure is
; identical to that of the earlier corresponding defun.  Without such a check
; we can store incorrect induction information, as exhibited by the "soundness
; bug in the redundancy criterion for defun events" mentioned in :doc
; note-3-0-2.  The following examples, which work with Version_3.0.1 but
; (fortunately) not afterwards, build on the aforementioned proof of nil given
; in :doc note-3-0-2, giving further weight to our insistence on the same
; measure if the mode isn't changing from :program to :logic.

; The following example involves redundancy only for :program mode functions.

;  (encapsulate
;   ()
;
;   (local (defun foo (x y)
;            (declare (xargs :measure (acl2-count y) :mode :program))
;            (if (and (consp x) (consp y))
;                (foo (cons x x) (cdr y))
;              y)))
;
;   (defun foo (x y)
;     (declare (xargs :mode :program))
;     (if (and (consp x) (consp y))
;         (foo (cons x x) (cdr y))
;       y))
;
;   (verify-termination foo))
;
;  (defthm bad
;    (atom x)
;    :rule-classes nil
;    :hints (("Goal" :induct (foo x '(3)))))
;
;  (defthm contradiction
;    nil
;    :rule-classes nil
;    :hints (("Goal" :use ((:instance bad (x '(7)))))))

; Note that even though we do not store induction schemes for mutual-recursion,
; the following variant of the first example shows that we still need to check
; measures in that case:

;  (set-bogus-mutual-recursion-ok t) ; ease construction of example
;
;  (encapsulate
;   ()
;   (local (encapsulate
;           ()
;
;           (local (mutual-recursion
;                   (defun bar (x) x)
;                   (defun foo (x y)
;                     (declare (xargs :measure (acl2-count y)))
;                     (if (and (consp x) (consp y))
;                         (foo (cons x x) (cdr y))
;                       y))))
;
;           (mutual-recursion
;            (defun bar (x) x)
;            (defun foo (x y)
;              (if (and (consp x) (consp y))
;                  (foo (cons x x) (cdr y))
;                y)))))
;   (defun foo (x y)
;     (if (and (consp x) (consp y))
;         (foo (cons x x) (cdr y))
;       y)))
;
;  (defthm bad
;    (atom x)
;    :rule-classes nil
;    :hints (("Goal" :induct (foo x '(3)))))
;
;  (defthm contradiction
;    nil
;    :rule-classes nil
;    :hints (("Goal" :use ((:instance bad (x '(7))))))) ; |

; After Version_3.4 we no longer concern ourselves with the measure in the case
; of :program mode functions, as we now explain.

; Since verify-termination is now just a macro for make-event, we may view the
; :measure of a :program mode function as nothing more than a hint for use by
; that make-event.  So we need think only about definitions (defun, defuns).
; Note that the measure for a :logic mode definition will always come lexically
; from that definition.  So for redundancy, soundness only requires that the
; measured subsets agree when the old and new definitions are both in :logic
; mode.  We can even change the measure from an existing :program mode
; definition to produce a new :program mode definition, so as to provide a
; better hint for a later verify-termination call.

; One might think that we should do the measures check when the old definition
; is :logic and the new one is :program.  But in that case, either the new one
; is redundant or ultimately in :program mode (if the first is local and the
; second is installed on a second pass).  Either way, there is no concern: if
; the definition is installed, it will be in program mode and hence its measure
; presents no concern for soundness.

                      (eq (cadr val) :logic)
                      (eq defun-mode :logic))))

; The 'cltl-command val for a defun is (defuns :defun-mode ignorep . def-lst)
; where :defun-mode is a keyword (rather than nil which means this was an
; encapsulate or was :non-executable).

           (cond ((null val) nil)
                 ((and (consp val)
                       (eq (car val) 'defuns)
                       (keywordp (cadr val)))
                  (cond
                   ((non-identical-defp def
                                        (assoc-eq name (cdddr val))
                                        chk-measure-p
                                        wrld))

; Else, this cltl-command contains a member of def-lst that is identical to
; def.

                   ((eq (cadr val) defun-mode)
                    (cond ((and (eq symbol-class :common-lisp-compliant)
                                (eq (symbol-class name wrld) :ideal))

; The following produced a hard error in v2-7, because the second defun was
; declared redundant on the first pass and then installed as
; :common-lisp-compliant on the second pass:

; (encapsulate nil
;   (local
;     (defun foo (x) (declare (xargs :guard t :verify-guards nil)) (car x)))
;   (defun foo (x) (declare (xargs :guard t)) (car x)))
; (thm (equal (foo 3) xxx))

; The above example was derived from one sent by Jared Davis, who proved nil in
; an early version of v2-8 by exploiting this idea to trick ACL2 into
; considering guards verified for a function employing mbe.

; Here, we prevent such promotion of :ideal to :common-lisp-compliant.

                           'verify-guards)

; The next potential COND branch would avoid redundancy when downgrading from
; :common-lisp-compliant to :ideal.  But it is commented out, because there
; were many regression failures; see GitHub Issue 582.

;                           ((and (eq symbol-class :ideal)
;                                 (eq (symbol-class name wrld)
;                                     :common-lisp-compliant))
;
; ; We have returned 'redundant in this case, but we now realize that doing so
; ; could be problematic.  Consider a book with the following events.  If the
; ; second definition of foo is redundant on the first pass of certify-book,
; ; then bar will produce an error on the second pass because foo is not
; ; :common-lisp-compliant at that time.
;
; ;   (local
; ;    (defun foo (x)
; ;      (declare (xargs :guard t :verify-guards t))
; ;      x))
; ;
; ;   (defun foo (x)
; ;     (declare (xargs :guard t :verify-guards nil))
; ;     x)
; ;
; ;   (defun bar (x)
; ;     (declare (xargs :guard t))
; ;     (foo x))
;
; ; Out of courtesy, given this change to long-standing behavior, we print an
; ; explanatory message.
;
;                            (msg "it is not redundant to provide a new ~
;                                  definition that specifies the removal of ~
;                                  guard-verified status."))

                          (t 'redundant)))
                   ((and (eq (cadr val) :program)
                         (eq defun-mode :logic))
                    'reclassifying)
                   (t

; We allow "redefinition" from :logic to :program mode by treating the latter
; as redundant.  At one time we thought it should be disallowed because of an
; example like this:

; (encapsulate nil
;   (local (defun foo (x) x))
;   (defun foo (x) (declare (xargs :mode :program)) x)  ; redundant?
;   (defthm foo-is-id (equal (foo x) x)))

; We clearly don't want to allow this encapsulation or analogous books.  But
; this is prevented by pass 2 of the encapsulate (similarly, but at the book
; level, for certify-book), when ACL2 discovers that foo is now :program mode.
; We need to be careful to avoid similar traps elsewhere.

; It's important to allow such to be redundant in order to avoid the following
; problem, pointed out by Jared Davis.  Imagine that one book defines a
; function in :logic mode, while another has an identical definition in
; :program mode followed by verify-termination.  Also imagine that both books
; are independently certified.  Now imagine, in a fresh session, including the
; first book and then the second.  Inclusion of the second causes an error in
; Version_3.4 because of the "downgrade" from :logic mode to :program mode at
; the time the :program mode definition is encountered.

; Finally, note that we are relying on safe-mode!  Imagine a book with a local
; :logic mode definition of f followed by a non-local :program mode definition
; of f, followed by a defconst that uses f.  Also suppose that the guard of f
; is insufficient to verify its guards; to be specific, suppose (f x) is
; defined to be (car x) with a guard of t.  If we call (f 3) in the defconst,
; there is a guard violation.  In :logic mode that isn't a problem, because we
; are running *1* code.  But in :program mode we could get a hard Lisp error.
; In fact, we won't in the case of defconst, because defconst forms are
; evaluated in safe mode.  For a potentially related issue, see the comments in
; :DOC note-2-9 for an example of how we can get unsoundness, not merely a hard
; error, for the use of ill-guarded functions in defconst forms.

                    'redundant)))
                 ((and (null (cadr val)) ; optimization
                       (fetch-dcl-field :non-executable
                                        (butlast (cddr def) 1)))
                  (cond
                   ((let* ((event-tuple (cddr (car wrld1)))
                           (event (if (symbolp (cadr event-tuple))
                                      (cdr event-tuple) ; see make-event-tuple
                                    (cddr event-tuple))))
                      (non-identical-defp
                       def
                       (case (car event)
                         (mutual-recursion
                          (assoc-eq name (strip-cdrs (cdr event))))
                         (defuns
                           (assoc-eq name (cdr event)))
                         (otherwise
                          (cdr event)))
                       chk-measure-p
                       wrld)))
                   ((and (eq (symbol-class name wrld) :program)
                         (eq defun-mode :logic))
                    'reclassifying)
                   (t

; We allow "redefinition" from :logic to :program mode by treating the latter
; as redundant.  See the comment above on this topic.

                    'redundant)))
                 (t nil))))
        (t nil)))

(defun redundant-or-reclassifying-defunp (defun-mode symbol-class
                                            ld-skip-proofsp def wrld)

; Def is a defuns tuple such as (fn args ...dcls... body) that has been
; submitted to defuns with mode defun-mode.  We determine whether fn is already
; defined in wrld and has an "identical" definition (up to defun-mode).  We
; return either nil, a message (cons pair suitable for printing with ~@),
; 'redundant, 'reclassifying, or 'verify-guards.  'Redundant is returned if
; there is an existing definition for fn that is identical-defp to def and has
; mode :program or defun-mode, except that in this case 'verify-guards is
; returned if the symbol-class was :ideal but this definition indicates
; promotion to :common-lisp-compliant.  'Reclassifying is returned if there is
; an existing definition for fn that is identical-defp to def but in mode
; :program while defun-mode is :logic.  Otherwise nil or an explanatory
; message, suitable for printing using " Note that ~@0.", is returned.

; Functions further up the call tree will decide what to do with a result of
; 'verify-guards.  But a perfectly reasonable action would be to cause an error
; suggesting the use of verify-guards instead of defun.

  (redundant-or-reclassifying-defunp0 defun-mode symbol-class
                                      ld-skip-proofsp t def wrld))

(defun redundant-or-reclassifying-defunsp10 (defun-mode symbol-class
                                              ld-skip-proofsp chk-measure-p
                                              def-lst wrld ans)

; See redundant-or-reclassifying-defunsp1.  This function has the same behavior
; as that one, except in this one, if parameter chk-measure-p is nil, then
; measure checking is suppressed.

  (cond ((null def-lst) ans)
        (t (let ((x (redundant-or-reclassifying-defunp0
                     defun-mode symbol-class ld-skip-proofsp chk-measure-p
                     (car def-lst) wrld)))
             (cond
              ((consp x) x) ; a message
              ((eq ans x)
               (redundant-or-reclassifying-defunsp10
                defun-mode symbol-class ld-skip-proofsp chk-measure-p
                (cdr def-lst) wrld ans))
              (t nil))))))

(defun redundant-or-reclassifying-defunsp1 (defun-mode symbol-class
                                             ld-skip-proofsp def-lst wrld ans)
  (redundant-or-reclassifying-defunsp10 defun-mode symbol-class ld-skip-proofsp
                                        t def-lst wrld ans))

(defun recover-defs-lst (fn wrld)

; Fn is a :program function symbol in wrld.  Thus, it was introduced by defun.
; (Constrained and defchoose functions are :logic.)  We return the defs-lst
; that introduced fn.  We recover this from the cltl-command for fn.

; A special case is when fn is non-executable.  We started allowing
; non-executable :program mode functions after Version_4.1, to provide an easy
; way to use defattach, especially during the boot-strap.  We prohibit
; reclassifying such a function symbol into :logic mode, for at least the
; following reason: we store the true stobjs-out for non-executable :program
; mode functions, to match attachments that may be made; but we always store a
; stobjs-out of (nil) in the :logic mode case.  We could perhaps allow
; reclassifying into :logic mode in cases where the stobjs-out is (nil) in the
; :program mode function, by recovering defuns from the event.  But it seems
; most coherent simply to disallow the upgrade.  We store a different value,
; :program, for the 'non-executablep property for :program mode functions than
; for :logic mode functions, where we store t.

  (let ((err-str "For technical reasons, we do not attempt to recover the ~
                  definition of a ~s0 function such as ~x1.  It is surprising ~
                  actually that you are seeing this message; please contact ~
                  the ACL2 implementors unless you have called ~x2 yourself.")
        (ctx 'recover-defs-lst))
    (cond
     ((getpropc fn 'non-executablep nil wrld)

; We shouldn't be seeing this message, as something between verify-termination
; and this lower-level function should be handling the non-executable case
; (which is disallowed for the reasons explained above, related to
; stobjs-out).

      (er hard ctx
          err-str
          "non-executable" fn 'recover-defs-lst))
     (t
      (let ((val
             (scan-to-cltl-command
              (cdr (lookup-world-index 'event
                                       (getpropc fn 'absolute-event-number
                                                 '(:error "See ~
                                                           RECOVER-DEFS-LST.")
                                                 wrld)
                                       wrld)))))
        (cond ((and (consp val)
                    (eq (car val) 'defuns))

; Val is of the form (defuns defun-mode-flg ignorep def1 ... defn).  If
; defun-mode-flg is non-nil then the parent event was (defuns def1 ... defn)
; and the defun-mode was defun-mode-flg.  If defun-mode-flg is nil, the parent
; was an encapsulate, defchoose, or :non-executable, but none of these cases
; should occur since presumably we are only considering :program mode functions
; that are not non-executable.

               (cond ((cadr val) (cdddr val))
                     (t (er hard ctx
                            err-str
                            "non-executable or :LOGIC mode"
                            fn
                            'recover-defs-lst))))
              (t (er hard ctx
                     "We failed to find the expected CLTL-COMMAND for the ~
                      introduction of ~x0."
                     fn))))))))

(defun get-clique (fn wrld)

; Fn must be a function symbol.  We return the list of mutually recursive fns
; in the clique containing fn, according to their original definitions.  If fn
; is :program we have to look for the cltl-command and recover the clique from
; the defs-lst.  Otherwise, we can use the 'recursivep property.

  (cond ((programp fn wrld)
         (let ((defs (recover-defs-lst fn wrld)))
           (strip-cars defs)))
        (t (let ((recp (getpropc fn 'recursivep nil wrld)))
             (cond ((null recp) (list fn))
                   (t recp))))))

(defun redundant-or-reclassifying-defunsp0 (defun-mode symbol-class
                                             ld-skip-proofsp chk-measure-p
                                             def-lst wrld)

; See redundant-or-reclassifying-defunsp.  This function has the same behavior
; as that one, except in this one, if parameter chk-measure-p is nil, then
; measure checking is suppressed.

  (cond
   ((null def-lst) 'redundant)
   (t (let ((ans (redundant-or-reclassifying-defunp0
                  defun-mode symbol-class ld-skip-proofsp chk-measure-p
                  (car def-lst) wrld)))
        (cond ((consp ans) ans) ; a message
              (t (let ((ans (redundant-or-reclassifying-defunsp10
                             defun-mode symbol-class ld-skip-proofsp
                             chk-measure-p (cdr def-lst) wrld ans)))
                   (cond ((eq ans 'redundant)
                          (cond
                           ((or (eq defun-mode :program)
                                (let ((recp (getpropc (caar def-lst) 'recursivep
                                                      nil wrld)))
                                  (if (and (consp recp)
                                           (consp (cdr recp)))
                                      (set-equalp-eq (strip-cars def-lst) recp)
                                    (null (cdr def-lst)))))
                            ans)
                           (t (msg "for :logic mode definitions to be ~
                                    redundant, if one is defined with ~
                                    mutual-recursion then both must be ~
                                    defined in the same mutual-recursion.~|~%"))))
                         ((and (eq ans 'reclassifying)
                               (not (set-equalp-eq (strip-cars def-lst)
                                                   (get-clique (caar def-lst)
                                                               wrld))))
                          (msg "for reclassifying :program mode definitions ~
                                to :logic mode, an entire mutual-recursion ~
                                clique must be reclassified.  In this case, ~
                                the mutual-recursion that defined ~x0 also ~
                                defined the following, not included in the ~
                                present event: ~&1.~|~%"
                               (caar def-lst)
                               (set-difference-eq (get-clique (caar def-lst)
                                                              wrld)
                                                  (strip-cars def-lst))))
                         (t ans)))))))))

(defun strip-last-elements (lst)
  (declare (xargs :guard (true-list-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (car (last (car lst)))
                 (strip-last-elements (cdr lst))))))

(defun redundant-or-reclassifying-defunsp (defun-mode symbol-class
                                            ld-skip-proofsp def-lst ctx wrld
                                            ld-redefinition-action fives
                                            non-executablep stobjs-in-lst
                                            default-state-vars)

; We return 'redundant if the functions in def-lst are already identically
; defined with :mode defun-mode and class symbol-class.  We return
; 'verify-guards if they are all identically defined with :mode :logic and class
; :ideal, but this definition indicates promotion to :common-lisp-compliant.
; Finally, we return 'reclassifying if they are all identically defined in
; :mode :program and defun-mode is :logic.  We return nil otherwise.

; We start to answer this question by independently considering each def in
; def-lst.  We then add additional requirements pertaining to mutual-recursion.
; The first is for :logic mode definitions (but see the Historical Plaque
; below): if the old and new definition are in different mutual-recursion nests
; (or if one is in a mutual-recursion with other definitions and the other is
; not), then the new definition is not redundant.  To see why we make this
; additional restriction, consider the following example.

; (encapsulate
;  ()
;  (local
;    (mutual-recursion
;     (defun f (x y)
;       (if (and (consp x) (consp y))
;           (f (cons 3 x) (cdr y))
;         (list x y)))
;     (defun g (x y)
;       (if (consp y)
;           (f x (cdr y))
;         (list x y)))))
;
;  (defun f (x y)
;  ;;; possible IMPLICIT (bad) measure of (acl2-count x)
;    (if (and (consp x) (consp y))
;        (f (cons 3 x) (cdr y))
;      (list x y))))

; As the comment indicates, if ACL2 were to use the entire mutual-recursion to
; guess measures, then it might well guess a different measure (based on y) for
; the first definition of f than for the second (based on x), leaving us with
; an unsound induction scheme for f (based incorrectly on x).  Although ACL2
; does not guess measures that way as of this writing (shortly after the
; Version_3.4 release), still one can imagine future heuristic changes of this
; sort.  A more "practical" reason for this restriction is that it seems to
; make the underlying theory significantly easier to work out.

; A second requirement is that we do not reclassify from :program mode to
; :logic mode for a proper subset of a mutual-recursion nest.  This restriction
; may be overly conservative, but then again, we expect it to be rare that it
; would affect anyone.  While we do not have a definitive reason for this
; restriction, consider for example induction schemes, which are stored for
; single recursion but not mutual-recursion.  Although this issue may be fully
; handled by the restriction on redundancy described above, we see this as just
; one possible pitfall, so we prefer to maintain the invariant that all
; functions in a mutual-recursion nest have the same defun-mode.

; Note: Our redundancy check for definitions is based on the untranslated
; terms.  This is different from, say, theorems, where we compare translated
; terms.  The reason is that we do not store the translated versions of
; :program definitions and don't want to go to the cost of translating
; what we did store.  We could, I suppose.  We handle theorems the way we do
; because we store the translated theorem on the property list, so it is easy.
; Our main concern vis-a-vis redundancy is arranging for identical definitions
; not to blow us up when we are loading books that have copied definitions and
; I don't think translation will make an important difference to the utility of
; the feature.

; Note: There is a possible bug lurking here.  If the host Common Lisp expands
; macros before storing the symbol-function, then we could recognize as
; "redundant" an identical defun that, if actually passed to the underlying
; Common Lisp, would result in the storage of a different symbol-function
; because of the earlier redefinition of some macro used in the "redundant"
; definition.  This is not a soundness problem, since redefinition is involved.
; But it sure might annoy somebody who didn't notice that his redefinition
; wasn't processed.

; Historical Plaque:  The following comment was in place before we restricted
; redundancy to insist on identical mutual-recursion nests.

;  We answer this question by answering it independently for each def in
;  def-lst.  Thus, every def must be 'redundant or 'reclassifying as
;  appropriate.  This seems really weak because we do not insist that only one
;  cltl-command tuple is involved.  But (defuns def1 ... defn) just adds one
;  axiom for each defi and the axiom is entirely determined by the defi.  Thus,
;  if we have executed a defuns that added the axiom for defi then it is the
;  same axiom as would be added if we executed a different defuns that
;  contained defi.  Furthermore, a cltl-command of the form (defuns :defun-mode
;  ignorep def1 ... defn) means (defuns def1 ...  defn) was executed in this
;  world with the indicated defun-mode.

  (let ((ans
         (redundant-or-reclassifying-defunsp0 defun-mode symbol-class
                                              ld-skip-proofsp t def-lst wrld)))
    (cond ((and ld-redefinition-action
                (member-eq ans '(redundant reclassifying verify-guards)))

; We do some extra checking, converting ans to nil, in order to consider there
; to be true redefinition (by returning nil) in cases where that seems possible
; -- in particular, because translated bodies have changed due to prior
; redefinition of macros or defconsts called in a new body.  Our handling of
; this case isn't perfect, for example because it may reject reclassification
; when the order changes.  But at least it forces some definitions to be
; considered as doing redefinition.  Notice that this extra effort is only
; performed when redefinition is active, so as not to slow down the system in
; the normal case.  If there has been no redefinition in the session, then we
; expect this extra checking to be unnecessary.

           (let ((names (strip-cars fives))
                 (bodies (get-bodies fives)))
             (mv-let (erp lst bindings)
                     (translate-bodies1 (eq non-executablep t) ; not :program
                                        names bodies
                                        (pairlis$ names names)
                                        stobjs-in-lst
                                        ctx wrld default-state-vars)
                     (declare (ignore bindings))
                     (cond (erp

; This error could be due to an untouchable variable or function in one of the
; bodies.  In that case, we return the result returned by
; redundant-or-reclassifying-defunsp0 above, without possibly converting it to
; nil as may be done below.  That's OK; then we will not make an additional
; check that we are truly doing redefinition.  As discussed above, such
; perfection here is not required; in particular, we then simply consider the
; definition redundant here just as if redefinition were off.  However, it
; should be perfectly OK to consider the definition not to be redundant in that
; case.

                            ans)
                           ((eq (symbol-class (car names) wrld)
                                :program)
                            (let ((old-defs (recover-defs-lst (car names)
                                                              wrld)))
                              (and (equal names (strip-cars old-defs))
                                   (mv-let
                                    (erp old-lst bindings)
                                    (translate-bodies1

; The old non-executablep is nil; see recover-defs-lst.

                                     nil
                                     names
                                     (strip-last-elements old-defs)
                                     (pairlis$ names names)
                                     stobjs-in-lst
                                     ctx wrld default-state-vars)
                                    (declare (ignore bindings))
                                    (cond ((and (null erp)
                                                (equal lst old-lst))
                                           ans)
                                          (t

; If erp is true then we consider this to be true redefinition.  That is the
; opposite decision from what is made in the case above when translate-bodies1
; returns an error.  Which is the right decision: consider redefinition (vs.,
; say, redundancy) or not when there is an error in translate-bodies1?  The
; answer is that either is acceptable, as discussed above.  But as of this
; writing (August 2017) the code has probably been this way for a long time, we
; leave it alone, at least for now.

                                           nil))))))

; Otherwise we expect to be dealing with :logic mode functions.

                           ((equal lst
                                   (get-unnormalized-bodies names wrld))
                            ans)
                           (t nil)))))
          (t ans))))

(defun collect-when-cadr-eq (sym lst)
  (cond ((null lst) nil)
        ((eq sym (cadr (car lst)))
         (cons (car lst) (collect-when-cadr-eq sym (cdr lst))))
        (t (collect-when-cadr-eq sym (cdr lst)))))

(defun all-programp (names wrld)

; Names is a list of function symbols.  Return t iff every element of
; names is :program.

  (cond ((null names) t)
        (t (and (programp (car names) wrld)
                (all-programp (cdr names) wrld)))))

; Essay on the Identification of Irrelevant Formals

; A formal is irrelevant if its value does not affect the value of the
; function.  Of course, ignored formals have this property, but we here address
; ourselves to the much more subtle problem of formals that are used only in
; irrelevant ways.  For example, y in

; (defun foo (x y) (if (zerop x) 0 (foo (1- x) (cons x y))))

; is irrelevant.  Clearly, any formal mentioned outside of a recursive call is
; relevant -- provided that no previously introduced function has irrelevant
; arguments and no definition tests constants as in (if t x y).  But a formal
; that is never used outside a recursive call may still be relevant, as
; illustrated by y in:

; (defun foo (x y) (if (< x 2) x (foo y 0)))

; Observe that (foo 3 1) = 1 and (foo 3 0) = 0; thus, y is relevant.  (This
; function can be admitted with the measure (cond ((< x 2) 0) ((< y 2) 1) (t
; 2)).)

; Thus, we have to do a transitive closure computation based on which formals
; appear in which actuals of recursive calls.  In the first pass we see that x,
; above, is relevant because it is used outside the recursion.  In the next
; pass we see that y is relevant because it is passed into the x argument
; position of a recursive call.

; The whole thing is made somewhat more hairy by mutual recursion, though no
; new intellectual problems are raised.  However, to cope with mutual recursion
; we stop talking about "formals" and start talking about "posns."  A posn here
; is a natural number n that represents the nth formal for a function in the
; mutually recursive clique.  We say a "posn is used" if the corresponding
; formal is used.

; A "recursive call" here means a call of any function in the clique.  We
; generally use the variable clique-alist to mean an alist whose elements are
; each of the form (fn . posns).

; A second problem is raised by the presence of lambda expressions.  We discuss
; them more below.

; Our algorithm iteratively computes the relevant posns of a clique by
; successively enlarging an initial guess.  The initial guess consists of all
; the posns used outside of a recursive call, including the guard or measure or
; the lists of ignored or ignorable formals.  Clearly, every posn so collected
; is relevant.  We then iterate, sweeping into the set every posn used either
; outside recursion or in an actual used in a relevant posn.  When this
; computation ceases to add any new posns we consider the uncollected posns to
; be irrelevant.

; For example, in (defun foo (x y) (if (zerop x) 0 (foo (1- x) (cons x y)))) we
; initially guess that x is relevant and y is not.  The next iteration adds
; nothing, because y is not used in the x posn, so we are done.

; On the other hand, in (defun foo (x y) (if (< x 2) x (foo y 0))) we might
; once again guess that y is irrelevant.  However, the second pass would note
; the occurrence of y in a relevant posn and would sweep it into the set.  We
; conclude that there are no irrelevant posns in this definition.

; So far we have not discussed lambda expressions; they are unusual in this
; setting because they may hide recursive calls that we should analyze.  We do
; not want to expand the lambdas away, for fear of combinatoric explosions.
; Instead, we expand the clique-alist, by adding, for each lambda-application a
; new entry that pairs that lambda expression with the appropriate terms.
; (That is, the "fn" of the new clique member is the lambda expression itself.)
; Thus, we actually use assoc-equal instead of assoc-eq when looking in
; clique-alist.

(defun formal-position (var formals i)
  (cond ((null formals) i)
        ((eq var (car formals)) i)
        (t (formal-position var (cdr formals) (1+ i)))))

(defun make-posns (formals vars)
  (cond ((null vars) nil)
        (t (cons (formal-position (car vars) formals 0)
                 (make-posns formals (cdr vars))))))

(mutual-recursion

(defun relevant-posns-term (fn formals term fns clique-alist posns)

; Term is a term occurring in the body of fn which has formals formals.  We
; collect a posn into posns if it is used outside a recursive call (or in an
; already known relevant actual to a recursive call).  See the Essay on the
; Identification of Irrelevant Formals.

  (cond
   ((variablep term)
    (add-to-set (formal-position term formals 0) posns))
   ((fquotep term) posns)
   ((equal (ffn-symb term) fn)
    (relevant-posns-call fn formals (fargs term) 0 fns clique-alist :same
                         posns))
   ((member-equal (ffn-symb term) fns)
    (relevant-posns-call fn formals (fargs term) 0 fns clique-alist
                         (cdr (assoc-equal (ffn-symb term) clique-alist))
                         posns))
   (t
    (relevant-posns-term-lst fn formals (fargs term) fns clique-alist posns))))

(defun relevant-posns-term-lst (fn formals lst fns clique-alist posns)
  (cond ((null lst) posns)
        (t
         (relevant-posns-term-lst
          fn formals (cdr lst) fns clique-alist
          (relevant-posns-term fn formals (car lst) fns clique-alist posns)))))

(defun relevant-posns-call (fn formals actuals i fns clique-alist
                               called-fn-posns posns)

; See the Essay on the Identification of Irrelevant Formals.

; This function extends the set, posns, of posns for fn that are known to be
; relevant.  It does so by analyzing the given (tail of the) actuals for a call
; of some function in the clique, which we denote as called-fn, where that call
; occurs in the body of fn (which has the given formals).  Called-fn-posns is
; the set of posns for called-fn that are known to be relevant, except for the
; case that called-fn is fn, in which case called-fn-posns is :same.  The
; formal i, which is initially 0, is the position in called-fn's argument
; list of the first element of actuals.  We extend posns, the posns of fn known
; to be relevant, by seeing which posns are used in the actuals in the relevant
; posns of called-fn (i.e., called-fn-posns).

  (cond
   ((null actuals) posns)
   (t (relevant-posns-call
       fn formals (cdr actuals) (1+ i) fns clique-alist
       called-fn-posns
       (if (member i
                   (if (eq called-fn-posns :same)
                       posns ; might be extended through recursive calls
                     called-fn-posns))
           (relevant-posns-term fn formals (car actuals) fns clique-alist
                                posns)
         posns)))))
)

(defun relevant-posns-clique1 (fns arglists bodies all-fns ans)
  (cond
   ((null fns) ans)
   (t (relevant-posns-clique1
       (cdr fns)
       (cdr arglists) ; nil, once we cdr down to the lambdas
       (cdr bodies)   ; nil, once we cdr down to the lambdas
       all-fns
       (let* ((posns (cdr (assoc-equal (car fns) ans)))
              (new-posns
               (cond ((flambdap (car fns))
                      (relevant-posns-term (car fns)
                                           (lambda-formals (car fns))
                                           (lambda-body (car fns))
                                           all-fns
                                           ans
                                           posns))
                     (t
                      (relevant-posns-term (car fns)
                                           (car arglists)
                                           (car bodies)
                                           all-fns
                                           ans
                                           posns)))))
         (cond ((equal posns new-posns) ; optimization
                ans)
               (t (put-assoc-equal (car fns) new-posns ans))))))))

(defun relevant-posns-clique-recur (fns arglists bodies clique-alist)
  (let ((clique-alist1 (relevant-posns-clique1 fns arglists bodies fns
                                               clique-alist)))
    (cond ((equal clique-alist1 clique-alist) clique-alist)
          (t (relevant-posns-clique-recur fns arglists bodies
                                          clique-alist1)))))

(defun relevant-posns-clique-init (fns arglists guards split-types-terms
                                       measures ignores ignorables ans)

; We associate each function in fns, reversing the order in fns, with
; obviously-relevant formal positions.

  (cond
   ((null fns) ans)
   (t (relevant-posns-clique-init
       (cdr fns)
       (cdr arglists)
       (cdr guards)
       (cdr split-types-terms)
       (cdr measures)
       (cdr ignores)
       (cdr ignorables)
       (acons (car fns)
              (make-posns
               (car arglists)
               (all-vars1 (car guards)
                          (all-vars1 (car split-types-terms)
                                     (all-vars1 (car measures)

; Ignored formals are considered not to be irrelevant.  Should we do similarly
; for ignorable formals?

; - If yes (ignorables are not irrelevant), then we may miss some irrelevant
;   formals.  Of course, it is always OK to miss some irrelevant formals, but
;   we would prefer not to miss them needlessly.

; - If no (ignorables are irrelevant), then we may report an ignorable variable
;   as irrelevant, which might annoy the user even though it really is
;   irrelevant, if "ignorable" not only means "could be ignored" but also means
;   "could be irrelevant".

; We choose "yes".  If the user has gone through the trouble to label a
; variable as irrelevant, then the chance that irrelevance is due to a typo are
; dwarfed by the chance that irrelevance is due to being an ignorable var.

                                                (union-eq (car ignorables)
                                                          (car ignores))))))
              ans)))))

; We now develop the code to generate the clique-alist for lambda expressions.

(mutual-recursion

(defun relevant-posns-lambdas (term ans)
  (cond ((or (variablep term)
             (fquotep term))
         ans)
        ((flambdap (ffn-symb term))
         (relevant-posns-lambdas
          (lambda-body (ffn-symb term))
          (acons (ffn-symb term)
                 nil
                 (relevant-posns-lambdas-lst (fargs term) ans))))
        (t (relevant-posns-lambdas-lst (fargs term) ans))))

(defun relevant-posns-lambdas-lst (termlist ans)
  (cond ((endp termlist) ans)
        (t (relevant-posns-lambdas-lst
            (cdr termlist)
            (relevant-posns-lambdas (car termlist) ans)))))
)

(defun relevant-posns-merge (alist acc)
  (cond ((endp alist) acc)
        ((endp (cdr alist)) (cons (car alist) acc))
        ((equal (car (car alist))
                (car (cadr alist)))
         (relevant-posns-merge (acons (caar alist)
                                      (union$ (cdr (car alist))
                                              (cdr (cadr alist)))
                                      (cddr alist))
                               acc))
        (t (relevant-posns-merge (cdr alist) (cons (car alist) acc)))))

(defun relevant-posns-lambdas-top (bodies)
  (let ((alist (merge-sort-lexorder (relevant-posns-lambdas-lst bodies nil))))
    (relevant-posns-merge alist nil)))

(defun relevant-posns-clique (fns arglists guards split-types-terms measures
                                  ignores ignorables bodies)

; We compute the relevant posns in an expanded clique alist (one in which the
; lambda expressions have been elevated to clique membership).  The list of
; relevant posns includes the relevant lambda posns.  We do it by iteratively
; enlarging an initial clique-alist until it is closed.

  (let* ((clique-alist1 (relevant-posns-clique-init fns arglists guards
                                                    split-types-terms measures
                                                    ignores ignorables nil))
         (clique-alist2 (relevant-posns-lambdas-top bodies)))
    (relevant-posns-clique-recur (append fns (strip-cars clique-alist2))
                                 arglists
                                 bodies
                                 (revappend clique-alist1 clique-alist2))))

(defun irrelevant-non-lambda-slots-clique2 (fn formals i posns acc)
  (cond ((endp formals) acc)
        (t (irrelevant-non-lambda-slots-clique2
            fn (cdr formals) (1+ i) posns
            (cond ((member i posns) acc)
                  (t (cons (list* fn i (car formals))
                           acc)))))))

(defun irrelevant-non-lambda-slots-clique1 (fns arglists clique-alist acc)
  (cond ((endp fns)
         (assert$ (or (null clique-alist)
                      (flambdap (caar clique-alist)))
                  acc))
        (t (assert$ (eq (car fns) (caar clique-alist))
                    (irrelevant-non-lambda-slots-clique1
                     (cdr fns) (cdr arglists) (cdr clique-alist)
                     (irrelevant-non-lambda-slots-clique2
                      (car fns) (car arglists) 0 (cdar clique-alist)
                      acc))))))

(defun irrelevant-non-lambda-slots-clique (fns arglists guards
                                               split-types-terms measures
                                               ignores ignorables bodies)

; Let clique-alist be an expanded clique alist (one in which lambda expressions
; have been elevated to clique membership).  Return all the irrelevant slots
; for the non-lambda members of the clique.

; A "slot" is a triple of the form (fn n . var), where fn is a function symbol,
; n is some nonnegative integer less than the arity of fn, and var is the nth
; formal of fn.  If (fn n . var) is in the list returned by this function, then
; the nth formal of fn, namely var, is irrelevant to the value computed by fn.

  (let ((clique-alist (relevant-posns-clique fns arglists guards
                                             split-types-terms measures
                                             ignores ignorables bodies)))
    (irrelevant-non-lambda-slots-clique1 fns arglists clique-alist nil)))

(defun tilde-*-irrelevant-formals-msg1 (slots)
  (cond ((null slots) nil)
        (t (cons (cons "~n0 formal of ~x1, ~x2,"
                       (list (cons #\0 (list (1+ (cadar slots))))
                             (cons #\1 (caar slots))
                             (cons #\2 (cddar slots))))
                 (tilde-*-irrelevant-formals-msg1 (cdr slots))))))

(defun tilde-*-irrelevant-formals-msg (slots)
  (list "" "~@*" "~@* and the " "~@* the " (tilde-*-irrelevant-formals-msg1 slots)))

(defun missing-irrelevant-slots1 (irrelevant-slots irrelevants-alist acc)

; Recall that a slot has the form (fn n . var); see
; irrelevant-non-lambda-slots-clique.

  (cond ((endp irrelevant-slots) acc)
        (t (missing-irrelevant-slots1
            (cdr irrelevant-slots)
            irrelevants-alist
            (if (member-eq (cddr (car irrelevant-slots))               ; var
                           (cdr (assoc-eq (car (car irrelevant-slots)) ; fn
                                          irrelevants-alist)))
                acc
              (cons (car irrelevant-slots) acc))))))

(defun missing-irrelevant-slots (irrelevant-slots irrelevants-alist)
  (cond ((null irrelevant-slots) ; common case
         nil)
        ((null irrelevants-alist) ; common case
         irrelevant-slots)
        (t (missing-irrelevant-slots1 irrelevant-slots irrelevants-alist
                                      nil))))

(defun find-slot (fn var irrelevant-slots)
  (cond ((endp irrelevant-slots) nil)
        ((let ((slot (car irrelevant-slots))) ; (fn n . var)
           (or (and (eq fn (car slot))
                    (eq var (cddr slot))))))
        (t (find-slot fn var (cdr irrelevant-slots)))))

(defun bogus-irrelevants-alist2 (irrelevant-slots fn vars)
  (cond ((endp vars) nil)
        ((find-slot fn (car vars) irrelevant-slots)
         (bogus-irrelevants-alist2 irrelevant-slots fn (cdr vars)))
        (t
         (cons (car vars)
               (bogus-irrelevants-alist2 irrelevant-slots fn (cdr vars))))))

(defun bogus-irrelevants-alist1 (irrelevant-slots irrelevants-alist acc)

; Recall that a slot has the form (fn n . var); see
; irrelevant-non-lambda-slots-clique.

  (cond ((endp irrelevants-alist) acc)
        (t (bogus-irrelevants-alist1
            irrelevant-slots
            (cdr irrelevants-alist)
            (let ((bogus-vars
                   (bogus-irrelevants-alist2 irrelevant-slots
                                             (caar irrelevants-alist)
                                             (cdar irrelevants-alist))))
              (if bogus-vars
                  (acons (caar irrelevants-alist)
                         bogus-vars
                         acc)
                acc))))))

(defun bogus-irrelevants-alist (irrelevant-slots irrelevants-alist)
  (cond ((null irrelevants-alist) ; optimization for common case
         irrelevant-slots)
        (t (bogus-irrelevants-alist1 irrelevant-slots irrelevants-alist nil))))

(defun tilde-*-bogus-irrelevants-alist-msg1 (alist)
  (cond ((endp alist) nil)
        (t (cons (cons "formal~#0~[~/s~] ~&0 of ~x1"
                       (list (cons #\0 (cdar alist))
                             (cons #\1 (caar alist))))
                 (tilde-*-bogus-irrelevants-alist-msg1 (cdr alist))))))

(defun tilde-*-bogus-irrelevants-alist-msg (alist)
  (list "" "~@*" "~@*; and the " "~@*; the "
        (tilde-*-bogus-irrelevants-alist-msg1 alist)))

(defun chk-irrelevant-formals (fns arglists guards split-types-terms measures
                                   ignores ignorables irrelevants-alist bodies
                                   ctx state)
  (let ((irrelevant-formals-ok
         (cdr (assoc-eq :irrelevant-formals-ok
                        (table-alist 'acl2-defaults-table (w state))))))
    (cond
     ((or (eq irrelevant-formals-ok t)
          (and (eq irrelevant-formals-ok :warn)
               (warning-disabled-p "Irrelevant-formals")))
      (value nil))
     (t
      (let ((irrelevant-slots
             (irrelevant-non-lambda-slots-clique
              fns arglists guards split-types-terms measures ignores ignorables
              bodies)))
        (cond
         ((and (null irrelevant-slots)
               (null irrelevants-alist)) ; optimize for common case
          (value nil))
         (t
          (let ((bogus-irrelevants-alist ; declared irrelevant but not
                 (bogus-irrelevants-alist irrelevant-slots irrelevants-alist))
                (missing-irrelevant-slots ; irrelevant but not declared
                 (missing-irrelevant-slots irrelevant-slots
                                           irrelevants-alist)))
            (cond
             ((and (null bogus-irrelevants-alist)
                   (null missing-irrelevant-slots))
              (value nil))
             (t
              (let ((msg (msg
                          "~@0~@1See :DOC irrelevant-formals."
                          (if missing-irrelevant-slots
                              (msg "The ~*0 ~#1~[is~/are~] irrelevant but not ~
                                    declared to be irrelevant.  "
                                   (tilde-*-irrelevant-formals-msg
                                    missing-irrelevant-slots)
                                   (if (cdr missing-irrelevant-slots) 1 0))
                            "")
                          (if bogus-irrelevants-alist
                              (msg "The ~*0 ~#1~[is~/are~] falsely declared ~
                                    irrelevant.  "
                                   (tilde-*-bogus-irrelevants-alist-msg
                                    bogus-irrelevants-alist)
                                   (if (or (cdr bogus-irrelevants-alist)
                                           (cddr (car bogus-irrelevants-alist)))
                                       1
                                     0))
                            ""))))
                (cond
                 ((eq irrelevant-formals-ok :warn)
                  (pprogn
                   (warning$ ctx ("Irrelevant-formals") "~@0" msg)
                   (value nil)))
                 (t (er soft ctx "~@0" msg))))))))))))))

(defun chk-logic-subfunctions (names0 names terms wrld str ctx state)

; Assume we are defining names in terms of terms (1:1 correspondence).  Assume
; also that the definitions are to be :logic.  Then we insist that every
; function used in terms be :logic.  Str is a string used in our error
; message and is either "guard", "split-types expression", or "body".

; WARNING: This function guarantees that a call of a :logic mode function
; cannot lead to a call of a :program mode function.  This guarantee justifies
; the restriction, implemented in oneify-cltl-code, that only :program mode
; functions lay down *1* code that is sensitive to invariant-risk.  It seems
; conceivable that without the guarantee, a :logic mode function could lead to
; a call of a :program mode function that violates stobj invariants or writes
; past the end of an array.  So be careful when considering a relaxation of
; this guarantee!

  (cond ((null names) (value nil))
        (t (let ((bad (collect-programs
                       (set-difference-eq (all-fnnames (car terms))
                                          names0)
                       wrld)))
             (cond
              (bad

; Before eliminating the error below, think carefully!  In particular, consider
; the following problem involving trans-eval.  A related concern, which points
; to the comment below, may be found in a comment in the definition of
; magic-ev-fncall.

; Sol Swords wondered whether there might be an issue when function takes and
; returns both a user-defined stobj and state, calling trans-eval to change the
; stobj even though the function doesn't actually change it.  Below
; investigating whether Sol's idea can be exploited to destroy, perhaps with
; bad consequences, some sort of invariant related to the user-stobj-alist of
; the state.  The answer seems to be no, but only because (as Sol pointed out,
; if memory serves) trans-eval is in :program mode -- and it stays there
; because trans-eval calls ev-for-trans-eval, which calls ev, which belongs to
; the list *primitive-program-fns-with-raw-code* (and because :logic mode
; functions can't call :program mode functions).  Below is an example that
; illustrates what could go wrong if trans-eval were in :logic mode.

;   (defstobj st fld)
;
;   (set-state-ok t)
;
;   (defun f (st state)
;     (declare (xargs :stobjs (st state)
;                     :mode :program))
;     (let ((st (update-fld 2 st)))
;       (mv-let (erp val state)
;               (trans-eval '(update-fld 3 st) 'f state nil)
;               (declare (ignore erp val))
;               (mv state (fld st) st))))
;
;   ; Logically, f sets (fld st) to 2, so the return value should be (mv _ 2
;   ; _).  But we get (mv _ 3 _).  The only thing that saves us is that
;   ; trans-eval is in :program mode, hence f is in :program mode.  This gives
;   ; us a good reason to be very cautious before allowing :program mode
;   ; functions to be called from :logic mode functions.  Note that even if we
;   ; were to allow the return state to be somehow undefined, still the middle
;   ; return value would be a problem logically!
;
;   ; Succeeds
;   (mv-let (state val st)
;           (f st state)
;           (assert$ (equal val 3)
;                    (mv state val st)))
;
;   ; Fails
;   (mv-let (state val st)
;           (f st state)
;           (assert$ (equal val 2)
;                    (mv state val st)))

               (er soft ctx
                   "The ~@0 for ~x1 calls the :program function~#2~[ ~
                    ~&2~/s ~&2~].  We require that :logic definitions be ~
                    defined entirely in terms of :logically defined ~
                    functions.  See :DOC defun-mode."
                   str (car names) bad))
              (t (chk-logic-subfunctions names0 (cdr names) (cdr terms)
                                             wrld str ctx state)))))))

;; Historical Comment from Ruben Gamboa:
;; This function strips out the functions which are
;; non-classical in a chk-acceptable-defuns "fives" structure.

#+:non-standard-analysis
(defun get-non-classical-fns-from-list (names wrld fns-sofar)
  (cond ((null names) fns-sofar)
        (t (let ((fns (if (or (not (symbolp (car names)))
                              (classicalp (car names) wrld))
                          fns-sofar
                        (cons (car names) fns-sofar))))
             (get-non-classical-fns-from-list (cdr names) wrld fns)))))

;; Historical Comment from Ruben Gamboa:
;; This function takes in a list of terms and returns any
;; non-classical functions referenced in the terms.

#+:non-standard-analysis
(defmacro get-non-classical-fns (lst wrld)
  `(get-non-classical-fns-aux ,lst ,wrld nil))

#+:non-standard-analysis
(defun get-non-classical-fns-aux (lst wrld fns-sofar)
  (cond ((null lst) fns-sofar)
        (t (get-non-classical-fns-aux
            (cdr lst)
            wrld
            (get-non-classical-fns-from-list
             (all-fnnames (car lst)) wrld fns-sofar)))))

;; Historical Comment from Ruben Gamboa:
;; this function checks that the measures used to accept the definition
;; are classical.  Note, *no-measure* is a signal that the default measure is
;; being used (see get-measures1) -- and in that case, we know it's classical,
;; since it's just the acl2-count of some tuple consisting of variables in the
;; defun.

#+:non-standard-analysis
(defun strip-missing-measures (lst accum)
  (if (consp lst)
      (if (equal (car lst) *no-measure*)
          (strip-missing-measures (cdr lst) accum)
        (strip-missing-measures (cdr lst) (cons (car lst) accum)))
    accum))

#+:non-standard-analysis
(defun chk-classical-measures (measures names ctx wrld state)
  (let ((non-classical-fns (get-non-classical-fns
                            (strip-missing-measures measures nil)
                            wrld)))
    (cond ((null non-classical-fns)
           (value nil))
          (t
           (er soft ctx
               "It is illegal to use non-classical measures to justify a ~
                recursive definition.  However, there has been an ~
                attempt to recursively define ~*0 using the ~
                non-classical function~#1~[~/s~] ~*2 in the measure."
               `("<MissingFunction>" "~x*," "~x* and " "~x*, " ,names)
               non-classical-fns
               `("<MissingFunction>" "~x*," "~x* and " "~x*, "
                 ,non-classical-fns))))))

;; Historical Comment from Ruben Gamboa:
;; This function checks that non-classical functions only appear
;; on non-recursive functions.

#+:non-standard-analysis
(defun chk-no-recursive-non-classical (non-classical-fns names mp rel
                                                         measures
                                                         bodies ctx
                                                         wrld state)
  (cond ((and (int= (length names) 1)
              (not (ffnnamep-mod-mbe (car names) (car bodies))))

; Then there is definitely no recursion (see analogous computation in
; putprop-recursivep-lst).  Note that with :bogus-mutual-recursion-ok, a clique
; of size greater than 1 might not actually have any recursion.  But then it
; will be up to the user in this case to eliminate the appearance of possible
; recursion.

         (value nil))
        ((not (null non-classical-fns))
         (er soft ctx
             "It is illegal to use non-classical functions in a ~
              recursive definition.  However, there has been an ~
              attempt to recursively define ~*0 using the ~
              non-classical function~#1~[~/s~] ~*2"
             `("<MissingFunction>" "~x*," "~x* and " "~x*, " ,names)
             non-classical-fns
             `("<MissingFunction>." "~x*." "~x* and " "~x*, "
               ,non-classical-fns)))
        ((not (and (classicalp mp wrld)
                   (classicalp rel wrld)))
         (er soft ctx
             "It is illegal to use a non-classical function as a ~
              well-ordering or well-ordered domain in a recursive ~
              definition.  However, there has been an ~
              attempt to recursively define ~*0 using the ~
              well-ordering function ~x1 and domain ~x2."
             `("<MissingFunction>" "~x*," "~x* and " "~x*, " ,names)
             mp
             rel))
        (t
         (chk-classical-measures measures names ctx wrld state))))

(defun union-collect-non-x (x lst)
  (cond ((endp lst) nil)
        (t (union-equal (collect-non-x x (car lst))
                        (union-collect-non-x x (cdr lst))))))

(defun translate-measures (terms logic-modep ctx wrld state)

; WARNING: Keep this in sync with translate-term-lst.  Here we allow (:? var1
; ... vark), where the vari are distinct variables.

  (cond ((null terms) (value nil))
        (t (er-let*
            ((term
              (cond ((and (consp (car terms))
                          (eq (car (car terms)) :?))
                     (cond ((arglistp (cdr (car terms)))
                            (value (car terms)))
                           (t (er soft ctx
                                  "A measure whose car is :? must be of the ~
                                   form (:? v1 ... vk), where (v1 ... vk) is ~
                                   a list of distinct variables.  The measure ~
                                   ~x0 is thus illegal."
                                  (car terms)))))
                    (t
                     (translate (car terms)

; One might use stobjs-out '(nil) below, if one felt uneasy about measures
; changing state.  But we know no logical justification for this feeling, nor
; do we ever expect to execute the measures in Common Lisp.  In fact we find it
; useful to be able to pass state into a measure even when its argument
; position isn't "state"; consider for example the function big-clock-entry.

                                t ; stobjs-out
                                logic-modep t ctx wrld state))))
             (rst (translate-measures (cdr terms) logic-modep ctx wrld state)))
            (value (cons term rst))))))

(defun redundant-predefined-error-msg (name)
  (let ((pkg-name (and (symbolp name) ; probably always true
                       (symbol-package-name name))))
    (msg "ACL2 is processing a redundant definition of the name ~x0, which is ~
          ~#1~[already defined using special raw Lisp code~/predefined in the ~
          ~x2 package~].  For technical reasons, we disallow non-LOCAL ~
          redundant definitions in such cases; see :DOC redundant-events.  ~
          Consider wrapping this definition inside a call of LOCAL."
         name
         (if (equal pkg-name *main-lisp-package-name*)
             1
           0)
         *main-lisp-package-name*)))

(defun chk-acceptable-defuns-redundancy (names ctx wrld state)

; The following comment is referenced in :doc redundant-events and in a comment
; in defmacro-fn.  If it is removed or altered, consider modifying that
; documentation and comment (respectively).

; The definitions of names have tentatively been determined to be redundant.
; We cause an error if this is not allowed, else return (value 'redundant).

; Here we cause an error for non-local redundant built-in definitions.  The
; reason is that some built-ins are defined using #-acl2-loop-only code.  So
; consider what happens when such a built-in function has a definition
; occurring in the compiled file for a book.  At include-book time, this new
; definition will be loaded from that compiled file, presumably without any
; #-acl2-loop-only.

; The following book certified in ACL2 Version_3.3 built on SBCL, where we have
; #+acl2-mv-as-values and also we load compiled files.  In this case the
; problem was that while ACL2 defined prog2$ as a macro in #-acl2-loop-only,
; for proper multiple-value handling, nevertheless that definition was
; overridden by the compiled definition loaded by the compiled file associated
; with the book "prog2" (not shown here, but containing the redundant
; #+acl2-loop-only definition of prog2$).

; (in-package "ACL2")
;
; (include-book "prog2") ; redundant #+acl2-loop-only def. of prog2$
;
; (defun foo (x)
;   (prog2$ 3 (mv x x)))
;
; (defthm foo-fact
;   (equal (foo 4)
;          (list 4 4))
;   :rule-classes nil)
;
; (verify-guards foo)
;
; (defthm foo-fact-bogus
;   (equal (foo 4)
;          (list 4))
;   :rule-classes nil)
;
; (defthm contradiction
;   nil
;   :hints (("Goal" :use (foo-fact foo-fact-bogus)))
;   :rule-classes nil)

; After Version_4.1, prog2$ became just a macro whose calls expanded to forms
; (return-last 'progn ...).  But the idea illustrated above is still relevant.

; We make this restriction for functions whose #+acl2-loop-only and
; #-acl2-loop-only definitions disagree.  See
; fns-different-wrt-acl2-loop-only.

; By the way, it is important to include functions defined in #+acl2-loop-only
; that have no definition in #-acl2-loop-only.  This becomes clear if you
; create a book with (in-package "ACL2") followed by the definition of LENGTH
; from axioms.lisp.  In an Allegro CL build of ACL2 Version_3.3, you will get a
; raw Lisp error during the compilation phase when you apply certify-book to
; this book, complaining about redefining a function in the COMMON-LISP
; package.

; Note that we can avoid the restriction for local definitions, since those
; will be ignored in the compiled file.

  (cond ((and (not (f-get-global 'in-local-flg state))
              (not (global-val 'boot-strap-flg (w state)))
              (not (f-get-global 'redundant-with-raw-code-okp state))
              (let ((recp (getpropc (car names) 'recursivep nil wrld))
                    (bad-fns

; The test below isn't right if a built-in function with raw Lisp code has been
; promoted to logic mode after assigning state global
; 'verify-termination-on-raw-program-okp to t.  However, that assignment may
; only be done with a trust tag, and the documentation warns that doing this
; promotion could be unsound.  So we don't worry about that case here.

                     (if (eq (symbol-class (car names) wrld)
                             :program)
                         (f-get-global
                          'program-fns-with-raw-code
                          state)
                       (f-get-global
                        'logic-fns-with-raw-code
                        state))))
                (if recp
                    (intersectp-eq recp bad-fns)
                  (member-eq (car names) bad-fns))))
         (er soft ctx
             "~@0"
             (redundant-predefined-error-msg (car names))))
        (t (value 'redundant))))

(defun chk-acceptable-defuns-verify-guards-er (names ctx wrld state)

; The redundancy check during processing the definition(s) of names has
; returned 'verify-guards.  We cause an error.  If that proves to be too
; inconvenient for users, we could look into arranging for a call of
; verify-guards.

  (let ((include-book-path
         (global-val 'include-book-path wrld)))
    (mv-let
     (erp ev-wrld-and-cmd-wrld state)
     (state-global-let*
      ((inhibit-output-lst
        (cons 'error (f-get-global 'inhibit-output-lst state))))

; Keep the following in sync with pe-fn.

      (let ((wrld (w state)))
        (er-let*
         ((ev-wrld (er-decode-logical-name (car names) wrld :pe state))
          (cmd-wrld (superior-command-world ev-wrld wrld :pe
                                            state)))
         (value (cons ev-wrld cmd-wrld)))))
     (mv-let (erp1 val1 state)
             (er soft ctx
                 "The definition of ~x0~#1~[~/ (along with the others in its ~
                  mutual-recursion clique)~]~@2 demands guard verification, ~
                  but there is already a corresponding existing definition ~
                  without its guard verified.  ~@3Use verify-guards instead; ~
                  see :DOC verify-guards. ~#4~[Here is the existing ~
                  definition of ~x0:~/The existing definition of ~x0 appears ~
                  to precede this one in the same top-level command.~]"
                 (car names)
                 names
                 (cond
                  (include-book-path
                   (cons " in the book ~xa"
                         (list (cons #\a (car include-book-path)))))
                  (t ""))
                 (cond
                  ((cddr include-book-path)
                   (cons "Note: The above book is included under the ~
                          following sequence of included books from outside ~
                          to inside, i.e., top-level included book ~
                          first:~|~&b.~|"
                         (list (cons #\b (reverse
                                          (cdr include-book-path))))))
                  ((cdr include-book-path)
                   (cons "Note: The above book is included inside the book ~
                          ~xb.  "
                         (list (cons #\b (cadr include-book-path)))))
                  (t ""))
                 (if erp 1 0))
             (pprogn (if erp
                         state
                       (pe-fn1 wrld (standard-co state)
                               (car ev-wrld-and-cmd-wrld)
                               (cdr ev-wrld-and-cmd-wrld)
                               state))
                     (mv erp1 val1 state))))))

(defun chk-non-executablep (defun-mode non-executablep ctx state)

; We check that the value for keyword :non-executable is legal with respect to
; the given defun-mode.

  (cond ((eq non-executablep nil)
         (value nil))
        ((eq defun-mode :logic)
         (cond ((eq non-executablep t)
                (value nil))
               (t (er soft ctx
                      "The :NON-EXECUTABLE flag for :LOGIC mode functions ~
                       must be ~x0 or ~x1, but ~x2 is neither."
                      t nil non-executablep))))
        (t ; (eq defun-mode :program)
         (cond ((eq non-executablep :program)
                (value nil))
               (t (er soft ctx
                      "The :NON-EXECUTABLE flag for :PROGRAM mode functions ~
                       must be ~x0 or ~x1, but ~x2 is neither."
                      :program nil non-executablep))))))

(defun chk-acceptable-defuns0 (fives ctx wrld state)

; This helper function for chk-acceptable-defuns factors out some computation,
; as requested by Daron Vroon for ACL2s purposes.

  (er-let*
   ((defun-mode (get-unambiguous-xargs-flg :MODE
                                           fives
                                           (default-defun-mode wrld)
                                           ctx state))
    (stobjs-in-lst (get-stobjs-in-lst fives defun-mode ctx wrld state))
    (non-executablep
     (get-unambiguous-xargs-flg :NON-EXECUTABLE fives nil ctx state))
    (verify-guards (get-unambiguous-xargs-flg :VERIFY-GUARDS
                                              fives
                                              '(unspecified)
                                              ctx state)))
   (er-progn
    (chk-defun-mode defun-mode ctx state)
    (chk-non-executablep defun-mode non-executablep ctx state)
    (cond ((consp verify-guards)

; This means that the user did not specify a :verify-guards.  We will default
; it appropriately.

           (value nil))
          ((eq defun-mode :program)
           (if (eq verify-guards nil)
               (value nil)
             (er soft ctx
                 "When the :MODE is :program, the only legal :VERIFY-GUARDS ~
                  setting is NIL.  ~x0 is illegal."
                 verify-guards)))
          ((or (eq verify-guards nil)
               (eq verify-guards t))
           (value nil))
          (t (er soft ctx
                 "The legal :VERIFY-GUARD settings are NIL and T.  ~x0 is ~
                  illegal."
                 verify-guards)))
    (let* ((symbol-class (cond ((eq defun-mode :program) :program)
                               ((consp verify-guards)
                                (cond
                                 ((= (default-verify-guards-eagerness wrld)
                                     0)
                                  :ideal)
                                 ((= (default-verify-guards-eagerness wrld)
                                     1)
                                  (if (get-guardsp fives wrld)
                                      :common-lisp-compliant
                                    :ideal))
                                 (t :common-lisp-compliant)))
                               (verify-guards :common-lisp-compliant)
                               (t :ideal))))
      (value (list* stobjs-in-lst defun-mode non-executablep symbol-class))))))

(defun get-boolean-unambiguous-xargs-flg-lst (key lst default ctx state)
  (er-let* ((lst (get-unambiguous-xargs-flg-lst key lst default ctx state)))
    (cond ((boolean-listp lst) (value lst))
          (t (er soft ctx
                 "The value~#0~[ ~&0 is~/s ~&0 are~] illegal for XARGS key ~x1,
                  as ~x2 and ~x3 are the only legal values for this key."
                 lst key t nil)))))

(defun get-irrelevants-alist (fives)
  (cond ((null fives) nil)
        (t (acons (caar fives)
                  (irrelevant-vars (fourth (car fives)))
                  (get-irrelevants-alist (cdr fives))))))

(defun chk-acceptable-defuns1 (names fives stobjs-in-lst defun-mode
                                     symbol-class rc non-executablep ctx wrld
                                     state
                                     #+:non-standard-analysis std-p)

; WARNING: This function installs a world, hence should only be called when
; protected by a revert-world-on-error (a condition that should be inherited
; when called by chk-acceptable-defuns).

  (let ((docs (get-docs fives))
        (big-mutrec (big-mutrec names))
        (arglists (strip-cadrs fives))
        (default-hints (default-hints wrld))
        (assumep (or (eq (ld-skip-proofsp state) 'include-book)
                     (eq (ld-skip-proofsp state) 'include-book-with-locals)))
        (reclassifying-all-programp (and (eq rc 'reclassifying)
                                         (all-programp names wrld))))
    (er-let*
     ((wrld1 (chk-just-new-names names 'function rc ctx wrld state))
      (wrld2 (update-w
              big-mutrec
              (store-stobjs-ins
               names stobjs-in-lst
               (putprop-x-lst2

; Warning: We rely on these 'formals properties, placed in reverse order from
; names, in the function termination-theorem-fn-subst (and its supporting
; functions).

                names 'formals arglists
                (putprop-x-lst1
                 names 'symbol-class symbol-class
                 wrld1)))))
      (untranslated-measures

; If the defun-mode is :program, or equivalently, the symbol-class is :program,
; then we don't need the measures, other than to check that non-recursive
; functions aren't given measures.

       (get-measures fives ctx state))
      (measures (translate-measures untranslated-measures
                                    (not (eq symbol-class :program))
                                    ctx wrld2
                                    state))
      (ruler-extenders-lst (get-ruler-extenders-lst symbol-class fives
                                                    ctx

; Warning: If you move this binding of ruler-extenders-lst, then consider
; whether the 'formals property is still set on the new functions in wrld2.

                                                    wrld2 state))
      (rel (get-unambiguous-xargs-flg
            :WELL-FOUNDED-RELATION
            fives
            (default-well-founded-relation wrld2)
            ctx state))
      (do-not-translate-hints
       (value (or assumep
                  (eq (ld-skip-proofsp state) 'initialize-acl2))))
      (hints (if (or do-not-translate-hints
                     (eq defun-mode :program))
                 (value nil)
               (let ((hints (get-hints fives)))
                 (if hints
                     (translate-hints+
                      (cons "Measure Lemma for" (car names))
                      hints
                      default-hints
                      ctx wrld2 state)
                   (value nil)))))
      (guard-hints (if (or do-not-translate-hints
                           (eq defun-mode :program))
                       (value nil)

; We delay translating the guard-hints until after the definition is installed,
; so that for example the hint setting :in-theory (enable foo), where foo is
; being defined, won't cause an error.

                     (value (append (get-guard-hints fives)
                                    default-hints))))
      (std-hints #+:non-standard-analysis
                 (cond
                  ((and std-p (not assumep))
                   (translate-hints+
                    (cons "Std-p for" (car names))
                    (get-std-hints fives)
                    default-hints
                    ctx wrld2 state))
                  (t (value nil)))
                 #-:non-standard-analysis
                 (value nil))
      (otf-flg (if do-not-translate-hints
                   (value nil)
                 (get-unambiguous-xargs-flg :OTF-FLG
                                            fives t ctx state)))
      (guard-debug (get-unambiguous-xargs-flg :GUARD-DEBUG
                                              fives

; Note: If you change the following default for guard-debug, then consider
; changing it in verify-guards as well, and fix the "Otherwise" message about
; :guard-debug in prove-guard-clauses.

                                              nil ; guard-debug default
                                              ctx state))
      (measure-debug (get-unambiguous-xargs-flg :MEASURE-DEBUG
                                                fives
                                                nil ; guard-debug default
                                                ctx state))
      (split-types-lst (get-boolean-unambiguous-xargs-flg-lst
                        :SPLIT-TYPES fives nil ctx state))
      (normalizeps (get-boolean-unambiguous-xargs-flg-lst
                    :NORMALIZE fives t ctx state)))
     (er-progn
      (cond
       ((not (and (symbolp rel)
                  (assoc-eq
                   rel
                   (global-val 'well-founded-relation-alist
                               wrld2))))
        (er soft ctx
            "The :WELL-FOUNDED-RELATION specified by XARGS must be a symbol ~
             which has previously been shown to be a well-founded relation.  ~
             ~x0 has not been. See :DOC well-founded-relation."
            rel))
       (t (value nil)))
      (let ((mp (cadr (assoc-eq
                       rel
                       (global-val 'well-founded-relation-alist
                                   wrld2)))))
        (er-let*
         ((bodies-and-bindings
           (translate-bodies non-executablep ; t or :program
                             names
                             arglists
                             (get-bodies fives)
                             stobjs-in-lst ; see "slight abuse" comment below
                             reclassifying-all-programp
                             ctx wrld2 state)))
         (let* ((bodies (car bodies-and-bindings))
                (bindings
                 (super-defun-wart-bindings
                  (cdr bodies-and-bindings)))
                #+:non-standard-analysis
                (non-classical-fns
                 (get-non-classical-fns bodies wrld2)))
           (er-progn
            (if assumep
                (value nil)
              (er-progn
               (chk-stobjs-out-bound names bindings ctx state)
               #+:non-standard-analysis
               (chk-no-recursive-non-classical
                non-classical-fns
                names mp rel measures bodies ctx wrld2 state)))
            (let* ((wrld30 (store-super-defun-warts-stobjs-in
                            names wrld2))
                   (wrld31 (store-stobjs-out names bindings wrld30))
                   (wrld3 #+:non-standard-analysis
                          (if (or std-p
                                  (null non-classical-fns))
                              wrld31
                            (putprop-x-lst1 names 'classicalp
                                            nil wrld31))
                          #-:non-standard-analysis
                          wrld31))
              (er-let* ((guards (translate-term-lst
                                 (get-guards fives split-types-lst nil wrld2)

; Warning: Keep this call of translate-term-lst in sync with translation of a
; guard in chk-defabsstobj-guard.

; Stobjs-out:
; Each guard returns one, non-stobj result.  This arg is used for each guard.
; By using stobjs-out '(nil) we enable the thorough checking of the use of
; state.  Thus, the above call ensures that guards do not modify (or return)
; state.  We are taking the conservative position because intuitively there is
; a confusion over the question of whether, when, and how often guards are run.
; By prohibiting them from modifying state we don't have to answer the
; questions about when they run.

                                                    '(nil)

; Logic-modep:
; Since guards have nothing to do with the logic, and since they may
; legitimately have mode :program, we set logic-modep to nil here.  This arg is
; used for each guard.

                                                    nil

; Known-stobjs-lst:
; Here is a slight abuse.  Translate-term-lst is expecting, in this
; argument, a list in 1:1 correspondence with its first argument,
; specifying the known-stobjs for the translation of corresponding
; terms.  But we are supplying the stobjs-in for the term, not the
; known-stobjs.  The former is a list of stobj flags and the latter is
; a list of stobj names, i.e., the list we supply may contain a NIL
; element where it should have no element at all.  This is allowed by
; stobjsp.  Technically we ought to map over the stobjs-in-lst and
; change each element to its collect-non-x nil.

                                                    stobjs-in-lst ctx

; Note the use of wrld3 instead of wrld2.  It is important that the proper
; stobjs-out be put on the new functions before we translate the guards!  When
; we first allowed the functions being defined to be used in their guards (in
; v3-6), we introduced a soundness bug found by Sol Swords just after the
; release of v4-0, as follows.

; (defun foo (x)
;    (declare (xargs :guard (or (consp x)
;                               (atom (foo '(a . b))))))
;    (mv (car x)
;        (mbe :logic (consp x)
;             :exec t)))
;
; (defthm bad
;    nil
;    :hints (("goal" :use ((:instance foo (x nil)))))
;    :rule-classes nil)

                                                    wrld3
                                                    state))
                        (split-types-terms
                         (translate-term-lst
                          (get-guards fives split-types-lst t wrld2)

; The arguments below are the same as those for the preceding call of
; translate-term-lst.

                          '(nil) nil stobjs-in-lst ctx wrld3 state)))
                (er-progn
                 (if (eq defun-mode :logic)

; Although translate checks for inappropriate calls of :program functions,
; translate11 and translate1 do not.

                     (er-progn
                      (chk-logic-subfunctions names names
                                              guards wrld3 "guard"
                                              ctx state)
                      (chk-logic-subfunctions names names
                                              split-types-terms wrld3
                                              "split-types expression"
                                              ctx state)
                      (chk-logic-subfunctions names names bodies
                                              wrld3 "body"
                                              ctx state))
                   (value nil))
                 (if (eq symbol-class :common-lisp-compliant)
                     (er-progn
                      (chk-common-lisp-compliant-subfunctions
                       names names guards wrld3 "guard" ctx state)
                      (chk-common-lisp-compliant-subfunctions
                       names names split-types-terms wrld3
                       "split-types expression" ctx state)
                      (chk-common-lisp-compliant-subfunctions
                       names names bodies wrld3 "body" ctx state))
                   (value nil))
                 (mv-let
                  (erp val state)
; This mv-let is just an aside that lets us conditionally check a bunch of
; conditions we needn't do in assumep mode.
                  (cond
                   (assumep (mv nil nil state))
                   (t
                    (let ((ignores (get-ignores fives))
                          (ignorables (get-ignorables fives))
                          (irrelevants-alist (get-irrelevants-alist fives)))
                      (er-progn
                       (chk-free-and-ignored-vars-lsts names
                                                       arglists
                                                       guards
                                                       split-types-terms
                                                       measures
                                                       ignores
                                                       ignorables
                                                       bodies
                                                       ctx state)
                       (chk-irrelevant-formals names arglists
                                               guards
                                               split-types-terms
                                               measures
                                               ignores
                                               ignorables
                                               irrelevants-alist
                                               bodies ctx state)
                       (chk-mutual-recursion names bodies ctx
                                             state)))))
                  (cond
                   (erp (mv erp val state))
                   (t (value (list 'chk-acceptable-defuns
                                   names
                                   arglists
                                   docs
                                   nil ; doc-pairs
                                   guards
                                   measures
                                   ruler-extenders-lst
                                   mp
                                   rel
                                   hints
                                   guard-hints
                                   std-hints ;nil for non-std
                                   otf-flg
                                   bodies
                                   symbol-class
                                   normalizeps
                                   reclassifying-all-programp
                                   wrld3
                                   non-executablep
                                   guard-debug
                                   measure-debug
                                   split-types-terms))))))))))))))))

(defun conditionally-memoized-fns (fns memoize-table)
  (declare (xargs :guard (and (symbol-listp fns)
                              (alistp memoize-table))))
  (cond ((endp fns) nil)
        (t
         (let ((alist (cdr (assoc-eq (car fns) memoize-table))))
           (cond
            ((and alist ; optimization
                  (let ((condition-fn (cdr (assoc-eq :condition-fn alist))))
                    (and condition-fn
                         (not (eq condition-fn t)))))
             (cons (car fns)
                   (conditionally-memoized-fns (cdr fns) memoize-table)))
            (t (conditionally-memoized-fns (cdr fns) memoize-table)))))))

;; Historical Comment from Ruben Gamboa:
;; I modified the function below to check for recursive
;; definitions using non-classical predicates.

(defun chk-acceptable-defuns (lst ctx wrld state #+:non-standard-analysis std-p)

; WARNING: This function installs a world, hence should only be called when
; protected by a revert-world-on-error.

; Rockwell Addition:  We now also return the non-executable flag.

; This function does all of the syntactic checking associated with defuns.  It
; causes an error if it doesn't like what it sees.  It returns the traditional
; 3 values of an error-producing, output-producing function.  However, the
; "real" value of the function is a list of items extracted from lst during the
; checking.  These items are:

;    names     - the names of the fns in the clique
;    arglists  - their formals
;    docs      - their documentation strings
;    pairs     - the (section-symbol . citations) pairs parsed from docs
;    guards    - their translated guards
;    measures  - their translated measure terms
;    ruler-extenders-lst
;              - their ruler-extenders
;    mp        - the domain predicate (e.g., o-p) for well-foundedness
;    rel       - the well-founded relation (e.g., o<)
;    hints     - their translated hints, to be used during the proofs of
;                the measure conjectures, all flattened into a single list
;                of hints of the form ((cl-id . settings) ...).
;    guard-hints
;              - like hints but to be used for the guard conjectures and
;                untranslated
;    std-hints (always returned, but only of interest when
;               #+:non-standard-analysis)
;              - like hints but to be used for the std-p conjectures
;    otf-flg   - t or nil, used as "Onward Thru the Fog" arg for prove
;    bodies    - their translated bodies
;    symbol-class
;              - :program, :ideal, or :common-lisp-compliant
;    normalizeps
;              - list of Booleans, used to determine for each fn in the clique
;                whether its body is to be normalized
;    reclassifyingp
;              - t or nil, t if this is a reclassifying from :program
;                with identical defs.
;    wrld      - a modified wrld in which the following properties
;                may have been stored for each fn in names:
;                  'formals, 'stobjs-in and 'stobjs-out
;    non-executablep - t, :program, or nil according to whether these defuns
;                  are to be non-executable.  Defuns with non-executable t may
;                  violate the translate conventions on stobjs.
;    guard-debug
;              - t or nil, used to add calls of EXTRA-INFO to guard conjectures
;    measure-debug
;              - t or nil, used to add calls of EXTRA-INFO to measure conjectures
;    split-types-terms
;              - list of translated terms, each corresponding to type
;                declarations made for a definition with XARGS keyword
;                :SPLIT-TYPES T

  (er-let*
   ((fives (chk-defuns-tuples lst nil ctx wrld state))

; Fives is a list in 1:1 correspondence with lst.  Each element of
; fives is a 5-tuple of the form (name args doc edcls body).  Consider the
; element of fives that corresponds to

;   (name args (DECLARE ...) "Doc" (DECLARE ...) body)

; in lst.  Then that element of fives is (name args "Doc" (...) body),
; where the ... is the cdrs of the DECLARE forms appended together.
; No translation has yet been applied to them.  The newness of name
; has not been checked yet either, though we know it is all but new,
; i.e., is a symbol in the right package.  We do know that the args
; are all legal.

    (names (value (strip-cars fives))))
   (er-progn
    (chk-no-duplicate-defuns names ctx state)
    (chk-xargs-keywords fives *xargs-keywords* ctx state)
    (er-let*
     ((tuple (chk-acceptable-defuns0 fives ctx wrld state)))
     (let* ((stobjs-in-lst (car tuple))
            (defun-mode (cadr tuple))
            (non-executablep (caddr tuple))
            (symbol-class (cdddr tuple))
            (rc (redundant-or-reclassifying-defunsp
                 defun-mode symbol-class (ld-skip-proofsp state) lst
                 ctx wrld
                 (ld-redefinition-action state)
                 fives non-executablep stobjs-in-lst
                 (default-state-vars t))))
       (cond
        ((eq rc 'redundant)
         (chk-acceptable-defuns-redundancy names ctx wrld state))
        ((eq rc 'verify-guards)

; We avoid needless complication by simply causing a polite error in this
; case.  If that proves to be too inconvenient for users, we could look into
; arranging for a call of verify-guards here.

         (chk-acceptable-defuns-verify-guards-er names ctx wrld state))
        #+hons
        ((and (eq rc 'reclassifying)
              (conditionally-memoized-fns names
                                          (table-alist 'memoize-table wrld)))

; We no longer recall exactly why we have this restriction.  However, after
; discussing this with Sol Swords we think it's because we tolerate all sorts
; of guard violations when dealing with :program mode functions, but we expect
; guards to be handled properly with :logic mode functions, including the
; condition function.  If we verify termination and guards for the memoized
; function but not the condition, that could present a problem.  Quite possibly
; we can relax this check somewhat after thinking things through -- e.g., if
; the condition function is a guard-verified :logic mode function -- if there
; is demand for such an enhancement.

         (er soft ctx
             "It is illegal to verify termination (i.e., convert from ~
              :program to :logic mode) for function~#0~[~/s~] ~&0, because ~
              ~#0~[it is~/they are~] currently memoized with conditions; you ~
              need to unmemoize ~#0~[it~/them~] first.  See :DOC memoize."
             (conditionally-memoized-fns names
                                         (table-alist 'memoize-table wrld))))
        (t
         (chk-acceptable-defuns1 names fives
                                 stobjs-in-lst defun-mode symbol-class rc
                                 non-executablep ctx wrld state
                                 #+:non-standard-analysis std-p))))))))

#+:non-standard-analysis
(defun build-valid-std-usage-clause (arglist body)
  (cond ((null arglist)
         (list (mcons-term* 'standardp body)))
        (t (cons (mcons-term* 'not
                              (mcons-term* 'standardp (car arglist)))
                 (build-valid-std-usage-clause (cdr arglist) body)))))

#+:non-standard-analysis
(defun verify-valid-std-usage (names arglists bodies hints otf-flg
                                     ttree0 ctx ens wrld state)
  (cond
   ((null (cdr names))
    (let* ((name (car names))
           (arglist (car arglists))
           (body (car bodies)))
      (mv-let
       (cl-set cl-set-ttree)
       (clean-up-clause-set
        (list (build-valid-std-usage-clause arglist body))
        ens
        wrld ttree0 state)
       (pprogn
        (increment-timer 'other-time state)
        (let ((displayed-goal (prettyify-clause-set
                               cl-set
                               (let*-abstractionp state)
                               wrld)))
          (mv-let
           (col state)
           (io? event nil (mv col state)
                (cl-set displayed-goal name)
                (cond ((null cl-set)
                       (fmt "~%The admission of ~x0 as a classical function ~
                             is trivial."
                            (list (cons #\0 name))
                            (proofs-co state)
                            state
                            nil))
                      (t
                       (fmt "~%The admission of ~x0 as a classical function ~
                             with non-classical body requires that it return ~
                             standard values for standard arguments.  That ~
                             is, we must prove~%~%Goal~%~Q12."
                            (list (cons #\0 name)
                                  (cons #\1 displayed-goal)
                                  (cons #\2 (term-evisc-tuple nil state)))
                            (proofs-co state)
                            state
                            nil))))
           (pprogn
            (increment-timer 'print-time state)
            (cond
             ((null cl-set)
              (value (cons col cl-set-ttree)))
             (t
              (mv-let (erp ttree state)
                      (prove (termify-clause-set cl-set)
                             (make-pspv ens wrld state
                                        :displayed-goal displayed-goal
                                        :otf-flg otf-flg)
                             hints ens wrld ctx state)
                      (cond (erp (mv t nil state))
                            (t
                             (mv-let
                              (col state)
                              (io? event nil (mv col state)
                                   (name)
                                   (fmt "That completes the proof that ~x0 ~
                                         returns standard values for standard ~
                                         arguments."
                                        (list (cons #\0 name))
                                        (proofs-co state)
                                        state
                                        nil))
                              (pprogn
                               (increment-timer 'print-time state)
                               (value (cons col
                                            (cons-tag-trees
                                             cl-set-ttree
                                             ttree)))))))))))))))))
   (t (er soft ctx
          "It is not permitted to use MUTUAL-RECURSION to define non-standard ~
           predicates.  Use MUTUAL-RECURSION to define standard versions of ~
           these predicates, then use DEFUN-STD to generalize them, if that's ~
           what you mean."))))

(defun union-eq1-rev (x y)

; This is like (union-eq x y) but is tail recursive and
; reverses the order of the new elements.

  (cond ((endp x) y)
        ((member-eq (car x) y)
         (union-eq1-rev (cdr x) y))
        (t (union-eq1-rev (cdr x) (cons (car x) y)))))

(defun collect-hereditarily-constrained-fnnames (names wrld ans)
  (cond ((endp names) ans)
        (t (let ((name-fns (getpropc (car names)
                                     'hereditarily-constrained-fnnames
                                     nil
                                     wrld)))
             (cond
              (name-fns
               (collect-hereditarily-constrained-fnnames
                (cdr names)
                wrld
                (union-eq1-rev name-fns ans)))
              (t (collect-hereditarily-constrained-fnnames
                  (cdr names) wrld ans)))))))

(defun putprop-hereditarily-constrained-fnnames-lst (names bodies wrld)

; Names is a non-empty list of defined function names and bodies is in
; 1:1 correspondence.  We set the hereditarily-constrained-fnnames
; property of each name in names, by collecting all the function names
; appearing in the bodies and filtering for the hereditarily
; constrained ones.  We also add each name in names to the world global
; defined-hereditarily-constrained-fns.

; A ``hereditarily constrained function'' is either a constrained
; function, e.g., one introduced with defchoose or encapsulate, or
; else a defun'd function whose definition involves a hereditarily
; constrained function.  The value of the
; hereditarily-constrained-fnnames property of a function symbol, fn,
; is a list of all the hereditarily constrained functions involved
; (somehow) in the definition of fn.  If the list is nil, the symbol
; is in no sense constrained, but is either a primitive, e.g., car, or
; an ordinary defun'd function.  If the list is a singleton, then its
; only element must necessarily be the fn itself and we know therefore
; that fn is constrained.  Otherwise, the list has at least two
; elements and that fn is a defined but hereditarily constrained
; function.  For example, if h is constrained and map-h is defined in
; terms of h, then the property for h will be '(h) and that for map-h
; will be '(map-h h).  Mutually recursive cliques will list all the
; fns in the clique.  One cannot assume the car of the list is fn.

  (let ((fnnames (collect-hereditarily-constrained-fnnames
                  (all-fnnames1 t bodies nil)
                  wrld
                  nil)))
    (cond
     (fnnames
      (global-set
       'defined-hereditarily-constrained-fns
       (append names
               (global-val 'defined-hereditarily-constrained-fns wrld))
       (putprop-x-lst1 names 'hereditarily-constrained-fnnames
                       (append names fnnames)
                       wrld)))
     (t wrld))))

(defun defuns-fn1 (tuple ens big-mutrec names arglists docs pairs guards
                         guard-hints std-hints otf-flg guard-debug bodies
                         symbol-class normalizeps split-types-terms
                         non-executablep
                         #+:non-standard-analysis std-p
                         ctx state)

; See defuns-fn0.

; WARNING: This function installs a world.  That is safe at the time of this
; writing because this function is only called by defuns-fn0, which is only
; called by defuns-fn, where that call is protected by a revert-world-on-error.

  #-:non-standard-analysis
  (declare (ignore std-hints))
  (declare (ignore docs pairs))
  (let ((col (car tuple))
        (subversive-p (cdddr tuple)))
    (er-let*
     ((wrld1 (update-w big-mutrec (cadr tuple)))
      (wrld2 (update-w big-mutrec
                       (putprop-defun-runic-mapping-pairs names t wrld1)))
      (wrld3 (update-w big-mutrec
                       (putprop-x-lst2-unless names 'guard guards *t*
                                              wrld2)))
      (wrld4 (update-w big-mutrec
                       (putprop-x-lst2-unless names 'split-types-term
                                              split-types-terms *t* wrld3)))
      #+:non-standard-analysis
      (assumep
       (value (or (eq (ld-skip-proofsp state) 'include-book)
                  (eq (ld-skip-proofsp state)
                      'include-book-with-locals))))
      #+:non-standard-analysis
      (col/ttree1 (if (and std-p (not assumep))
                      (verify-valid-std-usage names arglists bodies
                                              std-hints otf-flg
                                              (caddr tuple)
                                              ctx ens wrld4 state)
                    (value (cons col (caddr tuple)))))
      #+:non-standard-analysis
      (col (value (car col/ttree1)))
      (ttree1 #+:non-standard-analysis
              (value (cdr col/ttree1))
              #-:non-standard-analysis
              (value (caddr tuple))))
     (mv-let
      (wrld5 ttree2)
      (putprop-body-lst names arglists bodies normalizeps
                        (getpropc (car names) 'recursivep nil wrld4)
                        (make-controller-alist names wrld4)
                        #+:non-standard-analysis std-p
                        ens wrld4 wrld4 nil)
      (er-progn
       (update-w big-mutrec wrld5)
       (mv-let
        (wrld6 ttree2 state)
        (putprop-type-prescription-lst names
                                       subversive-p
                                       (fn-rune-nume (car names)
                                                     t nil wrld5)
                                       ens wrld5 ttree2 state)
        (er-progn
         (update-w big-mutrec wrld6)
         (er-let*
          ((wrld7 (update-w big-mutrec
                            (putprop-level-no-lst names wrld6)))
           (wrld8 (update-w big-mutrec
                            (putprop-primitive-recursive-defunp-lst
                             names wrld7)))
           (wrld9 (update-w big-mutrec
                            (putprop-hereditarily-constrained-fnnames-lst
                             names bodies wrld8)))
           (wrld10 (update-w big-mutrec
                             (put-invariant-risk
                              names
                              bodies
                              non-executablep
                              symbol-class
                              guards
                              wrld9)))
           (wrld11 (update-w big-mutrec
                             (putprop-x-lst1
                              names 'pequivs nil
                              (putprop-x-lst1 names 'congruences nil wrld10))))
           (wrld11a (update-w big-mutrec
                              (putprop-x-lst1 names 'coarsenings nil
                                              wrld11)))
           (wrld11b (update-w big-mutrec
                              (if non-executablep
                                  (putprop-x-lst1 names 'non-executablep
                                                  non-executablep
                                                  wrld11a)
                                wrld11a))))
          (let ((wrld12
                 #+:non-standard-analysis
                 (if std-p
                     (putprop-x-lst1
                      names 'unnormalized-body nil
                      (putprop-x-lst1 names 'def-bodies nil wrld11b))
                   wrld11b)
                 #-:non-standard-analysis
                 wrld11b))
            (pprogn
             (print-defun-msg names ttree2 wrld12 col state)
             (set-w 'extension wrld12 state)
             (cond
              ((eq symbol-class :common-lisp-compliant)
               (er-let*
                ((guard-hints (if guard-hints
                                  (translate-hints
                                   (cons "Guard for" (car names))
                                   guard-hints
                                   ctx wrld12 state)
                                (value nil)))
                 (pair (verify-guards-fn1 names guard-hints otf-flg
                                          guard-debug ctx state)))

; Pair is of the form (wrld . ttree3) and we return a pair of the same
; form, but we must combine this ttree with the ones produced by the
; termination proofs and type-prescriptions.

                (value
                 (cons (car pair)
                       (cons-tag-trees ttree1
                                       (cons-tag-trees
                                        ttree2
                                        (cdr pair)))))))
              (t (value
                  (cons wrld12
                        (cons-tag-trees ttree1
                                        ttree2)))))))))))))))

(defun defuns-fn0 (names arglists docs pairs guards measures
                         ruler-extenders-lst mp rel hints guard-hints std-hints
                         otf-flg guard-debug measure-debug bodies symbol-class
                         normalizeps split-types-terms non-executablep
                         #+:non-standard-analysis std-p
                         ctx wrld state)

; WARNING: This function installs a world.  That is safe at the time of this
; writing because this function is only called by defuns-fn, where that call is
; protected by a revert-world-on-error.

  (cond
   ((eq symbol-class :program)
    (defuns-fn-short-cut names docs pairs guards measures split-types-terms
      bodies non-executablep ctx wrld state))
   (t
    (let ((ens (ens state))
          (big-mutrec (big-mutrec names)))
      (er-let*
       ((tuple (put-induction-info names arglists
                                   measures
                                   ruler-extenders-lst
                                   bodies
                                   mp rel
                                   hints
                                   otf-flg
                                   big-mutrec
                                   measure-debug
                                   ctx ens wrld state)))
       (defuns-fn1
         tuple
         ens
         big-mutrec
         names
         arglists
         docs
         pairs
         guards
         guard-hints
         std-hints
         otf-flg
         guard-debug
         bodies
         symbol-class
         normalizeps
         split-types-terms
         non-executablep
         #+:non-standard-analysis std-p
         ctx
         state))))))

(defun strip-non-hidden-package-names (known-package-alist)
  (if (endp known-package-alist)
      nil
    (let ((package-entry (car known-package-alist)))
      (cond ((package-entry-hidden-p package-entry)
             (strip-non-hidden-package-names (cdr known-package-alist)))
            (t (cons (package-entry-name package-entry)
                     (strip-non-hidden-package-names (cdr known-package-alist))))))))

(defun in-package-fn (str state)

; Important Note:  Don't change the formals of this function without
; reading the *initial-event-defmacros* discussion in axioms.lisp.

  (cond ((not (stringp str))
         (er soft 'in-package
             "The argument to IN-PACKAGE must be a string, but ~
              ~x0 is not."
             str))
        ((not (find-non-hidden-package-entry str (known-package-alist state)))
         (er soft 'in-package
             "The argument to IN-PACKAGE must be a known package ~
              name, but ~x0 is not.  The known packages are ~*1"
             str
             (tilde-*-&v-strings
              '&
              (strip-non-hidden-package-names (known-package-alist state))
              #\.)))
        (t (let ((state (f-put-global 'current-package str state)))
             (value str)))))

(defun defstobj-functionsp (names embedded-event-lst)

; This function determines whether all the names in names are being defined as
; part of a defstobj or defabsstobj event.  If so, it returns the name of the
; stobj; otherwise, nil.

; Explanation of the context: Defstobj and defabsstobj use defun to define the
; recognizers, accessors and updaters.  But these events must install their own
; versions of the raw lisp code for these functions, to take advantage of the
; single-threadedness of their use.  So what happens when defstobj or
; defabsstobj executes (defun name ...), where name is say an updater?
; Defuns-fn is run on the singleton list '(name) and the axiomatic def of name.
; At the end of the normal processing, defuns-fn computes a CLTL-COMMAND for
; name.  When this command is installed by add-trip, it sets the
; symbol-function of name to the given body.  Add-trip also installs a *1*name
; definition by oneifying the given body.  But in the case of a defstobj (or
; defabsstobj) function we do not want the first thing to happen: we will
; compute a special body for the name and install it with its own CLTL-COMMAND.
; So to handle defstobj and defabsstobj, defuns-fn tells add-trip not to set
; the symbol-function.  This is done by setting the ignorep flag in the defun
; CLTL-COMMAND.  So the question arises: how does defun know that the name it
; is defining is being introduced by defstobj or defabsstobj?  This function
; answers that question.

; Note that *1*name should still be defined as the oneified axiomatic body, as
; with any defun.  Before v2-9 we introduced the *1* function at defun time.
; (We still do so if the function is being reclassified with an identical body,
; from :program mode to :logic mode, since there is no need to redefine its
; symbol-function -- -- indeed its installed symbol-function might be
; hand-coded as part of these sources -- but add-trip must generate a *1*
; body.)  Because stobj functions can be inlined as macros (via the :inline
; keyword of defstobj), we need to defer definition of the *1* function until
; after the raw Lisp def (which may be a macro) has been added.  We failed to
; do this in v2-8, which caused an error in CCL as reported by John
; Matthews:

;   (defstobj tiny-state
;           (progc :type (unsigned-byte 10) :initially 0)
;         :inline t)
;
;   (update-progc 3 tiny-state)

; Note: At the moment, defstobj and defabsstobj do not introduce any mutually
; recursive functions.  So every name is handled separately by defuns-fns.
; Hence, names, here, is always a singleton, though we do not exploit that.
; Also, embedded-event-lst is always a list ee-entries, each being a cons with
; the name of some superevent like ENCAPSULATE, INCLUDE-BOOK, or DEFSTOBJ
; (which is also used for DEFABSSTOBJ), in the car.  The ee-entry for the most
; immediate superevent is the first on the list.  At the moment, defstobj and
; defabsstobj do not use encapsulate or other structuring mechanisms.  Thus,
; the defstobj ee-entry will be first on the list.  But we look up the list,
; just in case.  The ee-entry for a defstobj or defabsstobj is of the form
; (defstobj name names) where name is the name of the stobj and names is the
; list of recognizers, accessors and updaters and their helpers.

  (let ((temp (assoc-eq 'defstobj embedded-event-lst)))
    (cond ((and temp
                (subsetp-equal names (caddr temp)))
           (cadr temp))
          (t nil))))

; The following definition only supports non-standard analysis, but it seems
; reasonable to allow it in the standard version too.
; #+:non-standard-analysis
(defun index-of-non-number (lst)
  (cond
   ((endp lst) nil)
   ((acl2-numberp (car lst))
    (let ((temp (index-of-non-number (cdr lst))))
      (and temp (1+ temp))))
   (t 0)))

#+:non-standard-analysis
(defun non-std-error (fn index formals actuals)
  (er hard fn
   "Function ~x0 was called with the ~n1 formal parameter, ~x2, bound to ~
    actual parameter ~x3, which is not a (standard) number.  This is illegal, ~
    because the arguments of a function defined with defun-std must all be ~
    (standard) numbers."
   fn (list index) (nth index formals) (nth index actuals)))

#+:non-standard-analysis
(defun non-std-body (name formals body)

; The body below is a bit inefficient in the case that we get an error.
; However, we do not expect to get errors very often, and the alternative is to
; bind a variable that we have to check is not in formals.

  `(if (index-of-non-number (list ,@formals))
       (non-std-error ',name
                      (index-of-non-number ',formals)
                      ',formals
                      (list ,@formals))
     ,body))

#+:non-standard-analysis
(defun non-std-def-lst (def-lst)
  (if (and (consp def-lst) (null (cdr def-lst)))
      (let* ((def (car def-lst))
             (fn (car def))
             (formals (cadr def))
             (body (car (last def))))
        `((,@(butlast def 1)
             ,(non-std-body fn formals body))))
    (er hard 'non-std-def-lst
        "Unexpected call; please contact ACL2 implementors.")))

; Rockwell Addition:  To support non-executable fns we have to be able,
; at defun time, to introduce an undefined function.  So this stuff is
; moved up from other-events.lisp.

(defun make-udf-insigs (names wrld)
  (cond
   ((endp names) nil)
   (t (cons (list (car names)
                  (formals (car names) wrld)
                  (stobjs-in (car names) wrld)
                  (stobjs-out (car names) wrld))
            (make-udf-insigs (cdr names) wrld)))))

(defun intro-udf (insig wrld)

; This function is called during pass 2 of an encapsulate.  See the comment
; below about guards.

  (case-match
   insig
   ((fn formals stobjs-in stobjs-out)
    (putprop
     fn 'coarsenings nil
     (putprop
      fn 'congruences nil
      (putprop
       fn 'pequivs nil
       (putprop
        fn 'constrainedp t ; 'constraint-lst comes later
        (putprop
         fn 'hereditarily-constrained-fnnames (list fn)
         (putprop
          fn 'symbol-class :COMMON-LISP-COMPLIANT
          (putprop-unless
           fn 'stobjs-out stobjs-out nil
           (putprop-unless
            fn 'stobjs-in stobjs-in nil
            (putprop
             fn 'formals formals
             (putprop fn 'guard

; We are putting a guard of t on a signature function, even though a :guard
; other than t might have been specified for this function.  This may seem to
; be an error.  However, proofs are skipped during that pass, so an incorrect
; guard proof obligation will not be noticed anyhow.  Instead, guard
; verification takes place during the first pass of the encapsulate, which
; could indeed present a problem if we are not careful.  However, we call
; function bogus-exported-compliants to check that we are not making that sort
; of mistake; see bogus-exported-compliants.

                      *t*
                      wrld)))))))))))
  (& (er hard 'store-signature "Unrecognized signature!" insig))))

(defun intro-udf-lst1 (insigs wrld)
  (cond ((null insigs) wrld)
        (t (intro-udf-lst1 (cdr insigs)
                           (intro-udf (car insigs)
                                      wrld)))))

(defun intro-udf-lst2 (insigs kwd-value-list-lst)

; Warning: Keep this in sync with oneify-cltl-code.

; Insigs is a list of internal form signatures, e.g., ((fn1 formals1 stobjs-in1
; stobjs-out1) ...), and we convert it to a "def-lst" suitable for giving the
; Common Lisp version of defuns, ((fn1 formals1 body1) ...), where each bodyi
; is just a throw to 'raw-ev-fncall with the signal that says there is no body.
; Note that the body we build (in this ACL2 code) is a Common Lisp body but not
; an ACL2 expression!

; kwd-value-list-lst is normally a list that corresponds by position to insigs,
; each of whose elements associates keywords with values; in particular it can
; associate :guard with the guard for the corresponding element of insigs.
; However, kwd-value-list-lst can be the atom 'non-executable-programp, which
; we use for proxy functions (see :DOC defproxy), i.e., :program mode functions
; with the xarg declaration :non-executable :program.

  (cond
   ((null insigs) nil)
   (t (cons `(,(caar insigs)
              ,(cadar insigs)
              ,@(cond
                 ((eq kwd-value-list-lst 'non-executable-programp)
                  '((declare (xargs :non-executable :program))))
                 (t (let ((guard
                           (cadr (assoc-keyword :guard
                                                (car kwd-value-list-lst)))))
                      (and guard
                           `((declare (xargs :guard ,guard)))))))
              ,(null-body-er (caar insigs)
                             (cadar insigs)
                             t))
            (intro-udf-lst2 (cdr insigs)
                            (if (eq kwd-value-list-lst 'non-executable-programp)
                                'non-executable-programp
                              (cdr kwd-value-list-lst)))))))

(defun intro-udf-lst (insigs kwd-value-list-lst wrld)

; Insigs is a list of internal form signatures.  We know all the function
; symbols are new in wrld.  We declare each of them to have the given formals,
; stobjs-in, and stobjs-out, symbol-class :common-lisp-compliant, a guard of t
; and constrainedp of t.  We also arrange to execute a defun in the underlying
; Common Lisp so that each function is defined to throw to an error handler if
; called from ACL2.

  (if (null insigs)
      wrld
    (put-cltl-command `(defuns nil nil
                         ,@(intro-udf-lst2 insigs
                                           (and (not (eq kwd-value-list-lst t))
                                                kwd-value-list-lst)))
                      (intro-udf-lst1 insigs wrld)
                      wrld)))

(defun defun-ctx (def-lst state event-form #+:non-standard-analysis std-p)
  #-acl2-infix (declare (ignore event-form state))
  (make-ctx-for-event
   event-form
   (cond ((atom def-lst)
          (msg "( DEFUNS ~x0)"
               def-lst))
         ((atom (car def-lst))
          (cons 'defuns (car def-lst)))
         ((null (cdr def-lst))
          #+:non-standard-analysis
          (if std-p
              (cons 'defun-std (caar def-lst))
            (cons 'defun (caar def-lst)))
          #-:non-standard-analysis
          (cons 'defun (caar def-lst)))
         (t (msg *mutual-recursion-ctx-string*
                 (caar def-lst))))))

(defun install-event-defuns (names event-form def-lst0 symbol-class
                                   reclassifyingp non-executablep pair ctx wrld
                                   state)

; See defuns-fn.

  (install-event (cond ((null (cdr names)) (car names))
                       (t names))
                 event-form
                 (cond ((null (cdr names)) 'defun)
                       (t 'defuns))
                 (cond ((null (cdr names)) (car names))
                       (t names))
                 (cdr pair)
                 (cond
                  (non-executablep
                   `(defuns nil nil
                      ,@(intro-udf-lst2
                         (make-udf-insigs names wrld)
                         (and (eq non-executablep :program)
                              'non-executable-programp))))
                  (t `(defuns ,(if (eq symbol-class :program)
                                   :program
                                 :logic)
                        ,(if reclassifyingp
                             'reclassifying
                           (if (defstobj-functionsp names
                                 (global-val 'embedded-event-lst
                                             (car pair)))
                               (cons 'defstobj

; The following expression computes the stobj name, e.g., $S, for
; which this defun is supportive.  The STOBJS-IN of this function is
; built into the expression created by oneify-cltl-code
; namely, in the throw-raw-ev-fncall expression (see
; oneify-fail-form).  We cannot compute the STOBJS-IN of the function
; accurately from the world because $S is not yet known to be a stobj!
; This problem is a version of the super-defun-wart problem.


                                     (defstobj-functionsp names
                                       (global-val
                                        'embedded-event-lst
                                        (car pair))))
                             nil))
                        ,@def-lst0)))
                 t
                 ctx
                 (car pair)
                 state))

(defun defuns-fn (def-lst state event-form #+:non-standard-analysis std-p)

; Important Note:  Don't change the formals of this function without
; reading the *initial-event-defmacros* discussion in axioms.lisp.

; On Guards

; When a function symbol fn is defund the user supplies a guard, g, and a
; body b.  Logically speaking, the axiom introduced for fn is

;    (fn x1...xn) = b.

; After admitting fn, the guard-related properties are set as follows:

; prop                after defun

; body                   b*
; guard                  g
; unnormalized-body      b
; type-prescription      computed from b
; symbol-class           :ideal

; * We actually normalize the above.  During normalization we may expand some
; boot-strap non-rec fns.

; In addition, we magically set the symbol-function of fn

; symbol-function        b

; and the symbol-function of *1*fn as a program which computes the logical
; value of (fn x).  However, *1*fn is quite fancy because it uses the raw body
; in the symbol-function of fn if fn is :common-lisp-compliant, and may signal
; a guard error if 'guard-checking-on is set to other than nil or :none.  See
; oneify-cltl-code for the details.

; Observe that the symbol-function after defun may be a form that
; violates the guards on primitives.  Until the guards in fn are
; checked, we cannot let raw Common Lisp evaluate fn.

; Intuitively, we think of the Common Lisp programmer intending to defun (fn
; x1...xn) to be b, and is declaring that the raw fn can be called only on
; arguments satisfying g.  The need for guards stems from the fact that there
; are many Common Lisp primitives, such as car and cdr and + and *, whose
; behavior outside of their guarded domains is unspecified.  To use these
; functions in the body of fn one must "guard" fn so that it is never called in
; a way that would lead to the violation of the primitive guards.  Thus, we
; make a formal precondition on the use of the Common Lisp program fn that the
; guard g, along with the tests along the various paths through body b, imply
; each of the guards for every subroutine in b.  We also require that each of
; the guards in g be satisfied.  This is what we mean when we say fn is
; :common-lisp-compliant.

; It is, however, often impossible to check the guards at defun time.  For
; example, if fn calls itself recursively and then gives the result to +, we
; would have to prove that the guard on + is satisfied by fn's recursive
; result, before we admit fn.  In general, induction may be necessary to
; establish that the recursive calls satisfy the guards of their masters;
; hence, it is probably also necessary for the user to formulate general lemmas
; about fn to establish those conditions.  Furthermore, guard checking is no
; longer logically necessary and hence automatically doing it at defun time may
; be a waste of time.

  (with-ctx-summarized
   (defun-ctx def-lst state event-form #+:non-standard-analysis std-p)
   (let ((wrld (w state))
         (def-lst0
           #+:non-standard-analysis
           (if std-p
               (non-std-def-lst def-lst)
             def-lst)
           #-:non-standard-analysis
           def-lst)
         (event-form (or event-form (list 'defuns def-lst))))
     (revert-world-on-error
      (er-let*
       ((tuple (chk-acceptable-defuns def-lst ctx wrld state
                                      #+:non-standard-analysis std-p)))

; Chk-acceptable-defuns puts the 'formals, 'stobjs-in and 'stobjs-out
; properties (which are necessary for the translation of the bodies).
; All other properties are put by the defuns-fn0 call below.

       (cond
        ((eq tuple 'redundant)
         (stop-redundant-event ctx state))
        (t
         (enforce-redundancy
          event-form ctx wrld
          (let ((names (nth 1 tuple))
                (arglists (nth 2 tuple))
                (docs (nth 3 tuple))
                (pairs (nth 4 tuple))
                (guards (nth 5 tuple))
                (measures (nth 6 tuple))
                (ruler-extenders-lst (nth 7 tuple))
                (mp (nth 8 tuple))
                (rel (nth 9 tuple))
                (hints (nth 10 tuple))
                (guard-hints (nth 11 tuple))
                (std-hints (nth 12 tuple))
                (otf-flg (nth 13 tuple))
                (bodies (nth 14 tuple))
                (symbol-class (nth 15 tuple))
                (normalizeps (nth 16 tuple))
                (reclassifyingp (nth 17 tuple))
                (wrld (nth 18 tuple))
                (non-executablep (nth 19 tuple))
                (guard-debug (nth 20 tuple))
                (measure-debug (nth 21 tuple))
                (split-types-terms (nth 22 tuple)))
            (er-let*
             ((pair (defuns-fn0
                      names
                      arglists
                      docs
                      pairs
                      guards
                      measures
                      ruler-extenders-lst
                      mp
                      rel
                      hints
                      guard-hints
                      std-hints
                      otf-flg
                      guard-debug
                      measure-debug
                      bodies
                      symbol-class
                      normalizeps
                      split-types-terms
                      non-executablep
                      #+:non-standard-analysis std-p
                      ctx
                      wrld
                      state)))

; Pair is of the form (wrld . ttree).

             (er-progn
              (chk-assumption-free-ttree (cdr pair) ctx state)
              (install-event-defuns names event-form def-lst0 symbol-class
                                    reclassifyingp non-executablep pair ctx wrld
                                    state))))))))))
        :event-type 'defun))

(defun defun-fn (def state event-form #+:non-standard-analysis std-p)

; Important Note:  Don't change the formals of this function without
; reading the *initial-event-defmacros* discussion in axioms.lisp.

; The only reason this function exists is so that the defmacro for
; defun is in the form expected by primordial-event-defmacros.

  (defuns-fn (list def) state
    (or event-form (cons 'defun def))
    #+:non-standard-analysis std-p))

; Here we develop the :args keyword command that will print all that
; we know about a function.

(defun args-fn (name state)
  (io? temporary nil (mv erp val state)
       (name)
       (let ((wrld (w state))
             (channel (standard-co state)))
         (cond
          ((eq name 'return-last)
           (pprogn (fms "Special form, basic to ACL2.  See :DOC return-last."
                        nil channel state nil)
                   (value name)))
          ((and (symbolp name)
                (function-symbolp name wrld))
           (let* ((formals (formals name wrld))
                  (stobjs-in (stobjs-in name wrld))
                  (stobjs-out (stobjs-out name wrld))
                  (guard (untranslate (guard name nil wrld) t wrld))
                  (tp (find-runed-type-prescription
                       (list :type-prescription name)
                       (getpropc name 'type-prescriptions nil wrld)))
                  (tpthm (cond (tp (untranslate
                                    (access type-prescription tp :corollary)
                                    t wrld))
                               (t nil)))
                  (constraint (mv-let
                               (some-name constraint-lst)
                               (constraint-info name wrld)
                               (cond ((eq constraint-lst *unknown-constraints*)
                                      :unknown-from-dependent-clause-processor)
                                     (some-name
                                      (untranslate (conjoin constraint-lst)
                                                   t wrld))
                                     (t t)))))
             (pprogn
              (fms "Function         ~x0~|~
               Formals:         ~y1~|~
               Signature:       ~y2~|~
               ~                 => ~y3~|~
               Guard:           ~q4~|~
               Guards Verified: ~y5~|~
               Defun-Mode:      ~@6~|~
               Type:            ~#7~[built-in (or unrestricted)~/~q8~]~|~
               ~#9~[~/Constraint:  ~qa~|~]~
               ~%"
                   (list (cons #\0 name)
                         (cons #\1 formals)
                         (cons #\2 (cons name
                                         (prettyify-stobj-flags stobjs-in)))
                         (cons #\3 (prettyify-stobjs-out stobjs-out))
                         (cons #\4 guard)
                         (cons #\5 (eq (symbol-class name wrld)
                                       :common-lisp-compliant))
                         (cons #\6 (defun-mode-string (fdefun-mode name wrld)))
                         (cons #\7 (if tpthm 1 0))
                         (cons #\8 tpthm)
                         (cons #\9 (if (eq constraint t) 0 1))
                         (cons #\a constraint))
                   channel state nil)
              (value name))))
          ((and (symbolp name)
                (getpropc name 'macro-body nil wrld))
           (let ((args (macro-args name wrld))
                 (guard (untranslate (guard name nil wrld) t wrld)))
             (pprogn
              (fms "Macro ~x0~|~
               Macro Args:  ~y1~|~
               Guard:       ~Q23~|~
               ~%"
                   (list (cons #\0 name)
                         (cons #\1 args)
                         (cons #\2 guard)
                         (cons #\3 (term-evisc-tuple nil state)))
                   channel state nil)
              (value name))))
          ((member-eq name '(let lambda declare quote))
           (pprogn (fms "Special form, basic to the Common Lisp language.  ~
                         See for example CLtL."
                        nil channel state nil)
                   (value name)))
          (t (er soft :args
                 "~x0 is neither a function symbol nor a macro name."
                 name))))))

(defmacro args (name)
  (list 'args-fn name 'state))

; We now develop the code for verify-termination, a macro that is essentially
; a form of defun.

(defun make-verify-termination-def (old-def new-dcls wrld)

; Old-def is a def tuple that has previously been accepted by defuns.  For
; example, if is of the form (fn args ...dcls... body), where dcls is a list of
; at most one doc string and possibly many DECLARE forms.  New-dcls is a new
; list of dcls (known to satisfy plausible-dclsp).  We create a new def tuple
; that uses new-dcls instead of ...dcls... but which keeps any member of the
; old dcls not specified by the new-dcls except for the :mode (if any), which
; is replaced by :mode :logic.

  (let* ((fn (car old-def))
         (args (cadr old-def))
         (body (car (last (cddr old-def))))
         (dcls (butlast (cddr old-def) 1))
         (new-fields (dcl-fields new-dcls))
         (modified-old-dcls (strip-dcls
                             (add-to-set-eq :mode new-fields)
                             dcls)))
    (assert$
     (not (getpropc fn 'non-executablep nil wrld))
     `(,fn ,args
           ,@new-dcls
           ,@(if (and (not (member-eq :mode new-fields))
                      (eq (default-defun-mode wrld) :program))
                 '((declare (xargs :mode :logic)))
               nil)
           ,@modified-old-dcls
           ,body))))

(defun make-verify-termination-defs-lst (defs-lst lst wrld)

; Defs-lst is a list of def tuples as previously accepted by defuns.  Lst is
; a list of tuples supplied to verify-termination.  Each element of a list is
; of the form (fn . dcls) where dcls satisfies plausible-dclsp, i.e., is a list
; of doc strings and/or DECLARE forms.  We copy defs-lst, modifying each member
; by merging in the dcls specified for the fn in lst.  If some fn in defs-lst
; is not mentioned in lst, we don't modify its def tuple except to declare it
; of :mode :logic.

  (cond
   ((null defs-lst) nil)
   (t (let ((temp (assoc-eq (caar defs-lst) lst)))
        (cons (make-verify-termination-def (car defs-lst) (cdr temp) wrld)
              (make-verify-termination-defs-lst (cdr defs-lst) lst wrld))))))

(defun chk-acceptable-verify-termination1 (lst clique fn1 ctx wrld state)

; Lst is the input to verify-termination.  Clique is a list of function
; symbols, fn1 is a member of clique (and used for error reporting only).  Lst
; is putatively of the form ((fn . dcls) ...)  where each fn is a member of
; clique and each dcls is a plausible-dclsp, as above.  That means that each
; dcls is a list containing documentation strings and DECLARE forms mentioning
; only TYPE, IGNORE, and XARGS.  We do not check that the dcls are actually
; legal because what we will ultimately do with them in verify-termination-fn
; is just create a modified definition to submit to defuns.  Thus, defuns will
; ultimately approve the dcls.  By construction, the dcls submitted to
; verify-termination will find their way, whole, into the submitted defuns.  We
; return nil or cause an error according to whether lst satisfies the
; restrictions noted above.

  (cond ((null lst) (value nil))
        ((not (and (consp (car lst))
                   (symbolp (caar lst))
                   (function-symbolp (caar lst) wrld)
                   (plausible-dclsp (cdar lst))))
         (er soft ctx
             "Each argument to verify-termination must be of the form (name ~
              dcl ... dcl), where each dcl is either a DECLARE form or a ~
              documentation string.  The DECLARE forms may contain TYPE, ~
              IGNORE, and XARGS entries, where the legal XARGS keys are ~&0.  ~
              The argument ~x1 is illegal.  See :DOC verify-termination."
             *xargs-keywords*
             (car lst)))
        ((not (member-eq (caar lst) clique))
         (er soft ctx
             "The function symbols whose termination is to be verified must ~
              all be members of the same clique of mutually recursive ~
              functions.  ~x0 is not in the clique of ~x1.  The clique of ~x1 ~
              consists of ~&2.  See :DOC verify-termination."
             (caar lst) fn1 clique))
        (t (chk-acceptable-verify-termination1 (cdr lst) clique fn1 ctx wrld
                                               state))))

(defun uniform-defun-modes (defun-mode clique wrld)

; Defun-Mode should be a defun-mode.  Clique is a list of fns.  If defun-mode is
; :program then we return :program if every element of clique is
; :program; else nil.  If defun-mode is :logic we return :logic if
; every element of clique is :logic; else nil.

  (cond ((null clique) defun-mode)
        ((programp (car clique) wrld)
         (and (eq defun-mode :program)
              (uniform-defun-modes defun-mode (cdr clique) wrld)))
        (t (and (eq defun-mode :logic)
                (uniform-defun-modes defun-mode (cdr clique) wrld)))))

(defun chk-acceptable-verify-termination (lst ctx wrld state)

; We check that lst is acceptable input for verify-termination.  To be
; acceptable, lst must be of the form ((fn . dcls) ...) where each fn is the
; name of a function, all of which are in the same clique and are in :program
; mode, not non-executable, where each dcls above is a plausible-dclsp.  We
; cause an error or return (value nil).

  (cond
   ((and (consp lst)
         (consp (car lst))
         (symbolp (caar lst)))
    (cond
     ((not (function-symbolp (caar lst) wrld))
      (er soft ctx
          "The symbol ~x0 is not a function symbol in the current ACL2 world."
          (caar lst)))
     ((not (programp (caar lst) wrld))

; If (caar lst) was introduced by encapsulate, then recover-defs-lst below will
; cause an implementation error.  So we short-circuit our checks here,
; especially given since the uniform-defun-modes assertion below suggests that
; all functions should then be in :logic mode.  Eventually, we will generate
; the empty list of definitions and treat the verify-termination as redundant,
; except: as a courtesy to the user, we may cause an error here if the function
; could not have been upgraded from :program mode.

      (cond ((getpropc (caar lst) 'constrainedp nil wrld)
             (er soft ctx
                 "The :LOGIC mode function symbol ~x0 was originally ~
                  introduced introduced not with DEFUN, but ~#1~[as a ~
                  constrained function~/with DEFCHOOSE~].  So ~
                  VERIFY-TERMINATION does not make sense for this function ~
                  symbol."
                 (caar lst)
                 (cond ((getpropc (caar lst) 'defchoose-axiom nil wrld)
                        1)
                       (t 0))))
            (t (value :redundant))))
     ((getpropc (caar lst) 'non-executablep nil wrld)
      (er soft ctx
          "The :PROGRAM mode function symbol ~x0 is declared non-executable, ~
           so ~x1 is not legal for this symbol.  Such functions are intended ~
           only for hacking with defattach; see :DOC defproxy."
          (caar lst)
          'verify-termination
          'defun))
     (t
      (let ((clique (get-clique (caar lst) wrld)))
        (assert$

; We maintain the invariant that all functions in a mutual-recursion clique
; have the same defun-mode.  This assertion check is not complete; for all we
; know, lst involves two mutual-recursion nests, and only the one for (caar
; lst) has uniform defun-modes.  But we include this simple assertion to
; provide an extra bit of checking.

         (uniform-defun-modes (fdefun-mode (caar lst) wrld)
                              clique
                              wrld)
         (chk-acceptable-verify-termination1 lst clique (caar lst) ctx wrld
                                             state))))))
   ((atom lst)
    (er soft ctx
        "Verify-termination requires at least one argument."))
   (t (er soft ctx
          "The first argument supplied to verify-termination, ~x0, is not of ~
           the form (fn dcl ...)."
          (car lst)))))

(defun verify-termination1 (lst state)
  (let* ((lst (cond ((and (consp lst)
                          (symbolp (car lst)))
                     (list lst))
                    (t lst)))
         (ctx
          (cond ((null lst) "(VERIFY-TERMINATION)")
                ((and (consp lst)
                      (consp (car lst)))
                 (cond
                  ((null (cdr lst))
                   (cond
                    ((symbolp (caar lst))
                     (cond
                      ((null (cdr (car lst)))
                       (msg "( VERIFY-TERMINATION ~x0)" (caar lst)))
                      (t (msg "( VERIFY-TERMINATION ~x0 ...)" (caar lst)))))
                    ((null (cdr (car lst)))
                     (msg "( VERIFY-TERMINATION (~x0))" (caar lst)))
                    (t (msg "( VERIFY-TERMINATION (~x0 ...))" (caar lst)))))
                  ((null (cdr (car lst)))
                   (msg "( VERIFY-TERMINATION (~x0) ...)" (caar lst)))
                  (t (msg "( VERIFY-TERMINATION (~x0 ...) ...)" (caar lst)))))
                (t (cons 'VERIFY-TERMINATION lst))))
         (wrld (w state)))
    (er-let* ((temp (chk-acceptable-verify-termination lst ctx wrld state)))
      (let ((defs (if (eq temp :redundant)
                      nil
                    (recover-defs-lst (caar lst) wrld))))
        (value (make-verify-termination-defs-lst
                defs
                lst wrld))))))

(defun verify-termination-boot-strap-fn (lst state event-form)
  (cond
   ((global-val 'boot-strap-flg (w state))
    (when-logic

; It is convenient to use when-logic so that we skip verify-termination during
; pass1 of the boot-strap in axioms.lisp.

     "VERIFY-TERMINATION"
     (let ((event-form (or event-form
                           (cons 'VERIFY-TERMINATION lst))))
       (er-let*
        ((verify-termination-defs-lst (verify-termination1 lst state)))
        (defuns-fn
          verify-termination-defs-lst
          state
          event-form
          #+:non-standard-analysis
          nil)))))
   (t

; We do not allow users to use 'verify-termination-boot-strap.  Why?  See the
; comment in redundant-or-reclassifying-defunp0 about "verify-termination is
; now just a macro for make-event", and see the discussion about make-event at
; the end of :doc verify-termination.

    (er soft 'verify-termination-boot-strap
        "~x0 may only be used while ACL2 is being built.  Use ~x1 instead."
        'verify-termination-boot-strap
        'verify-termination))))

(defmacro when-logic3 (str x)
  (list 'if
        '(eq (default-defun-mode-from-state state)
             :program)
        (list 'er-progn
              (list 'skip-when-logic (list 'quote str) 'state)
              (list 'value ''(value-triple nil)))
        x))

(defun verify-termination-fn (lst state)
  (when-logic3

; We originally used when-logic here so that we would skip verify-termination during
; pass1 of the boot-strap in axioms.lisp.  Now we use
; verify-termination-boot-strap for that purpose, but we continue the same
; convention, since by now users might rely on it.

; We could always return a defuns form, but the user may find it more pleasing
; to see a defun when there is a single definition, so we return a defun form
; in that case.

   "VERIFY-TERMINATION"
   (er-let*
       ((verify-termination-defs-lst (verify-termination1 lst state)))
     (value (cond ((null verify-termination-defs-lst)
                   '(value-triple :redundant))
                  ((null (cdr verify-termination-defs-lst))
                   (cons 'defun (car verify-termination-defs-lst)))
                  (t
                   (cons 'defuns verify-termination-defs-lst)))))))

; When we defined instantiablep we included the comment that a certain
; invariant holds between it and the axioms.  The functions here are
; not used in the system but can be used to check that invariant.
; They were not defined earlier because they use event tuples.

(defun fns-used-in-axioms (lst wrld ans)

; Intended for use only by check-out-instantiablep.

  (cond ((null lst) ans)
        ((and (eq (caar lst) 'event-landmark)
              (eq (cadar lst) 'global-value)
              (eq (access-event-tuple-type (cddar lst)) 'defaxiom))

; In this case, (car lst) is a tuple of the form

; (event-landmark global-value . tuple)

; where tuple is a defaxiom of some name, namex, and we are interested
; in all the function symbols occurring in the formula named namex.

         (fns-used-in-axioms (cdr lst)
                             wrld
                             (all-ffn-symbs (formula
                                             (access-event-tuple-namex
                                              (cddar lst))
                                             nil
                                             wrld)
                                            ans)))
        (t (fns-used-in-axioms (cdr lst) wrld ans))))

(defun check-out-instantiablep1 (fns wrld)

; Intended for use only by check-out-instantiablep.

  (cond ((null fns) nil)
        ((instantiablep (car fns) wrld)
         (cons (car fns) (check-out-instantiablep1 (cdr fns) wrld)))
        (t (check-out-instantiablep1 (cdr fns) wrld))))

(defun check-out-instantiablep (wrld)

; See the comment in instantiablep.

  (let ((bad (check-out-instantiablep1 (fns-used-in-axioms wrld wrld nil)
                                       wrld)))
    (cond
     ((null bad) "Everything checks")
     (t (er hard 'check-out-instantiablep
         "The following functions are instantiable and shouldn't be:~%~x0"
         bad)))))
