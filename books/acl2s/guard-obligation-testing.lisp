(in-package "ACL2")

; The idea here is to do body contract testing. One interesting issue
; here is that the generation of the proof obligations will fail if
; one uses the ACL2 code around guards, verify-guards,
; guard-obligation, etc. when functions whose guards have not been
; verified are used. In the case of proving theorems, of course you
; can't verify guards of functions that use non-guard-verified
; functions. But, when testing properties (and even when testing body
; contracts! I should generate all the proof obligations that I can,
; using any guard information I have. This is a *preliminary* hack at
; doing that.

; Things that come to mind that should be improved. I should support
; program mode functions. Right now, I expect that errors will be
; generated. 

; I just removed the checks that throw an error if they find
; non-guard-verified functions. I have to check that this really works
; and to write a reasonable spec, but I don't have the cycles to do
; that right now.
;
; I added this to properties, but I should also add it to
; definec/defunc to deal with body contract testing. TODO.
;
; The functions I redefined are from defuns.lisp and they are:
; chk-acceptable-verify-guards-formula-cmp
; chk-common-lisp-compliant-subfunctions-cmp
;
; The rest of the functions here are just copied from defuns.lisp and
; renamed so that I have the appropriate high-level version of
; guard-obligation. The renaming scheme is to start with the ACL2 name
; and add -testing to the end of the function name.

(set-ignore-ok t)
(set-irrelevant-formals-ok t)
(set-state-ok t)

(program)
; Renamed and commented out some error checking code.
(defun chk-common-lisp-compliant-subfunctions-cmp-testing (names0 names terms wrld str
                                                          ctx)

; See chk-common-lisp-compliant-subfunctions and note especially its warning
; about how not all names have been defined in wrld.

  (cond ((null names) (value-cmp nil))
        (t (let* ((fns (set-difference-eq
                        (all-fnnames1-exec
                         t ; list of terms (all-fnnames-exec (car terms))
                         (cons (car terms)
                               (if (global-val 'boot-strap-flg wrld)
                                   nil
                                   (collect-guards-and-bodies
                                    (collect-certain-lambda-objects
                                     :well-formed
                                     (car terms)
                                     wrld
                                     nil))))
                         (if (global-val 'boot-strap-flg wrld)
                             nil
                             (all-fnnames! nil :inside nil
                                           (car terms)
                                           nil wrld nil)))
                        names0))
                  (bad (collect-non-common-lisp-compliants fns wrld)))
             (cond
              ;; (bad
              ;;  (er-cmp ctx "The ~@0 for ~x1 calls the function~#2~[ ~&2~/s ~
              ;;               ~&2~], the guards of which have not yet been ~
              ;;               verified.  See :DOC verify-guards."
              ;;          str (car names) bad))
              (t (mv-let (warrants unwarranteds)
                   (if (global-val 'boot-strap-flg wrld)
                       (mv nil nil)
                       (warrants-for-tamep-lambdap-lst
                        (collect-certain-lambda-objects :well-formed
                                                        (car terms)
                                                        wrld nil)
                        wrld nil nil))
                   (declare (ignore warrants))
                   (cond
                    (unwarranteds
                     (er-cmp ctx "The ~@0 for ~x1 applies the function~#2~[ ~
                                  ~&2~/s ~&2~] which ~#2~[is~/are~] not yet ~
                                  warranted.  Lambda objects containing ~
                                  unwarranted function symbols are not ~
                                  provably tame and can't be applied.  See ~
                                  :DOC verify-guards."
                             str (car names) unwarranteds))
                    (t (chk-common-lisp-compliant-subfunctions-cmp-testing
                        names0 (cdr names) (cdr terms)
                        wrld str ctx))))))))))

; Renamed and commented out some error checking code.
(defun chk-acceptable-verify-guards-formula-cmp-testing (name x ctx wrld state-vars)
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
                    "The guards for the given formula cannot be verified ~
                     because it has the wrong syntactic form for evaluation, ~
                     perhaps due to multiple-value or stobj restrictions.  ~
                     See :DOC verify-guards.")))))
     (erp
      (er-cmp ctx
              "The guards for ~x0 cannot be verified because its formula has ~
               the wrong syntactic form for evaluation, perhaps due to ~
               multiple-value or stobj restrictions.  See :DOC verify-guards."
              (or name x)))
     ;; ((collect-non-common-lisp-compliants (all-fnnames-exec term)
     ;;                                      wrld)
     ;;  (er-cmp ctx
     ;;          "The formula ~#0~[named ~x1~/~x1~] contains a call of the ~
     ;;           function~#2~[ ~&2~/s ~&2~], the guards of which have not yet ~
     ;;           been verified.  See :DOC verify-guards."
     ;;          (if name 0 1)
     ;;          (or name x)
     ;;          (collect-non-common-lisp-compliants (all-fnnames-exec term)
     ;;                                              wrld)))
     (t
      (er-progn-cmp
       (chk-common-lisp-compliant-subfunctions-cmp-testing
        (list name) (list name)
        (list term)
        wrld "formula" ctx)
       (value-cmp (cons :term term)))))))

; renamed 
(defun chk-acceptable-verify-guards-cmp-testing (name rrp guard-simplify ctx wrld
                                              state-vars)

; We check that name is acceptable input for verify-guards and either cause an
; error or return the list of objects from which guard clauses should be
; generated or (when rrp = t, we might return 'redundant).  We're more precise
; below.

; Below we describe a case analysis on name, a Test to perform, and the
; Non-Erroneous Value to return if the test succeeds.  If a Test fails or the
; case analysis on name is exhausted without specifying an answer, an error is
; caused.  When name is a function symbol we'll use names to be the set of
; function symbols in name's clique.

; * if name is a :common-lisp-compliant function symbol or lambda expression
;   and rrp = t:
;   Test: T
;   Non-Erroneous Value: 'redundant.

; * if name is a function symbol:
;   Test: is every subfunction in the definitions of names -- including symbols
;   in quoted well-formed lambda objects -- except possibly names themselves
;   :common-lisp-compliant?
;   Non-erroneous Value: names

; * if name is a theorem name:
;   Test: is every function used in the formula :common-lisp-compliant?
;   Note: This test leaves out quoted well-formed lambda objects from consideration
;   because we're not really interested in fast execution of instances of thms.
;   Non-erroneous Value: (list name)

; * if name is a lambda object:
;   Test: is name a well-formed lambda object and every function symbol in it
;   (including in the :guard and body) -- including symbols in quoted
;   well-formed lambda objects :common-lisp-compliant?
;   Non-erroneous Value: (list name)

; * if name is a lambda$ expression
;   Test: can name be translated non-erroneously to name', where name' is a
;   well-formed lambda object, and is every function in name' (including in the
;   :guard and body) -- including symbols in well-formed lambda objects
;   :common-lisp-compliant?
;   Non-erroneous Value: (list name')

; Otherwise, an error is caused.

; One might wonder when two peers in a clique can have different symbol-classes,
; e.g., how is it possible (as implied above) for name to be :ideal but for one
; of its peers to be :common-lisp-compliant or :program?  Redefinition.  For
; example, the clique could have been admitted as :logic and then later one
; function in it redefined as :program.  Because redefinition invalidates the
; system, we could do anything in this case.  What we choose to do is to cause
; an error and say you can't verify the guards of any of the functions in the
; nest.

; Motivation: When rrp is t, we get one of three answers: the redundancy signal
; (if name is compliant), a list of objects (either names or well-formed lambda
; expressions) from which to generate guard obligations (if such obligations
; can be generated), or an error.  If rrp is nil, we get either the objects
; from which to generate guard obligations or an error.  The ``objects'' are
; all either names or well-formed lambda expressions.  We use rrp = nil when we
; are trying to (re-)generate the guard obligations as by
; verify-guards-formula.  Note that rrp = nil is more strict than rrp = t in
; the sense that with rrp=t we might be 'redundant but with rrp=nil the same
; name might generate an error because it's in a clique that, due to
; redefinition, now has a :program mode function in it.

  (er-let*-cmp
   ((ignore
     (cond

; Keep this in sync with guard-simplify-p and a similar check in
; chk-acceptable-defuns1.

      ((member-eq guard-simplify '(t :limited))
       (value-cmp nil))
      (t (er-cmp ctx "~@0" (guard-simplify-msg guard-simplify)))))
    (name
     (cond
      ((symbolp name)
       (value-cmp name))
      ((and (consp name)
            (or (eq (car name) 'lambda)
                (eq (car name) 'lambda$)))
       (cond
        ((eq (car name) 'lambda)
         (cond
          ((well-formed-lambda-objectp name wrld)

; We call hons-copy-lambda-object? here for the same reason that is given in
; translate11-lambda-object.  Our convention is to call
; hons-copy-lambda-object?  on QUOTEd lambda objects and name isn't quoted.  So
; we quote it just so the error message is nice.  And then we unquote the
; returned value when there's no error.

           (mv-let (erp val)
             (hons-copy-lambda-object? (kwote name))
             (cond
              (erp (er-cmp ctx "~@0" val))
              (t (value-cmp (unquote val))))))
          (t (er-cmp ctx
                     "~x0 is not a well-formed LAMBDA expression.  See :DOC ~
                      verify-guards."
                     name))))
        (t
         (mv-let (erp val bindings)
           (translate11-lambda-object
            name
            '(nil) ; stobjs-out
            nil    ; bindings
            nil    ; known-stobjs
            nil    ; flet-alist
            name
            'verify-guards
            wrld
            state-vars
            nil)
           (declare (ignore bindings))
           (mv erp (if erp val (unquote val)))))))
      (t (er-cmp ctx
                 "~x0 is not a symbol, a lambda object, or a lambda$ ~
                  expression.  See :DOC verify-guards."
                 name)))))

; Name is now either a symbol or a consp, and if it is a consp it is a
; well-formed lambda object.

   (let ((symbol-class
          (cond ((symbolp name)
                 (symbol-class name wrld))
                ((member-equal name
                               (global-val 'common-lisp-compliant-lambdas wrld))
                 :common-lisp-compliant)
                (t

; Name is known to be a well-formed lambda, but it may contain all classes of
; badged symbols, including :program mode ones.  We don't know how to classify
; the lambda and so we'll choose the worst possibility.  But as of this writing
; symbol-class is not used in the lambda case below!

                 :program))))
     (cond
      ((and rrp
            (eq symbol-class :common-lisp-compliant))
       (value-cmp 'redundant))
      ((consp name)

; Name is a well-formed lambda object.  If every fn in the guard and body is
; compliant (so guard obligations can be computed) we return the list
; containing the well-formed lambda expression derived from name which is now
; the value of the variable of that name.

       (let* ((names (list name))
              (guards (list (lambda-object-guard name)))
              (bodies (list (lambda-object-body name))))
         (er-progn-cmp
          (chk-common-lisp-compliant-subfunctions-cmp-testing
           names names guards wrld "guard" ctx)
          (chk-common-lisp-compliant-subfunctions-cmp-testing
           names names bodies wrld "body" ctx)
          (value-cmp names))))

; Old stuff:
;               (bad-guard-fns
;                (collect-non-common-lisp-compliants (all-fnnames guard) wrld))
;               (bad-body-fns
;                (collect-non-common-lisp-compliants (all-fnnames body) wrld)))
;
; ; Any non-compliant fns in the guard or body are known to be :ideal because
; ; :program mode fns are not allowed in well-formed lambda objects.
;
;          (cond
;           (bad-guard-fns
;            (er-cmp ctx
;                    "This lambda expression cannot be guard verified because ~
;                     the guard mentions ~&0 which ~#0~[is~/are~] not guard ~
;                     verified: ~x1."
;                    bad-guard-fns
;                    name))
;           (bad-body-fns
;            (er-cmp ctx
;                    "This lambda expression cannot be guard verified because ~
;                     the body mentions ~&0 which ~#0~[is~/are~] not guard ~
;                     verified: ~x1."
;                    bad-body-fns
;                    name))
;           (t (value-cmp (list name))))
;          ))
      ((getpropc name 'theorem nil wrld)

; Theorems are of either symbol-class :ideal or :common-lisp-compliant.

       (er-progn-cmp
        (chk-acceptable-verify-guards-formula-cmp-testing
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
                           "One or more of the mutually-recursive peers of ~
                            ~x0 ~#1~[was not defined in :logic mode~/either ~
                            was not defined in :logic mode or has already had ~
                            its guards verified~].  The offending ~
                            function~#2~[ is~/s are~] ~&2.  We thus cannot ~
                            verify the guards of ~x0.  This situation can ~
                            arise only through redefinition."
                           name
                           (if (eq symbol-class :ideal) 1 0)
                           bad-names))
                  (t
                   (er-progn-cmp
                    (chk-common-lisp-compliant-subfunctions-cmp-testing
                     names names
                     (guard-lst names nil wrld)
                     wrld "guard" ctx)
                    (chk-common-lisp-compliant-subfunctions-cmp-testing
                     names names
                     (getprop-x-lst names 'unnormalized-body wrld)
                     wrld "body" ctx)
                    (value-cmp names))))))
         (otherwise ; the symbol-class :common-lisp-compliant is handled above
          (er-cmp ctx
                  "Implementation error: Unexpected symbol-class, ~x0, for ~
                   the function symbol ~x1."
                  symbol-class name))))
      (t (let ((fn (deref-macro-name name (macro-aliases wrld))))
           (er-cmp ctx
                   "~x0 is not a function symbol or a theorem name in the ~
                    current ACL2 world.  ~@1"
                   name
                   (cond ((eq fn name) "See :DOC verify-guards.")
                         (t (msg "Note that ~x0 is a macro-alias for ~x1.  ~
                                  Consider calling verify-guards with ~
                                  argument ~x1 instead, or use ~
                                  verify-guards+.  See :DOC verify-guards, ~
                                  see :DOC verify-guards+, and see :DOC ~
                                  macro-aliases-table."
                                 name fn))))))))))

; Renamed
(defun guard-obligation-clauses-testing (x guard-debug ens wrld state)

; X is of one of three forms: (i) a list of function names and/or well-formed
; lambda object, (ii) a singleton list containing a theorem name, or (iii)
; (:term . y) where y must be a translated term.  Returns two results.  The
; first is a set of clauses justifying the guards x, i.e., in case (i) the
; guards of all the functions in x, (ii) the guards of the theorem's formula,
; or (iii) the guards of term y.  The second result is an assumption-free
; tag-tree justifying that set of clauses.

; Ens may be an actual ens or :do-not-simplify, in which case no simplification
; that depends on the current set of enabled rules will take place in producing
; the guard clauses.

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
              nil
              nil)
             (mv cl-set cl-set-ttree)))
          ((and (consp x)
                (null (cdr x))
                (symbolp (car x))
                (getpropc (car x) 'theorem nil wrld))
           (mv-let (cl-set cl-set-ttree)
             (guard-clauses+
              (getpropc (car x) 'theorem nil wrld)
              (and guard-debug (car x))
              nil ;stobj-optp = nil
              nil ens wrld
              (f-get-global 'safe-mode state)
              (gc-off state)
              nil
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
      (clean-up-clause-set cl-set
                           (if (eq ens :do-not-simplify) nil ens)
                           wrld cl-set-ttree state)

; Cl-set-ttree is still 'assumption-free.

      (mv cl-set cl-set-ttree))))

; Renamed
(defun guard-obligation-testing (x rrp guard-debug guard-simplify ctx state)
  (let* ((wrld (w state))
         (namep (and (symbolp x)
                     (not (keywordp x))
                     (not (defined-constant x wrld)))))
    (er-let*-cmp
     ((y
       (cond (namep (chk-acceptable-verify-guards-cmp-testing
                     x rrp guard-simplify ctx wrld (default-state-vars t)))
             (t (chk-acceptable-verify-guards-formula-cmp-testing
                 nil x ctx wrld (default-state-vars t))))))
     (cond
      ((and namep (eq y 'redundant))
       (value-cmp :redundant))
      (t (mv-let (cl-set cl-set-ttree)
                 (guard-obligation-clauses-testing
                  y guard-debug
                  (if (guard-simplify-p guard-simplify ctx)
                      (ens state)
                    :do-not-simplify)
                  wrld state)
                 (value-cmp (list* y cl-set cl-set-ttree))))))))

(set-ignore-ok nil)
(set-irrelevant-formals-ok nil)
(set-state-ok nil)
