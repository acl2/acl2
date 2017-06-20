; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "defmacroq")

(defxdoc make-termination-theorem
  :parents (termination-theorem history measure kestrel-utilities)
  :short "Create a copy of a function's termination theorem that calls stubs."
  :long "<p>The @(':')@(tsee termination-theorem) @(see lemma-instance)
 provides a way to re-use a recursive definition's termination (measure)
 theorem.  You might find it convenient, however, to create a @('defthm') event
 for that theorem.  Moreover, a termination theorem can mention the function
 symbol that is being defined, but it may be convenient to have a version of
 that theorem that instead mentions an unconstrained function symbol, which can
 support the use of @(see functional-instantiation).</p>

 <p>The form @('(make-termination-theorem f)') will create such a @('defthm')
 event, named @('F$TTHM'), with @(':')@(tsee rule-classes) @('nil'), whose body
 is the termination-theorem for @('f'), but modified to replace calls of
 @('f').  Here is a small example; for more extensive examples see @(see
 community-book)
 @('kestrel/utilities/make-termination-theorem-tests.lisp').  Suppose we submit
 the following definition.</p>

 @({
 (defun f (x)
   (if (consp x)
       (and (f (caar x))
            (f (cddr x)))
     x))
 })

 <p>Here is the termination-theorem for @('f').</p>

 @({
 ACL2 !>:tthm f
  (AND (O-P (ACL2-COUNT X))
       (OR (NOT (CONSP X))
           (O< (ACL2-COUNT (CAR (CAR X)))
               (ACL2-COUNT X)))
       (OR (NOT (CONSP X))
           (NOT (F (CAR (CAR X))))
           (O< (ACL2-COUNT (CDDR X))
               (ACL2-COUNT X))))
 ACL2 !>
 })

 <p>We now create the corresponding @('defthm') event shown below.</p>

 @({
 ACL2 !>(make-termination-theorem f)

 Summary
 Form:  ( MAKE-EVENT (ER-LET* ...))
 Rules: NIL
 Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.01)
  (DEFTHM F$TTHM
          (AND (O-P (ACL2-COUNT X))
               (OR (NOT (CONSP X))
                   (O< (ACL2-COUNT (CAR (CAR X)))
                       (ACL2-COUNT X)))
               (OR (NOT (CONSP X))
                   (NOT (F$STUB (CAR (CAR X))))
                   (O< (ACL2-COUNT (CDDR X))
                       (ACL2-COUNT X))))
          :HINTS ((\"Goal\" :USE (:TERMINATION-THEOREM F ((F F$STUB)))
                          :IN-THEORY (THEORY 'MINIMAL-THEORY)))
          :RULE-CLASSES NIL)
 ACL2 !>
 })

 <p>Notice that the call of @('f') in the termination-theorem has been
 replaced, in the @('defthm') form above, by a new function symbol,
 @('f$stub').  That new symbol was introduced using @(tsee defstub), which has
 no constraints, thus easing the application of @(see functional-instantiation)
 to this theorem.</p>

 @({
 General Form:

 (make-termination-theorem Fun
                           :subst S        ; default described below
                           :thm-name N     ; default Fun$TTHM
                           :rule-classes R ; default nil
                           :verbose Vflg   ; default nil
                           :show-only Sflg ; default nil
                           )
 })

 <p>where no keyword argument is evaluated unless wrapped in @(':eval'), as
 @('make-termination-theorem') is defined with @('defmacroq'); see @(see
 defmacroq).  Evaluation of this form produces a @(tsee defthm) event based
 on the @(see termination-theorem) of @('Fun'), taking into account the
 arguments as follows.</p>

 <ul>

 <li>@('Fun') is a function symbol defined by recursion (possibly @(tsee
 mutual-recursion)).</li>

 <li>@('S') is a functional substitution, that is, a list of 2-element lists of
 symbols @('(fi gi)').  For each symbol @('gi') that is not a function symbol
 in the current @(see world), a suitable @(tsee defstub) event will be
 introduced for @('gi').  If @('Fun') is singly recursive then there will be a
 single such pair @('(Fun g)'); otherwise @('Fun') is defined by @(tsee
 mutual-recursion) and each @('fi') must have been defined together with
 @('Fun'), in the same @('mutual-recursion') form.  If @(':subst') is omitted
 then each suitable function symbol @('f') &mdash; that is, @('Fun') as well
 as, in the case of mutual recursion, the others defined with @('Fun') &mdash;
 is paired with the result of adding the suffix @('\"$STUB\"') to the @(see
 symbol-name) of @('f').</li>

 <li>@('R') is the @(':')@(tsee rule-classes) argument of the generated
 @('defthm') event.</li>

 <li>Output is mostly suppressed by default, but is enabled when @('Vflg') is
 not @('nil').</li>

 <li>If @('Sflg') is not @('nil'), then the generated @('defthm') event @('EV')
 will not be submitted; instead, it will be returned in an error-triple @('(mv
 nil EV state)').</li>

 </ul>")

(program)
(set-state-ok t)

(defun make-termination-theorem-subst (fns)
  (cond ((endp fns) nil)
        (t (cons (list (car fns)
                       (add-suffix (car fns) "$STUB"))
                 (make-termination-theorem-subst (cdr fns))))))

(defun make-termination-theorem-defstub-events (subst wrld)
  (cond ((endp subst) nil)
        ((function-symbolp (cadar subst) wrld)
         (make-termination-theorem-defstub-events (cdr subst) wrld))
        (t (cons `(defstub ,(cadar subst)
                    ,(formals (caar subst) wrld)
                    t)
                 (make-termination-theorem-defstub-events (cdr subst) wrld)))))

(defun make-termination-theorem-fn (fn subst subst-p thm-name rule-classes
                                       verbose wrld ctx state)
  (let ((fn-nest (and (symbolp fn)
                      (getpropc fn 'recursivep nil wrld)))
        (thm-name (or thm-name (add-suffix fn "$TTHM"))))
    (cond
     ((null fn-nest)
      (er soft ctx
          "The first argument, ~x0, is not a recursively defined function ~
           symbol."
          fn))
     ((and subst-p
           (not (doublet-style-symbol-to-symbol-alistp subst)))
      (er soft ctx
          "The :subst argument, is not a list of pairs of the form (old-sym ~
           new-sym)"
          subst))
     ((and subst-p
           (not (subsetp-eq (strip-cars subst) fn-nest)))
      (cond
       ((null (cdr fn-nest))
        (er soft ctx
            "The :subst argument has key ~x0, which should be ~x1."
            (caar subst)
            fn))
       (t
        (er soft ctx
            "The keys of the substitution specified by :subst must all be ~
             introduced in the same mutual-recursion as the given function ~
             symbol, ~x0.  But this fails for ~&1."
            fn
            (set-difference-eq (strip-cars subst) fn-nest)))))
     (t (let* ((subst (if subst-p
                          subst
                        (make-termination-theorem-subst fn-nest)))
               (tformula (sublis-fn-simple (pairlis$ (strip-cars subst)
                                                     (strip-cadrs subst))
                                           (termination-theorem fn wrld)))
               (formula (untranslate tformula t wrld))
               (thm `(defthm ,thm-name
                       ,formula
                       :hints (("Goal"
                                :use (:termination-theorem ,fn ,subst)
                                :in-theory (theory 'minimal-theory)))
                       :rule-classes ,rule-classes)))
          (value `(with-output
                    :off :all
                    :gag-mode nil ; prover output suppressed, so avoid goals
                    :on error
                    :stack :push
                    (progn
                      ,@(make-termination-theorem-defstub-events subst wrld)
                      ,(if verbose `(with-output :stack :pop ,thm) thm)
                      (value-triple ',thm)))))))))

(defmacroq make-termination-theorem (fn &key
                                        (subst 'nil subst-p)
                                        thm-name rule-classes
                                        verbose show-only)
  `(make-event (er-let* ((event (make-termination-theorem-fn
                                 ,fn ,subst ,subst-p ,thm-name ,rule-classes
                                 ,verbose (w state)
                                 'make-termination-theorem state)))
                 (if ,show-only
                     (value `(value-triple ',event))
                   (value event)))))
