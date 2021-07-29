; Simplify-defun-sk Transformation -- Documentation
;
; Copyright (C) 2016, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file documents the simplify-defun-sk data transformation,
; which is used for simplifying a definition made with defun-sk.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc simplify-defun-sk
  :parents (apt)
  :short "Simplify the definition of a given function made with @(tsee defun-sk)."
  :long "
 <h3>Introduction</h3>

 <p>This macro is an interface to the @(tsee simplify) transformation for
 function symbols that the user (or a tool) introduces with @(tsee defun-sk) or
 the @(see soft::SOFT) tool, @('defun-sk2').  When successful, it creates a new
 such form by simplifying the body of the definition of such a function
 symbol.</p>

 <p>See @(see simplify-defun-sk-examples) for an introductory tutorial for
 @('simplify-defun-sk'), which presents an extensive series of examples.</p>

 <p>Evaluation of the form @('(simplify-defun-sk fn)') will attempt to define a
 new function, say, @('fn$1'), that is logically equivalent to the @(tsee
 defun-sk) definition of @('fn') but is simpler.  The new definition is also
 made with @('defun-sk').  In the rest of this documentation page, @('FN') will
 denote the input function symbol and @('NEW') will generally denote the new
 function symbol.</p>

 <p>Also see @(see simplify-defun) for an analogous utility for simplifying
 @(tsee defun) forms.</p>

 <p>A @('simplify-defun-sk') call causes an error if no simplification takes
 place or if the proof obligations fail to be met.  The implementation has been
 carefully orchestrated so that the proof obligations will generally succeed.
 When this is not the case, you may invoke @('show-simplify-defun-sk') with the
 same arguments in order to obtain the form that failed to be admitted, so that
 you can modify it manually.  Or equivalently, simply use keyword argument
 @(':show-only t') in your @('simplify-defun-sk') call.</p>

 <h3>General Form</h3>

 <p>The following form shows all the keyword arguments in alphabetical order,
 together with their default values (i.e., when the keyword is omitted).  No
 argument is evaluated, except that if an argument is of the form @('(:eval
 x)'), then the actual argument is the result of evaluting of @('x').  Note
 that @('FN') should be a function symbol previously defined with @(tsee
 defun-sk) or the @(see soft::SOFT) tool, @('defun-sk2'); thus,
 @('simplify-defun-sk') may be replaced by @(tsee simplify) to obtain an
 essentially equivalent call.</p>

 @({
 (simplify-defun-sk fn ; input function symbol previously defined with defun-sk
                    &key
                    :assumptions       ; default nil
                    :disable           ; default :none
                    :enable            ; default :none
                    :new-enable        ; default :auto
                    :new-name          ; default nil
                    :guard             ; default :auto
                    :guard-hints       ; default :auto
                    :must-simplify     ; default t
                    :print             ; default :result
                    :show-only         ; default nil
                    :rewrite           ; default :auto
                    :simplify-body     ; default t
                    :skolem-name       ; default nil
                    :thm-enable        ; default t
                    :thm-name          ; default :auto
                    :theory            ; default :none
                    :untranslate       ; default :nice
                    :verify-guards     ; default :auto
                    )
 })

 <h3>Inputs</h3>

 <p>
 @('FN')
 </p>
 <blockquote>

 <p>Denotes the target function to transform.</p>

 <p>Evaluation of @('(simplify-defun-sk FN ...)') assumes that the input
 symbol, @('FN'), is a @(':')@(tsee logic) mode function symbol defined with
 @('defun-sk') or with a macro expanding to a call of @('defun-sk').
 Successful evaluation admits a new @('defun-sk'), with the same formals as
 @('FN'), and a theorem equating @('FN') with the newly-defined function
 symbol.  Details, such as whether or not to perform guard verification, may be
 controlled by keyword parameters as described below.</p>

 <p>If @('FN') was defined using the @(see soft::SOFT) tool @('defun-sk2'),
 then the new function symbol is also introduced with @('defun-sk2').</p>

 </blockquote>

 <p>
 @(':assumptions') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Determines the assumptions for simplification.</p>

 <p>The value of @(':assumptions') must be a list of terms (not necessarily
 translated; see @(see acl2::term)) that only reference variables among the
 formal parameters of @('FN').  However, @(':assumptions') may be @(':guard'),
 which is equivalent to @(':assumptions (G)') where @('G') is the @(see guard)
 of @('FN'); and for @(':assumptions (A1 ... :guard ... An)'), @(':guard') is
 similarly replaced by @('G').  Below we imagine that @(':guard') has been
 replaced in these ways; let us assume below that the value of
 @(':assumptions') is a list that does not contain @(':guard').</p>

 <p>When @(':assumptions H') is supplied, all simplification will be performed
 assuming @('H''), where @('H'') is the result of simplifying @('H').</p>

 </blockquote>

 <p>
 @(':disable') &mdash; default @(':none')<br/>
 @(':enable') &mdash; default @(':none')
 </p>
 <blockquote>

 <p>Determine the theory for simplification.</p>

 <p>If @(':disable D') and @(':enable E') are supplied, then simplification
 will be performed in the theory @('(e/d* E D)').  Similarly, if only this
 @(':disable') or @(':enable') is supplied, then the theory will be @('(disable
 D)') or @('(enable E)'), respectively.  If either of these keywords is
 supplied, then it is illegal to supply @(':theory').  Also see the discussion
 below of the @(':theory') argument.  Note that @(':disable') may be useful for
 preserving calls of @(tsee prog2$), @(tsee ec-call), @(tsee time$), and other
 such operators that provide special behavior; see @(see
 acl2::return-last-blockers).</p>

 </blockquote>

 <p>
 @(':new-enable') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Determines whether the new function is enabled.</p>

 <p>If this keyword has value @('t') or @('nil'), then the new function symbol
 will be enabled or disabled, respectively.  Otherwise its value should be the
 keyword @(':auto'), and the new function symbol will be enabled or disabled
 according to whether the input function symbol is disabled or enabled,
 respectively.</p>

 </blockquote>

 <p>
 @(':guard') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Specify the new guard.</p>

 <p>The value of @(':guard') is a guard for the new function symbol, in place
 of the default of inheriting the guard of the input function symbol.</p>

 </blockquote>

 <p>
 @(':guard-hints') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Provides @(see acl2::hints) for verifying @(see guard)s of the generated
 function.  If this argument is supplied with value other than its default of
 @(':auto'), then that value becomes the @(':hints') of a @(tsee verify-guards)
 event.  Otherwise such hints are generated automatically.  See the discussion
 of @(':verify-guards') below for a discussion of guard verification and its
 automatically-generated hints.</p>

 </blockquote>

 <p>
 @(':must-simplify') &mdash; default @('t')
 </p>
 <blockquote>

 <p>This keyword specifies whether the simplified body must be different from
 the original body: yes, if the value is @('t') (the default), and no if the
 value is @('nil').  However, this keyword is ignored if the keyword
 @(':simplify-body') has value @('nil').</p>

 </blockquote>

 <p>
 @(':new-name') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Determines the name of the generated function.</p>

 <p>This value, if provided, becomes the function symbol of the generated
 definition.  Otherwise the generated function symbol is obtained by adding a
 suffix @('\"$n\"') to the input function symbol's name, for the least natural
 number @('n') will that results in a new function symbol.  Note: the value
 @('nil') is treated the same as @(':auto').</p>

 </blockquote>

 <p>
 @(':print') &mdash; default @(':result')
 </p>
 <blockquote>

 <p>Specify what to print.</p>

 <p>By default, only the resulting definition and theorem are printed.  In
 general, the value is a print specifier @(see print-specifier) that controls
 the output.</p>

 </blockquote>

 <p>
 @(':show-only') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Determines whether the events generated by the macro should be
 submitted (the default) or only shown on the screen.  Note that if
 @(':show-only') is @('t'), then @(':print') is ignored.</p>

 <ul>

   <li>
   @('nil'), to submit the events (the default).
   </li>

   <li>
   @('t'), to only show the events.
   </li>

 </ul>

 </blockquote>

 <p>
 @(':rewrite')
 </p>
 <blockquote>

 <p>Specify the @(':rewrite') option for the generated @('defun-sk') form.</p>

 <p>By default, the @(':rewrite') field of the generated @('defun-sk') form (or
 @('defun-sk2') form) corresponds to that of the corresponding form for the
 input function symbol.  (Exception: currently, custom @(':rewrite') fields are
 dropped.  A comment about a proposed @('simplify-defthm') in source file
 @('simplify-defun-sk.lisp') discusses this issue.)  If the @(':rewrite')
 option is supplied, then its value is used for the @(':rewrite') field of the
 generated @('defun-sk') (or @('defun-sk2')) form.</p>

 </blockquote>

 <p>
 @(':simplify-body') &mdash; default @('t')
 </p>
 <blockquote>

 <p>If this keyword has value @('t'), which is the default, then the body of
 the input function symbol's definition is simplified (more precisely: the
 <i>matrix</i> of the body, which occurs after the quantifier).  If this
 keyword has value @('nil'), then no simplification is attempted.  Otherwise,
 the value of this keyword is a pattern.  See @(see simplify-defun),
 specifically the documentation there for keyword argument @(':simplify-body'),
 for a discussion of patterns and how they are matched.</p>

 </blockquote>

 <p>
 @(':skolem-name') &mdash; default @('nil')<br/>
 @(':thm-enable') &mdash; default @('t')<br/>
 @(':thm-name') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Control the Skolem function for the generated @('defun-sk') form, as well
 as the enabled status and name for the generated theorem.</p>

 <p>If @(':thm-enable') has value @('nil'), then the generated theorem that
 equates the old and new function symbols will be disabled; else it will be
 enabled (the default).  In either case, the name of the theorem will be the
 value of @(':thm-name'); if that keyword argument is missing or is @(':auto')
 or @('nil'), then the name of the theorem will be @('FN-becomes-NEW').  When
 @(':skolem-name') is supplied, it becomes the @(':skolem-name') of the
 generated @('defun-sk') form.</p>

 </blockquote>

 <p>
 @(':theory') &mdash; default @(':none')
 </p>
 <blockquote>

 <p>Specify the theory under which simplification is performed.</p>

 <p>If @(':theory EXPR') is supplied, then simplification will be performed in
 the theory given by @('EXPR'), that is, as though the event @('(in-theory
 EXPR)') were first evaluated.  If either the @(':disable') or @(':enable')
 keyword is supplied, then it is illegal to supply @(':theory').  Note that
 some disabling may be useful if it is desired to preserve certain operators
 with special behavior such as @(tsee prog2$), @(tsee ec-call), and @(tsee
 time$); see @(see acl2::return-last-blockers).</p>

 </blockquote>

 <p>
 @(':untranslate') &mdash; default @(':nice')
 </p>
 <blockquote>

 <p>Specify how to create a user-level term from the simplified body.</p>

 <p>See @(see untranslate-specifier).</p>

 </blockquote>

 <p>
 @(':verify-guards') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Specify whether to verify guards for the new function.</p>

 <p>By default, guard verification is performed for the new function symbol if
 and only if the input function symbol is guard-verified.  This default
 behavior is overridden by a Boolean value @('V') of @(':verify-guards'): guard
 verification is done if @('V') is @('t'), else is not done.</p>

 <p>When guard verification is performed, it is attempted after several other
 events are admitted, including the new definition and the @('OLD-becomes-NEW')
 theorem (see above), by calling @(tsee verify-guards) on the new function
 symbol.  The @(':guard-hints') are utilized, if supplied (and not @(':auto')).
 Otherwise, a @(':guard-hints') value is generated that specifies the theory
 used for simplification (see the discussion of @(':theory')) augmented by the
 @('OLD-becomes-NEW') theorem (see above); also, if the old function symbol is
 guard-verified, the hints apply its guard theorem with a @(':use') hint.  This
 generated @(':guard-hints') value can cause  up to three different proof
 attempts, each somewhat different from the others, when necessary.  (For
 details use @(':show-only t').)</p>

 </blockquote>

 <h3>Generated Definition and Theorem</h3>

 <p>The generated definition has the same formals as the definition of @('FN'),
 and has the form</p>

 @({
 (defun-sk NEW (...)
   (declare ...)
   NEW-BODY)
 })

 <p>where @('NEW-BODY') is the result of simplifying the body of @('FN') (more
 precisely, the matrix of that quantified formula) unless keyword option
 @(':simplify-body') has value @('nil').  See above for how that option
 controls simplification of the body, measure, and guard.  However, if @('FN')
 was defined using the @(see soft::SOFT) tool @('defun-sk2'), then the
 definition of @('NEW') is also made with @('defun-sk2').</p>

 <p>The generated theorem generally has the form</p>

 @({
 (defthm FN-becomes-NEW
   (implies (and A1 A2 ... An)
            (equal (FN ...) (NEW ...))))
 })

 <p>where the calls of @('FN') and @('NEW') are on the formals of @('FN').
 However, if keyword argument @(':assumptions') specifies assumptions @('A1'),
 ... @('An'), then the generated theorem has the following form.</p>

 @({
 (defthm FN-becomes-NEW
   (iff (FN ...) (NEW ...)))
 })

 <p>In both cases, the name of the new theorem shown is the default but may be
 specified with keyword option @(':thm-name').</p>
 ")

(defxdoc simplify-defun-sk-examples
  :parents (simplify-defun-sk)
  :short "Examples illustrating @(tsee simplify-defun-sk)."
  :long "
 <p>The examples below are deliberately quite trivial, in order to make clear
 how @('simplify-defun-sk') behaves with various keyword arguments.  For all
 those examples, we assume that the following event has already been
 evaluated.</p>

 @({
 (defthm member-equal-fix-true-list
   (iff (member-equal a (fix-true-list lst))
        (member-equal a lst)))
 })

 <h3>Example Set 1: Basics</h3>

 <p>We start with the following basic example.  The keywords can all be omitted
 with minimal change to the outcome, but we include them as a way to introduce
 some of the simplest keywords.</p>

 @({
 (defun-sk foo (lst)
   (exists x (member-equal x (fix-true-list lst))))
 ; redundant (see above)
 (defthm member-equal-fix-true-list
   (iff (member-equal a (fix-true-list lst))
        (member-equal a lst)))
 (simplify-defun-sk foo
                    :new-name foo-simp
                    :thm-name foo-simplified
                    :function-disabled nil
                    :thm-enable t
                    :skolem-name foo-simp-sk)
 })

 <p>ACL2 responds to the call above of @('simplify-defun-sk') by creating the
 following @('DEFUN-SK') form among others, silently submitting the created
 forms, and then returning the new @('DEFUN-SK') form (as the value component
 of an @(see acl2::error-triple)).  The new function is named @('foo-simp')
 because that is what we specified with the @(':new-name') argument above.
 Similarly, the @(':skolem-name') below comes directly from the keyword above
 and otherwise would be omitted below.  Notice that the rewrite rule
 @('member-fix-true-listp'), displayed above, was applied to create the new
 definition.</p>

 @({
 (DEFUN-SK FOO-SIMP (LST)
           (EXISTS (X) (MEMBER-EQUAL X LST))
           :QUANT-OK T
           :SKOLEM-NAME FOO-SIMP-SK)
 })

 <p>You can add @(':verbose t'), to get output from the prover when evaluating
 the @(see acl2::events) generated by the @('simplify-defun-sk') call.</p>

 <p>To see the full expansion produced by the call of @('simplify-defun-sk')
 above, we can use @('show-simplify-defun-sk') instead of
 @('simplify-defun-sk'), on the same arguments (or, simply add keyword argument
 @(':show-only t') to your @('simplify-defun-sk') call).  The result is as
 follows (elided somewhat).</p>

 @({
  (ENCAPSULATE
       NIL
       ... ; helpful stuff local to the encapsulate
       (DEFUN-SK FOO-SIMP ...)  ; as shown above
       ... ; local helper events, not shown here
       (DEFTHM FOO-SIMPLIFIED ; the value of keyword argument :thm-name
               (IFF (FOO LST) (FOO-SIMP LST))
               :HINTS ...)
       (IN-THEORY (DISABLE FOO-SIMP)))
 })

 <p>Notice that new function symbol @('FOO-SIMP') and new theorem
 @('FOO-SIMPLIFIED') are disabled and enabled, respectively, because of keyword
 arguments supplied @(':function-disabled t') and @(':thm-enable t'),
 respectively.</p>

 <p>On the other hand, if you want less output, not more, use
 @('simplify-defun-sk') with @(':print nil').  For example:</p>

 @({
 ACL2 !>(simplify-defun-sk foo
                           :new-name foo-simp
                           :thm-name foo-simplified
                           :function-disabled t
                           :thm-enable t
                           :skolem-name foo-simp-sk
                           :print nil)
  T
 ACL2 !>:pe foo-simp
    d       4:x(SIMPLIFY-DEFUN-SK FOO
                                  :NEW-NAME ...)
               \
 >L d           (DEFUN FOO-SIMP (LST)
                       (DECLARE (XARGS :NON-EXECUTABLE T :MODE :LOGIC))
                       (PROG2$ (THROW-NONEXEC-ERROR 'FOO-SIMP
                                                    (LIST LST))
                               (LET ((X (FOO-SIMP-SK LST)))
                                    (MEMBER-EQUAL X LST))))
 ACL2 !>
 })

 <h3>Example Set 2: Assumptions</h3>

 <p>The following trivial example illustrates the use of assumptions.</p>

 @({
 (defthm fix-true-list-is-identity
   (implies (true-listp x)
            (equal (fix-true-list x)
                   x)))
 (defun-sk foo (lst1 lst2)
   (forall x (equal (member-equal x (fix-true-list lst1))
                    (member-equal x (fix-true-list lst2)))))
 (simplify-defun-sk foo :assumptions ((and (true-listp lst1)
                                           (true-listp lst2))))
 })

 <p>Here is the result.  Notice that since we did not specify
 @(':new-name'), the generated function name is obtained by adding a
 suffix @('\"$1\"') to the given function symbol's name.  In general, the least
 natural number @('n') will be used that results in a new function symbol when
 adding the suffix @('\"$n\"').</p>

 @({
 (DEFUN-SK FOO$1 (LST1 LST2)
           (FORALL (X)
                   (EQUAL (MEMBER-EQUAL X LST1)
                          (MEMBER-EQUAL X LST2)))
           :QUANT-OK T)
 })

 <p>Notice that the body was simplified under the given assumption that
 @('lst1') and @('lst2') satisfy @(tsee true-listp); without any such
 assumption, no simplification would have taken place.</p>

 <p>The following example has a non-trivial @(see guard), and illustrates that
 the value of keyword @(':assumptions') can be @(':guard'), which means that
 the @(':assumptions') value is taken to be the given function's guard.</p>

 @({
 (defun-sk foo (lst1 lst2)
  (declare (xargs :guard (and (true-listp lst1)
                              (true-listp lst2))
                  :verify-guards nil))
   (forall x (equal (member-equal x (fix-true-list lst1))
                    (member-equal x (fix-true-list lst2)))))
 (simplify-defun-sk foo :assumptions :guard)
 })

 <p>Here is the result.  Notice that the simplified body is the same as
 before.</p>

 @({
 (DEFUN-SK FOO$1 (LST1 LST2)
           (DECLARE (XARGS :NON-EXECUTABLE NIL))
                          (DECLARE (XARGS :GUARD (AND (TRUE-LISTP LST1)
                                                      (TRUE-LISTP LST2))
                                          :VERIFY-GUARDS NIL))
           (FORALL (X)
                   (EQUAL (MEMBER-EQUAL X LST1)
                          (MEMBER-EQUAL X LST2)))
           :QUANT-OK T)
 })

 <p>Unlike @(tsee simplify-defun), @('simplify-defun-sk') does not support
 keywords @(':assumption-disable'), @(':assumption-enable'), and
 @(':assumption-theory'), and @(':hyp-fn'), since there is no need, as @(tsee
 defun-sk) does not support recursion.</p>

 <h3>Example Set 3: Guard Verification</h3>

 <p>Consider the preceding example, but where we verify guards before
 attempting simplification, as follows.</p>

 @({
 (verify-guards foo)
 (simplify-defun-sk foo :assumptions :guard)
 })

 <p>The new @(tsee defun-sk) form is the same as before.  However, this time
 the new function symbol is guard-verified.  If we use
 @('show-simplify-defun-sk') in place of @('simplify-defun-sk') just above, we
 can see that the following @(tsee verify-guards) event is generated for the
 new function symbol.</p>

 @({
   (VERIFY-GUARDS FOO$1
                  :HINTS ((\"Goal\" :USE (:GUARD-THEOREM FOO))))
 })

 <p>This illustrates that by default, guard verification will be attempted for
 the new function symbol exactly when the original function symbol is
 guard-verified.  However, that default behavior can be overridden by using the
 @(':verify-guards') keyword.  For example, suppose that the preceding call of
 @('simplify-defun-sk') displayed above is replaced by the following.</p>

 @({
 (simplify-defun-sk foo
                    :assumptions :guard
                    :verify-guards nil)
 })

 <p>In this case, guard verification will not be attempted for the new function
 symbol.</p>

 <p>@('Simplify-defun-sk') provides the keyword @(':guard-hints') for the
 simplified function's guard verification proofs.  For example, suppose that
 instead of the @('simplify-defun-sk') forms above we evaluate this (rather
 silly) form.</p>

 @({
 (simplify-defun-sk foo
                    :assumptions :guard
                    :guard-hints ((\"Goal\" :in-theory (enable append))))
 })

 <p>Then in place of the default @(':hints') supplied to the call of @(tsee
 verify-guards), as displayed above, the guard hints supplied in our
 @('simplify-defun-sk') are used.</p>

 @({
     (VERIFY-GUARDS FOO$1
                    :HINTS ((\"Goal\" :IN-THEORY (ENABLE APPEND))))
 })

 <h3>Example Set 4: @('Defun-sk') specific: @('defun-sk2') and
 @(':rewrite')</h3>

 <p>Next, we discuss two features of @('simplify-defun-sk') that do not
 correspond to features of @(tsee simplify-defun).</p>

 <p>The macro @('defun-sk2') is part of the SOFT tool suite (see @(see
 soft::SOFT)).  It is a wrapper for @('defun-sk').  When @('simplify-defun-sk')
 is called on a function that was introduced with @('defun-sk2'), the new
 function is also introduced with @('defun-sk2').  Here is an example.</p>

 @({
 (include-book \"simplify-defun-sk\")
 (include-book \"kestrel/soft/top\" :dir :system)
 (defunvar ?foo (*) => *)
 (defun-sk2 spec[?foo] (?foo) ()
   (forall (x) (equal (?foo x) (* x 2))))
 (simplify-defun-sk spec[?foo])
 })

 <p>The resulting definition benefits from simplification of @('(* x 2)') to
 @('(* 2 x)').  More interesting: it too is a call of @('defun-sk2').</p>

 @({
 (DEFUN-SK2 SPEC[?FOO]$1 (?FOO)
            NIL
            (FORALL (X) (EQUAL (?FOO X) (* 2 X)))
            :QUANT-OK T)
 })

 <p>A second capability offered by @('simplify-defun-sk') is the @(':rewrite')
 keyword.  By default, the @(':rewrite') field of the generated @('defun-sk')
 form (or @('defun-sk2') form) corresponds to that of the corresponding form
 for the input function symbol.  (Exception: currently, custom @(':rewrite')
 fields are dropped.  A comment about a proposed @('simplify-defthm') in source
 file @('simplify-defun-sk.lisp') discusses this issue.)  Here is an example
 showing a new @(':rewrite') field, based closedly on the first example in this
 topic.</p>

 @({
 ; Start a fresh ACL2 session.
 (include-book \"simplify-defun-sk\")
 (defthm member-equal-fix-true-list
   (iff (member-equal a (fix-true-list lst))
        (member-equal a lst)))
 (defun-sk foo (lst)
   (forall x (not (member-equal x (fix-true-list lst)))))
 (simplify-defun-sk foo :rewrite :direct)
 })

 <p>As a result of the @(':rewrite') argument above, the resulting
 @('defun-sk') form includes @(':rewrite :direct').</p>

 @({
 (DEFUN-SK FOO$1 (LST)
           (FORALL (X) (NOT (MEMBER-EQUAL X LST)))
           :QUANT-OK T
           :REWRITE :DIRECT)
 })

 <p>As for @('defun-sk'), the value of the @(':rewrite') option of
 @('simplify-defun-sk') can ony be @(':direct') if the quantifier is @(tsee
 forall).</p>

 <h3>Example Set 5: Controlling the Theory for Simplification</h3>

 <p>By default, simplification done on behalf of @('simplify-defun-sk') is
 carried out in the current theory (see @(see current-theory)).  However, the
 @(':theory') keyword allows control over that theory without changing the
 current theory globally.  Let us return to our original example, without extra
 keywords this time; but this time, let's introduce the key lemma with @(tsee defthmd)
 (not because it helps our proofs to disable it, but because that will help us
 to illustrate the @(':theory') keyword).</p>

 @({
 ; Start a fresh ACL2 session.
 (include-book \"simplify-defun-sk\")
 (defthmd member-equal-fix-true-list
   (iff (member-equal a (fix-true-list lst))
        (member-equal a lst)))
 (defun-sk foo (lst)
   (exists x (member-equal x (fix-true-list lst))))
 (simplify-defun-sk foo :theory (enable member-equal-fix-true-list))
 })

 <p>If we omit the @(':theory') value above, the call of @('simplify-defun-sk')
 fails because @('member-equal-fix-true-list') is @(see disable)d.  The
 @(':theory') keyword value causes simplification (and some subsequent
 reasoning) to be done in the indicated theory.</p>

 <p>For convenience, @(':enable') and/or @(':disable') keywords are available,
 provided that they are not used when @(':theory') is used.  For example, the
 following form is treated equivaletly to the @('simplify-defun-sk') call
 displayed just above.</p>

 @({
 (simplify-defun-sk foo :enable (member-equal-fix-true-list))
 })

 <h3>Example Set 6: Simplifying Subterms</h3>

 <p>Like @(tsee simplify-defun), value of the @(':simplify-body') keyword of
 @('simplify-defun-sk') can be @('t'), @('nil'), or a pattern.  It may be
 surprising that @('nil') is allowed, since (unlike @('simplify-defun')) the
 body is the only piece of the definition that is simplified (not the guard or
 measure).  However, it is anticipated that sometimes @('simplify-defun-sk')
 may be called without knowing if simplification will succeed, but nevertheless
 wanting a new function symbol to be defined.  (If that same functionality is
 desired for @('simplify-defun') then it could be changed as well.)</p>

 <p>The handling of patterns is the same as for @('simplify-defun'); see @(see
 simplify-defun) for further discussion of ``Simplifying a Subterm''.  Here we
 present a simple example with a single subterm simplified, but as with
 @('simplify-defun'), it is legal to specify more than one such subterm.</p>

 @({
 ; Start a fresh ACL2 session.
 (include-book \"simplify-defun-sk\")
 ; Books included above define set-equiv as an equivalence relation,
 ; and provide some nice congruence rules.
 (defthm set-equiv-fix-true-list
   (set-equiv (fix-true-list lst)
              lst))
 (defun-sk foo (lst1 lst2)
   (exists x (iff (and (member-equal x (fix-true-list lst1))
                       (member-equal x (fix-true-list lst2)))
                  t)))
 (simplify-defun-sk foo
                    :simplify-body
                    (and (member-equal x @)
                         (member-equal x (fix-true-list lst2))))
 })

 <p>The result is below.  Notice that simplification has taken place at the
 subterm labeled with @('@'), and nowhere else.</p>

 @({
 (DEFUN-SK FOO$1 (LST1 LST2)
           (EXISTS (X)
                   (IFF (AND (MEMBER-EQUAL X LST1)
                             (MEMBER-EQUAL X (FIX-TRUE-LIST LST2)))
                        T))
           :QUANT-OK T)
 })

 <p>It is interesting to note that our original lemma,
 @('member-equal-fix-true-list'), is not sufficient for the simplification.
 That is because it is a rule to rewrite calls of @('member-equal'), but the
 subterm in question has no such calls.</p>

 @({
 ; Start a fresh ACL2 session.
 (include-book \"simplify-defun-sk\")
 (defthm member-equal-fix-true-list
   (iff (member-equal a (fix-true-list lst))
        (member-equal a lst)))
 (defun-sk foo (lst1 lst2)
   (exists x (and (member-equal x (fix-true-list lst1))
                  (member-equal x (fix-true-list lst2)))))
 (simplify-defun-sk foo
                    :simplify-body
                    (and (member-equal x @)
                         (member-equal x (fix-true-list lst2))))
 })

")

(defxdoc simplify-defun-sk-programmatic
  :parents (apt)
  :short "Programmatic interface to @(tsee simplify-defun-sk)"
  :long "<p>Call @('simplify-defun-sk-programmatic') exactly as you would call
 @(tsee simplify-defun-sk), except that arguments are not automatically quoted;
 so avoid using arguments of the form @('(:eval x)').  Unlike
 @('simplify-defun-sk'), @('simplify-defun-sk-programmatic') does not introduce
 a new definition or theorem.  Rather, it returns the @('encapsulate') form
 that would be evaluated by @('simplify-defun-sk') &mdash; that is, the form
 displayed by a corresponding call of @(tsee show-simplify-defun-sk).</p>")

(acl2::defpointer show-simplify-defun-sk simplify-defun-sk)
