; Simplify-term Transformation -- Documentation
;
; Copyright (C) 2018, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file documents the simplify-term data transformation,
; which is used for simplifying a term.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc simplify-term
  :parents (apt)
  :short "Simplify a term."
  :long "
 <h3>Introduction</h3>

 <p>This macro is an interface to the @(tsee simplify) transformation that,
 when successful, creates a new term by simplifying the given input term.  The
 input should not be a symbol, and it need not be translated (see @(see
 acl2::term)).</p>

 <p>See @(see simplify-term-examples) for examples that illustrate the use of
 @('simplify-term').</p>

 <p>Evaluation of the form @('(simplify-term OLD)') will attempt to create a
 new term, say, @('NEW'), that is logically equivalent to the input term
 @('OLD') but is simpler.  In the rest of this documentation page, @('OLD')
 will denote the input term and @('NEW') will generally denote the new,
 simplified term.</p>

 <p>Also see @(see simplify) for an analogous utilities for simplifying
 definitions.</p>

 <p>A @('simplify-term') call causes an error if no simplification takes place
 or if the proof obligations fail to be met.  The implementation has been
 carefully orchestrated so that the proof obligations will generally succeed.
 When this is not the case, you may invoke @('show-simplify-term') with the
 same arguments in order to obtain the form that failed to be admitted, so that
 you can modify it manually.  Or equivalently, simply use keyword argument
 @(':show-only t') in your @('simplify-term') call.</p>

 <h3>General Form</h3>

 <p>The following form shows all the keyword arguments in alphabetical order,
 together with their default values (i.e., when the keyword is omitted).  No
 argument is evaluated, except that if an argument is of the form @('(:eval
 x)'), then the actual argument is the result of evaluting of @('x').  Note
 that @('simplify-term') may be replaced by @(tsee simplify) to obtain an
 essentially equivalent call.</p>

 @({
 (simplify-term old
                &key
                :assumptions       ; default nil
                :disable           ; default :none
                :enable            ; default :none
                :equiv             ; default nil
                :expand            ; default nil
                :must-simplify     ; default t
                :print             ; default :result
                :rule-classes      ; default :rewrite
                :show-only         ; default nil
                :simplify-body     ; default t
                :theory            ; default :none
                :thm-enable        ; default t
                :thm-name          ; default :auto
                :untranslate       ; default :nice
                )
 })

 <h3>Inputs</h3>

 <p>
 @('OLD')
 </p>
 <blockquote>

 <p>Denotes the term to transform, which need not be translated (see @(see
 acl2::term)).</p>

 <p>Evaluation of @('(simplify-term OLD ...)') assumes that the input term
 contains only calls of @(':')@(tsee logic) mode function symbols, that is, not
 calls of @(':')@(tsee program) mode function symbols.  Successful evaluation
 produces a new term, @('NEW'), and a theorem equating @('OLD') with @('NEW').
 Details may be controlled by keyword parameters as described below.</p>

 </blockquote>

 <p>
 @(':assumptions') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Determines the assumptions for simplification.</p>

 <p>The value of @(':assumptions') must be a list of terms (not necessarily
 translated; see @(see acl2::term)) that only reference variables that occur
 in @('OLD').</p>

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
 @(':equiv') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Determine the equivalence relation to preserve when simplifying.</p>

 <p>By specifying @(':equiv EQV') @('simplify-term') attempts to simplify the
 input term to one that is equivalent, in the sense of the equivalence
 relation, @('EQV').  If @(':equiv') is @('nil') or not specified, then the
 equivalence relation used is @('EQUAL').  For example, the successful
 application of @('simplify-term') with argument @(':equiv iff') will result in
 a body that is Boolean-equivalent to the original body.</p>

 </blockquote>

 <p>
 @(':expand') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Give an @(':')@(tsee acl2::expand) hint to the simplifier.</p>

 <p>When @(':expand E') is supplied, simplification will take place as though
 the hint @(':expand E') is given to the top-level goal in the theorem
 prover.</p>

 </blockquote>

 <p>
 @(':must-simplify') &mdash; default @('t')
 </p>
 <blockquote>

 <p>This keyword specifies whether the simplified term must be different from
 the input term: yes, if the value is @('t') (the default), and no if the
 value is @('nil').  However, this keyword is ignored if the keyword
 @(':simplify-body') has value @('nil').</p>

 </blockquote>

 <p>
 @(':print') &mdash; default @(':result')
 </p>
 <blockquote>

 <p>Specify what to print.</p>

 <p>By default, only the resulting theorem is printed.  In general, the value
 is a print specifier @(see print-specifier) that controls the output.</p>

 </blockquote>

 <p>
 @(':rule-classes') &mdash; default @(':rewrite')
 </p>
 <blockquote>

 <p>By default, or if @(':rewrite') is specified for @(':rule-classes'), the
 @(tsee defthm) or @(tsee defthmd) event created by @('simplify-term') will be
 generated without a @(':rule-classes') argument, hence stored as a rewrite
 rule (see @(see acl2::rule-classes)).  Otherwise, the value specified for the
 @(':rule-classes') argument of the @('simplify-term') call will be provided as
 the @(':rule-classes') argument of the generated event.</p>

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
 @(':simplify-body') &mdash; default @('t')
 </p>
 <blockquote>

 <p>If this keyword has value @('t'), which is the default, then the input term
 is simplified.  If this keyword has value @('nil'), then no simplification is
 attempted.  Otherwise, the value of this keyword is a pattern.  See @(see
 simplify-defun), specifically the documentation there for keyword argument
 @(':simplify-body'), for a discussion of patterns and how they are
 matched.</p>

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
 @(':thm-enable') &mdash; default @('t')<br/>
 @(':thm-name') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Determines the name and enabled status of the new theorem.</p>

 <p>If @(':thm-enable') has value @('nil'), then the generated theorem that
 equates the input term, @('OLD') with the new term, @('NEW'), will be a call
 of @('defthmd').  Otherwise, @('defthm') will be used.  In either case: if
 @(':thm-name') is missing or is @(':auto') or @('nil'), then the name of the
 theorem will be @('OLD-becomes-NEW'); otherwise, the name of the theorem will
 be the value of @(':thm-name').</p>

 </blockquote>

 <p>
 @(':untranslate') &mdash; default @(':nice')
 </p>
 <blockquote>

 <p>Specify how to create a user-level term from the simplified term.</p>

 <p>See @(see untranslate-specifier).</p>

 </blockquote>

 <h3>Generated Theorem</h3>

 <p>The generated theorem generally has the form</p>

 @({
 (defthm OLD-becomes-NEW
   (equal OLD NEW))
 })

 <p>where @('equal') will be replaced by an equivalence relation if specified
 by keyword argument @(':equiv').  However, if keyword argument
 @(':assumptions') specifies assumptions @('A1'), ... @('An'), then the
 generated theorem has the following form (with @('equal') possibly replaced by
 an equivalence relation as explained above).</p>

 @({
 (defthm OLD-becomes-NEW
   (implies (and A1 A2 ... An)
            (equal OLD NEW)))
 })

 <p>In both cases, the name of the new theorem shown is the default but may be
 specified with keyword option @(':thm-name').</p>
 ")

(defxdoc simplify-term-examples
  :parents (simplify-term)
  :short "Examples illustrating @(tsee simplify-term)."
  :long "
 <p>The examples below are deliberately quite trivial, in order to show
 how @(tsee simplify-term) behaves with some keyword arguments.  For all
 those examples, we assume that the following event has already been
 evaluated.</p>

 @({
 (defun f (x) (+ 3 -3 (car x)))
 })

 <p>The results in the log below are intended to follow clearly from the
 keyword arguments supplied in the respective invocations of
 @('simplify-term'), which we invoke here with @(tsee simplify).</p>

 @({
 ACL2 !>(simplify (f (cons y z))
                  :disable (car-cons)
                  :thm-enable nil)
 (DEFTHMD SIMPLIFY-TERM-THM
          (EQUAL (F (CONS Y Z))
                 (IF (ACL2-NUMBERP (CAR (CONS Y Z)))
                     (CAR (CONS Y Z))
                     0)))
 ACL2 !>(simplify (f (cons y z))
                  :thm-name f1
                  :assumptions ((natp y)))
 (DEFTHM F1 (IMPLIES (NATP Y) (EQUAL (F (CONS Y Z)) Y)))
 ACL2 !>(simplify (f (cons (+ 7 y) z))
                  :thm-name f2
                  :untranslate nil)
 (DEFTHM F2 (EQUAL (F (CONS (+ 7 Y) Z)) (BINARY-+ '7 Y)))
 ACL2 !>
 })")

(defxdoc simplify-term-programmatic
  :parents (apt)
  :short "Programmatic interface to @(tsee simplify-term)"
  :long "<p>Call @('simplify-term-programmatic') exactly as you would call
 @(tsee simplify-term), except that arguments are not automatically quoted; so
 avoid using arguments of the form @('(:eval x)').  Unlike @('simplify-term'),
 @('simplify-defun-sk-programmatic') does not introduce a new definition or
 theorem.  Rather, it returns the @('encapsulate') form that would be evaluated
 by @('simplify-term') &mdash; that is, the form displayed by a corresponding
 call of @(tsee show-simplify-term).</p>")

(acl2::defpointer show-simplify-term simplify-term)
