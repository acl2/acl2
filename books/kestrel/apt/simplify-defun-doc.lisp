; Simplify-defun Transformation -- Documentation
;
; Copyright (C) 2016, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file documents the simplify-defun data transformation,
; which is used for simplifying a definition.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TO DO: Add reference to transform-and-propagate below.
(defxdoc simplify-defun
  :parents (apt)
  :short "Simplify the definition of a given function."
  :long "<p>This macro is an interface to the @(tsee simplify) transformation
 for function symbols that the user (or a tool) introduces with @(tsee defun).
 When successful, it creates a new @('defun') form by simplifying the body of
 the definition of such a function symbol.</p>

 <h3>Introduction</h3>

 <p>See @(see simplify-defun-examples) for an introductory tutorial for
 @('simplify-defun'), which presents an extensive series of examples.</p>

 <p>Evaluation of the form @('(simplify-defun FN)') will attempt to define a
 new function, say, @('FN$1'), that is logically equivalent to the definition
 of @('FN') but is simpler.  In the rest of this documentation page,
 @('FN') will denote the input function symbol and @('NEW') will generally
 denote the new function symbol.</p>

 <p>Note that @('simplify-defun') transforms definitions made using @(tsee
 defun) or macros such as @(tsee defund) that expand to calls of @('defun'), or
 the application of @(tsee mutual-recursion) to such forms.  See @(see
 simplify-defun-sk) for an analogous utility for which the input function
 symbol was originally defined with @(tsee defun-sk) rather than @('defun').
 Also see @(see simplify-defun+) for a variant of @('simplify-defun'), and see
 @('transform-and-propagate') for a utility that can apply
 @('simplify-defun') to several function symbols after applying an indicated
 transformation.</p>

 <p>A @('simplify-defun') call causes an error if the proof obligations fail to
 be met or, by default, if no simplification takes place.  The implementation
 has been carefully orchestrated so that the proof obligations will generally
 succeed.  When this is not the case, you may invoke @('show-simplify-defun')
 with the same arguments in order to obtain the form that failed to be
 admitted, so that you can modify it manually.  Or equivalently, simply add
 keyword argument @(':show-only t') in your @('simplify-defun') call.</p>

 <h3>General Form</h3>

 <p>The following form shows all the keyword arguments in alphabetical order,
 together with their default values (i.e., when the keyword is omitted).  No
 argument is evaluated, except that if an argument is of the form @('(:eval
 x)'), then the actual argument is the result of evaluating @('x').  Note that
 @('FN') should be a function symbol previously defined with @(tsee defun);
 thus, @('simplify-defun') may be replaced by @(tsee simplify) to obtain an
 essentially equivalent call.</p>

 @({
 (simplify-defun FN
                 &key
                 :assumptions        ; default nil
                 :disable            ; default :none
                 :enable             ; default :none
                 :equiv              ; default nil
                 :expand             ; default nil
                 :hints              ; default nil
                 :new-enable         ; default :auto
                 :new-name           ; default :auto
                 :guard-hints        ; default :auto
                 :hyp-fn             ; default nil
                 :measure            ; default :auto
                 :measure-hints      ; default :auto
                 :must-simplify      ; default (:body t :measure nil :guard nil)
                 :non-executable     ; default :auto
                 :print              ; default :result
                 :show-only          ; default nil
                 :simplify-body      ; default t
                 :simplify-guard     ; default nil
                 :simplify-measure   ; default nil
                 :thm-enable         ; default t
                 :thm-name           ; default :auto
                 :theory             ; default :none
                 :untranslate        ; default :nice
                 :verify-guards      ; default :auto
                 )
 })

 <h3>Inputs</h3>

 <p><b>Special Note on keyword arguments in the case of @(tsee
 mutual-recursion).</b> If @('FN') was defined with @('mutual-recursion'), then
 normally all keyword arguments are applied to the simplification of all
 definitions that were introduced in that same @('mutual-recursion') event.
 However, every keyword argument except @(':non-executable'), @(':print'),
 @(':verify-guards'), and @(':show-only') can direct different values to be
 applied to different definitions, by supplying a keyword argument of the form
 @('(:map (fn1 val1) ... (fnk valk))'), where @('(fn1 ... fnk)') is the
 <i>clique</i> introduced by that @('mutual-recursion').  To get that clique,
 evaluate the form @('(get-clique 'FN (w state))').  Every member of the clique
 must be specified, but in any order.  Moreover, entries can be combined in a
 way inspired by @(tsee case): the key may be a list of functions, i.e.,
 @('(:map ... ((f g ... h) val) ... )') which is equivalent to @('(:map ... (f
 val) (g val) ... (h val) ... )'); and an optional final entry of the form
 @('(:otherwise val)') specifies that all remaining clique members should be
 assigned @('val').  End of Special Note.</p>

 <p>
 @('FN')
 </p>
 <blockquote>

 <p>Denotes the target function to transform.</p>

 <p>Evaluation of @('(simplify-defun FN ...)') assumes that the input symbol,
 @('FN'), is a @(':')@(tsee logic) mode function symbol, defined with @(tsee
 defun) or with a macro expanding to a call of @('defun') (such as @(tsee
 defund)).  Successful evaluation admits a new @('defun'), with the same
 formals as @('FN'), and a theorem equating @('FN') with the newly-defined
 function symbol, @('NEW').  Details, such as whether or not to perform guard
 verification, may be controlled by keyword parameters as described below.</p>

 </blockquote>

 <p>
 @(':assumptions') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Determines the assumptions for simplification.</p>

 <p>The value of @(':assumptions') must be a list of terms (not necessarily
 translated; see @(see acl2::term)) that only reference variables among the
 formal parameters of @('FN').</p>

 <p>When @(':assumptions H') is supplied, all simplification will be performed
 assuming the conjunction of @('H''), where @('H'') is the result of
 simplifying each term in the list @('H').  For another way to specify
 assumptions, see the discussion of @(':hyp-fn'), below.</p>

 <p>If @('FN') is defined recursively and @(':assumptions') is specified, there
 will generally be a formula, called an ``applicability condition,'' that must
 be a theorem in order for the transformation to succeed.  Any transformation
 might have applicability conditions, each of which has a label; in the case of
 @('simplify-defun'), the sole label is @(':assumptions-preserved').  This
 particular condition is that the assumptions must be preserved by recursive
 calls of the function.</p>

 </blockquote>

 <p>
 @(':disable') &mdash; default @(':none')<br/>
 @(':enable') &mdash; default @(':none')
 </p>
 <blockquote>

 <p>Determine the theory for simplification.</p>

 <p>If @(':disable D') and @(':enable E') are supplied, then simplification
 will be performed in the theory @('(e/d* E D')'), where @('D'') is the result
 of adding to @('D') the @(see acl2::rune)s that were introduced with the given
 function, @('FN').  The same holds if @(':disable') is omitted, in which case
 @('D') is treated as @('nil').  Similarly, if only @(':disable') is supplied,
 then the theory will be @('(disable* D')').  If either of these keywords is
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

 <p>By specifying @(':equiv EQV') @('simplify-defun') attempts to simplify the
 body to one that is equivalent, in the sense of the equivalence relation,
 @('EQV').  If @(':equiv') is @('nil') or not specified, then the equivalence
 relation used is @('EQUAL').  For example, the successful application of
 @('simplify-defun') with argument @(':equiv iff') will result in a body that
 is Boolean-equivalent to the original body.</p>

 </blockquote>

 <p>
 @(':expand') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Give an @(':')@(tsee acl2::expand) hint to the simplifier.</p>

 <p>When @(':expand E') is supplied, simplification will take place as though
 the hint @(':expand E') is given to the top-level goal in the theorem prover.
 NOTE however that when @('simplify-defun') is applied to a function defined
 using recursion, any such directive to expand a call of that function will be
 ignored.</p>

 </blockquote>

 <p>
 @(':hints') &mdash; default @('nil')<br/>
 </p>
 <blockquote>

 <p>Specifies the @(see acl2::hints) for proving that assumptions are preserved
 by recursive calls.</p>

 <p>If @(':hints') is omitted or has value @('nil'), then the @(see
 acl2::definition), @(see acl2::executable-counterpart), and @(see
 acl2::type-prescription) @(see acl2::rune)s for the given function symbol will
 all be disabled.  If moreover that symbol is introduced with @(tsee
 mutual-recursion), then these runes will be disabled for all function symbols
 in its clique, i.e., all function symbols that were introduced with that
 symbol.</p>

 <p>If @(':hints') has a non-@('nil') value, then that value should be a legal
 hints-specifier for the single applicability condition,
 @(':assumptions-preserved'); see @(see hints-specifier).</p>

 <p>NOTE: If you supply @(':hints') with a value other than @('nil'), then you
 may find it helpful to specify that the runes mentioned above are all
 disabled: @('FN'), @('(:e FN)'), and @('(:t FN)') (see @(see acl2::rune)).  If
 you are simplifying a @(tsee mutual-recursion) form then you may find it
 helpful to disable these for every @('FN') in the clique of functions being
 introduced.</p>

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
 @(':hyp-fn') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Determines the assumptions for simplification.</p>

 <p>If the list of formals of the given function symbol, @('FN'), is @('(X1
 ... Xk)'), then specifying @(':hyp-fn h') for @('h') not @('nil') is
 equivalent to specifying @(':assumptions ((h X1 ... Xk))').  It is illegal to
 provide non-@('nil') values for both @(':hyp-fn') and @(':assumptions').</p>

 </blockquote>

 <p>
 @(':measure') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Provides the measure for the generated function.</p>

 <p>The default is @(':auto'), in which case: when there is a measure @('M_FN')
 associated with the input function symbol, @('FN') (because the definition of
 @('FN') is recursive), then @(':measure M_FN') is included in the @('xargs')
 of the new definition.  Otherwise @(':measure M') has been supplied for some
 @('M') that is not @(':auto'); then @(':measure M') is included in the
 @('xargs') of the new definition unless @('M') is @('nil').</p>

 </blockquote>

 <p>
 @(':measure-hints') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Provides the measure @(see acl2::hints) for the generated function.</p>

 <p>The @(':measure-hints') option is used as the @(tsee xargs) @(':hints')
 value in the generated definition.  A special value @(':auto'), which is the
 default, creates @(':hints') for the termination proof that use the input
 function symbol's @(see termination-theorem) as well as suitable theory
 modification if any of @(':disable'), @(':enable'), or @(':theory') have value
 other than their default of @(':none').</p>

 </blockquote>

 <p>
 @(':must-simplify') &mdash; default @('t')
 </p>
 <blockquote>

 <p>Determine where simplification must make a change.</p>

 <p>This keyword specifies whether each of the body, measure, and guard of the
 input definition is required to be simplified.  Its value is a @(tsee
 keyword-value-listp), except that @('t') represents the value @('(:body
 t :measure nil :guard nil)').  Thus each key is one of @(':body'),
 @(':measure'), or @(':guard'), and each value is @('t') or @('nil'), where
 @('nil') is the implicit value if the key is omitted.  So by default: the body
 must simplify to a result different from the original body, or an error
 occurs; but no such requirement is made for simplification of the measure or
 the guard.  Note that the respective value for keyword argument @(':body'),
 @(':measure'), or @(':guard') is ignored when, for the @(':must-simplify')
 keyword argument, the value of keyword @(':simplify-body'),
 @(':simplify-measure'), or @(':simplify-guard') is @('nil').  Note that the
 value @('nil') for @(':must-simplify') is equivalent to the value @('(:body
 nil :measure nil :guard nil)'), since the three keywords do not occur in the
 empty keyword-value-list.</p>

 <p><b>NOTE</b> for the case that option @(':simplify-body') specifies a
 pattern.  In that case, <i>every</i> subterm targeted for simplification by
 the pattern must simplify to a result different from the subterm.  When there
 are @('LET')-bindings above the subterm, the requirement is a bit more subtle:
 the simplification of the subterm under those bindings must differ from the
 result of substituting the bindings into the subterm.</p>

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
 @(':new-name') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Determines the name of the generated function.</p>

 <p>This value, if provided, becomes the function symbol of the generated
 definition.  Otherwise the generated function symbol is obtained by adding a
 suffix @('\"$n\"') to the input function symbol's name, for the least natural
 number @('n') that results in a new function symbol.  Note: the value @('nil')
 is treated the same as @(':auto'), and in the case that @('FN') was introduced
 with @(tsee mutual-recursion), only these two values and a value of the form
 @('(:map ...)') (as described above) are legal for @(':new-name').</p>

 </blockquote>

 <p>
 @(':non-executable') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Specify non-executability of the new function.</p>

 <p>When this keyword has value @('t'), the generated definition is a call of
 @(tsee defun-nx) or @(tsee defund-nx); if the value is @('nil'), then the
 generated definition is a call of @(tsee defun) or @(tsee defund).  The
 default is @(':auto'), which is equivalent to @('t') if the original
 definition is non-executable (defined with @('defun-nx') or @('defund-nx') or,
 more generally, with @(tsee xargs) keyword @(':non-executable t')), else
 @('nil').  This option is useful when simplification transforms the definition
 into one that violates syntactic rules for executability, such as taking the
 @('CAR') of a function call that returns multiple values.</p>

 <p>Note that the body of the generated definition may depend on the value of
 @(':non-executable').  Specifically, if the value is @('nil'), then the
 simplified body may be adjusted in an attempt to make it executable, for
 example by inserting a call of @(tsee mv-list) in a context where a single
 value is expected but multiple values are supplied.</p>

 </blockquote>

 <p>
 @(':print') &mdash; default @(':result')
 </p>
 <blockquote>

 <p>Specify what to print.</p>

 <p>By default, only the resulting definition and theorem are printed.  In
 general, the value is a print specifier @(see print-specifier) that
 controls the output.</p>

 </blockquote>

 <p>
 @(':show-only') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Determines whether the events generated by the macro should be
 submitted (the default) or only shown on the screen.  Note that if
 @(':show-only') is @('t'), then @(':print') is ignored.</p>

 <p>
 Note that if @(':show-only') is @('t'), then @(':print') is ignored.
 </p>

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

 <p>Specify whether to simplify the body and (optionally) if so, which
 subterms.</p>

 <p>This keyword indicates whether to simplify the body of the input function
 symbol.  Simplification is to be attempted when the value is not @('nil'), in
 which case it is an error if simplification leaves the body unchanged.</p>

 <p>Other than @('t') or @('nil'), the value can be a <i>pattern</i>, which
 must have at least one occurrence of a variable whose first character is an
 atsign (@('@')) or a call of the form @('(:@ term)'); these variables and
 calls are to be matched with subterms to be simplified, according to the
 following process.</p>

 <ol>

 <li>First, each variable reference @('var') whose first character is an
 atsign (@('@')) is replaced by a call @('(:@ _var)'), where @('_var') denotes
 the variable @('_') (in the ACL2 package) if the @(tsee symbol-name) of
 @('var') contains just the single atsign character, and otherwise @('_var')
 denotes the result of prefixing an underscore character to the
 @('symbol-name') of @('var'), without changing its @(tsee
 symbol-package-name).  Note that the result must have at least one call of
 @(':@'), but no nested such calls.  This replacement is done directly on the
 supplied pattern, using obvious heuristics to determine what is a variable
 reference; for example, @('@') is a variable reference in @('(foo @)') and
 @('(let ((x @)) _)') but not in @('(@ x)') or @('(let ((@ x)) _)').</li>

 <li>The resulting pattern is then replaced by its translation to an ACL2
 term (see @(see termp)), which involves macroexpansion and removal of
 abbreviations; for example, the pattern @('(+ (:@ _) 17)') is translated to
 @('(BINARY-+ (:@ _) '17)').  Note that for this purpose, @(':@') is treated as
 a unary function symbol.</li>

 <li>The resulting pattern @('P') gives rise to a new pattern @('P'') by
 expanding away calls of @(':@') as though it were the identity macro, that is,
 by replacing each call of the form @('(:@ u)') by @('u').  Then @('P'') is
 matched against the definition body @('B') in a left-to-right depth-first
 traversal to find the first subterm @('B'') of @('B') that is an instance of
 @('P'') in which only variables whose name starts with the underscore
 character (@('_')) are instantiated, in the following generous sense: for a
 variable whose @(tsee symbol-name) is exactly @('\"_\"') each occurrence is
 allowed to match a different term.  If no subterm @('B'') exists as described
 above, then an error occurs.</li>

 <li>The terms to be simplified are those subterms of @('B'') that correspond
 to subterms of @('P'') that were originally (that is, in @('P')) calls of
 @(':@').</li>

 <li>Each subterm is simplified with respect to the governing @('IF') tests (or
 negated tests, as appropriate) in @('B') as well the simplifications of any
 @(':assumptions') provided.  If any such simplification yields an unchanged
 subterm, then the call of @('simplify-defun') fails.  Note that any dive into
 the body of a @('LET') expression takes into account its bindings.</li>

 </ol>

 <p>Note: Because of how patterns are handled, you may find it safest to avoid
 variables @('@') and @('_') in favor of their subscripted versions (e.g.,
 @('@3') or @('_4')), if you use macros &mdash; in particular, @(tsee or)
 &mdash; and are surprised by how patterns are matched.  Consider the following
 example.</p>

 @({
 (defun foo (x y)
   (if (true-listp (cons 3 x))
       (or (eql (length x) 17) y)
     'dont-care))
 })

 <p>Then the following log may seem surprising at first, since the pattern
 might seem to specify only the call of @('foo') in the body of the
 definition.</p>

 @({
 ACL2 !>(simplify-defun foo :simplify-body (or @ _))
  (DEFUN FOO$1 (X Y)
         (DECLARE (XARGS :GUARD T
                         :VERIFY-GUARDS NIL))
         (IF (TRUE-LISTP X)
             (OR (EQUAL (LEN X) 17) Y)
             'DONT-CARE))
 ACL2 !>
 })

 <p>But the pattern @('(or @ _)') translates to @('(if @ @ _)'), which matches
 the entire body; hence both the test of the top-level @('IF') call and its
 true branch were simplified.  If instead we provide a subscript as shown
 below, the result is what we might reasonably expect: the match this time is
 on the @('OR') call in the body, since @('(if @1 @1 _)') only matches when the
 test and true branch of the @('IF') call are the same.</p>

 @({
 ACL2 !>(simplify-defun foo :simplify-body (or @1 _))
  (DEFUN FOO$1 (X Y)
         (DECLARE (XARGS :GUARD T
                         :VERIFY-GUARDS NIL))
         (IF (TRUE-LISTP (CONS 3 X))
             (OR (EQUAL (LEN X) 17) Y)
             'DONT-CARE))
 ACL2 !>
 })

 </blockquote>

 <p>
 @(':simplify-guard') &mdash; default @('nil')<br/>
 @(':simplify-measure') &mdash; default @('nil')
 </p>
 <blockquote>

 <p>Determine whether to simplify the guard or the measure of the input
 function symbol, respectively.</p>

 <p>A non-@('nil') value indicates that simplification is to be attempted.</p>

 </blockquote>

 <p>
 @(':thm-enable') &mdash; default @('t')<br/>
 @(':thm-name') &mdash; default @(':auto')
 </p>
 <blockquote>

 <p>Determines the name and enabled status of the new theorem.</p>

 <p>If @(':thm-enable') has value @('nil'), then the generated theorem that
 equates the old function symbol @('FN') with the new, @('NEW'), will be a call
 of @('defthmd').  Otherwise, @('defthm') will be used.  In either case: if
 @(':thm-name') is missing or is @(':auto') or @('nil'), then the name of the
 theorem will be @('OLD-becomes-NEW'); otherwise, the name of the theorem will
 be the value of @(':thm-name'), but note that in this case, if @('FN') was
 introduced with @(tsee mutual-recursion) then a value of the form @('(:map ...)')
 (as described above) must be used.</p>

 </blockquote>

 <p>
 @(':theory') &mdash; default @(':none')
 </p>
 <blockquote>

 <p>Specify the theory under which simplification is performed.</p>

 <p>If @(':theory EXPR') is supplied, then simplification will be performed in
 the theory given by @('EXPR'), that is, as though the event @('(in-theory
 EXPR)') were first evaluated.  If either the @(':disable') or @(':enable')
 keyword is supplied, then it is illegal to supply @(':theory').  Note that if
 @(':theory') is omitted (or @(':none')), then the @(see acl2::definition),
 @(see acl2::executable-counterpart), and @(see acl2::type-prescription) @(see
 acl2::rune)s for the given function symbol, @('FN'), will all be added
 automatically to the @(':disable') argument.  Note also that some disabling
 may be useful if it is desired to preserve certain operators with special
 behavior such as @(tsee prog2$), @(tsee ec-call), and @(tsee time$); see @(see
 acl2::return-last-blockers).</p>

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
 (defun NEW (...)
   (declare ...)
   NEW-BODY)
 })

 <p>where @('NEW-BODY') is the result of simplifying the body of @('FN') unless
 keyword option @(':simplify-body') has value @('nil').  See above for how that
 option controls simplification of the body, measure, and guard.  The @(see
 declare) form, if any, in the generated definition is generally consistent
 with the declarations in the definition of @('FN'), except when overridden by
 arguments to the @('simplify') (or @('simplify-defun')) call.  For example, by
 default: the generated definition includes a @(':verify-guards') xarg that
 reflects the guard-verified status of @('FN'), and it includes a declaration
 of the form @('(xargs ... :normalize ...)')  if and only if there is such a
 declaration in the definition of @('FN').</p>

 <p>The generated theorem generally has the form</p>

 @({
 (defthm FN-becomes-NEW
   (equal (FN ...) (NEW ...)))
 })

 <p>where the calls of @('FN') and @('NEW') are on the formals of @('FN'), and
 where @('equal') will be replaced by an equivalence relation if specified by
 keyword argument @(':equiv').  However, if either keyword argument
 @(':assumptions') or @(':hyp-fn') specifies assumptions @('A1'), ... @('An'),
 then the generated theorem has the following form (with @('equal') possibly
 replaced by an equivalence relation as explained above).</p>

 @({
 (defthm FN-becomes-NEW
   (implies (and A1 A2 ... An)
            (equal (FN ...) (NEW ...))))
 })

 <p>In both cases, the name of the new theorem shown is the default but may be
 specified with keyword option @(':thm-name').</p>
 ")

(defxdoc simplify-defun-examples
  :parents (simplify-defun)
  :short "Examples illustrating @(tsee simplify-defun)."
  :long "<p>See @(see simplify-defun) for relevant background.  The examples
 below are deliberately simple, in order to make clear how @(tsee
 simplify-defun) behaves with various keyword arguments.</p>

 <h3>Example Set 1: Basics</h3>

 <p>We start with the following basic example.</p>

 @({
 (defun bar (x)
   (declare (xargs :measure (nfix x)))
   (if (zp x) 0 (+ 1 1 (bar (+ -1 x)))))
 (include-book \"kestrel/apt/simplify\" :dir :system)
 (simplify-defun bar
                 :new-name bar-simp
                 :thm-name bar-simplified
                 :new-enable nil
                 :thm-enable t)
 })

 <p>ACL2 responds to this call of @('simplify-defun') by creating the following
 @('DEFUN') form among others, silently submitting the created forms, and then
 returning the new @('DEFUN') form (as the value component of an @(see
 acl2::error-triple)).  The new function is named @('bar-simp') because that is
 what we specified with the @(':new-name') argument above.</p>

 @({
 (DEFUND BAR-SIMP (X)
         (DECLARE (XARGS :GUARD T
                         :MEASURE (NFIX X)
                         :VERIFY-GUARDS NIL ; would be T if BAR were guard-verified
                         :HINTS ((\"Goal\" :USE (:TERMINATION-THEOREM BAR))
                                 '(:IN-THEORY (DISABLE* BAR (:E BAR) (:T BAR))))))
         (IF (ZP X) 0 (+ 2 (BAR-SIMP (+ -1 X)))))
 })

 <p>Notice that the guard and measure are the same as for @('BAR'), but the
 subterm @('(+ 1 1 (bar (+ -1 x)))') of the body of @('bar') has been replaced
 by the simpler term @('(+ 2 (BAR-SIMP (+ -1 X)))') in the body of
 @('bar-simp'), with the recursive call appropriately replaced.</p>

 <p>Adding @(':verbose t') shows simplified non-trivial @(':assumptions'),
 followed by the proposed simplified definition, and then prover output from
 evaluating the generated @(see acl2::events).</p>

 <p>To see the full expansion produced by the call of @('simplify-defun')
 above, we can use @('show-simplify-defun') instead of @('simplify-defun'), on
 the same arguments (or, simply add keyword argument @(':show-only t') to your
 @('simplify-defun') call).  The result is as follows (elided somewhat).</p>

 @({
  (ENCAPSULATE
   NIL
   ... ; helpful stuff local to the encapsulate
   (DEFUND BAR-SIMP (X) ...) ; as shown above
   (LOCAL ; helper events, not shown here
    ...)
   (DEFTHM BAR-SIMPLIFIED ; the value of keyword argument :thm-name
     (EQUAL (BAR X) (BAR-SIMP X))
     :HINTS ...))
 })

 <p>On the other hand, if you want less output, not more, use
 @('simplify-defun') with @(':print nil').  For example:</p>

 @({
 ACL2 !>(simplify-defun bar
                        :new-name bar-simp
                        :thm-name bar-simplified
                        :new-enable nil
                        :thm-enable t
                        :print nil)
  T
 ACL2 !>:pe bar-simp
    d       3:x(SIMPLIFY-DEFUN BAR :NEW-NAME ...)
               \
 >L d           (DEFUN
                 BAR-SIMP (X)
                 (DECLARE
                     (XARGS :GUARD T
                            :MEASURE (NFIX X)
                            :VERIFY-GUARDS NIL
                            :HINTS ((\"Goal\" :USE (:TERMINATION-THEOREM BAR)))))
                 (IF (ZP X) 0 (+ 2 (BAR-SIMP (+ -1 X)))))
 ACL2 !>
 })

 <p>Notice the calls of @(tsee defund) and @(tsee defthm), which respect
 keyword arguments supplied to @('simplify-defun'), @(':new-enable nil')
 and @(':thm-enable t'), respectively.</p>

 <h3>Example Set 2: Assumptions</h3>

 <p>The following trivial example illustrates the use of assumptions.</p>

 @({
 (defun foo (x)
   (ifix x))
 (simplify-defun foo :assumptions ((integerp x)))
 })

 <p>If you want to evaluate the @(':assumptions') argument, or indeed any
 argument @('A') of @('simplify-defun'), simply replace @('A') by @('(:eval
 A)').  The @('simplify-defun') call displayed just above is thus equivalent to
 the following.</p>

 @({
 (simplify-defun foo :assumptions (:eval '((integerp x))))
 })

 <p>Here is the result (either way).  Notice that since we did not specify
 @(':new-name'), the generated function name is obtained by adding a suffix
 @('\"$1\"') to the given function symbol's name.  In general, the least
 natural number @('n') will be used that results in a new function symbol when
 adding the suffix @('\"$n\"').</p>

 @({
 (DEFUN FOO$1 (X)
        (DECLARE (XARGS :GUARD T
                        :VERIFY-GUARDS NIL))
        X)
 })

 <p>Notice that the body was simplified under the given assumption that @('x')
 is an integer; without any such assumption, simplification to @('x') would not
 have taken place.</p>

 <p>The @(':hints') argument allows you to supply @(see acl2::hints) for the
 key lemma that specifies preservation of the assumptions on recursive calls.
 The following example illustrates how that works, based on this
 definition.</p>

 @({
 (defun foo (x)
   (declare (xargs :guard (true-listp x)))
   (if (consp x)
       (foo (cdr x))
     x))
 })

 <p>In this example we specify @(':assumptions :guard'), which means that the
 @(':assumptions') value is taken to be the given function's guard.</p>

 @({
 (show-simplify-defun foo
                      :assumptions :guard
                      :hints
                      (:assumptions-preserved ; the sole applicability condition
                       ((\"Goal\" :in-theory (e/d (append) (union-eq))))))
 })

 <p>The command above generates the following key lemma.  Note that the local
 function @('FOO-HYPS') is defined above with the same formals as the given
 function symbol, and with a body that represents the @(':assumptions')
 argument, which in this example specifies the guard of @('foo').</p>

 @({
 (DEFTHM FOO-HYPS-PRESERVED-FOR-FOO-LEMMA
   (FLET ((FOO-HYPS (X)
                    (DECLARE (IGNORABLE X))
                    (TRUE-LISTP X)))
         (IMPLIES (AND (FOO-HYPS X) (CONSP X))
                  (FOO-HYPS (CDR X))))
   :HINTS ((\"Goal\" :IN-THEORY (E/D (APPEND) (UNION-EQ)))
           '(:USE (:GUARD-THEOREM FOO)))
   :RULE-CLASSES NIL)
 })

 <p>Since the original body is @('(if (consp x) (foo$1 (cdr x)) x)'), we see
 that @('x') has been simplified to @('nil') under the combination of the
 top-level assumption of @('(true-listp x)'), from @(':assumptions :guard'),
 and the governing @('IF') test of @('(not (consp x))').</p>

 <h3>Example Set 3: Simplifying the Guard and Measure</h3>

 <p>The examples above all pertain to simplifying the body of a definition.
 The following example shows how to simplify the guard and/or measure of a
 definition.</p>

 @({
 ACL2 !>(defun foo (x)
           (declare (xargs :guard (and (true-listp x)
                                       (not (atom x)))
                           :measure (fix (len x))))
           (if (consp (cdr x))
               (foo (append nil (cdr x)))
             x))
 ...
  FOO
 ACL2 !>(simplify-defun foo
                        :simplify-body nil
                        :simplify-guard t
                        :simplify-measure t)
  (DEFUN FOO$1 (X)
         (DECLARE (XARGS :GUARD (AND (TRUE-LISTP X) (CONSP X))
                         :MEASURE (LEN X)
                         :VERIFY-GUARDS T
                         :GUARD-HINTS ... ; uses (:GUARD-THEOREM FOO)
                         :HINTS ... ; uses (:GUARD-THEOREM FOO)
                         ))
         (IF (CONSP (CDR X))
             (FOO$1 (APPEND NIL (CDR X)))
             X))
 ACL2 !>
 })

 <p>Clearly the values of both the @(':guard') and the @(':measure') have been
 simplified.</p>

 <p>Notice that the body has not been simplified, even though ACL2 could easily
 simplify @('(APPEND NIL (CDR X))') to @('(CDR X)'), because of the argument
 @(':simplify-body nil').  To simplify the body as well, we can omit
 @(':simplify-body') so that its value defaults to @('t'), or we can specify
 @(':simplify-body t') explicitly.</p>

 <h3>Example Set 4: Guard and Measure Hints</h3>

 <p>@('Simplify-defun') provides keywords @(':guard-hints') and
 @(':measure-hints') for the guard verification and termination proofs of the
 simplified function that is generated.  To see how these work, we can add such
 hints to the @('simplify-defun') form displayed in the section just above.
 Recall that the default hints generated for the guard and termination proofs
 use the guard and termination theorems, respectively, for the function whose
 definition is being simplified.  Suppose now that we add our own hints, for
 example rather nonsensical @(':guard-hints') and @(':measure-hints') as
 follows.</p>

 @({
 (simplify-defun foo
                 :simplify-body nil
                 :simplify-guard t
                 :simplify-measure t
                 :guard-hints ((\"Goal\" :use car-cons))
                 :measure-hints ((\"Goal\" :in-theory (enable nth))))
 })

 <p>This time our own hints show up in the resulting definition of @('FOO$1')
 in place of those that are generated by default.</p>

 @({
                        :GUARD-HINTS ((\"Goal\" :USE CAR-CONS))
                        :HINTS ((\"Goal\" :IN-THEORY (ENABLE NTH)))
 })

 <h3>Example Set 5: Controlling the Theory for Simplification</h3>

 <p>By default, simplification done on behalf of @('simplify-defun') &mdash;
 whether for the body, guard, or measure of a @(tsee defun) form &mdash; is
 carried out in the current theory (see @(see current-theory)).  However, the
 @(':theory') keyword allows control over that theory without changing the
 current theory globally.  Consider the following example.</p>

 @({
 (defun foo (x)
   (declare (xargs :guard (natp x)))
   (car (cons (+ x x) 3)))
 (defthmd double ; disabled globally
   (equal (+ x x) (* 2 x)))
 (simplify-defun foo
                 :theory '(double natp)
                 :simplify-body t ; default
                 :simplify-guard t)
 })

 <p>The resulting @(tsee defun) form contains simplifications for both the
 guard and the body.  The rewrite rule @('double') and the definition of
 @('natp') were applied during the simplification, in spite of being globally
 disabled, because of the specified @(':theory') for simplification.  Note
 that this theory works its way into the generated @(':guard-hints') for the
 generated function.</p>

 <p>For convenience, @(':enable') and/or @(':disable') keywords are available,
 provided that they are not used when @(':theory') is used.  For example,
 specifying @(':enable (double natp)') instead of the @(':theory') hint above
 gives the following result.  Notice that the body is further simplified
 because the built-in rewrite rule @('car-cons') is available this time,
 because the theory is constructed by enabling @('double') and @('natp'),
 rather than consisting of <i>exactly</i> those two rules.</p>

 @({
 (DEFUN FOO$1 (X)
        (DECLARE (XARGS :GUARD (AND (INTEGERP X) (NOT (< X 0)))
                        :VERIFY-GUARDS T
                        :GUARD-HINTS ...))
        (* 2 X))
 })

 <p>At this point let us mention the one keyword argument not yet mentioned:
 @(':verify-guards').  By default, the value of this keyword is @(':auto'),
 meaning that the value of @(':verify-guards') in the generated @('defun') is
 @('t') if the input function symbol is guard-verified, and otherwise is
 @('nil').  If you supply @(':verify-guards nil') explicitly in your
 @('simplify-defun') call, however, then @('nil') will be used instead.  For
 example, that would change the @('defun') for @('FOO$1') displayed just above
 to include</p>

 @({
                        :VERIFY-GUARDS NIL
 })

 <p>instead of what it has currently, namely the following.</p>

 @({
                        :VERIFY-GUARDS T
 })

 <h3>Example Set 6: Simplifying a Subterm</h3>

 <p>Examples above illustrate Boolean values for the @(':simplify-body')
 keyword (default @('t')).  However, @(':simplify-body') can specify a pattern,
 to indicate one or more specific subterms to be simplified.  Consider the
 following example.</p>

 @({
 (defun foo (x) x)
 (defun bar (x) (if x (cons x x) 17))
 (defun f (x y z)
   (cons (if (foo x) (bar x) z)
         (if (foo x) (foo y) z)))
 (simplify-defun f
                 :simplify-body (if (foo x) @ z))
 })

 <p>In a left-to-right depth-first traversal of the body of @('f'), the first
 subterm that matches the pattern &mdash; where @('@') is allowed to be
 instantiated &mdash; is the subterm @('(if (foo x) (bar x) z)').  For that
 match, the appropriate instantiation of @('@') is @('(bar x)').  Therefore,
 the value of @(':simplify-body') above instructs @('simplify-defun') to
 simplify not the entire body of @('f'), but only the subterm @('(bar x)').
 That simplification is to be performed under the result of simplifying the
 conjunction of the @(':assumptions') (simply @('t') in this case) with the
 <i>governors</i> of the subterm, formed from the superior IF-tests.  In this
 case, @('(bar x)') is governed by @('(foo x)'), so the subterm @('(bar x)') is
 simplified under the simplification of @('(foo x)'), i.e., under the
 assumption of @('x') (i.e., that @('x') is non-@('nil')).  Under that
 assumption, @('(bar x)') simplifies to @('(cons x x)'), which explains how the
 new body below is derived from the body of the input function symbol, @('f').
 Notice that no other part of the body has changed.</p>

 @({
 ACL2 !>(simplify-defun f
                  :simplify-body (if (foo x) @ z))
  (DEFUN F$1 (X Y Z)
         (DECLARE (XARGS :GUARD T
                         :VERIFY-GUARDS NIL))
         (CONS (IF (FOO X) (CONS X X) Z)
               (IF (FOO X) (FOO Y) Z)))
 ACL2 !>
 })

 <p>Any variable whose name begins with an atsign (@('@')) gets this special
 treatment, that is, indicating a simplification site.  We call such variables
 ``@-vars''.  Variables whose name starts with the underscore
 character (@('_')), called ``_-vars'', also get special treatment: like
 @-vars, they can be instantiated to match a subterm of the body, but unlike
 @-vars, they do not indicate simplification sites.  For the definitions of
 @('foo'), @('bar'), and @('f') as above, consider the following form.</p>

 @({
 (simplify-defun f
                 :simplify-body (if (foo a) @ z))
 })

 <p>The specified pattern does not match the subterm @('(IF (FOO X) (CONS X X)
 Z)'), because the variable @('A') differs from the variable @('X').  But we
 can fix this by adding an underscore to the front of @('A'), since the pattern
 matches that subterm by instantiating @('_A') to @('X').</p>

 @({
 (simplify-defun f
                 :simplify-body (if (foo _a) @ z))
 })

 <p>For that matter, we can even replace @('Z') in the pattern by any variable
 whose name starts with an underscore, for example as follows.</p>

 @({
 (simplify-defun f
                 :simplify-body (if (foo _a) @ _b))
 })

 <p>Both of the @('simplify-defun') calls just above give rise to the same
 definition of @('F$1') as before (i.e., as displayed above.).</p>

 <p>On the other hand, the following call fails because the variable @('_a')
 would need to be instantiated both to @('X') and to @('Z').</p>

 @({
 (simplify-defun f
                 :simplify-body (if (foo _a) @ _a))
 })

 <p>The _-var, @('_') &mdash; that is the variable in the @('\"ACL2\"') package
 whose @(tsee symbol-name), @('\"_\"'), consists of just a single underscore
 character &mdash; gets special treatment.  It is allowed to match different
 subterms, so this succeeds:</p>

 @({
 (simplify-defun f
                 :simplify-body (if (foo _) @ _))
 })

 <p>See @(see simplify-defun) (specifically, the section on the
 @(':simplify-body') argument) for a precise explanation of the sense in which
 the variable @('_') gets special treatment by allowing matches to more than
 one subterm.</p>

 <p>We have seen that the language of patterns allows variables @('@') and
 @('@XX') to represent simplification sites, as well as variables @('_') and
 @('_XX') that also match arbitrary subterms; here @('XX') denotes an arbitrary
 non-empty suffix, and the symbol's package is arbitrary.  But an additional
 construct can be used to represent simplification sites: @('(:@ u)'), where
 @('u') is a term and the keyword @(':@') is used as a unary function symbol.
 When a pattern is matched against a term, @('(:@ u)') indicates not only that
 @('u') is to be matched, but also that we have a simplification site.  Indeed,
 @('@') is an abbreviation for @('(:@ _)') and @('@XX') is an abbreviation for
 @('(:@ _@XX)').  The @('simplify-defun') call immediately above could thus be
 written equivalently as follows.</p>

 @({
 (simplify-defun f
                 :simplify-body (if (foo _) (:@ _) _))
 })

 <p>Let's look at another example of the use of @(':@'), starting with the
 following (contrived) definition.</p>

 @({
 (defun g (x y)
   (list (+ (nth 0 x) 3)
         (* (car (cons y y)) 4)
         (* (nth 0 x) 5)))
 })

 <p>Suppose we want to simplify just the second call of @('nth') above.  Here's
 a nice way to accomplish that.</p>

 @({
 ACL2 !>(simplify-defun g :simplify-body (* (:@ (nth 0 x)) _))
  (DEFUN G$1 (X Y)
         (DECLARE (XARGS :GUARD T
                         :VERIFY-GUARDS NIL))
         (LIST (+ (NTH 0 X) 3)
               (* (CAR (CONS Y Y)) 4)
               (* (AND (CONSP X) (CAR X)) 5)))
 ACL2 !>
 })

 <p>Notice that neither of the following alternatives would produce the result
 above.</p>

 @({
 ; Would simplifythe first occurrence of (nth 0 x) instead:
 (simplify-defun g :simplify-body (:@ (nth 0 x)))

 ; Would simplify (car (cons y y)) instead.
 (simplify-defun g :simplify-body (* @ _))
 })

 <p>Here is an example that specifies more than one subterm to be simplified.
 Consider:</p>

 @({
 (defun foo (x y)
   (list (list (list
                (* 3 (+ 1 (+ 1 x)))
                (* 3 (+ 1 (+ 1 x)))
                (* 4 5 (+ 1 (+ 1 y)))))))
 })

 <p>Then the indicated pattern below matches the subterm</p>

 @({
 (list
  (* 3 (+ 1 (+ 1 x)))
  (* 3 (+ 1 (+ 1 x)))
  (* 4 5 (+ 1 (+ 1 y))))
 })

 <p>with the @-var @('@1') bound to the subterm @('(* 3 (+ 1 (+ 1 x)))') and
 the @-var @('@2') bound to the subterm @('(+ 1 (+ 1 y))'), so that those two
 subterms are simplified.</p>

 @({
 ACL2 !>(simplify-defun foo
                        :simplify-body (list @1 ; equivalently, (:@ _@1)
                                             _
                                             (* _ 5 @2)))
  (DEFUN FOO$1 (X Y)
         (DECLARE (XARGS :GUARD T
                         :VERIFY-GUARDS NIL))
         (LIST (LIST (LIST (+ 6 (* 3 X))
                           (* 3 (+ 1 (+ 1 X)))
                           (* 4 5 (+ 2 Y))))))
 ACL2 !>
 })

 <p>Actually, it suffices simply to use only the special @-var, @('@') &mdash;
 or equivalently, @('(:@ _)') &mdash; to produce the same result, as follows.
 See @(see simplify-defun) (specifically, the section on the
 @(':simplify-body') argument) for a precise explanation of the sense in which
 the variables @('_') and @('@') get special treatment by allowing matches to
 more than one subterm.</p>

 @({
 (simplify-defun foo
                 :simplify-body (list @
                                      _
                                      (* _ 5 @)))
 (simplify-defun foo
                 :simplify-body (list (:@ _)
                                      _
                                      (* _ 5 (:@ _))))
 })

 <p>It is also possible to specify simplification inside @(tsee let)
 and @(tsee let*) expressions.  Let's look at two examples based on the
 following definition.</p>

 @({
 (defun let-test (x y)
   (let* ((u (cons x x))
          (v (car u)))
     (car (cons v y))))
 })

 <p>First we simplify one of the bindings.</p>

 @({
 (simplify-defun let-test :simplify-body (:@ (car _)))
 })

 <p>The new definition body results from simplifying the binding of @('v').
 Notice that the binding of @('u') is dropped, since @('u') is now unusued.
 Also notice that only the binding of @('v') is simplified; the body of the
 @('let*') is left alone.</p>

 @({
 (LET ((V X))
      (CAR (CONS V Y)))
 })

 <p>This time, let us simplify just the body of the definition.  What do you
 think the result will be?  It might surprise you.</p>

 @({
 (simplify-defun let-test :simplify-body (:@ (car (cons _ _))))
 })

 <p>You might have expected that the new body is obtained simply by replacing
 @('(car (cons v y))') by @('v') in the body.  However, the new body is
 simply:</p>

 @({
 X
 })

 <p>To see why, consider how @('simplify-defun') performs the simplification.
 It actually simplifies @('(car (cons v y))') with respect to the bindings
 above it; with that in mind, the result is obviously @('X').  Since the term
 @('(car u)') does not appear in the result, the binding of @('v') is
 discarded, as is the binding of @('u') as before.  We are left simply with
 @('X').</p>

 <h3>Example Set 7: Specifying an equivalence relation</h3>

 <p>By default, the simplified body is equal to the original body, under the
 given assumptions (if any).  But you may specify that the two bodies should
 merely be equivalent, with respect to a specified known equivalence relation.
 Here is an example showing how that works.  We start with the following
 events.</p>

 @({
 (defun fix-true-listp (lst)
   (if (consp lst)
       (cons (car lst)
             (fix-true-listp (cdr lst)))
     nil))

 (defthm member-fix-true-listp
   (iff (member a (fix-true-listp lst))
        (member a lst)))

 (defun foo (e x)
   (member-equal e (fix-true-listp x)))
 })

 <p>We would like to eliminate the call of @('fix-true-listp'), but the
 resulting call of @('member-equal') is only Boolean-equivalent to the original
 call, not equal to it (see @('member-fix-true-listp') above).  Thus, if we try
 evaluating @('(simplify-defun foo)') here, it will fail because no
 simplification takes place.  Instead, we can specify that the @(':equiv') is
 @('iff').</p>

 @({
 ACL2 !>(simplify-defun foo :equiv iff)
  (DEFUN FOO$1 (E X)
         (DECLARE (XARGS :GUARD T
                         :VERIFY-GUARDS NIL))
         (MEMBER-EQUAL E X))
 ACL2 !>
 })

 <h3>Example Set 8: Mutual-recursion</h3>

 <p>If @('(simplify-defun FN ...)') is called where @('FN') is defined using
 @(tsee mutual-recursion), then every function defined with @('FN') will be
 processed.  Consider the following example.</p>

 @({
 (mutual-recursion
  (defun foo (x)
    (if (atom x)
        (+ 1 1)
      (cons (ffn-symb x) (foo-lst (rest x)))))
  (defun foo-lst (x)
    (if (atom x)
        nil
      (cons (+ 1 2 (foo (first x)))
            (foo-lst (rest x))))))
 (simplify-defun foo)
 })

 <p>The result is the introduction of a new @('mutual-recursion') with
 simplified bodies, as follows.</p>

 @({
 (MUTUAL-RECURSION
  (DEFUN FOO$1 (X)
    (DECLARE (XARGS ...))
    (IF (CONSP X)
        (CONS (CAR X) (FOO-LST$1 (CDR X)))
        2))
  (DEFUN FOO-LST$1 (X)
    (DECLARE (XARGS ...))
    (IF (CONSP X)
        (CONS (+ 3 (FOO$1 (CAR X)))
              (FOO-LST$1 (CDR X)))
        NIL)))
 })

 <p>Moreover, keyword arguments are handled in a special way (except for
 @(':non-executable'), @(':print'), @(':verify-guards'), and @(':show-only'),
 which we ignore in this example).  Normally keyword arguments will be applied
 to every function that is defined by the @('mutual-recursion').  For example,
 the @('simplify-defun') call above is equivalent to @('(simplify-defun
 foo :simplify-body t)'), which directs simplification of the body not only for
 @('foo') but also for @('foo-lst') &mdash; that is, for every member of the
 <i>clique</i> of functions introduced by the @('mutual-recursion').  A special
 construct, @(':map'), allows different values of a keyword argument for
 different members of that clique.  For the given @('mutual-recursion') above,
 suppose that instead of the @('simplify-defun') call above, we invoke:</p>

 @({
 (simplify-defun foo :simplify-body (:map (foo t) (foo-lst nil)))
 })

 <p>Then, as specified, only the definition of @('foo') is simplified in the
 result.</p>

 @({
 (MUTUAL-RECURSION
  (DEFUN FOO$1 (X)
    (DECLARE (XARGS ...))
    (IF (CONSP X)
        (CONS (CAR X) (FOO-LST$1 (CDR X)))
        2))
  (DEFUN FOO-LST$1 (X)
    (DECLARE (XARGS ...))
    (IF (ATOM X)
        NIL
        (CONS (+ 1 2 (FOO$1 (FIRST X)))
              (FOO-LST$1 (REST X))))))
 })

")

(defxdoc simplify-defun+
  :parents (apt)
  :short "Simplify the definition of a given function, including the guard and measure."
  :long "<p>See @(see simplify-defun).  @('Simplify-defun+') is merely a macro
 whose calls expand to corresponding calls of @('simplify-defun') with
 @(':simplify-guard t') and @(':simplify-measure t').  For example:</p>

 @({
 ACL2 !>:trans1 (simplify-defun+ f1 :enable (foo bar))
  (SIMPLIFY-DEFUN F1
                  :SIMPLIFY-GUARD T
                  :SIMPLIFY-MEASURE T
                  :ENABLE (FOO BAR))
 ACL2 !>:trans1 (show-simplify-defun+ f1 :enable (foo bar))
  (SHOW-SIMPLIFY-DEFUN F1
                       :SIMPLIFY-GUARD T
                       :SIMPLIFY-MEASURE T
                       :ENABLE (FOO BAR))
 ACL2 !>
 })
 ")

(acl2::defpointer show-simplify-defun+ simplify-defun+)
(acl2::defpointer show-simplify-defun simplify-defun)

(defxdoc simplify-defun-programmatic
  :parents (apt)
  :short "Programmatic interface to @(tsee simplify-defun)"
  :long "<p>Call @('simplify-defun-programmatic') exactly as you would call
 @(tsee simplify-defun), except that arguments are not automatically quoted; so
 avoid using arguments of the form @('(:eval x)').  Unlike @('simplify-defun'),
 @('simplify-defun-programmatic') does not introduce a new definition or
 theorem.  Rather, it returns the @('encapsulate') form that would be evaluated
 by @('simplify-defun') &mdash; that is, the form displayed by a corresponding
 call of @(tsee show-simplify-defun).</p>")
