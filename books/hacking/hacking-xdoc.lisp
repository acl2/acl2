; This file was initially generated automatically from legacy documentation
; strings.  See source files in this directory for copyright and license
; information.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc assert-no-special-raw-definition
  :parents (hacker)
  :short "Assert that given symbols do not have a special raw function definition."
  :long "@({
  Example Form:
  (assert-no-special-raw-definition my-fn your-fn)

  General Form:
  (assert-no-special-raw-definition fn1 fn2 ... fnk)
 })

 <p>where each @('fni') is a literal symbol.  An error is raised if any
 @('fni') is is flagged as having a special raw definition.  See @(see
 ensure-special-raw-definition-flag).

 This is a pseudo-event, meaning it can be used in an event context but does
 not (ever) change the world.</p>")

(defxdoc assert-program-mode
  :parents (hacker)
  :short "Assert that given symbols name :PROGRAM mode functions."
  :long "@({
  Example Form:
  (assert-program-mode my-fn your-fn)

  General Form:
  (assert-program-mode fn1 fn2 ... fnk)
 })

 <p>where each @('fni') is a literal symbol which should have a @(tsee program)
 mode definition. An error is raised if any @('fni') is not a program mode
 function.

 This is a pseudo-event, meaning it can be used in an event context but does
 not (ever) change the world.</p>")

(defxdoc defun-bridge
  :parents (hacker)
  :short "Define a function with a different low-level definition."
  :long "<code>
 General Form:
 (defun-bridge <i>name</i> (<i>formals</i>)
   [:doc <i>doc-string</i>]
   [:loop-declare <i>loop-decls</i>]
   :loop <i>loop-body</i>
   [:raw-declare <i>raw-decls</i>]
   :raw <i>raw-body</i>)
 </code>

 <p>This is much like executing</p>

 <code>
 (defun <i>name</i> (<i>formals</i>)
   <i>doc-string</i>
   (declare (xargs :mode :program))
   <i>loop-decls</i>
   <i>loop-body</i>)
 </code>

 <p>in ACL2 and then</p>

 <code>
 (defun <i>name</i> (<i>formals</i>)
   <i>raw-decls</i>
   <i>raw-body</i>)
 </code>

 <p>in raw Lisp, except that extra checks and bookkeeping make it safer than
 that.

 An active ttag is required to use this form (See @(see defttag)), because
 it can easily corrupt ACL2 or render it unsound.</p>")

(defxdoc ensure-program-only
  :parents (hacker)
  :short "Ensure that named functions are and remain in :PROGRAM mode."
  :long "@({
  Example Form:
  (ensure-program-only my-fn your-fn)

  General Form:
  (ensure-program-only fn1 fn2 ... fnk)
 })

 <p>where each @('fni') is a literal symbol which should have a @(tsee program)
 mode definition. An error is raised if any @('fni') is not a program mode
 function.  Also, each @('fni') not already flagged as \"program only\" is
 flagged as such.  This prevents it from being migrated to @(tsee logic) mode
 or being used in a macro.

 This is actually a combination of @(tsee assert-program-mode) and
 @(tsee ensure-program-only-flag).

 This is a pseudo-event, meaning it can be used in an event context but does
 not (ever) change the world.

 Note that the normal undoing mechanism (see @(see ubt)) does not undo the effects
 of this pseudo-event.</p>")

(defxdoc ensure-program-only-flag
  :parents (hacker)
  :short "Ensure that given function names remain in :PROGRAM mode."
  :long "@({
  Example Form:
  (ensure-program-only-flag my-fn your-fn)

  General Form:
  (ensure-program-only-flag fn1 fn2 ... fnk)
 })

 <p>where each @('fni') is a literal symbol which should have a @(tsee program)
 mode definition. Each @('fni') not already flagged as \"program only\" is
 flagged as such.  This prevents it from being migrated to @(tsee logic) mode
 or being used in a macro.

 This is a pseudo-event, meaning it can be used in an event context but does
 not (ever) change the world.

 Note that the normal undoing mechanism (see @(see ubt)) does not undo the effects
 of this pseudo-event.</p>")

(defxdoc ensure-special-raw-definition-flag
  :parents (hacker)
  :short "Ensure that named functions are flagged as having special raw definitions."
  :long "@({
  Example Form:
  (ensure-special-raw-definition-flag my-fn your-fn)

  General Form:
  (ensure-special-raw-definition-flag fn1 fn2 ... fnk)
 })

 <p>where each @('fni') is a literal symbol which should have a function
 definition. Each @('fni') not already flagged as having a special raw
 definition is flagged as such.  This idicates to interested parties that the
 \"loop\" definition of the function doesn't fully characterize the effects it
 has in raw lisp.

 This is a pseudo-event, meaning it can be used in an event context but does
 not (ever) change the world.

 Note that the normal undoing mechanism (see @(see ubt)) does not undo the effects
 of this pseudo-event.</p>")

(defxdoc hacker
  :parents (interfacing-tools)
  :short "Functions for extending ACL2 in ways that are potentially unsound."
  :long "<p>The @('books/hacking') library.</p>

 <p>These functions typically require an active ttag (See @(see defttag)) to
 work.</p>

 ")

(defxdoc in-raw-mode
  :parents (hacker)
  :short "Embed some raw lisp code as an event."
  :long "@({
  Example Form:
  (in-raw-mode
    (format t \"Preparing to load file...~%\")
    (load \"my-file.lisp\"))

  General Form:
  (in-raw-mode form1 form2 ... formk)
 })

 <p>where each @('formi') is processed as though all the forms are preceded by
 @(':')@(tsee set-raw-mode)@(' t').  Thus, the forms need not be @(see events);
 they need not even be legal ACL2 forms.  See @(see set-raw-mode) for a
 discussion of the so-called ``raw mode'' under which the forms are evaluated
 &mdash; unless raw mode is disabled by one of the forms, for example,
 @('(set-raw-mode nil)'), in which case evaluation resumes in non-raw mode.</p>

 <p>WARNING: Thus, an @('in-raw-mode') form is potentially very dangerous!  For
 example, you can use it to call the Common Lisp @('load') function to load
 arbitrary Common Lisp code, perhaps even overwriting definitions of ACL2
 system functions!  Thus, as with @(tsee set-raw-mode), @(tsee in-raw-mode) may
 not be evaluated unless there is an active trust tag in effect.  See @(see
 defttag).</p>

 <p>Note that the normal undoing mechanism (see @(see ubt)) is not supported
 when raw mode is used.</p>")

(defxdoc progn+redef
  :parents (hacker)
  :short "Execute some events but with redefinition enabled."
  :long "@({
  Examples (all equivalent):
  (progn+redef
    (defun foo ...)
    (defun bar ...))
  (progn+redef :action t
    ...)
  (progn+redef :action (:doit! . :overwrite)
    ...)
 })

 <p>This is like @(tsee progn) except that it sets the @(tsee
 ld-redefinition-action) as (optionally) specified for the given events.  An
 @(':action') of @('t') is a shortcut for @('(:doit! . :overwrite)').  @(tsee
 make-event) is used to save and restore the old value of @(tsee
 ld-redefinition-action).

 An active ttag is required to use this form (See @(see defttag)).

 Note that the syntax for this macro is not quite like traditional
 keyword arguments, which would come at the end of the argument list.</p>")

(defxdoc progn+subsume-ttags
  :parents (hacker)
  :short "Execute some events, subsuming the specified ttags with the current ttag."
  :long "@({
  Example:
  (progn+subsume-ttags
    ((:foo) (:bar))
    (include-book
     \"foo\" :ttags ((:foo)))
    (include-book
     \"bar\" :ttags ((:bar))))
 })

 <p>This is like @(tsee progn) except that the first argument is a ttag-spec
 (See @(see defttag)) to be authorized within the constituent events and then
 subsumed.  That is, an active ttag is required to use this form and that ttag
 is (first) used to allow the use of other ttags that may not already be
 authorized and (second) used to wipe the record that any extra ttags were
 used.  This is what is meant by subsumption.  If my book requires a ttag, I
 can then use this to include other books/forms requiring other ttags without
 those others needing specific prior authorization.

 An active ttag is required to use this form (See @(see defttag)).</p>")

(defxdoc progn+touchable
  :parents (hacker)
  :short "Execute some events with some additional fns and/or vars made temporarily touchable."
  :long "@({
  Examples:
  (progn+touchable :all ; same as :fns :all :vars :all
    (defun foo ...)
    (defun bar ...))
  (progn+touchable :vars (current-package ld-skip-proofsp)
    ...)
  (progn+touchable :fns :all
    ...)
  (progn+touchable :fns set-w :vars :all
    ...)
 })

 <p>This is like @(tsee progn) except that it surrounds the events with code to
 add certain fns and/or vars to those that are temporarily touchable.

 Related to @(tsee progn=touchable).

 An active ttag is required to use this form (See @(see defttag)) because it
 can render ACL2 unsound (See @(see remove-untouchable)).

 Note that the syntax for this macro is not quite like traditional
 keyword arguments, which would come at the end of the argument list.</p>")

(defxdoc progn=touchable
  :parents (hacker)
  :short "Execute some events with only the specified fns and/or vars temporarily touchable."
  :long "@({
  Examples:
  (progn=touchable :all ; same as :fns :all :vars :all
    (defun foo ...)
    (defun bar ...))
  (progn=touchable :vars (current-package ld-skip-proofsp) ; :fns ()  implied
    ...)
  (progn=touchable :fns :all    ; :vars ()  implied
    ...)
  (progn=touchable :fns set-w :vars :all
    ...)
 })

 <p>This is like @(tsee progn) except that it surrounds the events with code to
 set only certain fns and/or vars as temporarily touchable.

 Related to @(tsee progn+touchable).

 An active ttag is required to use this form (See @(see defttag)) because it
 can render ACL2 unsound (See @(see remove-untouchable)).

 Note that the syntax for this macro is not quite like traditional
 keyword arguments, which would come at the end of the argument list.</p>")

(defxdoc with-raw-mode
  :parents (hacker)
  :short "Embed some raw lisp code as an event."
  :long "<p>Same as @('in-raw-mode'). See @(see in-raw-mode).</p>")

(defxdoc with-redef-allowed
  :parents (hacker)
  :short "Execute some events but with redefinition enabled."
  :long "<p>Same as @('progn+redef'). See @(see progn+redef).</p>")

(defxdoc with-touchable
  :parents (hacker)
  :short "Execute some events but with certain untouchables removed."
  :long "<p>Same as @('progn+touchable'). See @(see progn+touchable).</p>")
