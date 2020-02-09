; APT (Automated Program Transformations) Library
;
; Copyright (C) 2018 Regents of the University of Texas
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc common-options
  :parents (apt)
  :short "Options that are common to different APT transformations.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc print-specifier

  :parents (common-options)

  :short "Specifies the screen output printed by an APT transformation."

  :long

  (xdoc::topstring

   (xdoc::p
    "A print specifier is passed as the @(':print') input to a transformation.
     It must be one of the following:")

   (xdoc::ul

    (xdoc::li
     "@('nil'), to print nothing (not even error output).")

    (xdoc::li
     "@(':error'), to print only error output (if any).")

    (xdoc::li
     "@(':result'), to print,
      besides error output,
      the generated functions and theorems
      described in reference documentation of the transformation,
      i.e. the result of the transformation.
      This is the default value of the @(':print') input.")

    (xdoc::li
     "@(':info'), to print,
       besides error output and the result (see @(':result') above),
       some additional information
       about the operations performed by the transformation.")

    (xdoc::li
     "@(':all'), to print,
      besides error output,
      the result,
      and the additional information (see @(':info') above),
      also ACL2's output in response to all the submitted events
      (the ones that form the result as well as some ancillary ones)."))

   (xdoc::p
    "If the call to the transformation is
     <see topic='@(url redundancy)'>redundant</see>,
     a message to that effect is printed on the screen,
     unless @(':print') is @('nil').")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc untranslate-specifier

  :parents (common-options)

  :short "Specifies the form of terms produced by an APT transformation."

  :long

  (xdoc::topstring

   (xdoc::p
    "BRIEF SUMMARY (details are skipped here but provided below).  When the
     value of @(':untranslate') is @(':nice'), then a custom utility, @(tsee
     acl2::directed-untranslate), uses the original user-level @(see
     acl2::term) (i.e., the body of a given definition) to direct creation of a
     user-level transformed term from the translated, transformed term.  The
     value @(':nice-expanded') is similar to @(':nice'), but may avoid some
     attempts to re-introduce @('LET') bindings into the result.  If the value
     is @('t'), then the translated, transformed term is subjected to ACL2's
     usual @('untranslate') utility, rather than to that custom @(tsee
     acl2::directed-untranslate) utility.  Otherwise the value should be
     @('nil'), in which case the result of simplifying the term is left alone
     as a translated @(see acl2::term).  End summary.")

   (xdoc::p
    "Strictly speaking, the notion of an ACL2 <i>term</i> is quite restrictive.
     However, ACL2 proof output avoids this notion of ``translated term'',
     instead using a more liberal notion of ``untranslated'' term, in
     which (for example) macros may appear and numbers are not quoted.  For
     more about these two notions of term, see @(see acl2::term).")

   (xdoc::p
    "When a transformation produces a new term (typically, the body of a new
     definition), the question arises: How should that term be presented?
     There are two obvious choices: the new term can be translated or
     untranslated.  For example, if a definition with body @('(+ 1 1 x)') is
     transformed to a definition in which @('2') is added to @('x'), the new
     body would be @('(+ '2 x)') as a translated term but would instead be
     @('(+ 2 x)') as an untranslated term (which avoids the rather ugly
     single-quote mark).  Normally the untranslated term is to be preferred,
     for readability.")

   (xdoc::p
    "But one can sometimes do better, with heuristics, than simply using the
     most obvious untranslated term.  Suppose for example that the original
     definition body is @('(+ 1 1 (first x))').  The simplified body may be
     created as the translated term @('(+ '2 (car x))'), which naturally
     ``untranslates'' to @('(+ 2 (car x))').  The call of the macro, @(tsee
     first), has been lost!  A nicer untranslation will attempt to preserve
     more of the original untranslated term.  This ``nice'' untranslation would
     thus be @('(+ 2 (first x))').  See @(see acl2::directed-untranslate) for
     more information on such ``nice'' untranslation.")

   (xdoc::p
    "A potentially tricky problem is to reconstruct @(tsee let) expressions.
     Suppose for example that the original body is @('(let ((z (first x))) (+ 1
     1 z))').  A transformation might naturally produce a new body that is
     @('(+ 2 (car x))').  A ``nice'' untranslation would ideally reconstruct
     the @('let') expression @('(let ((z (first x))) (+ 2 z))').  In some
     cases, however, the transformation's heuristics might fail to do a good
     job with such reconstructions.  Consider for example the body
     @('(let* ((cost (expt 2 0)) (inches 1)) (list cost inches x))').  a
     transformation might naturally produce a term whose ``nice'' untranslation
     is @('(let* ((cost 1) (inches cost)) (list cost inches x))'), yet it is
     clearly undesirable to bind @('inches') to @('cost').  In some cases, a
     fourth option, the ``nice-expanded'' untranslation, would avoid any
     attempt to reconstruct @('let') structure; in the example above, the
     result might be @('(list 1 1 x)').")

   (xdoc::p
    "An untranslate specifier is passed as the @(':untranslate') input to a
     transformation to control the form of terms produced.  An untranslate
     specifier is one of the following, though some transformations might
     support only some of these values, and the defaults may differ.")
   (xdoc::ul
    (xdoc::li
     "@(':nice') &mdash; the new term should be produced by a ``nice''
     heuristic untranslation that may respect the structure of the old body to
     some reasonable extent, as discussed above.")
    (xdoc::li
     "@('t') &mdash; the new term should be produced by the usual untranslation
      procedure after transforming the input term.")
    (xdoc::li
     "@('nil') &mdash; the new term should be produced without untranslation.")
    (xdoc::li
     "@(':nice-expanded') &mdash; the new term should be produced by a ``nice''
     heuristic untranslation that may respect the structure of the old body to
     some reasonable extent, but may avoid some attempts to reconstruct
     @('let')/@('let*') structure, as discussed above."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc hints-specifier

  :parents (common-options)

  :short "Specifies the form of hints for an APT transformation."

  :long

  (xdoc::topstring

   (xdoc::p
    "The @(':hints') keyword for an APT transformation is legal when there is
     at least one applicability condition.  The value may be a legal @(see
     acl2::hints) value, that is, a legal value for the theorem prover's
     @(':hints') option, as provided for example in a @(tsee defthm) event.
     Otherwise its value should be a keyword-value list (see @(see
     keyword-value-listp))")

   (xdoc::codeblock
    "(:KWD1 h1 :KWD2 h2 ...)")

   (xdoc::p
    "whose keywords @('KWDk') are unique and include only names of
     applicability conditions, where each value @('hk') is a legal @(see
     acl2::hints) value as discussed above.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
