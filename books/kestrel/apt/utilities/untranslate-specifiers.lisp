; APT Utilities -- Print Specifiers
;
; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)
;
; Note: This file is patterned after a similar file in the same directory,
; print-specifiers.lisp, authored by Alessandro Coglio.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/error-checking" :dir :system)
(include-book "kestrel/utilities/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc untranslate-specifier

  :parents (common-options)

  :short "Specifies the form of terms produced by an APT transformation."

  :long

  (str::cat

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
     @('let')/@('let*') structure, as discussed above."))  ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *untranslate-specifier-keywords*
  :parents (untranslate-specifier)
  :short "List of keywords used for untranslate specifiers."
  '(t nil :nice :nice-expanded)
  ///

  (assert-event (symbol-listp *untranslate-specifier-keywords*))

  (assert-event (no-duplicatesp-eq *untranslate-specifier-keywords*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define untranslate-specifier-p (x)
  :returns (yes/no booleanp)
  :parents (untranslate-specifier)
  :short "Recognize untranslate specifiers."
  (if (member-eq x *untranslate-specifier-keywords*) t nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following is analogous to apt::ensure-is-print-specifier.  It may well be
; nice to have at some point, but it is not yet used.

#||
(def-error-checker ensure-is-untranslate-specifier
  ((x "Value to check."))
  "Cause an error if a value is not a untranslate specifier."
  (((untranslate-specifier-p x)
    "~@0 must be an APT untranslate specifier.  See :DOC APT::UNTRANSLATE-SPECIFIER."
    description))
  :parents (untranslate-specifier acl2::error-checking)
  :returns (val (and (implies erp (equal val error-val))
                     (implies (and (not erp) error-erp)
                              (untranslate-specifier-p val))))
  :result x)
||#
