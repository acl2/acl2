; Documentation for terms-light library
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc terms-light
  :parents (kestrel-books)
  :short "A lightweight library for ACL2 pseudo-terms."
  :long
  (xdoc::topstring

   (xdoc::p
    "This library provides logic-mode, guard-verified utilities for
     inspecting, constructing, and transforming "
    (xdoc::seetopic "pseudo-termp" "pseudo-terms")
    ".  The functions are
     intended as small reusable building blocks for tools that operate on
     already-translated ACL2 terms &mdash; APT-style transformations, verified
     rewriters, code generators (e.g., "
    (xdoc::seetopic "c::atc" "atc")
    "), and term-walking utilities in general.")

   (xdoc::p
    "The library is intentionally minimal: each book introduces a focused
     utility plus its basic correctness theorems, with as few dependencies as
     practical.  This makes it easy to include only what you need without
     pulling in larger libraries.")

   (xdoc::h3 "What the library covers")

   (xdoc::ul

    (xdoc::li
     (xdoc::b "Recognizers for term shape")
     " &mdash; @('lambda-free-termp'), @('lambdas-closed-in-termp'),
      @('all-lambdas-serialized-in-termp'),
      @('no-duplicate-lambda-formals-in-termp'),
      @('no-nils-in-termp').")

    ;; Note: COUNT-OCCURENCES-IN-TERM is spelled with one 'r', matching
    ;; the function name, even though the file is count-occurrences-in-term.lisp
    ;; (two 'r's).
    (xdoc::li
     (xdoc::b "Free-variable and bound-variable analysis")
     " &mdash;
      @('free-vars-in-term'), @('bound-vars-in-term'), @('let-vars-in-term'),
      @('count-occurences-in-term'), and multiple utilities for counting
      variable occurrences in @('count-vars.lisp').")

    (xdoc::li
     (xdoc::b "Substitution and rewriting")
     " &mdash; @('sublis-var-simple'),
      @('subst-var-alt'), @('subst-var-deep'), @('rename-vars-in-term'),
      @('replace-term-with-term'), @('replace-corresponding-arg'),
      @('substitute-constants-in-lambdas'), and utilities for substituting
      lambda formals and unnecessary lambda variables in
      @('substitute-lambda-formals.lisp'),
      @('substitute-unnecessary-lambda-vars.lisp'), and
      @('substitute-unnecessary-lambda-vars2.lisp').")

    (xdoc::li
     (xdoc::b "Lambda construction")
     " &mdash; @('make-lambda-nest'),
      @('make-lambda-application-simple'),
      @('make-lambda-term-simple'),
      @('make-lambda-terms-simple'), @('make-lambda-with-hint').")

    (xdoc::li
     (xdoc::b "Lambda elimination and cleanup")
     " &mdash;
      @('expand-lambdas-in-term') (full beta-reduction),
      @('drop-trivial-lambdas') (remove lambdas binding formals to themselves),
      @('drop-unused-lambda-bindings'),
      @('serialize-lambdas-in-term').")

    (xdoc::li
     (xdoc::b "Reverse direction: lambdas back to LET / LET* / MV-LET")
     " &mdash;
      @(see reconstruct-lets-in-term),
      @('restore-mv-lets-in-term'), @('restore-mv-in-branches'),
      @(see simple-untranslate-in-term),
      @(see reconstruct-and-untranslate-term).")

    (xdoc::li
     (xdoc::b "Term constructors")
     " &mdash; @('make-if-term') (an iff-preserving IF
      builder with built-in simplifications), @('negate-term').")

    (xdoc::li
     (xdoc::b "IF-shape inspection and simplification")
     " &mdash; @('count-ifs-in-term'),
      @('count-ifs-in-then-and-else-branches'),
      @('combine-ifs-in-then-and-else-branches'), @('pre-simplify-term').")

    (xdoc::li
     (xdoc::b "Conjunction / disjunction structure")
     " &mdash; @('get-conjuncts'),
      @('get-hyps-and-conc'), @('term-is-conjunctionp'),
      @('term-is-disjunctionp'), @('drop-clearly-implied-conjuncts'),
      @('simplify-ors'), and utilities for strengthening conjuncts in
      @('strengthen-conjuncts.lisp').")

    (xdoc::li
     (xdoc::b "Function-call inspection")
     " &mdash; @('expr-calls-fn'), utilities for finding function-call
      subterms in @('function-call-subterms.lisp'), and rules about the
      built-in @(tsee all-fnnames1) in @('all-fnnames1.lisp')."))

   (xdoc::p
    "See the individual books under @('kestrel/terms-light/') for
     per-utility details, theorems, and tests.  Functions in this library are
     logic-mode and have verified guards unless specifically noted.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc reconstruct-lets-in-term
  :parents (terms-light)
  :short "Convert lambda applications in a pseudo-term back into surface-level
          @(tsee let), @(tsee let*), and @(tsee mv-let) forms."
  :long
  (xdoc::topstring

   (xdoc::p
    "Operates on a @(tsee pseudo-termp) and returns a Lisp form that is
     semantically equivalent but is no longer a @(tsee pseudo-termp): it
     contains user-level @(tsee let), @(tsee let*), and/or @(tsee mv-let)
     special forms.  This is useful for producing readable output from APT
     transformations and other tools that work on translated terms.")

   (xdoc::p
    "The recognizer for the translated form of @(tsee mv-let) is built in:
     @('translated-mv-letp') matches the two-lambda nest that ACL2's
     translator emits.  When the recognizer fires, the form is rebuilt as a
     user-level @(tsee mv-let); otherwise lambda applications become
     @(tsee let) bindings, with trivially-bound formals (those bound to
     themselves) elided and ignored variables surfaced via
     @('(declare (ignore ...))').")

   (xdoc::codeblock
    "General Form:"
    "(reconstruct-lets-in-term term)")

   (xdoc::p "where:")

   (xdoc::ul
    (xdoc::li "@('term') is a @(tsee pseudo-termp)."))

   (xdoc::p
    "The result is usually NOT a @(tsee pseudo-termp), because it contains
     @(tsee let) and/or @(tsee mv-let) special forms.")

   (xdoc::h3 "Notes")

   (xdoc::ul
    (xdoc::li
     "Function-call subterms remain in their translated form: arithmetic
      abbreviations such as @(tsee binary-+) are not rewritten to @(tsee +),
      and self-quoting constants such as "
     (xdoc::tt "'3")
     " are not unquoted.  Apply
      @(see simple-untranslate-in-term) on the result for those readability
      passes, or use @(see reconstruct-and-untranslate-term) to do both at
      once.")

    (xdoc::li
     "The translated @(tsee mv) constructor "
     (xdoc::tt "(cons '3 (cons '4 'nil))")
     " is not rewritten back to @('(mv 3 4)') by this function;
      see @('restore-mv-in-branches') for the companion that does so.
      A separate (in-progress) utility, @('restore-mv-lets-in-term'),
      rewrites @('(mv-nth ''0 (mv-list ...))') nests into @(tsee mv-let)."))

   (xdoc::h3 "Examples")

   (xdoc::codeblock
    "; :trans (let ((x (+ y z))) (+ 1 x))"
    "(reconstruct-lets-in-term '((lambda (x) (binary-+ '1 x))"
    "                            (binary-+ y z)))"
    "; => (let ((x (binary-+ y z))) (binary-+ '1 x))"
    ""
    "; :trans (mv-let (x y) (mv 3 4) (+ x y))"
    "(reconstruct-lets-in-term '((lambda (mv)"
    "                              ((lambda (x y) (binary-+ x y))"
    "                               (mv-nth '0 mv)"
    "                               (mv-nth '1 mv)))"
    "                            (cons '3 (cons '4 'nil))))"
    "; => (mv-let (x y) (cons '3 (cons '4 'nil)) (binary-+ x y))")

   (xdoc::p
    "See also @(see simple-untranslate-in-term) and
     @(see reconstruct-and-untranslate-term).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc simple-untranslate-in-term
  :parents (terms-light reconstruct-lets-in-term)
  :short "A small readability pass that unquotes self-quoting constants and
          replaces translated arithmetic aliases with their surface forms."
  :long
  (xdoc::topstring

   (xdoc::p
    "Intended to run on the output of @(see reconstruct-lets-in-term).  Two
     passes are applied:")

   (xdoc::ol
    (xdoc::li
     (xdoc::b "Unquote self-quoting constants.")
     "  @('(quote v)') becomes
      @('v') whenever @('v') is a number, character, string, keyword, @('t'),
      or @('nil').  Other quoted values (notably non-keyword symbols and
      conses) are left as @('(quote v)').")

    (xdoc::li
     (xdoc::b "Arithmetic alias replacement.")
     (xdoc::ul
      (xdoc::li "@('(binary-+ a b)') becomes @('(+ a b)')")
      (xdoc::li "@('(binary-* a b)') becomes @('(* a b)')")
      (xdoc::li "@('(unary-- a)') becomes @('(- a)')")
      (xdoc::li "@('(unary-/ a)') becomes @('(/ a)')"))))

   (xdoc::p
    "Other forms pass through structurally.  @(tsee let), @(tsee let*),
     and @(tsee mv-let) special forms are recognized so that bindings'
     values and bodies are untranslated while binding-variable names and
     @(tsee declare) forms are preserved verbatim.")

   (xdoc::p
    "The input is assumed to be the surface-style form produced by
     @(see reconstruct-lets-in-term) (which may contain
     @(tsee let)/@(tsee let*)/@(tsee mv-let)/@(tsee declare) alongside
     ordinary function calls); it is NOT in general a @(tsee pseudo-termp).
     The output is also a surface-style form.")

   (xdoc::codeblock
    "General Form:"
    "(simple-untranslate-in-term term)")

   (xdoc::h3 "Examples")

   (xdoc::codeblock
    "(simple-untranslate-in-term '(binary-+ '1 x))"
    "; => (+ 1 x)"
    ""
    "(simple-untranslate-in-term '(let ((x (binary-+ y z)))"
    "                               (binary-+ '1 x)))"
    "; => (let ((x (+ y z))) (+ 1 x))"
    ""
    "(simple-untranslate-in-term '(mv-let (x y)"
    "                               (cons '3 (cons '4 'nil))"
    "                               (binary-+ x y)))"
    "; => (mv-let (x y) (cons 3 (cons 4 nil)) (+ x y))")

   (xdoc::h3 "Limitations")

   (xdoc::ul
    (xdoc::li
     "Only the four arithmetic aliases above are rewritten.  Other
      translated forms (e.g., @('(if a a b)') for @(tsee or), nested
      @(tsee let)s for @(tsee let*), @('(cons ... 'nil)') for @(tsee list) or
      @(tsee mv)) are left alone.")

    (xdoc::li
     "The pass is purely structural &mdash; no world is consulted."))

   (xdoc::p
    "For the combined operation of reconstructing @(tsee let)/@(tsee mv-let)
     and applying these readability passes, see
     @(see reconstruct-and-untranslate-term).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc reconstruct-and-untranslate-term
  :parents (terms-light reconstruct-lets-in-term)
  :short "Composition of @(see reconstruct-lets-in-term) followed by
          @(see simple-untranslate-in-term)."
  :long
  (xdoc::topstring

   (xdoc::p
    "Convenience function: takes a @(tsee pseudo-termp), reconstructs
     @(tsee let) / @(tsee mv-let) forms, and then applies the small
     readability passes (constant unquoting and arithmetic alias
     replacement).")

   (xdoc::codeblock
    "(reconstruct-and-untranslate-term term)"
    "= (simple-untranslate-in-term (reconstruct-lets-in-term term))")

   (xdoc::p
    "The result is usually not a @(tsee pseudo-termp).")))
