; Documentation for terms-light library
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc terms-light
  :parents (kestrel-books)
  :short "A lightweight library for ACL2 pseudo-terms."
  :long
  "<p>This library provides logic-mode, guard-verified utilities for
   inspecting, constructing, and transforming
   <see topic='@(url pseudo-termp)'>pseudo-terms</see>.  The functions are
   intended as small reusable building blocks for tools that operate on
   already-translated ACL2 terms — APT-style transformations, verified
   rewriters, code generators (e.g., @(see acl2::atc)), and term-walking
   utilities in general.</p>

   <p>The library is intentionally minimal: each book introduces a focused
   utility plus its basic correctness theorems, with as few dependencies as
   practical.  This makes it easy to include only what you need without
   pulling in larger libraries.</p>

   <h3>What the library covers</h3>

   <ul>

   <li><b>Recognizers for term shape</b> — @(see pseudo-termp),
   @('lambda-free-termp'), @('lambdas-closed-in-termp'),
   @('all-lambdas-serialized-in-termp'),
   @('no-duplicate-lambda-formals-in-termp'),
   @('no-nils-in-termp').</li>

   <li><b>Free-variable and bound-variable analysis</b> —
   @('free-vars-in-term'), @('bound-vars-in-term'), @('let-vars-in-term'),
   @('all-vars1'), @('count-vars'), @('count-occurrences-in-term').</li>

   <li><b>Substitution and rewriting</b> — @('sublis-var-simple'),
   @('subst-var-alt'), @('subst-var-deep'), @('rename-vars-in-term'),
   @('replace-term-with-term'), @('replace-corresponding-arg'),
   @('substitute-constants-in-lambdas'), @('substitute-lambda-formals'),
   @('substitute-unnecessary-lambda-vars'),
   @('substitute-unnecessary-lambda-vars2').</li>

   <li><b>Lambda construction</b> — @('make-lambda-nest'),
   @('make-lambda-application-simple'), @('make-lambda-term-simple'),
   @('make-lambda-terms-simple'), @('make-lambda-with-hint').</li>

   <li><b>Lambda elimination and cleanup</b> —
   @('expand-lambdas-in-term') (full beta-reduction),
   @('drop-trivial-lambdas') (remove lambdas binding formals to themselves),
   @('drop-unused-lambda-bindings'),
   @('serialize-lambdas-in-term').</li>

   <li><b>Reverse direction: lambdas back to LET / LET* / MV-LET</b> —
   @(see reconstruct-lets-in-term), @('restore-mv-lets-in-term'),
   @(see simple-untranslate-in-term),
   @(see reconstruct-and-untranslate-term).</li>

   <li><b>Term constructors</b> — @('make-if-term') (an iff-preserving IF
   builder with built-in simplifications), @('negate-term'),
   @('negate-terms').</li>

   <li><b>Conjunction / disjunction structure</b> — @('get-conjuncts'),
   @('get-hyps-and-conc'), @('term-is-conjunctionp'),
   @('term-is-disjunctionp'), @('drop-clearly-implied-conjuncts'),
   @('strengthen-conjuncts'), @('simplify-ors').</li>

   <li><b>Function-call inspection</b> — @('function-call-subterms'),
   @('expr-calls-fn'), @('all-fnnames1').</li>

   </ul>

   <p>See the individual books under @('kestrel/terms-light/') for
   per-utility details, theorems, and tests.  Functions in this library are
   logic-mode and have verified guards unless specifically noted.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc reconstruct-lets-in-term
  :parents (terms-light)
  :short "Convert lambda applications in a pseudo-term back into surface-level
          @(tsee let), @(tsee let*), and @(tsee mv-let) forms."
  :long
  "<p>Operates on a @(tsee pseudo-termp) and returns a Lisp form that is
   semantically equivalent but is no longer a @(tsee pseudo-termp): it
   contains user-level @(tsee let), @(tsee let*), and/or @(tsee mv-let)
   special forms.  This is useful for producing readable output from APT
   transformations and other tools that work on translated terms.</p>

   <p>The recognizer for the translated form of @(tsee mv-let) is built in:
   @('translated-mv-letp') matches the two-lambda nest that ACL2's
   translator emits.  When the recognizer fires, the form is rebuilt as a
   user-level @(tsee mv-let); otherwise lambda applications become
   @(tsee let) bindings, with trivially-bound formals (those bound to
   themselves) elided and ignored variables surfaced via
   @('(declare (ignore ...))').</p>

   @({
   General Form:
   (reconstruct-lets-in-term term)
   })

   <p>where:</p>

   <ul>
   <li>@('term') is a @(tsee pseudo-termp).</li>
   </ul>

   <p>The result is usually NOT a @(tsee pseudo-termp), because it contains
   @(tsee let) and/or @(tsee mv-let) special forms.</p>

   <h3>Notes</h3>

   <ul>
   <li>Function-call subterms remain in their translated form: arithmetic
   abbreviations such as @('binary-+') are not rewritten to @('+'), and
   self-quoting constants such as @(''3') are not unquoted.  Apply
   @(see simple-untranslate-in-term) on the result for those readability
   passes, or use @(see reconstruct-and-untranslate-term) to do both at
   once.</li>

   <li>The translated @(tsee mv) constructor @('(cons '3 (cons '4 'nil))')
   is not currently rewritten back to @('(mv 3 4)') by this function;
   see @('restore-mv-lets-in-term') for an in-progress companion that
   does so.</li>
   </ul>

   <h3>Examples</h3>

   @({
   ; :trans (let ((x (+ y z))) (+ 1 x))
   (reconstruct-lets-in-term '((lambda (x) (binary-+ '1 x))
                               (binary-+ y z)))
   ; => (let ((x (binary-+ y z))) (binary-+ '1 x))

   ; :trans (mv-let (x y) (mv 3 4) (+ x y))
   (reconstruct-lets-in-term '((lambda (mv)
                                 ((lambda (x y) (binary-+ x y))
                                  (mv-nth '0 mv)
                                  (mv-nth '1 mv)))
                               (cons '3 (cons '4 'nil))))
   ; => (mv-let (x y) (cons '3 (cons '4 'nil)) (binary-+ x y))
   })

   <p>See also @(see simple-untranslate-in-term) and
   @(see reconstruct-and-untranslate-term).</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc simple-untranslate-in-term
  :parents (terms-light reconstruct-lets-in-term)
  :short "A small readability pass that unquotes self-quoting constants and
          replaces translated arithmetic aliases with their surface forms."
  :long
  "<p>Intended to run on the output of @(see reconstruct-lets-in-term).  Two
   passes are applied:</p>

   <ol>
   <li><b>Unquote self-quoting constants.</b>  @('(quote v)') becomes
   @('v') whenever @('v') is a number, character, string, keyword, @('t'),
   or @('nil').  Other quoted values (notably non-keyword symbols and
   conses) are left as @('(quote v)').</li>

   <li><b>Arithmetic alias replacement.</b>
   <ul>
   <li>@('(binary-+ a b)') becomes @('(+ a b)')</li>
   <li>@('(binary-* a b)') becomes @('(* a b)')</li>
   <li>@('(unary-- a)') becomes @('(- a)')</li>
   <li>@('(unary-/ a)') becomes @('(/ a)')</li>
   </ul></li>
   </ol>

   <p>Other forms pass through structurally.  @(tsee let), @(tsee let*),
   and @(tsee mv-let) special forms are recognized so that bindings'
   values and bodies are untranslated while binding-variable names and
   @('declare') forms are preserved verbatim.</p>

   <p>The input is assumed to be the surface-style form produced by
   @(see reconstruct-lets-in-term) (which may contain
   @(tsee let)/@(tsee let*)/@(tsee mv-let)/@('declare') alongside ordinary
   function calls); it is NOT in general a @(tsee pseudo-termp).  The
   output is also a surface-style form.</p>

   @({
   General Form:
   (simple-untranslate-in-term term)
   })

   <h3>Examples</h3>

   @({
   (simple-untranslate-in-term '(binary-+ '1 x))
   ; => (+ 1 x)

   (simple-untranslate-in-term '(let ((x (binary-+ y z)))
                                  (binary-+ '1 x)))
   ; => (let ((x (+ y z))) (+ 1 x))

   (simple-untranslate-in-term '(mv-let (x y)
                                  (cons '3 (cons '4 'nil))
                                  (binary-+ x y)))
   ; => (mv-let (x y) (cons 3 (cons 4 nil)) (+ x y))
   })

   <h3>Limitations</h3>

   <ul>
   <li>Only the four arithmetic aliases above are rewritten.  Other
   translated forms (e.g., @('(if a a b)') for @(tsee or), nested
   @(tsee let)s for @(tsee let*), @('(cons … 'nil)') for @(tsee list) or
   @(tsee mv)) are left alone.</li>

   <li>The pass is purely structural — no world is consulted.</li>
   </ul>

   <p>For the combined operation of reconstructing @(tsee let)/@(tsee mv-let)
   and applying these readability passes, see
   @(see reconstruct-and-untranslate-term).</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc reconstruct-and-untranslate-term
  :parents (terms-light reconstruct-lets-in-term)
  :short "Composition of @(see reconstruct-lets-in-term) followed by
          @(see simple-untranslate-in-term)."
  :long
  "<p>Convenience function: takes a @(tsee pseudo-termp), reconstructs
   @(tsee let) / @(tsee mv-let) forms, and then applies the small
   readability passes (constant unquoting and arithmetic alias
   replacement).</p>

   @({
   (reconstruct-and-untranslate-term term)
   = (simple-untranslate-in-term (reconstruct-lets-in-term term))
   })

   <p>The result is usually not a @(tsee pseudo-termp).</p>")
