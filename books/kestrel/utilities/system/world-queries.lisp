; System Utilities -- World Queries
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2018 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)
(include-book "system/pseudo-good-worldp" :dir :system)

(include-book "kestrel/std/system/arity-plus" :dir :system)
(include-book "kestrel/std/system/classes" :dir :system)
(include-book "kestrel/std/system/classes-plus" :dir :system)
(include-book "kestrel/std/system/definedp" :dir :system)
(include-book "kestrel/std/system/definedp-plus" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/fresh-namep" :dir :system)
(include-book "kestrel/std/system/function-name-listp" :dir :system)
(include-book "kestrel/std/system/function-namep" :dir :system)
(include-book "kestrel/std/system/function-symbol-listp" :dir :system)
(include-book "kestrel/std/system/fundef-disabledp" :dir :system)
(include-book "kestrel/std/system/fundef-enabledp" :dir :system)
(include-book "kestrel/std/system/guard-verified-p" :dir :system)
(include-book "kestrel/std/system/guard-verified-p-plus" :dir :system)
(include-book "kestrel/std/system/included-books" :dir :system)
(include-book "kestrel/std/system/induction-machine" :dir :system)
(include-book "kestrel/std/system/induction-machine-plus" :dir :system)
(include-book "kestrel/std/system/irecursivep" :dir :system)
(include-book "kestrel/std/system/irecursivep-plus" :dir :system)
(include-book "kestrel/std/system/known-packages" :dir :system)
(include-book "kestrel/std/system/known-packages-plus" :dir :system)
(include-book "kestrel/std/system/logic-function-namep" :dir :system)
(include-book "kestrel/std/system/logical-name-listp" :dir :system)
(include-book "kestrel/std/system/macro-args-plus" :dir :system)
(include-book "kestrel/std/system/macro-keyword-args" :dir :system)
(include-book "kestrel/std/system/macro-keyword-args-plus" :dir :system)
(include-book "kestrel/std/system/macro-required-args" :dir :system)
(include-book "kestrel/std/system/macro-required-args-plus" :dir :system)
(include-book "kestrel/std/system/macro-name-listp" :dir :system)
(include-book "kestrel/std/system/macro-namep" :dir :system)
(include-book "kestrel/std/system/macro-symbol-listp" :dir :system)
(include-book "kestrel/std/system/macro-symbolp" :dir :system)
(include-book "kestrel/std/system/measure" :dir :system)
(include-book "kestrel/std/system/measure-plus" :dir :system)
(include-book "kestrel/std/system/measured-subset" :dir :system)
(include-book "kestrel/std/system/measured-subset-plus" :dir :system)
(include-book "kestrel/std/system/no-stobjs-p" :dir :system)
(include-book "kestrel/std/system/no-stobjs-p-plus" :dir :system)
(include-book "kestrel/std/system/non-executablep" :dir :system)
(include-book "kestrel/std/system/non-executablep-plus" :dir :system)
(include-book "kestrel/std/system/number-of-results" :dir :system)
(include-book "kestrel/std/system/number-of-results-plus" :dir :system)
(include-book "kestrel/std/system/pseudo-tests-and-callp" :dir :system)
(include-book "kestrel/std/system/pseudo-tests-and-call-listp" :dir :system)
(include-book "kestrel/std/system/primitivep" :dir :system)
(include-book "kestrel/std/system/primitivep-plus" :dir :system)
(include-book "kestrel/std/system/ruler-extenders" :dir :system)
(include-book "kestrel/std/system/ruler-extenders-plus" :dir :system)
(include-book "kestrel/std/system/rune-disabledp" :dir :system)
(include-book "kestrel/std/system/rune-enabledp" :dir :system)
(include-book "kestrel/std/system/stobjs-in-plus" :dir :system)
(include-book "kestrel/std/system/stobjs-out-plus" :dir :system)
(include-book "kestrel/std/system/term-function-recognizers" :dir :system)
(include-book "kestrel/std/system/thm-formula" :dir :system)
(include-book "kestrel/std/system/thm-formula-plus" :dir :system)
(include-book "kestrel/std/system/theorem-name-listp" :dir :system)
(include-book "kestrel/std/system/theorem-namep" :dir :system)
(include-book "kestrel/std/system/theorem-symbol-listp" :dir :system)
(include-book "kestrel/std/system/theorem-symbolp" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)
(include-book "kestrel/std/system/ubody-plus" :dir :system)
(include-book "kestrel/std/system/uguard" :dir :system)
(include-book "kestrel/std/system/uguard-plus" :dir :system)
(include-book "kestrel/std/system/unwrapped-nonexec-body" :dir :system)
(include-book "kestrel/std/system/unwrapped-nonexec-body-plus" :dir :system)
(include-book "kestrel/std/system/well-founded-relation" :dir :system)
(include-book "kestrel/std/system/well-founded-relation-plus" :dir :system)

(local (include-book "std/typed-lists/symbol-listp" :dir :system))
(local (include-book "arglistp-theorems"))
(local (include-book "world-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc world-queries
  :parents (system-utilities-non-built-in)
  :short "Utilities to query @(see world)s."
  :long
  "<p>
   These complement the world query utilities
   in the <see topic='@(url system-utilities)'>built-in system utilities</see>.
   </p>
   <p>
   Many of these world query utilities come in two variants:
   a ``fast'' one and a ``logic-friendly'' one.
   The former has relatively weak and no (strong) return type theorems;
   the latter has stronger guards and some run-time checks
   that are believed to never fail
   and that enable the proof of (stronger) return type theorems
   without having to assume stronger properties in the guard
   of the @(see world) arguments.
   The logic-friendly variants are helpful
   to prove properties (including verifying guards)
   of logic-mode code that calls them,
   but the fast variants avoid the performance penalty
   of the always-satisfied run-time checks,
   when proving properties of the code that calls them is not a focus
   (e.g. in program-mode code).
   </p>
   <p>
   The built-in world query utilities
   have the characteristics of the fast variants.
   Below we provide logic-friendly variants of
   some built-in world query utilities.
   </p>
   <p>
   The fast variants provided below are named in a way
   that is ``consistent'' with the built-in world query utilities.
   The logic-friendly world query utilities are named by adding @('+')
   after the name of the corresponding fast world query utilities
   (both built-in and provided below).
   </p>
   <p>
   These utilities are being moved to @(csee std/system).
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define recursive-calls ((fn symbolp) (wrld plist-worldp))
  :returns (calls-with-tests "A @(tsee pseudo-tests-and-call-listp).")
  :mode :program
  :parents (world-queries)
  :short "Recursive calls of a named non-mutually-recursive function,
          along with the controlling tests."
  :long
  "<p>
   For singly recursive logic-mode functions,
   this is similar to the result of @(tsee induction-machine),
   but each record has one recursive call (instead of zero or more),
   and there is exactly one record for each recursive call.
   </p>
   <p>
   This utility works on both logic-mode and program-mode functions
   (if the program-mode functions have an @('unnormalized-body') property).
   This utility should not be called on a function that is
   mutually recursive with other functions;
   it must be called only on singly recursive functions,
   or on non-recursive functions (the result is @('nil') in this case).
   </p>
   <p>
   This utility may be extended to handle also mutually recursive functions.
   </p>
   <p>
   If the function is in logic mode and recursive,
   we obtain its ruler extenders and pass them to
   the built-in function @('termination-machine').
   Otherwise, we pass the default ruler extenders.
   </p>"
  (b* ((ruler-extenders (if (and (logicp fn wrld)
                                 (irecursivep fn wrld))
                            (ruler-extenders fn wrld)
                          (default-ruler-extenders wrld))))
    (termination-machine
     (list fn) (ubody fn wrld) nil nil ruler-extenders)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist pseudo-event-landmark-listp (x)
  (pseudo-event-landmarkp x)
  :parents (world-queries)
  :short "Recognize true lists of event landmarks."
  :long
  "<p>
   See @('pseudo-event-landmarkp')
   in @('[books]/system/pseudo-good-worldp.lisp').
   </p>"
  :true-listp t
  :elementp-of-nil nil)

(std::deflist pseudo-command-landmark-listp (x)
  (pseudo-command-landmarkp x)
  :parents (world-queries)
  :short "Recognize true lists of command landmarks."
  :long
  "<p>
   See @('pseudo-command-landmarkp')
   in @('[books]/system/pseudo-good-worldp.lisp').
   </p>"
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define event-landmark-names ((event pseudo-event-landmarkp))
  :returns (names "A @('string-or-symbol-listp').")
  :verify-guards nil
  :parents (world-queries)
  :short "Names introduced by an event landmark."
  :long
  "<p>
   Each event landmark introduces zero or more names into the @(see world).
   See @('pseudo-event-landmarkp')
   in @('[books]/system/pseudo-good-worldp.lisp'),
   and the description of event tuples in the ACL2 source code.
   </p>"
  (let ((namex (access-event-tuple-namex event)))
    (cond ((equal namex 0) nil) ; no names
          ((consp namex) namex) ; list of names
          (t (list namex))))) ; single name
