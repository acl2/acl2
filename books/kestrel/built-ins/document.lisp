; Built-Ins Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "collect")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We create XDOC topics that list built-in axioms and theorems,
; organized in two different ways, as defined in collect.lisp:
; (1) according to their rule classes
; (2) according to the *builtin-defaxiom/defthm-<topic>* constants.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Turn a list of names (of axioms and theorems)
; into a string consisting of a sequence of
; corresponding XDOC preprocessor @(def ...) directives.

(defun builtin-names-to-xdoc-defs (names)
  (declare (xargs :guard (symbol-listp names)))
  (cond ((endp names) "")
        (t (concatenate 'string
                        "@(def "
                        (symbol-name (car names))
                        ")"
                        (builtin-names-to-xdoc-defs (cdr names))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc builtin-defaxioms/defthms
  :parents (builtins)
  :short "Built-in axioms and theorems.")

(defxdoc builtin-defaxioms/defthms-by-rule-classes
  :parents (builtin-defaxioms/defthms)
  :short "Built-in axioms and theorems, organized by rule-classes.")

(defxdoc builtin-defaxioms/defthms-by-types/functions
  :parents (builtin-defaxioms/defthms)
  :short "Built-in axioms and theorems, organized by types and functions.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc builtin-defaxioms/defthms-without-rule-classes
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems without rule classes."
  :long (builtin-names-to-xdoc-defs
         *builtin-noclass-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-rewrite
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':rewrite') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-rewrite-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-rewrite-quoted-constant
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':rewrite-quoted-constant') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-rewrite-quoted-constant-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-built-in-clause
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':built-in-clause') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-built-in-clause-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-clause-processor
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':clause-processor') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-clause-processor-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-compound-recognizer
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':compound-recognizer') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-compound-recognizer-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-congruence
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':congruence') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-congruence-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-definition
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':definition') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-definition-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-elim
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':elim') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-elim-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-equivalence
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':equivalence') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-equivalence-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-forward-chaining
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':forward-chaining') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-forward-chaining-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-generalize
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':generalize') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-generalize-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-induction
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':induction') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-induction-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-linear
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':linear') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-linear-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-meta
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':meta') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-meta-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-refinement
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':refinement') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-refinement-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-tau-system
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':tau-system') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-tau-system-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-type-prescription
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':type-prescription') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-type-prescription-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-type-set-inverter
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':type-set-inverter') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-type-set-inverter-defaxiom/defthm-names*))

(defxdoc builtin-defaxioms/defthms-of-class-well-founded-relation
  :parents (builtin-defaxioms/defthms-by-rule-classes)
  :short "Built-in axioms and theorems
          of the @(':well-founded-relation') rule class."
  :long (builtin-names-to-xdoc-defs
         *builtin-well-founded-relation-defaxiom/defthm-names*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc builtin-defaxioms/defthms-about-logical-connectives
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about logical connectives."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-logical-connectives*))

(defxdoc builtin-defaxioms/defthms-about-booleans
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about booleans."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-booleans*))

(defxdoc builtin-defaxioms/defthms-about-cons-pairs
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about @(tsee cons) pairs."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-cons-pairs*))

(defxdoc builtin-defaxioms/defthms-about-numbers
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about numbers."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-numbers*))

(defxdoc builtin-defaxioms/defthms-about-characters
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about characters."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-characters*))

(defxdoc builtin-defaxioms/defthms-about-strings
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about strings."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-strings*))

(defxdoc builtin-defaxioms/defthms-about-symbols
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about symbols."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-symbols*))

(defxdoc builtin-defaxioms/defthms-about-bad-atoms
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about bad atoms."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-bad-atoms*))

(defxdoc builtin-defaxioms/defthms-about-eqlables
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about values amenable to @(tsee eql)."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-eqlables*))

(defxdoc builtin-defaxioms/defthms-about-lists
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about lists."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-lists*))

(defxdoc builtin-defaxioms/defthms-about-alists
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about alists."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-alists*))

(defxdoc builtin-defaxioms/defthms-about-arrays
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about arrays."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-arrays*))

(defxdoc builtin-defaxioms/defthms-about-total-order
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about the total order."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-total-order*))

(defxdoc builtin-defaxioms/defthms-about-ordinals
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about ordinals."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-ordinals*))

(defxdoc builtin-defaxioms/defthms-about-random$
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about (tsee random$)."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-random$*))

(defxdoc builtin-defaxioms/defthms-about-io
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about input/output."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-io*))

(defxdoc builtin-defaxioms/defthms-about-system-utilities
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about system utilities."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-system-utilities*))

(defxdoc builtin-defaxioms/defthms-about-tau
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about @(see tau-system)."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-tau*))

(defxdoc builtin-defaxioms/defthms-about-apply$
  :parents (builtin-defaxioms/defthms-by-types/functions)
  :short "Built-in axioms and theorems about @(tsee apply$)."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom/defthm-apply$*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc builtin-defaxioms
  :parents (builtin-defaxioms/defthms)
  :short "All built-in axioms."
  :long (builtin-names-to-xdoc-defs
         *builtin-defaxiom-names*))

(defxdoc builtin-defthms
  :parents (builtin-defaxioms/defthms)
  :short "All built-in theorems."
  :long (builtin-names-to-xdoc-defs
         *builtin-defthm-names*))
