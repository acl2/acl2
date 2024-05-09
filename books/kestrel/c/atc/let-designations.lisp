; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-let-designations
  :parents (atc-shallow-embedding)
  :short "Designations of @(tsee let) and @(tsee mv-let) representations
          for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2's @(tsee let) is used to represent different things in C:")
   (xdoc::ol
    (xdoc::li
     "A local variable declaration with an initializer.")
    (xdoc::li
     "An assignment of an expression to a local variable.")
    (xdoc::li
     "An assignment to an integer by pointer.")
    (xdoc::li
     "An assignment to an element of an array.")
    (xdoc::li
     "An assignment to an integer member of a structure.")
    (xdoc::li
     "An assignment to an element of an array member of a structure.")
    (xdoc::li
     "A transformation of a variable via statements."))
   (xdoc::p
    "The third, fourth, fifth, and sixth cases are recognized
     by the presence of certain write functions,
     according to the patterns described in the user documentation.
     The other three cases could be recognized
     by looking at the conditions that must hold in each cases,
     but in order to ease ATC's task,
     and also to encourage the user to explicate their intentions,
     we use @(tsee declar) and @(tsee assign)
     to indicate the declaration and assignment cases,
     as explained in the user documentation.
     Thus, the seventh case is what remains
     when the others do not apply.")
   (xdoc::p
    "In all four cases above,
     the term to which the variable is bound must be single-valued.
     For multi-valued terms, we follow a similar approach for @(tsee mv-let),
     which is used to represent three different things in C:")
   (xdoc::ol
    (xdoc::li
     "A local variable declaration with an initializer
      that side-effects some variable(s)
      in addition to returning the value to initialize the variable with.")
    (xdoc::li
     "An assignment of an expression to a local variable
      where the expression side-effects some variable(s)
      in addition to returning the value to assign to the variable.")
    (xdoc::li
     "A transformation of two or more variables via statements."))
   (xdoc::p
    "These cases mirror the first, second, and last cases
     described above for @(tsee let).")
   (xdoc::p
    "For these @(tsee mv-let) cases,
     we use a similiar approach to the @(tsee let) cases,
     i.e. we explicitly use indicators for declarations and assignments.
     But the functions @(tsee declar) and @(tsee assign)
     cannot be applied to multi-valued terms.
     Thus, we introduce macros @('declar<n>') and @('assign<n>'),
     for @('<n>') equal to 1, 2, 3, etc.
     (we stop at some point, but it is easy to add more if needed).
     Note that @('<n>') indicates the number of side-effected variables,
     in addition to the declared or assigned variable;
     it does not indicate the number of variables bound by @(tsee mv-let),
     which are always @('<n> + 1').
     These must be macros, and cannot be functions,
     because function may be only applied to single-valued terms,
     while macros do not have that restriction;
     and we need to have different macros for different values of @('<n>').
     These representations are described in the user documentation.")
   (xdoc::p
    "Since ATC works on translated terms,
     it does not directly see the macros @('declar<n>') and @('assign<n>').
     But it recognizes their presence as the term patterns they expand to.
     See the ATC developer documentation for details.")
   (xdoc::p
    "We remark that an external (APT) transformation
     could automatically add the needed wrappers
     based on the conditions under which a @(tsee let) or @(tsee mv-let) occurs.
     Thus, our approach does not forgo automation,
     but rather modularizes the problem into simpler pieces."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define declar (x)
  :short "Wrapper to indicate a C local variable declaration in a @(tsee let)."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assign (x)
  :short "Wrapper to indicate a C local variable assignment in a @(tsee let)."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar1 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 1 additional variable."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1)
     ,x
     (mv (declar *0) *1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign1 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 1 additional variable."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1)
     ,x
     (mv (assign *0) *1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar2 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 2 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2)
     ,x
     (mv (declar *0) *1 *2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign2 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 2 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2)
     ,x
     (mv (assign *0) *1 *2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar3 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 3 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3)
     ,x
     (mv (declar *0) *1 *2 *3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign3 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 3 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3)
     ,x
     (mv (assign *0) *1 *2 *3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar4 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 4 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4)
     ,x
     (mv (declar *0) *1 *2 *3 *4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign4 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 4 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4)
     ,x
     (mv (assign *0) *1 *2 *3 *4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar5 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 5 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5)
     ,x
     (mv (declar *0) *1 *2 *3 *4 *5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign5 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 5 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5)
     ,x
     (mv (assign *0) *1 *2 *3 *4 *5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar6 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 6 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5 *6)
     ,x
     (mv (declar *0) *1 *2 *3 *4 *5 *6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign6 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 6 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5 *6)
     ,x
     (mv (assign *0) *1 *2 *3 *4 *5 *6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar7 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 7 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5 *6 *7)
     ,x
     (mv (declar *0) *1 *2 *3 *4 *5 *6 *7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign7 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 7 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5 *6 *7)
     ,x
     (mv (assign *0) *1 *2 *3 *4 *5 *6 *7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar8 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 8 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5 *6 *7 *8)
     ,x
     (mv (declar *0) *1 *2 *3 *4 *5 *6 *7 *8)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign8 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 8 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5 *6 *7 *8)
     ,x
     (mv (assign *0) *1 *2 *3 *4 *5 *6 *7 *8)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar9 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) that side-effects 9 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5 *6 *7 *8 *9)
     ,x
     (mv (declar *0) *1 *2 *3 *4 *5 *6 *7 *8 *9)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign9 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) that side-effects 9 additional variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*0 *1 *2 *3 *4 *5 *6 *7 *8 *9)
     ,x
     (mv (assign *0) *1 *2 *3 *4 *5 *6 *7 *8 *9)))
