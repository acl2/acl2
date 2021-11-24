; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-let-designations
  :parents (atc-implementation)
  :short "Designations of @(tsee let) and @(tsee mv-let) representations
          for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2's @(tsee let) is used to represent four different things in C:")
   (xdoc::ul
    (xdoc::li
     "A local variable declaration with an initializer.")
    (xdoc::li
     "An assignment of an expression to a local variable.")
    (xdoc::li
     "An assignment to an element of an array variable.")
    (xdoc::li
     "A transformation of a (local or array) variable via statements."))
   (xdoc::p
    "The case of an array element assignment
     is recognized by the presence of the array write functions,
     according to the pattern described in the user documentation.
     The other three cases could be recognized
     by looking at the conditions that must hold in each cases,
     but in order to ease ATC's task,
     and also to encourage the user to explicate their intentions,
     we use @(tsee declar) and @(tsee assign)
     to indicate the declaration and assignment cases,
     as explained in the user documentation.
     Thus, the fourth case is what remains when the other three do not apply.")
   (xdoc::p
    "In all four cases above,
     the term to which the variable is bound must be single-valued.
     For multi-valued terms, we follow a similar approach for @(tsee mv-let),
     which is used to represent three different things in C:")
   (xdoc::ul
    (xdoc::li
     "A local variable declaration with an initializer
      that side-effects some array(s)
      in addition to returning the value to initialize the variable with.")
    (xdoc::li
     "An assignment of an expression to a local variable
      where the expression side-effects some array(s)
      in addition to returning the value to assign to the variable.")
    (xdoc::li
     "A transformation of two or more (local or array) variables
      via statements."))
   (xdoc::p
    "These cases mirror three of the @(tsee let) cases described above,
     with the exclusion of array writes, which are only for @(tsee let),
     due to the restrictions on the ACL2 terms accepted by ATC.")
   (xdoc::p
    "For these @(tsee mv-let) cases,
     we use a similiar approach to the @(tsee let) cases,
     i.e. we explicitly use indicators for declarations and assignments.
     But the functions @(tsee declar) and @(tsee assign)
     cannot be applied to multi-valued terms.
     Thus, we introduce macros @('declar<n>') and @('assign<n>'),
     for @('<n>') equal to 2, 3, etc.
     (we stop at some point, but it is easy to add more if needed).
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

(defmacro+ declar2 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) for 2 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2)
     ,x
     (mv (declar *1) *2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign2 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) for 2 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2)
     ,x
     (mv (assign *1) *2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar3 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) for 3 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3)
     ,x
     (mv (declar *1) *2 *3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign3 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) for 3 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3)
     ,x
     (mv (assign *1) *2 *3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar4 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) for 4 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4)
     ,x
     (mv (declar *1) *2 *3 *4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign4 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) for 4 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4)
     ,x
     (mv (assign *1) *2 *3 *4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar5 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) for 5 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5)
     ,x
     (mv (declar *1) *2 *3 *4 *5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign5 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) for 5 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5)
     ,x
     (mv (assign *1) *2 *3 *4 *5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar6 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) for 6 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5 *6)
     ,x
     (mv (declar *1) *2 *3 *4 *5 *6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign6 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) for 6 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5 *6)
     ,x
     (mv (assign *1) *2 *3 *4 *5 *6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar7 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) for 7 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5 *6 *7)
     ,x
     (mv (declar *1) *2 *3 *4 *5 *6 *7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign7 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) for 7 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5 *6 *7)
     ,x
     (mv (assign *1) *2 *3 *4 *5 *6 *7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar8 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) for 8 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5 *6 *7 *8)
     ,x
     (mv (declar *1) *2 *3 *4 *5 *6 *7 *8)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign8 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) for 8 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5 *6 *7 *8)
     ,x
     (mv (assign *1) *2 *3 *4 *5 *6 *7 *8)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ declar9 (x)
  :short "Wrapper to indicate a C local variable declaration
          in an @(tsee mv-let) for 8 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5 *6 *7 *8 *9)
     ,x
     (mv (declar *1) *2 *3 *4 *5 *6 *7 *8 *9)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ assign9 (x)
  :short "Wrapper to indicate a C local variable assignment
          in an @(tsee mv-let) for 8 bound variables."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  `(mv-let (*1 *2 *3 *4 *5 *6 *7 *8 *9)
     ,x
     (mv (assign *1) *2 *3 *4 *5 *6 *7 *8 *9)))
