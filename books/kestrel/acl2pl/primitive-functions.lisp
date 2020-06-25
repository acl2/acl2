; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "values")
(include-book "packages")

(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-functions
  :parents (acl2-programming-language)
  :short "A formalization of the ACL2 primitive functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The " (xdoc::seetopic "acl2::primitive" "ACL2 primitive functions")
    "have no definitions.
     Their evaluation semantics is described in the ACL2 documentation.")
   (xdoc::p
    "In order to formalize the evaluation semantics of ACL2,
     we need to formalize the evaluation semantics of the primitive functions.
     We do so ``directly'' here,
     i.e. not via execution steps through evaluation states
     as we do for defined functions.")
   (xdoc::p
    "Since our formalization of the ACL2 primitive functions
     is written in the ACL2 logical language,
     we make use the executable ACL2 primitive functions of the logical language
     to formalize the ACL2 primitive functions of the ACL2 programming language.
     However, note that the latter operate on our model of ACL2 values,
     i.e. on the @(tsee value) fixtype,
     while the former operate on ACL2 values directly.
     So there is a necessary indirection there,
     due to the meta level nature of our formalization.
     The treatment of symbol values is also slightly different,
     because, as noted in the documentation of @(tsee symbol-value),
     at the meta level we want to be able to talk about
     all possible symbols for all possible known packages,
     and not just the symbols for the packages that happen to be known
     at the point in which we write this formalization.")
   (xdoc::p
    "Here we formalize the evaluation of the ACL2 primitive functions
     in the logic, i.e. for all possible values, inside and outside the guards.
     The treatment of values outside the guards
     are according to the completion axioms shown in the documentation,
     which amount to fixing the values to the required types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-acl2-numberp ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee acl2-numberp)."
  (lift-value (value-case x :number))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-rationalp ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee rationalp)."
  (lift-value (value-case-rational x))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-integerp ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee integerp)."
  (lift-value (value-case-integer x))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-complex-rationalp ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee complex-rationalp)."
  (lift-value (and (value-case x :number)
                   (complex-rationalp (value-number->get x))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-complex ((x valuep) (y valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee complex)."
  (b* ((x-rational (if (value-case-rational x)
                       (value-rational->get x)
                     0))
       (y-rational (if (value-case-rational y)
                       (value-rational->get y)
                     0)))
    (value-number (complex x-rational y-rational)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-realpart ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee realpart)."
  (value-number (if (value-case x :number)
                    (realpart (value-number->get x))
                  0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-imagpart ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee imagpart)."
  (value-number (if (value-case x :number)
                    (imagpart (value-number->get x))
                  0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-numerator ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee numerator)."
  (value-number (if (value-case-rational x)
                    (value-rational->get x)
                  0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-denominator ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee denominator)."
  (value-number (if (value-case-rational x)
                    (value-rational->get x)
                  0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-unary-- ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee unary--)."
  (value-number (if (value-case x :number)
                    (unary-- (value-number->get x))
                  0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-unary-/ ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee unary-/)."
  (value-number (if (value-case x :number)
                    (b* ((x-number (value-number->get x)))
                      (if (/= x-number 0)
                          (unary-/ x-number)
                        0))
                  0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-binary-+ ((x valuep) (y valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee binary-+)."
  (if (value-case x :number)
      (if (value-case y :number)
          (value-number (binary-+ (value-number->get x)
                                  (value-number->get y)))
        (value-fix x))
    (if (value-case y :number)
        (value-fix y)
      (value-number 0)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-binary-* ((x valuep) (y valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee binary-*)."
  (value-number (if (value-case x :number)
                    (if (value-case y :number)
                        (binary-* (value-number->get x)
                                  (value-number->get y))
                      0)
                  0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-< ((x valuep) (y valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee <)."
  (lift-value (if (and (value-case-rational x)
                       (value-case-rational y))
                  (< (value-rational->get x)
                     (value-rational->get y))
                (let ((x1 (if (value-case x :number)
                              (value-number->get x)
                            0))
                      (y1 (if (value-case y :number)
                              (value-number->get y)
                            0)))
                  (or (< (realpart x1) (realpart y1))
                      (and (equal (realpart x1) (realpart y1))
                           (< (imagpart x1) (imagpart y1)))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-characterp ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee characterp)."
  (lift-value (value-case x :character))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-char-code ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee char-code)."
  (value-number (if (value-case x :character)
                    (char-code (value-character->get x))
                  0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-code-char ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee code-char)."
  (value-character (if (value-case-integer x)
                       (b* ((x-integer (value-integer->get x)))
                         (if (and (>= x-integer 0)
                                  (< x-integer 256))
                             (code-char x-integer)
                           (code-char 0)))
                     (code-char 0)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-stringp ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee stringp)."
  (lift-value (value-case x :string))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-coerce ((x valuep) (y valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee coerce)."
  (cond ((value-equiv y (value-symbol (lift-symbol 'list)))
         (if (value-case x :string)
             (lift-value (coerce (value-string->get x) 'list))
           (value-nil)))
        (t (value-string (coerce (make-character-list (lower-value x))
                                 'string))))
  :hooks (:fix)
  :prepwork
  ((defrule verify-guards-lemma
     (implies (character-listp x)
              (good-valuep x))
     :enable good-valuep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-symbolp ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee symbolp)."
  (lift-value (value-case x :symbol))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-symbol-package-name ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee symbol-package-name)."
  (value-string (if (value-case x :symbol)
                    (symbol-value->package (value-symbol->get x))
                  ""))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-symbol-name ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee symbol-name)."
  (value-string (if (value-case x :symbol)
                    (symbol-value->name (value-symbol->get x))
                  ""))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-intern-in-package-of-symbol ((x valuep)
                                          (y valuep)
                                          (packages package-listp))
  :returns (result maybe-valuep)
  :short "Evaluation semantics of @(tsee intern-in-package-of-symbol)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation semantics of this function depends on
     the package definition in the ACL2 environment.
     Thus, this meta-level function takes a list of packages as argument
     (meant to capture the package definitions in the ACL2 environment).")
   (xdoc::p
    "We find the package of the second symbol argument.
     If the package does not exist, it is an error,
     which we formalize by returning @('nil') instead of a value.
     Under suitable well-formedness conditions on
     ACL2 programs and evaluation states,
     the package should always exist,
     because only symbols from existing packages
     can be manipulated during evaluation.
     This will be proved formally eventually,
     but here we define a defensive evaluation semantics,
     which is common practice in programming language formalizations.")
   (xdoc::p
    "If a package is found,
     we check whether its import list includes a symbol
     whose name is the first string argument.
     If it does, that symbol is the result.
     Otherwise, we return a symbol consisting of
     the package name and the first string argument name."))
  (if (and (value-case x :string)
           (value-case y :symbol))
      (b* ((x-string (value-string->get x))
           (y-symbol (value-symbol->get y))
           (y-package (symbol-value->package y-symbol))
           (package? (package-lookup y-package packages))
           ((when (not package?)) nil)
           (imports (package->imports package?))
           (symbol? (import-lookup x-string imports))
           ((when symbol?) (value-symbol symbol?)))
        (value-symbol (make-symbol-value :package y-package :name x-string)))
    (value-nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-consp ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee consp)."
  (lift-value (value-case x :cons))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-cons ((x valuep) (y valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee cons)."
  (value-cons x y)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-car ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee car)."
  (cond ((value-case x :cons) (value-cons->car x))
        (t (value-nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-cdr ((x valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee cdr)."
  (cond ((value-case x :cons) (value-cons->cdr x))
        (t (value-nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-pkg-imports ((x valuep) (packages package-listp))
  :returns (result maybe-valuep)
  :short "Evaluation semantics of @(tsee pkg-imports)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation semantics of this function depends on
     the package definitions in the ACL2 environment.
     Thus, this meta-level function takes a list of packages as argument
     (meant to capture the package definitions in the ACL2 environment).")
   (xdoc::p
    "We find the package with the given name.
     If the package does not exist, it is an error,
     which we model by returning @('nil') here.
     The documentation of @(tsee pkg-imports) says that,
     when the string does not name a package known to ACL2
     (i.e. not in the environment),
     the result is (logically) undefined and evaluation fails to yield a value.
     Thus our modeling is consistent with this documentation.
     In practice, calling @(tsee pkg-imports) on a non-package string
     causes an ACL2 error."))
  (if (value-case x :string)
      (b* ((x-string (value-string->get x))
           (package? (package-lookup x-string packages))
           ((when (not package?)) nil)
           (imports (package->imports package?)))
        (value-list-of (value-symbol-list imports)))
    (value-nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-pkg-witness ((x valuep) (packages package-listp))
  :returns (result maybe-valuep)
  :short "Evaluation semantics of @(tsee pkg-witness)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation semantics of this function depends on
     the package definition in the ACL2 environment.
     Thus, this meta-level function takes a list of packages as argument
     (meant to capture the package definitions in the ACL2 environment).")
   (xdoc::p
    "We find the package with the given name.
     If the package does not exist, it is an error,
     which we model by returning @('nil') here.
     The documentation of @(tsee pkg-witness) says that,
     when the string does not name a package known to ACL2
     (i.e. not in the environment),
     evaluation yields an ACL2 hard error.
     Thus our modeling is consistent with this documentation.")
   (xdoc::p
    "If the package exists,
     we return the symbol with the package
     and the name of the ACL2 package witness,
     which is contained in the constant @('acl2::*pkg-witness-name*').")
   (xdoc::p
    "If the input is not a string,
     it is treated like the string @('\"ACL2\"')."))
  (b* ((x-string (if (value-case x :string)
                     (value-string->get x)
                   "ACL2"))
       (package? (package-lookup x-string packages))
       ((when (not package?)) nil))
    (value-symbol (make-symbol-value :package x-string
                                     :name acl2::*pkg-witness-name*)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-equal ((x valuep) (y valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee equal)."
  (lift-value (value-equiv x y))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-if ((x valuep) (y valuep) (z valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @(tsee if)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee if) is non-strict in the evaluation semantics.
     So we may not need this @('eval-if') function.
     Nonetheless, we have it return the prescribed value,
     given the argument values."))
  (if (value-equiv x (value-nil))
      (value-fix z)
    (value-fix y))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-bad-atom<= ((x valuep) (y valuep))
  :returns (result valuep)
  :short "Evaluation semantics of @('bad-atom<=')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard of this function requires bad atoms,
     which we do not model in our formalization.
     It looks like the raw Lisp code of this function returns @('nil').
     So we do the same here."))
  (declare (ignore x y))
  (value-nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitive-function-namep ((name symbol-valuep))
  :returns (yes/no booleanp)
  :short "Check if a symbol value is the name of a primitive function."
  (or (symbol-value-equiv name (lift-symbol 'acl2::acl2-numberp))
      (symbol-value-equiv name (lift-symbol 'common-lisp::rationalp))
      (symbol-value-equiv name (lift-symbol 'common-lisp::integerp))
      (symbol-value-equiv name (lift-symbol 'acl2::complex-rationalp))
      (symbol-value-equiv name (lift-symbol 'common-lisp::complex))
      (symbol-value-equiv name (lift-symbol 'common-lisp::realpart))
      (symbol-value-equiv name (lift-symbol 'common-lisp::imagpart))
      (symbol-value-equiv name (lift-symbol 'common-lisp::numerator))
      (symbol-value-equiv name (lift-symbol 'common-lisp::denominator))
      (symbol-value-equiv name (lift-symbol 'acl2::unary--))
      (symbol-value-equiv name (lift-symbol 'acl2::unary-/))
      (symbol-value-equiv name (lift-symbol 'acl2::binary-+))
      (symbol-value-equiv name (lift-symbol 'acl2::binary-*))
      (symbol-value-equiv name (lift-symbol 'common-lisp::<))
      (symbol-value-equiv name (lift-symbol 'common-lisp::characterp))
      (symbol-value-equiv name (lift-symbol 'common-lisp::char-code))
      (symbol-value-equiv name (lift-symbol 'common-lisp::code-char))
      (symbol-value-equiv name (lift-symbol 'common-lisp::stringp))
      (symbol-value-equiv name (lift-symbol 'common-lisp::coerce))
      (symbol-value-equiv name (lift-symbol 'common-lisp::symbolp))
      (symbol-value-equiv name (lift-symbol 'acl2::symbol-package-name))
      (symbol-value-equiv name (lift-symbol 'acl2::symbol-name))
      (symbol-value-equiv name (lift-symbol 'acl2::intern-in-package-of-symbol))
      (symbol-value-equiv name (lift-symbol 'common-lisp::consp))
      (symbol-value-equiv name (lift-symbol 'common-lisp::cons))
      (symbol-value-equiv name (lift-symbol 'common-lisp::car))
      (symbol-value-equiv name (lift-symbol 'common-lisp::cdr))
      (symbol-value-equiv name (lift-symbol 'acl2::pkg-imports))
      (symbol-value-equiv name (lift-symbol 'acl2::pkg-witness))
      (symbol-value-equiv name (lift-symbol 'common-lisp::equal))
      (symbol-value-equiv name (lift-symbol 'common-lisp::if))
      (symbol-value-equiv name (lift-symbol 'acl2::bad-atom<=)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primitive-function-arity ((name symbol-valuep))
  :guard (primitive-function-namep name)
  :returns (arity natp)
  :short "Arith of a primitive function."
  (cond
   ((symbol-value-equiv name (lift-symbol 'acl2::acl2-numberp)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::rationalp)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::integerp)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::complex-rationalp)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::complex)) 2)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::realpart)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::imagpart)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::numerator)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::denominator)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::unary--)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::unary-/)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::binary-+)) 2)
   ((symbol-value-equiv name (lift-symbol 'acl2::binary-*)) 2)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::<)) 2)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::characterp)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::char-code)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::code-char)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::stringp)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::coerce)) 2)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::symbolp)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::symbol-package-name)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::symbol-name)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::intern-in-package-of-symbol)) 2)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::consp)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::cons)) 2)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::car)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::cdr)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::pkg-imports)) 1)
   ((symbol-value-equiv name (lift-symbol 'acl2::pkg-witness)) 1)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::equal)) 2)
   ((symbol-value-equiv name (lift-symbol 'common-lisp::if)) 3)
   ((symbol-value-equiv name (lift-symbol 'acl2::bad-atom<=)) 2)
   (t (prog2$ (impossible) 0)))
  :hooks (:fix)
  :guard-hints (("Goal" :in-theory (enable primitive-function-namep))))
