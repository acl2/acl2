; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "abstract-syntax")

(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ convenience-constructors
  :parents (abstract-syntax)
  :short "Utilities to conveniently construct abstract syntactic entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "These functions and macros have short and evocative names,
     to support the concise and readable construction of (constituents of) rules
     in the abstract syntax.")
   (xdoc::p
    "These functions and macros are used only to define
     the core rules [RFC:B] and the concrete syntax rules [RFC:4].
     Thus, these function and macros only need to handle
     the constructs used in those rules, not all possible constructs."))
  :order-subtopics t
  :default-parent t)

(defsection %.
  :short "Construct a direct numeric value notation element
          from a variable number of numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of this macro is inspired by
     the ABNF notation @('%Rn1.n2. ...'),
     where @('R') is the letter for the radix
     and @('n1'), @('n2'), ... are numbers in base @('R'):
     the name of this macro has the @('%') and the @('.') of that notation.")
   (xdoc::@def "%."))

  (defmacro %. (&rest numbers)
    `(%.-fn (list ,@numbers)))

  (define %.-fn ((nats nat-listp))
    :returns (element elementp)
    (element-num-val (num-val-direct nats))
    :hooks (:fix)
    :no-function t))

(define %- ((min natp) (max natp))
  :returns (element elementp)
  :short "Construct a range numeric value notation element
          from a minimum and a maximum."
  :long
  (xdoc::topstring-p
   "The name of this function is inspired by
    the ABNF notation @('%Rmin-max'),
    where @('R') is the letter for the radix
    and @('min') and @('max') are numbers in base @('R'):
    the name of this function has the @('%') and the @('-') of that notation.")
  (element-num-val (num-val-range min max))
  :hooks (:fix)
  :no-function t)

(define <> ((charstring acl2::stringp))
  :returns (element elementp)
  :short "Construct a prose value notation element from a character string."
  :long
  (xdoc::topstring-p
   "The name of this function is inspired by
    the ABNF notation @('<...>'),
    where the brackets form the name of this function.")
  (element-prose-val (prose-val charstring))
  :hooks (:fix)
  :no-function t)

(define element/rulename-p (x)
  :returns (yes/no booleanp)
  :short "Recognize elements and rule names."
  :long
  (xdoc::topstring-p
   "Note that elements and rule names are disjoint.")
  (or (elementp x)
      (rulenamep x))
  :no-function t
  ///

  (defruled disjoint-element/rulename
    (not (and (elementp x)
              (rulenamep x)))
    :enable (elementp rulenamep)))

(define *_ ((x element/rulename-p))
  :returns (repetition repetitionp)
  :short "Construct a repetition of zero or more instances of an element."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a rule name is supplied, it is promoted to an element.")
   (xdoc::p
    "The name of this function is inspired by the ABNF notation @('*')."))
  (b* ((element (if (elementp x)
                    x
                  (element-rulename x)))
       (range (make-repeat-range :min 0 :max (nati-infinity))))
    (make-repetition :range range :element element))
  :hooks (:fix)
  :no-function t
  :guard-hints (("Goal" :in-theory (enable element/rulename-p))))

(define 1*_ ((x element/rulename-p))
  :returns (repetition repetitionp)
  :short "Construct a repetition of one or more instances of an element."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a rule name is supplied, it is promoted to an element.")
   (xdoc::p
    "The name of this function is inspired by the ABNF notation @('1*')."))
  (b* ((element (if (elementp x)
                    x
                  (element-rulename x)))
       (range (make-repeat-range :min 1 :max (nati-infinity))))
    (make-repetition :range range :element element))
  :hooks (:fix)
  :no-function t
  :guard-hints (("Goal" :in-theory (enable element/rulename-p))))

(define repetition/element/rulename/charstring-p (x)
  :returns (yes/no booleanp)
  :short "Recognize repetitions, elements, rule names, and character strings."
  :long
  (xdoc::topstring-p
   "Note that these are pairwise disjoint.")
  (or (repetitionp x)
      (elementp x)
      (rulenamep x)
      (acl2::stringp x))
  :no-function t
  ///

  (defruled disjoint-repetition/element
    (not (and (repetitionp x)
              (elementp x)))
    :cases ((equal (car x) :repetition))
    :enable (repetitionp elementp))

  (defruled disjoint-repetition/rulename
    (not (and (repetitionp x)
              (rulenamep x)))
    :enable (repetitionp rulenamep))

  (defruled disjoint-repetition/charstring
    (not (and (repetitionp x)
              (acl2::stringp x))))

  (defruled disjoint-element/rulename
    (not (and (elementp x)
              (rulenamep x))))

  (defruled disjoint-element/charstring
    (not (and (elementp x)
              (acl2::stringp x))))

  (defruled disjoint-rulename/charstring
    (not (and (rulenamep x)
              (acl2::stringp x)))))

(std::deflist repetition/element/rulename/charstring-listp (x)
  (repetition/element/rulename/charstring-p x)
  :short "Recognize true lists of
          repetitions, elements, rule names, and character strings."
  :true-listp t
  :elementp-of-nil nil)

(defsection /_
  :short "Construct a concatenation from a variable number of repetitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "If an element is supplied,
     it is promoted to a repetition of one instance of the element.
     If a rule name is supplied,
     it is promoted first to a rule element
     and then to a repetition of one instance of that element.
     If a character string is supplied,
     it is promoted first to a case-insensitive character value notation element
     and then to a repetition of one instance of that element.")
   (xdoc::p
    "The name of this macro is inspired by the fact that
     the concatenations of an alternation are separated by @('/') in ABNF:
     when writing a sequence of concatenations
     (i.e. when writing an alternation)
     with this macro,
     the resulting sequence will have a @('/') separating the concatenations
     (plus an extra @('/') at the beginning).
     See the "
    (xdoc::seetopic "core-rules" "core rules")
    " and the "
    (xdoc::seetopic "concrete-syntax-rules" "concrete syntax rules")
    ".")
   (xdoc::@def "/_"))

  (defmacro /_ (&rest xs)
    `(/_-fn (list ,@xs)))

  (define /_-fn ((xs repetition/element/rulename/charstring-listp))
    :returns (concatenation concatenationp)
    (cond ((endp xs) nil)
          (t (b* ((x (car xs))
                  (range1 (make-repeat-range :min 1 :max (nati-finite 1)))
                  (repetition
                   (cond ((elementp x)
                          (make-repetition :range range1 :element x))
                         ((rulenamep x)
                          (make-repetition :range range1
                                           :element (element-rulename x)))
                         ((acl2::stringp x)
                          (make-repetition :range range1
                                           :element (element-char-val
                                                     (char-val-insensitive x))))
                         (t (repetition-fix x)))))
               (cons repetition (/_-fn (cdr xs))))))
    :hooks (:fix)
    :no-function t
    :guard-hints (("Goal"
                   :in-theory
                   (enable repetition/element/rulename/charstring-p)))))

(defsection !_
  :short "Construct a group from a variable number of concatenations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The concatenations are assembled into an alternation,
     which is the immediate constituent of a group.")
   (xdoc::@def "!_"))

  (defmacro !_ (&rest concatenations)
    `(!_-fn (list ,@concatenations)))

  (define !_-fn ((alternation alternationp))
    :returns (element elementp)
    (element-group alternation)
    :hooks (:fix)
    :no-function t))

(defsection ?_
  :short "Construct an option from a variable number of concatenations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The concatenations are assembled into an alternation,
     which is the immediate constituent of a option.")
   (xdoc::@def "?_"))

  (defmacro ?_ (&rest concatenations)
    `(?_-fn (list ,@concatenations)))

  (define ?_-fn ((alternation alternationp))
    :returns (element elementp)
    (element-option alternation)
    :hooks (:fix)
    :no-function t))

(defsection =_
  :short "Construct a non-incremental rule from
          a rule name and a variable number of concatenations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of this macro is inspired by
     the ABNF notation @('=') for defining non-incremental rules.")
   (xdoc::@def "=_"))

  (defmacro =_ (rulename &rest concatenations)
    `(=_-fn ,rulename (list ,@concatenations)))

  (define =_-fn ((rulename rulenamep) (alternation alternationp))
    :returns (rule rulep)
    (make-rule :name (rulename-fix rulename)
               :incremental nil
               :definiens (alternation-fix alternation))
    :hooks (:fix)
    :no-function t))

(defsection =/_
  :short "Construct an incremental rule from
          a rule name and a variable number of concatenations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of this macro is inspired by
     the ABNF notation @('=/') for defining incremental rules.")
   (xdoc::@def "=/_"))

  (defmacro =/_ (rulename &rest concatenations)
    `(=/_-fn ,rulename (list ,@concatenations)))

  (define =/_-fn ((rulename rulenamep) (alternation alternationp))
    :returns (rule rulep)
    (make-rule :name (rulename-fix rulename)
               :incremental t
               :definiens (alternation-fix alternation))
    :hooks (:fix)
    :no-function t))

(defsection def-rule-const
  :short "Introduce an ACL2 constant for a (non-incremental) rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('name') argument must be a valid constant name.
     The @('name') argument is followed by
     a variable number of forms that must evaluate to concatenations,
     whose list is the alternation that is the definiens of the rule.
     The name of the constant that defines the rule is obtained from @('name')
     by inserting @('rule_') just after the starting @('*').")
   (xdoc::@def "def-rule-const"))

  (defmacro def-rule-const (name &rest concatenation-forms)
    `(make-event (def-rule-const-fn ',name ',concatenation-forms)))

  (define def-rule-const-fn ((name legal-constantp)
                             (concatenation-forms pseudo-event-form-listp))
    :returns (const-event pseudo-event-formp)
    (b* ((name-string (symbol-name name))
         (name-chars (explode name-string))
         (name-chars-without-1st-* (cdr name-chars))
         (name-string-without-1st-* (implode name-chars-without-1st-*))
         (const-string (concatenate 'acl2::string
                                    "*RULE_"
                                    name-string-without-1st-*))
         (const-name (intern-in-package-of-symbol const-string name)))
      `(defval ,const-name (=_ ,name ,@concatenation-forms)))
    :no-function t))
