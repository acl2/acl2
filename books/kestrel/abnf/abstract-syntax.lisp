; ABNF -- Abstract Syntax
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/nati" :dir :system)
(include-book "kestrel/utilities/define-sk" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "kestrel/utilities/osets" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "kestrel/utilities/system/event-form-lists" :dir :system)
(include-book "misc/seq" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/util/defval" :dir :system)

(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (abnf)
  :short "Abstract syntax of ABNF."
  :long
  "<p>
   ABNF is a language to describe the concrete syntax of languages.
   Being itself a language,
   ABNF has its own concrete syntax, described in [RFC:4] using ABNF itself.
   To break the self-description circularity,
   we start by formalizing an abstract syntax of ABNF,
   based on an inspection of the concrete syntax in [RFC:4].
   The ABNF abstract syntax abstracts away from the ABNF concrete syntax
   things that are not relevant to the ABNF @(see semantics),
   such as blank space and comments,
   as well as certain restrictions that are not needed to define the semantics.
   </p>"
  :order-subtopics t)

(fty::defprod rulename
  :parents (abstract-syntax)
  :short "Rule names in the abstract syntax."
  :long
  "<p>
   In the abstract syntax,
   we use character strings
   for the rule names described in [RFC:2.1]
   and by the rule @('rulename') in [RFC:4].
   We abstract away the restrictions on the characters allowed in rule names,
   which [RFC:4] requires to start with a letter
   and only use letters, digits, and dashes;
   these are ACL2 characters.
   These restrictions are captured by the notion of
   <see topic='@(url rulename-wfp)'>well-formed rule names</see>,
   which also requires all the letters to be lowercase,
   as a normalized representation of rule names,
   which are case-insensitive [RFC:2.1].
   </p>"
  ((get acl2::string))
  :tag :rulename
  :layout :list
  :pred rulenamep)

(fty::defoption maybe-rulename
  rulename
  :parents (abstract-syntax)
  :short "Union of rule names and @('nil')."
  :pred maybe-rulenamep)

(define set-all-rulenamep ((set setp))
  :returns (yes/no booleanp)
  :parents (abstract-syntax)
  :short "Check if all the elements of a set are rule names."
  (or (empty set)
      (and (rulenamep (head set))
           (set-all-rulenamep (tail set))))
  :no-function t
  ///

  (defrule set-all-rulenamep-of-insert
    (equal (set-all-rulenamep (insert rulename rulenames))
           (and (rulenamep rulename)
                (set-all-rulenamep (sfix rulenames)))))

  (defrule set-all-rulenamep-of-union
    (equal (set-all-rulenamep (union rulenames1 rulenames2))
           (and (set-all-rulenamep (sfix rulenames1))
                (set-all-rulenamep (sfix rulenames2))))
    :induct (union rulenames1 rulenames2)
    :enable union)

  (defrule set-all-rulenamep-of-difference
    (implies (set-all-rulenamep rulenames1)
             (set-all-rulenamep (difference rulenames1 rulenames2)))
    :enable difference)

  (defrule rulenamep-of-head-when-set-all-rulenamep
    (implies (set-all-rulenamep rulenames)
             (equal (rulenamep (head rulenames))
                    (not (empty rulenames)))))

  (defrule rulenamep-of-tail-when-set-all-rulenamep
    (implies (set-all-rulenamep rulenames)
             (set-all-rulenamep (tail rulenames))))

  (defrule rulenamep-when-member-of-set-all-rulenamep
    (implies (and (in rulename rulenames)
                  (set-all-rulenamep rulenames))
             (rulenamep rulename))))

(define rulename-setp (x)
  :returns (yes/no booleanp)
  :parents (abstract-syntax)
  :short "Recognize finite sets of rule names."
  (and (setp x)
       (set-all-rulenamep x))
  :no-function t
  ///

  (defrule setp-when-rulename-setp
    (implies (rulename-setp rulenames)
             (setp rulenames)))

  (defrule rulename-setp-of-insert
    (equal (rulename-setp (insert rulename rulenames))
           (and (rulenamep rulename)
                (rulename-setp (sfix rulenames)))))

  (defrule rulename-setp-of-union
    (equal (rulename-setp (union rulenames1 rulenames2))
           (and (rulename-setp (sfix rulenames1))
                (rulename-setp (sfix rulenames2)))))

  (defrule rulename-setp-of-difference
    (implies (rulename-setp rulenames1)
             (rulename-setp (difference rulenames1 rulenames2))))

  (defrule rulenamep-of-head-when-rulename-setp
    (implies (rulename-setp rulenames)
             (equal (rulenamep (head rulenames))
                    (not (empty rulenames)))))

  (defrule rulenamep-of-tail-when-rulename-setp
    (implies (rulename-setp rulenames)
             (rulename-setp (tail rulenames))))

  (defrule rulenamep-when-member-of-rulename-setp
    (implies (and (in rulename rulenames)
                  (rulename-setp rulenames))
             (rulenamep rulename))))

(fty::deftagsum num-val
  :parents (abstract-syntax)
  :short "Numeric value notations in the abstract syntax."
  :long
  "<p>
   In the abstract syntax,
   we use lists of natural numbers
   for the numeric value notations described in [RFC:2.3],
   and pairs of natural numbers
   for the value range alternatives described in [RFC:3.4];
   both notations are described by the rule @('num-val') (and sub-rules)
   in [RFC:4].
   We abstract away the radix notations @('%b'), @('%d'), and @('%x').
   We also abstract away the restriction
   that lists of natural numbers be non-empty.
   This restriction is captured by the notion of
   <see topic='@(url num-val-wfp)'>well-formed numeric value notations</see>,
   which also requires that the minimum of a range does not exceed the maximum.
   </p>"
  (:direct ((get nat-list)))
  (:range ((min nat)
           (max nat))))

(fty::deftagsum char-val
  :parents (abstract-syntax)
  :short "Character value notations in the abstract syntax."
  :long
  "<p>
   In the abstract syntax,
   we use character strings
   for the literal text strings described in [RFC:2.3]
   and by the rule @('char-val') (and sub-rules) in [RFC:4].
   We tag strings with an indication of their case sensitivity,
   corresponding to the @('%s') and @('%i') notations.
   We abstract away the restriction
   that quoted strings include only certain characters
   (which all are ACL2 characters).
   This restriction is captured by the notion of
   <see topic='@(url char-val-wfp)'>well-formed character value notations</see>.
   </p>"
  (:sensitive ((get acl2::string)))
  (:insensitive ((get acl2::string))))

(fty::defprod prose-val
  :parents (abstract-syntax)
  :short "Prose value notations in the abstract syntax."
  :long
  "<p>
   In the abstract syntax,
   we use character strings
   for the bracketed prose described by the rule @('prose-val') in [RFC:4].
   We abstract away the restriction
   that the prose include only certain characters
   (which all are ACL2 characters).
   This restriction is captured by the notion of
   <see topic='@(url prose-val-wfp)'>well-formed prose value notations</see>.
   </p>"
  ((get acl2::string))
  :tag :prose
  :layout :list)

(fty::defprod repeat-range
  :parents (abstract-syntax)
  :short "Repetition ranges in the abstract syntax."
  :long
  "<p>
   In the abstract syntax,
   for the repetition notation described in [RFC:3.6] and [RFC:3.7]
   and by rule @('repeat') in [RFC:4],
   we use pairs of natural numbers and natural numbers plus infinity.
   A specific repetition [RFC:3.7] is abstracted
   to a variable repetition [RFC:3.6] with the same minimum and maximum.
   A repetition with a missing lower bound is abstracted
   to one with the default (i.e. 0) as lower bound.
   A repetition with a missing upper bound is abstracted
   to one with the default (i.e. infinity) as explicit upper bound.
   The notion of
   <see topic='@(url repeat-range-wfp)'>well-formed repetition ranges</see>
   requires the minimum not to exceed the maximum.
   </p>"
  ((min nat)
   (max nati))
  :tag :repeat
  :layout :list
  :pred repeat-rangep)

(fty::deftypes alt/conc/rep/elem

  (fty::deflist alternation
    :parents (abstract-syntax)
    :short "Alternations in the abstract syntax."
    :long
    "<p>
     In the abstract syntax,
     for the alternatives described in [RFC:3.2]
     and by rule @('alternation') in [RFC:4],
     we use true lists of @(see concatenation)s.
     We abstract away comments and blank space.
     We also abstract away the restriction that
     there be at least one alternation.
     This restriction is captured by the notion of
     <see topic='@(url alternation-wfp)'>well-formed alternations</see>.
     </p>"
    :elt-type concatenation
    :true-listp t
    :pred alternationp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist concatenation
    :parents (abstract-syntax)
    :short "Concatenations in the abstract syntax."
    :long
    "<p>
     In the abstract syntax,
     for the concatenations described in [RFC:3.1]
     and by rule @('concatenation') in [RFC:4],
     we use true lists of @(see repetition)s.
     We abstract away comments and blank space.
     We also abstract away the restriction that
     there be at least one repetition.
     This restriction is captured by the notion of
     <see topic='@(url concatenation-wfp)'>well-formed concatenations</see>.
     </p>"
    :elt-type repetition
    :true-listp t
    :elementp-of-nil nil
    :pred concatenationp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod repetition
    :parents (abstract-syntax)
    :short "Repetitions in the abstract syntax."
    :long
    "<p>
     In the abstract syntax,
     for the repetitions described in [RFC:3.6] and [RFC:3.7]
     and by rule @('repetition') in [RFC:4],
     we use pairs consisting of repetition ranges and elements.
     A repetition with a missing repetition range is abstracted
     to one with a repetition range from 1 to 1.
     </p>"
    ((range repeat-range)
     (element element))
    :tag :repetition
    :layout :list
    :pred repetitionp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deftagsum element
    :parents (abstract-syntax)
    :short "Elements in the abstract syntax."
    :long
    "<p>
     In the abstract syntax,
     an element (of a @(see repetition))
     is defined in accordance with rule @('element') in [RFC:4].
     </p>"
    (:rulename ((get rulename)))
    (:group ((get alternation)))
    (:option ((get alternation)))
    (:char-val ((get char-val)))
    (:num-val ((get num-val)))
    (:prose-val ((get prose-val)))
    :pred elementp
    :measure (two-nats-measure (acl2-count x) 0)))

(fty::defprod rule
  :parents (abstract-syntax)
  :short "Rules in the abstract syntax."
  :long
  "<p>
   In the abstract syntax,
   we formalize a rule as consisting of
   a rule name,
   an indication of whether the rule provides incremental alternatives
   [RFC:3.3],
   and an alternation that defines the rule.
   This corresponds to rule @('rule') in [RFC:4],
   abstracting away comments and blank space.
   </p>"
  ((name rulename)
   (incremental bool)
   (definiens alternation))
  :tag :rule
  :layout :list
  :pred rulep)

(fty::defoption maybe-rule
  rule
  :parents (abstract-syntax)
  :short "Union of rules and @('nil')."
  :pred maybe-rulep)

(fty::deflist rulelist
  :parents (abstract-syntax)
  :short "Lists of rules in the abstract syntax."
  :long
  "<p>
   In the abstract syntax,
   we use true lists of rules.
   This corresponds to @('rulelist') in [RFC:4],
   abstracting away comments and blank space.
   </p>"
  :elt-type rule
  :true-listp t
  :elementp-of-nil nil
  :pred rulelistp)

(defxdoc grammar
  :parents (abstract-syntax)
  :short "An ABNF grammar is
          a <see topic='@(url rulelist)'>list of rules</see>."
  :long
  "<p>
   Unlike the typical notion of formal grammar in textbooks,
   ABNF does not include an explicit notion of axiom (or start symbol).
   An ABNF grammar is just a list of rules.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ convenience-constructors
  :parents (abstract-syntax)
  :short "Utilities to conveniently construct abstract syntactic entities."
  :long
  "<p>
   These functions and macros have short and evocative names,
   to support the concise and readable construction of (constituents of) rules
   in the abstract syntax.
   </p>
   <p>
   These functions and macros are used only to define
   the core rules [RFC:B] and the concrete syntax rules [RFC:4].
   Thus, these function and macros only need to handle
   the constructs used in those rules, not all possible constructs.
   </p>"
  :order-subtopics t)

(defsection %.
  :parents (convenience-constructors)
  :short "Construct a direct numeric value notation element
          from a variable number of numbers."
  :long
  "<p>
   The name of this macro is inspired by
   the ABNF notation @('%Rn1.n2. ...'),
   where @('R') is the letter for the radix
   and @('n1'), @('n2'), ... are numbers in base @('R'):
   the name of this macro has the @('%') and the @('.') of that notation.
   </p>
   @(def %.)"

  (defmacro %. (&rest numbers)
    `(%.-fn (list ,@numbers)))

  (define %.-fn ((nats nat-listp))
    :returns (element elementp)
    (element-num-val (num-val-direct nats))
    :no-function t))

(define %- ((min natp) (max natp))
  :returns (element elementp)
  :parents (convenience-constructors)
  :short "Construct a range numeric value notation element
          from a minimum and a maximum."
  :long
  "<p>
   The name of this function is inspired by
   the ABNF notation @('%Rmin-max'),
   where @('R') is the letter for the radix
   and @('min') and @('max') are numbers in base @('R'):
   the name of this function has the @('%') and the @('-') of that notation.
   </p>"
  (element-num-val (num-val-range min max))
  :no-function t)

(define <> ((charstring acl2::stringp))
  :returns (element elementp)
  :parents (convenience-constructors)
  :short "Construct a prose value notation element from a character string."
  :long
  "<p>
   The name of this function is inspired by
   the ABNF notation @('<...>'),
   where the brackets form the name of this function.
   </p>"
  (element-prose-val (prose-val charstring))
  :no-function t)

(define element/rulename-p (x)
  :returns (yes/no booleanp)
  :parents (convenience-constructors)
  :short "Recognize elements and rule names."
  :long
  "<p>
   Note that elements and rule names are disjoint.
   </p>"
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
  :parents (convenience-constructors)
  :short "Construct a repetition of zero or more instances of an element."
  :long
  "<p>
   If a rule name is supplied, it is promoted to an element.
   </p>
   <p>
   The name of this function is inspired by the ABNF notation @('*').
   </p>"
  (b* ((element (if (elementp x)
                    x
                  (element-rulename x)))
       (range (make-repeat-range :min 0 :max (nati-infinity))))
    (make-repetition :range range :element element))
  :guard-hints (("Goal" :in-theory (enable element/rulename-p)))
  :no-function t)

(define 1*_ ((x element/rulename-p))
  :returns (repetition repetitionp)
  :parents (convenience-constructors)
  :short "Construct a repetition of one or more instances of an element."
  :long
  "<p>
   If a rule name is supplied, it is promoted to an element.
   </p>
   <p>
   The name of this function is inspired by the ABNF notation @('1*').
   </p>"
  (b* ((element (if (elementp x)
                    x
                  (element-rulename x)))
       (range (make-repeat-range :min 1 :max (nati-infinity))))
    (make-repetition :range range :element element))
  :guard-hints (("Goal" :in-theory (enable element/rulename-p)))
  :no-function t)

(define repetition/element/rulename/charstring-p (x)
  :returns (yes/no booleanp)
  :parents (convenience-constructors)
  :short "Recognize repetitions, elements, rule names, and character strings."
  :long
  "<p>
   Note that these are pairwise disjoint.
   </p>"
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
  :parents (convenience-constructors)
  :short "Recognize true lists of
          repetitions, elements, rule names, and character strings."
  :true-listp t
  :elementp-of-nil nil)

(defsection /_
  :parents (convenience-constructors)
  :short "Construct a concatenation from a variable number of repetitions."
  :long
  "<p>
   If an element is supplied,
   it is promoted to a repetition of one instance of the element.
   If a rule name is supplied,
   it is promoted first to a rule element
   and then to a repetition of one instance of that element.
   If a character string is supplied,
   it is promoted first to an insensitive character value notation element
   and then to a repetition of one instance of that element.
   </p>
   <p>
   The name of this macro is inspired by the fact that
   the concatenations of an alternation are separated by @('/') in ABNF:
   when writing a sequence of concatenations (i.e. when writing an alternation)
   with this macro,
   the resulting sequence will have a @('/') separating the concatenations
   (plus an extra @('/') at the beginning).
   See the <see topic='@(url core-rules)'>core rules</see>
   and the <see topic='@(url concrete-syntax-rules)'>concrete syntax rules</see>
   for examples.
   </p>
   @(def /_)"

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
    :guard-hints (("Goal"
                   :in-theory
                   (enable repetition/element/rulename/charstring-p)))
    :no-function t))

(defsection !_
  :parents (convenience-constructors)
  :short "Construct a group from a variable number of concatenations."
  :long
  "<p>
   The concatenations are assembled into an alternation,
   which is the immediate constituent of a group.
   </p>
   @(def !_)"

  (defmacro !_ (&rest concatenations)
    `(!_-fn (list ,@concatenations)))

  (define !_-fn ((alternation alternationp))
    :returns (element elementp)
    (element-group alternation)
    :no-function t))

(defsection ?_
  :parents (convenience-constructors)
  :short "Construct an option from a variable number of concatenations."
  :long
  "<p>
   The concatenations are assembled into an alternation,
   which is the immediate constituent of a option.
   </p>
   @(def ?_)"

  (defmacro ?_ (&rest concatenations)
    `(?_-fn (list ,@concatenations)))

  (define ?_-fn ((alternation alternationp))
    :returns (element elementp)
    (element-option alternation)
    :no-function t))

(defsection =_
  :parents (convenience-constructors)
  :short "Construct a non-incremental rule from
          a rule name and a variable number of concatenations."
  :long
  "<p>
   The name of this macro is inspired by
   the ABNF notation @('=') for defining non-incremental rules.
   </p>
   @(def =_)"

  (defmacro =_ (rulename &rest concatenations)
    `(=_-fn ,rulename (list ,@concatenations)))

  (define =_-fn ((rulename rulenamep) (alternation alternationp))
    :returns (rule rulep)
    (make-rule :name (rulename-fix rulename)
               :incremental nil
               :definiens (alternation-fix alternation))
    :no-function t))

(defsection =/_
  :parents (convenience-constructors)
  :short "Construct an incremental rule from
          a rule name and a variable number of concatenations."
  :long
  "<p>
   The name of this macro is inspired by
   the ABNF notation @('=/') for defining incremental rules.
   </p>
   @(def =/_)"

  (defmacro =/_ (rulename &rest concatenations)
    `(=/_-fn ,rulename (list ,@concatenations)))

  (define =/_-fn ((rulename rulenamep) (alternation alternationp))
    :returns (rule rulep)
    (make-rule :name (rulename-fix rulename)
               :incremental t
               :definiens (alternation-fix alternation))
    :no-function t))

(defsection def-rule-const
  :parents (convenience-constructors)
  :short "Introduce an ACL2 constant for a (non-incremental) rule."
  :long
  "<p>
   The @('name') argument must be a valid constant name.
   The @('name') argument is followed by
   a variable number of forms that must evaluate to concatenations,
   whose list is the alternation that is the definiens of the rule.
   The name of the constant that defines the rule is obtained from @('name')
   by inserting @('rule_') just after the starting @('*').
   </p>
   @(def def-rule-const)"

  (defmacro def-rule-const (name &rest concatenation-forms)
    `(make-event (def-rule-const-fn ',name ',concatenation-forms)))

  (define def-rule-const-fn ((name legal-constantp)
                             (concatenation-forms pseudo-event-form-listp))
    :returns (const-event pseudo-event-formp)
    :prepwork ((program))
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
