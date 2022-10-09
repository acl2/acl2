; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/nati" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (abnf)
  :short "Abstract syntax of ABNF."
  :long
  (xdoc::topstring-p
   "ABNF is a language to describe the concrete syntax of languages.
    Being itself a language,
    ABNF has its own concrete syntax, described in [RFC:4] using ABNF itself.
    To break the self-description circularity,
    we start by formalizing an abstract syntax of ABNF,
    based on an inspection of the concrete syntax in [RFC:4].
    The ABNF abstract syntax abstracts away from the ABNF concrete syntax
    things that are not relevant to the ABNF @(see semantics),
    such as blank space and comments,
    as well as certain restrictions
    that are not needed to define the semantics.")
  :order-subtopics t
  :default-parent t)

(fty::defprod rulename
  :short "Fixtype of rule names."
  :long
  (xdoc::topstring-p
   "In the abstract syntax,
    we use character strings
    for the rule names described in [RFC:2.1]
    and by the rule @('rulename') in [RFC:4].
    We abstract away the restrictions on the characters allowed in rule names,
    which [RFC:4] requires to start with a letter
    and only use letters, digits, and dashes;
    these are ACL2 characters.
    These restrictions are captured by the notion of "
   (xdoc::seetopic "rulename-wfp" "well-formed rule names")
   ", which also requires all the letters to be lowercase,
    as a normalized representation of rule names,
    which are case-insensitive [RFC:2.1].")
  ((get acl2::string))
  :tag :rulename
  :layout :list
  :pred rulenamep)

(fty::defoption rulename-option
  rulename
  :short "Fixtype of rule names and @('nil')."
  :pred rulename-optionp)

(fty::defset rulename-set
  :elt-type rulename
  :elementp-of-nil nil
  :pred rulename-setp
  :fix rulename-sfix
  :equiv rulename-sequiv
  :short "Finite sets of rule names.")

(fty::deftagsum num-val
  :short "Fixtype of numeric value notations."
  :long
  (xdoc::topstring-p
   "In the abstract syntax,
    we use lists of natural numbers
    for the numeric value notations described in [RFC:2.3],
    and pairs of natural numbers
    for the value range alternatives described in [RFC:3.4];
    both notations are described by the rule @('num-val') (and sub-rules)
    in [RFC:4].
    We abstract away the radix notations @('%b'), @('%d'), and @('%x').
    We also abstract away the restriction
    that lists of natural numbers be non-empty.
    This restriction is captured by the notion of "
   (xdoc::seetopic "num-val-wfp" "well-formed numeric value notations")
   ", which also requires that the minimum of a range
    does not exceed the maximum.")
  (:direct ((get nat-list)))
  (:range ((min nat)
           (max nat))))

(fty::deftagsum char-val
  :short "Fixtype of character value notations."
  :long
  (xdoc::topstring-p
   "In the abstract syntax,
    we use character strings
    for the literal text strings described in [RFC:2.3]
    and by the rule @('char-val') (and sub-rules) in [RFC:4].
    We tag strings with an indication of their case sensitivity,
    corresponding to the @('%s') and @('%i') notations;
    the latter also abstract plain strings,
    i.e. strings without the @('%s') and @('%i') notations,
    which are equivalent to case-insensitive strings with the @('%i') notation.
    We abstract away the restriction
    that quoted strings include only certain characters
    (which all are ACL2 characters).
    This restriction is captured by the notion of "
   (xdoc::seetopic "char-val-wfp" "well-formed character value notations")
   ".")
  (:sensitive ((get acl2::string)))
  (:insensitive ((get acl2::string))))

(fty::defprod prose-val
  :short "Fixtype of prose value notations."
  :long
  (xdoc::topstring-p
   "In the abstract syntax,
    we use character strings
    for the bracketed prose described by the rule @('prose-val') in [RFC:4].
    We abstract away the restriction
    that the prose include only certain characters
    (which all are ACL2 characters).
    This restriction is captured by the notion of "
   (xdoc::seetopic "prose-val-wfp" "well-formed prose value notations")
   ".")
  ((get acl2::string))
  :tag :prose
  :layout :list)

(fty::defprod repeat-range
  :short "Fixtype of repetition ranges."
  :long
  (xdoc::topstring-p
   "In the abstract syntax,
    for the repetition notation described in [RFC:3.6] and [RFC:3.7]
    and by rule @('repeat') in [RFC:4],
    we use pairs of (i) natural numbers and (ii) natural numbers plus infinity.
    A specific repetition [RFC:3.7] is abstracted
    to a variable repetition [RFC:3.6] with the same minimum and maximum.
    A repetition with a missing lower bound is abstracted
    to one with the default (i.e. 0) as lower bound.
    A repetition with a missing upper bound is abstracted
    to one with the default (i.e. infinity) as explicit upper bound.
    The notion of "
   (xdoc::seetopic "repeat-range-wfp" "well-formed repetition ranges")
   " requires the minimum not to exceed the maximum.")
  ((min nat)
   (max nati))
  :tag :repeat
  :layout :list
  :pred repeat-rangep)

(fty::deftypes alt/conc/rep/elem

  (fty::deflist alternation
    :short "Fixtype of alternations."
    :long
    (xdoc::topstring-p
     "In the abstract syntax,
      for the alternatives described in [RFC:3.2]
      and by rule @('alternation') in [RFC:4],
      we use true lists of @(see concatenation)s.
      We abstract away comments and blank space.
      We also abstract away the restriction that
      there be at least one alternation.
      This restriction is captured by the notion of "
     (xdoc::seetopic "alternation-wfp" "well-formed alternations")
     ".")
    :elt-type concatenation
    :true-listp t
    :pred alternationp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist concatenation
    :short "Fixtype of concatenations."
    :long
    (xdoc::topstring-p
     "In the abstract syntax,
      for the concatenations described in [RFC:3.1]
      and by rule @('concatenation') in [RFC:4],
      we use true lists of @(see repetition)s.
      We abstract away comments and blank space.
      We also abstract away the restriction that
      there be at least one repetition.
      This restriction is captured by the notion of "
     (xdoc::seetopic "concatenation-wfp" "well-formed concatenations")
     ".")
    :elt-type repetition
    :true-listp t
    :elementp-of-nil nil
    :pred concatenationp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod repetition
    :short "Fixtype of repetitions."
    :long
    (xdoc::topstring-p
     "In the abstract syntax,
      for the repetitions described in [RFC:3.6] and [RFC:3.7]
      and by rule @('repetition') in [RFC:4],
      we use pairs consisting of repetition ranges and elements.
      A repetition with a missing repetition range is abstracted
      to one with a repetition range from 1 to 1.")
    ((range repeat-range)
     (element element))
    :tag :repetition
    :layout :list
    :pred repetitionp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deftagsum element
    :short "Fixtype of elements."
    :long
    (xdoc::topstring-p
     "In the abstract syntax,
      an element (of a @(see repetition))
      is defined in accordance with rule @('element') in [RFC:4].")
    (:rulename ((get rulename)))
    (:group ((get alternation)))
    (:option ((get alternation)))
    (:char-val ((get char-val)))
    (:num-val ((get num-val)))
    (:prose-val ((get prose-val)))
    :pred elementp
    :measure (two-nats-measure (acl2-count x) 0)))

(fty::defprod rule
  :short "Fixtype of rules."
  :long
  (xdoc::topstring-p
   "In the abstract syntax,
    we formalize a rule as consisting of
    a rule name,
    an indication of whether the rule provides incremental alternatives
    [RFC:3.3],
    and an alternation that defines the rule.
    This corresponds to rule @('rule') in [RFC:4],
    abstracting away comments and blank space.")
  ((name rulename)
   (incremental bool)
   (definiens alternation))
  :tag :rule
  :layout :list
  :pred rulep)

(fty::defoption maybe-rule
  rule
  :short "Fixtype of rules and @('nil')."
  :pred maybe-rulep)

(fty::deflist rulelist
  :short "Fixtype of lists of rules."
  :long
  (xdoc::topstring-p
   "In the abstract syntax,
    we use true lists of rules.
    This corresponds to @('rulelist') in [RFC:4],
    abstracting away comments and blank space.")
  :elt-type rule
  :true-listp t
  :elementp-of-nil nil
  :pred rulelistp)

(defxdoc grammar
  :short
  (xdoc::topstring
   "An ABNF grammar is a " (xdoc::seetopic "rulelist" "list of rules") ".")
  :long
  (xdoc::topstring-p
   "Unlike the typical notion of formal grammar in textbooks,
    ABNF does not include an explicit notion of axiom
    (or goal, or start symbol).
    An ABNF grammar is just a list of rules."))
