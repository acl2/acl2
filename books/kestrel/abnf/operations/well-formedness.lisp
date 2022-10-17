; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../notation/semantics")

(include-book "kestrel/std/strings/letter-chars" :dir :system)
(include-book "kestrel/std/strings/letter-digit-dash-chars" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "kestrel/utilities/strings/chars-codes" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ well-formedness
  :parents (operations)
  :short "Well-formed ABNF grammars."
  :long
  (xdoc::topstring-p
   "Certain ABNF @(see grammar)s are valid according to the "
   (xdoc::seetopic "abstract-syntax" "formalized abstract syntax")
   ", but (include parts that) violate certain conditions that are
   either required by the concrete syntax defined in [RFC:4]
   or otherwise reasonably justifiable.
   These additional conditions are captured by the notion of well-formedness.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulename-wfp ((rulename rulenamep))
  :returns (yes/no booleanp)
  :short "A rule name must start with a lowercase letter (and thus not be empty)
          and contain only lowercase letters, numbers, and dashes."
  :long
  (xdoc::topstring-p
   "Aside from all letters being lowercase,
    these constraints are required by the rule @('rulename') in [RFC:4].
    The constraint that all letters be lowercase
    provides a normalized representation of rule names,
    which are case-insensitive [RFC:2.1].")
  (b* ((charstring (rulename->get rulename))
       (chars (explode charstring)))
    (and (consp chars)
         (str::letter-char-p (car chars))
         (str::letter/digit/dash-charlist-p (cdr chars))
         (equal (str::downcase-charlist chars) chars)))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define num-val-wfp ((num-val num-val-p))
  :returns (yes/no booleanp)
  :short "A direct numeric value notation is well-formed iff
          it consists of at least one number;
          a range numeric value notation is well-formed iff
          the minimum does not exceed the maximum."
  :long
  (xdoc::topstring-p
   "The condition on direct numeric value notations is required
    by the rules @('bin-val'), @('dec-val'), and @('hex-val') in [RFC:4].
    The condition on range numeric value notations is reasonably justifiable
    because no number exists in a range whose minimum exceeds the maximum;
    formally, no tree matches a malformed range numeric value notation.")
  (num-val-case num-val
                :direct (consp num-val.get)
                :range (<= num-val.min num-val.max))
  :no-function t
  ///

  (defruled justification-for-num-val-range-wfp
    (implies (and (num-val-case num-val :range)
                  (> (num-val-range->min num-val)
                     (num-val-range->max num-val)))
             (not (tree-match-num-val-p tree num-val)))
    :enable tree-match-num-val-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-val-wfp ((char-val char-val-p))
  :returns (yes/no booleanp)
  :short "A character value notation is well-formed iff
          it consists of only non-control ASCII characters,
          except for the double quote character."
  :long
  (xdoc::topstring-p
   "These allowed characters are consistent with
    the rule @('quoted-string') in [RFC:4].
    That rule allows empty strings,
    so the rule @('char-val') in [RFC:4] also allows empty strings.
    An empty character value notation
    may play the role of the empty sequence of symbols
    (often denoted by @($\\epsilon$) in textbooks).")
  (b* ((allowed-chars (nats=>chars (append (integers-from-to #x20 #x21)
                                           (integers-from-to #x23 #x7e)))))
    (char-val-case char-val
                   :sensitive (subsetp (explode char-val.get)
                                       allowed-chars)
                   :insensitive (subsetp (explode char-val.get)
                                         allowed-chars)))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prose-val-wfp ((prose-val prose-val-p))
  :returns (yes/no booleanp)
  :short "A prose value notation is well-formed iff
          it consists of only non-control ASCII characters,
          except for the right angle bracket character."
  :long
  (xdoc::topstring-p
   "These allowed characters are consistent with
    the rule @('prose-val') in [RFC:4].
    That rule allows empty bracketed strings.
    Normally prose should be non-empty (so it provides some description),
    but in the formal semantics any tree matches prose,
    so the emptiness of prose makes no difference in the formal semantics.")
  (b* ((allowed-chars (nats=>chars (append (integers-from-to #x20 #x3d)
                                           (integers-from-to #x3f #x7e)))))
    (subsetp (explode (prose-val->get prose-val))
             allowed-chars))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define repeat-range-wfp ((range repeat-rangep))
  :returns (yes/no booleanp)
  :short "A repetition range is well-formed iff
          the minimum does not exceed the maximum."
  :long
  (xdoc::topstring-p
   "This condition is reasonably justifiable because
    no number of repetitions exists in a range
    whose minimum exceeds the maximum.")
  (b* ((min (repeat-range->min range))
       (max (repeat-range->max range)))
    (or (nati-case max :infinity)
        (<= min (nati-finite->get max))))
  :no-function t
  ///

  (defruled justification-for-repeat-range-wfp
    (implies (and (nati-case (repeat-range->max range) :finite)
                  (> (repeat-range->min range)
                     (nati-finite->get (repeat-range->max range))))
             (not (numrep-match-repeat-range-p numrep range)))
    :enable numrep-match-repeat-range-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines alt/conc/rep/elem-wfp

  (define alternation-wfp ((alternation alternationp))
    :returns (yes/no booleanp)
    :short "An alternation is well-formed iff
            it is not empty and all its concatenations are well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "This non-emptiness condition
       is required by the rule @('alternation') in [RFC:4].
       The well-formedness condition on the concatenations is structural.")
     (xdoc::@def "alternation-wfp"))
    (and (consp alternation)
         (concatenation-list-wfp alternation))
    :measure (two-nats-measure (alternation-count alternation) 1)
    :no-function t)

  (define concatenation-list-wfp ((concatenations alternationp))
    :returns (yes/no booleanp)
    :short "Check if all the concatenations in a list of concatenations
            are well-formed."
    :long (xdoc::topstring-@def "concatenation-list-wfp")
    (or (endp concatenations)
        (and (concatenation-wfp (car concatenations))
             (concatenation-list-wfp (cdr concatenations))))
    :measure (two-nats-measure (alternation-count concatenations) 0)
    :no-function t)

  (define concatenation-wfp ((concatenation concatenationp))
    :returns (yes/no booleanp)
    :short "A concatenation is well-formed iff
            it is not empty and all its repetitions are well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "This non-emptiness condition
       is required by the rule @('concatenation') in [RFC:4].
       The well-formedness condition on the repetitions is structural.")
     (xdoc::@def "concatenation-wfp"))
    (and (consp concatenation)
         (repetition-list-wfp concatenation))
    :measure (two-nats-measure (concatenation-count concatenation) 1)
    :no-function t)

  (define repetition-list-wfp ((repetitions concatenationp))
    :returns (yes/no booleanp)
    :short "Check if all the repetitions in a list of repetitions
            are well-formed."
    :long (xdoc::topstring-@def "repetition-list-wfp")
    (or (endp repetitions)
        (and (repetition-wfp (car repetitions))
             (repetition-list-wfp (cdr repetitions))))
    :measure (two-nats-measure (concatenation-count repetitions) 0)
    :no-function t)

  (define repetition-wfp ((repetition repetitionp))
    :returns (yes/no booleanp)
    :short "A repetition is well-formed iff
            its repetition range and its element are well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "This condition is structural.")
     (xdoc::@def "repetition-wfp"))
    (and (repeat-range-wfp (repetition->range repetition))
         (element-wfp (repetition->element repetition)))
    :measure (two-nats-measure (repetition-count repetition) 1)
    :no-function t)

  (define element-wfp ((element elementp))
    :returns (yes/no booleanp)
    :short "An element is well-formed iff its constituents are well-formed."
    :long
    (xdoc::topstring
     (xdoc::p
      "This condition is structural.")
     (xdoc::@def "element-wfp"))
    (element-case element
                  :rulename (rulename-wfp element.get)
                  :group (alternation-wfp element.get)
                  :option (alternation-wfp element.get)
                  :char-val (char-val-wfp element.get)
                  :num-val (num-val-wfp element.get)
                  :prose-val (prose-val-wfp element.get))
    :measure (two-nats-measure (element-count element) 0)
    :no-function t)

  ///

  (std::deflist concatenation-list-wfp (x)
    (concatenation-wfp x)
    :guard (alternationp x)
    :elementp-of-nil nil)

  (std::deflist repetition-list-wfp (x)
    (repetition-wfp x)
    :guard (concatenationp x)
    :elementp-of-nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rule-wfp ((rule rulep))
  :returns (yes/no booleanp)
  :short "A rule is well-formed iff its name and definiens are well-formed."
  :long
  (xdoc::topstring-p
   "This condition is structural.")
  (and (rulename-wfp (rule->name rule))
       (alternation-wfp (rule->definiens rule)))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist rule-list-wfp (x)
  (rule-wfp x)
  :guard (rulelistp x)
  :short "Check if all the rules in a list of rules are well-formed."
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulelist-incremental-ok-p ((rules rulelistp))
  :returns (yes/no booleanp)
  :short "Check if incremental rules appear after
          non-incremental rules with the same names."
  :long
  (xdoc::topstring-p
   "An incremental rule may appear
    only if there is a preceding rule with the same name.
    A non-incremental rule may appear
    only if there is no preceding rule with the same name.")
  (rulelist-incremental-ok-p-aux nil rules)
  :no-function t

  :prepwork
  ((define rulelist-incremental-ok-p-aux ((previous-rules rulelistp)
                                          (next-rules rulelistp))
     :returns (yes/no booleanp)
     :parents (rulelist-incremental-ok-p)
     :short "Auxiliary function to define @(tsee rulelist-incremental-ok-p)."
     :long
     (xdoc::topstring-p
      "The rules in @('next-rules') are examined one after the other,
       and checked against the rules already examined,
       which are accumulated in @('previous-rules').")
     (or (endp next-rules)
         (and (iff (rule->incremental (car next-rules))
                   (lookup-rulename (rule->name (car next-rules))
                                    previous-rules))
              (rulelist-incremental-ok-p-aux (append previous-rules
                                                     (list (car next-rules)))
                                             (cdr next-rules))))
     :measure (len next-rules)
     :no-function t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulelist-wfp ((rules rulelistp))
  :returns (yes/no booleanp)
  :short "A rule list is well-formed iff
          all its rules are well-formed,
          there are no duplicate rules,
          and incremental rules follow non-incremental rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first condition is structural.
     The second condition is justifiable
     because duplicate rules are redundant.
     The third condition is reasonably implied by [RFC:3.3].")
   (xdoc::p
    "Non-emptiness is not required by the rule @('rulelist') in [RFC:4],
     which allows just @('(*c-wsp c-nl)') groups without @('rule')s."))
  (and (rule-list-wfp rules)
       (no-duplicatesp-equal rules)
       (rulelist-incremental-ok-p rules))
  :no-function t)
