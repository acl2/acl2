; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "well-formedness")
(include-book "closure")
(include-book "in-terminal-set")
(include-book "ambiguity")

(include-book "../semantics")

(include-book "kestrel/std/strings/letter-chars" :dir :system)
(include-book "kestrel/std/strings/letter-digit-dash-chars" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "kestrel/utilities/osets" :dir :system)
(include-book "kestrel/utilities/strings/chars-codes" :dir :system)
(include-book "kestrel/fty/string-list-result" :dir :system)

(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))
(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations
  :parents (abnf)
  :short "Operations on ABNF grammars."
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ plugging
  :parents (operations)
  :short "Composition of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certain ABNF grammars are defined modularly.
     A ``module'' may not be "
    (xdoc::seetopic "closure" "closed")
    ", but when it is combined with other modules,
     the resulting grammar may be closed.")
   (xdoc::p
    "For example, the "
    (xdoc::seetopic "concrete-syntax-rules" "concrete syntax rules")
    " are not closed.
     But when they are combined with the "
    (xdoc::seetopic "core-rules" "core rules")
    ", the "
    (xdoc::seetopic "*all-concrete-syntax-rules*" "resulting rule list")
    " is closed.")
   (xdoc::p
    "As another example,
     the HTTP grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7230" "RFC 7230")
    " includes rules defined by prose value notations
     that refer to the URI grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc3986" "RFC 3968")
    ". The intended way to compose the two grammars is
     to replace the prose HTTP rules with the corresponding URI rules.")
   (xdoc::p
    "Here we define an operation to accomplish the kind of composition
    exemplified above.
    The operation ``plugs'' a rule list into another rule list,
    e.g. it plugs the core rules into the concrete syntax rules,
    and it plugs the URI rules into the HTTP rules."))
  :order-subtopics t)

(define rule-prosep ((rule rulep))
  :returns (yes/no booleanp)
  :parents (plugging)
  :short "Check if a rule has a single prose value notation as definiens."
  (b* ((alternation (rule->definiens rule)))
    (and (consp alternation)
         (not (consp (cdr alternation)))
         (b* ((concatenation (car alternation)))
           (and (consp concatenation)
                (not (consp (cdr concatenation)))
                (b* ((repetition (car concatenation))
                     (range (repetition->range repetition))
                     (element (repetition->element repetition)))
                  (and (equal range (repeat-range 1 (nati-finite 1)))
                       (element-case element :prose-val)))))))
  :no-function t)

(define remove-prose-rules ((rules1 rulelistp) (rules2 rulelistp))
  :returns (rules rulelistp)
  :parents (plugging)
  :short "Remove from a list of rules all the prose rules
          whose names have definitions in another list of rules."
  :long
  (xdoc::topstring-p
   "This is the first step of the "
   (xdoc::seetopic "plug-rules" "plugging operation")
   ". This step removes from @('rules1') all the prose rules
    whose names have definitions in @('rules2').")
  (cond ((endp rules1) nil)
        (t (b* ((rule (car rules1)))
             (and (mbt (rulep rule))
                  (if (and (rule-prosep rule)
                           (lookup-rulename (rule->name rule) rules2))
                      (remove-prose-rules (cdr rules1) rules2)
                    (cons rule (remove-prose-rules (cdr rules1) rules2)))))))
  :no-function t)

(define plug-rules ((rules1 rulelistp) (rules2 rulelistp))
  :returns (rules rulelistp)
  :parents (plugging)
  :short "Plug a list of rules into another list of rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "This plugs @('rules2') into @('rules1'), not vice versa.
     This choice is motivated by the fact that grammar rules
     are usually presented in a top-down manner,
     and so it seems more natural to have
     the ``plugged'' rules (e.g. HTTP)
     appear before the ``plugging'' rules (e.g. URI).")
   (xdoc::p
    "After removing from @('rules1') the prose rules
     whose names have definitions in @('rules2'),
     we find the rules in @('rules2') that transitively define
     rule names referenced but not defined
     in the remaining rules of @('rules1').
     We append the rules found after the remaining rules of @('rules1').")
   (xdoc::p
    "Thus, prose rules in @('rules1') are effectively replaced
     by corresponding rules in @('rules')
     (assuming that each prose rule removed from @('rules1')
     is the only rule in @('rules1') that defines its rule name).
     Besides replacing @('prose-rules') like this,
     the plugging operation may also provide definitions
     for rule names that are only referenced in @('rules1').")
   (xdoc::p
    "Prose rules in @('rules1')
     whose names do not have definitions in @('rules2')
     are not removed from @('rules1') and thus appear in the resulting rules.
     Similarly, rules referenced in @('rules1')
     but defined neither in @('rules1') nor in @('rules2')
     remain referenced but not defined in the resulting rules.
     These features allow multi-step plugging,
     i.e. @('rules2') is plugged into @('rules1'),
     then @('rules3') is plugged into the result of the previous operation,
     and so on."))
  (b* ((rules1 (remove-prose-rules rules1 rules2))
       (rules2 (trans-rules-of-names (difference
                                      (rulelist-called-rules rules1)
                                      (rulelist-defined-rules rules1))
                                     rules2)))
    (append rules1 rules2))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renaming
  :parents (operations)
  :short "Renaming of rules in ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is sometimes useful to systematically rename a rule in a grammar.")
   (xdoc::p
    "For example, the HTTP grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7230" "RFC 7230")
    " includes a rule @('uri-host') defined by a prose value notation
     that references the rule @('host') from the URI grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc3986" "RFC 3968")
    ". Prior to @(see plugging) the URI grammar rules
     into the HTTP grammar rules,
     the rule @('host') in the URI grammar rules
     should be renamed to @('uri-host')."))
  :order-subtopics t)

(defines alt/conc/rep/elem-rename-rule
  :verify-guards nil ; done below

  (define alternation-rename-rule ((alternation alternationp)
                                   (oldname rulenamep)
                                   (newname rulenamep))
    :returns (new-alternation alternationp)
    :parents (renaming)
    :short "Rename all the occurrences of a rule name in an alternation
            to a new rule name."
    :long (xdoc::topstring-@def "alternation-rename-rule")
    (cond ((endp alternation) nil)
          (t (cons (concatenation-rename-rule (car alternation)
                                              oldname newname)
                   (alternation-rename-rule (cdr alternation)
                                            oldname newname))))
    :measure (two-nats-measure (alternation-count alternation) 0)
    :no-function t)

  (define concatenation-rename-rule ((concatenation concatenationp)
                                     (oldname rulenamep)
                                     (newname rulenamep))
    :returns (new-concatenation concatenationp)
    :parents (renaming)
    :short "Rename all the occurrences of a rule name in a conatenation
            to a new rule name."
    :long (xdoc::topstring-@def "concatenation-rename-rule")
    (cond ((endp concatenation) nil)
          (t (cons (repetition-rename-rule (car concatenation)
                                           oldname newname)
                   (concatenation-rename-rule (cdr concatenation)
                                              oldname newname))))
    :measure (two-nats-measure (concatenation-count concatenation) 0)
    :no-function t)

  (define repetition-rename-rule ((repetition repetitionp)
                                  (oldname rulenamep)
                                  (newname rulenamep))
    :returns (new-repetition repetitionp)
    :parents (renaming)
    :short "Rename all the occurrences of a rule name in a repetition
            to a new rule name."
    :long (xdoc::topstring-@def "repetition-rename-rule")
    (make-repetition :range (repetition->range repetition)
                     :element (element-rename-rule
                               (repetition->element repetition)
                               oldname newname))
    :measure (two-nats-measure (repetition-count repetition) 1)
    :no-function t)

  (define element-rename-rule ((element elementp)
                               (oldname rulenamep)
                               (newname rulenamep))
    :returns (new-element elementp)
    :parents (renaming)
    :short "Rename all the occurrences of a rule name in an element
            to a new rule name."
    :long (xdoc::topstring-@def "element-rename-rule")
    (element-case element
                  :rulename (if (equal element.get oldname)
                                (element-rulename newname)
                              (element-fix element))
                  :group (element-group (alternation-rename-rule element.get
                                                                 oldname
                                                                 newname))
                  :option (element-option (alternation-rename-rule element.get
                                                                   oldname
                                                                   newname))
                  :char-val (element-fix element)
                  :num-val (element-fix element)
                  :prose-val (element-fix element))
    :measure (two-nats-measure (element-count element) 0)
    :no-function t)

  ///

  (verify-guards alternation-rename-rule))

(define rule-rename-rule ((rule rulep) (oldname rulenamep) (newname rulenamep))
  :returns (new-rule rulep)
  :parents (renaming)
  :short "Rename all the occurrences of a rule name to a new rule name,
          both in the definiens of a rule
          and in the name of the rule itself."
  (make-rule :name (if (equal (rule->name rule) oldname)
                       newname
                     (rule->name rule))
             :incremental (rule->incremental rule)
             :definiens (alternation-rename-rule (rule->definiens rule)
                                                 oldname newname))
  :no-function t)

(define rulelist-rename-rule ((rules rulelistp)
                              (oldname rulenamep)
                              (newname rulenamep))
  :returns (new-rules rulelistp)
  :parents (renaming)
  :short "Rename all the occurrences of a rule name to a new rule name,
          in all the rules in a list of rules."
  (cond ((endp rules) nil)
        (t (cons (rule-rename-rule (car rules) oldname newname)
                 (rulelist-rename-rule (cdr rules) oldname newname))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ removal
  :parents (operations)
  :short "Removal of rules in ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is sometimes useful to remove from a grammar
     all the rules that define certain rule names.")
   (xdoc::p
    "For example, the SMTP grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5321" "RFC 5321")
    " references rules defined in the IMF grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5322" "RFC 5322")
    ". The IMF rules depend on a rule @('atom'),
     but the SMTP rules provide their own definition of @('Atom')
     (recall that rule names are case-insensitive).
     Thus, before @(see plugging) the IMF rules into the SMTP rules,
     the removal operation can be used to remove, from the IMF rules,
     @('atom') and possibly any other rule already defined by SMTP."))
  :order-subtopics t)

(define remove-rules-that-define ((rulenames rulename-setp) (rules rulelistp))
  :returns (new-rules rulelistp)
  :parents (removal)
  :short "Remove from a list of rules all the ones
          that define one of the given rule names."
  (cond ((endp rules) nil)
        (t (if (in (rule->name (car rules)) rulenames)
               (remove-rules-that-define rulenames (cdr rules))
             (cons (rule-fix (car rules))
                   (remove-rules-that-define rulenames (cdr rules))))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rule-utilities
  :parents (operations)
  :short "Finding various structures within rule lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some rules or groups of rules can be used to help automate defining
     an abstract syntax corresponding to the concrete syntax defined in
     a grammar.")
   (xdoc::p
    "We begin by observing that if there is only one rule for a given
     rulename, and if the right hand side is a simple alternation of
     rulenames, then the rule names could correspond to a type/subtype
     relationship.  This relationship can be used to help generate
     an abstract syntax model of the language, and to help simplify
     code that processes values of the abstract syntax."))
  :order-subtopics t)

(define rulenames-from-singular-conc-and-rep ((concs alternationp))
  :returns (rulenames acl2::string-list-resultp)
  (b* (((when (endp concs)) nil)
       (first-conc (first concs))
       ((unless (equal (len first-conc) 1))
        (reserrf (cons :concatenation-is-not-singular first-conc)))
       (the-rep (car first-conc))
       ((unless (and (repetitionp the-rep)
                     (numrep-match-repeat-range-p
                      1 (repetition->range the-rep))))
        (reserrf (cons :not-singular-repetition the-rep)))
       (the-el (repetition->element the-rep))
       ((unless (and (elementp the-el)
                     (element-case the-el :rulename)))
        (reserrf (cons :not-rulename-element the-el)))
       (rest-rulenames (rulenames-from-singular-conc-and-rep (rest concs)))
       ((when (reserrp rest-rulenames))
        rest-rulenames)
       ((unless (acl2::string-listp rest-rulenames))
        (reserrf (cons :impossible rest-rulenames))))
    (cons (acl2::str-fix (rulename->get (element-rulename->get the-el)))
          rest-rulenames)))

(define rule-simple-subs ((rule-name acl2::stringp) (grammar rulelistp))
  :returns (sub-rule-names acl2::string-list-resultp)
  :parents (rule-utilities)
  :short "See if a rule could be used to define a type/subtype relationship."
  :long
  (xdoc::topstring
   (xdoc::p
    "This uses a very restrictive definition of whether the rule names
     in a rule are being used like a type/subtype relationship:")
   (xdoc::ul
    (xdoc::li
     "There must be only one rule with the given name in @('grammar').")
    (xdoc::li
     "It is not an incremental rule.")
    (xdoc::li
     "The rule must consist solely of an alternation of unadorned rule names.
      By unadorned we mean the concatenation and repetition are singular
      in the abstract syntax."))
   (xdoc::p
    "For example:")
   (xdoc::@{}
    "integer-type = unsigned-type / signed-type")
   (xdoc::p
    "If all of the requirements are satisified, the return value is a list
     of the \"sub\" rulenames.  Otherwise a @(see reserrp) is returned."))

  (b* (((mv rules ?not-rules)
        (rules-of-name (rulename (acl2::str-fix rule-name)) grammar))
       ((unless (equal (len rules) 1))
        (reserrf (cons :not-exactly-one-rule-with-name rule-name)))
       (the-rule (car rules))
       ((when (rule->incremental the-rule))
        (reserrf (cons :the-rule-is-incremental the-rule)))
       (alt (rule->definiens the-rule))
       ((unless (alternationp alt))
        (reserrf (cons :impossible alt))))
    (rulenames-from-singular-conc-and-rep (rule->definiens the-rule))))
