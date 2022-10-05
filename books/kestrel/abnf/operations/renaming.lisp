; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../abstract-syntax")

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
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines alt/conc/rep/elem-rename-rule
  :verify-guards nil ; done below

  (define alternation-rename-rule ((alternation alternationp)
                                   (oldname rulenamep)
                                   (newname rulenamep))
    :returns (new-alternation alternationp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rule-rename-rule ((rule rulep) (oldname rulenamep) (newname rulenamep))
  :returns (new-rule rulep)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulelist-rename-rule ((rules rulelistp)
                              (oldname rulenamep)
                              (newname rulenamep))
  :returns (new-rules rulelistp)
  :short "Rename all the occurrences of a rule name to a new rule name,
          in all the rules in a list of rules."
  (cond ((endp rules) nil)
        (t (cons (rule-rename-rule (car rules) oldname newname)
                 (rulelist-rename-rule (cdr rules) oldname newname))))
  :no-function t)
