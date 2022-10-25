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

(local (include-book "kestrel/utilities/oset-theorems" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ closure
  :parents (operations)
  :short "Closure in ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "A rule's definiens may reference (i.e. ``call'') other rules.
     Those rules may in turn call further rules,
     and so on until a ``closed'' set of rules is reached.")
   (xdoc::p
    "When grammars are modularly defined, a grammar may not be closed,
     but after the modules are composed into one grammar for parsing,
     the resulting grammar should be closed.
     When composing grammars, sometimes only a portion of a grammar is selected,
     consisting of a subset of its rules (perhaps called by other grammars)
     along with their closure."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines alt/conc/rep/elem-called-rules
  :verify-guards nil ; done below

  (define alternation-called-rules ((alternation alternationp))
    :returns (rulenames rulename-setp)
    :short "Rule names that occur in an alternation."
    :long (xdoc::topstring-@def "alternation-called-rules")
    (cond ((endp alternation) nil)
          (t (union (concatenation-called-rules (car alternation))
                    (alternation-called-rules (cdr alternation)))))
    :measure (alternation-count alternation)
    :no-function t)

  (define concatenation-called-rules ((concatenation concatenationp))
    :returns (rulenames rulename-setp)
    :short "Rule names that occur in a concatenation."
    :long (xdoc::topstring-@def "concatenation-called-rules")
    (cond ((endp concatenation) nil)
          (t (union (repetition-called-rules (car concatenation))
                    (concatenation-called-rules (cdr concatenation)))))
    :measure (concatenation-count concatenation)
    :no-function t)

  (define repetition-called-rules ((repetition repetitionp))
    :returns (rulenames rulename-setp)
    :short "Rule names that occur in a repetition."
    :long (xdoc::topstring-@def "repetition-called-rules")
    (element-called-rules (repetition->element repetition))
    :measure (repetition-count repetition)
    :no-function t)

  (define element-called-rules ((element elementp))
    :returns (rulenames rulename-setp)
    :short "Rule names that occur in an element."
    :long (xdoc::topstring-@def "element-called-rules")
    (element-case element
                  :rulename (insert element.get nil)
                  :group (alternation-called-rules element.get)
                  :option (alternation-called-rules element.get)
                  :char-val nil
                  :num-val nil
                  :prose-val nil)
    :measure (element-count element)
    :no-function t)

  ///

  (verify-guards alternation-called-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rule-called-rules ((rule rulep))
  :returns (rulenames rulename-setp)
  :short "Rule names that occur in (the definiens of) a rule."
  (alternation-called-rules (rule->definiens rule))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulelist-called-rules ((rules rulelistp))
  :returns (rulenames rulename-setp)
  :short "Rule names that occur in (the definientia of) a list of rules."
  (cond ((endp rules) nil)
        (t (union (rule-called-rules (car rules))
                  (rulelist-called-rules (cdr rules)))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulelist-defined-rules ((rules rulelistp))
  :returns (rulenames rulename-setp)
  :short "Rule names that are defined in a list of rules."
  (cond ((endp rules) nil)
        (t (insert (rule->name (car rules))
                   (rulelist-defined-rules (cdr rules)))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulelist-closedp ((rules rulelistp))
  :returns (yes/no booleanp)
  :short "A rule list is closed iff it defines all the rules that it calls."
  (subset (rulelist-called-rules rules)
          (rulelist-defined-rules rules))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rules-of-name ((rulename rulenamep) (rules rulelistp))
  :returns (mv (rulename-rules rulelistp)
               (other-rules rulelistp))
  :short "Separate from some rules the ones that define a rule name."
  :long
  (xdoc::topstring-p
   "We scan @('rules'), taking out the rules that define @('rulename').
    The first result contains the rules that have been taken out,
    in the same order in which they appear in @('rules').
    The second result contains the remaining rules in @('rules'),
    after the ones in the first result have been taken out.")
  (b* (((when (endp rules)) (mv nil nil))
       (rule (rule-fix (car rules)))
       ((mv rulename-rules other-rules) (rules-of-name rulename (cdr rules))))
    (if (equal (rule->name rule) rulename)
        (mv (cons rule rulename-rules) other-rules)
      (mv rulename-rules (cons rule other-rules))))
  :no-function t
  ///

  (local
   (defrule len-of-other-rules-of-rules-of-name
     (b* (((mv rulename-rules other-rules) (rules-of-name rulename rules)))
       (equal (len other-rules)
              (- (len rules) (len rulename-rules))))))

  (defrule len-of-other-rules-of-rules-of-name-<
    (b* (((mv rulename-rules other-rules) (rules-of-name rulename rules)))
      (implies rulename-rules
               (< (len other-rules) (len rules))))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define calc-trans-rules-of-names ((workset rulename-setp)
                                   (accumulator rulelistp)
                                   (rules rulelistp))
  :returns (result rulelistp)
  :short "Calculate the rules from a list of rules
          that transitively define names in a list of rule names,
          collecting them into an accumulator (list of rules)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a work set algorithm.
     When the work set is empty,
     we are done and we return the rules collected so far.
     Otherwise, we remove one rule name from the work set
     and take out of @('rules') the rules that define it.
     If no rules in @('rules') define the rule name,
     we make a recursive call to examine the next rule name in the work set.
     Otherwise, we add these rules to the current result,
     extend the work set with the rule names referenced by these rules,
     and make a recursive call to re-examine the work set.")
   (xdoc::p
    "The algorithm makes progress
     either by reducing the length of @('rules')
     (if rules are taken out of @('rules')),
     or by reducing the size of the work set
     (if no rules are taken out of @('rules')),
     in which case the length of @('rules') stays the same."))
  (b* (((when (empty workset)) (rulelist-fix accumulator))
       (rulename (head workset))
       (workset (tail workset))
       ((mv rulename-rules other-rules) (rules-of-name rulename rules))
       ((when (not rulename-rules))
        (calc-trans-rules-of-names workset accumulator rules))
       (workset (union workset (rulelist-called-rules rulename-rules)))
       (accumulator (append accumulator rulename-rules)))
    (calc-trans-rules-of-names workset accumulator other-rules))
  :measure (two-nats-measure (len rules) (cardinality workset))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define trans-rules-of-names ((rulenames rulename-setp) (rules rulelistp))
  :returns (result rulelistp)
  :short "Find the rules from a list of rules
          that transitively define the names in a list of rule names."
  (calc-trans-rules-of-names rulenames nil rules)
  :no-function t)
