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

(include-book "closure")

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
    (xdoc::seetopic "concrete-syntax-validation" "resulting rule list")
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
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rule-prosep ((rule rulep))
  :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-prose-rules ((rules1 rulelistp) (rules2 rulelistp))
  :returns (rules rulelistp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plug-rules ((rules1 rulelistp) (rules2 rulelistp))
  :returns (rules rulelistp)
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
