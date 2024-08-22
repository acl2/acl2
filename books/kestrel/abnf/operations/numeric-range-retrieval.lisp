; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../notation/abstract-syntax")

(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ numeric-range-retrieval
  :parents (operations)
  :short "Retrieval of numeric ranges from an ABNF grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define operations to retrieve the set of numeric ranges,
     as abstract syntactic entities,
     from an ABNF grammar and its components."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod num-range
  :short "Fixtype of numeric range notations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the @(':range') case of @(tsee num-val),
     which perhaps should be refactored so that the fixtype introduced here
     is instead introduced as part of the ABNF abstract syntax."))
  ((base num-base)
   (min nat)
   (max nat))
  :pred num-range-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset num-range-set
  :short "Fixtype of sets of numeric range notations."
  :elt-type num-range
  :elementp-of-nil nil
  :pred num-range-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define num-val-num-ranges ((numval num-val-p))
  :returns (ranges num-range-setp)
  :short "Set of numeric ranges in a numeric value notation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is empty for a direct numeric value notation,
     and a singleton for a numeric range value notation."))
  (num-val-case numval
                :direct nil
                :range (set::insert (make-num-range :base numval.base
                                                    :min numval.min
                                                    :max numval.max)
                                    nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines alt/conc/rep/elem-num-ranges

  (define alternation-num-ranges ((alt alternationp))
    :returns (ranges num-range-setp)
    :short "Set of numeric ranges in an alternation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the union of the sets of numeric ranges
       from all the alternatives (i.e. concatenations)
       that form the alternation."))
    (cond ((endp alt) nil)
          (t (set::union (concatenation-num-ranges (car alt))
                         (alternation-num-ranges (cdr alt)))))
    :measure (alternation-count alt))

  (define concatenation-num-ranges ((conc concatenationp))
    :returns (ranges num-range-setp)
    :short "Set of numeric ranges in a concatenation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the union of the sets of numeric ranges
       from all the repetitions that form the concatenation."))
    (cond ((endp conc) nil)
          (t (set::union (repetition-num-ranges (car conc))
                         (concatenation-num-ranges (cdr conc)))))
    :measure (concatenation-count conc))

  (define repetition-num-ranges ((rep repetitionp))
    :returns (ranges num-range-setp)
    :short "Set of numeric ranges in a repetition."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the set of numeric ranges in the underlying element."))
    (element-num-ranges (repetition->element rep))
    :measure (repetition-count rep))

  (define element-num-ranges ((elem elementp))
    :returns (ranges num-range-setp)
    :short "Set of numeric ranges in an element."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the element is a group or option,
       we return the set of numeric ranges of the underlying alternation.
       If the element is a numeric value notation,
       we return the empty or singleton set (see @(tsee num-val-num-ranges).
       In all other cases, we return the empty set:
       rule names, character value notations, and prose notations
       do not contain any numeric ranges."))
    (element-case
     elem
     :rulename nil
     :group (alternation-num-ranges elem.get)
     :option (alternation-num-ranges elem.get)
     :char-val nil
     :num-val (num-val-num-ranges elem.get)
     :prose-val nil)
    :measure (element-count elem))

  :hints (("Goal" :in-theory (enable o-p o< o-finp)))

  :verify-guards nil ; done below
  ///
  (verify-guards alternation-num-ranges)

  (fty::deffixequiv-mutual alt/conc/rep/elem-num-ranges))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rule-num-ranges ((rule rulep))
  :returns (ranges num-range-setp)
  :short "Set of numeric ranges in a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the set of numeric ranges
     in the alternation that defines the rules."))
  (alternation-num-ranges (rule->definiens rule))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulelist-num-ranges ((rules rulelistp))
  :returns (ranges num-range-setp)
  :short "Set of numeric ranges in a rule list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the union of the sets of numeric ranges
     from all the rules that form the list."))
  (cond ((endp rules) nil)
        (t (set::union (rule-num-ranges (car rules))
                       (rulelist-num-ranges (cdr rules)))))
  :verify-guards :after-returns
  :hooks (:fix))
