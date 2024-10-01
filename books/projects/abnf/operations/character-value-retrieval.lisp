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

(defxdoc+ character-value-retrieval
  :parents (operations)
  :short "Retrieval of character value notations from an ABNF grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define operations to retrieve the set of character value notations,
     as abstract syntactic entities,
     from an ABNF grammar and its components."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines alt/conc/rep/elem-char-vals

  (define alternation-char-vals ((alt alternationp))
    :returns (charvals char-val-setp)
    :short "Set of character value notations in an alternation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the union of the sets of character value notations
       from all the alternatives (i.e. concatenations)
       that form the alternation."))
    (cond ((endp alt) nil)
          (t (set::union (concatenation-char-vals (car alt))
                         (alternation-char-vals (cdr alt)))))
    :measure (alternation-count alt))

  (define concatenation-char-vals ((conc concatenationp))
    :returns (charvals char-val-setp)
    :short "Set of character value notations in a concatenation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the union of the sets of character value notations
       from all the repetitions that form the concatenation."))
    (cond ((endp conc) nil)
          (t (set::union (repetition-char-vals (car conc))
                         (concatenation-char-vals (cdr conc)))))
    :measure (concatenation-count conc))

  (define repetition-char-vals ((rep repetitionp))
    :returns (charvals char-val-setp)
    :short "Set of character value notations in a repetition."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the set of character value notations
       in the underlying element."))
    (element-char-vals (repetition->element rep))
    :measure (repetition-count rep))

  (define element-char-vals ((elem elementp))
    :returns (charvals char-val-setp)
    :short "Set of character value notations in an element."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the element is a group or option,
       we return the set of character value notations
       of the underlying alternation.
       If the element is a character value notation,
       we return it as a singleton set.
       In all other cases, we return the empty set:
       rule names, numeric value notations, and prose notations
       do not contain any character value notations."))
    (element-case
     elem
     :rulename nil
     :group (alternation-char-vals elem.get)
     :option (alternation-char-vals elem.get)
     :char-val (set::insert elem.get nil)
     :num-val nil
     :prose-val nil)
    :measure (element-count elem))

  :hints (("Goal" :in-theory (enable o-p o< o-finp)))

  :verify-guards nil ; done below
  ///
  (verify-guards alternation-char-vals)

  (fty::deffixequiv-mutual alt/conc/rep/elem-char-vals))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rule-char-vals ((rule rulep))
  :returns (charvals char-val-setp)
  :short "Set of character value notations in a rule."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the set of character value notations
     in the alternation that defines the rules."))
  (alternation-char-vals (rule->definiens rule))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rulelist-char-vals ((rules rulelistp))
  :returns (charvals char-val-setp)
  :short "Set of character value notations in a rule list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the union of the sets of character value notations
     from all the rules that form the list."))
  (cond ((endp rules) nil)
        (t (set::union (rule-char-vals (car rules))
                       (rulelist-char-vals (cdr rules)))))
  :verify-guards :after-returns
  :hooks (:fix))
