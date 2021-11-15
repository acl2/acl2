; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "semantics")

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "misc/seq" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parsing-primitives
  :parents (abnf)
  :short "Some basic parsing functions for ABNF."
  :long
  (xdoc::topstring
   (xdoc::p
    "These functions may be useful when writing
     parsers for languages specified via ABNF grammars.
     These functions are being moved here
     from the ABNF grammar parser:
     they are used by the ABNF grammar parser,
     but they are more general."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-any ((input nat-listp))
  :returns (mv (error? maybe-msgp)
               (nat natp :rule-classes (:rewrite :type-prescription))
               (rest-input nat-listp))
  :short "Parse any natural number."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the most basic parsing function:
     it parses any natural number (i.e. ABNF terminal).
     It is a building block of all the other parsing functions.")
   (xdoc::p
    "The parsed natural number is returned as the second result,
     so that the caller can examine it
     (e.g. to see that it is the expected one, or one of the expected ones).
     The only case in which this may fail is
     when the input list of natural number is empty;
     in this case, 0 is returned as second result, but it is irrelevant."))
  (if (consp input)
      (mv nil
          (lnfix (car input))
          (nat-list-fix (cdr input)))
    (mv "Failed to parse any natural number: end of input reached."
        0
        (nat-list-fix input)))
  :no-function t
  :prepwork ((local (in-theory (disable natp))))
  :hooks (:fix)
  ///

  (defret len-of-parse-any-linear-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-any-linear-<
    (implies (not error?)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-exact ((nat natp) (input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :short "Parse a given natural number
          into a tree that matches
          a direct numeric value notation that consists of that number."
  (b* ((nat (lnfix nat))
       ((mv error? input-nat input) (parse-any input))
       ((when error?) (mv error? nil input))
       ((unless (= input-nat nat))
        (mv (msg "Failed to parse ~x0; found ~x1 instead." nat input-nat)
            nil
            (cons input-nat input))))
    (mv nil (tree-leafterm (list nat)) input))
  :no-function t
  :hooks (:fix)
  ///

  (defret len-of-parse-exact-linear-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-exact-linear-<
    (implies (not error?)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-exact-list ((nats nat-listp) (input nat-listp))
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :short "Parse zero or more given natural numbers
          into a tree that matches
          a direct numeric value notation
          that consists of that list of numbers."
  (b* (((mv error? input) (parse-exact-list-aux nats input))
       ((when error?) (mv error? nil input)))
    (mv nil (tree-leafterm nats) input))
  :hooks (:fix)

  :prepwork
  ((define parse-exact-list-aux ((nats nat-listp) (input nat-listp))
     :returns (mv (error? maybe-msgp)
                  (rest-input nat-listp))
     (b* (((when (endp nats)) (mv nil (nat-list-fix input)))
          (nat (lnfix (car nats)))
          ((mv error? input-nat input) (parse-any input))
          ((when error?) (mv error? input))
          ((unless (= input-nat nat))
           (mv (msg "Failed to parse ~x0: found ~x1 instead." nat input-nat)
               (cons input-nat input)))
          ((mv error? input) (parse-exact-list-aux (cdr nats) input))
          ((when error?) (mv error? input)))
       (mv nil input))
     :hooks (:fix)
     ///

     (defret len-of-parse-exact-list-aux-linear-<=
       (<= (len rest-input)
           (len input))
       :rule-classes :linear)

     (defret len-of-parse-exact-list-aux-linear-<
       (implies (and (not error?)
                     (consp nats))
                (< (len rest-input)
                   (len input)))
       :rule-classes :linear)))

  ///

  (defret len-of-parse-exact-list-linear-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-exact-list-linear-<
    (implies (and (not error?)
                  (consp nats))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-in-range ((min natp) (max natp) (input nat-listp))
  :guard (<= min max)
  :returns (mv (error? maybe-msgp)
               (tree? (and (tree-optionp tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :short "Parse a natural number in a given range
          into a tree that matches
          a range numeric value notation that consists of that range."
  (b* ((min (lnfix min))
       (max (lnfix max))
       ((mv error? nat input) (parse-any input))
       ((when error?) (mv error? nil input))
       ((unless (and (<= min nat) (<= nat max)))
        (mv (msg "Failed to parse a number between ~x0 and ~x1; ~
                  found ~x2 instead."
                 min max nat)
            nil
            (cons nat input))))
    (mv nil (tree-leafterm (list nat)) input))
  :no-function t
  :hooks (:fix)
  ///

  (defret len-of-parse-in-range-linear-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-in-range-linear-<
    (implies (not error?)
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))
