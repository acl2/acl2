; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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
    "These funtions may be useful when writing
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
               (nat? (and (maybe-natp nat?)
                          (implies (not error?) (natp nat?))
                          (implies error? (not nat?))))
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
     (e.g. to see that it is the expected one, or an expected one).
     The only case in which this may fail is
     when the input list of natural number is empty;
     in this case, @('nil') is returned instead of a natural number."))
  (b* ((input (nat-list-fix input)))
    (if (consp input)
        (mv nil (car input) (cdr input))
      (mv "Failed to parse any natural number: end of input reached."
          nil
          input)))
  :no-function t
  :hooks (:fix)
  ///

  (defret natp-of-parse-any
    (implies (not error?)
             (natp nat?))
    :rule-classes :type-prescription)

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
               (tree? (and (maybe-treep tree?)
                           (implies (not error?) (treep tree?))
                           (implies error? (not tree?))))
               (rest-input nat-listp))
  :short "Parse a given natural number
          into a tree that matches
          a direct numeric value notation that consists of that number."
  (b* ((nat (mbe :logic (nfix nat) :exec nat)))
    (seq input
         (input-nat := (parse-any input))
         (unless (eql input-nat nat)
           (return-raw
            (mv (msg "Failed to parse ~x0; found ~x1 instead."
                     nat input-nat)
                nil
                (cons input-nat input))))
         (return (tree-leafterm (list nat)))))
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
