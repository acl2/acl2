; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../notation/abstract-syntax")

(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-printer-implementation
  :parents (grammar-printer)
  :short "Implementation of the pretty-printer of ABNF grammars."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pretty-printing
  :short "Pretty-print ABNF
          elements, alternations, concatenations, and repetitions
          to ACL2 strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to generate portions of documentation strings
     in the generated parsing functions.")
   (xdoc::p
    "We print numeric notations without leading zeros,
     except for a single zero if the number is 0.
     We might extend the abstract syntax
     to keep information about any leading zeros.")
   (xdoc::p
    "For the repetition prefix of a repetition,
     we print nothing for it if it is just one.
     If minimum and maximum are the same,
     we just print that.
     If the minimum is 0 and the maximum infinity,
     we just print @('*') (not the equivalent @('0*')).
     In all other cases, we print both minimum and maximum separated by @('*'),
     except that we omit the maximum if it is infinity.
     This is a minimal printing strategy,
     in the sense that it prints the prefix in the shortest possible way;
     noenetheless, we might extend the abstract syntax
     to preserve more information from the concrete syntax,
     and thus support different printed forms.")
   (xdoc::p
    "Prose elements are not supported,
     because currently we do not generate any paring functions for them.
     (To do that, we would need some external information.)"))

  (define pretty-print-element ((elem elementp))
    :returns (string acl2::stringp)
    (element-case
     elem
     :rulename (rulename->get elem.get)
     :group (str::cat "( " (pretty-print-alternation elem.get) " )")
     :option (str::cat "[ " (pretty-print-alternation elem.get) " ]")
     :char-val (char-val-case
                elem.get
                :insensitive (str::cat
                              (if (char-val-insensitive->iprefix elem.get)
                                  "%i"
                                "")
                              "\""
                              (char-val-insensitive->get elem.get)
                              "\"")
                :sensitive (str::cat
                            "%s\""
                            (char-val-sensitive->get elem.get)
                            "\""))
     :num-val (num-val-case
               elem.get
               :direct (str::cat
                        (b* ((base (num-val-direct->base elem.get)))
                          (num-base-case base
                                         :dec "%d"
                                         :hex "%x"
                                         :bin "%b"))
                        (pretty-print-num-val-direct-numbers
                         (num-val-direct->get elem.get)))
               :range (str::cat
                       (b* ((base (num-val-range->base elem.get)))
                         (num-base-case base
                                        :dec "%d"
                                        :hex "%x"
                                        :bin "%b"))
                       (str::nat-to-dec-string (num-val-range->min elem.get))
                       "-"
                       (str::nat-to-dec-string (num-val-range->max elem.get))))
     :prose-val (prog2$ (raise "Printing of ~x0 not supported." elem.get) ""))
    :measure (element-count elem))

  (define pretty-print-alternation ((alt alternationp))
    :returns (string acl2::stringp)
    (cond ((endp alt) "")
          ((endp (cdr alt)) (pretty-print-concatenation (car alt)))
          (t (str::cat (pretty-print-concatenation (car alt))
                       " / "
                       (pretty-print-alternation (cdr alt)))))
    :measure (alternation-count alt))

  (define pretty-print-concatenation ((conc concatenationp))
    :returns (string acl2::stringp)
    (cond ((endp conc) "")
          ((endp (cdr conc)) (pretty-print-repetition (car conc)))
          (t (str::cat (pretty-print-repetition (car conc))
                       " "
                       (pretty-print-concatenation (cdr conc)))))
    :measure (concatenation-count conc))

  (define pretty-print-repetition ((rep repetitionp))
    :returns (string acl2::stringp)
    (b* (((repetition rep) rep)
         ((repeat-range range) rep.range)
         ((when (and (equal range.min 1)
                     (equal range.max (nati-finite 1))))
          (pretty-print-element rep.element))
         ((when (equal range.max
                       (nati-finite range.min)))
          (str::cat (str::nat-to-dec-string range.min)
                    (pretty-print-element rep.element))))
      (str::cat (if (equal range.min 0)
                    ""
                  (str::nat-to-dec-string range.min))
                "*"
                (if (nati-case range.max :infinity)
                    ""
                  (str::nat-to-dec-string (nati-finite->get range.max)))
                (pretty-print-element rep.element)))
    :measure (repetition-count rep))

  :prepwork
  ((define pretty-print-num-val-direct-numbers ((nats nat-listp))
     :returns (string acl2::stringp)
     (cond ((endp nats) "")
           ((endp (cdr nats)) (str::nat-to-dec-string (car nats)))
           (t (str::cat
               (str::nat-to-dec-string (car nats))
               "."
               (pretty-print-num-val-direct-numbers (cdr nats))))))))
