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
(include-book "std/strings/hex" :dir :system)
(include-book "std/strings/binary" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-printer-implementation
  :parents (grammar-printer)
  :short "Implementation of the pretty-printer of ABNF grammars."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-number ((nat natp) (base num-base-p))
  :returns (string acl2::stringp)
  :short "Pretty-print a number in a given base."
  :long
  (xdoc::topstring
   (xdoc::p
    "We print numbers without leading zeros,
     except for a single zero if the number is 0.
     We might extend the abstract syntax
     to keep information about any leading zeros,
     in numeric value notations and in repetition prefixes."))
  (num-base-case base
                 :dec (str::nat-to-dec-string nat)
                 :hex (str::nat-to-hex-string nat)
                 :bin (str::nat-to-bin-string nat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-num-base ((base num-base-p))
  :returns (string acl2::stringp)
  :short "Pretty-print a numeric base prefix."
  (num-base-case base
                 :dec "%d"
                 :hex "%x"
                 :bin "%b"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-num-val-direct ((nats nat-listp) (base num-base-p))
  :returns (string acl2::stringp)
  :short "Pretty-print a direct numeric value notation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameters of this pretty-printing function are
     the components of the direct numeric value notation."))
  (str::cat
   (pretty-print-num-base base)
   (pretty-print-num-val-direct-aux nats base))

  :prepwork
  ((define pretty-print-num-val-direct-aux ((nats nat-listp) (base num-base-p))
     :returns (string acl2::stringp)
     :parents nil
     (cond ((endp nats) "")
           ((endp (cdr nats)) (pretty-print-number (car nats) base))
           (t (str::cat
               (pretty-print-number (car nats) base)
               "."
               (pretty-print-num-val-direct-aux (cdr nats) base)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-num-val-range ((min natp) (max natp) (base num-base-p))
  :returns (string acl2::stringp)
  :short "Pretty-print a range numeric value notation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameters of this pretty-printing function are
     the components of the range numeric value notation."))
  (str::cat
   (pretty-print-num-base base)
   (pretty-print-number min base)
   "-"
   (pretty-print-number max base)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-num-val ((numval num-val-p))
  :returns (string acl2::stringp)
  :short "Pretty-print a numeric value notation."
  (num-val-case
   numval
   :direct (pretty-print-num-val-direct numval.get numval.base)
   :range (pretty-print-num-val-range numval.min numval.max numval.base)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-char-val ((charval char-val-p))
  :returns (string acl2::stringp)
  :short "Pretty-print a character value notation."
  (char-val-case
   charval
   :insensitive (str::cat
                 (if (char-val-insensitive->iprefix charval)
                     "%i"
                   "")
                 "\""
                 (char-val-insensitive->get charval)
                 "\"")
   :sensitive (str::cat
               "%s\""
               (char-val-sensitive->get charval)
               "\"")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-prose-val ((proseval prose-val-p))
  :returns (string acl2::stringp)
  :short "Pretty-print a prose value notation."
  (str::cat "<"
            (prose-val->get proseval)
            ">"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-repeat-range ((range repeat-rangep))
  :returns (string acl2::stringp)
  :short "Pretty-print a repetition range."
  :long
  (xdoc::topstring
   (xdoc::p
    "We print nothing if the range is just from one to one.
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
     and thus support different printed forms."))
  (b* (((repeat-range range) range)
       ((when (and (equal range.min 1)
                   (equal range.max (nati-finite 1))))
        "")
       ((when (equal range.max
                     (nati-finite range.min)))
        (pretty-print-number range.min
                             (num-base-dec))))
    (str::cat (if (equal range.min 0)
                  ""
                (pretty-print-number range.min
                                     (num-base-dec)))
              "*"
              (if (nati-case range.max :infinity)
                  ""
                (pretty-print-number (nati-finite->get range.max)
                                     (num-base-dec))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pretty-print-alt/conc/rep/elem

  (define pretty-print-element ((elem elementp))
    :returns (string acl2::stringp)
    :short "Pretty-print an element."
    (element-case
     elem
     :rulename (rulename->get elem.get)
     :group (str::cat "( " (pretty-print-alternation elem.get) " )")
     :option (str::cat "[ " (pretty-print-alternation elem.get) " ]")
     :char-val (pretty-print-char-val elem.get)
     :num-val (pretty-print-num-val elem.get)
     :prose-val (pretty-print-prose-val elem.get))
    :measure (element-count elem))

  (define pretty-print-alternation ((alt alternationp))
    :returns (string acl2::stringp)
    :short "Pretty-print an alternation."
    (cond ((endp alt) "")
          ((endp (cdr alt)) (pretty-print-concatenation (car alt)))
          (t (str::cat (pretty-print-concatenation (car alt))
                       " / "
                       (pretty-print-alternation (cdr alt)))))
    :measure (alternation-count alt))

  (define pretty-print-concatenation ((conc concatenationp))
    :returns (string acl2::stringp)
    :short "Pretty-print a concatenation."
    (cond ((endp conc) "")
          ((endp (cdr conc)) (pretty-print-repetition (car conc)))
          (t (str::cat (pretty-print-repetition (car conc))
                       " "
                       (pretty-print-concatenation (cdr conc)))))
    :measure (concatenation-count conc))

  (define pretty-print-repetition ((rep repetitionp))
    :returns (string acl2::stringp)
    :short "Pretty-print a repetition."
    (b* (((repetition rep) rep))
      (str::cat (pretty-print-repeat-range rep.range)
                (pretty-print-element rep.element)))
    :measure (repetition-count rep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-rule ((rule rulep))
  :returns (string acl2::stringp)
  :short "Pretty-print a rule."
  (b* (((rule rule) rule))
    (str::cat (rulename->get rule.name)
              (if rule.incremental "=/" "=")
              (pretty-print-alternation rule.definiens))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pretty-print-rulelist ((rules rulelistp))
  :returns (string acl2::stringp)
  :short "Pretty-print a list of rules."
  (cond ((endp rules) "")
        ((endp (cdr rules))
         (str::cat (pretty-print-rule (car rules))
                   (str::implode (list (code-char 13) (code-char 10)))))
        (t (str::cat (pretty-print-rule (car rules))
                     (str::implode (list (code-char 13) (code-char 10)))
                     (pretty-print-rulelist (cdr rules))))))
