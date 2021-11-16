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

(include-book "kestrel/fty/nat-result" :dir :system)
(include-book "kestrel/fty/nat-list-result" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parsing-primitives-defresult
  :parents (abnf)
  :short "Some basic ABNF parsing functions
          for use with @(tsee fty::defresult)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These functions may be be useful when writing
     @(tsee fty::defresult)-based parsers for
     languages specified via ABNF grammar.
     These functions take lists of natural numbers as inputs
     and return two outputs:
     (i) a @(tsee fty::defresult) value (e.g. tree or error)
     obtained from the consumed input natural numbers, and
     (ii) the remaining unconsumed input natural numbers.")
   (xdoc::p
    "These are somewhat similar to the "
    (xdoc::seetopic "parsing-primitives-seq"
                    "<i>Seq</i>-based parsing primitives")
    ", but they have an interface suitable for @(tsee fty::defresult)
     instead of an interface suitable for <i>Seq</i>."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-next ((input nat-listp))
  :returns (mv (nat nat-resultp)
               (rest-input nat-listp))
  :short "Obtain the next natural number from the input."
  (if (consp input)
      (mv (lnfix (car input))
          (nat-list-fix (cdr input)))
    (mv (err :end-of-input)
        nil))
  :hooks (:fix)
  ///

  (defret len-of-parse-next-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-next-<
    (implies (not (resulterrp nat))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-direct ((nats nat-listp) (input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a direct numeric value consisting of given natural numbers."
  (b* (((mv nats input) (parse-direct-aux nats input))
       ((when (resulterrp nats)) (mv (err-push nats) input)))
    (mv (abnf::tree-leafterm nats)
        input))
  :hooks (:fix)

  :prepwork

  ((define parse-direct-aux ((nats nat-listp) (input nat-listp))
     :returns
     (mv (nats1
          nat-list-resultp
          :hints
          (("Goal"
            :in-theory
            (enable
             acl2::nat-listp-when-nat-list-resultp-and-not-resulterrp))))
         (rest-input nat-listp))
     :parents nil
     (b* (((when (endp nats)) (mv nil (nat-list-fix input)))
          ((mv nat? input1) (parse-next input))
          ((when (resulterrp nat?)) (mv (err-push nat?) (nat-list-fix input)))
          (nat nat?)
          ((unless (equal nat (lnfix (car nats))))
           (mv (err (list :found nat :required (lnfix (car nats))))
               (nat-list-fix input)))
          ((mv nats? input2) (parse-direct-aux (cdr nats) input1))
          ((when (resulterrp nats?)) (mv (err-push nats?) input1))
          (nats nats?))
       (mv (cons nat nats) input2))
     :hooks (:fix)
     ///

     (defret len-of-parse-direct-aux-<=
       (<= (len rest-input)
           (len input))
       :rule-classes :linear)

     (defret len-of-parse-direct-aux-<
       (implies (and (not (resulterrp nats1))
                     (consp nats))
                (< (len rest-input)
                   (len input)))
       :rule-classes :linear)))

  ///

  (defret len-of-parse-direct-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-direct-<
    (implies (and (not (resulterrp tree))
                  (consp nats))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-range ((min natp) (max natp) (input nat-listp))
  :guard (<= min max)
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a range numeric value consisting of given minimum and maximum."
  (b* (((mv nat? input1) (parse-next input))
       ((when (resulterrp nat?)) (mv (err-push nat?) (nat-list-fix input)))
       (nat nat?)
       ((unless (and (<= (lnfix min)
                         nat)
                     (<= nat
                         (lnfix max))))
        (mv (err (list :found nat :required (lnfix min) (lnfix max)))
            (nat-list-fix input))))
    (mv (abnf::tree-leafterm (list nat))
        input1))
  :hooks (:fix)
  ///

  (defret len-of-parse-range-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-range-<
    (implies (not (resulterrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-ichars ((chars acl2::stringp) (input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a case-insensitive character value consisting of
          a given string of characters."
  (b* (((mv nats input) (parse-ichars-aux (str::explode chars) input))
       ((when (resulterrp nats)) (mv (err-push nats) input)))
    (mv (abnf::tree-leafterm nats)
        input))
  :hooks (:fix)

  :prepwork

  ((define parse-ichars-aux ((chars character-listp) (input nat-listp))
     :returns
     (mv (nats
          nat-list-resultp
          :hints
          (("Goal"
            :in-theory
            (enable
             acl2::natp-when-nat-resultp-and-not-resulterrp
             acl2::nat-listp-when-nat-list-resultp-and-not-resulterrp))))
         (rest-input nat-listp))
     :parents nil
     (b* (((when (endp chars)) (mv nil (nat-list-fix input)))
          ((mv nat? input1) (parse-next input))
          ((when (resulterrp nat?)) (mv (err-push nat?) (nat-list-fix input)))
          (nat nat?)
          ((unless (abnf::nat-match-insensitive-char-p nat (car chars)))
           (mv (err (list :found nat :required (acl2::char-fix (car chars))))
               (nat-list-fix input)))
          ((mv nats? input2) (parse-ichars-aux (cdr chars) input1))
          ((when (resulterrp nats?)) (mv (err-push nats?) input1))
          (nats nats?))
       (mv (cons nat nats) input2))
     :hooks (:fix)
     ///

     (defret len-of-parse-ichars-aux-<=
       (<= (len rest-input)
           (len input))
       :rule-classes :linear)

     (defret len-of-parse-ichars-aux-<
       (implies (and (not (resulterrp nats))
                     (consp chars))
                (< (len rest-input)
                   (len input)))
       :rule-classes :linear)))

  ///

  (defret len-of-parse-ichars-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-ichars-<
    (implies (and (not (resulterrp tree))
                  (consp (str::explode chars)))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-schars ((chars acl2::stringp) (input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a case-sensitive character value consisting of
          a given string of characters."
  (b* (((mv nats input) (parse-schars-aux (str::explode chars) input))
       ((when (resulterrp nats)) (mv (err-push nats) input)))
    (mv (abnf::tree-leafterm nats)
        input))
  :hooks (:fix)

  :prepwork

  ((define parse-schars-aux ((chars character-listp) (input nat-listp))
     :returns
     (mv (nats
          nat-list-resultp
          :hints
          (("Goal"
            :in-theory
            (enable
             acl2::natp-when-nat-resultp-and-not-resulterrp
             acl2::nat-listp-when-nat-list-resultp-and-not-resulterrp))))
         (rest-input nat-listp))
     :parents nil
     (b* (((when (endp chars)) (mv nil (nat-list-fix input)))
          ((mv nat? input1) (parse-next input))
          ((when (resulterrp nat?)) (mv (err-push nat?) (nat-list-fix input)))
          (nat nat?)
          ((unless (abnf::nat-match-sensitive-char-p nat (car chars)))
           (mv (err (list :found nat :required (acl2::char-fix (car chars))))
               (nat-list-fix input)))
          ((mv nats? input2) (parse-schars-aux (cdr chars) input1))
          ((when (resulterrp nats?)) (mv (err-push nats?) input1))
          (nats nats?))
       (mv (cons nat nats) input2))
     :hooks (:fix)
     ///

     (defret len-of-parse-schars-aux-<=
       (<= (len rest-input)
           (len input))
       :rule-classes :linear)

     (defret len-of-parse-schars-aux-<
       (implies (and (not (resulterrp nats))
                     (consp chars))
                (< (len rest-input)
                   (len input)))
       :rule-classes :linear)))

  ///

  (defret len-of-parse-schars-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-schars-<
    (implies (and (not (resulterrp tree))
                  (consp (str::explode chars)))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))
