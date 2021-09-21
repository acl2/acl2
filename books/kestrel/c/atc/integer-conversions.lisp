; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integer-conversions
  :parents (atc-shallow-embedding)
  :short "A model of C integer conversions for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define ACL2 functions that convert
     between values of different C integer types.
     In the ACL2 representation of C code for ATC,
     these explicit conversions are necessary,
     because the ACL2 representations of different C integer types
     are disjoint, i.e. there are no automatic inclusions.")
   (xdoc::p
    "Conversions between C types are described in [C:6.3].
     Here we define conversions among the integer types supported by our model;
     these conversions are described in [C:6.3.1.3].")
   (xdoc::p
    "For the case of a conversion to a signed integer
     that cannot represent the original value,
     we use a guard that rules out that case.
     This way, in order to use the conversion,
     it must be provably the case that
     the value is representable in the new signed integer type.")
   (xdoc::p
    "For the case of a conversion to an unsigned integer,
     we use @(tsee mod) (via the modular constructor) to make it fit.
     If the original value fits, the @(tsee mod) has no effect.
     Otherwise, the @(tsee mod) corresponds to the
     repeated addition or subtraction described in [C:6.3.1.3]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-conversion ((stype typep) (dtype typep))
  :guard (and (type-integerp stype)
              (type-integerp dtype)
              (not (equal stype dtype)))
  :returns (event pseudo-event-formp)
  :short "Event to generate the conversion between C integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conversion turns values of a source type @('stype')
     into values of the destination type @('dtype').
     The two types must be different.")
   (xdoc::p
    "Unless the destination type is signed,
     and the source type is also signed
     and always included in the destination type
     (for every possible choice of integer bit sizes),
     we generate not only the conversion,
     but also a function for the guard of the conversion,
     asserting that the original value is representable
     in the destination type.
     Some of the generated guards may be always true
     for certain choices of integer bit sizes."))

  (b* ((stype-string (atc-integer-type-string stype))
       (dtype-string (atc-integer-type-string dtype))
       (signedp (type-signed-integerp dtype))
       (guardp (and signedp
                    (case (type-kind dtype)
                      (:schar t)
                      (:sshort (not (eq (type-kind stype) :schar)))
                      (:sint (not (member-eq (type-kind stype)
                                             '(:schar :sshort))))
                      (:slong (not (member-eq (type-kind stype)
                                              '(:schar :sshort :sint))))
                      (:sllong (not (member-eq (type-kind stype)
                                               '(:schar :sshort :sint :slong))))
                      (t (impossible)))))
       (<stype> (atc-integer-type-fixtype stype))
       (<dtype> (atc-integer-type-fixtype dtype))
       (<stype>p (pack <stype> 'p))
       (<dtype>p (pack <dtype> 'p))
       (<stype>->get (pack <stype> '->get))
       (<dtype>-integerp (pack <dtype> '-integerp))
       (<dtype>-integerp-alt-def (pack <dtype>-integerp '-alt-def))
       (<dtype>-mod (pack <dtype> '-mod))
       (<dtype>-from-<stype> (pack <dtype> '-from- <stype>))
       (<dtype>-from-<stype>-okp (pack <dtype>-from-<stype> '-okp)))

    `(progn

       ,@(and
          guardp
          `((define ,<dtype>-from-<stype>-okp ((x ,<stype>p))
              :returns (yes/no booleanp)
              :short ,(str::cat "Check if a conversion from "
                                stype-string
                                " to "
                                dtype-string
                                " is well-defined.")
              (,<dtype>-integerp (,<stype>->get x))
              :hooks (:fix))))

       (define ,<dtype>-from-<stype> ((x ,<stype>p))
         ,@(and guardp `(:guard (,<dtype>-from-<stype>-okp x)))
         :returns (result ,<dtype>p)
         :short ,(str::cat "Convert from "
                           stype-string
                           " to "
                           dtype-string
                           "').")
         (,(if signedp <dtype> <dtype>-mod) (,<stype>->get x))
         :guard-hints (("Goal"
                        :in-theory (enable ,(if guardp
                                                <dtype>-from-<stype>-okp
                                              <dtype>-integerp-alt-def))))
         :hooks (:fix))))

  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-signed-integerp
                                           type-unsigned-integerp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-conversions-loop-inner ((stype typep)
                                                (dtypes type-listp))
  :guard (and (type-integerp stype)
              (type-integer-listp dtypes))
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the conversions
          between a source type and each of a list of destination types."
  :long
  (xdoc::topstring-p
   "This is the inner loop for generating conversions
    for all combinations of source and destination types.")
  (cond ((endp dtypes) nil)
        ((equal stype (car dtypes))
         (atc-def-integer-conversions-loop-inner stype (cdr dtypes)))
        (t (cons
            (atc-def-integer-conversion stype (car dtypes))
            (atc-def-integer-conversions-loop-inner stype (cdr dtypes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-conversions-loop-outer ((stypes type-listp)
                                                (dtypes type-listp))
  :guard (and (type-integer-listp stypes)
              (type-integer-listp dtypes))
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the conversions
          between each of a list of source types
          and each of a list of destination types."
  :long
  (xdoc::topstring-p
   "This is the outer loop for generating conversions
    for all combinations of source and destination types.")
  (cond ((endp stypes) nil)
        (t (append
            (atc-def-integer-conversions-loop-inner (car stypes) dtypes)
            (atc-def-integer-conversions-loop-outer (cdr stypes) dtypes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(progn ,@(atc-def-integer-conversions-loop-outer *atc-integer-types*
                                                   *atc-integer-types*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-integer-conversions-signed-from-unsigned-okp
  :short "Theorems about certain conversions from unsigned to signed
          being always allowed for certain integer type sizes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove these theorems in a general way,
     with hypotheses on the integer type sizes,
     disabling the rules that may otherwise obviate the hypotheses."))

  (defrule sint-from-uchar-okp-when-uchar-max-<=-sint-max
    (implies (<= (uchar-max) (sint-max))
             (sint-from-uchar-okp x))
    :enable (sint-from-uchar-okp sint-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule sint-from-ushort-okp-when-ushort-max-<=-sint-max
    (implies (<= (ushort-max) (sint-max))
             (sint-from-ushort-okp x))
    :enable (sint-from-ushort-okp sint-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule slong-from-uchar-okp-when-uchar-max-<=slong-max
    (implies (<= (uchar-max) (slong-max))
             (slong-from-uchar-okp x))
    :enable (slong-from-uchar-okp slong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule slong-from-ushort-okp-when-ushort-max-<=slong-max
    (implies (<= (ushort-max) (slong-max))
             (slong-from-ushort-okp x))
    :enable (slong-from-ushort-okp slong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule slong-from-uint-okp-when-uint-max-<=slong-max
    (implies (<= (uint-max) (slong-max))
             (slong-from-uint-okp x))
    :enable (slong-from-uint-okp slong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule sllong-from-uchar-okp-when-uchar-max-<=sllong-max
    (implies (<= (uchar-max) (sllong-max))
             (sllong-from-uchar-okp x))
    :enable (sllong-from-uchar-okp sllong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule sllong-from-ushort-okp-when-ushort-max-<=sllong-max
    (implies (<= (ushort-max) (sllong-max))
             (sllong-from-ushort-okp x))
    :enable (sllong-from-ushort-okp sllong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule sllong-from-uint-okp-when-uint-max-<=sllong-max
    (implies (<= (uint-max) (sllong-max))
             (sllong-from-uint-okp x))
    :enable (sllong-from-uint-okp sllong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max))

  (defrule sllong-from-ulong-okp-when-ulong-max-<=sllong-max
    (implies (<= (ulong-max) (sllong-max))
             (sllong-from-ulong-okp x))
    :enable (sllong-from-ulong-okp sllong-integerp-alt-def)
    :disable (uchar-max-vs-sint-max
              ushort-max-vs-sint-max
              uchar-max-vs-slong-max
              ushort-max-vs-slong-max
              uint-max-vs-slong-max
              uchar-max-vs-sllong-max
              ushort-max-vs-sllong-max
              uint-max-vs-sllong-max
              ulong-max-vs-sllong-max)))
