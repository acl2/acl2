; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "values")
(include-book "static-semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-operations
  :parents (language)
  :short "Operations on C integers."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integer->get ((val valuep))
  :guard (value-integerp val)
  :returns (int integerp)
  :short "Turn a C integer value into a mathematical (i.e. ACL2) integer."
  (value-case val
              :uchar val.get
              :schar val.get
              :ushort val.get
              :sshort val.get
              :uint val.get
              :sint val.get
              :ulong val.get
              :slong val.get
              :ullong val.get
              :sllong val.get
              :pointer (prog2$ (impossible) 0)
              :array (prog2$ (impossible) 0)
              :struct (prog2$ (impossible) 0))
  :guard-hints (("Goal" :in-theory (enable value-integerp
                                           value-signed-integerp
                                           value-unsigned-integerp)))
  :hooks (:fix)
  ///

  (defrule value-integer->get-bounds
    (and (<= (integer-type-min (type-of-value val))
             (value-integer->get val))
         (<= (value-integer->get val)
             (integer-type-max (type-of-value val))))
    :rule-classes ((:linear :trigger-terms ((value-integer->get val))))
    :enable (value-integer->get
             integer-type-min
             integer-type-max)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integer ((int integerp) (type typep))
  :guard (type-integerp type)
  :returns (val value-resultp)
  :short "Turn a mathematical (i.e. ACL2) integer into a C integer value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the C integer value is passed as parameter to this function.")
   (xdoc::p
    "If the type is plain @('char'), we return an error for now,
     because our model of values does not yet include plain @('char').")
   (xdoc::p
    "If the integer is not in the range representable by the type,
     we return an error."))
  (b* ((int (ifix int)))
    (type-case type
               :void (error (impossible))
               :char (error :char-not-supported)
               :uchar (if (uchar-integerp int)
                          (value-uchar int)
                        (error (list :uchar-out-of-range int)))
               :schar (if (schar-integerp int)
                          (value-schar int)
                        (error (list :schar-out-of-range int)))
               :ushort (if (ushort-integerp int)
                           (value-ushort int)
                         (error (list :ushort-out-of-range int)))
               :sshort (if (sshort-integerp int)
                           (value-sshort int)
                         (error (list :sshort-out-of-range int)))
               :uint (if (uint-integerp int)
                         (value-uint int)
                       (error (list :uint-out-of-range int)))
               :sint (if (sint-integerp int)
                         (value-sint int)
                       (error (list :sint-out-of-range int)))
               :ulong (if (ulong-integerp int)
                          (value-ulong int)
                        (error (list :ulong-out-of-range int)))
               :slong (if (slong-integerp int)
                          (value-slong int)
                        (error (list :slong-out-of-range int)))
               :ullong (if (ullong-integerp int)
                           (value-ullong int)
                         (error (list :ullong-out-of-range int)))
               :sllong (if (sllong-integerp int)
                           (value-sllong int)
                         (error (list :sllong-out-of-range int)))
               :pointer (error (impossible))
               :struct (error (impossible))
               :array (error (impossible))))
  :guard-hints (("Goal" :in-theory (enable type-integerp
                                           type-unsigned-integerp
                                           type-signed-integerp)))
  :hooks (:fix)
  ///

  (defret type-of-value-of-value-integer
    (implies (not (errorp val))
             (equal (type-of-value val)
                    (type-fix type)))
    :hints (("Goal" :in-theory (enable type-of-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-integer-and-value-integer->get
  :short "Theorems about @(tsee value-integer) and @(tsee value-integer->get)."

  (defrule value-integer-of-value-integer->get-when-type-of-value
    (implies (and (value-integerp val)
                  (equal type (type-of-value val)))
             (equal (value-integer (value-integer->get val) type)
                    (value-fix val)))
    :enable (value-integer
             value-integer->get
             value-integerp
             value-unsigned-integerp
             value-signed-integerp))

  (defrule value-integer->get-of-value-integer
    (b* ((val (value-integer int type)))
      (implies (not (errorp val))
               (equal (value-integer->get val)
                      (ifix int))))
    :enable (value-integer
             value-integer->get)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define convert-integer-value ((val valuep) (type typep))
  :guard (and (value-integerp val)
              (type-nonchar-integerp type))
  :returns (newval value-resultp)
  :short "Convert an integer value to an integer type [C:6.3.1.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We extract the underlying mathematical (i.e. ACL2) integer from the value,
     and we attempt to contruct an integer value of the new type from it.
     If the new type is unsigned,
     the mathematical integer is reduced
     modulo one plus the maximum value of the unsigned type;
     this always works, i.e. no error is ever returned.
     If the new type is signed, there are two cases:
     if the mathematical integer fits in the type,
     we return a value of that type with that integer;
     otherwise, we return an error.")
   (xdoc::p
    "We do not yet support conversions to the plain @('char') type;
     this restriction is expressed by the guard.
     However, we prefer to keep the name of this function more general,
     in anticipation for extending it to those two types."))
  (b* ((mathint (value-integer->get val)))
    (if (type-unsigned-integerp type)
        (value-integer (mod mathint (1+ (integer-type-max type)))
                       type)
      (value-integer mathint type)))
  :hooks (:fix))
