; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "real-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ arithmetic-operations
  :parents (language)
  :short "Operations on C arithmetic values."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plus-arithmetic-value ((val valuep))
  :guard (value-arithmeticp val)
  :returns (resval valuep)
  :short "Apply unary @('+') to an arithmetic value [C17:6.5.3.3/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We promote the operand
     and then we apply the operation on the integer.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic values."))
  (b* ((val (promote-value val)))
    (plus-integer-value val))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-plus-arithmetic-value
    (equal (type-of-value resval)
           (promote-type (type-of-value val)))
    :hints (("Goal" :in-theory (enable type-of-value-of-promote-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define minus-arithmetic-value ((val valuep))
  :guard (value-arithmeticp val)
  :returns (resval value-resultp)
  :short "Apply unary @('-') to an arithmetic value [C17:6.5.3.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We promote the operand
     and then we apply the operation on the integer.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic value."))
  (b* ((val (promote-value val)))
    (minus-integer-value val))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-minus-arithmetic-value
    (implies (not (errorp resval))
             (equal (type-of-value resval)
                    (promote-type (type-of-value val))))
    :hyp (value-arithmeticp val)
    :hints (("Goal" :in-theory (enable value-arithmeticp
                                       value-realp
                                       type-of-value-of-promote-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mul-arithmetic-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (resval value-resultp)
  :short "Apply binary @('*') to arithmetic values [C17:6.5.5/3] [C17:6.5.5/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (mul-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-mul-arithmetic-values
    (implies (not (errorp resval))
             (equal (type-of-value resval)
                    (uaconvert-types (type-of-value val1)
                                     (type-of-value val2))))
    :hyp (and (value-arithmeticp val1)
              (value-arithmeticp val2))
    :hints (("Goal"
             :in-theory (enable value-arithmeticp
                                value-realp
                                type-of-value-of-uaconvert-values)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define div-arithmetic-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (resval value-resultp)
  :short "Apply @('/') to arithmetic values
          [C17:6.5.5/3] [C17:6.5.5/5] [C17:6.5.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (div-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-div-arithmetic-values
    (implies (not (errorp resval))
             (equal (type-of-value resval)
                    (uaconvert-types (type-of-value val1)
                                     (type-of-value val2))))
    :hyp (and (value-arithmeticp val1)
              (value-arithmeticp val2))
    :hints (("Goal"
             :in-theory (enable value-arithmeticp
                                value-realp
                                type-of-value-of-uaconvert-values)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rem-arithmetic-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (resval value-resultp)
  :short "Apply @('%') to arithmetic values
          [C17:6.5.5/3] [C17:6.5.5/5] [C17:6.5.5/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (rem-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-rem-arithmetic-values
    (implies (not (errorp resval))
             (equal (type-of-value resval)
                    (uaconvert-types (type-of-value val1)
                                     (type-of-value val2))))
    :hyp (and (value-arithmeticp val1)
              (value-arithmeticp val2))
    :hints (("Goal"
             :in-theory (enable value-arithmeticp
                                value-realp
                                type-of-value-of-uaconvert-values)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-arithmetic-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (resval value-resultp)
  :short "Apply binary @('+') to arithmetic values [C17:6.5.6/4] [C17:6.5.6/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (add-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-add-arithmetic-values
    (implies (not (errorp resval))
             (equal (type-of-value resval)
                    (uaconvert-types (type-of-value val1)
                                     (type-of-value val2))))
    :hyp (and (value-arithmeticp val1)
              (value-arithmeticp val2))
    :hints (("Goal"
             :in-theory (enable value-arithmeticp
                                value-realp
                                type-of-value-of-uaconvert-values)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sub-arithmetic-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (resval value-resultp)
  :short "Apply binary @('-') to arithmetic values [C17:6.5.6/4] [C17:6.5.6/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (sub-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-sub-arithmetic-values
    (implies (not (errorp resval))
             (equal (type-of-value resval)
                    (uaconvert-types (type-of-value val1)
                                     (type-of-value val2))))
    :hyp (and (value-arithmeticp val1)
              (value-arithmeticp val2))
    :hints (("Goal"
             :in-theory (enable value-arithmeticp
                                value-realp
                                type-of-value-of-uaconvert-values)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eq-arithmetic-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (resval valuep)
  :short "Apply @('==') to arithmetic values [C17:6.5.9/3] [C17:6.5.9/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (eq-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-eq-arithmetic-values
    (equal (type-of-value resval)
           (type-sint))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ne-arithmetic-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (resval valuep)
  :short "Apply @('!=') to arithmetic values [C17:6.5.9/3] [C17:6.5.9/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We perform the usual arithmetic conversions
     and then we apply the operation on the integers.
     In our current formalization,
     integers are the only arithmetic values.
     This ACL2 function will be extended with more cases
     if/when we extend our model with non-integer arithmetic values."))
  (b* (((mv val1 val2) (uaconvert-values val1 val2)))
    (ne-integer-values val1 val2))
  :guard-hints (("Goal" :in-theory (enable value-arithmeticp
                                           value-realp
                                           type-of-value-of-uaconvert-values)))
  :hooks (:fix)

  ///

  (defret type-of-value-of-ne-arithmetic-values
    (equal (type-of-value resval)
           (type-sint))))
