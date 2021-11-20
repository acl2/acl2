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

(include-book "abstract-syntax-operations")
(include-book "function-environments")
(include-book "computation-states")
(include-book "integer-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-execution
  :parents (atc-dynamic-semantics)
  :short "A model of C execution for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We distinguish between pure (i.e. side-effect-free) expressions
     and expressions that may have side effects.
     We allow the latter to appear only in certain parts of statements,
     and we put restrictions to ensure a predictable order of evaluation.
     Pure expressions may be evaluated in any order;
     we evaluate them left to right.")
   (xdoc::p
    "We formalize a big-step operational interpretive semantics.
     To ensure the termination of the ACL2 mutually recursive functions
     that formalize the execution of statements, function calls, etc.,
     these ACL2 functions take a limit on the depth of the recursive calls,
     which ends the recursion with an error when it reaches 0,
     which is decremented at each recursive call,
     and which is used as termination measure.
     Thus, a proof of total correctness
     (i.e. the code terminates and produces correct results)
     involves showing the existence of sufficiently large limit values,
     while a proof of partial correctness
     (i.e. the code produces correct results if it terminates)
     is relativized to the limit value not running out.
     The limit is an artifact of the formalization;
     it has no explicit counterpart in the execution state of the C code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-iconst ((ic iconstp))
  :returns (result value-resultp)
  :short "Execute an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to [C:6.4.4.1/5]:
     based on the suffixes and the base,
     we find the first type that suffices to represent the value,
     in the lists indicated in the table,
     and we return the value of the found type.
     If the value is too large, we return an error.")
   (xdoc::p
    "This is the dynamic counterpart of @(tsee check-iconst)."))
  (b* (((iconst ic) ic)
       (error (error (list :iconst-out-of-range (iconst-fix ic)))))
    (if ic.unsignedp
        (iconst-tysuffix-case
         ic.type
         :none (cond ((uint-integerp ic.value) (uint ic.value))
                     ((ulong-integerp ic.value) (ulong ic.value))
                     ((ullong-integerp ic.value) (ullong ic.value))
                     (t error))
         :long (cond ((ulong-integerp ic.value) (ulong ic.value))
                     ((ullong-integerp ic.value) (ullong ic.value))
                     (t error))
         :llong (cond ((ullong-integerp ic.value) (ullong ic.value))
                      (t error)))
      (iconst-tysuffix-case
       ic.type
       :none (if (iconst-base-case ic.base :dec)
                 (cond ((sint-integerp ic.value) (sint ic.value))
                       ((slong-integerp ic.value) (slong ic.value))
                       ((sllong-integerp ic.value) (sllong ic.value))
                       (t error))
               (cond ((sint-integerp ic.value) (sint ic.value))
                     ((uint-integerp ic.value) (uint ic.value))
                     ((slong-integerp ic.value) (slong ic.value))
                     ((ulong-integerp ic.value) (ulong ic.value))
                     ((sllong-integerp ic.value) (sllong ic.value))
                     ((ullong-integerp ic.value) (ullong ic.value))
                     (t error)))
       :long (if (iconst-base-case ic.base :dec)
                 (cond ((slong-integerp ic.value) (slong ic.value))
                       ((sllong-integerp ic.value) (sllong ic.value))
                       (t error))
               (cond ((slong-integerp ic.value) (slong ic.value))
                     ((ulong-integerp ic.value) (ulong ic.value))
                     ((sllong-integerp ic.value) (sllong ic.value))
                     ((ullong-integerp ic.value) (ullong ic.value))
                     (t error)))
       :llong (if (iconst-base-case ic.base :dec)
                  (cond ((sllong-integerp ic.value) (sllong ic.value))
                        (t error))
                (cond ((sllong-integerp ic.value) (sllong ic.value))
                      ((ullong-integerp ic.value) (ullong ic.value))
                      (t error))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-const ((c constp))
  :returns (result value-resultp)
  :short "Execute a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only support the execution of integer constants."))
  (const-case c
              :int (exec-iconst c.get)
              :float (error :exec-const-float)
              :enum (error :exec-const-enum)
              :char (error :exec-const-char))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ident ((id identp) (compst compustatep))
  :returns (result value-resultp)
  :short "Execute a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "We read the variable's value (if any) from the computation state."))
  (read-var id compst)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define promote-value ((val valuep))
  :returns (promoted-val valuep)
  :short "Apply the integer promotions to a value [C:6.3.1.1/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee promote-type).
     See the documentation of that function for details.
     Here we actually convert values;
     we do not merely compute a promoted type."))
  (b* ((val (value-fix val)))
    (cond ((ucharp val) (if (<= (uchar-max) (sint-max))
                            (sint-from-uchar val)
                          (uint-from-uchar val)))
          ((scharp val) (sint-from-schar val))
          ((ushortp val) (if (<= (ushort-max) (sint-max))
                             (sint-from-ushort val)
                           (uint-from-ushort val)))
          ((sshortp val) (sint-from-sshort val))
          (t val)))
  :guard-hints (("Goal" :in-theory (enable
                                    sint-from-uchar-okp
                                    sint-from-ushort-okp
                                    uchar-integerp-alt-def
                                    schar-integerp-alt-def
                                    ushort-integerp-alt-def
                                    sshort-integerp-alt-def
                                    sint-integerp-alt-def)))
  :hooks (:fix)
  ///

  (defruled values-of-promote-value
    (implies (value-arithmeticp val)
             (b* ((pval (promote-value val)))
               (or (uintp pval)
                   (sintp pval)
                   (ulongp pval)
                   (slongp pval)
                   (ullongp pval)
                   (sllongp pval))))
    :enable (value-arithmeticp
             value-realp
             value-integerp
             value-unsigned-integerp
             value-signed-integerp))

  (defrule value-integerp-of-promote-value
    (equal (value-integerp (promote-value val))
           (value-integerp (value-fix val)))
    :enable (value-integerp
             value-unsigned-integerp
             value-signed-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-plus ((arg valuep))
  :returns (result value-resultp)
  :short "Execute unary plus [C:6.5.3.3/1] [C:6.5.3.3/2]."
  (b* ((arg (value-fix arg))
       ((unless (value-arithmeticp arg))
        (error (list :mistype-plus
                     :required :arithmetic
                     :supplied arg)))
       (val (promote-value arg)))
    (cond ((uintp val) (plus-uint val))
          ((sintp val) (plus-sint val))
          ((ulongp val) (plus-ulong val))
          ((slongp val) (plus-slong val))
          ((ullongp val) (plus-ullong val))
          ((sllongp val) (plus-sllong val))
          (t (error (impossible)))))
  :guard-hints (("Goal"
                 :in-theory (enable value-arithmeticp
                                    value-realp
                                    value-integerp
                                    value-unsigned-integerp
                                    value-signed-integerp)
                 :use (:instance values-of-promote-value (val arg))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-minus ((arg valuep))
  :returns (result value-resultp)
  :short "Execute unary minus [C:6.5.3.3/1] [C:6.5.3.3/3]."
  (b* ((arg (value-fix arg))
       ((unless (value-arithmeticp arg))
        (error (list :mistype-minus
                     :required :arithmetic
                     :supplied arg)))
       (val (promote-value arg))
       (err (error (list :undefined-minus arg))))
    (cond ((uintp val) (minus-uint val))
          ((sintp val) (if (minus-sint-okp val) (minus-sint val) err))
          ((ulongp val) (minus-ulong val))
          ((slongp val) (if (minus-slong-okp val) (minus-slong val) err))
          ((ullongp val) (minus-ullong val))
          ((sllongp val) (if (minus-sllong-okp val) (minus-sllong val) err))
          (t (error (impossible)))))
  :guard-hints (("Goal"
                 :in-theory (enable value-arithmeticp
                                    value-realp
                                    value-integerp
                                    value-unsigned-integerp
                                    value-signed-integerp)
                 :use (:instance values-of-promote-value (val arg))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bitnot ((arg valuep))
  :returns (result value-resultp)
  :short "Execute bitwise complement [C:6.5.3.3/1] [C:6.5.3.3/4]."
  (b* ((arg (value-fix arg))
       ((unless (value-integerp arg))
        (error (list :mistype-bitnot
                     :required :integer
                     :supplied arg)))
       (val (promote-value arg)))
    (cond ((uintp val) (bitnot-uint val))
          ((sintp val) (bitnot-sint val))
          ((ulongp val) (bitnot-ulong val))
          ((slongp val) (bitnot-slong val))
          ((ullongp val) (bitnot-ullong val))
          ((sllongp val) (bitnot-sllong val))
          (t (error (impossible)))))
  :guard-hints (("Goal"
                 :in-theory (enable value-arithmeticp
                                    value-realp
                                    value-integerp
                                    value-unsigned-integerp
                                    value-signed-integerp)
                 :use (:instance values-of-promote-value (val arg))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lognot ((arg valuep))
  :returns (result value-resultp)
  :short "Execute unary lognot [C:6.5.3.3/1] [C:6.5.3.3/5]."
  (b* ((arg (value-fix arg))
       ((unless (value-scalarp arg))
        (error (list :mistype-lognot
                     :required :scalar
                     :supplied arg))))
    (cond ((ucharp arg) (lognot-uchar arg))
          ((scharp arg) (lognot-schar arg))
          ((ushortp arg) (lognot-ushort arg))
          ((sshortp arg) (lognot-sshort arg))
          ((uintp arg) (lognot-uint arg))
          ((sintp arg) (lognot-sint arg))
          ((ulongp arg) (lognot-ulong arg))
          ((slongp arg) (lognot-slong arg))
          ((ullongp arg) (lognot-ullong arg))
          ((sllongp arg) (lognot-sllong arg))
          ((pointerp arg) (sint-from-boolean (pointer-nullp arg)))
          (t (error (impossible)))))
  :guard-hints (("Goal"
                 :in-theory (enable value-scalarp
                                    value-arithmeticp
                                    value-realp
                                    value-integerp
                                    value-unsigned-integerp
                                    value-signed-integerp)
                 :use (:instance values-of-promote-value (val arg))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-unary ((op unopp) (arg value-resultp))
  :returns (result value-resultp)
  :short "Execute a unary operation."
  (b* ((arg (value-result-fix arg))
       ((when (errorp arg)) arg))
    (unop-case op
               :plus (exec-plus arg)
               :minus (exec-minus arg)
               :bitnot (exec-bitnot arg)
               :lognot (exec-lognot arg)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uaconvert-values ((val1 valuep) (val2 valuep))
  :guard (and (value-arithmeticp val1)
              (value-arithmeticp val2))
  :returns (mv (new-val1 valuep)
               (new-val2 valuep))
  :short "Apply the usual arithmetic conversions to two arithmetic values
          [C:6.3.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart of @(tsee uaconvert-types).
     See the documentation of that function for details.
     Here we actually convert the values;
     we do not merely compute the common type."))
  (b* ((val1 (promote-value val1))
       (val2 (promote-value val2)))
    (cond ((sllongp val1)
           (cond ((sllongp val2) (mv val1 val2))
                 ((slongp val2) (mv val1 (sllong-from-slong val2)))
                 ((sintp val2) (mv val1 (sllong-from-sint val2)))
                 ((ullongp val2) (mv (ullong-from-sllong val1) val2))
                 ((ulongp val2) (if (>= (sllong-max) (ulong-max))
                                    (mv val1 (sllong-from-ulong val2))
                                  (mv (ullong-from-sllong val1)
                                      (ullong-from-ulong val2))))
                 ((uintp val2) (if (>= (sllong-max) (uint-max))
                                   (mv val1 (sllong-from-uint val2))
                                 (mv (ullong-from-sllong val1)
                                     (ullong-from-uint val2))))
                 (t (prog2$ (impossible) (mv val1 val2)))))
          ((slongp val1)
           (cond ((sllongp val2) (mv (sllong-from-slong val1) val2))
                 ((slongp val2) (mv val1 val2))
                 ((sintp val2) (mv val1 (slong-from-sint val2)))
                 ((ullongp val2) (mv (ullong-from-slong val1) val2))
                 ((ulongp val2) (mv (ulong-from-slong val1) val2))
                 ((uintp val2) (if (>= (slong-max) (uint-max))
                                   (mv val1 (slong-from-uint val2))
                                 (mv (ulong-from-slong val1)
                                     (ulong-from-uint val2))))
                 (t (prog2$ (impossible) (mv val1 val2)))))
          ((sintp val1)
           (cond ((sllongp val2) (mv (sllong-from-sint val1) val2))
                 ((slongp val2) (mv (slong-from-sint val1) val2))
                 ((sintp val2) (mv val1 val2))
                 ((ullongp val2) (mv (ullong-from-sint val1) val2))
                 ((ulongp val2) (mv (ulong-from-sint val1) val2))
                 ((uintp val2) (mv (uint-from-sint val1) val2))
                 (t (prog2$ (impossible) (mv val1 val2)))))
          ((ullongp val1)
           (cond ((sllongp val2) (mv val1 (ullong-from-sllong val2)))
                 ((slongp val2) (mv val1 (ullong-from-slong val2)))
                 ((sintp val2) (mv val1 (ullong-from-sint val2)))
                 ((ullongp val2) (mv val1 val2))
                 ((ulongp val2) (mv val1 (ullong-from-ulong val2)))
                 ((uintp val2) (mv val1 (ullong-from-uint val2)))
                 (t (prog2$ (impossible) (mv val1 val2)))))
          ((ulongp val1)
           (cond ((sllongp val2) (if (>= (sllong-max) (ulong-max))
                                     (mv (sllong-from-ulong val1) val2)
                                   (mv (ullong-from-ulong val1)
                                       (ullong-from-sllong val2))))
                 ((slongp val2) (mv val1 (ulong-from-slong val2)))
                 ((sintp val2) (mv val1 (ulong-from-sint val2)))
                 ((ullongp val2) (mv (ullong-from-ulong val1) val2))
                 ((ulongp val2) (mv val1 val2))
                 ((uintp val2) (mv val1 (ulong-from-uint val2)))
                 (t (prog2$ (impossible) (mv val1 val2)))))
          ((uintp val1)
           (cond ((sllongp val2) (if (>= (sllong-max) (uint-max))
                                     (mv (sllong-from-uint val1) val2)
                                   (mv (ullong-from-uint val1)
                                       (ullong-from-sllong val2))))
                 ((slongp val2) (if (>= (slong-max) (uint-max))
                                    (mv (slong-from-uint val1) val2)
                                  (mv (ulong-from-uint val1)
                                      (ulong-from-slong val2))))
                 ((sintp val2) (mv val1 (uint-from-sint val2)))
                 ((ullongp val2) (mv (ullong-from-uint val1) val2))
                 ((ulongp val2) (mv (ulong-from-uint val1) val2))
                 ((uintp val2) (mv val1 val2))
                 (t (prog2$ (impossible) (mv val1 val2)))))
          (t (prog2$ (impossible) (mv val1 val2)))))
  :guard-hints (("Goal"
                 :do-not '(preprocess) ; just for speed
                 :in-theory (enable slong-from-uint-okp
                                    sllong-from-uint-okp
                                    sllong-from-ulong-okp
                                    sint-integerp-alt-def
                                    slong-integerp-alt-def
                                    sllong-integerp-alt-def
                                    uint-integerp-alt-def
                                    ulong-integerp-alt-def
                                    ullong-integerp-alt-def)
                 :use ((:instance values-of-promote-value (val val1))
                       (:instance values-of-promote-value (val val2)))))
  ///

  (defrule values-of-uaconvert-values
    (implies (and (value-arithmeticp val1)
                  (value-arithmeticp val2))
             (b* (((mv cval1 cval2) (uaconvert-values val1 val2)))
               (or (and (uintp cval1) (uintp cval2))
                   (and (sintp cval1) (sintp cval2))
                   (and (ulongp cval1) (ulongp cval2))
                   (and (slongp cval1) (slongp cval2))
                   (and (ullongp cval1) (ullongp cval2))
                   (and (sllongp cval1) (sllongp cval2)))))
    :use ((:instance values-of-promote-value (val val1))
          (:instance values-of-promote-value (val val2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-test ((arg value-resultp))
  :returns (result boolean-resultp)
  :short "Execute a test on a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for tests of conditionals
     and for the operands of the non-strict operations.")
   (xdoc::p
    "The argument value must be a scalar.
     We return an ACL2 boolean, or an error."))
  (b* ((arg (value-result-fix arg))
       ((when (errorp arg)) arg)
       ((unless (value-scalarp arg)) (error (list :test-mistype
                                                  :required :scalar
                                                  :supplied arg))))
    (cond ((ucharp arg) (boolean-from-uchar arg))
          ((scharp arg) (boolean-from-schar arg))
          ((ushortp arg) (boolean-from-ushort arg))
          ((sshortp arg) (boolean-from-sshort arg))
          ((uintp arg) (boolean-from-uint arg))
          ((sintp arg) (boolean-from-sint arg))
          ((ulongp arg) (boolean-from-ulong arg))
          ((slongp arg) (boolean-from-slong arg))
          ((ullongp arg) (boolean-from-ullong arg))
          ((sllongp arg) (boolean-from-sllong arg))
          ((pointerp arg) (not (pointer-nullp arg)))
          (t (error (impossible)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-integer ((arg valuep))
  :guard (value-integerp arg)
  :returns (result integerp)
  :short "Execute a value to obtain an (ACL2) integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for operands such that
     only their mathematical values affect the result of the operation,
     and not their C types.
     Examples are the second operand of shift operations
     and the index operand of array subscript operations."))
  (b* ((arg (value-fix arg)))
    (cond ((ucharp arg) (uchar-integer-value arg))
          ((scharp arg) (schar-integer-value arg))
          ((ushortp arg) (ushort-integer-value arg))
          ((sshortp arg) (sshort-integer-value arg))
          ((uintp arg) (uint-integer-value arg))
          ((sintp arg) (sint-integer-value arg))
          ((ulongp arg) (ulong-integer-value arg))
          ((slongp arg) (slong-integer-value arg))
          ((ullongp arg) (ullong-integer-value arg))
          ((sllongp arg) (sllong-integer-value arg))
          (t (prog2$ (impossible) 0))))
  :guard-hints (("Goal" :in-theory (enable value-integerp
                                           value-unsigned-integerp
                                           value-signed-integerp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-mul ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute multiplication [C:6.5.5/2] [C:6.5.5/3] [C:6.5.5/4]."
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-arithmeticp arg1))
        (error (list :mistype-mul
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-arithmeticp arg2))
        (error (list :mistype-mul
                     :required :arithmetic
                     :supplied arg2)))
       (err (error (list :undefined-mul arg1 arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (mul-uint-uint val1 val2))
     ((sintp val1) (if (mul-sint-sint-okp val1 val2)
                       (mul-sint-sint val1 val2)
                     err))
     ((ulongp val1) (mul-ulong-ulong val1 val2))
     ((slongp val1) (if (mul-slong-slong-okp val1 val2)
                        (mul-slong-slong val1 val2)
                      err))
     ((ullongp val1) (mul-ullong-ullong val1 val2))
     ((sllongp val1) (if (mul-sllong-sllong-okp val1 val2)
                         (mul-sllong-sllong val1 val2)
                       err))
     (t (error (impossible)))))
  :guard-hints (("Goal" :use (:instance values-of-uaconvert-values
                              (val1 arg1) (val2 arg2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-div ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute division [C:6.5.5/2] [C:6.5.5/3] [C:6.5.5/5]."
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-arithmeticp arg1))
        (error (list :mistype-div
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-arithmeticp arg2))
        (error (list :mistype-div
                     :required :arithmetic
                     :supplied arg2)))
       (err (error (list :undefined-div arg1 arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (if (div-uint-uint-okp val1 val2)
                       (div-uint-uint val1 val2)
                     err))
     ((sintp val1) (if (div-sint-sint-okp val1 val2)
                       (div-sint-sint val1 val2)
                     err))
     ((ulongp val1) (if (div-ulong-ulong-okp val1 val2)
                        (div-ulong-ulong val1 val2)
                      err))
     ((slongp val1) (if (div-slong-slong-okp val1 val2)
                        (div-slong-slong val1 val2)
                      err))
     ((ullongp val1) (if (div-ullong-ullong-okp val1 val2)
                         (div-ullong-ullong val1 val2)
                       err))
     ((sllongp val1) (if (div-sllong-sllong-okp val1 val2)
                         (div-sllong-sllong val1 val2)
                       err))
     (t (error (impossible)))))
  :guard-hints (("Goal" :use (:instance values-of-uaconvert-values
                              (val1 arg1) (val2 arg2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-rem ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute remainder [C:6.5.5/2] [C:6.5.5/3] [C:6.5.5/5]."
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-integerp arg1))
        (error (list :mistype-rem
                     :required :integer
                     :supplied arg1)))
       ((unless (value-integerp arg2))
        (error (list :mistype-rem
                     :required :integer
                     :supplied arg2)))
       (err (error (list :undefined-rem arg1 arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (if (rem-uint-uint-okp val1 val2)
                       (rem-uint-uint val1 val2)
                     err))
     ((sintp val1) (if (rem-sint-sint-okp val1 val2)
                       (rem-sint-sint val1 val2)
                     err))
     ((ulongp val1) (if (rem-ulong-ulong-okp val1 val2)
                        (rem-ulong-ulong val1 val2)
                      err))
     ((slongp val1) (if (rem-slong-slong-okp val1 val2)
                        (rem-slong-slong val1 val2)
                      err))
     ((ullongp val1) (if (rem-ullong-ullong-okp val1 val2)
                         (rem-ullong-ullong val1 val2)
                       err))
     ((sllongp val1) (if (rem-sllong-sllong-okp val1 val2)
                         (rem-sllong-sllong val1 val2)
                       err))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance values-of-uaconvert-values
                       (val1 arg1) (val2 arg2))
                 :in-theory (enable value-arithmeticp value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-add ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute addition [C:6.5.6/2] [C:6.5.6/4] [C:6.5.6/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not support additions involving pointers for now."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-arithmeticp arg1))
        (error (list :mistype-add
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-arithmeticp arg2))
        (error (list :mistype-add
                     :required :arithmetic
                     :supplied arg2)))
       (err (error (list :undefined-add arg1 arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (add-uint-uint val1 val2))
     ((sintp val1) (if (add-sint-sint-okp val1 val2)
                       (add-sint-sint val1 val2)
                     err))
     ((ulongp val1) (add-ulong-ulong val1 val2))
     ((slongp val1) (if (add-slong-slong-okp val1 val2)
                        (add-slong-slong val1 val2)
                      err))
     ((ullongp val1) (add-ullong-ullong val1 val2))
     ((sllongp val1) (if (add-sllong-sllong-okp val1 val2)
                         (add-sllong-sllong val1 val2)
                       err))
     (t (error (impossible)))))
  :guard-hints (("Goal" :use (:instance values-of-uaconvert-values
                              (val1 arg1) (val2 arg2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-sub ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute subtraction [C:6.5.6/3] [C:6.5.6/4] [C:6.5.6/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not support subtractions involving pointers for now."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-arithmeticp arg1))
        (error (list :mistype-sub
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-arithmeticp arg2))
        (error (list :mistype-sub
                     :required :arithmetic
                     :supplied arg2)))
       (err (error (list :undefined-sub arg1 arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (sub-uint-uint val1 val2))
     ((sintp val1) (if (sub-sint-sint-okp val1 val2)
                       (sub-sint-sint val1 val2)
                     err))
     ((ulongp val1) (sub-ulong-ulong val1 val2))
     ((slongp val1) (if (sub-slong-slong-okp val1 val2)
                        (sub-slong-slong val1 val2)
                      err))
     ((ullongp val1) (sub-ullong-ullong val1 val2))
     ((sllongp val1) (if (sub-sllong-sllong-okp val1 val2)
                         (sub-sllong-sllong val1 val2)
                       err))
     (t (error (impossible)))))
  :guard-hints (("Goal" :use (:instance values-of-uaconvert-values
                              (val1 arg1) (val2 arg2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-shl ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute left shifts [C:6.5.7/2] [C:6.5.7/3] [C:6.5.7/4]."
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-integerp arg1))
        (error (list :mistype-shl
                     :required :integer
                     :supplied arg1)))
       (val1 (promote-value arg1))
       ((unless (value-integerp arg2))
        (error (list :mistype-shl
                     :required :integer
                     :supplied arg2)))
       (val2 (promote-value arg2))
       (val2 (exec-integer val2))
       (err (error (list :undefined-shl arg1 arg2))))
    (cond
     ((uintp val1) (if (shl-uint-okp val1 val2)
                       (shl-uint val1 val2)
                     err))
     ((sintp val1) (if (shl-sint-okp val1 val2)
                       (shl-sint val1 val2)
                     err))
     ((ulongp val1) (if (shl-ulong-okp val1 val2)
                        (shl-ulong val1 val2)
                      err))
     ((slongp val1) (if (shl-slong-okp val1 val2)
                        (shl-slong val1 val2)
                      err))
     ((ullongp val1) (if (shl-ullong-okp val1 val2)
                         (shl-ullong val1 val2)
                       err))
     ((sllongp val1) (if (shl-sllong-okp val1 val2)
                         (shl-sllong val1 val2)
                       err))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use ((:instance values-of-promote-value (val arg1))
                       (:instance values-of-promote-value (val arg2)))
                 :in-theory (enable value-arithmeticp
                                    value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-shr ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute right shifts [C:6.5.7/2] [C:6.5.7/3] [C:6.5.7/5]."
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-integerp arg1))
        (error (list :mistype-shr
                     :required :integer
                     :supplied arg1)))
       (val1 (promote-value arg1))
       ((unless (value-integerp arg2))
        (error (list :mistype-shr
                     :required :integer
                     :supplied arg2)))
       (val2 (promote-value arg2))
       (val2 (exec-integer val2))
       ((when (errorp val2)) val2)
       (err (error (list :undefined-shr arg1 arg2))))
    (cond
     ((uintp val1) (if (shr-uint-okp val1 val2) (shr-uint val1 val2) err))
     ((sintp val1) (if (shr-sint-okp val1 val2) (shr-sint val1 val2) err))
     ((ulongp val1) (if (shr-ulong-okp val1 val2) (shr-ulong val1 val2) err))
     ((slongp val1) (if (shr-slong-okp val1 val2) (shr-slong val1 val2) err))
     ((ullongp val1) (if (shr-ullong-okp val1 val2) (shr-ullong val1 val2) err))
     ((sllongp val1) (if (shr-sllong-okp val1 val2) (shr-sllong val1 val2) err))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use ((:instance values-of-promote-value (val arg1))
                       (:instance values-of-promote-value (val arg2)))
                 :in-theory (enable value-arithmeticp
                                    value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-lt ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute less-than [C:6.5.8/2] [C:6.5.8/3] [C:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not support comparisons involving pointers for now."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-realp arg1))
        (error (list :mistype-lt
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-realp arg2))
        (error (list :mistype-lt
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (lt-uint-uint val1 val2))
     ((sintp val1) (lt-sint-sint val1 val2))
     ((ulongp val1) (lt-ulong-ulong val1 val2))
     ((slongp val1) (lt-slong-slong val1 val2))
     ((ullongp val1) (lt-ullong-ullong val1 val2))
     ((sllongp val1) (lt-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance values-of-uaconvert-values
                       (val1 arg1) (val2 arg2))
                 :in-theory (enable value-arithmeticp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-gt ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute greater-than [C:6.5.8/2] [C:6.5.8/3] [C:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not support comparisons involving pointers for now."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-realp arg1))
        (error (list :mistype-gt
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-realp arg2))
        (error (list :mistype-gt
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (gt-uint-uint val1 val2))
     ((sintp val1) (gt-sint-sint val1 val2))
     ((ulongp val1) (gt-ulong-ulong val1 val2))
     ((slongp val1) (gt-slong-slong val1 val2))
     ((ullongp val1) (gt-ullong-ullong val1 val2))
     ((sllongp val1) (gt-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance values-of-uaconvert-values
                       (val1 arg1) (val2 arg2))
                 :in-theory (enable value-arithmeticp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-le ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute less-than-or-equal-to [C:6.5.8/2] [C:6.5.8/3] [C:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not support comparisons involving pointers for now."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-realp arg1))
        (error (list :mistype-le
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-realp arg2))
        (error (list :mistype-le
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (le-uint-uint val1 val2))
     ((sintp val1) (le-sint-sint val1 val2))
     ((ulongp val1) (le-ulong-ulong val1 val2))
     ((slongp val1) (le-slong-slong val1 val2))
     ((ullongp val1) (le-ullong-ullong val1 val2))
     ((sllongp val1) (le-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance values-of-uaconvert-values
                       (val1 arg1) (val2 arg2))
                 :in-theory (enable value-arithmeticp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ge ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute greater-than-or-equal-to [C:6.5.8/2] [C:6.5.8/3] [C:6.5.8/6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not support comparisons involving pointers for now."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-realp arg1))
        (error (list :mistype-ge
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-realp arg2))
        (error (list :mistype-ge
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (ge-uint-uint val1 val2))
     ((sintp val1) (ge-sint-sint val1 val2))
     ((ulongp val1) (ge-ulong-ulong val1 val2))
     ((slongp val1) (ge-slong-slong val1 val2))
     ((ullongp val1) (ge-ullong-ullong val1 val2))
     ((sllongp val1) (ge-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance values-of-uaconvert-values
                       (val1 arg1) (val2 arg2))
                 :in-theory (enable value-arithmeticp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-eq ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute equality [C:6.5.9/2] [C:6.5.9/3] [C:6.5.9/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not support comparisons involving pointers for now."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-arithmeticp arg1))
        (error (list :mistype-eq
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-arithmeticp arg2))
        (error (list :mistype-eq
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (eq-uint-uint val1 val2))
     ((sintp val1) (eq-sint-sint val1 val2))
     ((ulongp val1) (eq-ulong-ulong val1 val2))
     ((slongp val1) (eq-slong-slong val1 val2))
     ((ullongp val1) (eq-ullong-ullong val1 val2))
     ((sllongp val1) (eq-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal" :use (:instance values-of-uaconvert-values
                              (val1 arg1) (val2 arg2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-ne ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute non-equality [C:6.5.9/2] [C:6.5.9/3] [C:6.5.9/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not support comparisons involving pointers for now."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-arithmeticp arg1))
        (error (list :mistype-ne
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-arithmeticp arg2))
        (error (list :mistype-ne
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (ne-uint-uint val1 val2))
     ((sintp val1) (ne-sint-sint val1 val2))
     ((ulongp val1) (ne-ulong-ulong val1 val2))
     ((slongp val1) (ne-slong-slong val1 val2))
     ((ullongp val1) (ne-ullong-ullong val1 val2))
     ((sllongp val1) (ne-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal" :use (:instance values-of-uaconvert-values
                              (val1 arg1) (val2 arg2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bitand ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute bitwise cojunction [C:6.5.10]."
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-integerp arg1))
        (error (list :mistype-bitand
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-integerp arg2))
        (error (list :mistype-bitand
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (bitand-uint-uint val1 val2))
     ((sintp val1) (bitand-sint-sint val1 val2))
     ((ulongp val1) (bitand-ulong-ulong val1 val2))
     ((slongp val1) (bitand-slong-slong val1 val2))
     ((ullongp val1) (bitand-ullong-ullong val1 val2))
     ((sllongp val1) (bitand-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance values-of-uaconvert-values
                       (val1 arg1) (val2 arg2))
                 :in-theory (enable value-arithmeticp value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bitxor ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute bitwise cojunction [C:6.5.11]."
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-integerp arg1))
        (error (list :mistype-bitxor
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-integerp arg2))
        (error (list :mistype-bitxor
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (bitxor-uint-uint val1 val2))
     ((sintp val1) (bitxor-sint-sint val1 val2))
     ((ulongp val1) (bitxor-ulong-ulong val1 val2))
     ((slongp val1) (bitxor-slong-slong val1 val2))
     ((ullongp val1) (bitxor-ullong-ullong val1 val2))
     ((sllongp val1) (bitxor-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance values-of-uaconvert-values
                       (val1 arg1) (val2 arg2))
                 :in-theory (enable value-arithmeticp value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-bitior ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute bitwise cojunction [C:6.5.12]."
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-integerp arg1))
        (error (list :mistype-bitior
                     :required :arithmetic
                     :supplied arg1)))
       ((unless (value-integerp arg2))
        (error (list :mistype-bitior
                     :required :arithmetic
                     :supplied arg2)))
       ((mv val1 val2) (uaconvert-values arg1 arg2)))
    (cond
     ((uintp val1) (bitior-uint-uint val1 val2))
     ((sintp val1) (bitior-sint-sint val1 val2))
     ((ulongp val1) (bitior-ulong-ulong val1 val2))
     ((slongp val1) (bitior-slong-slong val1 val2))
     ((ullongp val1) (bitior-ullong-ullong val1 val2))
     ((sllongp val1) (bitior-sllong-sllong val1 val2))
     (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance values-of-uaconvert-values
                       (val1 arg1) (val2 arg2))
                 :in-theory (enable value-arithmeticp value-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-binary-strict-pure ((op binopp)
                                 (arg1 value-resultp)
                                 (arg2 value-resultp))
  :guard (and (binop-strictp op)
              (binop-purep op))
  :returns (result value-resultp)
  :short "Execute a binary expression with a strict pure operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the results of
     recursively executing the operand expressions,
     both of which must be considered because the operator is non-strict.")
   (xdoc::p
    "These operators are pure,
     so we just return a value as result (if there is no error)."))
  (b* ((arg1 (value-result-fix arg1))
       (arg2 (value-result-fix arg2))
       ((when (errorp arg1)) arg1)
       ((when (errorp arg2)) arg2))
    (case (binop-kind op)
      (:mul (exec-mul arg1 arg2))
      (:div (exec-div arg1 arg2))
      (:rem (exec-rem arg1 arg2))
      (:add (exec-add arg1 arg2))
      (:sub (exec-sub arg1 arg2))
      (:shl (exec-shl arg1 arg2))
      (:shr (exec-shr arg1 arg2))
      (:lt (exec-lt arg1 arg2))
      (:gt (exec-gt arg1 arg2))
      (:le (exec-le arg1 arg2))
      (:ge (exec-ge arg1 arg2))
      (:eq (exec-eq arg1 arg2))
      (:ne (exec-ne arg1 arg2))
      (:bitand (exec-bitand arg1 arg2))
      (:bitxor (exec-bitxor arg1 arg2))
      (:bitior (exec-bitior arg1 arg2))
      (t (error (impossible)))))
  :guard-hints (("Goal" :in-theory (enable binop-strictp binop-purep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-cast ((tyname tynamep) (arg value-resultp))
  :returns (result value-resultp)
  :short "Execute a cast expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support casts between integer types.
     None involving pointers.")
   (xdoc::p
    "We reject casts to @('void'),
     because a scalar type is required [C:6.5.4/2]."))
  (b* ((arg (value-result-fix arg))
       ((when (errorp arg)) arg)
       (type (type-name-to-type tyname))
       (err (error (list :cast-undefined :from arg :to type)))
       (todo (error (list :cast-todo :from arg :to type)))
       (void (error (list :cast-void :from arg :to type))))
    (cond ((ucharp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar arg
            :schar (if (schar-from-uchar-okp arg) (schar-from-uchar arg) err)
            :ushort (ushort-from-uchar arg)
            :sshort (if (sshort-from-uchar-okp arg) (sshort-from-uchar arg) err)
            :uint (uint-from-uchar arg)
            :sint (if (sint-from-uchar-okp arg) (sint-from-uchar arg) err)
            :ulong (ulong-from-uchar arg)
            :slong (if (slong-from-uchar-okp arg) (slong-from-uchar arg) err)
            :ullong (ullong-from-uchar arg)
            :sllong (if (sllong-from-uchar-okp arg) (sllong-from-uchar arg) err)
            :pointer todo))
          ((scharp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-schar arg)
            :schar arg
            :ushort (ushort-from-schar arg)
            :sshort (sshort-from-schar arg)
            :uint (uint-from-schar arg)
            :sint (sint-from-schar arg)
            :ulong (ulong-from-schar arg)
            :slong (slong-from-schar arg)
            :ullong (ullong-from-schar arg)
            :sllong (sllong-from-schar arg)
            :pointer todo))
          ((ushortp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-ushort arg)
            :schar (if (schar-from-ushort-okp arg) (schar-from-ushort arg) err)
            :ushort arg
            :sshort (if (sshort-from-ushort-okp arg) (sshort-from-ushort arg) err)
            :uint (uint-from-ushort arg)
            :sint (if (sint-from-ushort-okp arg) (sint-from-ushort arg) err)
            :ulong (ulong-from-ushort arg)
            :slong (if (slong-from-ushort-okp arg) (slong-from-ushort arg) err)
            :ullong (ullong-from-ushort arg)
            :sllong (if (sllong-from-ushort-okp arg) (sllong-from-ushort arg) err)
            :pointer todo))
          ((sshortp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-sshort arg)
            :schar (if (schar-from-sshort-okp arg) (schar-from-sshort arg) err)
            :ushort (ushort-from-sshort arg)
            :sshort arg
            :uint (uint-from-sshort arg)
            :sint (sint-from-sshort arg)
            :ulong (ulong-from-sshort arg)
            :slong (slong-from-sshort arg)
            :ullong (ullong-from-sshort arg)
            :sllong (sllong-from-sshort arg)
            :pointer todo))
          ((uintp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-uint arg)
            :schar (if (schar-from-uint-okp arg) (schar-from-uint arg) err)
            :ushort (ushort-from-uint arg)
            :sshort (if (sshort-from-uint-okp arg) (sshort-from-uint arg) err)
            :uint arg
            :sint (if (sint-from-uint-okp arg) (sint-from-uint arg) err)
            :ulong (ulong-from-uint arg)
            :slong (if (slong-from-uint-okp arg) (slong-from-uint arg) err)
            :ullong (ullong-from-uint arg)
            :sllong (if (sllong-from-uint-okp arg) (sllong-from-uint arg) err)
            :pointer todo))
          ((sintp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-sint arg)
            :schar (if (schar-from-sint-okp arg) (schar-from-sint arg) err)
            :ushort (ushort-from-sint arg)
            :sshort (if (sshort-from-sint-okp arg) (sshort-from-sint arg) err)
            :uint (uint-from-sint arg)
            :sint arg
            :ulong (ulong-from-sint arg)
            :slong (slong-from-sint arg)
            :ullong (ullong-from-sint arg)
            :sllong (sllong-from-sint arg)
            :pointer todo))
          ((ulongp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-ulong arg)
            :schar (if (schar-from-ulong-okp arg) (schar-from-ulong arg) err)
            :ushort (ushort-from-ulong arg)
            :sshort (if (sshort-from-ulong-okp arg) (sshort-from-ulong arg) err)
            :uint (uint-from-ulong arg)
            :sint (if (sint-from-ulong-okp arg) (sint-from-ulong arg) err)
            :ulong arg
            :slong (if (slong-from-ulong-okp arg) (slong-from-ulong arg) err)
            :ullong (ullong-from-ulong arg)
            :sllong (if (sllong-from-ulong-okp arg) (sllong-from-ulong arg) err)
            :pointer todo))
          ((slongp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-slong arg)
            :schar (if (schar-from-slong-okp arg) (schar-from-slong arg) err)
            :ushort (ushort-from-slong arg)
            :sshort (if (sshort-from-slong-okp arg) (sshort-from-slong arg) err)
            :uint (uint-from-slong arg)
            :sint (if (sint-from-slong-okp arg) (sint-from-slong arg) err)
            :ulong (ulong-from-slong arg)
            :slong arg
            :ullong (ullong-from-slong arg)
            :sllong (sllong-from-slong arg)
            :pointer todo))
          ((ullongp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-ullong arg)
            :schar (if (schar-from-ullong-okp arg) (schar-from-ullong arg) err)
            :ushort (ushort-from-ullong arg)
            :sshort (if (sshort-from-ullong-okp arg) (sshort-from-ullong arg) err)
            :uint (uint-from-ullong arg)
            :sint (if (sint-from-ullong-okp arg) (sint-from-ullong arg) err)
            :ulong (ulong-from-ullong arg)
            :slong (if (slong-from-ullong-okp arg) (slong-from-ullong arg) err)
            :ullong arg
            :sllong (if (sllong-from-ullong-okp arg) (sllong-from-ullong arg) err)
            :pointer todo))
          ((sllongp arg)
           (type-case
            type
            :void void
            :char todo
            :uchar (uchar-from-sllong arg)
            :schar (if (schar-from-sllong-okp arg) (schar-from-sllong arg) err)
            :ushort (ushort-from-sllong arg)
            :sshort (if (sshort-from-sllong-okp arg) (sshort-from-sllong arg) err)
            :uint (uint-from-sllong arg)
            :sint (if (sint-from-sllong-okp arg) (sint-from-sllong arg) err)
            :ulong (ulong-from-sllong arg)
            :slong (if (slong-from-sllong-okp arg) (slong-from-sllong arg) err)
            :ullong (ullong-from-sllong arg)
            :sllong arg
            :pointer todo))
          ((pointerp arg) todo)
          (t (error (impossible)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-arrsub ((arr value-resultp)
                     (sub value-resultp)
                     (compst compustatep))
  :returns (result value-resultp)
  :short "Execute an array subscripting expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first operand must be a pointer to an array.
     The second operand must be an integer value (of any integer type).
     The resulting index must be in range for the array,
     and the indexed element is returned as result."))
  (b* ((arr (value-result-fix arr))
       (sub (value-result-fix sub))
       ((when (errorp arr)) arr)
       ((when (errorp sub)) sub)
       ((unless (pointerp arr)) (error (list :mistype-array :array
                                             :required :pointer
                                             :supplied (type-of-value arr))))
       ((unless (value-integerp sub)) (error
                                       (list :mistype-array :index
                                             :required (type-sint)
                                             :supplied (type-of-value sub))))
       (array (read-array arr compst))
       ((when (errorp array))
        (error (list :array-not-found arr (compustate-fix compst))))
       (index (exec-integer sub))
       (err (error (list :array-index-out-of-range
                         :pointer arr
                         :array array
                         :index sub))))
    (cond ((uchar-arrayp array)
           (if (uchar-array-index-okp array index)
               (uchar-array-read array index)
             err))
          ((schar-arrayp array)
           (if (schar-array-index-okp array index)
               (schar-array-read array index)
             err))
          ((ushort-arrayp array)
           (if (ushort-array-index-okp array index)
               (ushort-array-read array index)
             err))
          ((sshort-arrayp array)
           (if (sshort-array-index-okp array index)
               (sshort-array-read array index)
             err))
          ((uint-arrayp array)
           (if (uint-array-index-okp array index)
               (uint-array-read array index)
             err))
          ((sint-arrayp array)
           (if (sint-array-index-okp array index)
               (sint-array-read array index)
             err))
          ((ulong-arrayp array)
           (if (ulong-array-index-okp array index)
               (ulong-array-read array index)
             err))
          ((slong-arrayp array)
           (if (slong-array-index-okp array index)
               (slong-array-read array index)
             err))
          ((ullong-arrayp array)
           (if (ullong-array-index-okp array index)
               (ullong-array-read array index)
             err))
          ((sllong-arrayp array)
           (if (sllong-array-index-okp array index)
               (sllong-array-read array index)
             err))
          (t (error (impossible)))))
  :guard-hints (("Goal"
                 :use (:instance array-resultp-of-read-array (ptr arr))
                 :in-theory (e/d (arrayp
                                  array-resultp)
                                 (array-resultp-of-read-array))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-expr-pure ((e exprp) (compst compustatep))
  :returns (result value-resultp)
  :short "Execute a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return an error if we encounter a non-pure expression.
     While function calls do not necessarily have side effects,
     establishing that requires looking at the function.
     Thus, for simplicity, we regard function calls to be non-pure,
     i.e. we return an error if we encounter them here.")
   (xdoc::p
    "We also reject pre/post-increment/decrement expressions,
     which are obviously non-pure.")
   (xdoc::p
    "Recall that our C abstract syntax does not cover
     all the possible C expressions yet.
     Thus, we may extend this ACL2 function
     with support for more kinds of pure expressions in the future.")
   (xdoc::p
    "If no error occurs, none of the expressions has side effects.
     Thus, the order in which the sub-expressions are evaluated does not matter:
     we just proceed left to right."))
  (b* ((e (expr-fix e)))
    (expr-case
     e
     :ident (exec-ident e.get compst)
     :const (exec-const e.get)
     :arrsub (exec-arrsub (exec-expr-pure e.arr compst)
                          (exec-expr-pure e.sub compst)
                          compst)
     :call (error (list :non-pure-expr e))
     :member (error (list :not-supported-yet e))
     :memberp (error (list :not-supported-yet e))
     :postinc (error (list :non-pure-expr e))
     :postdec (error (list :non-pure-expr e))
     :preinc (error (list :non-pure-expr e))
     :predec (error (list :non-pure-expr e))
     :unary (exec-unary e.op (exec-expr-pure e.arg compst))
     :cast (exec-cast e.type (exec-expr-pure e.arg compst))
     :binary (b* (((unless (binop-purep e.op)) (error (list :non-pure-expr e))))
               (case (binop-kind e.op)
                 (:logand
                  (b* ((test1 (exec-test (exec-expr-pure e.arg1 compst)))
                       ((when (errorp test1)) test1)
                       ((when (not test1)) (sint 0))
                       (test2 (exec-test (exec-expr-pure e.arg2 compst)))
                       ((when (errorp test2)) test2))
                    (if test2 (sint 1) (sint 0))))
                 (:logor
                  (b* ((test1 (exec-test (exec-expr-pure e.arg1 compst)))
                       ((when (errorp test1)) test1)
                       ((when test1) (sint 1))
                       (test2 (exec-test (exec-expr-pure e.arg2 compst)))
                       ((when (errorp test2)) test2))
                    (if test2 (sint 1) (sint 0))))
                 (t (exec-binary-strict-pure e.op
                                             (exec-expr-pure e.arg1 compst)
                                             (exec-expr-pure e.arg2 compst)))))
     :cond (b* ((test (exec-test (exec-expr-pure e.test compst)))
                ((when (errorp test)) test))
             (if test
                 (exec-expr-pure e.then compst)
               (exec-expr-pure e.else compst)))))
  :measure (expr-count e)
  :hooks (:fix)
  :verify-guards nil ; done below
  ///

  (defret value-resultp-of-exec-expr-pure-forward
    (value-resultp result)
    :rule-classes ((:forward-chaining
                    :trigger-terms ((exec-expr-pure e compst)))))

  (verify-guards exec-expr-pure
    :hints (("Goal" :in-theory (enable binop-strictp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-expr-pure-list ((es expr-listp) (compst compustatep))
  :returns (result
            value-list-resultp
            :hints (("Goal"
                     :in-theory
                     (enable
                      valuep-when-value-resultp-and-not-errorp
                      value-listp-when-value-list-resultp-and-not-errorp))))
  :short "Execute a list of pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used, in particular,
     for the argument expressions a function call.")
   (xdoc::p
    "Given that the expression have no side effects (if there is no error),
     the order of evaluation does not matter.
     Thus, we proceed left to right."))
  (b* (((when (endp es)) nil)
       (val (exec-expr-pure (car es) compst))
       ((when (errorp val)) val)
       (vals (exec-expr-pure-list (cdr es) compst))
       ((when (errorp vals)) vals))
    (cons val vals))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-scope ((formals param-declon-listp) (actuals value-listp))
  :returns (result scope-resultp
                   :hints (("Goal"
                            :in-theory
                            (enable scopep-when-scope-resultp-and-not-errorp))))
  :short "Initialize the variable scope for a function call."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through formal parameters and actual arguments,
     pairing them up into the scope.
     We return an error if they do not match in number or types,
     or if there are repeated parameters."))
  (b* ((formals (param-declon-list-fix formals))
       (actuals (value-list-fix actuals))
       ((when (endp formals))
        (if (endp actuals)
            nil
          (error (list :init-scope :extra-actuals actuals))))
       ((when (endp actuals))
        (error (list :init-scope :extra-formals formals)))
       (scope (init-scope (cdr formals) (cdr actuals)))
       ((when (errorp scope)) scope)
       (formal (car formals))
       (actual (car actuals))
       (declor (param-declon->declor formal))
       (pointerp (declor->pointerp declor))
       (name (declor->ident declor))
       (formal-type (type-name-to-type
                     (make-tyname :specs (param-declon->type formal)
                                  :pointerp pointerp)))
       (actual-type (type-of-value actual))
       ((unless (equal formal-type actual-type))
        (error (list :formal-actual-mistype
                     :name name
                     :formal formal-type
                     :actual actual-type))))
    (if (omap::in name scope)
        (error (list :init-scope :duplicate-param name))
      (omap::update name actual scope)))
  :hooks (:fix)
  :measure (len formals)
  :verify-guards nil ; done below
  ///
  (verify-guards init-scope))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exec
  :short "Mutually recursive functions for execution."
  :flag-local nil

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-expr-call ((fun identp)
                          (args expr-listp)
                          (compst compustatep)
                          (fenv fun-envp)
                          (limit natp))
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (atc-execution exec)
    :short "Execution a function call."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return an optional value,
       which is @('nil') for a function that returns @('void')."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (vals (exec-expr-pure-list args compst))
         ((when (errorp vals)) (mv vals (compustate-fix compst))))
      (exec-fun fun vals compst fenv (1- limit)))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-expr-call-or-pure ((e exprp)
                                  (compst compustatep)
                                  (fenv fun-envp)
                                  (limit natp))
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (atc-execution exec)
    :short "Execute a function call or a pure expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used for expressions that must be
       either function calls or pure.
       If the expression is a call, we use @(tsee exec-expr-call).
       Otherwise, we resort to @(tsee exec-expr-pure).")
     (xdoc::p
      "We return an optional value,
       which is @('nil') for a function that returns @('void')."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (e (expr-fix e)))
      (if (expr-case e :call)
          (exec-expr-call (expr-call->fun e)
                          (expr-call->args e)
                          compst
                          fenv
                          (1- limit))
        (mv (exec-expr-pure e compst)
            (compustate-fix compst))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-expr-asg ((e exprp)
                         (compst compustatep)
                         (fenv fun-envp)
                         (limit natp))
    :returns (new-compst compustate-resultp)
    :parents (atc-execution exec)
    :short "Execute an assignment expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used for expressions that must be assignments.
       For now we only support simple assignment expressions, with:")
     (xdoc::ul
      (xdoc::li
       "A left-hand side consisting of
        either a variable
        or an array subscripting expression where the array is a variable.")
      (xdoc::li
       "A right-hand side consisting of a function call or a pure expression."))
     (xdoc::p
      "We ensure that if the right-hand side expression is a function call,
       it returns a value (i.e. it is not @('void')).")
     (xdoc::p
      "We allow these assignment expressions
       as the expressions of expression statements.
       Thus, we discard the value of the assignment
       (which is the value written to the variable);
       this ACL2 function just returns an updated computation state."))
    (b* (((when (zp limit)) (error :limit))
         ((unless (expr-case e :binary))
          (error (list :expr-asg-not-binary (expr-fix e))))
         (op (expr-binary->op e))
         (left (expr-binary->arg1 e))
         (right (expr-binary->arg2 e))
         ((unless (binop-case op :asg))
          (error (list :expr-asg-not-asg op)))
         ((mv val? compst)
          (exec-expr-call-or-pure right compst fenv (1- limit)))
         ((when (errorp val?)) val?)
         ((when (not val?)) (error (list :asg-void-expr (expr-fix e))))
         (val val?))
      (case (expr-kind left)
        (:ident
         (b* ((var (expr-ident->get left)))
           (write-var var val compst)))
        (:arrsub
         (b* ((arr (expr-arrsub->arr left))
              (sub (expr-arrsub->sub left))
              ((unless (expr-case arr :ident))
               (error (list :expr-asg-arrsub-not-var left)))
              (var (expr-ident->get arr))
              (ptr (read-var var compst))
              ((when (errorp ptr)) ptr)
              ((unless (pointerp ptr))
               (error (list :mistype-array :array
                            :required :pointer
                            :supplied (type-of-value ptr))))
              (array (read-array ptr compst))
              ((when (errorp array)) array)
              (idx (exec-expr-pure sub compst))
              ((when (errorp idx)) idx)
              ((unless (value-integerp idx))
               (error (list :mistype-array-index
                            :required :integer
                            :found idx)))
              (index (exec-integer idx))
              (err-elem (error (list :mistype-array-write
                                     :required (type-of-value ptr)
                                     :found val)))
              (err-idx (error (list :array-index-out-of-range
                                    :pointer ptr
                                    :array array
                                    :index idx))))
           (cond ((uchar-arrayp array)
                  (b* (((unless (ucharp val)) err-elem)
                       ((unless (uchar-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (uchar-array-write array index val)
                                 compst)))
                 ((schar-arrayp array)
                  (b* (((unless (scharp val)) err-elem)
                       ((unless (schar-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (schar-array-write array index val)
                                 compst)))
                 ((ushort-arrayp array)
                  (b* (((unless (ushortp val)) err-elem)
                       ((unless (ushort-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (ushort-array-write array index val)
                                 compst)))
                 ((sshort-arrayp array)
                  (b* (((unless (sshortp val)) err-elem)
                       ((unless (sshort-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (sshort-array-write array index val)
                                 compst)))
                 ((uint-arrayp array)
                  (b* (((unless (uintp val)) err-elem)
                       ((unless (uint-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (uint-array-write array index val)
                                 compst)))
                 ((sint-arrayp array)
                  (b* (((unless (sintp val)) err-elem)
                       ((unless (sint-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (sint-array-write array index val)
                                 compst)))
                 ((ulong-arrayp array)
                  (b* (((unless (ulongp val)) err-elem)
                       ((unless (ulong-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (ulong-array-write array index val)
                                 compst)))
                 ((slong-arrayp array)
                  (b* (((unless (slongp val)) err-elem)
                       ((unless (slong-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (slong-array-write array index val)
                                 compst)))
                 ((ullong-arrayp array)
                  (b* (((unless (ullongp val)) err-elem)
                       ((unless (ullong-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (ullong-array-write array index val)
                                 compst)))
                 ((sllong-arrayp array)
                  (b* (((unless (sllongp val)) err-elem)
                       ((unless (sllong-array-index-okp array index)) err-idx))
                    (write-array ptr
                                 (sllong-array-write array index val)
                                 compst)))
                 (t (error :impossible)))))
        (t (error (list :expr-asg-left-not-var-or-array-var-subscript left)))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-fun ((fun identp)
                    (args value-listp)
                    (compst compustatep)
                    (fenv fun-envp)
                    (limit natp))
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (atc-execution exec)
    :short "Execute a function on argument values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We retrieve the information about the function from the environment.
       We initialize a scope with the argument values,
       and we push a frame onto the call stack.
       We execute the function body,
       which must return a result that matches the function's result type.
       We pop the frame and return the value of the function call as result."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (info (fun-env-lookup fun fenv))
         ((when (not info))
          (mv (error (list :function-undefined (ident-fix fun)))
              (compustate-fix compst)))
         ((fun-info info) info)
         (scope (init-scope info.params args))
         ((when (errorp scope)) (mv scope (compustate-fix compst)))
         (frame (make-frame :function fun :scopes (list scope)))
         (compst (push-frame frame compst))
         ((mv val? compst) (exec-block-item-list info.body
                                                 compst
                                                 fenv
                                                 (1- limit)))
         (compst (pop-frame compst))
         ((when (errorp val?)) (mv val? compst))
         ((unless (equal (type-of-value-option val?)
                         (type-name-to-type
                          (make-tyname :specs info.result
                                       :pointerp nil))))
          (mv (error (list :return-value-mistype
                           :required info.result
                           :supplied (type-of-value-option val?)))
              compst)))
      (mv val? compst))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-stmt ((s stmtp)
                     (compst compustatep)
                     (fenv fun-envp)
                     (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (atc-execution exec)
    :short "Execute a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we only support the execution of certain statements.")
     (xdoc::p
      "We only allow, and in fact require,
       assignment expressions in expression statements.")
     (xdoc::p
      "For a compound statement (i.e. a block),
       we enter a new (empty) scope prior to executing the block items,
       and we exit that scope after executing the block items."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (s (stmt-fix s)))
      (stmt-case
       s
       :labeled (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :compound (b* ((compst (enter-scope compst))
                      ((mv value? compst)
                       (exec-block-item-list s.items compst fenv (1- limit))))
                   (mv value? (exit-scope compst)))
       :expr (b* ((compst/error (exec-expr-asg s.get compst fenv (1- limit)))
                  ((when (errorp compst/error))
                   (mv compst/error (compustate-fix compst))))
               (mv nil compst/error))
       :null (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :if (b* ((test (exec-test (exec-expr-pure s.test compst)))
                ((when (errorp test)) (mv test (compustate-fix compst))))
             (if test
                 (exec-stmt s.then compst fenv (1- limit))
               (mv nil (compustate-fix compst))))
       :ifelse (b* ((test (exec-test (exec-expr-pure s.test compst)))
                    ((when (errorp test)) (mv test (compustate-fix compst))))
                 (if test
                     (exec-stmt s.then compst fenv (1- limit))
                   (exec-stmt s.else compst fenv (1- limit))))
       :switch (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :while (exec-stmt-while s.test s.body compst fenv (1- limit))
       :dowhile (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :for (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :goto (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :continue (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :break (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :return (if (exprp s.value)
                   (exec-expr-call-or-pure s.value compst fenv (1- limit))
                 (mv nil (compustate-fix compst)))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-stmt-while ((test exprp)
                           (body stmtp)
                           (compst compustatep)
                           (fenv fun-envp)
                           (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (atc-execution exec)
    :short "Execute a @('while') statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "First, we execute the test.
       If it yields a 0 scalar, we return a @('nil') value result,
       because it means that the loop completes,
       and execution can proceed with any code after the loop.
       Otherwise, we recursively execute the body.
       If the body returns a result,
       we return it from this ACL2 function without continuing the loop.
       If the body returns no result,
       we re-execute the loop,
       by calling this ACL2 function recursively."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (continuep (exec-test (exec-expr-pure test compst)))
         ((when (errorp continuep)) (mv continuep (compustate-fix compst)))
         ((when (not continuep)) (mv nil (compustate-fix compst)))
         ((mv val? compst) (exec-stmt body compst fenv (1- limit)))
         ((when (errorp val?)) (mv val? compst))
         ((when (valuep val?)) (mv val? compst)))
      (exec-stmt-while test body compst fenv (1- limit)))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-block-item ((item block-itemp)
                           (compst compustatep)
                           (fenv fun-envp)
                           (limit natp))
    :guard (and (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 0))
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (atc-execution exec)
    :short "Execute a block item."
    :long
    (xdoc::topstring
     (xdoc::p
      "Besides an optional value result,
       we also return a possibly updated computation state.")
     (xdoc::p
      "If the block item is a declaration,
       we ensure it is a variable (not a structure type) declaration,
       then we execute the expression,
       then we add the variable to the top scope of the top frame.
       The initializer value must have the same type as the variable,
       which automatically excludes the case of the variable being @('void'),
       since @(tsee type-of-value) never returns @('void')
       (under the guard).")
     (xdoc::p
      "If the block item is a statement,
       we execute it like any other statement."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst))))
      (block-item-case
       item
       :declon
       (b* (((unless (declon-case item.get :var))
             (mv (error (list :struct-declaration-in-block-item item.get))
                 (compustate-fix compst)))
            (type (declon-var->type item.get))
            (declor (declon-var->declor item.get))
            (init (declon-var->init item.get))
            ((mv init compst) (exec-expr-call-or-pure init
                                                      compst
                                                      fenv
                                                      (1- limit)))
            ((when (errorp init)) (mv init compst))
            ((when (not init))
             (mv (error (list :void-initializer (block-item-fix item)))
                 compst))
            (var (declor->ident declor))
            (pointerp (declor->pointerp declor))
            (type (type-name-to-type
                   (make-tyname :specs type
                                :pointerp pointerp)))
            ((unless (equal type (type-of-value init)))
             (mv (error (list :decl-var-mistype var
                              :required type
                              :supplied (type-of-value init)))
                 compst))
            (new-compst (create-var var init compst))
            ((when (errorp new-compst)) (mv new-compst compst)))
         (mv nil new-compst))
       :stmt (exec-stmt item.get compst fenv (1- limit))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-block-item-list ((items block-item-listp)
                                (compst compustatep)
                                (fenv fun-envp)
                                (limit natp))
    :guard (and (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 0))
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (atc-execution exec)
    :short "Execute a list of block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "We thread the computation state through the block items."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         ((when (endp items)) (mv nil (compustate-fix compst)))
         ((mv val? compst) (exec-block-item (car items) compst fenv (1- limit)))
         ((when (errorp val?)) (mv val? compst))
         ((when (valuep val?)) (mv val? compst)))
      (exec-block-item-list (cdr items) compst fenv (1- limit)))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :prepwork ((local
              (in-theory
               (enable
                value-optionp-when-value-option-resultp-and-not-errorp
                compustatep-when-compustate-resultp-and-not-errorp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below
  ///

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual compustate-frames-number-of-exec
    (defret compustate-frames-number-of-exec-expr-call
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :fn exec-expr-call)
    (defret compustate-frames-number-of-exec-expr-call-or-pure
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :fn exec-expr-call-or-pure)
    (defret compustate-frames-number-of-exec-expr-asg
      (implies (compustatep new-compst)
               (equal (compustate-frames-number new-compst)
                      (compustate-frames-number compst)))
      :fn exec-expr-asg)
    (defret compustate-frames-number-of-exec-fun
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :fn exec-fun)
    (defret compustate-frames-number-of-exec-stmt
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt)
    (defret compustate-frames-number-of-exec-stmt-while
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt-while)
    (defret compustate-frames-number-of-exec-block-item
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-block-item)
    (defret compustate-frames-number-of-exec-block-item-list
      (equal (compustate-frames-number new-compst)
             (compustate-frames-number compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-block-item-list)
    :hints (("Goal" :expand ((exec-expr-call fun args compst fenv limit)
                             (exec-expr-call-or-pure e compst fenv limit)
                             (exec-expr-asg e compst fenv limit)
                             (exec-fun fun args compst fenv limit)
                             (exec-stmt s compst fenv limit)
                             (exec-block-item item compst fenv limit)
                             (exec-block-item-list items compst fenv limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual compustate-scopes-numbers-of-exec
    (defret compustate-scopes-numbers-of-exec-expr-call
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :fn exec-expr-call)
    (defret compustate-scopes-numbers-of-exec-expr-call-or-pure
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :fn exec-expr-call-or-pure)
    (defret compustate-scopes-numbers-of-exec-expr-asg
      (implies (compustatep new-compst)
               (equal (compustate-scopes-numbers new-compst)
                      (compustate-scopes-numbers compst)))
      :fn exec-expr-asg)
    (defret compustate-scopes-numbers-of-exec-fun
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :rule-classes nil
      :fn exec-fun)
    (defret compustate-scopes-numbers-of-exec-stmt
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt)
    (defret compustate-scopes-numbers-of-exec-stmt-while
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (> (compustate-frames-number compst) 0)
      :fn exec-stmt-while)
    (defret compustate-scopes-numbers-of-exec-block-item
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (and (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 0))
      :fn exec-block-item)
    (defret compustate-scopes-numbers-of-exec-block-item-list
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (and (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 0))
      :fn exec-block-item-list)
    :hints (("Goal" :expand ((exec-expr-call fun args compst fenv limit)
                             (exec-expr-call-or-pure e compst fenv limit)
                             (exec-expr-asg e compst fenv limit)
                             (exec-fun fun args compst fenv limit)
                             (exec-stmt s compst fenv limit)
                             (exec-stmt-while test body compst fenv limit)
                             (exec-block-item item compst fenv limit)
                             (exec-block-item-list items compst fenv limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards exec-stmt)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual exec))
