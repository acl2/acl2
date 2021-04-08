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
(include-book "integer-conversions")

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
  (b* ((ic (iconst-fix ic))
       ((iconst ic) ic))
    (if ic.unsignedp
        (iconst-tysuffix-case
         ic.type
         :none (cond ((uint-integerp ic.value) (uint ic.value))
                     ((ulong-integerp ic.value) (ulong ic.value))
                     ((ullong-integerp ic.value) (ullong ic.value))
                     (t (error (list :iconst-out-of-range ic))))
         :long (cond ((ulong-integerp ic.value) (ulong ic.value))
                     ((ullong-integerp ic.value) (ullong ic.value))
                     (t (error (list :iconst-out-of-range ic))))
         :llong (cond ((ullong-integerp ic.value) (ullong ic.value))
                      (t (error (list :iconst-out-of-range ic)))))
      (iconst-tysuffix-case
       ic.type
       :none (if (iconst-base-case ic.base :dec)
                 (cond ((sint-integerp ic.value) (sint ic.value))
                       ((slong-integerp ic.value) (slong ic.value))
                       ((sllong-integerp ic.value) (sllong ic.value))
                       (t (error (list :iconst-out-of-range ic))))
               (cond ((sint-integerp ic.value) (sint ic.value))
                     ((uint-integerp ic.value) (uint ic.value))
                     ((slong-integerp ic.value) (slong ic.value))
                     ((ulong-integerp ic.value) (ulong ic.value))
                     ((sllong-integerp ic.value) (sllong ic.value))
                     ((ullong-integerp ic.value) (ullong ic.value))
                     (t (error (list :iconst-out-of-range ic)))))
       :long (if (iconst-base-case ic.base :dec)
                 (cond ((slong-integerp ic.value) (slong ic.value))
                       ((sllong-integerp ic.value) (sllong ic.value))
                       (t (error (list :iconst-out-of-range ic))))
               (cond ((slong-integerp ic.value) (slong ic.value))
                     ((ulong-integerp ic.value) (ulong ic.value))
                     ((sllong-integerp ic.value) (sllong ic.value))
                     ((ullong-integerp ic.value) (ullong ic.value))
                     (t (error (list :iconst-out-of-range ic)))))
       :llong (if (iconst-base-case ic.base :dec)
                  (cond ((sllong-integerp ic.value) (sllong ic.value))
                        (t (error (list :iconst-out-of-range ic))))
                (cond ((sllong-integerp ic.value) (sllong ic.value))
                      ((ullong-integerp ic.value) (ullong ic.value))
                      (t (error (list :iconst-out-of-range ic))))))))
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
                                    sint-from-schar-okp
                                    sint-from-ushort-okp
                                    sint-from-sshort-okp
                                    ucharp
                                    scharp
                                    ushortp
                                    sshortp
                                    uchar->get
                                    schar->get
                                    ushort->get
                                    sshort->get
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
    :enable (promote-value
             value-arithmeticp
             value-realp
             value-integerp
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
    (cond ((uintp val) (uint-plus val))
          ((sintp val) (sint-plus val))
          ((ulongp val) (ulong-plus val))
          ((slongp val) (slong-plus val))
          ((ullongp val) (ullong-plus val))
          ((sllongp val) (sllong-plus val))
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
    (cond ((uintp val) (uint-minus val))
          ((sintp val) (if (sint-minus-okp val) (sint-minus val) err))
          ((ulongp val) (ulong-minus val))
          ((slongp val) (if (slong-minus-okp val) (slong-minus val) err))
          ((ullongp val) (ullong-minus val))
          ((sllongp val) (if (sllong-minus-okp val) (sllong-minus val) err))
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
    (cond ((uintp val) (uint-bitnot val))
          ((sintp val) (sint-bitnot val))
          ((ulongp val) (ulong-bitnot val))
          ((slongp val) (slong-bitnot val))
          ((ullongp val) (ullong-bitnot val))
          ((sllongp val) (sllong-bitnot val))
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
    (cond ((ucharp arg) (uchar-lognot arg))
          ((scharp arg) (schar-lognot arg))
          ((ushortp arg) (ushort-lognot arg))
          ((sshortp arg) (sshort-lognot arg))
          ((uintp arg) (uint-lognot arg))
          ((sintp arg) (sint-lognot arg))
          ((ulongp arg) (ulong-lognot arg))
          ((slongp arg) (slong-lognot arg))
          ((ullongp arg) (ullong-lognot arg))
          ((sllongp arg) (sllong-lognot arg))
          ((pointerp arg) (sint01 (pointer-nullp arg)))
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
                 :in-theory (enable slong-from-sint-okp
                                    slong-from-uint-okp
                                    sllong-from-sint-okp
                                    sllong-from-slong-okp
                                    sllong-from-uint-okp
                                    sllong-from-ulong-okp
                                    sintp
                                    slongp
                                    sllongp
                                    uintp
                                    ulongp
                                    ullongp
                                    sint->get
                                    slong->get
                                    uint->get
                                    ulong->get
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
     ((uintp val1) (uint-mul val1 val2))
     ((sintp val1) (if (sint-mul-okp val1 val2) (sint-mul val1 val2) err))
     ((ulongp val1) (ulong-mul val1 val2))
     ((slongp val1) (if (slong-mul-okp val1 val2) (slong-mul val1 val2) err))
     ((ullongp val1) (ullong-mul val1 val2))
     ((sllongp val1) (if (sllong-mul-okp val1 val2) (sllong-mul val1 val2) err))
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
     ((uintp val1) (if (uint-div-okp val1 val2) (uint-div val1 val2) err))
     ((sintp val1) (if (sint-div-okp val1 val2) (sint-div val1 val2) err))
     ((ulongp val1) (if (ulong-div-okp val1 val2) (ulong-div val1 val2) err))
     ((slongp val1) (if (slong-div-okp val1 val2) (slong-div val1 val2) err))
     ((ullongp val1) (if (ullong-div-okp val1 val2) (ullong-div val1 val2) err))
     ((sllongp val1) (if (sllong-div-okp val1 val2) (sllong-div val1 val2) err))
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
     ((uintp val1) (if (uint-rem-okp val1 val2) (uint-rem val1 val2) err))
     ((sintp val1) (if (sint-rem-okp val1 val2) (sint-rem val1 val2) err))
     ((ulongp val1) (if (ulong-rem-okp val1 val2) (ulong-rem val1 val2) err))
     ((slongp val1) (if (slong-rem-okp val1 val2) (slong-rem val1 val2) err))
     ((ullongp val1) (if (ullong-rem-okp val1 val2) (ullong-rem val1 val2) err))
     ((sllongp val1) (if (sllong-rem-okp val1 val2) (sllong-rem val1 val2) err))
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
     ((uintp val1) (uint-add val1 val2))
     ((sintp val1) (if (sint-add-okp val1 val2) (sint-add val1 val2) err))
     ((ulongp val1) (ulong-add val1 val2))
     ((slongp val1) (if (slong-add-okp val1 val2) (slong-add val1 val2) err))
     ((ullongp val1) (ullong-add val1 val2))
     ((sllongp val1) (if (sllong-add-okp val1 val2) (sllong-add val1 val2) err))
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
     ((uintp val1) (uint-sub val1 val2))
     ((sintp val1) (if (sint-sub-okp val1 val2) (sint-sub val1 val2) err))
     ((ulongp val1) (ulong-sub val1 val2))
     ((slongp val1) (if (slong-sub-okp val1 val2) (slong-sub val1 val2) err))
     ((ullongp val1) (ullong-sub val1 val2))
     ((sllongp val1) (if (sllong-sub-okp val1 val2) (sllong-sub val1 val2) err))
     (t (error (impossible)))))
  :guard-hints (("Goal" :use (:instance values-of-uaconvert-values
                              (val1 arg1) (val2 arg2))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-shl ((arg1 valuep) (arg2 valuep))
  :returns (result value-resultp)
  :short "Execute left shifts [C:6.5.7/2] [C:6.5.7/3] [C:6.5.7/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support operands with the same promoted type."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-integerp arg1))
        (error (list :mistype-shl
                     :required :integer
                     :supplied arg1)))
       ((unless (value-integerp arg2))
        (error (list :mistype-shl
                     :required :integer
                     :supplied arg2)))
       (err (error (list :undefined-shl arg1 arg2)))
       (val1 (promote-value arg1))
       (val2 (promote-value arg2)))
    (cond
     ((uintp val1) (if (uintp val2)
                       (if (uint-shl-uint-okp val1 val2)
                           (uint-shl-uint val1 val2)
                         err)
                     (error :todo)))
     ((sintp val1) (if (sintp val2)
                       (if (sint-shl-sint-okp val1 val2)
                           (sint-shl-sint val1 val2)
                         err)
                     (error :todo)))
     ((ulongp val1) (if (ulongp val2)
                        (if (ulong-shl-ulong-okp val1 val2)
                            (ulong-shl-ulong val1 val2)
                          err)
                      (error :todo)))
     ((slongp val1) (if (slongp val2)
                        (if (slong-shl-slong-okp val1 val2)
                            (slong-shl-slong val1 val2)
                          err)
                      (error :todo)))
     ((ullongp val1) (if (ullongp val2)
                         (if (ullong-shl-ullong-okp val1 val2)
                             (ullong-shl-ullong val1 val2)
                           err)
                       (error :todo)))
     ((sllongp val1) (if (sllongp val2)
                         (if (sllong-shl-sllong-okp val1 val2)
                             (sllong-shl-sllong val1 val2)
                           err)
                       (error :todo)))
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
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support operands with the same promoted type."))
  (b* ((arg1 (value-fix arg1))
       (arg2 (value-fix arg2))
       ((unless (value-integerp arg1))
        (error (list :mistype-shr
                     :required :integer
                     :supplied arg1)))
       ((unless (value-integerp arg2))
        (error (list :mistype-shr
                     :required :integer
                     :supplied arg2)))
       (err (error (list :undefined-shr arg1 arg2)))
       (val1 (promote-value arg1))
       (val2 (promote-value arg2)))
    (cond
     ((uintp val1) (if (uintp val2)
                       (if (uint-shr-uint-okp val1 val2)
                           (uint-shr-uint val1 val2)
                         err)
                     (error :todo)))
     ((sintp val1) (if (sintp val2)
                       (if (sint-shr-sint-okp val1 val2)
                           (sint-shr-sint val1 val2)
                         err)
                     (error :todo)))
     ((ulongp val1) (if (ulongp val2)
                        (if (ulong-shr-ulong-okp val1 val2)
                            (ulong-shr-ulong val1 val2)
                          err)
                      (error :todo)))
     ((slongp val1) (if (slongp val2)
                        (if (slong-shr-slong-okp val1 val2)
                            (slong-shr-slong val1 val2)
                          err)
                      (error :todo)))
     ((ullongp val1) (if (ullongp val2)
                         (if (ullong-shr-ullong-okp val1 val2)
                             (ullong-shr-ullong val1 val2)
                           err)
                       (error :todo)))
     ((sllongp val1) (if (sllongp val2)
                         (if (sllong-shr-sllong-okp val1 val2)
                             (sllong-shr-sllong val1 val2)
                           err)
                       (error :todo)))
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
     ((uintp val1) (uint-lt val1 val2))
     ((sintp val1) (sint-lt val1 val2))
     ((ulongp val1) (ulong-lt val1 val2))
     ((slongp val1) (slong-lt val1 val2))
     ((ullongp val1) (ullong-lt val1 val2))
     ((sllongp val1) (sllong-lt val1 val2))
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
     ((uintp val1) (uint-gt val1 val2))
     ((sintp val1) (sint-gt val1 val2))
     ((ulongp val1) (ulong-gt val1 val2))
     ((slongp val1) (slong-gt val1 val2))
     ((ullongp val1) (ullong-gt val1 val2))
     ((sllongp val1) (sllong-gt val1 val2))
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
     ((uintp val1) (uint-le val1 val2))
     ((sintp val1) (sint-le val1 val2))
     ((ulongp val1) (ulong-le val1 val2))
     ((slongp val1) (slong-le val1 val2))
     ((ullongp val1) (ullong-le val1 val2))
     ((sllongp val1) (sllong-le val1 val2))
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
     ((uintp val1) (uint-ge val1 val2))
     ((sintp val1) (sint-ge val1 val2))
     ((ulongp val1) (ulong-ge val1 val2))
     ((slongp val1) (slong-ge val1 val2))
     ((ullongp val1) (ullong-ge val1 val2))
     ((sllongp val1) (sllong-ge val1 val2))
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
     ((uintp val1) (uint-eq val1 val2))
     ((sintp val1) (sint-eq val1 val2))
     ((ulongp val1) (ulong-eq val1 val2))
     ((slongp val1) (slong-eq val1 val2))
     ((ullongp val1) (ullong-eq val1 val2))
     ((sllongp val1) (sllong-eq val1 val2))
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
     ((uintp val1) (uint-ne val1 val2))
     ((sintp val1) (sint-ne val1 val2))
     ((ulongp val1) (ulong-ne val1 val2))
     ((slongp val1) (slong-ne val1 val2))
     ((ullongp val1) (ullong-ne val1 val2))
     ((sllongp val1) (sllong-ne val1 val2))
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
     ((uintp val1) (uint-bitand val1 val2))
     ((sintp val1) (sint-bitand val1 val2))
     ((ulongp val1) (ulong-bitand val1 val2))
     ((slongp val1) (slong-bitand val1 val2))
     ((ullongp val1) (ullong-bitand val1 val2))
     ((sllongp val1) (sllong-bitand val1 val2))
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
     ((uintp val1) (uint-bitxor val1 val2))
     ((sintp val1) (sint-bitxor val1 val2))
     ((ulongp val1) (ulong-bitxor val1 val2))
     ((slongp val1) (slong-bitxor val1 val2))
     ((ullongp val1) (ullong-bitxor val1 val2))
     ((sllongp val1) (sllong-bitxor val1 val2))
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
     ((uintp val1) (uint-bitior val1 val2))
     ((sintp val1) (sint-bitior val1 val2))
     ((ulongp val1) (ulong-bitior val1 val2))
     ((slongp val1) (slong-bitior val1 val2))
     ((ullongp val1) (ullong-bitior val1 val2))
     ((sllongp val1) (sllong-bitior val1 val2))
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
     so we just return a value as result (if there is no error).")
   (xdoc::p
    "We temporarily disallow @('unsigned char') values,
     by returning an error when we encounter them
     (this rejects valid programs, but does not accept invalid ones).
     We will add support for @('unsigned char') values later."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-test ((arg value-resultp))
  :returns (result bool-resultp)
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
    (cond ((ucharp arg) (uchar-nonzerop arg))
          ((scharp arg) (schar-nonzerop arg))
          ((ushortp arg) (ushort-nonzerop arg))
          ((sshortp arg) (sshort-nonzerop arg))
          ((uintp arg) (uint-nonzerop arg))
          ((sintp arg) (sint-nonzerop arg))
          ((ulongp arg) (ulong-nonzerop arg))
          ((slongp arg) (slong-nonzerop arg))
          ((ullongp arg) (ullong-nonzerop arg))
          ((sllongp arg) (sllong-nonzerop arg))
          ((pointerp arg) (pointer-nullp arg))
          (t (error (impossible)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-binary-logand ((arg1 value-resultp) (arg2 value-resultp))
  :returns (result value-resultp)
  :short "Execute a binary logical conjunction expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the results of
     recursively executing the operand expressions.
     However, since this operator is non-strict,
     we ignore the result of the second operand
     if the result of the first operand is 0,
     and return 0 in this case.
     Otherwise, we look at the result of the second operand,
     and return 0 or 1 depending on whether it is 0 or non-0.")
   (xdoc::p
    "Note that this binary operator is non-strict but pure."))
  (b* ((arg1 (value-result-fix arg1))
       (arg2 (value-result-fix arg2)))
    (cond ((errorp arg1) arg1)
          ((ucharp arg1) (error (list :exec-logand-uchar-todo arg1)))
          ((scharp arg1) (error (list :exec-logand-schar-todo arg1)))
          ((ushortp arg1) (error (list :exec-logand-ushort-todo arg1)))
          ((sshortp arg1) (error (list :exec-logand-sshort-todo arg1)))
          ((uintp arg1) (error (list :exec-logand-uint-todo arg1)))
          ((sintp arg1)
           (cond ((not (sint-nonzerop arg1)) (sint 0))
                 ((errorp arg2) arg2)
                 ((ucharp arg2) (error (list :exec-logand-uchar-todo arg2)))
                 ((scharp arg2) (error (list :exec-logand-schar-todo arg2)))
                 ((ushortp arg2) (error (list :exec-logand-ushort-todo arg2)))
                 ((sshortp arg2) (error (list :exec-logand-sshort-todo arg2)))
                 ((uintp arg2) (error (list :exec-logand-uint-todo arg2)))
                 ((sintp arg2) (sint01 (sint-nonzerop arg2)))
                 ((ulongp arg2) (error (list :exec-logand-ulong-todo arg2)))
                 ((slongp arg2) (error (list :exec-logand-slong-todo arg2)))
                 ((ullongp arg2) (error (list :exec-logand-ullong-todo arg2)))
                 ((sllongp arg2) (error (list :exec-logand-sllong-todo arg2)))
                 ((pointerp arg2) (error (list :exec-logand-pointer-todo arg2)))
                 (t (error (impossible)))))
          ((ulongp arg1) (error (list :exec-logand-ulong-todo arg1)))
          ((slongp arg1) (error (list :exec-logand-slong-todo arg1)))
          ((ullongp arg1) (error (list :exec-logand-ullong-todo arg1)))
          ((sllongp arg1) (error (list :exec-logand-sllong-todo arg1)))
          ((pointerp arg1) (error (list :exec-logand-pointer-todo arg1)))
          (t (error (impossible)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-binary-logor ((arg1 value-resultp) (arg2 value-resultp))
  :returns (result value-resultp)
  :short "Execute a binary logical disjunction expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the results of
     recursively executing the operand expressions.
     However, since this operator is non-strict,
     we ignore the result of the second operand
     if the result of the first operand is non-0,
     and return 1 in this case.
     Otherwise, we look at the result of the second operand,
     and return 0 or 1 depending on whether it is 0 or non-0.")
   (xdoc::p
    "Note that this binary operator is non-strict but pure."))
  (b* ((arg1 (value-result-fix arg1))
       (arg2 (value-result-fix arg2)))
    (cond ((errorp arg1) arg1)
          ((ucharp arg1) (error (list :exec-logor-uchar-todo arg1)))
          ((scharp arg1) (error (list :exec-logor-schar-todo arg1)))
          ((ushortp arg1) (error (list :exec-logor-ushort-todo arg1)))
          ((sshortp arg1) (error (list :exec-logor-sshort-todo arg1)))
          ((uintp arg1) (error (list :exec-logor-uint-todo arg1)))
          ((sintp arg1)
           (cond ((sint-nonzerop arg1) (sint 1))
                 ((errorp arg2) arg2)
                 ((ucharp arg2) (error (list :exec-logor-uchar-todo arg2)))
                 ((scharp arg2) (error (list :exec-logor-schar-todo arg2)))
                 ((ushortp arg2) (error (list :exec-logor-ushort-todo arg2)))
                 ((sshortp arg2) (error (list :exec-logor-sshort-todo arg2)))
                 ((uintp arg2) (error (list :exec-logor-uint-todo arg2)))
                 ((sintp arg2) (sint01 (sint-nonzerop arg2)))
                 ((ulongp arg2) (error (list :exec-logor-ulong-todo arg2)))
                 ((slongp arg2) (error (list :exec-logor-slong-todo arg2)))
                 ((ullongp arg2) (error (list :exec-logor-ullong-todo arg2)))
                 ((sllongp arg2) (error (list :exec-logor-sllong-todo arg2)))
                 ((pointerp arg2) (error (list :exec-logor-pointer-todo arg2)))
                 (t (error (impossible)))))
          ((ulongp arg1) (error (list :exec-logor-ulong-todo arg1)))
          ((slongp arg1) (error (list :exec-logor-slong-todo arg1)))
          ((ullongp arg1) (error (list :exec-logor-ullong-todo arg1)))
          ((sllongp arg1) (error (list :exec-logor-sllong-todo arg1)))
          ((pointerp arg1) (error (list :exec-logor-pointer arg1)))
          (t (error (impossible)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-binary-pure ((op binopp) (arg1 value-resultp) (arg2 value-resultp))
  :guard (binop-purep op)
  :returns (result value-resultp)
  :short "Execute a pure binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we only define the execution of pure binary operators.
     Assignments is handled in @(tsee exec-expr-asg)."))
  (if (binop-strictp op)
      (exec-binary-strict-pure op arg1 arg2)
    (case (binop-kind op)
      (:logand (exec-binary-logand arg1 arg2))
      (:logor (exec-binary-logor arg1 arg2))
      (t (error (impossible)))))
  :guard-hints (("Goal" :in-theory (enable binop-purep binop-strictp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-cast ((tyname tynamep) (arg value-resultp))
  :returns (result value-resultp)
  :short "Execute a cast expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support conversions
     between @('int')s and @('unsigned char')s."))
  (b* ((arg (value-result-fix arg))
       ((when (errorp arg)) arg)
       (type (type-name-to-type tyname)))
    (cond ((type-case type :uchar)
           (cond ((ucharp arg) arg)
                 ((scharp arg) (error
                                (list :cast-not-supported :from arg :to type)))
                 ((ushortp arg) (error
                                 (list :cast-not-supported :from arg :to type)))
                 ((sshortp arg) (error
                                 (list :cast-not-supported :from arg :to type)))
                 ((uintp arg) (error
                               (list :cast-not-supported :from arg :to type)))
                 ((sintp arg) (uchar-from-sint arg))
                 ((ulongp arg) (error
                                (list :cast-not-supported :from arg :to type)))
                 ((slongp arg) (error
                                (list :cast-not-supported :from arg :to type)))
                 ((ullongp arg) (error
                                 (list :cast-not-supported :from arg :to type)))
                 ((sllongp arg) (error
                                 (list :cast-not-supported :from arg :to type)))
                 ((pointerp arg) (error
                                  (list :cast-not-supported :from arg :to type)))
                 (t (error (impossible)))))
          ((type-case type :sint)
           (cond ((sintp arg) arg)
                 ((ucharp arg) (if (sint-from-uchar-okp arg)
                                   (sint-from-uchar arg)
                                 (error (list :cast-not-representable
                                              :from arg :to type))))
                 ((scharp arg) (error
                                (list :cast-not-supported :from arg :to type)))
                 ((ushortp arg) (error
                                 (list :cast-not-supported :from arg :to type)))
                 ((sshortp arg) (error
                                 (list :cast-not-supported :from arg :to type)))
                 ((uintp arg) (error
                               (list :cast-not-supported :from arg :to type)))
                 ((sintp arg) (error
                               (list :cast-not-supported :from arg :to type)))
                 ((ulongp arg) (error
                                (list :cast-not-supported :from arg :to type)))
                 ((slongp arg) (error
                                (list :cast-not-supported :from arg :to type)))
                 ((ullongp arg) (error
                                 (list :cast-not-supported :from arg :to type)))
                 ((sllongp arg) (error
                                 (list :cast-not-supported :from arg :to type)))
                 ((pointerp arg) (error
                                  (list :cast-pointer-not-supported
                                        :from arg :to type)))
                 (t (error (impossible)))))
          (t (error (list :cast-not-supported :from arg :to type)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-arrsub ((arr value-resultp) (sub value-resultp) (heap heapp))
  :returns (result value-resultp)
  :short "Execute an array subscripting expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first operand must be a pointer that can be derefenced
     (this means that it must be a non-null pointer to @('unsigned char');
     see @(tsee deref)),
     obtaining an array.
     The second operand must be an @('int'),
     which is a bit more restrictive than [C18],
     which allows any integer;
     we will relax this at some point.
     The resulting index must be in range for the array,
     and the indexed element is returned as result."))
  (b* ((arr (value-result-fix arr))
       (sub (value-result-fix sub))
       ((when (errorp arr)) arr)
       ((when (errorp sub)) sub)
       ((unless (pointerp arr)) (error (list :mistype-array :array
                                             :required :pointer
                                             :supplied (type-of-value arr))))
       ((unless (sintp sub)) (error (list :mistype-array :index
                                          :required (type-sint)
                                          :supplied (type-of-value sub))))
       (array (deref arr heap))
       ((when (errorp array))
        (error (list :array-not-found arr (heap-fix heap))))
       ((unless (uchar-array-sint-index-okp array sub))
        (error (list :array-index-out-of-range
                     :pointer arr
                     :array array
                     :index sub))))
    (uchar-array-read-sint array sub))
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
    "For now we reject cast expressions just for lack of support,
     but eventually we will support them, since they are pure.")
   (xdoc::p
    "For now we reject tests of conditionals
     that are non-@('int') values.
     We will add support for them later.")
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
     :arrsub (b* ((arr (exec-expr-pure e.arr compst))
                  (sub (exec-expr-pure e.sub compst)))
               (exec-arrsub arr sub (compustate->heap compst)))
     :call (error (list :non-pure-expr e))
     :postinc (error (list :non-pure-expr e))
     :postdec (error (list :non-pure-expr e))
     :preinc (error (list :non-pure-expr e))
     :predec (error (list :non-pure-expr e))
     :unary (b* ((arg (exec-expr-pure e.arg compst)))
              (exec-unary e.op arg))
     :cast (exec-cast e.type (exec-expr-pure e.arg compst))
     :binary (b* (((unless (binop-purep e.op))
                   (error (list :non-pure-expr e)))
                  (arg1 (exec-expr-pure e.arg1 compst))
                  (arg2 (exec-expr-pure e.arg2 compst)))
               (exec-binary-pure e.op arg1 arg2))
     :cond (b* ((test (exec-expr-pure e.test compst))
                ((when (errorp test)) test)
                ((when (ucharp test)) (error
                                       (list :exec-cond-uchar-todo e)))
                ((when (scharp test)) (error
                                       (list :exec-cond-schar-todo e)))
                ((when (ushortp test)) (error
                                       (list :exec-cond-ushort-todo e)))
                ((when (sshortp test)) (error
                                        (list :exec-cond-sshort-todo e)))
                ((when (uintp test)) (error
                                      (list :exec-cond-uint-todo e)))
                ((when (ulongp test)) (error
                                       (list :exec-cond-ulong-todo e)))
                ((when (slongp test)) (error
                                        (list :exec-cond-slong-todo e)))
                ((when (ullongp test)) (error
                                       (list :exec-cond-ullong-todo e)))
                ((when (sllongp test)) (error
                                        (list :exec-cond-sllong-todo e)))
                ((when (pointerp test)) (error
                                         (list :exec-cond-pointer-todo e)))
                ((unless (mbt (sintp test))) (error (impossible))))
             (if (sint-nonzerop test)
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

  (verify-guards exec-expr-pure))

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
     or if there are repeated parameters.")
   (xdoc::p
    "For now we return an error if we encounter a pointer declarator."))
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

  (define exec-expr-call-or-pure ((e exprp)
                                  (compst compustatep)
                                  (fenv fun-envp)
                                  (limit natp))
    :returns (mv (result value-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute a function call or a pure expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used for expressions that must be
       either function calls or pure.
       If the expression is a call, we handle it here.
       Otherwise, we resort to @(tsee exec-expr-pure)."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
         (e (expr-fix e)))
      (if (expr-case e :call)
          (b* ((e.args (expr-call->args e))
               (e.fun (expr-call->fun e))
               (args (exec-expr-pure-list e.args compst))
               ((when (errorp args)) (mv args (compustate-fix compst))))
            (exec-fun e.fun args compst fenv (1- limit)))
        (mv (exec-expr-pure e compst)
            (compustate-fix compst))))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-expr-asg ((e exprp)
                         (compst compustatep)
                         (fenv fun-envp)
                         (limit natp))
    :returns (new-compst compustate-resultp)
    :parents (dynamic-semantics exec)
    :short "Execute an assignment expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is only used for expressions that must be assignments,
       whose left subexpression is a variable
       and whose right subexpression is a function call or pure;
       this is what we support for now.")
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
         ((unless (expr-case left :ident))
          (error (list :expr-asg-left-not-var left)))
         (var (expr-ident->get left))
         ((mv val compst)
          (exec-expr-call-or-pure right compst fenv (1- limit)))
         ((when (errorp val)) val))
      (write-var var val compst))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-fun ((fun identp)
                    (args value-listp)
                    (compst compustatep)
                    (fenv fun-envp)
                    (limit natp))
    :returns (mv (result value-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execution a function on argument values."
    :long
    (xdoc::topstring
     (xdoc::p
      "We retrieve the information about the function from the environment.
       We initialize a scope with the argument values,
       and we push a frame onto the call stack.
       We execute the function body,
       which must return a result,,
       which must match the function's result type.
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
         ((mv val-opt compst) (exec-stmt info.body compst fenv (1- limit)))
         (compst (pop-frame compst))
         ((when (errorp val-opt)) (mv val-opt compst)))
      (if val-opt
          (if (equal (type-of-value val-opt)
                     (type-name-to-type
                      (make-tyname :specs info.result
                                   :pointerp nil)))
              (mv val-opt compst)
            (mv (error (list :return-value-mistype
                             :required info.result
                             :supplied (type-of-value val-opt)))
                compst))
        (mv (error (list :no-return-value (ident-fix fun)))
            compst)))
    :measure (nfix limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define exec-stmt ((s stmtp)
                     (compst compustatep)
                     (fenv fun-envp)
                     (limit natp))
    :guard (> (compustate-frames-number compst) 0)
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
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
       :if (b* ((test (exec-expr-pure s.test compst))
                ((when (errorp test)) (mv test (compustate-fix compst))))
             (if (sintp test)
                 (if (sint-nonzerop test)
                     (exec-stmt s.then compst fenv (1- limit))
                   (mv nil (compustate-fix compst)))
               (mv (error (list :exec-if-non-sint-todo s))
                   (compustate-fix compst))))
       :ifelse (b* ((test (exec-expr-pure s.test compst))
                    ((when (errorp test)) (mv test (compustate-fix compst))))
                 (if (sintp test)
                     (if (sint-nonzerop test)
                         (exec-stmt s.then compst fenv (1- limit))
                       (exec-stmt s.else compst fenv (1- limit)))
                   (mv (error (list :exec-ifelse-non-sint-todo s))
                       (compustate-fix compst))))
       :switch (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :while (mv (error (list :exec-stmt s)) (compustate-fix compst))
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

  (define exec-block-item ((item block-itemp)
                           (compst compustatep)
                           (fenv fun-envp)
                           (limit natp))
    :guard (and (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 1))
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
    :short "Execute a block item."
    :long
    (xdoc::topstring
     (xdoc::p
      "Besides an optional value result,
       we also return a possibly updated computation state.")
     (xdoc::p
      "If the block item is a declaration,
       we first execute the expression,
       then we add the variable to the top scope of the top frame.
       The initializer value must have the same type as the variable.")
     (xdoc::p
      "If the block item is a statement,
       we execute it like any other statement."))
    (b* (((when (zp limit)) (mv (error :limit) (compustate-fix compst))))
      (block-item-case
       item
       :declon (b* (((declon declon) item.get)
                    ((mv init compst) (exec-expr-call-or-pure declon.init
                                                              compst
                                                              fenv
                                                              (1- limit)))
                    ((when (errorp init)) (mv init compst))
                    (var (declor->ident declon.declor))
                    (pointerp (declor->pointerp declon.declor))
                    (type (type-name-to-type
                           (make-tyname :specs declon.type
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
                (> (compustate-top-frame-scopes-number compst) 1))
    :returns (mv (result value-option-resultp)
                 (new-compst compustatep))
    :parents (dynamic-semantics exec)
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
    :hints (("Goal" :expand ((exec-expr-call-or-pure e compst fenv limit)
                             (exec-expr-asg e compst fenv limit)
                             (exec-fun fun args compst fenv limit)
                             (exec-stmt s compst fenv limit)
                             (exec-block-item item compst fenv limit)
                             (exec-block-item-list items compst fenv limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual compustate-scopes-numbers-of-exec
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
    (defret compustate-scopes-numbers-of-exec-block-item
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (and (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 1))
      :fn exec-block-item)
    (defret compustate-scopes-numbers-of-exec-block-item-list
      (equal (compustate-scopes-numbers new-compst)
             (compustate-scopes-numbers compst))
      :hyp (and (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 1))
      :fn exec-block-item-list)
    :hints (("Goal" :expand ((exec-expr-call-or-pure e compst fenv limit)
                             (exec-expr-asg e compst fenv limit)
                             (exec-fun fun args compst fenv limit)
                             (exec-stmt s compst fenv limit)
                             (exec-block-item item compst fenv limit)
                             (exec-block-item-list items compst fenv limit)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards exec-stmt)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual exec))
