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

(include-book "../execution")

(include-book "syntaxp")
(include-book "promote-value")
(include-book "uaconvert-values")
(include-book "integer-conversions")
(include-book "value-integer-get")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x)
                  x)))

(defrulel truncate-lemma
  (implies (and (natp a)
                (natp b))
           (and (<= 0
                    (truncate a (expt 2 b)))
                (<= (truncate a (expt 2 b))
                    a)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-sint-get-rules
  :short "Rules about the composition of @(tsee sint->get)
          with @('sint-from-<type>') functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are not used during the symbolic execution;
     they are used to prove rules used during the symbolic execution."))

  (defruled sint->get-of-sint-from-schar
    (equal (sint->get (sint-from-schar x))
           (schar->get x))
    :enable (sint-from-schar
             sint-integerp-alt-def))

  (defruled sint->get-of-sint-from-uchar
    (equal (sint->get (sint-from-uchar x))
           (uchar->get x))
    :enable (sint-from-uchar
             sint-integerp-alt-def))

  (defruled sint->get-of-sint-from-sshort
    (equal (sint->get (sint-from-sshort x))
           (sshort->get x))
    :enable (sint-from-sshort
             sint-integerp-alt-def))

  (defruled sint->get-of-sint-from-ushort
    (equal (sint->get (sint-from-ushort x))
           (ushort->get x))
    :enable (sint-from-ushort
             sint-integerp-alt-def))

  (defval *atc-sint-get-rules*
    '(sint->get-of-sint-from-schar
      sint->get-of-sint-from-uchar
      sint->get-of-sint-from-sshort
      sint->get-of-sint-from-ushort)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-binary-strict-pure-rules-generation
  :short "Code to generate the rules for executing
          strict pure binary operations."

  (define atc-exec-binary-rules-gen-op-ltype-rtype ((op binopp)
                                                    (ltype typep)
                                                    (rtype typep))
    :guard (and (type-nonchar-integerp ltype)
                (type-nonchar-integerp rtype))
    :returns (mv (name symbolp) (event pseudo-event-formp))
    :parents nil
    (b* ((lfixtype (integer-type-to-fixtype ltype))
         (rfixtype (integer-type-to-fixtype rtype))
         (rpred (pack rfixtype 'p))
         (op-kind (binop-kind op))
         (exec-op (pack 'exec- op-kind))
         (op-values (pack op-kind '-values))
         (op-arithmetic-values (and (or (binop-case op :div)
                                        (binop-case op :mul)
                                        (binop-case op :rem)
                                        (binop-case op :add)
                                        (binop-case op :sub))
                                    (pack op-kind '-arithmetic-values)))
         (op-integer-values (pack op-kind '-integer-values))
         (exec-binary-strict-pure-of-op-and-ltype
          (pack 'exec-binary-strict-pure-of- op-kind '-and- lfixtype))
         (type (uaconvert-types ltype rtype))
         (promotedp (and (member-eq op-kind '(:shl :shr))
                         (member-eq (type-kind ltype)
                                    '(:schar :uchar :sshort :ushort))))
         (name (pack exec-binary-strict-pure-of-op-and-ltype '-when- rfixtype))
         (op-ltype-rtype (pack op-kind '- lfixtype '- rfixtype))
         (op-type-type (pack op-kind '- (type-kind type) '- (type-kind type)))
         (op-type-type-okp (pack op-type-type '-okp))
         (op-ltype-rtype-okp (and (or (member-eq op-kind
                                                 '(:div :rem :shl :shr))
                                      (and (member-eq op-kind
                                                      '(:add :sub :mul))
                                           (type-signed-integerp type)))
                                  (pack op-ltype-rtype '-okp)))
         (op-ltype (and (member-eq op-kind '(:shl :shr))
                        (pack op-kind '- (type-kind ltype))))
         (op-ltype-okp (and op-ltype
                            (pack op-ltype '-okp)))
         (formula `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'y)
                                 (,rpred y)
                                 ,@(and op-ltype-rtype-okp
                                        `((,op-ltype-rtype-okp x y))))
                            (equal
                             (,exec-binary-strict-pure-of-op-and-ltype x y)
                             (,op-ltype-rtype x y))))
         (enables (if (member-eq (binop-kind op) '(:mul :div :rem :add :sub
                                                   :shl :shr))
                      `(,exec-binary-strict-pure-of-op-and-ltype
                        ,op-values
                        ,@(and op-arithmetic-values
                               (list op-arithmetic-values))
                        ,op-integer-values
                        ,op-ltype-rtype
                        ,@(and op-ltype
                               (list op-ltype))
                        ,@(and (member-eq op-kind '(:mul :div :rem :add :sub))
                               (or (not (equal type ltype))
                                   (not (equal type rtype)))
                               (list op-type-type))
                        ,@(and promotedp
                               (list (pack op-kind '-sint)))
                        ,@(and op-ltype-rtype-okp
                               (list op-ltype-rtype-okp))
                        ,@(and op-ltype-okp
                               (list op-ltype-okp))
                        ,@(and (member-eq op-kind '(:mul :div :rem :add :sub))
                               op-ltype-rtype-okp
                               (or (not (equal type ltype))
                                   (not (equal type rtype)))
                               (list op-type-type-okp))
                        ,@(and promotedp
                               (list (pack op-kind '-sint-okp)))
                        ,@*atc-uaconvert-values-rules*
                        ,@*atc-promote-value-rules*
                        result-integer-value
                        ,@*atc-value-integer->get-rules*
                        ,@(and (member-eq op-kind '(:shl :shr))
                               *atc-sint-get-rules*)
                        ,@(and (member-eq op-kind '(:shl :shr))
                               (list 'integer-type-bits))
                        value-integer
                        value-sint-to-sint
                        value-uint-to-uint
                        value-slong-to-slong
                        value-ulong-to-ulong
                        value-sllong-to-sllong
                        value-ullong-to-ullong
                        sint-integerp-alt-def
                        uint-integerp-alt-def
                        slong-integerp-alt-def
                        ulong-integerp-alt-def
                        sllong-integerp-alt-def
                        ullong-integerp-alt-def
                        uint-mod
                        ulong-mod
                        ullong-mod
                        value-unsigned-integerp-alt-def
                        integer-type-rangep
                        integer-type-min
                        integer-type-max)
                    `(,exec-binary-strict-pure-of-op-and-ltype
                      ,exec-op
                      ,@(and (or (not (equal type ltype))
                                 (not (equal type rtype))
                                 (member-eq op-kind '(:shl :shr)))
                             (list op-ltype-rtype))
                      ,@(and op-ltype-rtype-okp
                             (or (not (equal type ltype))
                                 (not (equal type rtype))
                                 (member-eq op-kind '(:shl :shr)))
                             (list op-ltype-rtype-okp))
                      ,@(and (member-eq op-kind '(:shl :shr))
                             (not (equal ltype (promote-type ltype)))
                             (list
                              (pack op-kind '- lfixtype)
                              (pack op-kind '- lfixtype '-okp)))
                      ,@(and (member-eq op-kind '(:shl :shr))
                             (append *atc-value-integer->get-rules*
                                     *atc-sint-get-rules*))
                      ,@*atc-uaconvert-values-rules*
                      ,@*atc-promote-value-rules*)))
         (event `(defruled ,name
                   ,formula
                   :enable ,enables
                   :disable (truncate
                             rem
                             floor
                             mod
                             ifix))))
      (mv name event))
    :guard-hints (("Goal" :in-theory (enable type-arithmeticp type-realp))))

  (define atc-exec-binary-rules-gen-op-ltype ((op binopp)
                                              (ltype typep)
                                              (rtypes type-listp))
    :guard (and (type-nonchar-integerp ltype)
                (type-nonchar-integer-listp rtypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp rtypes)) (mv nil nil))
         ((mv name event)
          (atc-exec-binary-rules-gen-op-ltype-rtype op ltype (car rtypes)))
         ((mv names events)
          (atc-exec-binary-rules-gen-op-ltype op ltype (cdr rtypes))))
      (mv (cons name names) (cons event events))))

  (define atc-exec-binary-rules-gen-op ((op binopp)
                                        (ltypes type-listp)
                                        (rtypes type-listp))
    :guard (and (type-nonchar-integer-listp ltypes)
                (type-nonchar-integer-listp rtypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp ltypes)) (mv nil nil))
         (ltype (car ltypes))
         (lfixtype (integer-type-to-fixtype ltype))
         (lpred (pack lfixtype 'p))
         (ltype-fix (pack lfixtype '-fix))
         (op-kind (binop-kind op))
         (exec-op (if (member-eq (binop-kind op) '(:mul :div :rem :add :sub
                                                   :shl :shr))
                      (pack op-kind '-values)
                    (pack 'exec- op-kind)))
         (exec-binary-strict-pure-of-op
          (pack 'exec-binary-strict-pure-of- op-kind))
         (exec-binary-strict-pure-of-op-and-ltype
          (pack 'exec-binary-strict-pure-of- op-kind '-and- lfixtype))
         (exec-binary-strict-pure-of-op-when-ltype
          (pack 'exec-binary-strict-pure-of- op-kind '-when- lfixtype))
         (fun-event
          `(defund ,exec-binary-strict-pure-of-op-and-ltype (x y)
             (b* ((y (value-result-fix y))
                  ((when (errorp y)) y))
               (,exec-op (,ltype-fix x) y))))
         (thm-event
          `(defruled ,exec-binary-strict-pure-of-op-when-ltype
             (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                           (,lpred x))
                      (equal (,exec-binary-strict-pure-of-op x y)
                             (,exec-binary-strict-pure-of-op-and-ltype x y)))
             :enable (,exec-binary-strict-pure-of-op
                      ,exec-binary-strict-pure-of-op-and-ltype)))
         ((mv names events)
          (atc-exec-binary-rules-gen-op-ltype op (car ltypes) rtypes))
         ((mv more-names more-events)
          (atc-exec-binary-rules-gen-op op (cdr ltypes) rtypes)))
      (mv (append (list exec-binary-strict-pure-of-op-when-ltype)
                  names
                  more-names)
          (append (list fun-event thm-event)
                  events
                  more-events))))

  (define atc-exec-binary-rules-gen ((ops binop-listp)
                                     (ltypes type-listp)
                                     (rtypes type-listp))
    :guard (and (type-nonchar-integer-listp ltypes)
                (type-nonchar-integer-listp rtypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp ops)) (mv nil nil))
         (op (car ops))
         (op-kind (binop-kind op))
         (exec-op (if (member-eq (binop-kind op) '(:mul :div :rem :add :sub
                                                   :shl :shr))
                      (pack op-kind '-values)
                    (pack 'exec- op-kind)))
         (exec-binary-strict-pure-of-op
          (pack 'exec-binary-strict-pure-of- op-kind))
         (exec-binary-strict-pure-when-op
          (pack 'exec-binary-strict-pure-when- op-kind))
         (fun-event
          `(defund ,exec-binary-strict-pure-of-op (x y)
             (b* ((x (value-result-fix x))
                  (y (value-result-fix y))
                  ((when (errorp x)) x)
                  ((when (errorp y)) y))
               (,exec-op x y))))
         (thm-event
          `(defruled ,exec-binary-strict-pure-when-op
             (implies (and (equal op (,(pack 'binop- op-kind))))
                      (equal (exec-binary-strict-pure op x y)
                             (,exec-binary-strict-pure-of-op x y)))
             :enable (exec-binary-strict-pure
                      ,exec-binary-strict-pure-of-op)))
         ((mv names events)
          (atc-exec-binary-rules-gen-op op ltypes rtypes))
         ((mv more-names more-events)
          (atc-exec-binary-rules-gen (cdr ops) ltypes rtypes)))
      (mv (append (list exec-binary-strict-pure-when-op)
                  names
                  more-names)
          (append (list fun-event thm-event)
                  events
                  more-events))))

  (define atc-exec-binary-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* ((ops (list (binop-mul)
                    (binop-div)
                    (binop-rem)
                    (binop-add)
                    (binop-sub)
                    (binop-shl)
                    (binop-shr)
                    (binop-lt)
                    (binop-gt)
                    (binop-le)
                    (binop-ge)
                    (binop-eq)
                    (binop-ne)
                    (binop-bitand)
                    (binop-bitxor)
                    (binop-bitior)))
         ((mv names events)
          (atc-exec-binary-rules-gen ops
                                     *nonchar-integer-types**
                                     *nonchar-integer-types**)))
      `(progn
         (defsection atc-exec-binary-strict-pure-rules
           :short "Rules for executing strict pure binary operations."
           :long
           (xdoc::topstring
            (xdoc::p
             "The goal of these rules is to
              rewrite @('(exec-binary-strict-pure op x y)')
              to @('(op-type1-type2 x y)')
              when @('x') has type @('type1'),
              and @('y') has type @('type2').
              We could have a rule for each combination of
              @('op'), @('type1'), and @('type2'),
              but that would lead to 1,600 rules being applicable to
              @('(exec-binary-strict-pure op x y)').
              So we stage the rewriting as follows:")
            (xdoc::ul
             (xdoc::li
              "First, we rewrite @('(exec-binary-strict-pure op x y)')
               to a call @('(exec-binary-strict-pure-of-op x y)'),
               under the hypothesis that @('op') is a specific operator,
               where @('exec-binary-strict-pure-of-op') is one of 16 functions,
               one per binary strict operator.")
             (xdoc::li
              "Next, we rewrite @('(exec-binary-strict-pure-of-op x y)')
               to a call @('(exec-binary-strict-pure-of-op-and-type1 x y)'),
               under the hypothesis that @('x') has type @('type1'),
               where @('exec-binary-strict-pure-of-op-and-type1')
               is one of 10 functions,
               one per supported integer type.")
             (xdoc::li
              "Finally, we rewrite
               @('(exec-binary-strict-pure-of-op-and-type1 x y)')
               to the call @('(op-type1-type2 x y)'),
               under the hypothesis the @('y') has type @('type2'),
               for each of the 10 supported integer types."))
            (xdoc::p
             "Note that the intermediate functions used here
              do not need guard verification."))
           ,@events
           (defval *atc-exec-binary-strict-pure-rules*
             '(,@names
               (:e binop-mul)
               (:e binop-div)
               (:e binop-rem)
               (:e binop-add)
               (:e binop-sub)
               (:e binop-shl)
               (:e binop-shr)
               (:e binop-lt)
               (:e binop-gt)
               (:e binop-le)
               (:e binop-ge)
               (:e binop-eq)
               (:e binop-ne)
               (:e binop-bitand)
               (:e binop-bitxor)
               (:e binop-bitior))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-binary-rules-gen-all))



(atc-exec-binary-rules-gen (list (binop-shl))
                           (list (type-uchar))
                           (list (type-uchar)))



(progn
  (DEFUND EXEC-BINARY-STRICT-PURE-OF-SHL (X Y)
    (B* ((X (VALUE-RESULT-FIX X))
         (Y (VALUE-RESULT-FIX Y))
         ((WHEN (ERRORP X)) X)
         ((WHEN (ERRORP Y)) Y))
      (SHL-VALUES X Y)))
  (DEFRULED EXEC-BINARY-STRICT-PURE-WHEN-SHL
    (IMPLIES (AND (EQUAL OP (BINOP-SHL)))
             (EQUAL (EXEC-BINARY-STRICT-PURE OP X Y)
                    (EXEC-BINARY-STRICT-PURE-OF-SHL X Y)))
    :ENABLE (EXEC-BINARY-STRICT-PURE EXEC-BINARY-STRICT-PURE-OF-SHL))
  (DEFUND EXEC-BINARY-STRICT-PURE-OF-SHL-AND-UCHAR
    (X Y)
    (B* ((Y (VALUE-RESULT-FIX Y))
         ((WHEN (ERRORP Y)) Y))
      (SHL-VALUES (UCHAR-FIX X) Y)))
  (DEFRULED
    EXEC-BINARY-STRICT-PURE-OF-SHL-WHEN-UCHAR
    (IMPLIES
     (AND
      (SYNTAXP
       (OR (ATOM X)
           (NOT (MEMBER-EQ X
                           '(EXEC-IDENT EXEC-CONST
                                        EXEC-ICONST EXEC-ARRSUB EXEC-MEMBER
                                        EXEC-MEMBERP EXEC-ARRSUB-OF-MEMBER
                                        EXEC-ARRSUB-OF-MEMBERP EXEC-UNARY
                                        EXEC-CAST EXEC-BINARY-STRICT-PURE
                                        EXEC-EXPR-PURE TEST-VALUE)))))
      (UCHARP X))
     (EQUAL (EXEC-BINARY-STRICT-PURE-OF-SHL X Y)
            (EXEC-BINARY-STRICT-PURE-OF-SHL-AND-UCHAR X Y)))
    :ENABLE
    (EXEC-BINARY-STRICT-PURE-OF-SHL EXEC-BINARY-STRICT-PURE-OF-SHL-AND-UCHAR)))


(DEFRULED
  EXEC-BINARY-STRICT-PURE-OF-SHL-AND-UCHAR-WHEN-UCHAR
  (IMPLIES
   (AND
    (SYNTAXP
     (OR (ATOM Y)
         (NOT (MEMBER-EQ Y
                         '(EXEC-IDENT EXEC-CONST
                                      EXEC-ICONST EXEC-ARRSUB EXEC-MEMBER
                                      EXEC-MEMBERP EXEC-ARRSUB-OF-MEMBER
                                      EXEC-ARRSUB-OF-MEMBERP EXEC-UNARY
                                      EXEC-CAST EXEC-BINARY-STRICT-PURE
                                      EXEC-EXPR-PURE TEST-VALUE)))))
    (UCHARP Y)
    (SHL-UCHAR-UCHAR-OKP X Y))
   (EQUAL (EXEC-BINARY-STRICT-PURE-OF-SHL-AND-UCHAR X Y)
          (SHL-UCHAR-UCHAR X Y)))
  :ENABLE (EXEC-BINARY-STRICT-PURE-OF-SHL-AND-UCHAR
           SHL-VALUES
           SHL-INTEGER-VALUES SHL-UCHAR-UCHAR
           SHL-UCHAR SHL-SINT SHL-UCHAR-UCHAR-OKP
           SHL-UCHAR-OKP SHL-SINT-OKP
           UACONVERT-VALUES-WHEN-SCHARP-AND-SCHARP
           UACONVERT-VALUES-WHEN-SCHARP-AND-UCHARP
           UACONVERT-VALUES-WHEN-SCHARP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-SCHARP-AND-USHORTP
           UACONVERT-VALUES-WHEN-SCHARP-AND-SINTP
           UACONVERT-VALUES-WHEN-SCHARP-AND-UINTP
           UACONVERT-VALUES-WHEN-SCHARP-AND-SLONGP
           UACONVERT-VALUES-WHEN-SCHARP-AND-ULONGP
           UACONVERT-VALUES-WHEN-SCHARP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-SCHARP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-UCHARP-AND-SCHARP
           UACONVERT-VALUES-WHEN-UCHARP-AND-UCHARP
           UACONVERT-VALUES-WHEN-UCHARP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-UCHARP-AND-USHORTP
           UACONVERT-VALUES-WHEN-UCHARP-AND-SINTP
           UACONVERT-VALUES-WHEN-UCHARP-AND-UINTP
           UACONVERT-VALUES-WHEN-UCHARP-AND-SLONGP
           UACONVERT-VALUES-WHEN-UCHARP-AND-ULONGP
           UACONVERT-VALUES-WHEN-UCHARP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-UCHARP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-SCHARP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-UCHARP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-USHORTP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-SINTP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-UINTP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-SLONGP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-ULONGP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-SSHORTP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-USHORTP-AND-SCHARP
           UACONVERT-VALUES-WHEN-USHORTP-AND-UCHARP
           UACONVERT-VALUES-WHEN-USHORTP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-USHORTP-AND-USHORTP
           UACONVERT-VALUES-WHEN-USHORTP-AND-SINTP
           UACONVERT-VALUES-WHEN-USHORTP-AND-UINTP
           UACONVERT-VALUES-WHEN-USHORTP-AND-SLONGP
           UACONVERT-VALUES-WHEN-USHORTP-AND-ULONGP
           UACONVERT-VALUES-WHEN-USHORTP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-USHORTP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-SINTP-AND-SCHARP
           UACONVERT-VALUES-WHEN-SINTP-AND-UCHARP
           UACONVERT-VALUES-WHEN-SINTP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-SINTP-AND-USHORTP
           UACONVERT-VALUES-WHEN-SINTP-AND-SINTP
           UACONVERT-VALUES-WHEN-SINTP-AND-UINTP
           UACONVERT-VALUES-WHEN-SINTP-AND-SLONGP
           UACONVERT-VALUES-WHEN-SINTP-AND-ULONGP
           UACONVERT-VALUES-WHEN-SINTP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-SINTP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-UINTP-AND-SCHARP
           UACONVERT-VALUES-WHEN-UINTP-AND-UCHARP
           UACONVERT-VALUES-WHEN-UINTP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-UINTP-AND-USHORTP
           UACONVERT-VALUES-WHEN-UINTP-AND-SINTP
           UACONVERT-VALUES-WHEN-UINTP-AND-UINTP
           UACONVERT-VALUES-WHEN-UINTP-AND-SLONGP
           UACONVERT-VALUES-WHEN-UINTP-AND-ULONGP
           UACONVERT-VALUES-WHEN-UINTP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-UINTP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-SLONGP-AND-SCHARP
           UACONVERT-VALUES-WHEN-SLONGP-AND-UCHARP
           UACONVERT-VALUES-WHEN-SLONGP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-SLONGP-AND-USHORTP
           UACONVERT-VALUES-WHEN-SLONGP-AND-SINTP
           UACONVERT-VALUES-WHEN-SLONGP-AND-UINTP
           UACONVERT-VALUES-WHEN-SLONGP-AND-SLONGP
           UACONVERT-VALUES-WHEN-SLONGP-AND-ULONGP
           UACONVERT-VALUES-WHEN-SLONGP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-SLONGP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-ULONGP-AND-SCHARP
           UACONVERT-VALUES-WHEN-ULONGP-AND-UCHARP
           UACONVERT-VALUES-WHEN-ULONGP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-ULONGP-AND-USHORTP
           UACONVERT-VALUES-WHEN-ULONGP-AND-SINTP
           UACONVERT-VALUES-WHEN-ULONGP-AND-UINTP
           UACONVERT-VALUES-WHEN-ULONGP-AND-SLONGP
           UACONVERT-VALUES-WHEN-ULONGP-AND-ULONGP
           UACONVERT-VALUES-WHEN-ULONGP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-ULONGP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-SCHARP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-UCHARP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-USHORTP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-SINTP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-UINTP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-SLONGP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-ULONGP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-SLLONGP-AND-ULLONGP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-SCHARP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-UCHARP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-SSHORTP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-USHORTP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-SINTP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-UINTP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-SLONGP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-ULONGP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-SLLONGP
           UACONVERT-VALUES-WHEN-ULLONGP-AND-ULLONGP
           PROMOTE-VALUE-WHEN-SCHARP
           PROMOTE-VALUE-WHEN-UCHARP
           PROMOTE-VALUE-WHEN-SSHORTP
           PROMOTE-VALUE-WHEN-USHORTP
           PROMOTE-VALUE-WHEN-SINTP
           PROMOTE-VALUE-WHEN-UINTP
           PROMOTE-VALUE-WHEN-SLONGP
           PROMOTE-VALUE-WHEN-ULONGP
           PROMOTE-VALUE-WHEN-SLLONGP
           PROMOTE-VALUE-WHEN-ULLONGP
           RESULT-INTEGER-VALUE
           VALUE-INTEGER->GET-WHEN-SCHARP
           VALUE-INTEGER->GET-WHEN-UCHARP
           VALUE-INTEGER->GET-WHEN-SSHORTP
           VALUE-INTEGER->GET-WHEN-USHORTP
           VALUE-INTEGER->GET-WHEN-SINTP
           VALUE-INTEGER->GET-WHEN-UINTP
           VALUE-INTEGER->GET-WHEN-SLONGP
           VALUE-INTEGER->GET-WHEN-ULONGP
           VALUE-INTEGER->GET-WHEN-SLLONGP
           VALUE-INTEGER->GET-WHEN-ULLONGP
           SINT->GET-OF-SINT-FROM-SCHAR
           SINT->GET-OF-SINT-FROM-UCHAR
           SINT->GET-OF-SINT-FROM-SSHORT
           SINT->GET-OF-SINT-FROM-USHORT
           INTEGER-TYPE-BITS
           VALUE-INTEGER VALUE-SINT-TO-SINT
           VALUE-UINT-TO-UINT VALUE-SLONG-TO-SLONG
           VALUE-ULONG-TO-ULONG
           VALUE-SLLONG-TO-SLLONG
           VALUE-ULLONG-TO-ULLONG
           SINT-INTEGERP-ALT-DEF
           UINT-INTEGERP-ALT-DEF
           SLONG-INTEGERP-ALT-DEF
           ULONG-INTEGERP-ALT-DEF
           SLLONG-INTEGERP-ALT-DEF
           ULLONG-INTEGERP-ALT-DEF
           UINT-MOD ULONG-MOD ULLONG-MOD
           VALUE-UNSIGNED-INTEGERP-ALT-DEF
           INTEGER-TYPE-RANGEP
           INTEGER-TYPE-MIN INTEGER-TYPE-MAX)
  :DISABLE (TRUNCATE REM FLOOR MOD IFIX
                     equal-of-sint
                     equal-of-error
                     equal-of-uint
                     equal-of-sllong
                     equal-of-slong
                     equal-of-ullong
                     equal-of-ulong
                     equal-of-value-schar
                     equal-of-value-sshort
                     equal-of-value-uchar
                     equal-of-value-ushort

                     ))
