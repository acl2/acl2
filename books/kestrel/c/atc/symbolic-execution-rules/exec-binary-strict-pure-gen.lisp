; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/dynamic-semantics")

(include-book "../../representation/integer-operations")

(include-book "syntaxp")
(include-book "promote-value")
(include-book "uaconvert-values")
(include-book "integer-conversions")
(include-book "value-integer-get")
(include-book "apconvert")


(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-sint-get-rules
  :short "Rules about the composition of @(tsee integer-from-sint)
          with @('sint-from-<type>') functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are not used during the symbolic execution;
     they are used to prove rules used during the symbolic execution."))

  (defruled integer-from-sint-of-sint-from-schar
    (equal (integer-from-sint (sint-from-schar x))
           (integer-from-schar x))
    :enable (sint-from-schar
             sint-integerp-alt-def))

  (defruled integer-from-sint-of-sint-from-uchar
    (equal (integer-from-sint (sint-from-uchar x))
           (integer-from-uchar x))
    :enable (sint-from-uchar
             sint-integerp-alt-def
             bit-width-value-choices))

  (defruled integer-from-sint-of-sint-from-sshort
    (equal (integer-from-sint (sint-from-sshort x))
           (integer-from-sshort x))
    :enable (sint-from-sshort
             sint-integerp-alt-def))

  (defruled integer-from-sint-of-sint-from-ushort
    (equal (integer-from-sint (sint-from-ushort x))
           (integer-from-ushort x))
    :enable (sint-from-ushort
             sint-integerp-alt-def
             bit-width-value-choices))

  (defval *atc-sint-get-rules*
    '(integer-from-sint-of-sint-from-schar
      integer-from-sint-of-sint-from-uchar
      integer-from-sint-of-sint-from-sshort
      integer-from-sint-of-sint-from-ushort)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-binary-strict-pure-rules-generation
  :short "Code to generate the rules for executing
          strict pure binary operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since there are 16 binary operations and 10 integer types,
     there are 1600 instances of these rules.
     Generating all of them in the same file takes a bit of time;
     for example, a machine takes about 300 seconds to process all of them,
     which is actually less than 0.2 seconds for each instance,
     which is not particularly slow, but things add up.")
   (xdoc::p
    "So we split the generation across 16 files, one per operation,
     to take advantage of parallel certification.
     Each file contains a @(tsee make-event) form that generates
     (i) the rules for the operation,
     (ii) a named constant with the rules of the operation, and
     (iii) a named constant with the rule events.
     The argument of the @(tsee make-event) is
     a call of @('atc-exec-binary-rules-for-op-gen') defined in this file.
     Then the top-level file @('exec-binary-strict-pure-rules.lisp')
     puts together all the rule names,
     and generates a @(tsee defsection) with all the rule events,
     which are redundant and so are processed quickly,
     but in that way all the rules appear in XDOC."))

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
         (op-values (pack op-kind '-values))
         (op-arithmetic-values (and (or (binop-case op :div)
                                        (binop-case op :mul)
                                        (binop-case op :rem)
                                        (binop-case op :add)
                                        (binop-case op :sub)
                                        (binop-case op :eq)
                                        (binop-case op :ne))
                                    (pack op-kind '-arithmetic-values)))
         (op-real-values (and (or (binop-case op :lt)
                                  (binop-case op :gt)
                                  (binop-case op :le)
                                  (binop-case op :ge))
                              (pack op-kind '-real-values)))
         (op-integer-values (pack op-kind '-integer-values))
         (op-ltype-and-value (pack op-kind '- lfixtype '-and-value))
         (type (uaconvert-types ltype rtype))
         (promotedp (and (member-eq op-kind '(:shl :shr))
                         (member-eq (type-kind ltype)
                                    '(:schar :uchar :sshort :ushort))))
         (name (pack op-ltype-and-value '-when- rfixtype))
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
                            (equal (,op-ltype-and-value x y)
                                   (,op-ltype-rtype x y))))
         (enables `(,op-ltype-and-value
                    ,@(if (member-eq op-kind '(:shl :shr))
                          '(shl-values-to-shl-integer-values
                            shr-values-to-shr-integer-values
                            value-integerp-when-scharp
                            value-integerp-when-ucharp
                            value-integerp-when-sshortp
                            value-integerp-when-ushortp
                            value-integerp-when-sintp
                            value-integerp-when-uintp
                            value-integerp-when-slongp
                            value-integerp-when-ulongp
                            value-integerp-when-sllongp
                            value-integerp-when-ullongp)
                        (list op-values))
                    ,@(and op-arithmetic-values
                           (list op-arithmetic-values))
                    ,@(and op-real-values
                           (list op-real-values))
                    ,op-integer-values
                    ,op-ltype-rtype
                    ,@(and op-ltype
                           (list op-ltype))
                    ,@(and (member-eq op-kind '(:mul :div :rem :add :sub
                                                :lt :gt :le :ge
                                                :eq :ne
                                                :bitand :bitxor :bitior))
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
                    ,@(if (member-eq op-kind '(:shl :shr))
                          *atc-promote-value-rules*
                        *atc-uaconvert-values-rules*)
                    result-integer-value
                    ,@*atc-value-integer->get-rules*
                    ,@(and (member-eq op-kind '(:shl :shr))
                           *atc-sint-get-rules*)
                    ,@(and (member-eq op-kind '(:shl :shr))
                           '(integer-type-bits-when-type-sint
                             integer-type-bits-when-type-uint
                             integer-type-bits-when-type-slong
                             integer-type-bits-when-type-ulong
                             integer-type-bits-when-type-sllong
                             integer-type-bits-when-type-ullong
                             type-of-value-when-sintp
                             type-of-value-when-uintp
                             type-of-value-when-slongp
                             type-of-value-when-ulongp
                             type-of-value-when-sllongp
                             type-of-value-when-ullongp))
                    apconvert-expr-value-when-not-value-array
                    value-integer
                    value-sint-to-sint-from-integer
                    value-uint-to-uint-from-integer
                    value-slong-to-slong-from-integer
                    value-ulong-to-ulong-from-integer
                    value-sllong-to-sllong-from-integer
                    value-ullong-to-ullong-from-integer
                    sint-integerp-alt-def
                    uint-integerp-alt-def
                    slong-integerp-alt-def
                    ulong-integerp-alt-def
                    sllong-integerp-alt-def
                    ullong-integerp-alt-def
                    uint-from-integer-mod
                    ulong-from-integer-mod
                    ullong-from-integer-mod
                    value-unsigned-integerp-alt-def
                    ,@(and (member-eq op-kind '(:add :sub :mul :div :rem))
                           '(value-arithmeticp-when-uintp
                             value-arithmeticp-when-sintp
                             value-arithmeticp-when-ulongp
                             value-arithmeticp-when-slongp
                             value-arithmeticp-when-ullongp
                             value-arithmeticp-when-sllongp))
                    ,@(and (member-eq op-kind '(:add :sub :mul :div :rem))
                           '(type-of-value-when-sintp
                             type-of-value-when-uintp
                             type-of-value-when-slongp
                             type-of-value-when-ulongp
                             type-of-value-when-sllongp
                             type-of-value-when-ullongp))
                    ,@(and (member-eq op-kind '(:add :sub :mul :div :rem))
                           '((:e uint-max)
                             (:e ulong-max)
                             (:e ullong-max)
                             (:e sint-min)
                             (:e sint-max)
                             (:e slong-min)
                             (:e slong-max)
                             (:e sllong-min)
                             (:e sllong-max)))
                    integer-type-rangep
                    ,@(and (not (member-eq op-kind '(:add :sub :mul :div :rem)))
                           '(integer-type-min
                             integer-type-max
                             bit-width-value-choices))))
         (event `(defruled ,name
                   ,formula
                   :enable ,enables
                   :disable (,@(and (member-eq op-kind '(:shl :shr))
                                    '((:e int-bits)
                                      (:e integer-type-bits)
                                      (:e integer-type-min)
                                      (:e integer-type-max)))
                             ;; the following are disabled for speed:
                             equal-of-error
                             equal-of-value-schar
                             equal-of-value-uchar
                             equal-of-value-sshort
                             equal-of-value-ushort
                             equal-of-value-sint
                             equal-of-value-uint
                             equal-of-value-slong
                             equal-of-value-ulong
                             equal-of-value-sllong
                             equal-of-value-ullong))))
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
         (op-values (pack op-kind '-values))
         (op-ltype-and-value (pack op-kind '- lfixtype '-and-value))
         (op-values-when-ltype (pack op-kind '-values-when- lfixtype))
         (fun-event
          `(defund ,op-ltype-and-value (x y)
             (,op-values (,ltype-fix x) y)))
         (thm-event
          `(defruled ,op-values-when-ltype
             (implies (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                           (,lpred x))
                      (equal (,op-values x y)
                             (,op-ltype-and-value x y)))
             :enable (,op-ltype-and-value)))
         ((mv names events)
          (atc-exec-binary-rules-gen-op-ltype op (car ltypes) rtypes))
         ((mv more-names more-events)
          (atc-exec-binary-rules-gen-op op (cdr ltypes) rtypes)))
      (mv (append (list op-values-when-ltype)
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
         (op-values (pack op-kind '-values))
         (exec-binary-strict-pure-when-op
          (pack 'exec-binary-strict-pure-when- op-kind))
         (thm-event
          `(defruled ,exec-binary-strict-pure-when-op
             (implies (and (equal op (,(pack 'binop- op-kind)))
                           (not (equal (value-kind x) :array))
                           (not (equal (value-kind y) :array))
                           (equal val (,op-values x y))
                           (valuep val))
                      (equal (exec-binary-strict-pure op
                                                      (expr-value x objdes-x)
                                                      (expr-value y objdes-y))
                             (expr-value val nil)))
             :enable (exec-binary-strict-pure
                      eval-binary-strict-pure
                      apconvert-expr-value-when-not-value-array)))
         ((mv names events)
          (atc-exec-binary-rules-gen-op op ltypes rtypes))
         ((mv more-names more-events)
          (atc-exec-binary-rules-gen (cdr ops) ltypes rtypes)))
      (mv (append (list exec-binary-strict-pure-when-op)
                  names
                  more-names)
          (append (list thm-event)
                  events
                  more-events))))

  (define atc-exec-binary-rules-for-op-gen ((op binopp))
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-binary-rules-gen (list op)
                                     *nonchar-integer-types*
                                     *nonchar-integer-types*))
         (atc-exec-op-rules (pack '*atc-exec- (binop-kind op) '-rules*))
         (defconst-names `(defconst ,atc-exec-op-rules ',names))
         (atc-exec-op-events (pack '*atc-exec- (binop-kind op) '-events*))
         (defconst-events `(defconst ,atc-exec-op-events ',events)))
      `(progn
         ,@events
         ,defconst-names
         ,defconst-events))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following commented-out code generates all 1600 instances in this file.
; It could be brought back if/when the events are made to certify much faster,
; as it is more convenient to have everything about binary operators in one file
; rather than splitting it across multiple files.

;;   (define atc-exec-binary-rules-gen-all ()
;;     :returns (event pseudo-event-formp)
;;     :parents nil
;;     (b* ((ops (list (binop-mul)
;;                     (binop-div)
;;                     (binop-rem)
;;                     (binop-add)
;;                     (binop-sub)
;;                     (binop-shl)
;;                     (binop-shr)
;;                     (binop-lt)
;;                     (binop-gt)
;;                     (binop-le)
;;                     (binop-ge)
;;                     (binop-eq)
;;                     (binop-ne)
;;                     (binop-bitand)
;;                     (binop-bitxor)
;;                     (binop-bitior)))
;;          ((mv names events)
;;           (atc-exec-binary-rules-gen ops
;;                                      *nonchar-integer-types*
;;                                      *nonchar-integer-types*)))
;;       `(progn
;;          (defsection atc-exec-binary-strict-pure-rules
;;            :short "Rules for executing strict pure binary operations."
;;            :long
;;            (xdoc::topstring
;;             (xdoc::p
;;              "The goal of these rules is to
;;               rewrite @('(exec-binary-strict-pure op x y)')
;;               to @('(op-type1-type2 x y)')
;;               when @('x') has type @('type1'),
;;               and @('y') has type @('type2').
;;               We could have a rule for each combination of
;;               @('op'), @('type1'), and @('type2'),
;;               but that would lead to 1,600 rules being applicable to
;;               @('(exec-binary-strict-pure op x y)').
;;               So we stage the rewriting as follows:")
;;             (xdoc::ul
;;              (xdoc::li
;;               "First, we rewrite @('(exec-binary-strict-pure op x y)')
;;                to a call @('(op-values x y)'),
;;                under the hypothesis that @('op') is a specific operator,
;;                where @('op-values') is one of 16 functions,
;;                one per binary strict operator.")
;;              (xdoc::li
;;               "Next, we rewrite @('(op-values x y)')
;;                to a call @('(op-type1-and-value x y)'),
;;                under the hypothesis that @('x') has type @('type1'),
;;                where @('op-type1-and-value')
;;                is one of 10 functions,
;;                one per supported integer type.")
;;              (xdoc::li
;;               "Finally, we rewrite
;;                @('(op-type1-and-value x y)')
;;                to the call @('(op-type1-type2 x y)'),
;;                under the hypothesis the @('y') has type @('type2'),
;;                for each of the 10 supported integer types."))
;;             (xdoc::p
;;              "Note that the intermediate functions used here
;;               do not need guard verification."))
;;            ,@events
;;            (defval *atc-exec-binary-strict-pure-rules*
;;              '(,@names
;;                (:e binop-mul)
;;                (:e binop-div)
;;                (:e binop-rem)
;;                (:e binop-add)
;;                (:e binop-sub)
;;                (:e binop-shl)
;;                (:e binop-shr)
;;                (:e binop-lt)
;;                (:e binop-gt)
;;                (:e binop-le)
;;                (:e binop-ge)
;;                (:e binop-eq)
;;                (:e binop-ne)
;;                (:e binop-bitand)
;;                (:e binop-bitxor)
;;                (:e binop-bitior)))))))

;; (make-event (atc-exec-binary-rules-gen-all))
