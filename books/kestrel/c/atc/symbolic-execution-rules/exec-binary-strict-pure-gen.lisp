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

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

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
         (op-real-values (and (binop-case op :lt)
                              (pack op-kind '-real-values)))
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
                                                   :shl :shr
                                                   :lt))
                      `(,exec-binary-strict-pure-of-op-and-ltype
                        ,op-values
                        ,@(and op-arithmetic-values
                               (list op-arithmetic-values))
                        ,@(and op-real-values
                               (list op-real-values))
                        ,op-integer-values
                        ,op-ltype-rtype
                        ,@(and op-ltype
                               (list op-ltype))
                        ,@(and (member-eq op-kind '(:mul :div :rem :add :sub
                                                    :lt))
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
                             ifix
                             ;; the following are disabled for speed:
                             equal-of-error
                             equal-of-schar
                             equal-of-uchar
                             equal-of-sshort
                             equal-of-ushort
                             equal-of-sint
                             equal-of-uint
                             equal-of-slong
                             equal-of-ulong
                             equal-of-sllong
                             equal-of-ullong
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
         (exec-op (if (member-eq (binop-kind op) '(:mul :div :rem :add :sub
                                                   :shl :shr
                                                   :lt))
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
                                                   :shl :shr
                                                   :lt))
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
                  more-events)))))
