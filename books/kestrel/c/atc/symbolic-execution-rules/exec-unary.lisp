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

(include-book "../types")

(include-book "syntaxp")
(include-book "promote-value")
(include-book "value-integer-get")
(include-book "apconvert")

(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-unary-nonpointer-rules-generation
  :short "Code to generate the rules for executing
          unary operations that do not involve pointers."

  (define atc-exec-unary-nonpointer-rules-gen ((op unopp) (type typep))
    :guard (type-nonchar-integerp type)
    :returns (mv (name symbolp)
                 (event pseudo-event-formp))
    :parents nil
    (b* ((fixtype (integer-type-to-fixtype type))
         (pred (pack fixtype 'p))
         (op-kind (unop-kind op))
         (op-value (pack op-kind '-value))
         (op-scalar-value (and (unop-case op :lognot)
                               (pack op-kind '-scalar-value)))
         (op-arithmetic-value (and (or (unop-case op :plus)
                                       (unop-case op :minus))
                                   (pack op-kind '-arithmetic-value)))
         (op-integer-value (pack op-kind '-integer-value))
         (name (pack op-value '-when- pred))
         (op-type (pack op-kind '- fixtype))
         (op-type-okp (and (unop-case op :minus)
                           (member-eq (type-kind type)
                                      '(:schar
                                        :sshort
                                        :sint
                                        :slong
                                        :sllong
                                        :uchar
                                        :ushort))
                           (pack op-type '-okp)))
         (promotedp (and (member-eq op-kind
                                    '(:plus :minus :bitnot))
                         (member-eq (type-kind type)
                                    '(:schar :uchar :sshort :ushort))))
         (hyps `(and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                     (equal op (,(pack 'unop- op-kind)))
                     (,pred x)
                     ,@(and op-type-okp
                            `((,op-type-okp x)))))
         (formula `(implies ,hyps
                            (equal (exec-unary op (expr-value x objdes) compst)
                                   (expr-value (,op-type x) nil))))
         (enables `(exec-unary
                    eval-unary
                    ,op-value
                    ,@(and op-scalar-value
                           (list op-scalar-value))
                    ,@(and op-arithmetic-value
                           (list op-arithmetic-value))
                    ,op-integer-value
                    ,op-type
                    ,@(and promotedp
                           (list (pack op-kind '-sint)))
                    ,@(and op-type-okp
                           (list op-type-okp))
                    ,@(and op-type-okp
                           promotedp
                           (list (pack op-kind '-sint-okp)))
                    ,@*atc-promote-value-rules*
                    result-integer-value
                    ,@*atc-value-integer->get-rules*
                    value-integer
                    valuep-when-uintp
                    valuep-when-sintp
                    valuep-when-ulongp
                    valuep-when-slongp
                    valuep-when-ullongp
                    valuep-when-sllongp
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
                    integer-type-rangep
                    integer-type-min
                    integer-type-max
                    bit-width-value-choices
                    apconvert-expr-value-when-not-value-array
                    value-kind-when-ucharp
                    value-kind-when-scharp
                    value-kind-when-ushortp
                    value-kind-when-sshortp
                    value-kind-when-uintp
                    value-kind-when-sintp
                    value-kind-when-ulongp
                    value-kind-when-slongp
                    value-kind-when-ullongp
                    value-kind-when-sllongp
                    ,@(and (unop-case op :bitnot)
                           `((:e sint-min)
                             (:e sint-max)
                             (:e slong-min)
                             (:e slong-max)
                             (:e sllong-min)
                             (:e sllong-max)))
                    ,@(and (unop-case op :lognot)
                           `(sint-from-boolean
                             value-schar->get-to-integer-from-schar
                             value-uchar->get-to-integer-from-uchar
                             value-sshort->get-to-integer-from-sshort
                             value-ushort->get-to-integer-from-ushort))
                    identity
                    ifix
                    fix
                    mod
                    lognot))
         (event `(defruled ,name
                   ,formula
                   :enable ,enables
                   :disable ((:e integer-type-min)
                             (:e integer-type-max)))))
      (mv name event)))

  (define atc-exec-unary-nonpointer-rules-gen-loop-types ((op unopp)
                                                          (types type-listp))
    :guard (type-nonchar-integer-listp types)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp types)) (mv nil nil))
         ((mv name event) (atc-exec-unary-nonpointer-rules-gen op (car types)))
         ((mv names events)
          (atc-exec-unary-nonpointer-rules-gen-loop-types op (cdr types))))
      (mv (cons name names) (cons event events))))

  (define atc-exec-unary-nonpointer-rules-gen-loop-ops ((ops unop-listp)
                                                        (types type-listp))
    :guard (type-nonchar-integer-listp types)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp ops)) (mv nil nil))
         ((mv names events)
          (atc-exec-unary-nonpointer-rules-gen-loop-types (car ops) types))
         ((mv more-names more-events)
          (atc-exec-unary-nonpointer-rules-gen-loop-ops (cdr ops) types)))
      (mv (append names more-names) (append events more-events))))

  (define atc-exec-unary-nonpointer-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* ((ops (list (unop-plus)
                    (unop-minus)
                    (unop-bitnot)
                    (unop-lognot)))
         ((mv names events)
          (atc-exec-unary-nonpointer-rules-gen-loop-ops
           ops *nonchar-integer-types*)))
      `(progn
         (defsection atc-exec-unary-nonpointer-rules
           :short "Rules for executing unary operations
                   that do not involve pointers."
           ,@events
           (defval *atc-exec-unary-nonpointer-rules*
             '(,@names
               (:e unop-plus)
               (:e unop-minus)
               (:e unop-bitnot)
               (:e unop-lognot))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-unary-nonpointer-rules-gen-all))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-indir-rules-generation
  :short "Code to generate the rules for executing
          the indirection unary operation."

  (define atc-exec-indir-rules-gen ((type typep))
    :guard (type-nonchar-integerp type)
    :returns (mv (name symbolp)
                 (event pseudo-event-formp))
    :parents nil
    (b* ((fixtype (integer-type-to-fixtype type))
         (pred (pack fixtype 'p))
         (name (pack 'exec-indir-when- pred))
         (hyps `(and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                     (valuep x)
                     (value-case x :pointer)
                     (value-pointer-validp x)
                     (equal (value-pointer->reftype x)
                            ,(type-to-maker type))
                     (unop-case op :indir)
                     (equal objdes (value-pointer->designator x))
                     (equal val (read-object objdes compst))
                     (,pred val)))
         (formula `(implies ,hyps
                            (equal (exec-unary op
                                               (expr-value x objdes-x)
                                               compst)
                                   (expr-value val objdes))))
         (hints
          `(("Goal"
             :in-theory (enable exec-unary
                                exec-indir
                                apconvert-expr-value-when-not-value-array))))
         (event `(defruled ,name
                   ,formula
                   :hints ,hints)))
      (mv name event)))

  (define atc-exec-indir-rules-loop ((types type-listp))
    :guard (type-nonchar-integer-listp types)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp types)) (mv nil nil))
         ((mv name event) (atc-exec-indir-rules-gen (car types)))
         ((mv names events) (atc-exec-indir-rules-loop (cdr types))))
      (mv (cons name names) (cons event events))))

  (define atc-exec-indir-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-indir-rules-loop *nonchar-integer-types*)))
      `(defsection atc-exec-indir-rules
         :short "Rules for executing the indirection unary operation."
         ,@events
         (defval *atc-exec-indir-rules*
           '(,@names
             (:e unop-kind)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-indir-rules-gen-all))
