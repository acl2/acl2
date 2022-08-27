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

(include-book "execution-rules")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-unary-rules-generation
  :short "Code to generate the rules for executing unary operations."

  (define atc-exec-unary-rules-gen ((op unopp) (type typep))
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
                            (equal (exec-unary op x)
                                   (,op-type x))))
         (enables `(exec-unary
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
                    value-integer->get
                    value-integer
                    value-sint->get-to-sint->get
                    value-uint->get-to-uint->get
                    value-slong->get-to-slong->get
                    value-ulong->get-to-ulong->get
                    value-sllong->get-to-sllong->get
                    value-ullong->get-to-ullong->get
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
                    integer-type-max
                    ,@(and (unop-case op :bitnot)
                           `((:e sint-min)
                             (:e sint-max)
                             (:e slong-min)
                             (:e slong-max)
                             (:e sllong-min)
                             (:e sllong-max)))
                    ,@(and (unop-case op :lognot)
                           `(sint-from-boolean
                             value-schar->get-to-schar->get
                             value-uchar->get-to-uchar->get
                             value-sshort->get-to-sshort->get
                             value-ushort->get-to-ushort->get))))
         (event `(defruled ,name
                   ,formula
                   :enable ,enables
                   :disable ((:e integer-type-min)
                             (:e integer-type-max)))))
      (mv name event)))

  (define atc-exec-unary-rules-gen-loop-types ((op unopp) (types type-listp))
    :guard (type-nonchar-integer-listp types)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp types)) (mv nil nil))
         ((mv name event) (atc-exec-unary-rules-gen op (car types)))
         ((mv names events) (atc-exec-unary-rules-gen-loop-types op (cdr types))))
      (mv (cons name names) (cons event events))))

  (define atc-exec-unary-rules-gen-loop-ops ((ops unop-listp) (types type-listp))
    :guard (type-nonchar-integer-listp types)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp ops)) (mv nil nil))
         ((mv names events) (atc-exec-unary-rules-gen-loop-types (car ops) types))
         ((mv more-names more-events)
          (atc-exec-unary-rules-gen-loop-ops (cdr ops) types)))
      (mv (append names more-names) (append events more-events))))

  (define atc-exec-unary-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* ((ops (list (unop-plus)
                    (unop-minus)
                    (unop-bitnot)
                    (unop-lognot)))
         ((mv names events)
          (atc-exec-unary-rules-gen-loop-ops ops
                                             *nonchar-integer-types**)))
      `(progn
         (defsection atc-exec-unary-rules
           :short "Rules for executing unary operations"
           ,@events
           (defval *atc-exec-unary-rules*
             '(,@names
               (:e unop-plus)
               (:e unop-minus)
               (:e unop-bitnot)
               (:e unop-lognot))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-unary-rules-gen-all))
