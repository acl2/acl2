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

(include-book "../types")

(include-book "syntaxp")
(include-book "arrays")
(include-book "value-integer-get")
(include-book "integers")
(include-book "apconvert")

(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-arrsub-rules-generation
  :short "Code to generate the rules for executing array subscript expressions."

  (define atc-exec-arrsub-rules-gen-1 ((atype typep))
    :guard (type-nonchar-integerp atype)
    :returns (mv (name symbolp)
                 (event pseudo-event-formp))
    :parents nil
    (b* ((afixtype (integer-type-to-fixtype atype))
         (apred (pack afixtype '-arrayp))
         (atype-array-index-okp (pack afixtype '-array-index-okp))
         (atype-array-read (pack afixtype '-array-read))
         (value-array->elemtype-when-apred (pack 'value-array->elemtype-when-
                                                 apred))
         (value-array-read-when-apred (pack 'value-array-read-when- apred))
         (name (pack 'exec-arrsub-when- apred))
         (formula
          `(implies
            (and (equal ex (apconvert-expr-value (expr-value x objdes-x)))
                 (expr-valuep ex)
                 (equal a (expr-value->value ex))
                 (value-case a :pointer)
                 (value-pointer-validp a)
                 (equal (value-pointer->reftype a)
                        ,(type-to-maker atype))
                 (equal objdes (value-pointer->designator a))
                 (equal array (read-object objdes compst))
                 (,apred array)
                 (cintegerp y)
                 (,atype-array-index-okp array y))
            (equal (exec-arrsub (expr-value x objdes-x)
                                (expr-value y objdes-y)
                                compst)
                   (expr-value (,atype-array-read array y)
                               (objdesign-element objdes
                                                  (integer-from-cinteger y))))))
         (event `(defruled ,name
                   ,formula
                   :enable (exec-arrsub
                            ,value-array->elemtype-when-apred
                            apconvert-expr-value-when-not-value-array
                            value-kind-not-array-when-cintegerp
                            value-integerp-when-cintegerp
                            ,atype-array-index-okp
                            integer-range-p
                            value-integer->get-when-cintegerp
                            ,value-array-read-when-apred))))
      (mv name event)))

  (define atc-exec-arrsub-rules-gen-2 ((atype typep)
                                       (itype typep)
                                       (genthm symbolp))
    :guard (and (type-nonchar-integerp atype)
                (type-nonchar-integerp itype))
    :returns (mv (name symbolp)
                 (event pseudo-event-formp))
    :parents nil
    (b* ((afixtype (integer-type-to-fixtype atype))
         (ifixtype (integer-type-to-fixtype itype))
         (apred (pack afixtype '-arrayp))
         (ipred (pack ifixtype 'p))
         (atype-array-itype-index-okp
          (pack afixtype '-array- ifixtype '-index-okp))
         (atype-array-read-itype
          (pack afixtype '-array-read- ifixtype))
         (integer-from-itype (pack 'integer-from- ifixtype))
         (name (pack 'exec-arrsub-when- apred '-and- ipred))
         (formula
          `(implies
            (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                 ,(atc-syntaxp-hyp-for-expr-pure 'y)
                 (equal ex (apconvert-expr-value (expr-value x objdes-x)))
                 (expr-valuep ex)
                 (equal a (expr-value->value ex))
                 (value-case a :pointer)
                 (value-pointer-validp a)
                 (equal (value-pointer->reftype a)
                        ,(type-to-maker atype))
                 (equal objdes (value-pointer->designator a))
                 (equal array (read-object objdes compst))
                 (,apred array)
                 (,ipred y)
                 (,atype-array-itype-index-okp array y))
            (equal (exec-arrsub (expr-value x objdes-x)
                                (expr-value y objdes-y)
                                compst)
                   (expr-value (,atype-array-read-itype array y)
                               (objdesign-element objdes
                                                  (,integer-from-itype y))))))
         (event `(defruled ,name
                   ,formula
                   :enable (,genthm
                            ,(pack atype-array-itype-index-okp '-alt-def)
                            ,(pack atype-array-read-itype '-alt-def)
                            integer-from-cinteger-alt-def))))
      (mv name event)))

  (define atc-exec-arrsub-rules-gen-loop-itypes ((atype typep)
                                                 (itypes type-listp)
                                                 (genthm symbolp))
    :guard (and (type-nonchar-integerp atype)
                (type-nonchar-integer-listp itypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp itypes)) (mv nil nil))
         ((mv name event) (atc-exec-arrsub-rules-gen-2 atype
                                                       (car itypes)
                                                       genthm))
         ((mv names events)
          (atc-exec-arrsub-rules-gen-loop-itypes atype
                                                 (cdr itypes)
                                                 genthm)))
      (mv (cons name names) (cons event events))))

  (define atc-exec-arrsub-rules-gen-loop-atypes ((atypes type-listp)
                                                 (itypes type-listp))
    :guard (and (type-nonchar-integer-listp atypes)
                (type-nonchar-integer-listp itypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp atypes)) (mv nil nil))
         ((mv name event) (atc-exec-arrsub-rules-gen-1 (car atypes)))
         ((mv names events)
          (atc-exec-arrsub-rules-gen-loop-itypes (car atypes) itypes name))
         ((mv more-names more-events)
          (atc-exec-arrsub-rules-gen-loop-atypes (cdr atypes) itypes)))
      (mv (append names more-names) (append (list event) events more-events))))

  (define atc-exec-arrsub-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-arrsub-rules-gen-loop-atypes
           *nonchar-integer-types*
           *nonchar-integer-types*)))
      `(progn
         (defsection atc-exec-arrsub-rules
           :short "Rules for executing array subscript expressions."
           ,@events
           (defval *atc-exec-arrsub-rules*
             '(,@names)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-arrsub-rules-gen-all))
