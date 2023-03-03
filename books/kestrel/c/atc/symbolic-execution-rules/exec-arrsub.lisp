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

(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-arrsub-rules-generation
  :short "Code to generate the rules for executing array subscript expressions."

  (define atc-exec-arrsub-rules-gen ((atype typep) (itype typep))
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
         (atype-array-index-okp
          (pack afixtype '-array-index-okp))
         (atype-array-read-itype
          (pack afixtype '-array-read- ifixtype))
         (atype-array-read
          (pack afixtype '-array-read))
         (atype-array-length
          (pack afixtype '-array-length))
         (atype-array-read-alt-def
          (pack atype-array-read '-alt-def))
         (atype-array-length-alt-def
          (pack atype-array-length '-alt-def))
         (elemtype-when-apred
          (pack 'value-array->elemtype-when- apred))
         (name (pack 'exec-arrsub-when- apred '-and- ipred))
         (integer-from-itype (pack 'integer-from- ifixtype))
         (formula `(implies
                    (and ,(atc-syntaxp-hyp-for-expr-pure 'x)
                         ,(atc-syntaxp-hyp-for-expr-pure 'y)
                         (valuep x)
                         (value-case x :pointer)
                         (value-pointer-validp x)
                         (equal (value-pointer->reftype x)
                                ,(type-to-maker atype))
                         (equal objdes (value-pointer->designator x))
                         (equal array (read-object objdes compst))
                         (,apred array)
                         (,ipred y)
                         (,atype-array-itype-index-okp array y))
                    (equal (exec-arrsub (expr-value x nil)
                                        (expr-value y nil)
                                        compst)
                           (expr-value (,atype-array-read-itype array y)
                                       (objdesign-element
                                        objdes
                                        (,integer-from-itype y))))))
         (event `(defruled ,name
                   ,formula
                   :enable (exec-arrsub
                            ,@*atc-value-integer->get-rules*
                            ,atype-array-itype-index-okp
                            ,atype-array-read-itype
                            ,atype-array-read-alt-def
                            ,elemtype-when-apred
                            ,atype-array-index-okp
                            ,atype-array-length-alt-def
                            value-array-read
                            integer-range-p
                            ifix
                            nfix
                            value-array->length
                            not-errorp-when-valuep)
                   :prep-lemmas
                   ((defrule lemma
                      (implies (and (,atype-array-index-okp array index)
                                    (integerp index))
                               (not (< index 0)))
                      :enable (,atype-array-index-okp
                               integer-range-p
                               ifix))))))
      (mv name event)))

  (define atc-exec-arrsub-rules-gen-loop-itypes ((atype typep)
                                                 (itypes type-listp))
    :guard (and (type-nonchar-integerp atype)
                (type-nonchar-integer-listp itypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp itypes)) (mv nil nil))
         ((mv name event) (atc-exec-arrsub-rules-gen atype (car itypes)))
         ((mv names events)
          (atc-exec-arrsub-rules-gen-loop-itypes atype (cdr itypes))))
      (mv (cons name names) (cons event events))))

  (define atc-exec-arrsub-rules-gen-loop-atypes ((atypes type-listp)
                                                 (itypes type-listp))
    :guard (and (type-nonchar-integer-listp atypes)
                (type-nonchar-integer-listp itypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp atypes)) (mv nil nil))
         ((mv names events)
          (atc-exec-arrsub-rules-gen-loop-itypes (car atypes) itypes))
         ((mv more-names more-events)
          (atc-exec-arrsub-rules-gen-loop-atypes (cdr atypes) itypes)))
      (mv (append names more-names) (append events more-events))))

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
