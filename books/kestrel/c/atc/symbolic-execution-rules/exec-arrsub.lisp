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

(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-arrsub-rules-generation
  :short "Code to generate the rules for executing array subscript expressions."

  (define atc-exec-arrsub-rules-gen ((atype typep))
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

  (define atc-exec-arrsub-rules-gen-loop ((atypes type-listp))
    :guard (type-nonchar-integer-listp atypes)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp atypes)) (mv nil nil))
         ((mv name event) (atc-exec-arrsub-rules-gen (car atypes)))
         ((mv more-names more-events)
          (atc-exec-arrsub-rules-gen-loop (cdr atypes))))
      (mv (cons name more-names)
          (cons event more-events))))

  (define atc-exec-arrsub-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-arrsub-rules-gen-loop *nonchar-integer-types*)))
      `(progn
         (defsection atc-exec-arrsub-rules
           :short "Rules for executing array subscript expressions."
           ,@events
           (defval *atc-exec-arrsub-rules*
             '(,@names)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-arrsub-rules-gen-all))
