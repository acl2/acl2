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
(include-book "../types")

(include-book "arrays")
(include-book "value-integer-get")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-asg-ident-rules
  :short "Rules for executing assignment expressions to identifier expressions."

  (defruled exec-expr-asg-ident
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :binary)
                  (equal (binop-kind (expr-binary->op e)) :asg)
                  (not (zp limit))
                  (equal e1 (expr-binary->arg1 e))
                  (equal (expr-kind e1) :ident)
                  (equal val+compst1
                         (exec-expr-call-or-pure (expr-binary->arg2 e)
                                                 compst
                                                 fenv
                                                 (1- limit)))
                  (equal val (mv-nth 0 val+compst1))
                  (equal compst1 (mv-nth 1 val+compst1))
                  (valuep val))
             (equal (exec-expr-asg e compst fenv limit)
                    (write-var (expr-ident->get e1) val compst1)))
    :enable exec-expr-asg)

  (defval *atc-exec-expr-asg-ident-rules*
    '(exec-expr-asg-ident
      (:e expr-kind)
      (:e expr-binary->op)
      (:e expr-binary->arg1)
      (:e expr-binary->arg2)
      (:e expr-ident->get)
      (:e binop-kind))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-asg-arrsub-rules-generation
  :short "Code to generate the rules for executing
          assignments to array subscripting expressions."

  (define atc-exec-expr-asg-arrsub-rules-gen ((atype typep) (itype typep))
    :guard (and (type-nonchar-integerp atype)
                (type-nonchar-integerp itype))
    :returns (mv (name symbolp)
                 (event pseudo-event-formp))
    :parents nil
    (b* ((afixtype (integer-type-to-fixtype atype))
         (ifixtype (integer-type-to-fixtype itype))
         (apred (pack afixtype '-arrayp))
         (epred (pack afixtype 'p))
         (ipred (pack ifixtype 'p))
         (atype-array-itype-index-okp
          (pack afixtype '-array- ifixtype '-index-okp))
         (atype-array-index-okp
          (pack afixtype '-array-index-okp))
         (atype-array-write-itype
          (pack afixtype '-array-write- ifixtype))
         (atype-array-write-alt-def
          (pack afixtype '-array-write-alt-def))
         (elemtype-when-apred
          (pack 'value-array->elemtype-when- apred))
         (name (pack 'exec-expr-asg-arrsub-when- apred '-and- ipred))
         (formula
          `(implies
            (and (syntaxp (quotep e))
                 (equal (expr-kind e) :binary)
                 (equal (binop-kind (expr-binary->op e)) :asg)
                 (equal left (expr-binary->arg1 e))
                 (equal right (expr-binary->arg2 e))
                 (equal (expr-kind left) :arrsub)
                 (equal arr (expr-arrsub->arr left))
                 (equal sub (expr-arrsub->sub left))
                 (equal (expr-kind arr) :ident)
                 (equal var (expr-ident->get arr))
                 (not (zp limit))
                 (equal arr-val (read-var var compst))
                 (valuep arr-val)
                 (equal ptr
                        (if (value-case arr-val :array)
                            (value-pointer (objdesign-variable var)
                                           (value-array->elemtype arr-val))
                          arr-val))
                 (value-case ptr :pointer)
                 (not (value-pointer-nullp ptr))
                 (equal (value-pointer->reftype ptr)
                        ,(type-to-maker atype))
                 (equal array
                        (read-object (value-pointer->designator ptr) compst))
                 (,apred array)
                 (equal index (exec-expr-pure sub compst))
                 (,ipred index)
                 (,atype-array-itype-index-okp array index)
                 (equal val (exec-expr-pure right compst))
                 (,epred val))
            (equal (exec-expr-asg e compst fenv limit)
                   (write-object (value-pointer->designator ptr)
                                 (,atype-array-write-itype array index val)
                                 compst))))
         (event `(defruled ,name
                   ,formula
                   :enable (exec-expr-asg
                            ,@*atc-value-integer->get-rules*
                            ,atype-array-itype-index-okp
                            ,atype-array-write-itype
                            ,atype-array-write-alt-def
                            ,elemtype-when-apred)
                   :prep-lemmas
                   ((defrule lemma1
                      (implies (and (,atype-array-index-okp array index)
                                    (integerp index))
                               (not (< index 0)))
                      :enable ,atype-array-index-okp)
                    (defrule lemma2
                      (implies (and (,apred array)
                                    (integerp index)
                                    (,atype-array-index-okp array index)
                                    (,epred val))
                               (not (errorp
                                     (value-array-write index val array))))
                      :use (:instance ,atype-array-write-alt-def
                            (elem val)))))))
      (mv name event)))

  (define atc-exec-expr-asg-arrsub-rules-gen-loop-itypes ((atype typep)
                                                          (itypes type-listp))
    :guard (and (type-nonchar-integerp atype)
                (type-nonchar-integer-listp itypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp itypes)) (mv nil nil))
         ((mv name event) (atc-exec-expr-asg-arrsub-rules-gen atype
                                                              (car itypes)))
         ((mv names events)
          (atc-exec-expr-asg-arrsub-rules-gen-loop-itypes atype (cdr itypes))))
      (mv (cons name names) (cons event events))))

  (define atc-exec-expr-asg-arrsub-rules-gen-loop-atypes ((atypes type-listp)
                                                          (itypes type-listp))
    :guard (and (type-nonchar-integer-listp atypes)
                (type-nonchar-integer-listp itypes))
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp atypes)) (mv nil nil))
         ((mv names events)
          (atc-exec-expr-asg-arrsub-rules-gen-loop-itypes (car atypes) itypes))
         ((mv more-names more-events)
          (atc-exec-expr-asg-arrsub-rules-gen-loop-atypes (cdr atypes) itypes)))
      (mv (append names more-names) (append events more-events))))

  (define atc-exec-expr-asg-arrsub-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-expr-asg-arrsub-rules-gen-loop-atypes
           *nonchar-integer-types**
           *nonchar-integer-types**)))
      `(progn
         (defsection atc-exec-expr-asg-arrsub-rules
           :short "Rules for executing assignment expressions to
                   array subscript expressions."
           ,@events
           (defval *atc-exec-expr-asg-arrsub-rules*
             '(,@names
               (:e expr-kind)
               (:e expr-arrsub->arr)
               (:e expr-arrsub->sub)
               (:e expr-binary->op)
               (:e expr-binary->arg1)
               (:e expr-binary->arg2)
               (:e expr-ident->get)
               (:e binop-kind))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-expr-asg-arrsub-rules-gen-all))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-asg-rules
  :short "Rules for executing assignment expressions."

  (defval *atc-exec-expr-asg-rules*
    (append *atc-exec-expr-asg-ident-rules*
            *atc-exec-expr-asg-arrsub-rules*)))
