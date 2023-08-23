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
(include-book "../pointed-integers")
(include-book "../read-write-variables")

(include-book "../types")

(include-book "arrays")
(include-book "value-integer-get")
(include-book "apconvert")
(include-book "integers")
(include-book "exec-expr-pure")

(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-asg-ident-rules
  :short "Rules for executing assignment expressions to identifier expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first one is used in the large symbolic execution.")
   (xdoc::p
    "The second one is for the new modular proof approach."))

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
                  (valuep val)
                  (valuep (read-var (expr-ident->get e1) compst1)))
             (equal (exec-expr-asg e compst fenv limit)
                    (write-var (expr-ident->get e1) val compst1)))
    :enable (exec-expr-asg
             exec-expr-pure
             exec-ident
             write-object-of-objdesign-of-var-to-write-var))

  (defruled exec-expr-asg-ident-via-object
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
                  (valuep val)
                  (equal objdes (objdesign-of-var (expr-ident->get e1) compst1))
                  objdes)
             (equal (exec-expr-asg e compst fenv limit)
                    (write-object objdes val compst1)))
    :enable (exec-expr-asg
             exec-expr-pure
             exec-ident))

  (defval *atc-exec-expr-asg-ident-rules*
    '(exec-expr-asg-ident
      (:e expr-kind)
      (:e expr-binary->op)
      (:e expr-binary->arg1)
      (:e expr-binary->arg2)
      (:e expr-ident->get)
      (:e binop-kind))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-asg-indir-rule-generation
  :short "Code to generate the rules for executing
          assignments to integers by pointer."

  (define atc-exec-expr-asg-indir-rules-gen ((type typep))
    :guard (type-nonchar-integerp type)
    :returns (mv (name symbolp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* ((fixtype (integer-type-to-fixtype type))
         (pred (pack fixtype 'p))
         (constructor (pack 'type- fixtype))
         (type-of-value-when-pred (pack 'type-of-value-when- pred))
         (not-pred-of-value-pointer (pack 'not- pred '-of-value-pointer))
         (value-kind-when-pred (pack 'value-kind-when- pred))
         (writer (pack fixtype '-write))
         (name (pack 'exec-expr-asg-indir-when- pred))
         (name-mod-proofs (pack name '-for-modular-proofs))
         (formula
          `(implies
            (and (syntaxp (quotep e))
                 (equal (expr-kind e) :binary)
                 (equal (binop-kind (expr-binary->op e)) :asg)
                 (equal left (expr-binary->arg1 e))
                 (equal right (expr-binary->arg2 e))
                 (equal (expr-kind left) :unary)
                 (equal (unop-kind (expr-unary->op left)) :indir)
                 (equal arg (expr-unary->arg left))
                 (equal (expr-kind arg) :ident)
                 (equal var (expr-ident->get arg))
                 (not (zp limit))
                 (equal ptr (read-var var compst))
                 (valuep ptr)
                 (value-case ptr :pointer)
                 (value-pointer-validp ptr)
                 (equal (value-pointer->reftype ptr) (,constructor))
                 (equal eval (exec-expr-pure right compst))
                 (expr-valuep eval)
                 (equal eval1 (apconvert-expr-value eval))
                 (expr-valuep eval1)
                 (equal val (expr-value->value eval1))
                 (,pred val)
                 (valuep (read-object (value-pointer->designator ptr) compst)))
            (equal (exec-expr-asg e compst fenv limit)
                   (write-object (value-pointer->designator ptr)
                                 val
                                 compst))))
         (formula-mod-proofs
          `(implies
            (and (syntaxp (quotep e))
                 (equal (expr-kind e) :binary)
                 (equal (binop-kind (expr-binary->op e)) :asg)
                 (equal left (expr-binary->arg1 e))
                 (equal right (expr-binary->arg2 e))
                 (equal (expr-kind left) :unary)
                 (equal (unop-kind (expr-unary->op left)) :indir)
                 (equal arg (expr-unary->arg left))
                 (equal (expr-kind arg) :ident)
                 (equal var (expr-ident->get arg))
                 (not (zp limit))
                 (equal ptr (read-var var compst))
                 (valuep ptr)
                 (value-case ptr :pointer)
                 (value-pointer-validp ptr)
                 (equal (value-pointer->reftype ptr) (,constructor))
                 (equal eval (exec-expr-pure right compst))
                 (expr-valuep eval)
                 (equal eval1 (apconvert-expr-value eval))
                 (expr-valuep eval1)
                 (equal val (expr-value->value eval1))
                 (,pred val)
                 (valuep (read-object (value-pointer->designator ptr) compst)))
            (equal (exec-expr-asg e compst fenv limit)
                   (write-object (value-pointer->designator ptr)
                                 (,writer val)
                                 compst))))
         (events `((defruled ,name
                     ,formula
                     :expand ((exec-expr-pure (expr-binary->arg1 e) compst)
                              (exec-expr-pure (expr-unary->arg
                                               (expr-binary->arg1 e)) compst))
                     :enable (exec-expr-asg
                              exec-unary
                              exec-indir
                              exec-ident
                              apconvert-expr-value-when-not-value-array-alt
                              value-kind-when-scharp
                              read-object-of-objdesign-of-var-to-read-var
                              ,type-of-value-when-pred
                              ,not-pred-of-value-pointer
                              ,value-kind-when-pred)
                     :disable (equal-of-error
                               equal-of-expr-value)
                     :prep-lemmas
                     ((defrule lemma
                        (implies (and (expr-valuep (apconvert-expr-value eval))
                                      (,pred (expr-value->value
                                              (apconvert-expr-value eval))))
                                 (,pred (expr-value->value eval)))
                        :enable apconvert-expr-value)))
                   (defruled ,name-mod-proofs
                     ,formula-mod-proofs
                     :use ,name
                     :enable ,writer))))
      (mv name events)))

  (define atc-exec-expr-asg-indir-rules-gen-loop ((types type-listp))
    :guard (type-nonchar-integer-listp types)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp types)) (mv nil nil))
         ((mv name events)
          (atc-exec-expr-asg-indir-rules-gen (car types)))
         ((mv more-names more-events)
          (atc-exec-expr-asg-indir-rules-gen-loop (cdr types))))
      (mv (cons name more-names) (append events more-events))))

  (define atc-exec-expr-asg-indir-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-expr-asg-indir-rules-gen-loop *nonchar-integer-types*)))
      `(progn
         (defsection atc-exec-expr-asg-indir-rules
           :short "Rules for executing assignment expressions
                 to integers by pointer."
           ,@events
           (defval *atc-exec-expr-asg-indir-rules*
             '(,@names
               (:e expr-kind)
               (:e binop-kind)
               (:e expr-binary->op)
               (:e expr-binary->arg1)
               (:e expr-binary->arg2)
               (:e unop-kind)
               (:e expr-unary->op)
               (:e expr-unary->arg)
               (:e expr-ident->get))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event (atc-exec-expr-asg-indir-rules-gen-all))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-asg-arrsub-rules-generation
  :short "Code to generate the rules for executing
          assignments to array subscripting expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a rule for the large symbolic execution,
     and also a rule for the modular proofs.
     The former will be eventually eliminated,
     once modular proofs cover all the ATC constructs."))

  (define atc-exec-expr-asg-arrsub-rules-gen ((atype typep))
    :guard (type-nonchar-integerp atype)
    :returns (mv (name symbolp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* ((afixtype (integer-type-to-fixtype atype))
         (apred (pack afixtype '-arrayp))
         (epred (pack afixtype 'p))
         (atype-array-index-okp (pack afixtype '-array-index-okp))
         (atype-array-write (pack afixtype '-array-write))
         (value-array->elemtype-when-apred (pack 'value-array->elemtype-when-
                                                 apred))
         (value-array-read-when-apred (pack 'value-array-read-when- apred))
         (value-array-write-when-apred (pack 'value-array-write-when- apred))
         (name (pack 'exec-expr-asg-arrsub-when- apred))
         (formula
          `(implies
            (and (equal (expr-kind e) :binary)
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
                 (equal eptr
                        (apconvert-expr-value
                         (expr-value arr-val (objdesign-of-var var compst))))
                 (expr-valuep eptr)
                 (equal ptr (expr-value->value eptr))
                 (value-case ptr :pointer)
                 (value-pointer-validp ptr)
                 (equal (value-pointer->reftype ptr)
                        ,(type-to-maker atype))
                 (equal array
                        (read-object (value-pointer->designator ptr) compst))
                 (,apred array)
                 (equal eindex (exec-expr-pure sub compst))
                 (expr-valuep eindex)
                 (equal eindex1 (apconvert-expr-value eindex))
                 (expr-valuep eindex1)
                 (equal index (expr-value->value eindex1))
                 (cintegerp index)
                 (,atype-array-index-okp array index)
                 (equal eval (exec-expr-pure right compst))
                 (expr-valuep eval)
                 (equal eval1 (apconvert-expr-value eval))
                 (expr-valuep eval1)
                 (equal val (expr-value->value eval1))
                 (,epred val))
            (equal (exec-expr-asg e compst fenv limit)
                   (write-object (value-pointer->designator ptr)
                                 (,atype-array-write array index val)
                                 compst))))
         (event
          `(defruled ,name
             ,formula
             :expand ((exec-expr-pure (expr-binary->arg1 e) compst)
                      (exec-expr-pure (expr-arrsub->arr
                                       (expr-binary->arg1 e)) compst))
             :enable (exec-expr-asg
                      exec-ident
                      exec-arrsub
                      apconvert-expr-value-when-not-value-array-alt
                      value-kind-not-array-when-cintegerp
                      read-object-of-objdesign-of-var-to-read-var
                      ,value-array->elemtype-when-apred
                      value-integer->get-when-cintegerp
                      ,atype-array-index-okp
                      integer-range-p
                      ,value-array-read-when-apred
                      ,value-array-write-when-apred
                      write-object)
             :disable (equal-of-error
                       equal-of-expr-value
                       equal-of-objdesign-element)
             :prep-lemmas
             ((defrule lemma
                (implies (and (expr-valuep (apconvert-expr-value eval))
                              (,epred (expr-value->value
                                       (apconvert-expr-value eval))))
                         (,epred (expr-value->value eval)))
                :enable apconvert-expr-value))))
         (name-mod-prf (pack name '-for-modular-proofs))
         (formula-mod-prf
          `(implies
            (and (equal (expr-kind e) :binary)
                 (equal (binop-kind (expr-binary->op e)) :asg)
                 (equal left (expr-binary->arg1 e))
                 (equal right (expr-binary->arg2 e))
                 (equal (expr-kind left) :arrsub)
                 (equal arr (expr-arrsub->arr left))
                 (equal sub (expr-arrsub->sub left))
                 (equal (expr-kind arr) :ident)
                 (not (zp limit))
                 (equal arr-eval (exec-expr-pure arr compst))
                 (expr-valuep arr-eval)
                 (equal ptr-eval (apconvert-expr-value arr-eval))
                 (expr-valuep ptr-eval)
                 (equal ptr (expr-value->value ptr-eval))
                 (value-case ptr :pointer)
                 (value-pointer-validp ptr)
                 (equal (value-pointer->reftype ptr)
                        ,(type-to-maker atype))
                 (equal array
                        (read-object (value-pointer->designator ptr) compst))
                 (,apred array)
                 (equal sub-eval (exec-expr-pure sub compst))
                 (expr-valuep sub-eval)
                 (equal index-eval (apconvert-expr-value sub-eval))
                 (expr-valuep index-eval)
                 (equal index (expr-value->value index-eval))
                 (cintegerp index)
                 (,atype-array-index-okp array index)
                 (equal right-eval (exec-expr-pure right compst))
                 (expr-valuep right-eval)
                 (equal eval (apconvert-expr-value right-eval))
                 (expr-valuep eval)
                 (equal val (expr-value->value eval))
                 (,epred val))
            (equal (exec-expr-asg e compst fenv limit)
                   (write-object (value-pointer->designator ptr)
                                 (,atype-array-write array index val)
                                 compst))))
         (event-mod-prf
          `(defruled ,name-mod-prf
             ,formula-mod-prf
             :enable (,name
                      read-var-to-read-object-of-objdesign-of-var
                      valuep-of-read-object-of-objdesign-of-var
                      exec-expr-pure-when-ident-no-syntaxp
                      exec-ident))))
      (mv name (list event event-mod-prf))))

  (define atc-exec-expr-asg-arrsub-rules-gen-loop ((atypes type-listp))
    :guard (type-nonchar-integer-listp atypes)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp atypes)) (mv nil nil))
         ((mv name events) (atc-exec-expr-asg-arrsub-rules-gen (car atypes)))
         ((mv more-names more-events)
          (atc-exec-expr-asg-arrsub-rules-gen-loop (cdr atypes))))
      (mv (cons name more-names)
          (append events more-events))))

  (define atc-exec-expr-asg-arrsub-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-expr-asg-arrsub-rules-gen-loop *nonchar-integer-types*)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-asg-rules
  :short "Rules for executing assignment expressions."

  (defval *atc-exec-expr-asg-rules*
    (append *atc-exec-expr-asg-ident-rules*
            *atc-exec-expr-asg-indir-rules*
            *atc-exec-expr-asg-arrsub-rules*)))
