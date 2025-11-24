; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/dynamic-semantics")
(include-book "../../language/pure-expression-execution")
(include-book "../pointed-integers")
(include-book "../read-write-variables")

(include-book "../types")

(include-book "arrays")
(include-book "value-integer-get")
(include-book "apconvert")
(include-book "integers")
(include-book "exec-expr-pure")

(local (include-book "../../language/variable-resolution-preservation"))

(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-when-asg-ident-rules
  :short "Rules for executing assignment expressions to identifier expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first one is used in the large symbolic execution.")
   (xdoc::p
    "The second one is for the new modular proof approach."))

  (defruled exec-expr-when-asg-ident
    (implies (and (syntaxp (quotep expr))
                  (not (zp limit))
                  (equal (expr-kind expr) :binary)
                  (equal (binop-kind (expr-binary->op expr)) :asg)
                  (equal left (expr-binary->arg1 expr))
                  (equal right (expr-binary->arg2 expr))
                  (equal (expr-kind left) :ident)
                  (equal var (expr-ident->get left))
                  (equal oldval (read-var var compst))
                  (valuep oldval)
                  (not (equal (value-kind oldval) :array))
                  (equal eval+compst1
                         (exec-expr right compst fenv (1- limit)))
                  (equal eval (mv-nth 0 eval+compst1))
                  (equal compst1 (mv-nth 1 eval+compst1))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1)
                  (equal newval (expr-value->value eval1))
                  (equal compst2 (write-var var newval compst1))
                  (compustatep compst2))
             (equal (exec-expr expr compst fenv limit)
                    (mv (expr-value newval nil) compst2)))
    :expand (exec-expr expr compst fenv limit)
    :use (:instance write-object-of-objdesign-of-var-to-write-var
                    (var (expr-ident->get (expr-binary->arg1 expr)))
                    (val (expr-value->value
                          (apconvert-expr-value
                           (mv-nth 0 (exec-expr (expr-binary->arg2 expr)
                                                compst fenv (+ -1 limit))))))
                    (compst (mv-nth 1 (exec-expr (expr-binary->arg2 expr)
                                                 compst fenv (+ -1 limit)))))
    :disable cons-equal
    :enable (exec-expr
             exec-ident
             expr-purep
             binop-purep
             var-resolve-of-exec-expr
             apconvert-expr-value-when-not-value-array
             read-object-of-objdesign-of-var-to-read-var))

  (defruled exec-expr-when-asg-ident-via-object
    (implies (and (syntaxp (quotep expr))
                  (not (zp limit))
                  (equal (expr-kind expr) :binary)
                  (equal (binop-kind (expr-binary->op expr)) :asg)
                  (equal left (expr-binary->arg1 expr))
                  (equal right (expr-binary->arg2 expr))
                  (equal (expr-kind left) :ident)
                  (equal objdes
                         (objdesign-of-var (expr-ident->get left) compst))
                  objdes
                  (not (equal (value-kind (read-object objdes compst))
                              :array))
                  (equal eval+compst1
                         (exec-expr right compst fenv (1- limit)))
                  (equal eval (mv-nth 0 eval+compst1))
                  (equal compst1 (mv-nth 1 eval+compst1))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1)
                  (equal val (expr-value->value eval1))
                  (equal compst2 (write-object objdes val compst1))
                  (compustatep compst2))
             (equal (exec-expr expr compst fenv limit)
                    (mv (expr-value val nil) compst2)))
    :expand (exec-expr expr compst fenv limit)
    :enable (exec-expr
             exec-ident
             expr-purep
             binop-purep
             apconvert-expr-value-when-not-value-array))

  (defval *atc-exec-expr-when-asg-ident-rules*
    '(exec-expr-when-asg-ident
      (:e expr-kind)
      (:e expr-binary->op)
      (:e expr-binary->arg1)
      (:e expr-binary->arg2)
      (:e expr-ident->get)
      (:e binop-kind))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-when-asg-indir-rule-generation
  :short "Code to generate the rules for executing
          assignments to integers by pointer."

  (define atc-exec-expr-when-asg-indir-rules-gen ((type typep))
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
         (name (pack 'exec-expr-when-asg-indir-when- pred))
         (name-mod-proofs (pack name '-for-modular-proofs))
         (formula
          `(implies
            (and (syntaxp (quotep expr))
                 (equal (expr-kind expr) :binary)
                 (equal (binop-kind (expr-binary->op expr)) :asg)
                 (equal left (expr-binary->arg1 expr))
                 (equal right (expr-binary->arg2 expr))
                 (equal (expr-kind left) :unary)
                 (equal (unop-kind (expr-unary->op left)) :indir)
                 (equal arg (expr-unary->arg left))
                 (equal (expr-kind arg) :ident)
                 (equal var (expr-ident->get arg))
                 (expr-purep right)
                 (integerp limit)
                 (>= limit (1+ (max 2 (expr-pure-limit right))))
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
                 (equal oldval
                        (read-object (value-pointer->designator ptr) compst))
                 (valuep oldval)
                 (not (equal (value-kind oldval) :array))
                 (equal compst1
                        (write-object (value-pointer->designator ptr)
                                      val
                                      compst))
                 (compustatep compst1))
            (equal (exec-expr expr compst fenv limit)
                   (mv (expr-value val nil) compst1))))
         (formula-mod-proofs
          `(implies
            (and (syntaxp (quotep expr))
                 (equal (expr-kind expr) :binary)
                 (equal (binop-kind (expr-binary->op expr)) :asg)
                 (equal left (expr-binary->arg1 expr))
                 (equal right (expr-binary->arg2 expr))
                 (equal (expr-kind left) :unary)
                 (equal (unop-kind (expr-unary->op left)) :indir)
                 (equal arg (expr-unary->arg left))
                 (equal (expr-kind arg) :ident)
                 (equal var (expr-ident->get arg))
                 (expr-purep right)
                 (integerp limit)
                 (>= limit (1+ (max 2 (expr-pure-limit right))))
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
                 (equal oldval
                        (read-object (value-pointer->designator ptr) compst))
                 (valuep oldval)
                 (not (equal (value-kind oldval) :array))
                 (equal compst1
                        (write-object (value-pointer->designator ptr)
                                      (,writer val)
                                      compst))
                 (compustatep compst1))
            (equal (exec-expr expr compst fenv limit)
                   (mv (expr-value val nil) compst1))))
         (events `((defruled ,name
                     ,formula
                     :expand ((exec-expr expr compst fenv limit)
                              (exec-expr (expr-binary->arg1 expr)
                                         compst fenv (1- limit)))
                     :enable (exec-expr-to-exec-expr-pure
                              max
                              nfix
                              exec-expr
                              exec-unary
                              exec-indir
                              exec-ident
                              apconvert-expr-value-when-not-value-array-alt
                              value-kind-when-scharp
                              read-object-of-objdesign-of-var-to-read-var
                              ,type-of-value-when-pred
                              ,not-pred-of-value-pointer
                              ,value-kind-when-pred
                              expr-purep
                              binop-purep)
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

  (define atc-exec-expr-when-asg-indir-rules-gen-loop ((types type-listp))
    :guard (type-nonchar-integer-listp types)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp types)) (mv nil nil))
         ((mv name events)
          (atc-exec-expr-when-asg-indir-rules-gen (car types)))
         ((mv more-names more-events)
          (atc-exec-expr-when-asg-indir-rules-gen-loop (cdr types))))
      (mv (cons name more-names) (append events more-events))))

  (define atc-exec-expr-when-asg-indir-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-expr-when-asg-indir-rules-gen-loop *nonchar-integer-types*)))
      `(progn
         (defsection atc-exec-expr-when-asg-indir-rules
           :short "Rules for executing assignment expressions
                 to integers by pointer."
           ,@events
           (defval *atc-exec-expr-when-asg-indir-rules*
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

(make-event (atc-exec-expr-when-asg-indir-rules-gen-all))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-when-asg-arrsub-rules-generation
  :short "Code to generate the rules for executing
          assignments to array subscripting expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a rule for the large symbolic execution,
     and also a rule for the modular proofs.
     The former will be eventually eliminated,
     once modular proofs cover all the ATC constructs."))

  (define atc-exec-expr-when-asg-arrsub-rules-gen ((atype typep))
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
         (name (pack 'exec-expr-when-asg-arrsub-when- apred))
         (formula
          `(implies
            (and (equal (expr-kind expr) :binary)
                 (equal (binop-kind (expr-binary->op expr)) :asg)
                 (equal left (expr-binary->arg1 expr))
                 (equal right (expr-binary->arg2 expr))
                 (equal (expr-kind left) :arrsub)
                 (equal arr (expr-arrsub->arr left))
                 (equal sub (expr-arrsub->sub left))
                 (equal (expr-kind arr) :ident)
                 (equal var (expr-ident->get arr))
                 (expr-purep right)
                 (integerp limit)
                 (>= limit (1+ (max (1+ (expr-pure-limit sub))
                                    (expr-pure-limit right))))
                 (expr-purep sub)
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
                 (,epred val)
                 (equal compst1
                        (write-object (value-pointer->designator ptr)
                                      (,atype-array-write array index val)
                                      compst))
                 (compustatep compst1))
            (equal (exec-expr expr compst fenv limit)
                   (mv (expr-value val nil) compst1))))
         (event
          `(defruled ,name
             ,formula
             :expand ((exec-expr expr compst fenv limit)
                      (exec-expr (expr-binary->arg1 expr)
                                 compst fenv (1- limit)))
             :enable (exec-expr-to-exec-expr-pure
                      max
                      nfix
                      exec-expr
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
                      write-object
                      expr-purep
                      binop-purep)
             :disable (equal-of-error
                       equal-of-expr-value
                       equal-of-objdesign-element
                       cons-equal
                       acl2::subsetp-member)
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
            (and (equal (expr-kind expr) :binary)
                 (equal (binop-kind (expr-binary->op expr)) :asg)
                 (equal left (expr-binary->arg1 expr))
                 (equal right (expr-binary->arg2 expr))
                 (equal (expr-kind left) :arrsub)
                 (equal arr (expr-arrsub->arr left))
                 (equal sub (expr-arrsub->sub left))
                 (equal (expr-kind arr) :ident)
                 (expr-purep right)
                 (integerp limit)
                 (>= limit (1+ (max (1+ (expr-pure-limit sub))
                                    (expr-pure-limit right))))
                 (expr-purep sub)
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
                 (,epred val)
                 (equal compst1
                        (write-object (value-pointer->designator ptr)
                                      (,atype-array-write array index val)
                                      compst))
                 (compustatep compst1))
            (equal (exec-expr expr compst fenv limit)
                   (mv (expr-value val nil) compst1))))
         (event-mod-prf
          `(defruled ,name-mod-prf
             ,formula-mod-prf
             :enable (,name
                      read-var-to-read-object-of-objdesign-of-var
                      valuep-of-read-object-of-objdesign-of-var
                      exec-expr-pure-when-ident-no-syntaxp
                      exec-ident))))
      (mv name (list event event-mod-prf))))

  (define atc-exec-expr-when-asg-arrsub-rules-gen-loop ((atypes type-listp))
    :guard (type-nonchar-integer-listp atypes)
    :returns (mv (names symbol-listp)
                 (events pseudo-event-form-listp))
    :parents nil
    (b* (((when (endp atypes)) (mv nil nil))
         ((mv name events) (atc-exec-expr-when-asg-arrsub-rules-gen (car atypes)))
         ((mv more-names more-events)
          (atc-exec-expr-when-asg-arrsub-rules-gen-loop (cdr atypes))))
      (mv (cons name more-names)
          (append events more-events))))

  (define atc-exec-expr-when-asg-arrsub-rules-gen-all ()
    :returns (event pseudo-event-formp)
    :parents nil
    (b* (((mv names events)
          (atc-exec-expr-when-asg-arrsub-rules-gen-loop *nonchar-integer-types*)))
      `(progn
         (defsection atc-exec-expr-when-asg-arrsub-rules
           :short "Rules for executing assignment expressions to
                   array subscript expressions."
           ,@events
           (defval *atc-exec-expr-when-asg-arrsub-rules*
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

(make-event (atc-exec-expr-when-asg-arrsub-rules-gen-all))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-when-asg-rules
  :short "Rules for executing assignment expressions."

  (defval *atc-exec-expr-when-asg-rules*
    (append *atc-exec-expr-when-asg-ident-rules*
            *atc-exec-expr-when-asg-indir-rules*
            *atc-exec-expr-when-asg-arrsub-rules*)))
