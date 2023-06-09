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

(include-book "abstract-syntax")
(include-book "variable-tables")
(include-book "tag-tables")
(include-book "term-checkers-atc")
(include-book "generation-contexts")
(include-book "theorem-generation")

(include-book "kestrel/fty/pseudo-event-form-list" :dir :system)
(include-book "kestrel/std/basic/if-star" :dir :system)

(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "kestrel/std/system/w" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-expression-generation
  :parents (atc-event-and-code-generation)
  :short "Generation of C expressions."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexpr-gin
  :short "Inputs for C pure expression generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not include the term, which is passed as a separate input."))
  ((context atc-contextp)
   (inscope atc-symbol-varinfo-alist-list)
   (prec-tags atc-string-taginfo-alist)
   (fn symbol)
   (fn-guard symbol)
   (compst-var symbol)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool)
   (deprecated symbol-list))
  :pred pexpr-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexpr-gout
  :short "Outputs for C pure expression generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The generated expression is @('expr'),
     and its type is @('type')."))
  ((expr expr)
   (type type)
   (term pseudo-termp)
   (events pseudo-event-form-list)
   (thm-name symbol)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred pexpr-goutp)

;;;;;;;;;;

(defirrelevant irr-pexpr-gout
  :short "An irrelevant output for C pure expression generation."
  :type pexpr-goutp
  :body (make-pexpr-gout :expr (irr-expr)
                         :type (irr-type)
                         :term nil
                         :events nil
                         :thm-name nil
                         :thm-index 1
                         :names-to-avoid nil
                         :proofs nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-var ((var symbolp)
                          (gin pexpr-ginp)
                          state)
  :returns (gout pexpr-goutp)
  :short "Generate a C expression from an ACL2 variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "An ACL2 variable is translated to a C variable.
     Its information is looked up in the symbol table.")
   (xdoc::p
    "If the variable has pointer or array type and is not an external object,
     its correctness theorem equates it to the @('-ptr') variable."))
  (b* (((pexpr-gin gin) gin)
       (info (atc-get-var var gin.inscope))
       ((when (not info))
        (raise "Internal error: the variable ~x0 in function ~x1 ~
                has no associated information." var gin.fn)
        (irr-pexpr-gout))
       (type (atc-var-info->type info))
       (var-thm (atc-var-info->thm info))
       (expr (expr-ident (make-ident :name (symbol-name var))))
       ((when (not gin.proofs))
        (make-pexpr-gout
         :expr expr
         :type type
         :term var
         :events nil
         :thm-name nil
         :thm-index gin.thm-index
         :names-to-avoid gin.names-to-avoid
         :proofs nil))
       (hints
        `(("Goal" :in-theory '(,var-thm
                               exec-expr-pure-when-ident
                               (:e expr-kind)
                               (:e expr-ident->get)
                               exec-ident-open-via-object
                               (:e identp)
                               (:e ident->name)
                               objdesign-of-var-of-const-identifier))))
       (objdes `(objdesign-of-var (ident ',(symbol-name var)) ,gin.compst-var))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       type
                                       (if (and (or (type-case type :pointer)
                                                    (type-case type :array))
                                                (not (atc-var-info->externalp
                                                      info)))
                                           (add-suffix-to-fn var "-PTR")
                                         var)
                                       var
                                       objdes
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       gin.thm-index
                                       gin.names-to-avoid
                                       state)))
    (make-pexpr-gout :expr expr
                     :type type
                     :term var
                     :events (list thm-event)
                     :thm-name thm-name
                     :thm-index thm-index
                     :names-to-avoid names-to-avoid
                     :proofs t))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-const ((term pseudo-termp)
                            (const iconstp)
                            (type typep)
                            (type-base-const symbolp)
                            (gin pexpr-ginp)
                            state)
  :guard (type-nonchar-integerp type)
  :returns (gout pexpr-goutp)
  :short "Generate a C expression and theorem from an ACL2 term
          that represents an integer constant expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The C integer constant is actually calculated by the caller,
     and passed as input here.")
   (xdoc::p
    "The theorem says that the execution yields the term.
     It also says that the term satisfies
     the applicable shallowly embedded type predicate.")
   (xdoc::p
    "This theorem holds unconditionally;
     it does not actually depend on the computation state.
     We do not need to contextualize the theorem,
     i.e. we ignore the @(tsee atc-context).")
   (xdoc::p
    "The hints cover all possible integer constants,
     but we could make them more nuanced to the specifics of the constant."))
  (b* (((pexpr-gin gin) gin)
       (expr (expr-const (const-int const)))
       ((when (not gin.proofs))
        (make-pexpr-gout :expr expr
                         :type type
                         :term term
                         :events nil
                         :thm-name nil
                         :thm-index gin.thm-index
                         :names-to-avoid gin.names-to-avoid
                         :proofs nil))
       (hints
        (b* ((fixtype (integer-type-to-fixtype type))
             (exec-const-to-fixtype (pack 'exec-const-to- fixtype))
             (fixtype-integerp (pack fixtype '-integerp))
             (recognizer (atc-type-to-recognizer type gin.prec-tags))
             (valuep-when-recognizer (pack 'valuep-when- recognizer))
             (recognizer-of-fixtype-from-integer
              (pack recognizer '-of- fixtype '-from-integer)))
          `(("Goal" :in-theory '(exec-expr-pure-when-const
                                 (:e expr-kind)
                                 (:e expr-const->get)
                                 ,exec-const-to-fixtype
                                 (:e const-kind)
                                 (:e const-int->get)
                                 (:e iconst->unsignedp)
                                 (:e iconst->length)
                                 (:e iconst->value)
                                 (:e iconst->base)
                                 (:e iconst-length-kind)
                                 (:e iconst-base-kind)
                                 (:e ,fixtype-integerp)
                                 ,type-base-const
                                 ,recognizer-of-fixtype-from-integer
                                 expr-valuep-of-expr-value
                                 expr-value->value-of-expr-value
                                 value-fix-when-valuep
                                 ,valuep-when-recognizer)))))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       type
                                       term
                                       term
                                       acl2::*nil*
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       gin.thm-index
                                       gin.names-to-avoid
                                       state)))
    (make-pexpr-gout :expr expr
                     :type type
                     :term term
                     :events (list thm-event)
                     :thm-name thm-name
                     :thm-index thm-index
                     :names-to-avoid names-to-avoid
                     :proofs t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-unary ((fn symbolp)
                            (arg-term pseudo-termp)
                            (arg-expr exprp)
                            (arg-type typep)
                            (arg-events pseudo-event-form-listp)
                            (arg-thm symbolp)
                            (in-type typep)
                            (out-type typep)
                            (op unopp)
                            (gin pexpr-ginp)
                            state)
  :guard (and (type-nonchar-integerp in-type)
              (type-nonchar-integerp out-type))
  :returns (mv erp (gout pexpr-goutp))
  :short "Generate a C expression and theorem from an ACL2 term
          that represents a unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression and theorem for the argument
     are generated in the caller, and passed here.")
   (xdoc::p
    "If the operation has an associated @('okp') predicate,
     we also generate a theorem saying that
     the @('okp') predicate holds under the guard."))
  (b* (((reterr) (irr-pexpr-gout))
       (wrld (w state))
       ((pexpr-gin gin) gin)
       ((unless (equal arg-type in-type))
        (reterr
         (msg "The unary operator ~x0 is applied ~
               to an expression term ~x1 returning ~x2, ~
               but a ~x3 operand is expected. ~
               This is indicative of provably dead code, ~
               given that the code is guard-verified."
              op arg-term arg-type in-type)))
       (expr (make-expr-unary :op op :arg arg-expr))
       (term `(,fn ,arg-term))
       ((when (not gin.proofs))
        (retok
         (make-pexpr-gout :expr expr
                          :type out-type
                          :term term
                          :events arg-events
                          :thm-name nil
                          :thm-index gin.thm-index
                          :names-to-avoid gin.names-to-avoid
                          :proofs nil)))
       (fn-okp (and (unop-case op :minus)
                    (not (member-eq (type-kind in-type)
                                    '(:uint :ulong :ullong)))
                    (pack fn '-okp)))
       ((mv okp-lemma-event?
            okp-lemma-name
            thm-index
            names-to-avoid)
        (if fn-okp
            (b* ((okp-lemma-name
                  (pack gin.fn '-expr- gin.thm-index '-okp-lemma))
                 ((mv okp-lemma-name names-to-avoid)
                  (fresh-logical-name-with-$s-suffix okp-lemma-name
                                                     nil
                                                     gin.names-to-avoid
                                                     wrld))
                 (arg-uterm (untranslate$ arg-term nil state))
                 (okp-lemma-formula `(,fn-okp ,arg-uterm))
                 (okp-lemma-formula
                  (atc-contextualize okp-lemma-formula
                                     gin.context
                                     gin.fn
                                     gin.fn-guard
                                     nil
                                     nil
                                     nil
                                     nil
                                     wrld))
                 (okp-lemma-hints
                  `(("Goal"
                     :in-theory '(,gin.fn-guard if* test* declar)
                     :use (:guard-theorem ,gin.fn))))
                 ((mv okp-lemma-event &)
                  (evmac-generate-defthm okp-lemma-name
                                         :formula okp-lemma-formula
                                         :hints okp-lemma-hints
                                         :enable nil)))
              (mv (list okp-lemma-event)
                  okp-lemma-name
                  (1+ gin.thm-index)
                  names-to-avoid))
          (mv nil nil gin.thm-index gin.names-to-avoid)))
       (hints
        (b* ((in-type-pred (atc-type-to-recognizer in-type gin.prec-tags))
             (valuep-when-in-type-pred (pack 'valuep-when- in-type-pred))
             (value-kind-when-in-type-pred
              (pack 'value-kind-when- in-type-pred))
             (op-name (pack (unop-kind op)))
             (exec-unary-when-op-and-in-type-pred
              (pack op-name '-value-when- in-type-pred))
             (type-pred (atc-type-to-recognizer out-type gin.prec-tags))
             (valuep-when-type-pred (pack 'valuep-when- type-pred))
             (type-pred-of-fn (pack type-pred '-of- fn)))
          `(("Goal" :in-theory '(exec-expr-pure-when-unary
                                 expr-valuep-of-expr-value
                                 expr-value->value-of-expr-value
                                 (:e expr-kind)
                                 (:e expr-unary->op)
                                 (:e expr-unary->arg)
                                 ,arg-thm
                                 ,valuep-when-in-type-pred
                                 ,value-kind-when-in-type-pred
                                 ,valuep-when-type-pred
                                 value-fix-when-valuep
                                 ,exec-unary-when-op-and-in-type-pred
                                 (:e ,(pack 'unop- op-name))
                                 ,type-pred-of-fn
                                 ,@(and fn-okp
                                        (list okp-lemma-name)))))))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       out-type
                                       term
                                       term
                                       acl2::*nil*
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       thm-index
                                       names-to-avoid
                                       state)))
    (retok
     (make-pexpr-gout :expr expr
                      :type out-type
                      :term term
                      :events (append arg-events
                                      okp-lemma-event?
                                      (list thm-event))
                      :thm-name thm-name
                      :thm-index thm-index
                      :names-to-avoid names-to-avoid
                      :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-binary ((fn symbolp)
                             (arg1-term pseudo-termp)
                             (arg2-term pseudo-termp)
                             (arg1-expr exprp)
                             (arg2-expr exprp)
                             (arg1-type typep)
                             (arg2-type typep)
                             (arg1-events pseudo-event-form-listp)
                             (arg2-events pseudo-event-form-listp)
                             (arg1-thm symbolp)
                             (arg2-thm symbolp)
                             (in-type1 typep)
                             (in-type2 typep)
                             (out-type typep)
                             (op binopp)
                             (gin pexpr-ginp)
                             state)
  :guard (and (type-nonchar-integerp in-type1)
              (type-nonchar-integerp in-type2)
              (type-nonchar-integerp out-type))
  :returns (mv erp (gout pexpr-goutp))
  :short "Generate a C expression and theorem from an ACL2 term
          that represents a binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expressions and theorems for the arguments
     are generated in the caller, and passed here.")
   (xdoc::p
    "We do not yet support operations with an associated @('okp') predicate.
     We will add support for them soon."))
  (b* (((reterr) (irr-pexpr-gout))
       (wrld (w state))
       ((pexpr-gin gin) gin)
       ((unless (and (equal arg1-type in-type1)
                     (equal arg2-type in-type2)))
        (reterr
         (msg "The binary operator ~x0 is applied ~
               to an expression term ~x1 returning ~x2 ~
               and to an expression term ~x3 returning ~x4, ~
               but a ~x5 operand and a ~x6 operand are expected. ~
               This is indicative of provably dead code, ~
               given that the code is guard-verified."
              op arg1-term arg1-type arg2-term arg2-type in-type1 in-type2)))
       (expr (make-expr-binary :op op :arg1 arg1-expr :arg2 arg2-expr))
       ((when (eq fn 'quote))
        (reterr (raise "Internal error: function symbol is QUOTE.")))
       (term `(,fn ,arg1-term ,arg2-term))
       ((when (not gin.proofs))
        (retok
         (make-pexpr-gout :expr expr
                          :type out-type
                          :term term
                          :events (append arg1-events arg2-events)
                          :thm-name nil
                          :thm-index gin.thm-index
                          :names-to-avoid gin.names-to-avoid
                          :proofs nil)))
       (op-name (pack (binop-kind op)))
       (fn-okp (and (or (member-eq (binop-kind op) '(:div :rem :shl :shr))
                        (and (member-eq (binop-kind op) '(:add :sub :mul))
                             (type-signed-integerp out-type)))
                    (pack fn '-okp)))
       ((mv okp-lemma-event?
            okp-lemma-name
            thm-index
            names-to-avoid)
        (if fn-okp
            (b* ((okp-lemma-name
                  (pack gin.fn '-expr- gin.thm-index '-okp-lemma))
                 ((mv okp-lemma-name names-to-avoid)
                  (fresh-logical-name-with-$s-suffix okp-lemma-name
                                                     nil
                                                     gin.names-to-avoid
                                                     wrld))
                 (arg1-uterm (untranslate$ arg1-term nil state))
                 (arg2-uterm (untranslate$ arg2-term nil state))
                 (okp-lemma-formula `(,fn-okp ,arg1-uterm ,arg2-uterm))
                 (okp-lemma-formula
                  (atc-contextualize okp-lemma-formula
                                     gin.context
                                     gin.fn
                                     gin.fn-guard
                                     nil
                                     nil
                                     nil
                                     nil
                                     wrld))
                 (okp-lemma-hints
                  `(("Goal"
                     :in-theory '(,gin.fn-guard if* test* declar)
                     :use (:guard-theorem ,gin.fn))))
                 ((mv okp-lemma-event &)
                  (evmac-generate-defthm okp-lemma-name
                                         :formula okp-lemma-formula
                                         :hints okp-lemma-hints
                                         :enable nil)))
              (mv (list okp-lemma-event)
                  okp-lemma-name
                  (1+ gin.thm-index)
                  names-to-avoid))
          (mv nil nil gin.thm-index gin.names-to-avoid)))
       (hints
        (b* ((arg1-type-pred (atc-type-to-recognizer arg1-type gin.prec-tags))
             (arg2-type-pred (atc-type-to-recognizer arg2-type gin.prec-tags))
             (valuep-when-arg1-type-pred (pack 'valuep-when- arg1-type-pred))
             (valuep-when-arg2-type-pred (pack 'valuep-when- arg2-type-pred))
             (value-kind-when-arg1-type-pred (pack 'value-kind-when-
                                                   arg1-type-pred))
             (value-kind-when-arg2-type-pred (pack 'value-kind-when-
                                                   arg2-type-pred))
             (exec-binary-strict-pure-when-op
              (pack 'exec-binary-strict-pure-when- op-name))
             (type-pred (atc-type-to-recognizer out-type gin.prec-tags))
             (arg1-fixtype (integer-type-to-fixtype arg1-type))
             (arg2-fixtype (integer-type-to-fixtype arg2-type))
             (op-values-when-arg1-type
              (pack op-name '-values-when- arg1-fixtype))
             (op-arg1-type-and-value-when-arg2-type
              (pack op-name '- arg1-fixtype '-and-value-when- arg2-fixtype))
             (type-pred-of-fn (pack type-pred '-of- fn))
             (valuep-when-type-pred (pack 'valuep-when- type-pred)))
          `(("Goal" :in-theory '(exec-expr-pure-when-strict-pure-binary
                                 (:e expr-kind)
                                 (:e expr-binary->op)
                                 (:e expr-binary->arg1)
                                 (:e expr-binary->arg2)
                                 (:e binop-kind)
                                 (:e member-equal)
                                 ,arg1-thm
                                 ,arg2-thm
                                 ,valuep-when-arg1-type-pred
                                 ,valuep-when-arg2-type-pred
                                 ,exec-binary-strict-pure-when-op
                                 (:e ,(pack 'binop- op-name))
                                 ,op-values-when-arg1-type
                                 ,op-arg1-type-and-value-when-arg2-type
                                 ,type-pred-of-fn
                                 ,@(and fn-okp
                                        (list okp-lemma-name))
                                 expr-valuep-of-expr-value
                                 expr-value->value-of-expr-value
                                 value-fix-when-valuep
                                 ,valuep-when-type-pred
                                 ,value-kind-when-arg1-type-pred
                                 ,value-kind-when-arg2-type-pred)))))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       out-type
                                       term
                                       term
                                       acl2::*nil*
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       thm-index
                                       names-to-avoid
                                       state)))
    (retok
     (make-pexpr-gout :expr expr
                      :type out-type
                      :term term
                      :events (append arg1-events
                                      arg2-events
                                      okp-lemma-event?
                                      (list thm-event))
                      :thm-name thm-name
                      :thm-index thm-index
                      :names-to-avoid names-to-avoid
                      :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-conv ((fn symbolp)
                           (arg-term pseudo-termp)
                           (arg-expr exprp)
                           (arg-type typep)
                           (arg-events pseudo-event-form-listp)
                           (arg-thm symbolp)
                           (in-type typep)
                           (out-type typep)
                           (tyname tynamep)
                           (gin pexpr-ginp)
                           state)
  :returns (mv erp (gout pexpr-goutp))
  :short "Generate a C expression from an ACL2 term
          that represents an integer conversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression and theorem for the argument
     are generated in the caller, and passed here.")
   (xdoc::p
    "For now we do not generate the theorem;
     we will add suppor for that later."))
  (b* (((reterr) (irr-pexpr-gout))
       (wrld (w state))
       ((pexpr-gin gin) gin)
       ((unless (equal arg-type in-type))
        (reterr
         (msg "The conversion from ~x0 to ~x1 is applied ~
               to an expression term ~x2 returning ~x3, ~
               which is not the expected type ~x0. ~
               This is indicative of provably dead code, ~
               given that the code is guard-verified."
              in-type out-type arg-term arg-type)))
       (expr (make-expr-cast :type tyname :arg arg-expr))
       (term `(,fn ,arg-term))
       ((when (not gin.proofs))
        (retok (make-pexpr-gout
                :expr expr
                :type out-type
                :term term
                :events arg-events
                :thm-name nil
                :thm-index gin.thm-index
                :names-to-avoid gin.names-to-avoid
                :proofs nil)))
       (fn-okp
        (and (or (type-case out-type :schar)
                 (and (type-case out-type :sshort)
                      (not (member-eq (type-kind in-type)
                                      '(:schar))))
                 (and (type-case out-type :sint)
                      (not (member-eq (type-kind in-type)
                                      '(:schar :sshort))))
                 (and (type-case out-type :slong)
                      (not (member-eq (type-kind in-type)
                                      '(:schar :sshort :sint))))
                 (and (type-case out-type :sllong)
                      (not (member-eq (type-kind in-type)
                                      '(:schar :sshort :sint :slong)))))
             (pack fn '-okp)))
       ((mv okp-lemma-event?
            okp-lemma-name
            thm-index
            names-to-avoid)
        (if fn-okp
            (b* ((okp-lemma-name
                  (pack gin.fn '-expr- gin.thm-index '-okp-lemma))
                 ((mv okp-lemma-name names-to-avoid)
                  (fresh-logical-name-with-$s-suffix okp-lemma-name
                                                     nil
                                                     gin.names-to-avoid
                                                     wrld))
                 (arg-uterm (untranslate$ arg-term nil state))
                 (okp-lemma-formula `(,fn-okp ,arg-uterm))
                 (okp-lemma-formula
                  (atc-contextualize okp-lemma-formula
                                     gin.context
                                     gin.fn
                                     gin.fn-guard
                                     nil
                                     nil
                                     nil
                                     nil
                                     wrld))
                 (okp-lemma-hints
                  `(("Goal"
                     :in-theory '(,gin.fn-guard if* test* declar)
                     :use (:guard-theorem ,gin.fn))))
                 ((mv okp-lemma-event &)
                  (evmac-generate-defthm okp-lemma-name
                                         :formula okp-lemma-formula
                                         :hints okp-lemma-hints
                                         :enable nil)))
              (mv (list okp-lemma-event)
                  okp-lemma-name
                  (1+ gin.thm-index)
                  names-to-avoid))
          (mv nil nil gin.thm-index gin.names-to-avoid)))
       (hints
        (b* ((arg-type-pred (atc-type-to-recognizer arg-type gin.prec-tags))
             (valuep-when-arg-type-pred (pack 'valuep-when- arg-type-pred))
             (exec-cast-of-out-type-when-arg-type-pred
              (pack 'exec-cast-of- (type-kind out-type) '-when- arg-type-pred))
             (type-pred (atc-type-to-recognizer out-type gin.prec-tags))
             (type-pred-of-fn (pack type-pred '-of- fn))
             (valuep-when-type-pred (pack 'valuep-when- type-pred)))
          `(("Goal" :in-theory '(exec-expr-pure-when-cast
                                 (:e expr-kind)
                                 (:e expr-cast->type)
                                 (:e expr-cast->arg)
                                 ,arg-thm
                                 ,valuep-when-arg-type-pred
                                 ,exec-cast-of-out-type-when-arg-type-pred
                                 ,type-pred-of-fn
                                 ,@(and fn-okp
                                        (list okp-lemma-name))
                                 expr-valuep-of-expr-value
                                 expr-value->value-of-expr-value
                                 value-fix-when-valuep
                                 ,valuep-when-type-pred)))))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       out-type
                                       term
                                       term
                                       acl2::*nil*
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       thm-index
                                       names-to-avoid
                                       state)))
    (retok
     (make-pexpr-gout :expr expr
                      :type out-type
                      :term term
                      :events (append arg-events
                                      okp-lemma-event?
                                      (list thm-event))
                      :thm-name thm-name
                      :thm-index thm-index
                      :names-to-avoid names-to-avoid
                      :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-bool-from-type ((fn symbolp)
                                     (arg-term pseudo-termp)
                                     (arg-expr exprp)
                                     (arg-type typep)
                                     (arg-events pseudo-event-form-listp)
                                     (arg-thm symbolp)
                                     (in-type typep)
                                     (gin pexpr-ginp)
                                     state)
  :returns (mv erp (gout pexpr-goutp))
  :short "Generate a C expression from an ACL2 term
          that represents a conversion to ACL2 boolean."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression is the same as the one for the argument term:
     the conversion to ACL2 boolean
     only serves a purpose in the ACL2 representation
     but it has no counterpart in the C code.")
   (xdoc::p
    "The argument term is the @('cterm')
     passed to @(tsee atc-gen-expr-bool-correct-thm);
     see the documentation of that function for the distinction
     between @('cterm') and @('aterm').
     For the @('aterm'), we use the ACL2 term from which
     the expression is generated, i.e. @('(boolean-from-<type> <arg-term>)').")
   (xdoc::p
    "The hints include
     the compound recognizer @('booleanp-compound-recognizer')
     in order to prove that @('t') or @('nil') satisfies @(tsee booleanp),
     in case the term or its negation happens to be in context
     and thus gets rewritten to @('t') or @('nil')."))
  (b* (((reterr) (irr-pexpr-gout))
       ((pexpr-gin gin) gin)
       ((unless (equal arg-type in-type))
        (reterr
         (msg "The conversion from ~x0 to boolean is applied to ~
               an expression term ~x1 returning ~x2, ~
               but a ~x0 operand is expected. ~
               This is indicative of provably dead code, ~
               given that the code is guard-verified."
              in-type arg-term arg-type)))
       (expr arg-expr)
       (aterm `(,fn ,arg-term))
       (type arg-type)
       ((when (not gin.proofs))
        (retok
         (make-pexpr-gout :expr expr
                          :type arg-type
                          :term aterm
                          :events arg-events
                          :thm-name nil
                          :thm-index gin.thm-index
                          :names-to-avoid gin.names-to-avoid
                          :proofs nil)))
       (cterm arg-term)
       ((unless (type-nonchar-integerp type))
        (reterr (raise "Internal error: non-integer type ~x0." type)))
       (type-pred (atc-type-to-recognizer type gin.prec-tags))
       (test-value-when-type-pred (pack 'test-value-when- type-pred))
       (booleanp-of-fn (pack 'booleanp-of- fn))
       (hints `(("Goal" :in-theory '(,arg-thm
                                     ,test-value-when-type-pred
                                     ,booleanp-of-fn
                                     booleanp-compound-recognizer))))
       (objdes (if (expr-case expr :ident)
                   `(objdesign-of-var
                     (ident ',(ident->name (expr-ident->get expr)))
                     ,gin.compst-var)
                 acl2::*nil*))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-bool-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       type
                                       aterm
                                       cterm
                                       objdes
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       gin.thm-index
                                       gin.names-to-avoid
                                       state)))
    (retok (make-pexpr-gout :expr expr
                            :type type
                            :term aterm
                            :events (append arg-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid names-to-avoid
                            :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-cond ((term pseudo-termp)
                           (test-term pseudo-termp)
                           (then-term pseudo-termp)
                           (else-term pseudo-termp)
                           (test-expr exprp)
                           (then-expr exprp)
                           (else-expr exprp)
                           (test-type typep)
                           (then-type typep)
                           (else-type typep)
                           (test-thm symbolp)
                           (then-thm symbolp)
                           (else-thm symbolp)
                           (test-events pseudo-event-form-listp)
                           (then-events pseudo-event-form-listp)
                           (else-events pseudo-event-form-listp)
                           (gin pexpr-ginp)
                           state)
  :returns (mv erp (gout pexpr-goutp))
  :short "Generate a C expression from an ACL2 term
          that represents a ternary conditional expression."
  (b* (((reterr) (irr-pexpr-gout))
       (wrld (w state))
       ((pexpr-gin gin) gin)
       ((unless (equal then-type else-type))
        (reterr
         (msg "When generating C code for the function ~x0, ~
               two branches ~x1 and ~x2 of a conditional term ~
               have different types ~x3 and ~x4; ~
               use conversion operations, if needed, ~
               to make the branches of the same type."
              gin.fn then-term else-term then-type else-type)))
       (type then-type)
       ((when (member-equal type (list (type-uchar)
                                       (type-schar)
                                       (type-ushort)
                                       (type-sshort))))
        (reterr
         (msg "When generating C code for the function ~x0, ~
               two branches of the conditional term ~x1 ~
               have type ~x2, which is disallowed; ~
               use conversion operations, if needed, ~
               to turn the branches into an integer type of higher rank."
              gin.fn term type)))
       (expr (make-expr-cond :test test-expr
                             :then then-expr
                             :else else-expr))
       ((when (not gin.proofs))
        (retok
         (make-pexpr-gout
          :expr expr
          :type type
          :term term
          :events (append test-events then-events else-events)
          :thm-name nil
          :thm-index gin.thm-index
          :names-to-avoid gin.names-to-avoid
          :proofs nil)))
       (test-type-pred (atc-type-to-recognizer test-type gin.prec-tags))
       (valuep-when-test-type-pred (pack 'valuep-when- test-type-pred))
       (type-pred (atc-type-to-recognizer type gin.prec-tags))
       (valuep-when-type-pred (pack 'valuep-when- type-pred))
       (value-kind-when-type-pred (pack 'value-kind-when- type-pred))
       (value-kind-when-test-type-pred (pack 'value-kind-when- test-type-pred))
       (term* `(condexpr (if* ,test-term ,then-term ,else-term)))
       (hints-then
        `(("Goal" :in-theory '(exec-expr-pure-when-cond-and-true
                               (:e expr-kind)
                               (:e expr-cond->test)
                               ,test-thm
                               (:e expr-cond->then)
                               ,then-thm
                               (:e expr-cond->else)
                               ,else-thm
                               booleanp-compound-recognizer
                               ,valuep-when-test-type-pred
                               expr-valuep-of-expr-value
                               expr-value->value-of-expr-value
                               value-fix-when-valuep
                               ,valuep-when-type-pred
                               apconvert-expr-value-when-not-value-array
                               ,value-kind-when-type-pred
                               ,value-kind-when-test-type-pred))))
       (hints-else
        `(("Goal" :in-theory '(exec-expr-pure-when-cond-and-false
                               (:e expr-kind)
                               (:e expr-cond->test)
                               ,test-thm
                               (:e expr-cond->then)
                               ,then-thm
                               (:e expr-cond->else)
                               ,else-thm
                               booleanp-compound-recognizer
                               ,valuep-when-test-type-pred
                               expr-valuep-of-expr-value
                               expr-value->value-of-expr-value
                               value-fix-when-valuep
                               ,valuep-when-type-pred
                               apconvert-expr-value-when-not-value-array
                               ,value-kind-when-type-pred
                               ,value-kind-when-test-type-pred))))
       (instructions
        `((casesplit
           ,(atc-contextualize test-term
                               gin.context nil nil nil nil nil nil wrld))
          (claim ,(atc-contextualize `(test* ,test-term)
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(test*))))
          (drop 1)
          (claim ,(atc-contextualize
                   `(equal (condexpr (if* ,test-term ,then-term ,else-term))
                           ,then-term)
                   gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal"
                          :in-theory '(acl2::if*-when-true
                                       condexpr
                                       test*))))
          (prove :hints ,hints-then)
          (claim ,(atc-contextualize `(test* (not ,test-term))
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(test*))))
          (drop 1)
          (claim ,(atc-contextualize
                   `(equal (condexpr (if* ,test-term ,then-term ,else-term))
                           ,else-term)
                   gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal"
                          :in-theory '(acl2::if*-when-false
                                       condexpr
                                       test*))))
          (prove :hints ,hints-else)))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       type
                                       term*
                                       term*
                                       acl2::*nil*
                                       gin.compst-var
                                       nil
                                       instructions
                                       gin.prec-tags
                                       gin.thm-index
                                       gin.names-to-avoid
                                       state)))
    (retok
     (make-pexpr-gout
      :expr expr
      :type type
      :term term*
      :events (append test-events
                      then-events
                      else-events
                      (list thm-event))
      :thm-name thm-name
      :thm-index thm-index
      :names-to-avoid names-to-avoid
      :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-and ((arg1-term pseudo-termp)
                          (arg2-term pseudo-termp)
                          (arg1-expr exprp)
                          (arg2-expr exprp)
                          (arg1-type typep)
                          (arg2-type typep)
                          (arg1-thm symbolp)
                          (arg2-thm symbolp)
                          (arg1-events pseudo-event-form-listp)
                          (arg2-events pseudo-event-form-listp)
                          (gin pexpr-ginp)
                          state)
  :returns (gout pexpr-goutp)
  :short "Generate a C expression from an ACL2 term
          that represents a logical conjunction."
  :long
  (xdoc::topstring
   (xdoc::p
    "The term returns an ACL2 boolean,
     which is equated, in the generated theorem, to @(tsee test-value).
     However, we also need a term to equate to
     the execution of the C expression:
     we wrap the term with @(tsee sint-from-boolean) for this purpsoe,
     obtaining a term that returns a C @('int') instead of an ACL2 boolean."))
  (b* (((pexpr-gin gin) gin)
       (wrld (w state))
       (term `(if* ,arg1-term ,arg2-term 'nil))
       (expr (make-expr-binary :op (binop-logand)
                               :arg1 arg1-expr
                               :arg2 arg2-expr))
       (type (type-sint))
       ((when (not gin.proofs))
        (make-pexpr-gout
         :expr expr
         :type type
         :term term
         :events (append arg1-events arg2-events)
         :thm-name nil
         :thm-index gin.thm-index
         :names-to-avoid gin.names-to-avoid
         :proofs nil))
       (cterm `(sint-from-boolean ,term))
       (arg1-type-pred (atc-type-to-recognizer arg1-type gin.prec-tags))
       (arg2-type-pred (atc-type-to-recognizer arg2-type gin.prec-tags))
       (valuep-when-arg1-type-pred (pack 'valuep-when- arg1-type-pred))
       (valuep-when-arg2-type-pred (pack 'valuep-when- arg2-type-pred))
       (value-kind-when-arg1-type-pred (pack 'value-kind-when- arg1-type-pred))
       (value-kind-when-arg2-type-pred (pack 'value-kind-when- arg2-type-pred))
       (hints-then
        `(("Goal"
           :in-theory '(exec-expr-pure-when-binary-logand-and-true
                        (:e expr-kind)
                        (:e expr-binary->op)
                        (:e binop-kind)
                        (:e expr-binary->arg1)
                        ,arg1-thm
                        ,valuep-when-arg1-type-pred
                        (:e expr-binary->arg2)
                        ,arg2-thm
                        ,valuep-when-arg2-type-pred
                        sintp-of-sint-from-boolean
                        test-value-when-sintp
                        boolean-from-sint-of-sint-from-boolean
                        expr-valuep-of-expr-value
                        expr-value->value-of-expr-value
                        value-fix-when-valuep
                        apconvert-expr-value-when-not-value-array
                        ,value-kind-when-arg1-type-pred
                        ,value-kind-when-arg2-type-pred))))
       (hints-else
        `(("Goal"
           :in-theory '(exec-expr-pure-when-binary-logand-and-false
                        (:e expr-kind)
                        (:e expr-binary->op)
                        (:e binop-kind)
                        (:e expr-binary->arg1)
                        ,arg1-thm
                        ,valuep-when-arg1-type-pred
                        test-value-when-sintp
                        sint-from-boolean-when-false
                        booleanp-compound-recognizer
                        sintp-of-sint-from-integer
                        boolean-from-sint-of-0
                        expr-valuep-of-expr-value
                        expr-value->value-of-expr-value
                        value-fix-when-valuep
                        apconvert-expr-value-when-not-value-array
                        ,value-kind-when-arg1-type-pred))))
       (instructions
        `((casesplit ,(atc-contextualize
                       arg1-term
                       gin.context nil nil nil nil nil nil wrld))
          (claim ,(atc-contextualize `(test* ,arg1-term)
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(test*))))
          (drop 1)
          (claim ,(atc-contextualize `(equal ,term ,arg2-term)
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal"
                          :in-theory '(acl2::if*-when-true test*))))
          (prove :hints ,hints-then)
          (claim ,(atc-contextualize `(test* (not ,arg1-term))
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(test*))))
          (drop 1)
          (claim ,(atc-contextualize `(equal ,term nil)
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal"
                          :in-theory '(acl2::if*-when-false test*))))
          (prove :hints ,hints-else)))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-bool-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       type
                                       term
                                       cterm
                                       acl2::*nil*
                                       gin.compst-var
                                       nil
                                       instructions
                                       gin.prec-tags
                                       gin.thm-index
                                       gin.names-to-avoid
                                       state)))
    (make-pexpr-gout
     :expr expr
     :type type
     :term term
     :events (append arg1-events
                     arg2-events
                     (list thm-event))
     :thm-name thm-name
     :thm-index thm-index
     :names-to-avoid names-to-avoid
     :proofs t))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-or ((arg1-term pseudo-termp)
                         (arg2-term pseudo-termp)
                         (arg1-expr exprp)
                         (arg2-expr exprp)
                         (arg1-type typep)
                         (arg2-type typep)
                         (arg1-thm symbolp)
                         (arg2-thm symbolp)
                         (arg1-events pseudo-event-form-listp)
                         (arg2-events pseudo-event-form-listp)
                         (gin pexpr-ginp)
                         state)
  :returns (gout pexpr-goutp)
  :short "Generate a C expressino from an ACL2 term
          that represents a logical disjunction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-gen-expr-and),
     but with a few differences due to the non-complete symmetry
     between ACL2's @(tsee and) and @(tsee or).
     In particular, for the case in which the first argument is true,
     and thus suffices to determine the result without the second argument,
     we need some additional rules to resolve certain subgoals that arise."))
  (b* (((pexpr-gin gin) gin)
       (wrld (w state))
       (term `(if* ,arg1-term ,arg1-term ,arg2-term))
       (expr (make-expr-binary :op (binop-logor)
                               :arg1 arg1-expr
                               :arg2 arg2-expr))
       (type (type-sint))
       ((when (not gin.proofs))
        (make-pexpr-gout
         :expr expr
         :type type
         :term term
         :events (append arg1-events arg2-events)
         :thm-name nil
         :thm-index gin.thm-index
         :names-to-avoid gin.names-to-avoid
         :proofs nil))
       (cterm `(sint-from-boolean ,term))
       (arg1-type-pred (atc-type-to-recognizer arg1-type gin.prec-tags))
       (arg2-type-pred (atc-type-to-recognizer arg2-type gin.prec-tags))
       (valuep-when-arg1-type-pred (pack 'valuep-when- arg1-type-pred))
       (valuep-when-arg2-type-pred (pack 'valuep-when- arg2-type-pred))
       (value-kind-when-arg1-type-pred (pack 'value-kind-when- arg1-type-pred))
       (value-kind-when-arg2-type-pred (pack 'value-kind-when- arg2-type-pred))
       (hints-then
        `(("Goal"
           :in-theory '(exec-expr-pure-when-binary-logor-and-true
                        (:e expr-kind)
                        (:e expr-binary->op)
                        (:e binop-kind)
                        (:e expr-binary->arg1)
                        ,arg1-thm
                        ,valuep-when-arg1-type-pred
                        test-value-when-sintp
                        boolean-from-sint-of-sint-from-boolean
                        sintp-of-sint-from-boolean
                        sintp-of-sint-from-integer
                        boolean-from-sint-of-1
                        if*-of-t-and-t
                        sint-from-boolean-when-true-test*
                        equal-to-t-when-holds-and-boolean
                        booleanp-compound-recognizer
                        test*-of-t
                        expr-valuep-of-expr-value
                        expr-value->value-of-expr-value
                        value-fix-when-valuep
                        apconvert-expr-value-when-not-value-array
                        ,value-kind-when-arg1-type-pred))))
       (hints-else
        `(("Goal"
           :in-theory '(exec-expr-pure-when-binary-logor-and-false
                        (:e expr-kind)
                        (:e expr-binary->op)
                        (:e binop-kind)
                        (:e expr-binary->arg1)
                        ,arg1-thm
                        ,valuep-when-arg1-type-pred
                        (:e expr-binary->arg2)
                        ,arg2-thm
                        ,valuep-when-arg2-type-pred
                        test-value-when-sintp
                        sintp-of-sint-from-boolean
                        boolean-from-sint-of-sint-from-boolean
                        expr-valuep-of-expr-value
                        expr-value->value-of-expr-value
                        value-fix-when-valuep
                        apconvert-expr-value-when-not-value-array
                        ,value-kind-when-arg1-type-pred
                        ,value-kind-when-arg2-type-pred))))
       (instructions
        `((casesplit ,(atc-contextualize
                       arg1-term
                       gin.context nil nil nil nil nil nil wrld))
          (claim ,(atc-contextualize `(test* ,arg1-term)
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(test*))))
          (drop 1)
          (claim ,(atc-contextualize `(equal ,term ,arg1-term)
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal"
                          :in-theory '(acl2::if*-when-true test*))))
          (prove :hints ,hints-then)
          (claim ,(atc-contextualize `(test* (not ,arg1-term))
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal" :in-theory '(test*))))
          (drop 1)
          (claim ,(atc-contextualize `(equal ,term ,arg2-term)
                                     gin.context nil nil nil nil nil nil wrld)
                 :hints (("Goal"
                          :in-theory '(acl2::if*-when-false test*))))
          (prove :hints ,hints-else)))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-bool-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       type
                                       term
                                       cterm
                                       acl2::*nil*
                                       gin.compst-var
                                       nil
                                       instructions
                                       gin.prec-tags
                                       gin.thm-index
                                       gin.names-to-avoid
                                       state)))
    (make-pexpr-gout
     :expr expr
     :type type
     :term term
     :events (append arg1-events
                     arg2-events
                     (list thm-event))
     :thm-name thm-name
     :thm-index thm-index
     :names-to-avoid names-to-avoid
     :proofs t))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-sint-from-bool ((arg-term pseudo-termp)
                                     (arg-expr exprp)
                                     (arg-events pseudo-event-form-listp)
                                     (arg-thm symbolp)
                                     (gin pexpr-ginp)
                                     state)
  :returns (mv erp (gout pexpr-goutp))
  :short "Generate a C expression from an ACL2 term
          that represents a conversion from ACL2 boolean."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression is the same as the argument expression:
     the conversion from ACL2 boolean
     only serves a purpose in the ACL2 representation
     but it has no counterpart in the C code.")
   (xdoc::p
    "To check that the argument term is an @(tsee and) or @(tsee or),
     as described in the user documentation,
     is carried out on transformed terms.
     So we check that the argument term is a call of @(tsee if*).")
   (xdoc::p
    "The proof of the correctness theorem is very simple.
     Since the argument term must be a call of @(tsee and) or @(tsee or),
     the correctness theorem already states that
     @(tsee sint-from-boolean) applied to the argument term
     is equal to executing the expression and has the appropriate C type."))
  (b* (((reterr) (irr-pexpr-gout))
       ((pexpr-gin gin) gin)
       ((unless (and (consp arg-term)
                     (eq (car arg-term) 'if*)))
        (reterr
         (msg "The conversion from boolean to C (signed) int ~
               is applied to a boolean expression term ~x0 ~
               that is not a (transformed) call of AND or OR."
              arg-term)))
       (term `(sint-from-boolean ,arg-term))
       (expr arg-expr)
       (type (type-sint))
       ((when (not gin.proofs))
        (retok (make-pexpr-gout :expr expr
                                :type type
                                :term term
                                :events arg-events
                                :thm-name nil
                                :thm-index gin.thm-index
                                :names-to-avoid gin.names-to-avoid
                                :proofs nil)))
       (hints `(("Goal" :by ,arg-thm)))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       type
                                       term
                                       term
                                       acl2::*nil*
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       gin.thm-index
                                       gin.names-to-avoid
                                       state)))
    (retok (make-pexpr-gout :expr expr
                            :type type
                            :term term
                            :events (append arg-events
                                            (list thm-event))
                            :thm-name thm-name
                            :thm-index thm-index
                            :names-to-avoid names-to-avoid
                            :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-integer-read ((fn symbolp)
                                   (arg-term pseudo-termp)
                                   (arg-expr exprp)
                                   (arg-type typep)
                                   (arg-events pseudo-event-form-listp)
                                   (arg-thm symbolp)
                                   (type typep)
                                   (gin pexpr-ginp)
                                   state)
  :guard (type-nonchar-integerp type)
  :returns (mv erp (gout pexpr-goutp))
  :short "Generate a C expression from an ACL2 term
          that represents an indirection of a pointer to integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression and theorem for the argument
     are generated in the caller, and passed here.")
   (xdoc::p
    "Currently, the argument term must be an ACL2 variable.
     We defensively check that it is the case.
     The generated theorem needs not only the theorem about the argument,
     but also the theorem about the variable in the symbol table.
     The reason is that the theorem about the argument
     just says that the execution of the C variable
     yields the ACL2 @('-ptr') variable,
     but here we need to show that the execution of the indirection expression
     yields the ACL2 variable that contains the integer, not the pointer:
     that assertion is in the theorem about the variable in the symbol table.
     An alternative proof generation approach is to
     extend the theorem about the argument to also say that
     dereferncing the pointer yields the integer variable,
     i.e. the same assertion in the symbol table:
     doing this obviated the need to use, in the theorem generated here,
     the theorem from the symbol table.
     However, that approach makes the theorem about the argument expression
     disuniform with other theorems about expressions;
     in particular, @(tsee atc-gen-expr-pure-correct-thm)
     would have to be generalized.
     Thus, the approach we use here seems better for now,
     since the only slight ``disuniformity'' is in the fact that
     we need to retrieve and use the theorem from the symbol table.
     The current approach critically depends on
     the argument of the indirection operator always being a variable;
     if in the future our ACL2 representation of C is extended
     so that the indirection operator can be applied to more general arguments,
     we may need to choose the alternative approach sketched above,
     which in that case would be more uniform."))
  (b* (((reterr) (irr-pexpr-gout))
       ((pexpr-gin gin) gin)
       ((unless (equal arg-type
                       (type-pointer type)))
        (reterr
         (msg "The indirection operator representation for integer type ~x0 ~
               is applied to an expression term ~x1 returning ~x2, ~
               but a ~x3 operand is expected. ~
               This is indicative of provably dead code, ~
               given that the code is guard-verified."
              type arg-term arg-type (type-pointer type))))
       (expr (make-expr-unary :op (unop-indir)
                              :arg arg-expr))
       (term `(,fn ,arg-term))
       ((when (not gin.proofs))
        (retok
         (make-pexpr-gout :expr expr
                          :type type
                          :term term
                          :events arg-events
                          :thm-name nil
                          :thm-index gin.thm-index
                          :names-to-avoid gin.names-to-avoid
                          :proofs nil)))
       ((unless (symbolp arg-term))
        (reterr (raise "Interal error: indirection applied to non-variable ~x0."
                       arg-term)))
       (info (atc-get-var arg-term gin.inscope))
       ((unless info)
        (reterr (raise "Internal error: variable ~x0 not found in scope."
                       arg-term)))
       (var-thm (atc-var-info->thm info))
       (hints
        (b* ((type-pred (atc-type-to-recognizer type gin.prec-tags))
             (exec-indir-when-type-pred (pack 'exec-indir-when- type-pred))
             (type-read (pack (type-kind type) '-read))
             (type-read-when-type-pred (pack type-read '-when- type-pred)))
          `(("Goal" :in-theory '(exec-expr-pure-when-unary
                                 (:e expr-kind)
                                 (:e expr-unary->arg)
                                 (:e expr-unary->op)
                                 ,arg-thm
                                 expr-valuep-of-expr-value
                                 ,exec-indir-when-type-pred
                                 (:e unop-kind)
                                 ,var-thm
                                 ,type-read-when-type-pred)))))
       (objdes (add-suffix-to-fn arg-term "-OBJDES"))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       type
                                       term
                                       term
                                       objdes
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       gin.thm-index
                                       gin.names-to-avoid
                                       state)))
    (retok
     (make-pexpr-gout :expr expr
                      :type type
                      :term term
                      :events (append arg-events
                                      (list thm-event))
                      :thm-name thm-name
                      :thm-index thm-index
                      :names-to-avoid names-to-avoid
                      :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-array-read ((fn symbolp)
                                 (arr-term pseudo-termp)
                                 (arr-expr exprp)
                                 (arr-type typep)
                                 (arr-events pseudo-event-form-listp)
                                 (arr-thm symbolp)
                                 (sub-term pseudo-termp)
                                 (sub-expr exprp)
                                 (sub-type typep)
                                 (sub-events pseudo-event-form-listp)
                                 (sub-thm symbolp)
                                 (elem-type typep)
                                 (gin pexpr-ginp)
                                 state)
  :guard (type-nonchar-integerp elem-type)
  :returns (mv erp (gout pexpr-goutp))
  :short "Generate a C expression from an ACL2 term
          that represents an array read."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a theorem to show that the @('okp') predicate is satisfied,
     and a theorem about the expression itself.")
   (xdoc::p
    "For now we only generate proofs for arrays that are not external objects.
     Support for arrays that are external objects is forthcoming."))
  (b* (((reterr) (irr-pexpr-gout))
       (wrld (w state))
       ((pexpr-gin gin) gin)
       ((unless (and (type-case arr-type :array)
                     (equal (type-array->of arr-type) elem-type)
                     (type-integerp sub-type)))
        (reterr
         (msg "The reading of a ~x0 array is applied to ~
               an expression term ~x1 returning ~x2 ~
               and to an expression term ~x3 returning ~x4, ~
               but a ~x0 array and an integer operand are expected. ~
               This is indicative of provably dead code, ~
               given that the code is guard-verified."
              elem-type arr-term arr-type sub-term sub-type)))
       (expr (make-expr-arrsub :arr arr-expr :sub sub-expr))
       ((when (eq fn 'quote))
        (reterr (raise "Internal error: function symbol is QUOTE.")))
       (term `(,fn ,arr-term ,sub-term))
       ((when (not gin.proofs))
        (retok (make-pexpr-gout
                :expr expr
                :type elem-type
                :term term
                :events (append arr-events sub-events)
                :thm-name nil
                :thm-index gin.thm-index
                :names-to-avoid gin.names-to-avoid
                :proofs nil)))
       (elem-fixtype (integer-type-to-fixtype elem-type))
       (fn-okp (pack elem-fixtype '-array-index-okp))
       ((mv okp-lemma-event
            okp-lemma-name
            thm-index
            names-to-avoid)
        (b* ((okp-lemma-name (pack gin.fn '-expr- gin.thm-index '-okp-lemma))
             ((mv okp-lemma-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix okp-lemma-name
                                                 nil
                                                 gin.names-to-avoid
                                                 wrld))
             (arr-uterm (untranslate$ arr-term nil state))
             (sub-uterm (untranslate$ sub-term nil state))
             (okp-lemma-formula `(,fn-okp ,arr-uterm ,sub-uterm))
             (okp-lemma-formula
              (atc-contextualize okp-lemma-formula
                                 gin.context
                                 gin.fn
                                 gin.fn-guard
                                 nil
                                 nil
                                 nil
                                 nil
                                 wrld))
             (okp-lemma-hints
              `(("Goal"
                 :in-theory '(,gin.fn-guard if* test* declar)
                 :use (:guard-theorem ,gin.fn))))
             ((mv okp-lemma-event &)
              (evmac-generate-defthm okp-lemma-name
                                     :formula okp-lemma-formula
                                     :hints okp-lemma-hints
                                     :enable nil)))
          (mv okp-lemma-event
              okp-lemma-name
              (1+ gin.thm-index)
              names-to-avoid)))
       (exec-arrsub-when-elemtype-arrayp
        (pack 'exec-arrsub-when- elem-fixtype '-arrayp))
       ((unless (symbolp arr-term))
        (reterr (raise "Interal error: non-variable array ~x0." arr-term)))
       (info (atc-get-var arr-term gin.inscope))
       ((unless info)
        (reterr (raise "Internal error: variable ~x0 not found in scope."
                       arr-term)))
       ((when (atc-var-info->externalp info))
        (retok (make-pexpr-gout
                :expr expr
                :type elem-type
                :term term
                :events (append arr-events sub-events)
                :thm-name nil
                :thm-index gin.thm-index
                :names-to-avoid gin.names-to-avoid
                :proofs nil)))
       (var-thm (atc-var-info->thm info))
       ((unless (type-nonchar-integerp sub-type))
        (reterr (raise "Internal error: non-integer index ~x0." sub-term)))
       (sub-fixtype (integer-type-to-fixtype sub-type))
       (sub-type-pred (pack sub-fixtype 'p))
       (cintegerp-when-type-pred (pack 'cintegerp-when- sub-type-pred))
       (elem-type-pred-of-fn (pack elem-fixtype 'p-of- fn))
       (hints
        `(("Goal" :in-theory '(exec-expr-pure-when-arrsub
                               (:e expr-kind)
                               (:e expr-arrsub->arr)
                               (:e expr-arrsub->sub)
                               ,arr-thm
                               ,sub-thm
                               expr-valuep-of-expr-value
                               ,exec-arrsub-when-elemtype-arrayp
                               apconvert-expr-value-when-not-value-array
                               expr-value->value-of-expr-value
                               value-fix-when-valuep
                               ,var-thm
                               ,cintegerp-when-type-pred
                               ,okp-lemma-name
                               ,elem-type-pred-of-fn))))
       (objdes `(objdesign-element ,(add-suffix-to-fn arr-term "-OBJDES")
                                   (integer-from-cinteger ,sub-term)))
       ((mv thm-event thm-name thm-index names-to-avoid)
        (atc-gen-expr-pure-correct-thm gin.fn
                                       gin.fn-guard
                                       gin.context
                                       expr
                                       elem-type
                                       term
                                       term
                                       objdes
                                       gin.compst-var
                                       hints
                                       nil
                                       gin.prec-tags
                                       thm-index
                                       names-to-avoid
                                       state)))
    (retok
     (make-pexpr-gout :expr expr
                      :type elem-type
                      :term term
                      :events (append arr-events
                                      sub-events
                                      (list okp-lemma-event
                                            thm-event))
                      :thm-name thm-name
                      :thm-index thm-index
                      :names-to-avoid names-to-avoid
                      :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-expr-pure/bool
  :short "Mutually recursive ACL2 functions to
          generate pure C expressions from ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for pure expression terms
     and for expression terms returning booleans (which are always pure).")
   (xdoc::p
    "We also generate correctness theorems for the generated expressions.
     The theorems relate (the semantics of) the expressions
     to the ACL2 terms from which they are generated.
     Fow now we only generate theorems for some expressions,
     but eventually we plan to extend this to all the expressions.")
   (xdoc::p
    "As we generate the code, we ensure that the ACL2 terms
     are well-typed according to the C types.
     This is subsumed by guard verification for all the code,
     except for any code that is dead (i.e. unreachable) under the guard:
     the dead code passes guard verification
     (under a hypothesis of @('nil'), i.e. false),
     but the resulting C code may not compile.
     The additional type checking we do here should ensure that
     all the code satisfies the C static semantics."))

  (define atc-gen-expr-pure ((term pseudo-termp)
                             (gin pexpr-ginp)
                             state)
    :returns (mv erp (gout pexpr-goutp))
    :parents (atc-event-and-code-generation atc-gen-expr-pure/bool)
    :short "Generate a C expression from an ACL2 term
            that must be a pure expression term."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time,
       we check that the term is a pure expression term,
       as described in the user documentation.
       Based on its form, we dispatch to different code,
       after recursively processing sub-expressions.")
     (xdoc::p
      "If the term fits the pattern of a indirection on a pointed integer,
       we translate it to an indirection expression
       on the recursively generated expression for the argument.")
     (xdoc::p
      "If the term fits the pattern of an array read,
       we translate it to an array subscripting expression
       on the recursively generated expressions.
       The type is the array's element type.")
     (xdoc::p
      "If the term fits the pattern of a structure scalar read,
       we translate it to a structure member or pointer member expression
       on the recursively generated expression.
       The type is the member's type.")
     (xdoc::p
      "If the term fits the pattern of a structure array element read,
       we translate it to an array subscripting expression
       on the recursively generated index expression
       and on a structure member of pointer member expression
       on the recursively generated structure expression.
       The type is the member element's type.")
     (xdoc::p
      "If the term is a call of @(tsee sint-from-boolean),
       we call the mutually recursive ACL2 function
       that translates the argument
       (which must be an expression term returning a boolean)
       to an expression, which we return.
       The type of this expression is always @('int').")
     (xdoc::p
      "If the term is a @(tsee condexpr) call on an @(tsee if) call,
       we call the mutually recursive ACL2 function on the test,
       we call this ACL2 function on the branches,
       and we construct a conditional expression.
       We ensure that the two branches have the same type.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not a pure expression term.
       We could extend this code to provide
       more information to the user at some point."))
    (b* (((reterr) (irr-pexpr-gout))
         ((pexpr-gin gin) gin)
         ((when (pseudo-term-case term :var))
          (retok (atc-gen-expr-var (pseudo-term-var->name term) gin state)))
         ((erp okp type-base-const type const) (atc-check-iconst term))
         ((when okp) (retok (atc-gen-expr-const term const type type-base-const
                                                gin state)))
         ((erp okp fn arg-term in-type out-type op) (atc-check-unop term))
         ((when okp)
          (b* (((erp (pexpr-gout arg)) (atc-gen-expr-pure arg-term gin state))
               (gin (change-pexpr-gin gin
                                      :thm-index arg.thm-index
                                      :names-to-avoid arg.names-to-avoid
                                      :proofs arg.proofs)))
            (atc-gen-expr-unary fn arg.term
                                arg.expr arg.type
                                arg.events arg.thm-name
                                in-type out-type op
                                gin state)))
         ((erp okp fn arg1-term arg2-term in-type1 in-type2 out-type op)
          (atc-check-binop term))
         ((when okp)
          (b* (((erp (pexpr-gout arg1))
                (atc-gen-expr-pure arg1-term gin state))
               (gin (change-pexpr-gin gin
                                      :thm-index arg1.thm-index
                                      :names-to-avoid arg1.names-to-avoid
                                      :proofs arg1.proofs))
               ((erp (pexpr-gout arg2))
                (atc-gen-expr-pure arg2-term gin state))
               (gin (change-pexpr-gin gin
                                      :thm-index arg2.thm-index
                                      :names-to-avoid arg2.names-to-avoid
                                      :proofs arg2.proofs)))
            (atc-gen-expr-binary fn
                                 arg1.term arg2.term
                                 arg1.expr arg2.expr
                                 arg1.type arg2.type
                                 arg1.events arg2.events
                                 arg1.thm-name arg2.thm-name
                                 in-type1 in-type2 out-type
                                 op
                                 gin
                                 state)))
         ((erp okp fn arg-term in-type out-type tyname) (atc-check-conv term))
         ((when okp)
          (b* (((erp (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin state))
               (gin (change-pexpr-gin gin
                                      :thm-index arg.thm-index
                                      :names-to-avoid arg.names-to-avoid
                                      :proofs arg.proofs)))
            (atc-gen-expr-conv fn arg.term
                               arg.expr arg.type
                               arg.events arg.thm-name
                               in-type out-type tyname
                               gin state)))
         ((erp okp fn arg-term type) (atc-check-integer-read term))
         ((when okp)
          (b* (((erp (pexpr-gout arg)) (atc-gen-expr-pure arg-term gin state))
               (gin (change-pexpr-gin gin
                                      :thm-index arg.thm-index
                                      :names-to-avoid arg.names-to-avoid
                                      :proofs arg.proofs)))
            (atc-gen-expr-integer-read fn
                                       arg.term
                                       arg.expr
                                       arg.type
                                       arg.events
                                       arg.thm-name
                                       type
                                       gin
                                       state)))
         ((erp okp fn arr-term sub-term elem-type)
          (atc-check-array-read term))
         ((when okp)
          (b* (((erp (pexpr-gout arr))
                (atc-gen-expr-pure arr-term gin state))
               ((erp (pexpr-gout sub))
                (atc-gen-expr-pure sub-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index arr.thm-index
                                    :names-to-avoid arr.names-to-avoid
                                    :proofs arr.proofs)
                                   state))
               (gin (change-pexpr-gin gin
                                      :thm-index sub.thm-index
                                      :names-to-avoid sub.names-to-avoid
                                      :proofs sub.proofs)))
            (atc-gen-expr-array-read fn
                                     arr.term
                                     arr.expr
                                     arr.type
                                     arr.events
                                     arr.thm-name
                                     sub.term
                                     sub.expr
                                     sub.type
                                     sub.events
                                     sub.thm-name
                                     elem-type
                                     gin
                                     state)))
         ((erp okp arg-term tag member mem-type)
          (atc-check-struct-read-scalar term gin.prec-tags))
         ((when okp)
          (b* (((erp (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin state)))
            (cond ((equal arg.type (type-struct tag))
                   (retok (make-pexpr-gout
                           :expr (make-expr-member :target arg.expr
                                                   :name member)
                           :type mem-type
                           :term term
                           :events arg.events
                           :thm-name nil
                           :thm-index arg.thm-index
                           :names-to-avoid arg.names-to-avoid
                           :proofs nil)))
                  ((equal arg.type (type-pointer (type-struct tag)))
                   (retok (make-pexpr-gout
                           :expr (make-expr-memberp :target arg.expr
                                                    :name member)
                           :type mem-type
                           :term term
                           :events arg.events
                           :thm-name nil
                           :thm-index arg.thm-index
                           :names-to-avoid arg.names-to-avoid
                           :proofs nil)))
                  (t (reterr
                      (msg "The reading of a ~x0 structure with member ~x1 ~
                            is applied to ~
                            an expression term ~x2 returning ~x3, ~
                            but a an operand of type ~x4 or ~x5 ~
                            is expected. ~
                            This is indicative of provably dead code, ~
                            given that the code is guard-verified."
                           tag
                           member
                           arg-term
                           arg.type
                           (type-struct tag)
                           (type-pointer (type-struct tag))))))))
         ((erp okp index-term struct-term tag member elem-type)
          (atc-check-struct-read-array term gin.prec-tags))
         ((when okp)
          (b* (((erp (pexpr-gout index))
                (atc-gen-expr-pure index-term gin state))
               ((unless (type-integerp index.type))
                (reterr
                 (msg "The reading of ~x0 structure with member ~x1 ~
                       is applied to ~
                       an index expression term ~x2 returning ~x3, ~
                       but a C integer operand is expected. ~
                       This is indicative of provably dead code, ~
                       given that the code is guard-verified."
                      (type-struct tag)
                      member
                      index-term
                      index.type)))
               ((erp (pexpr-gout struct))
                (atc-gen-expr-pure struct-term
                                   (change-pexpr-gin
                                    gin
                                    :thm-index index.thm-index
                                    :names-to-avoid index.names-to-avoid)
                                   state)))
            (cond ((equal struct.type (type-struct tag))
                   (retok (make-pexpr-gout
                           :expr (make-expr-arrsub
                                  :arr (make-expr-member
                                        :target struct.expr
                                        :name member)
                                  :sub index.expr)
                           :type elem-type
                           :term term
                           :events (append index.events struct.events)
                           :thm-name nil
                           :thm-index struct.thm-index
                           :names-to-avoid struct.names-to-avoid
                           :proofs nil)))
                  ((equal struct.type (type-pointer (type-struct tag)))
                   (retok (make-pexpr-gout
                           :expr (make-expr-arrsub
                                  :arr (make-expr-memberp
                                        :target struct.expr
                                        :name member)
                                  :sub index.expr)
                           :type elem-type
                           :term term
                           :events (append index.events struct.events)
                           :thm-name nil
                           :thm-index struct.thm-index
                           :names-to-avoid struct.names-to-avoid
                           :proofs nil)))
                  (t (reterr
                      (msg "The reading of ~x0 structure with member ~x1 ~
                            is applied to ~
                            an expression term ~x2 returning ~x3, ~
                            but an operand of type ~x4 or ~x5 ~
                            is expected. ~
                            This is indicative of provably dead code, ~
                            given that the code is guard-verified."
                           tag
                           member
                           struct-term
                           struct.type
                           (type-struct tag)
                           (type-pointer (type-struct tag))))))))
         ((erp okp arg-term) (atc-check-sint-from-boolean term))
         ((when okp)
          (b* (((erp (pexpr-gout arg)) (atc-gen-expr-bool arg-term gin state)))
            (atc-gen-expr-sint-from-bool arg.term
                                         arg.expr
                                         arg.events
                                         arg.thm-name
                                         (change-pexpr-gin
                                          gin
                                          :thm-index arg.thm-index
                                          :names-to-avoid arg.names-to-avoid
                                          :proofs arg.proofs)
                                         state)))
         ((erp okp test-term then-term else-term) (atc-check-condexpr term))
         ((when okp)
          (b* (((erp (pexpr-gout test)) (atc-gen-expr-bool test-term gin state))
               ((erp (pexpr-gout then))
                (b* ((then-cond (untranslate$ test.term t state))
                     (then-premise (atc-premise-test then-cond))
                     (premises (atc-context->premises gin.context))
                     (then-premises (append premises (list then-premise)))
                     (then-context
                      (change-atc-context gin.context :premises then-premises)))
                  (atc-gen-expr-pure then-term
                                     (change-pexpr-gin
                                      gin
                                      :context then-context
                                      :thm-index test.thm-index
                                      :names-to-avoid test.names-to-avoid
                                      :proofs test.proofs)
                                     state)))
               ((erp (pexpr-gout else))
                (b* ((not-test-term `(not ,test.term))
                     (else-cond (untranslate$ not-test-term nil state))
                     (else-premise (atc-premise-test else-cond))
                     (premises (atc-context->premises gin.context))
                     (else-premises (append premises (list else-premise)))
                     (else-context
                      (change-atc-context gin.context :premises else-premises)))
                  (atc-gen-expr-pure else-term
                                     (change-pexpr-gin
                                      gin
                                      :context else-context
                                      :thm-index then.thm-index
                                      :names-to-avoid then.names-to-avoid
                                      :proofs test.proofs)
                                     state))))
            (atc-gen-expr-cond term test.term then.term else.term
                               test.expr then.expr else.expr
                               test.type then.type else.type
                               test.thm-name then.thm-name else.thm-name
                               test.events then.events else.events
                               (change-pexpr-gin
                                gin
                                :thm-index else.thm-index
                                :names-to-avoid else.names-to-avoid
                                :proofs (and then.proofs else.proofs))
                               state))))
      (reterr
       (msg "When generating C code for the function ~x0, ~
             at a point where ~
             a pure expression term returning a C type is expected, ~
             the term ~x1 is encountered instead, ~
             which is not a C expression term returning a C type; ~
             see the ATC user documentation."
            gin.fn term)))
    :measure (pseudo-term-count term))

  (define atc-gen-expr-bool ((term pseudo-termp)
                             (gin pexpr-ginp)
                             state)
    :returns (mv erp (gout pexpr-goutp))
    :parents (atc-event-and-code-generation atc-gen-expr-pure/bool)
    :short "Generate a C expression from an ACL2 term
            that must be an expression term returning a boolean."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time, we check that the term is
       an expression term returning a boolean,
       as described in the user documentation.
       Based on its form, we dispatch to different code,
       after recursively processing sub-expressions.")
     (xdoc::p
      "If the term is a call of @(tsee and) or @(tsee or),
       we recursively translate the arguments,
       which must be an expression term returning a boolean,
       and we construct a logical expression
       with the corresponding C operators.")
     (xdoc::p
      "If the term is a call of @('boolean-from-<type>'),
       we call the mutually recursive function
       that translates the argument,
       which must be an expression term returning a C value,
       to an expression, which we return.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not an expression term returning a C value.
       We could extend this code to provide
       more information to the user at some point.")
     (xdoc::p
      "As in @(tsee atc-gen-expr-pure),
       we perform C type checks on the ACL2 terms.
       See  @(tsee atc-gen-expr-pure) for an explanation."))
    (b* (((reterr) (irr-pexpr-gout))
         ((pexpr-gin gin) gin)
         ((mv okp arg1-term arg2-term) (fty-check-and-call term))
         ((when okp)
          (b* (((erp (pexpr-gout arg1))
                (atc-gen-expr-bool arg1-term gin state))
               (cond (untranslate$ arg1.term t state))
               (premise (atc-premise-test cond))
               (premises (atc-context->premises gin.context))
               (premises (append premises (list premise)))
               (context (change-atc-context gin.context :premises premises))
               ((erp (pexpr-gout arg2))
                (atc-gen-expr-bool arg2-term
                                   (change-pexpr-gin
                                    gin
                                    :context context
                                    :thm-index arg1.thm-index
                                    :names-to-avoid arg1.names-to-avoid
                                    :proofs arg1.proofs)
                                   state)))
            (retok (atc-gen-expr-and arg1.term
                                     arg2.term
                                     arg1.expr
                                     arg2.expr
                                     arg1.type
                                     arg2.type
                                     arg1.thm-name
                                     arg2.thm-name
                                     arg1.events
                                     arg2.events
                                     (change-pexpr-gin
                                      gin
                                      :thm-index arg2.thm-index
                                      :names-to-avoid arg2.names-to-avoid
                                      :proofs arg2.proofs)
                                     state))))
         ((mv okp arg1-term arg2-term) (fty-check-or-call term))
         ((when okp)
          (b* (((erp (pexpr-gout arg1))
                (atc-gen-expr-bool arg1-term gin state))
               (cond (untranslate$ `(not ,arg1.term) t state))
               (premise (atc-premise-test cond))
               (premises (atc-context->premises gin.context))
               (premises (append premises (list premise)))
               (context (change-atc-context gin.context :premises premises))
               ((erp (pexpr-gout arg2))
                (atc-gen-expr-bool arg2-term
                                   (change-pexpr-gin
                                    gin
                                    :context context
                                    :thm-index arg1.thm-index
                                    :names-to-avoid arg1.names-to-avoid
                                    :proofs arg1.proofs)
                                   state)))
            (retok (atc-gen-expr-or arg1.term
                                    arg2.term
                                    arg1.expr
                                    arg2.expr
                                    arg1.type
                                    arg2.type
                                    arg1.thm-name
                                    arg2.thm-name
                                    arg1.events
                                    arg2.events
                                    (change-pexpr-gin
                                     gin
                                     :thm-index arg2.thm-index
                                     :names-to-avoid arg2.names-to-avoid
                                     :proofs arg2.proofs)
                                    state))))
         ((erp okp fn arg-term in-type) (atc-check-boolean-from-type term))
         ((when okp)
          (b* (((erp (pexpr-gout arg))
                (atc-gen-expr-pure arg-term gin state))
               (gin (change-pexpr-gin gin
                                      :thm-index arg.thm-index
                                      :names-to-avoid arg.names-to-avoid
                                      :proofs arg.proofs)))
            (atc-gen-expr-bool-from-type fn
                                         arg.term
                                         arg.expr
                                         arg.type
                                         arg.events
                                         arg.thm-name
                                         in-type
                                         gin
                                         state))))
      (reterr
       (msg "When generating C code for the function ~x0, ~
             at a point where ~
             an expression term returning boolean is expected, ~
             the term ~x1 is encountered instead, ~
             which is not a C epxression term returning boolean; ~
             see the ATC user documentation."
            gin.fn term)))
    :measure (pseudo-term-count term))

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-expr-pure
    :hints (("Goal" :in-theory (enable pseudo-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexprs-gin
  :short "Inputs for C pure expression list generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not include the terms, which are passed as a separate input."))
  ((context atc-contextp)
   (inscope atc-symbol-varinfo-alist-list)
   (prec-tags atc-string-taginfo-alist)
   (fn symbol)
   (fn-guard symbol)
   (compst-var symbol)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool)
   (deprecated symbol-list))
  :pred pexprs-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod pexprs-gout
  :short "Outputs for C pure expression list generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The generated expressions are @('exprs'),
     and their types are @('types'),
     in the same order."))
  ((exprs expr-list)
   (types type-list)
   (terms pseudo-term-listp)
   (events pseudo-event-form-list)
   (thm-name symbol)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred pexprs-goutp)

;;;;;;;;;;

(defirrelevant irr-pexprs-gout
  :short "An irrelevant output for C pure expression list generation."
  :type pexprs-goutp
  :body (make-pexprs-gout :exprs nil
                          :types nil
                          :terms nil
                          :events nil
                          :thm-name nil
                          :thm-index 1
                          :names-to-avoid nil
                          :proofs nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-pure-list ((terms pseudo-term-listp)
                                (gin pexprs-ginp)
                                state)
  :returns (mv erp (gout pexprs-goutp))
  :short "Generate a list of C expressions from a list of ACL2 terms
          that must be pure expression terms returning C values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee atc-gen-expr-pure) to lists.
     However, we do not return the C types of the expressions."))
  (b* (((reterr) (irr-pexprs-gout))
       ((pexprs-gin gin) gin)
       ((when (endp terms))
        (retok (make-pexprs-gout :exprs nil
                                 :types nil
                                 :terms nil
                                 :events nil
                                 :thm-name nil
                                 :thm-index gin.thm-index
                                 :names-to-avoid gin.names-to-avoid
                                 :proofs gin.proofs)))
       ((erp (pexpr-gout first))
        (atc-gen-expr-pure (car terms)
                           (make-pexpr-gin
                            :context gin.context
                            :inscope gin.inscope
                            :prec-tags gin.prec-tags
                            :fn gin.fn
                            :fn-guard gin.fn-guard
                            :compst-var gin.compst-var
                            :thm-index gin.thm-index
                            :names-to-avoid gin.names-to-avoid
                            :proofs gin.proofs
                            :deprecated gin.deprecated)
                           state))
       ((erp (pexprs-gout rest))
        (atc-gen-expr-pure-list (cdr terms)
                                (change-pexprs-gin
                                 gin
                                 :thm-index first.thm-index
                                 :names-to-avoid first.names-to-avoid
                                 :proofs first.proofs)
                                state)))
    (retok (make-pexprs-gout
            :exprs (cons first.expr rest.exprs)
            :types (cons first.type rest.types)
            :terms (cons first.term rest.terms)
            :events (append first.events rest.events)
            :thm-name nil
            :thm-index rest.thm-index
            :names-to-avoid rest.names-to-avoid
            :proofs rest.proofs)))
  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-expr-pure-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-gin
  :short "Inputs for C expression generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not include the term, which is passed as a separate input."))
  ((context atc-contextp)
   (var-term-alist symbol-pseudoterm-alist)
   (inscope atc-symbol-varinfo-alist-list)
   (fn symbol)
   (fn-guard symbol)
   (compst-var symbol)
   (fenv-var symbol)
   (limit-var symbol)
   (prec-fns atc-symbol-fninfo-alist)
   (prec-tags atc-string-taginfo-alist)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool)
   (deprecated symbol-list))
  :pred expr-ginp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-gout
  :short "Outputs for C expression generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The generated expression is @('expr'),
     and its type is @('type').
     The possibly updated computation state is returned as an untranslated term,
     in @('compst-term').")
   (xdoc::p
    "The @('limit') component is the lower bound of the limit,
     i.e. the minimum limit for which
     the execution of the expression terminates."))
  ((expr expr)
   (type type)
   (term pseudo-term)
   (compst-term pseudo-term)
   (affect symbol-list)
   (limit pseudo-term)
   (events pseudo-event-form-list)
   (thm-name symbol)
   (thm-index pos)
   (names-to-avoid symbol-list)
   (proofs bool))
  :pred expr-goutp)

;;;;;;;;;;

(defirrelevant irr-expr-gout
  :short "An irrelevant output for C expression generation."
  :type expr-goutp
  :body (make-expr-gout :expr (irr-expr)
                        :type (irr-type)
                        :term nil
                        :compst-term nil
                        :affect nil
                        :limit nil
                        :events nil
                        :thm-name nil
                        :thm-index 1
                        :names-to-avoid nil
                        :proofs nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-noncall ((term pseudo-termp)
                              (gin expr-ginp)
                              state)
  :returns (mv erp (gout expr-goutp))
  :short "Generate a C expression from an ACL2 term
          that is not a function call."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called by @(tsee atc-gen-expr),
     when given an expression term that is not a function call,
     in which case it must be a pure expression term.
     This is not the same as just @(tsee atc-gen-expr-pure),
     because that function generates a theorem
     involving @(tsee exec-expr-pure),
     while this function generates a theorem
     involving @(tsee exec-expr-call-or-pure).")
   (xdoc::p
    "The limit bound is set to 1,
     which suffices, in @(tsee exec-expr-call-or-pure),
     to go from there to @(tsee exec-expr-pure),
     which does not use any limit."))
  (b* (((reterr) (irr-expr-gout))
       ((expr-gin gin) gin)
       (wrld (w state))
       ((erp (pexpr-gout pure))
        (atc-gen-expr-pure term
                           (make-pexpr-gin :context gin.context
                                           :inscope gin.inscope
                                           :prec-tags gin.prec-tags
                                           :fn gin.fn
                                           :fn-guard gin.fn-guard
                                           :compst-var gin.compst-var
                                           :thm-index gin.thm-index
                                           :names-to-avoid gin.names-to-avoid
                                           :proofs gin.proofs
                                           :deprecated gin.deprecated)
                           state))
       (bound '(quote 1))
       ((when (not pure.proofs))
        (retok (make-expr-gout :expr pure.expr
                               :type pure.type
                               :term pure.term
                               :compst-term gin.compst-var
                               :affect nil
                               :limit bound
                               :events pure.events
                               :thm-name nil
                               :thm-index pure.thm-index
                               :names-to-avoid pure.names-to-avoid
                               :proofs nil)))
       (thm-name (pack gin.fn '-correct- pure.thm-index))
       ((mv thm-name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                      thm-name nil pure.names-to-avoid wrld))
       (type-pred (atc-type-to-recognizer pure.type gin.prec-tags))
       (valuep-when-type-pred
        (atc-type-to-valuep-thm pure.type gin.prec-tags))
       (value-kind-when-type-pred
        (atc-type-to-value-kind-thm pure.type gin.prec-tags))
       (uterm* (untranslate$ pure.term nil state))
       (formula1 `(equal (exec-expr-call-or-pure ',pure.expr
                                                 ,gin.compst-var
                                                 ,gin.fenv-var
                                                 ,gin.limit-var)
                         (mv ,uterm* ,gin.compst-var)))
       (formula2 `(,type-pred ,uterm*))
       (formula1 (atc-contextualize formula1
                                    gin.context
                                    gin.fn
                                    gin.fn-guard
                                    gin.compst-var
                                    gin.limit-var
                                    ''1
                                    t
                                    wrld))
       (formula2 (atc-contextualize formula2
                                    gin.context
                                    gin.fn
                                    gin.fn-guard
                                    nil
                                    nil
                                    nil
                                    nil
                                    wrld))
       (formula `(and ,formula1 ,formula2))
       (hints `(("Goal" :in-theory '(compustatep-of-add-frame
                                     compustatep-of-add-var
                                     compustatep-of-enter-scope
                                     exec-expr-call-or-pure-when-pure
                                     (:e expr-kind)
                                     not-zp-of-limit-variable
                                     ,pure.thm-name
                                     expr-valuep-of-expr-value
                                     expr-value->value-of-expr-value
                                     value-fix-when-valuep
                                     ,valuep-when-type-pred
                                     apconvert-expr-value-when-not-value-array
                                     ,value-kind-when-type-pred))))
       ((mv event &) (evmac-generate-defthm thm-name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (retok (make-expr-gout :expr pure.expr
                           :type pure.type
                           :term pure.term
                           :compst-term gin.compst-var
                           :limit bound
                           :events (append pure.events (list event))
                           :thm-name thm-name
                           :thm-index (1+ pure.thm-index)
                           :names-to-avoid names-to-avoid
                           :proofs t)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr ((term pseudo-termp)
                      (gin expr-ginp)
                      state)
  :returns (mv erp (gout expr-goutp))
  :short "Generate a C expression from an ACL2 term
          that must be an expression term."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the same time,
     we check that the term is an expression term,
     as described in the user documentation.")
   (xdoc::p
    "We also return the C type of the expression,
     the affected variables,
     and a limit that suffices for @(tsee exec-expr-call-or-pure)
     to execute the expression completely.")
   (xdoc::p
    "If the term is a call of a function that precedes @('fn')
     in the list of target functions among @('t1'), ..., @('tp'),
     we translate it to a C function call on the translated arguments.
     The type of the expression is the result type of the function,
     which is looked up in the function alist passed as input:
     we ensure that this type is not @('void').
     A sufficient limit for @(tsee exec-fun) to execute the called function
     is retrieved from the called function's information;
     we add 2 to it, to take into account the decrementing of the limit
     to go from @(tsee exec-expr-call-or-pure) to @(tsee exec-expr-call)
     and from there to @(tsee exec-fun).")
   (xdoc::p
    "Otherwise, we attempt to translate the term as a pure expression term.
     The type is the one returned by that translation.
     As limit we return 1, which suffices for @(tsee exec-expr-call-or-pure)
     to not stop right away due to the limit being 0."))
  (b* (((reterr) (irr-expr-gout))
       ((expr-gin gin) gin)
       ((mv okp called-fn arg-terms in-types out-type affect limit)
        (atc-check-cfun-call term gin.var-term-alist gin.prec-fns (w state)))
       ((when okp)
        (b* (((when (type-case out-type :void))
              (reterr
               (msg "A call ~x0 of the function ~x1, which returns void, ~
                     is being used where ~
                     an expression term returning a a non-void C type ~
                     is expected."
                    term called-fn)))
             ((unless (atc-check-cfun-call-args (formals+ called-fn (w state))
                                                in-types
                                                arg-terms))
              (reterr
               (msg "The call ~x0 does not satisfy the restrictions ~
                     on array arguments being identical to the formals."
                    term)))
             ((erp (pexprs-gout args))
              (atc-gen-expr-pure-list arg-terms
                                      (make-pexprs-gin
                                       :context gin.context
                                       :inscope gin.inscope
                                       :prec-tags gin.prec-tags
                                       :fn gin.fn
                                       :fn-guard gin.fn-guard
                                       :compst-var gin.compst-var
                                       :thm-index gin.thm-index
                                       :names-to-avoid gin.names-to-avoid
                                       :proofs gin.proofs
                                       :deprecated gin.deprecated)
                                      state))
             ((unless (equal args.types in-types))
              (reterr
               (msg "The function ~x0 with input types ~x1 ~
                     is applied to expression terms ~x2 returning ~x3. ~
                     This is indicative of provably dead code, ~
                     given that the code is guard-verified."
                    called-fn in-types arg-terms args.types))))
          (retok
           (make-expr-gout
            :expr (make-expr-call :fun (make-ident
                                        :name (symbol-name called-fn))
                                  :args args.exprs)
            :type out-type
            :term term
            :compst-term nil
            :affect affect
            :limit `(binary-+ '2 ,limit)
            :events args.events
            :thm-name nil
            :thm-index args.thm-index
            :names-to-avoid args.names-to-avoid
            :proofs nil)))))
    (atc-gen-expr-noncall term gin state))
  :prepwork ((local (in-theory (enable pseudo-termp)))))
