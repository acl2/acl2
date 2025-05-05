; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/define" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "std/lists/index-of" :dir :system)

(include-book "../syntax/abstract-syntax-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/remove-assoc-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ deftrans
  :parents (transformation-tools)
  :short "A tool to generate C-to-C transformations."
  :long
  (xdoc::topstring
   (xdoc::p
     "The C @(see c$::abstract-syntax) has many cases as well as large,
      mutually recursive cliques. Transformations will therefore have
      significant sections of boilerplate in which functions do nothing but
      call the appropriate sub-transformation on each child of the AST node. In
      addition, most all such transformations will have the same termination
      argument. @('deftrans') eases the burden of writing such transformations
      by generating all the \"trivial\" cases of the transformation, only
      requiring the user to provide function definitions for the interesting
      cases.")
   (xdoc::section
     "General form:"
     (xdoc::codeblock
       "(deftrans name"
       "  :extra-args extra-args           ;; Default: nil"
       "  :with-output-off with-output-off ;; Default: (:other-than summary error)"
       "  ..."
       "  other-keywords"
       "  ..."
       ")"))
   (xdoc::section
     "Inputs"
     (xdoc::ul
       (xdoc::li
         "@('name')"
         (xdoc::p
           "The name of the transformation, to be used as a prefix in the
            generated functions."))
       (xdoc::li
         "@(':extra-args')"
         (xdoc::p
           "A list of arguments to be passed to the transformation functions, in
            addition to the AST term. This list is expected to be in the format
            of @(see std::extended-formals)."))
       (xdoc::li
         "@(':with-output-off')"
         (xdoc::p
           "Controls the output. The value should be suitable for use in the
            @(':off') field of @(tsee with-output)."))
       (xdoc::li
         "other-keywords"
         (xdoc::p
           "For each case of the AST, you may specify @(':<case> fn'), where
            @('<case>') is the name of the case, and @('fn') is a lambda or
            function name. See the nullary function @(tsee deftrans-cases) for
            the possible values for @('<case>').")
         (xdoc::p
           "You may call other generated functions within @('fn'). The name of
            the function for case @('<case>') will be @('<name>-<case>'), where
            @('<name>') is the provided @('name') input."))))
   (xdoc::section
     "Example: simpadd0"
     (xdoc::p
       "The following example will generate a transformation @('my-simpadd0')
        which folds expressions such as @('x + 0') to @('x'). See
        @('tests/deftrans.lisp') for this and other examples.")
     (xdoc::codeblock
       "(deftrans my-simpadd0"
       "  :expr (lambda (expr)"
       "       (expr-case"
       "            expr"
       "            :ident (expr-fix expr)"
       "            :const (expr-fix expr)"
       "            :string (expr-fix expr)"
       "            :paren (expr-paren (my-simpadd0-expr expr.inner))"
       "            :gensel (make-expr-gensel"
       "                      :control (my-simpadd0-expr expr.control)"
       "                      :assocs (my-simpadd0-genassoc-list expr.assocs))"
       "            :arrsub (make-expr-arrsub"
       "                      :arg1 (my-simpadd0-expr expr.arg1)"
       "                      :arg2 (my-simpadd0-expr expr.arg2))"
       "            :funcall (make-expr-funcall"
       "                       :fun (my-simpadd0-expr expr.fun)"
       "                       :args (my-simpadd0-expr-list expr.args))"
       "            :member (make-expr-member"
       "                      :arg (my-simpadd0-expr expr.arg)"
       "                      :name expr.name)"
       "            :memberp (make-expr-memberp"
       "                       :arg (my-simpadd0-expr expr.arg)"
       "                       :name expr.name)"
       "            :complit (make-expr-complit"
       "                       :type (my-simpadd0-tyname expr.type)"
       "                       :elems (my-simpadd0-desiniter-list expr.elems)"
       "                       :final-comma expr.final-comma)"
       "            :unary (make-expr-unary"
       "                     :op expr.op"
       "                     :arg (my-simpadd0-expr expr.arg))"
       "                     :info expr.info)"
       "            :sizeof (expr-sizeof (my-simpadd0-tyname expr.type))"
       "            :sizeof-ambig (prog2$"
       "                            (raise \"Misusage error: ~x0.\" (expr-fix expr))"
       "                            (expr-fix expr))"
       "            :alignof (make-expr-alignof :type (my-simpadd0-tyname expr.type)"
       "                                        :uscores expr.uscores)"
       "            :cast (make-expr-cast"
       "                    :type (my-simpadd0-tyname expr.type)"
       "                    :arg (my-simpadd0-expr expr.arg))"
       "            :binary (b* ((arg1 (my-simpadd0-expr expr.arg1))"
       "                         (arg2 (my-simpadd0-expr expr.arg2)))"
       "                      ;; zero-folding occurs here"
       "                      (if (c$::expr-zerop arg2)"
       "                          arg1"
       "                        (make-expr-binary"
       "                          :op expr.op"
       "                          :arg1 arg1"
       "                          :arg2 arg2"
       "                          :info expr.info)))"
       "            :cond (make-expr-cond"
       "                    :test (my-simpadd0-expr expr.test)"
       "                    :then (my-simpadd0-expr-option expr.then)"
       "                    :else (my-simpadd0-expr expr.else))"
       "            :comma (make-expr-comma"
       "                     :first (my-simpadd0-expr expr.first)"
       "                     :next (my-simpadd0-expr expr.next))"
       "            :cast/call-ambig (prog2$"
       "                               (raise \"Misusage error: ~x0.\" (expr-fix expr))"
       "                               (expr-fix expr))"
       "            :cast/mul-ambig (prog2$"
       "                              (raise \"Misusage error: ~x0.\" (expr-fix expr))"
       "                              (expr-fix expr))"
       "            :cast/add-ambig (prog2$"
       "                              (raise \"Misusage error: ~x0.\" (expr-fix expr))"
       "                              (expr-fix expr))"
       "            :cast/sub-ambig (prog2$"
       "                              (raise \"Misusage error: ~x0.\" (expr-fix expr))"
       "                              (expr-fix expr))"
       "            :cast/and-ambig (prog2$"
       "                              (raise \"Misusage error: ~x0.\" (expr-fix expr))"
       "                              (expr-fix expr))"
       "            :stmt (expr-stmt (my-simpadd0-block-item-list expr.items))"
       "            :tycompat (make-expr-tycompat"
       "                        :type1 (my-simpadd0-tyname expr.type1)"
       "                        :type2 (my-simpadd0-tyname expr.type2))"
       "            :offsetof (make-expr-offsetof"
       "                        :type (my-simpadd0-tyname expr.type)"
       "                        :member (my-simpadd0-member-designor expr.member))"
       "            :va-arg (make-expr-va-arg"
       "                      :list (my-simpadd0-expr expr.list)"
       "                      :type (my-simpadd0-tyname expr.type))"
       "            :extension (expr-extension (my-simpadd0-tyname expr.expr)))))"
       )))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Separates a list into pairs.
;; E.g. '(foo bar baz qux) becomes '((foo . bar) (baz . qux)).
(define take-pairs
  ((list true-listp))
  :returns (alist alistp)
  (if (endp list)
      nil
    (if (consp (rest list))
        (cons (cons (first list) (second list))
              (take-pairs (rest (rest list))))
      ;; TODO: when the list is odd in length, we use nil as the last
      ;; value. Should we produce a (soft) error instead?
      (list (cons (first list) nil))))
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy deftrans-theory-forward-chaining
  '((:forward-chaining c$::expr-kind-possibilities)
    (:forward-chaining c$::decl-kind-possibilities)
    (:forward-chaining c$::decl-spec-kind-possibilities)
    (:forward-chaining c$::dirabsdeclor-kind-possibilities)
    (:forward-chaining c$::dirdeclor-kind-possibilities)
    (:forward-chaining c$::genassoc-kind-possibilities)
    (:forward-chaining c$::initer-kind-possibilities)
    (:forward-chaining c$::member-designor-kind-possibilities)
    (:forward-chaining c$::spec/qual-kind-possibilities)
    (:forward-chaining c$::structdecl-kind-possibilities)))

(defthy deftrans-theory-linear
  '((:linear c$::absdeclor-count-of-absdeclor-option-some->val)
    (:linear c$::absdeclor-count-of-dirabsdeclor-paren->inner)
    (:linear c$::absdeclor-count-of-paramdeclor-absdeclor->unwrap)
    (:linear c$::absdeclor-option-count-of-tyname->decl?)
    (:linear c$::align-spec-count-of-decl-spec-align->spec)
    (:linear c$::align-spec-count-of-spec/qual-align->spec)
    (:linear c$::block-item-count-of-car)
    (:linear c$::block-item-list-count-of-cdr)
    (:linear c$::block-item-list-count-of-expr-stmt->items)
    (:linear c$::block-item-list-count-of-stmt-compound->items)
    (:linear c$::const-expr-count-of-align-spec-alignas-expr->expr)
    (:linear c$::const-expr-count-of-const-expr-option-some->val)
    (:linear c$::const-expr-count-of-designor-sub->index)
    (:linear c$::const-expr-count-of-label-casexpr->expr)
    (:linear c$::const-expr-count-of-statassert->test)
    (:linear c$::const-expr-option-count-of-enumer->value)
    (:linear c$::const-expr-option-count-of-label-casexpr->range?)
    (:linear c$::const-expr-option-count-of-structdeclor->expr?)
    (:linear c$::decl-count-of-car)
    (:linear c$::decl-count-of-block-item-decl->unwrap)
    (:linear c$::decl-count-of-stmt-for-decl->init)
    (:linear c$::decl-list-count-of-cdr)
    (:linear c$::declor-count-of-declor-option-some->val)
    (:linear c$::declor-count-of-dirdeclor-paren->inner)
    (:linear c$::declor-count-of-initdeclor->declor)
    (:linear c$::declor-count-of-paramdeclor-declor->unwrap)
    (:linear c$::declor-option-count-of-structdeclor->declor?)
    (:linear c$::decl-spec-count-of-car)
    (:linear c$::decl-spec-list-count-of-cdr)
    (:linear c$::decl-spec-list-count-of-decl-decl->specs)
    (:linear c$::decl-spec-list-count-of-param-declon->specs)
    (:linear c$::designor-count-of-car)
    (:linear c$::designor-list-count-of-cdr)
    (:linear c$::designor-list-count-of-desiniter->designors)
    (:linear c$::desiniter-count-of-car)
    (:linear c$::desiniter-list-count-of-cdr)
    (:linear c$::desiniter-list-count-of-expr-complit->elems)
    (:linear c$::desiniter-list-count-of-initer-list->elems)
    (:linear c$::dirabsdeclor-count-of-dirabsdeclor-option-some->val)
    (:linear c$::dirabsdeclor-option-count-of-absdeclor->direct?)
    (:linear c$::dirabsdeclor-option-count-of-dirabsdeclor-array->declor?)
    (:linear c$::dirabsdeclor-option-count-of-dirabsdeclor-array-star->declor?)
    (:linear c$::dirabsdeclor-option-count-of-dirabsdeclor-array-static1->declor?)
    (:linear c$::dirabsdeclor-option-count-of-dirabsdeclor-array-static2->declor?)
    (:linear c$::dirabsdeclor-option-count-of-dirabsdeclor-function->declor?)
    (:linear c$::dirdeclor-count-of-declor->direct)
    (:linear c$::dirdeclor-count-of-dirdeclor-array->declor)
    (:linear c$::dirdeclor-count-of-dirdeclor-array-star->declor)
    (:linear c$::dirdeclor-count-of-dirdeclor-array-static1->declor)
    (:linear c$::dirdeclor-count-of-dirdeclor-array-static2->declor)
    (:linear c$::dirdeclor-count-of-dirdeclor-function-names->declor)
    (:linear c$::dirdeclor-count-of-dirdeclor-function-params->declor)
    (:linear c$::enumer-count-of-car)
    (:linear c$::enumer-list-count-of-cdr)
    (:linear c$::enumer-list-count-of-enumspec->list)
    (:linear c$::enumspec-count-of-type-spec-enum->spec)
    (:linear c$::expr-count-of-car)
    (:linear c$::expr-count-of-const-expr->expr)
    (:linear c$::expr-count-of-dirabsdeclor-array-static1->size)
    (:linear c$::expr-count-of-dirabsdeclor-array-static2->size)
    (:linear c$::expr-count-of-dirdeclor-array-static1->size)
    (:linear c$::expr-count-of-dirdeclor-array-static2->size)
    (:linear c$::expr-count-of-expr-arrsub->arg1)
    (:linear c$::expr-count-of-expr-arrsub->arg2)
    (:linear c$::expr-count-of-expr-binary->arg1)
    (:linear c$::expr-count-of-expr-binary->arg2)
    (:linear c$::expr-count-of-expr-cast->arg)
    (:linear c$::expr-count-of-expr-comma->first)
    (:linear c$::expr-count-of-expr-comma->next)
    (:linear c$::expr-count-of-expr-cond->else)
    (:linear c$::expr-count-of-expr-cond->test)
    (:linear c$::expr-count-of-expr-extension->expr)
    (:linear c$::expr-count-of-expr-funcall->fun)
    (:linear c$::expr-count-of-expr-gensel->control)
    (:linear c$::expr-count-of-expr-member->arg)
    (:linear c$::expr-count-of-expr-memberp->arg)
    (:linear c$::expr-count-of-expr-option-some->val)
    (:linear c$::expr-count-of-expr-paren->inner)
    (:linear c$::expr-count-of-expr-va-arg->list)
    (:linear c$::expr-count-of-expr-unary->arg)
    (:linear c$::expr-count-of-genassoc-default->expr)
    (:linear c$::expr-count-of-genassoc-type->expr)
    (:linear c$::expr-count-of-initer-single->expr)
    (:linear c$::expr-count-of-member-designor-sub->index)
    (:linear c$::expr-count-of-stmt-dowhile->test)
    (:linear c$::expr-count-of-stmt-if->test)
    (:linear c$::expr-count-of-stmt-ifelse->test)
    (:linear c$::expr-count-of-stmt-switch->target)
    (:linear c$::expr-count-of-stmt-while->test)
    (:linear c$::expr-count-of-type-spec-typeof-expr->expr)
    (:linear c$::expr-list-count-of-cdr)
    (:linear c$::expr-list-count-of-expr-funcall->args)
    (:linear c$::expr-option-count-of-dirabsdeclor-array->size?)
    (:linear c$::expr-option-count-of-dirdeclor-array->size?)
    (:linear c$::expr-option-count-of-expr-cond->then)
    (:linear c$::expr-option-count-of-stmt-expr->expr?)
    (:linear c$::expr-option-count-of-stmt-for-decl->next)
    (:linear c$::expr-option-count-of-stmt-for-decl->test)
    (:linear c$::expr-option-count-of-stmt-for-expr->init)
    (:linear c$::expr-option-count-of-stmt-for-expr->next)
    (:linear c$::expr-option-count-of-stmt-for-expr->test)
    (:linear c$::expr-option-count-of-stmt-return->expr?)
    (:linear c$::genassoc-count-of-car)
    (:linear c$::genassoc-list-count-of-cdr)
    (:linear c$::genassoc-list-count-of-expr-gensel->assocs)
    (:linear c$::initdeclor-count-of-car)
    (:linear c$::initdeclor-list-count-of-cdr)
    (:linear c$::initdeclor-list-count-of-decl-decl->init)
    (:linear c$::initer-count-of-desiniter->initer)
    (:linear c$::initer-count-of-initer-option-some->val)
    (:linear c$::initer-option-count-of-initdeclor->init?)
    (:linear c$::label-count-of-stmt-labeled->label)
    (:linear c$::member-designor-count-of-expr-offsetof->member)
    (:linear c$::member-designor-count-of-member-designor-dot->member)
    (:linear c$::member-designor-count-of-member-designor-sub->member)
    (:linear c$::param-declon-count-of-car)
    (:linear c$::param-declon-list-count-of-cdr)
    (:linear c$::param-declon-list-count-of-dirabsdeclor-function->params)
    (:linear c$::param-declon-list-count-of-dirdeclor-function-params->params)
    (:linear c$::paramdeclor-count-of-param-declon->decl)
    (:linear c$::spec/qual-count-of-car)
    (:linear c$::spec/qual-list-count-of-cdr)
    (:linear c$::spec/qual-list-count-of-structdecl-member->specqual)
    (:linear c$::spec/qual-list-count-of-tyname->specqual)
    (:linear c$::statassert-count-of-decl-statassert->unwrap)
    (:linear c$::statassert-count-of-structdecl-statassert->unwrap)
    (:linear c$::stmt-count-of-block-item-stmt->unwrap)
    (:linear c$::stmt-count-of-stmt-dowhile->body)
    (:linear c$::stmt-count-of-stmt-for-expr->body)
    (:linear c$::stmt-count-of-stmt-for-decl->body)
    (:linear c$::stmt-count-of-stmt-if->then)
    (:linear c$::stmt-count-of-stmt-ifelse->else)
    (:linear c$::stmt-count-of-stmt-ifelse->then)
    (:linear c$::stmt-count-of-stmt-labeled->stmt)
    (:linear c$::stmt-count-of-stmt-switch->body)
    (:linear c$::stmt-count-of-stmt-while->body)
    (:linear c$::structdecl-count-of-car)
    (:linear c$::structdecl-list-count-of-cdr)
    (:linear c$::structdecl-list-count-of-strunispec->members)
    (:linear c$::structdeclor-count-of-car)
    (:linear c$::structdeclor-list-count-of-cdr)
    (:linear c$::structdeclor-list-count-of-structdecl-member->declor)
    (:linear c$::strunispec-count-of-type-spec-struct->spec)
    (:linear c$::strunispec-count-of-type-spec-union->spec)
    (:linear c$::tyname-count-of-align-spec-alignas-type->type)
    (:linear c$::tyname-count-of-expr-alignof->type)
    (:linear c$::tyname-count-of-expr-cast->type)
    (:linear c$::tyname-count-of-expr-complit->type)
    (:linear c$::tyname-count-of-expr-sizeof->type)
    (:linear c$::tyname-count-of-expr-tycompat->type1)
    (:linear c$::tyname-count-of-expr-tycompat->type2)
    (:linear c$::tyname-count-of-genassoc-type->type)
    (:linear c$::tyname-count-of-expr-offsetof->type)
    (:linear c$::tyname-count-of-expr-va-arg->type)
    (:linear c$::tyname-count-of-type-spec-atomic->type)
    (:linear c$::tyname-count-of-type-spec-typeof-type->type)
    (:linear c$::type-spec-count-of-decl-spec-typespec->spec)
    (:linear c$::type-spec-count-of-spec/qual-typespec->spec)))

(defthy deftrans-theory-type-prescription
  '((:type-prescription absdeclor)
    (:type-prescription absdeclor-count)
    (:type-prescription absdeclor-option-count)
    (:type-prescription align-spec-alignas-expr)
    (:type-prescription align-spec-alignas-type)
    (:type-prescription align-spec-count)
    (:type-prescription block-item-count)
    (:type-prescription block-item-decl)
    (:type-prescription block-item-list-count)
    (:type-prescription block-item-stmt)
    (:type-prescription c$::align-spec-fix$inline)
    (:type-prescription c$::block-item-fix$inline)
    (:type-prescription c$::consp-of-align-spec-fix)
    (:type-prescription c$::consp-of-block-item-fix)
    (:type-prescription c$::consp-of-decl-spec-fix)
    (:type-prescription c$::consp-of-designor-fix)
    (:type-prescription c$::consp-of-dirabsdeclor-fix)
    (:type-prescription c$::consp-of-dirdeclor-fix)
    (:type-prescription c$::consp-of-expr-fix)
    (:type-prescription c$::consp-of-paramdeclor-fix)
    (:type-prescription c$::consp-of-spec/qual-fix)
    (:type-prescription c$::consp-of-stmt-fix)
    (:type-prescription c$::consp-of-type-spec-fix)
    (:type-prescription c$::decl-spec-fix$inline)
    (:type-prescription c$::designor-fix$inline)
    (:type-prescription c$::dirabsdeclor-array)
    (:type-prescription c$::dirabsdeclor-array-static1)
    (:type-prescription c$::dirabsdeclor-array-static2)
    (:type-prescription c$::dirabsdeclor-fix$inline)
    (:type-prescription c$::dirabsdeclor-function)
    (:type-prescription c$::dirdeclor-array)
    (:type-prescription c$::dirdeclor-array-star)
    (:type-prescription c$::dirdeclor-array-static1)
    (:type-prescription c$::dirdeclor-array-static2)
    (:type-prescription c$::dirdeclor-fix$inline)
    (:type-prescription c$::dirdeclor-function-names)
    (:type-prescription c$::dirdeclor-function-params)
    (:type-prescription c$::expr-arrsub)
    (:type-prescription c$::expr-binary)
    (:type-prescription c$::expr-cast)
    (:type-prescription c$::expr-comma)
    (:type-prescription c$::expr-complit)
    (:type-prescription c$::expr-cond)
    (:type-prescription c$::expr-fix$inline)
    (:type-prescription c$::expr-funcall)
    (:type-prescription c$::expr-gensel)
    (:type-prescription c$::expr-member)
    (:type-prescription c$::expr-memberp)
    (:type-prescription c$::expr-unary)
    (:type-prescription c$::genassoc-type)
    (:type-prescription c$::initer-list)
    (:type-prescription c$::paramdeclor-fix$inline)
    (:type-prescription c$::return-type-of-absdeclor-count.count)
    (:type-prescription c$::return-type-of-absdeclor-option-count.count)
    (:type-prescription c$::return-type-of-align-spec-count.count)
    (:type-prescription c$::return-type-of-block-item-count.count)
    (:type-prescription c$::return-type-of-block-item-list-count.count)
    (:type-prescription c$::return-type-of-const-expr-count.count)
    (:type-prescription c$::return-type-of-const-expr-option-count.count)
    (:type-prescription c$::return-type-of-decl-count.count)
    (:type-prescription c$::return-type-of-decl-list-count.count)
    (:type-prescription c$::return-type-of-declor-count.count)
    (:type-prescription c$::return-type-of-declor-option-count.count)
    (:type-prescription c$::return-type-of-decl-spec-count.count)
    (:type-prescription c$::return-type-of-decl-spec-list-count.count)
    (:type-prescription c$::return-type-of-designor-count.count)
    (:type-prescription c$::return-type-of-designor-list-count.count)
    (:type-prescription c$::return-type-of-desiniter-count.count)
    (:type-prescription c$::return-type-of-desiniter-list-count.count)
    (:type-prescription c$::return-type-of-dirabsdeclor-count.count)
    (:type-prescription c$::return-type-of-dirabsdeclor-option-count.count)
    (:type-prescription c$::return-type-of-dirdeclor-count.count)
    (:type-prescription c$::return-type-of-enumer-count.count)
    (:type-prescription c$::return-type-of-enumer-list-count.count)
    (:type-prescription c$::return-type-of-enumspec-count.count)
    (:type-prescription c$::return-type-of-expr-count.count)
    (:type-prescription c$::return-type-of-expr-list-count.count)
    (:type-prescription c$::return-type-of-expr-option-count.count)
    (:type-prescription c$::return-type-of-genassoc-count.count)
    (:type-prescription c$::return-type-of-genassoc-list-count.count)
    (:type-prescription c$::return-type-of-initdeclor-list-count.count)
    (:type-prescription c$::return-type-of-initer-count.count)
    (:type-prescription c$::return-type-of-initer-option-count.count)
    (:type-prescription c$::return-type-of-label-count.count)
    (:type-prescription c$::return-type-of-member-designor-count.count)
    (:type-prescription c$::return-type-of-param-declon-count.count)
    (:type-prescription c$::return-type-of-param-declon-list-count.count)
    (:type-prescription c$::return-type-of-paramdeclor-count.count)
    (:type-prescription c$::return-type-of-spec/qual-count.count)
    (:type-prescription c$::return-type-of-spec/qual-list-count.count)
    (:type-prescription c$::return-type-of-statassert-count.count)
    (:type-prescription c$::return-type-of-stmt-count.count)
    (:type-prescription c$::return-type-of-structdecl-count.count)
    (:type-prescription c$::return-type-of-structdecl-list-count.count)
    (:type-prescription c$::return-type-of-structdeclor-count.count)
    (:type-prescription c$::return-type-of-structdeclor-list-count.count)
    (:type-prescription c$::return-type-of-strunispec-count.count)
    (:type-prescription c$::return-type-of-tyname-count.count)
    (:type-prescription c$::return-type-of-type-spec-count.count)
    (:type-prescription c$::spec/qual-fix$inline)
    (:type-prescription c$::stmt-dowhile)
    (:type-prescription c$::stmt-fix$inline)
    (:type-prescription c$::stmt-for-expr)
    (:type-prescription c$::stmt-for-decl)
    (:type-prescription c$::stmt-if)
    (:type-prescription c$::stmt-ifelse)
    (:type-prescription c$::stmt-labeled)
    (:type-prescription c$::stmt-switch)
    (:type-prescription c$::stmt-while)
    (:type-prescription c$::structdecl-member)
    (:type-prescription c$::type-spec-fix$inline)
    (:type-prescription const-expr)
    (:type-prescription const-expr-count)
    (:type-prescription const-expr-option-count)
    (:type-prescription decl-count)
    (:type-prescription declor)
    (:type-prescription declor-count)
    (:type-prescription declor-option-count)
    (:type-prescription decl-spec-align)
    (:type-prescription decl-spec-count)
    (:type-prescription decl-spec-list-count)
    (:type-prescription decl-spec-typespec)
    (:type-prescription designor-count)
    (:type-prescription designor-list-count)
    (:type-prescription designor-sub)
    (:type-prescription desiniter)
    (:type-prescription desiniter-count)
    (:type-prescription desiniter-list-count)
    (:type-prescription dirabsdeclor-array-star)
    (:type-prescription dirabsdeclor-count)
    (:type-prescription dirabsdeclor-option-count)
    (:type-prescription dirabsdeclor-paren)
    (:type-prescription dirdeclor-count)
    (:type-prescription dirdeclor-paren)
    (:type-prescription enumer)
    (:type-prescription enumer-count)
    (:type-prescription enumer-list-count)
    (:type-prescription enumspec)
    (:type-prescription enumspec-count)
    (:type-prescription expr-alignof)
    (:type-prescription expr-count)
    (:type-prescription expr-list-count)
    (:type-prescription expr-option-count)
    (:type-prescription expr-paren)
    (:type-prescription expr-sizeof)
    (:type-prescription genassoc-count)
    (:type-prescription genassoc-default)
    (:type-prescription genassoc-list-count)
    (:type-prescription initer-count)
    (:type-prescription initer-option-count)
    (:type-prescription initer-single)
    (:type-prescription initdeclor-count)
    (:type-prescription param-declon)
    (:type-prescription param-declon-count)
    (:type-prescription param-declon-list-count)
    (:type-prescription paramdeclor-absdeclor)
    (:type-prescription paramdeclor-count)
    (:type-prescription paramdeclor-declor)
    (:type-prescription paramdeclor-none)
    (:type-prescription spec/qual-align)
    (:type-prescription spec/qual-count)
    (:type-prescription spec/qual-list-count)
    (:type-prescription spec/qual-typespec)
    (:type-prescription statassert)
    (:type-prescription statassert-count)
    (:type-prescription stmt-compound)
    (:type-prescription stmt-count)
    (:type-prescription stmt-expr)
    (:type-prescription stmt-return)
    (:type-prescription structdecl-count)
    (:type-prescription structdecl-list-count)
    (:type-prescription structdecl-statassert)
    (:type-prescription structdeclor)
    (:type-prescription structdeclor-count)
    (:type-prescription structdeclor-list-count)
    (:type-prescription strunispec)
    (:type-prescription strunispec-count)
    (:type-prescription tyname)
    (:type-prescription tyname-count)
    (:type-prescription type-spec-atomic)
    (:type-prescription type-spec-count)
    (:type-prescription type-spec-enum)
    (:type-prescription type-spec-struct)
    (:type-prescription type-spec-union)))

(defthy deftrans-measure-theory
  '(endp
    eql
    natp
    o-p
    o-finp
    o<
    deftrans-theory-forward-chaining
    deftrans-theory-linear
    deftrans-theory-type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftrans-get-args
  ((args true-listp))
  :short "Gets arg names from a define-style arg list."
  (if (endp args)
      nil
    (cons (if (consp (first args))
              (car (first args))
            (first args))
          (deftrans-get-args (rest args)))))

(define deftrans-defn
  ((case symbolp)
   (names alistp)
   (bodies alistp)
   (args true-listp)
   (extra-args true-listp)
   default-body
   extras)
  (b* ((lookup (assoc-eq (acl2::packn-pos (list case) (pkg-witness "KEYWORD")) bodies))
       (arg-names (append (deftrans-get-args args) (deftrans-get-args extra-args))))
    `(define ,(cdr (assoc-eq case names))
       (,@args ,@extra-args)
       (declare (ignorable ,@arg-names))
       ,(if lookup
            `(,(cdr lookup) ,@arg-names)
          default-body)
       ,@extras))
  :guard-hints (("Goal" :in-theory (enable atom-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftrans-defn-ident
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp))
  (deftrans-defn
   'ident
   names
   bodies
   '((ident identp))
   extra-args
   '(ident-fix ident)
   '(:returns (new-ident identp))))

(define deftrans-defn-ident-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'ident-list
   names
   bodies
   '((idents ident-listp))
   extra-args
   `(if (endp idents)
        nil
      (cons (,(cdr (assoc-eq 'ident names)) (car idents) ,@extra-args-names)
            (,(cdr (assoc-eq 'ident-list names)) (cdr idents) ,@extra-args-names)))
   '(:returns (new-idents ident-listp)
     :measure (acl2-count idents)
     :hints (("Goal" :in-theory nil)))))

(define deftrans-defn-const
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp))
  (deftrans-defn
   'const
   names
   bodies
   '((const constp))
   extra-args
   '(const-fix const)
   '(:returns (new-const constp))))

(define deftrans-defn-expr
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'expr
   names
   bodies
   '((expr exprp))
   extra-args
   `(expr-case
      expr
      :ident (make-expr-ident
               :ident (,(cdr (assoc-eq 'ident names)) expr.ident ,@extra-args-names)
               :info expr.info)
      :const (expr-fix expr)
      :string (expr-fix expr)
      :paren (expr-paren (,(cdr (assoc-eq 'expr names)) expr.inner ,@extra-args-names))
      :gensel (make-expr-gensel
                :control (,(cdr (assoc-eq 'expr names)) expr.control ,@extra-args-names)
                :assocs (,(cdr (assoc-eq 'genassoc-list names)) expr.assocs ,@extra-args-names))
      :arrsub (make-expr-arrsub
                :arg1 (,(cdr (assoc-eq 'expr names)) expr.arg1 ,@extra-args-names)
                :arg2 (,(cdr (assoc-eq 'expr names)) expr.arg2 ,@extra-args-names))
      :funcall (make-expr-funcall
                 :fun (,(cdr (assoc-eq 'expr names)) expr.fun ,@extra-args-names)
                 :args (,(cdr (assoc-eq 'expr-list names)) expr.args ,@extra-args-names))
      :member (make-expr-member
                :arg (,(cdr (assoc-eq 'expr names)) expr.arg ,@extra-args-names)
                :name expr.name)
      :memberp (make-expr-memberp
                 :arg (,(cdr (assoc-eq 'expr names)) expr.arg ,@extra-args-names)
                 :name expr.name)
      :complit (make-expr-complit
                 :type (,(cdr (assoc-eq 'tyname names)) expr.type ,@extra-args-names)
                 :elems (,(cdr (assoc-eq 'desiniter-list names)) expr.elems ,@extra-args-names)
                 :final-comma expr.final-comma)
      :unary (make-expr-unary
               :op expr.op
               :arg (,(cdr (assoc-eq 'expr names)) expr.arg ,@extra-args-names)
               :info expr.info)
      :sizeof (expr-sizeof (,(cdr (assoc-eq 'tyname names)) expr.type ,@extra-args-names))
      :sizeof-ambig (prog2$
                      (raise "Misusage error: ~x0." (expr-fix expr))
                      (expr-fix expr))
      :alignof (make-expr-alignof
                :type (,(cdr (assoc-eq 'tyname names)) expr.type ,@extra-args-names)
                :uscores expr.uscores)
      :cast (make-expr-cast
              :type (,(cdr (assoc-eq 'tyname names)) expr.type ,@extra-args-names)
              :arg (,(cdr (assoc-eq 'expr names)) expr.arg ,@extra-args-names))
      :binary (make-expr-binary
                :op expr.op
                :arg1 (,(cdr (assoc-eq 'expr names)) expr.arg1 ,@extra-args-names)
                :arg2 (,(cdr (assoc-eq 'expr names)) expr.arg2 ,@extra-args-names)
                :info expr.info)
      :cond (make-expr-cond
              :test (,(cdr (assoc-eq 'expr names)) expr.test ,@extra-args-names)
              :then (,(cdr (assoc-eq 'expr-option names)) expr.then ,@extra-args-names)
              :else (,(cdr (assoc-eq 'expr names)) expr.else ,@extra-args-names))
      :comma (make-expr-comma
               :first (,(cdr (assoc-eq 'expr names)) expr.first ,@extra-args-names)
               :next (,(cdr (assoc-eq 'expr names)) expr.next ,@extra-args-names))
      :cast/call-ambig (prog2$
                         (raise "Misusage error: ~x0." (expr-fix expr))
                         (expr-fix expr))
      :cast/mul-ambig (prog2$
                        (raise "Misusage error: ~x0." (expr-fix expr))
                        (expr-fix expr))
      :cast/add-ambig (prog2$
                        (raise "Misusage error: ~x0." (expr-fix expr))
                        (expr-fix expr))
      :cast/sub-ambig (prog2$
                        (raise "Misusage error: ~x0." (expr-fix expr))
                        (expr-fix expr))
      :cast/and-ambig (prog2$
                        (raise "Misusage error: ~x0." (expr-fix expr))
                        (expr-fix expr))
      :stmt (expr-stmt (,(cdr (assoc-eq 'block-item-list names)) expr.items ,@extra-args-names))
      :tycompat (make-expr-tycompat
                  :type1 (,(cdr (assoc-eq 'tyname names)) expr.type1 ,@extra-args-names)
                  :type2 (,(cdr (assoc-eq 'tyname names)) expr.type2 ,@extra-args-names))
      :offsetof (make-expr-offsetof
                  :type (,(cdr (assoc-eq 'tyname names)) expr.type ,@extra-args-names)
                  :member (,(cdr (assoc-eq 'member-designor names)) expr.member ,@extra-args-names))
      :va-arg (make-expr-va-arg
                :list (,(cdr (assoc-eq 'expr names)) expr.list ,@extra-args-names)
                :type (,(cdr (assoc-eq 'tyname names)) expr.type ,@extra-args-names))
      :extension (expr-extension (,(cdr (assoc-eq 'expr names)) expr.expr ,@extra-args-names)))
   '(:returns (new-expr exprp)
     :measure (expr-count expr))))

(define deftrans-defn-expr-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'expr-list
   names
   bodies
   '((exprs expr-listp))
   extra-args
   `(if (endp exprs)
        nil
      (cons (,(cdr (assoc-eq 'expr names)) (car exprs) ,@extra-args-names)
            (,(cdr (assoc-eq 'expr-list names)) (cdr exprs) ,@extra-args-names)))
   '(:returns (new-exprs expr-listp)
     :measure (expr-list-count exprs))))

(define deftrans-defn-expr-option
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'expr-option
   names
   bodies
   '((expr? expr-optionp))
   extra-args
   `(expr-option-case
      expr?
      :some (,(cdr (assoc-eq 'expr names)) expr?.val ,@extra-args-names)
      :none nil)
   '(:returns (new-expr? expr-optionp)
     :measure (expr-option-count expr?))))

(define deftrans-defn-const-expr
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'const-expr
   names
   bodies
   '((cexpr const-exprp))
   extra-args
   `(const-expr (,(cdr (assoc-eq 'expr names)) (const-expr->expr cexpr) ,@extra-args-names))
   '(:returns (new-cexpr const-exprp)
     :measure (const-expr-count cexpr))))

(define deftrans-defn-const-expr-option
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'const-expr-option
   names
   bodies
   '((const-expr? const-expr-optionp))
   extra-args
   `(const-expr-option-case
      const-expr?
      :some (,(cdr (assoc-eq 'const-expr names)) const-expr?.val ,@extra-args-names)
      :none nil)
   '(:returns (new-const-expr? const-expr-optionp)
     :measure (const-expr-option-count const-expr?))))

(define deftrans-defn-genassoc
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'genassoc
   names
   bodies
   '((genassoc genassocp))
   extra-args
   `(genassoc-case
      genassoc
      :type (make-genassoc-type
              :type (,(cdr (assoc-eq 'tyname names)) genassoc.type ,@extra-args-names)
              :expr (,(cdr (assoc-eq 'expr names)) genassoc.expr ,@extra-args-names))
      :default (genassoc-default (,(cdr (assoc-eq 'expr names)) genassoc.expr ,@extra-args-names)))
   '(:returns (new-genassoc genassocp)
     :measure (genassoc-count genassoc))))

(define deftrans-defn-genassoc-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'genassoc-list
   names
   bodies
   '((genassocs genassoc-listp))
   extra-args
   `(if (endp genassocs)
        nil
      (cons (,(cdr (assoc-eq 'genassoc names)) (car genassocs) ,@extra-args-names)
            (,(cdr (assoc-eq 'genassoc-list names)) (cdr genassocs) ,@extra-args-names)))
   '(:returns (new-genassocs genassoc-listp)
     :measure (genassoc-list-count genassocs))))

(define deftrans-defn-member-designor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'member-designor
   names
   bodies
   '((memdes member-designorp))
   extra-args
   `(member-designor-case
     memdes
     :ident (member-designor-fix memdes)
     :dot (make-member-designor-dot
            :member (,(cdr (assoc-eq 'member-designor names)) memdes.member ,@extra-args-names)
            :name memdes.name)
     :sub (make-member-designor-sub
            :member (,(cdr (assoc-eq 'member-designor names)) memdes.member ,@extra-args-names)
            :index (,(cdr (assoc-eq 'expr names)) memdes.index ,@extra-args-names)))
   '(:returns (new-memdes member-designorp)
     :measure (member-designor-count memdes))))

(define deftrans-defn-type-spec
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'type-spec
   names
   bodies
   '((tyspec type-specp))
   extra-args
   `(type-spec-case
      tyspec
      :void (type-spec-fix tyspec)
      :char (type-spec-fix tyspec)
      :short (type-spec-fix tyspec)
      :int (type-spec-fix tyspec)
      :long (type-spec-fix tyspec)
      :float (type-spec-fix tyspec)
      :double (type-spec-fix tyspec)
      :signed (type-spec-fix tyspec)
      :unsigned (type-spec-fix tyspec)
      :bool (type-spec-fix tyspec)
      :complex (type-spec-fix tyspec)
      :atomic (type-spec-atomic (,(cdr (assoc-eq 'tyname names)) tyspec.type ,@extra-args-names))
      :struct (type-spec-struct (,(cdr (assoc-eq 'strunispec names)) tyspec.spec ,@extra-args-names))
      :union (type-spec-union (,(cdr (assoc-eq 'strunispec names)) tyspec.spec ,@extra-args-names))
      :enum (type-spec-enum (,(cdr (assoc-eq 'enumspec names)) tyspec.spec ,@extra-args-names))
      :typedef (type-spec-fix tyspec)
      :int128 (type-spec-fix tyspec)
      :float32 (type-spec-fix tyspec)
      :float32x (type-spec-fix tyspec)
      :float64 (type-spec-fix tyspec)
      :float64x (type-spec-fix tyspec)
      :float128 (type-spec-fix tyspec)
      :float128x (type-spec-fix tyspec)
      :builtin-va-list (type-spec-fix tyspec)
      :struct-empty (type-spec-fix tyspec)
      :typeof-expr (make-type-spec-typeof-expr
                    :expr (,(cdr (assoc-eq 'expr names)) tyspec.expr ,@extra-args-names)
                    :uscores tyspec.uscores)
      :typeof-type (make-type-spec-typeof-type
                    :type (,(cdr (assoc-eq 'tyname names)) tyspec.type ,@extra-args-names)
                    :uscores tyspec.uscores)
      :typeof-ambig (prog2$
                     (raise "Misusage error: ~x0." (type-spec-fix tyspec))
                     (type-spec-fix tyspec))
      :auto-type (type-spec-fix tyspec))
   '(:returns (new-tyspec type-specp)
     :measure (type-spec-count tyspec))))

(define deftrans-defn-spec/qual
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'spec/qual
   names
   bodies
   '((specqual spec/qual-p))
   extra-args
   `(spec/qual-case
      specqual
      :typespec (spec/qual-typespec (,(cdr (assoc-eq 'type-spec names)) specqual.spec ,@extra-args-names))
      :typequal (spec/qual-fix specqual)
      :align (spec/qual-align (,(cdr (assoc-eq 'align-spec names)) specqual.spec ,@extra-args-names))
      :attrib (spec/qual-fix specqual))
   '(:returns (new-specqual spec/qual-p)
     :measure (spec/qual-count specqual))))

(define deftrans-defn-spec/qual-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'spec/qual-list
   names
   bodies
   '((specquals spec/qual-listp))
   extra-args
   `(if (endp specquals)
        nil
      (cons (,(cdr (assoc-eq 'spec/qual names)) (car specquals) ,@extra-args-names)
            (,(cdr (assoc-eq 'spec/qual-list names)) (cdr specquals) ,@extra-args-names)))
   '(:returns (new-specquals spec/qual-listp)
     :measure (spec/qual-list-count specquals))))

(define deftrans-defn-align-spec
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'align-spec
   names
   bodies
   '((alignspec align-specp))
   extra-args
   `(align-spec-case
      alignspec
      :alignas-type (align-spec-alignas-type (,(cdr (assoc-eq 'tyname names)) alignspec.type ,@extra-args-names))
      :alignas-expr (align-spec-alignas-expr (,(cdr (assoc-eq 'const-expr names)) alignspec.expr ,@extra-args-names))
      :alignas-ambig (prog2$
                       (raise "Misusage error: ~x0." (align-spec-fix alignspec))
                       (align-spec-fix alignspec)))
   '(:returns (new-alignspec align-specp)
     :measure (align-spec-count alignspec))))

(define deftrans-defn-decl-spec
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'decl-spec
   names
   bodies
   '((declspec decl-specp))
   extra-args
   `(decl-spec-case
      declspec
      :stoclass (decl-spec-fix declspec)
      :typespec (decl-spec-typespec (,(cdr (assoc-eq 'type-spec names)) declspec.spec ,@extra-args-names))
      :typequal (decl-spec-fix declspec)
      :function (decl-spec-fix declspec)
      :align (decl-spec-align (,(cdr (assoc-eq 'align-spec names)) declspec.spec ,@extra-args-names))
      :attrib (decl-spec-fix declspec)
      :stdcall (decl-spec-fix declspec)
      :declspec (decl-spec-fix declspec))
   '(:returns (new-declspec decl-specp)
     :measure (decl-spec-count declspec))))

(define deftrans-defn-decl-spec-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'decl-spec-list
   names
   bodies
   '((declspecs decl-spec-listp))
   extra-args
   `(if (endp declspecs)
        nil
      (cons (,(cdr (assoc-eq 'decl-spec names)) (car declspecs) ,@extra-args-names)
            (,(cdr (assoc-eq 'decl-spec-list names)) (cdr declspecs) ,@extra-args-names)))
   '(:returns (new-declspecs decl-spec-listp)
     :measure (decl-spec-list-count declspecs))))

(define deftrans-defn-initer
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'initer
   names
   bodies
   '((initer initerp))
   extra-args
   `(initer-case
      initer
      :single (initer-single (,(cdr (assoc-eq 'expr names)) initer.expr ,@extra-args-names))
      :list (make-initer-list
              :elems (,(cdr (assoc-eq 'desiniter-list names)) initer.elems ,@extra-args-names)
              :final-comma initer.final-comma))
   '(:returns (new-initer initerp)
     :measure (initer-count initer))))

(define deftrans-defn-initer-option
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'initer-option
   names
   bodies
   '((initer? initer-optionp))
   extra-args
   `(initer-option-case
      initer?
      :some (,(cdr (assoc-eq 'initer names)) initer?.val ,@extra-args-names)
      :none nil)
   '(:returns (new-initer? initer-optionp)
     :measure (initer-option-count initer?))))

(define deftrans-defn-desiniter
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'desiniter
   names
   bodies
   '((desiniter desiniterp))
   extra-args
   `(b* (((desiniter desiniter) desiniter))
      (make-desiniter
        :designors (,(cdr (assoc-eq 'designor-list names)) desiniter.designors ,@extra-args-names)
        :initer (,(cdr (assoc-eq 'initer names)) desiniter.initer ,@extra-args-names)))
   '(:returns (new-desiniter desiniterp)
     :measure (desiniter-count desiniter))))

(define deftrans-defn-desiniter-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'desiniter-list
   names
   bodies
   '((desiniters desiniter-listp))
   extra-args
   `(if (endp desiniters)
        nil
      (cons (,(cdr (assoc-eq 'desiniter names)) (car desiniters) ,@extra-args-names)
            (,(cdr (assoc-eq 'desiniter-list names)) (cdr desiniters) ,@extra-args-names)))
   '(:returns (new-desiniters desiniter-listp)
     :measure (desiniter-list-count desiniters))))

(define deftrans-defn-designor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'designor
   names
   bodies
   '((designor designorp))
   extra-args
   `(designor-case
      designor
      :sub (designor-sub (,(cdr (assoc-eq 'const-expr names)) designor.index ,@extra-args-names))
      :dot (designor-fix designor))
   '(:returns (new-designor designorp)
     :measure (designor-count designor))))

(define deftrans-defn-designor-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'designor-list
   names
   bodies
   '((designors designor-listp))
   extra-args
   `(if (endp designors)
        nil
      (cons (,(cdr (assoc-eq 'designor names)) (car designors) ,@extra-args-names)
            (,(cdr (assoc-eq 'designor-list names)) (cdr designors) ,@extra-args-names)))
   '(:returns (new-designors designor-listp)
     :measure (designor-list-count designors))))

(define deftrans-defn-declor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'declor
   names
   bodies
   '((declor declorp))
   extra-args
   `(b* (((declor declor) declor))
      (make-declor
        :pointers declor.pointers
        :direct (,(cdr (assoc-eq 'dirdeclor names)) declor.direct ,@extra-args-names)))
   '(:returns (new-declor declorp)
     :measure (declor-count declor))))

(define deftrans-defn-declor-option
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'declor-option
   names
   bodies
   '((declor? declor-optionp))
   extra-args
   `(declor-option-case
      declor?
      :some (,(cdr (assoc-eq 'declor names)) declor?.val ,@extra-args-names)
      :none nil)
   '(:returns (new-declor? declor-optionp)
     :measure (declor-option-count declor?))))

(define deftrans-defn-dirdeclor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'dirdeclor
   names
   bodies
   '((dirdeclor dirdeclorp))
   extra-args
   `(dirdeclor-case
      dirdeclor
      :ident (dirdeclor-ident (,(cdr (assoc-eq 'ident names)) dirdeclor.ident ,@extra-args-names))
      :paren (dirdeclor-paren (,(cdr (assoc-eq 'declor names)) dirdeclor.inner ,@extra-args-names))
      :array (make-dirdeclor-array
               :declor (,(cdr (assoc-eq 'dirdeclor names)) dirdeclor.declor ,@extra-args-names)
               :qualspecs dirdeclor.qualspecs
               :size? (,(cdr (assoc-eq 'expr-option names)) dirdeclor.size? ,@extra-args-names))
      :array-static1 (make-dirdeclor-array-static1
                       :declor (,(cdr (assoc-eq 'dirdeclor names)) dirdeclor.declor ,@extra-args-names)
                       :qualspecs dirdeclor.qualspecs
                       :size (,(cdr (assoc-eq 'expr names)) dirdeclor.size ,@extra-args-names))
      :array-static2 (make-dirdeclor-array-static2
                       :declor (,(cdr (assoc-eq 'dirdeclor names)) dirdeclor.declor ,@extra-args-names)
                       :qualspecs dirdeclor.qualspecs
                       :size (,(cdr (assoc-eq 'expr names)) dirdeclor.size ,@extra-args-names))
      :array-star (make-dirdeclor-array-star
                    :declor (,(cdr (assoc-eq 'dirdeclor names)) dirdeclor.declor ,@extra-args-names)
                    :qualspecs dirdeclor.qualspecs)
      :function-params (make-dirdeclor-function-params
                         :declor (,(cdr (assoc-eq 'dirdeclor names)) dirdeclor.declor ,@extra-args-names)
                         :params (,(cdr (assoc-eq 'param-declon-list names)) dirdeclor.params ,@extra-args-names)
                         :ellipsis dirdeclor.ellipsis)
      :function-names (make-dirdeclor-function-names
                        :declor (,(cdr (assoc-eq 'dirdeclor names)) dirdeclor.declor ,@extra-args-names)
                        :names (,(cdr (assoc-eq 'ident-list names)) dirdeclor.names ,@extra-args-names)))
   '(:returns (new-dirdeclor dirdeclorp)
     :measure (dirdeclor-count dirdeclor))))

(define deftrans-defn-absdeclor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'absdeclor
   names
   bodies
   '((absdeclor absdeclorp))
   extra-args
   `(b* (((absdeclor absdeclor) absdeclor))
      (make-absdeclor
        :pointers absdeclor.pointers
        :direct? (,(cdr (assoc-eq 'dirabsdeclor-option names)) absdeclor.direct? ,@extra-args-names)))
   '(:returns (new-absdeclor absdeclorp)
     :measure (absdeclor-count absdeclor))))

(define deftrans-defn-absdeclor-option
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'absdeclor-option
   names
   bodies
   '((absdeclor? absdeclor-optionp))
   extra-args
   `(absdeclor-option-case
      absdeclor?
      :some (,(cdr (assoc-eq 'absdeclor names)) absdeclor?.val ,@extra-args-names)
      :none nil)
   '(:returns (new-absdeclor? absdeclor-optionp)
     :measure (absdeclor-option-count absdeclor?))))

(define deftrans-defn-dirabsdeclor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'dirabsdeclor
   names
   bodies
   '((dirabsdeclor dirabsdeclorp))
   extra-args
   `(dirabsdeclor-case
      dirabsdeclor
      :dummy-base (prog2$
                    (raise "Misusage error: ~x0." (dirabsdeclor-fix dirabsdeclor))
                    (dirabsdeclor-fix dirabsdeclor))
      :paren (dirabsdeclor-paren (,(cdr (assoc-eq 'absdeclor names)) dirabsdeclor.inner ,@extra-args-names))
      :array (make-dirabsdeclor-array
               :declor? (,(cdr (assoc-eq 'dirabsdeclor-option names)) dirabsdeclor.declor? ,@extra-args-names)
               :qualspecs dirabsdeclor.qualspecs
               :size? (,(cdr (assoc-eq 'expr-option names)) dirabsdeclor.size? ,@extra-args-names))
      :array-static1 (make-dirabsdeclor-array-static1
                       :declor? (,(cdr (assoc-eq 'dirabsdeclor-option names)) dirabsdeclor.declor? ,@extra-args-names)
                       :qualspecs dirabsdeclor.qualspecs
                       :size (,(cdr (assoc-eq 'expr names)) dirabsdeclor.size ,@extra-args-names))
      :array-static2 (make-dirabsdeclor-array-static2
                       :declor? (,(cdr (assoc-eq 'dirabsdeclor-option names)) dirabsdeclor.declor? ,@extra-args-names)
                       :qualspecs dirabsdeclor.qualspecs
                       :size (,(cdr (assoc-eq 'expr names)) dirabsdeclor.size ,@extra-args-names))
      :array-star (dirabsdeclor-array-star
                    (,(cdr (assoc-eq 'dirabsdeclor-option names)) dirabsdeclor.declor? ,@extra-args-names))
      :function (make-dirabsdeclor-function
                  :declor? (,(cdr (assoc-eq 'dirabsdeclor-option names)) dirabsdeclor.declor? ,@extra-args-names)
                  :params (,(cdr (assoc-eq 'param-declon-list names)) dirabsdeclor.params ,@extra-args-names)
                  :ellipsis dirabsdeclor.ellipsis))
   '(:returns (new-dirabsdeclor dirabsdeclorp)
     :measure (dirabsdeclor-count dirabsdeclor))))

(define deftrans-defn-dirabsdeclor-option
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'dirabsdeclor-option
   names
   bodies
   '((dirabsdeclor? dirabsdeclor-optionp))
   extra-args
   `(dirabsdeclor-option-case
      dirabsdeclor?
      :some (,(cdr (assoc-eq 'dirabsdeclor names)) dirabsdeclor?.val ,@extra-args-names)
      :none nil)
   '(:returns (new-dirabsdeclor? dirabsdeclor-optionp)
     :measure (dirabsdeclor-option-count dirabsdeclor?))))

(define deftrans-defn-param-declon
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'param-declon
   names
   bodies
   '((paramdecl param-declonp))
   extra-args
   `(b* (((param-declon paramdecl) paramdecl))
      (make-param-declon :specs (,(cdr (assoc-eq 'decl-spec-list names)) paramdecl.specs ,@extra-args-names)
                      :decl (,(cdr (assoc-eq 'paramdeclor names)) paramdecl.decl ,@extra-args-names)))
   '(:returns (new-paramdecl param-declonp)
     :measure (param-declon-count paramdecl))))

(define deftrans-defn-param-declon-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'param-declon-list
   names
   bodies
   '((paramdecls param-declon-listp))
   extra-args
   `(if (endp paramdecls)
        nil
      (cons (,(cdr (assoc-eq 'param-declon names)) (car paramdecls) ,@extra-args-names)
            (,(cdr (assoc-eq 'param-declon-list names)) (cdr paramdecls) ,@extra-args-names)))
   '(:returns (new-paramdecls param-declon-listp)
     :measure (param-declon-list-count paramdecls))))

(define deftrans-defn-paramdeclor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'paramdeclor
   names
   bodies
   '((paramdeclor paramdeclorp))
   extra-args
   `(paramdeclor-case
      paramdeclor
      :declor (paramdeclor-declor (,(cdr (assoc-eq 'declor names)) paramdeclor.unwrap ,@extra-args-names))
      :absdeclor (paramdeclor-absdeclor (,(cdr (assoc-eq 'absdeclor names)) paramdeclor.unwrap ,@extra-args-names))
      :none (paramdeclor-none)
      :ambig (prog2$
               (raise "Misusage error: ~x0." (paramdeclor-fix paramdeclor))
               (paramdeclor-fix paramdeclor)))
   '(:returns (new-paramdeclor paramdeclorp)
     :measure (paramdeclor-count paramdeclor))))

(define deftrans-defn-tyname
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'tyname
   names
   bodies
   '((tyname tynamep))
   extra-args
   `(b* (((tyname tyname) tyname))
      (make-tyname
        :specqual (,(cdr (assoc-eq 'spec/qual-list names)) tyname.specqual ,@extra-args-names)
        :decl? (,(cdr (assoc-eq 'absdeclor-option names)) tyname.decl? ,@extra-args-names)))
   '(:returns (new-tyname tynamep)
     :measure (tyname-count tyname))))

(define deftrans-defn-strunispec
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'strunispec
   names
   bodies
   '((strunispec strunispecp))
   extra-args
   `(b* (((strunispec strunispec) strunispec))
      (make-strunispec
        :name strunispec.name
        :members (,(cdr (assoc-eq 'structdecl-list names)) strunispec.members ,@extra-args-names)))
   '(:returns (new-strunispec strunispecp)
     :measure (strunispec-count strunispec))))

(define deftrans-defn-structdecl
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'structdecl
   names
   bodies
   '((structdecl structdeclp))
   extra-args
   `(structdecl-case
      structdecl
      :member (make-structdecl-member
                :extension structdecl.extension
                :specqual (,(cdr (assoc-eq 'spec/qual-list names)) structdecl.specqual ,@extra-args-names)
                :declor (,(cdr (assoc-eq 'structdeclor-list names)) structdecl.declor ,@extra-args-names)
                :attrib structdecl.attrib)
      :statassert (structdecl-statassert
                    (,(cdr (assoc-eq 'statassert names)) structdecl.unwrap ,@extra-args-names))
      :empty (structdecl-empty))
   '(:returns (new-structdecl structdeclp)
     :measure (structdecl-count structdecl))))

(define deftrans-defn-structdecl-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'structdecl-list
   names
   bodies
   '((structdecls structdecl-listp))
   extra-args
   `(if (endp structdecls)
        nil
      (cons (,(cdr (assoc-eq 'structdecl names)) (car structdecls) ,@extra-args-names)
            (,(cdr (assoc-eq 'structdecl-list names)) (cdr structdecls) ,@extra-args-names)))
   '(:returns (new-structdecls structdecl-listp)
     :measure (structdecl-list-count structdecls))))

(define deftrans-defn-structdeclor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'structdeclor
   names
   bodies
   '((structdeclor structdeclorp))
   extra-args
   `(b* (((structdeclor structdeclor) structdeclor))
      (make-structdeclor
        :declor? (,(cdr (assoc-eq 'declor-option names)) structdeclor.declor? ,@extra-args-names)
        :expr? (,(cdr (assoc-eq 'const-expr-option names)) structdeclor.expr? ,@extra-args-names)))
   '(:returns (new-structdeclor structdeclorp)
     :measure (structdeclor-count structdeclor))))

(define deftrans-defn-structdeclor-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'structdeclor-list
   names
   bodies
   '((structdeclors structdeclor-listp))
   extra-args
   `(if (endp structdeclors)
        nil
      (cons (,(cdr (assoc-eq 'structdeclor names)) (car structdeclors) ,@extra-args-names)
            (,(cdr (assoc-eq 'structdeclor-list names)) (cdr structdeclors) ,@extra-args-names)))
   '(:returns (new-structdeclors structdeclor-listp)
     :measure (structdeclor-list-count structdeclors))))

(define deftrans-defn-enumspec
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'enumspec
   names
   bodies
   '((enumspec enumspecp))
   extra-args
   `(b* (((enumspec enumspec) enumspec))
      (make-enumspec
        :name enumspec.name
        :list (,(cdr (assoc-eq 'enumer-list names)) enumspec.list ,@extra-args-names)
        :final-comma enumspec.final-comma))
   '(:returns (new-enumspec enumspecp)
     :measure (enumspec-count enumspec))))

(define deftrans-defn-enumer
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'enumer
   names
   bodies
   '((enumer enumerp))
   extra-args
   `(b* (((enumer enumer) enumer))
      (make-enumer
        :name enumer.name
        :value (,(cdr (assoc-eq 'const-expr-option names)) enumer.value ,@extra-args-names)))
   '(:returns (new-enumer enumerp)
     :measure (enumer-count enumer))))

(define deftrans-defn-enumer-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'enumer-list
   names
   bodies
   '((enumers enumer-listp))
   extra-args
   `(if (endp enumers)
        nil
      (cons (,(cdr (assoc-eq 'enumer names)) (car enumers) ,@extra-args-names)
            (,(cdr (assoc-eq 'enumer-list names)) (cdr enumers) ,@extra-args-names)))
   '(:returns (new-enumers enumer-listp)
     :measure (enumer-list-count enumers))))

(define deftrans-defn-statassert
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'statassert
   names
   bodies
   '((statassert statassertp))
   extra-args
   `(b* (((statassert statassert) statassert))
      (make-statassert
        :test (,(cdr (assoc-eq 'const-expr names)) statassert.test ,@extra-args-names)
        :message statassert.message))
   '(:returns (new-statassert statassertp)
     :measure (statassert-count statassert))))

(define deftrans-defn-initdeclor
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'initdeclor
   names
   bodies
   '((initdeclor initdeclorp))
   extra-args
   `(b* (((initdeclor initdeclor) initdeclor))
      (make-initdeclor
        :declor (,(cdr (assoc-eq 'declor names)) initdeclor.declor ,@extra-args-names)
        :asm? initdeclor.asm?
        :attribs initdeclor.attribs
        :init? (,(cdr (assoc-eq 'initer-option names)) initdeclor.init? ,@extra-args-names)))
   '(:returns (new-initdeclor initdeclorp)
     :measure (initdeclor-count initdeclor))))

(define deftrans-defn-initdeclor-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'initdeclor-list
   names
   bodies
   '((initdeclors initdeclor-listp))
   extra-args
   `(if (endp initdeclors)
        nil
      (cons (,(cdr (assoc-eq 'initdeclor names)) (car initdeclors) ,@extra-args-names)
            (,(cdr (assoc-eq 'initdeclor-list names)) (cdr initdeclors) ,@extra-args-names)))
   '(:returns (new-initdeclors initdeclor-listp)
     :measure (initdeclor-list-count initdeclors))))

(define deftrans-defn-decl
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'decl
   names
   bodies
   '((decl declp))
   extra-args
   `(decl-case
      decl
      :decl (make-decl-decl
              :extension decl.extension
              :specs (,(cdr (assoc-eq 'decl-spec-list names)) decl.specs ,@extra-args-names)
              :init (,(cdr (assoc-eq 'initdeclor-list names)) decl.init ,@extra-args-names))
      :statassert (decl-statassert
                    (,(cdr (assoc-eq 'statassert names)) decl.unwrap ,@extra-args-names)))
   '(:returns (new-decl declp)
     :measure (decl-count decl))))

(define deftrans-defn-decl-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'decl-list
   names
   bodies
   '((decls decl-listp))
   extra-args
   `(if (endp decls)
        nil
      (cons (,(cdr (assoc-eq 'decl names)) (car decls) ,@extra-args-names)
            (,(cdr (assoc-eq 'decl-list names)) (cdr decls) ,@extra-args-names)))
   '(:returns (new-decls decl-listp)
     :measure (decl-list-count decls))))

(define deftrans-defn-label
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'label
   names
   bodies
   '((label labelp))
   extra-args
   `(label-case
      label
      :name (label-fix label)
      :casexpr (make-label-casexpr
                 :expr (,(cdr (assoc-eq 'const-expr names)) label.expr ,@extra-args-names)
                 :range? (,(cdr (assoc-eq 'const-expr-option names)) label.range? ,@extra-args-names))
      :default (label-fix label))
   '(:returns (new-label labelp)
     :measure (label-count label))))

(define deftrans-defn-stmt
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'stmt
   names
   bodies
   '((stmt stmtp))
   extra-args
   `(stmt-case
      stmt
      :labeled (make-stmt-labeled
                 :label (,(cdr (assoc-eq 'label names)) stmt.label ,@extra-args-names)
                 :stmt (,(cdr (assoc-eq 'stmt names)) stmt.stmt ,@extra-args-names))
      :compound (stmt-compound (,(cdr (assoc-eq 'block-item-list names)) stmt.items ,@extra-args-names))
      :expr (stmt-expr (,(cdr (assoc-eq 'expr-option names)) stmt.expr? ,@extra-args-names))
      :if (make-stmt-if
            :test (,(cdr (assoc-eq 'expr names)) stmt.test ,@extra-args-names)
            :then (,(cdr (assoc-eq 'stmt names)) stmt.then ,@extra-args-names))
      :ifelse (make-stmt-ifelse
                :test (,(cdr (assoc-eq 'expr names)) stmt.test ,@extra-args-names)
                :then (,(cdr (assoc-eq 'stmt names)) stmt.then ,@extra-args-names)
                :else (,(cdr (assoc-eq 'stmt names)) stmt.else ,@extra-args-names))
      :switch (make-stmt-switch
                :target (,(cdr (assoc-eq 'expr names)) stmt.target ,@extra-args-names)
                :body (,(cdr (assoc-eq 'stmt names)) stmt.body ,@extra-args-names))
      :while (make-stmt-while
               :test (,(cdr (assoc-eq 'expr names)) stmt.test ,@extra-args-names)
               :body (,(cdr (assoc-eq 'stmt names)) stmt.body ,@extra-args-names))
      :dowhile (make-stmt-dowhile
                 :body (,(cdr (assoc-eq 'stmt names)) stmt.body ,@extra-args-names)
                 :test (,(cdr (assoc-eq 'expr names)) stmt.test ,@extra-args-names))
      :for-expr (make-stmt-for-expr
                  :init (,(cdr (assoc-eq 'expr-option names)) stmt.init ,@extra-args-names)
                  :test (,(cdr (assoc-eq 'expr-option names)) stmt.test ,@extra-args-names)
                  :next (,(cdr (assoc-eq 'expr-option names)) stmt.next ,@extra-args-names)
                  :body (,(cdr (assoc-eq 'stmt names)) stmt.body ,@extra-args-names))
      :for-decl (make-stmt-for-decl
                  :init (,(cdr (assoc-eq 'decl names)) stmt.init ,@extra-args-names)
                  :test (,(cdr (assoc-eq 'expr-option names)) stmt.test ,@extra-args-names)
                  :next (,(cdr (assoc-eq 'expr-option names)) stmt.next ,@extra-args-names)
                  :body (,(cdr (assoc-eq 'stmt names)) stmt.body ,@extra-args-names))
      :for-ambig (prog2$
                  (raise "Misusage error: ~x0." (stmt-fix stmt))
                  (stmt-fix stmt))
      :goto (stmt-fix stmt)
      :continue (stmt-fix stmt)
      :break (stmt-fix stmt)
      :return (stmt-return (,(cdr (assoc-eq 'expr-option names)) stmt.expr? ,@extra-args-names))
      :asm (stmt-fix stmt))
   '(:returns (new-stmt stmtp)
     :measure (stmt-count stmt))))

(define deftrans-defn-block-item
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'block-item
   names
   bodies
   '((item block-itemp))
   extra-args
   `(block-item-case
      item
      :decl (block-item-decl (,(cdr (assoc-eq 'decl names)) item.unwrap ,@extra-args-names))
      :stmt (block-item-stmt (,(cdr (assoc-eq 'stmt names)) item.unwrap ,@extra-args-names))
      :ambig (prog2$
               (raise "Misusage error: ~x0." (block-item-fix item))
               (block-item-fix item)))
   '(:returns (new-item block-itemp)
     :measure (block-item-count item))))

(define deftrans-defn-block-item-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'block-item-list
   names
   bodies
   '((items block-item-listp))
   extra-args
   `(if (endp items)
        nil
      (cons (,(cdr (assoc-eq 'block-item names)) (car items) ,@extra-args-names)
            (,(cdr (assoc-eq 'block-item-list names)) (cdr items) ,@extra-args-names)))
   '(:returns (new-items block-item-listp)
     :measure (block-item-list-count items))))

(define deftrans-defn-fundef
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'fundef
   names
   bodies
   '((fundef fundefp))
   extra-args
   `(b* (((fundef fundef) fundef))
      (make-fundef
        :extension fundef.extension
        :spec (,(cdr (assoc-eq 'decl-spec-list names)) fundef.spec ,@extra-args-names)
        :declor (,(cdr (assoc-eq 'declor names)) fundef.declor ,@extra-args-names)
        :asm? fundef.asm?
        :attribs fundef.attribs
        :decls (,(cdr (assoc-eq 'decl-list names)) fundef.decls ,@extra-args-names)
        :body (,(cdr (assoc-eq 'stmt names)) fundef.body ,@extra-args-names)))
   '(:returns (new-fundef fundefp))))

(define deftrans-defn-extdecl
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'extdecl
   names
   bodies
   '((extdecl extdeclp))
   extra-args
   `(extdecl-case
      extdecl
      :fundef (extdecl-fundef (,(cdr (assoc-eq 'fundef names)) extdecl.unwrap ,@extra-args-names))
      :decl (extdecl-decl (,(cdr (assoc-eq 'decl names)) extdecl.unwrap ,@extra-args-names))
      :empty (extdecl-empty)
      :asm (extdecl-fix extdecl))
   '(:returns (new-extdecl extdeclp))))

(define deftrans-defn-extdecl-list
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'extdecl-list
   names
   bodies
   '((extdecls extdecl-listp))
   extra-args
   `(if (endp extdecls)
        nil
      (cons (,(cdr (assoc-eq 'extdecl names)) (car extdecls) ,@extra-args-names)
            (,(cdr (assoc-eq 'extdecl-list names)) (cdr extdecls) ,@extra-args-names)))
   '(:returns (new-extdecls extdecl-listp)
     :measure (acl2-count extdecls)
     :hints (("Goal" :in-theory nil)))))

(define deftrans-defn-transunit
  ((names alistp)
   (bodies alistp)
   (extra-args true-listp)
   (extra-args-names true-listp))
  (deftrans-defn
   'transunit
   names
   bodies
   '((tunit transunitp))
   extra-args
   `(b* (((transunit tunit) tunit))
      (make-transunit :decls (,(cdr (assoc-eq 'extdecl-list names)) tunit.decls ,@extra-args-names)
                      :info tunit.info))
   '(:returns (new-tunit transunitp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftrans-cases
  ()
  :returns (cases symbol-listp)
  '(ident
    ident-list
    const
    expr
    expr-list
    expr-option
    const-expr
    const-expr-option
    genassoc
    genassoc-list
    member-designor
    type-spec
    spec/qual
    spec/qual-list
    align-spec
    decl-spec
    decl-spec-list
    initer
    initer-option
    desiniter
    desiniter-list
    designor
    designor-list
    declor
    declor-option
    dirdeclor
    absdeclor
    absdeclor
    absdeclor-option
    dirabsdeclor
    dirabsdeclor-option
    param-declon
    param-declon-list
    paramdeclor
    tyname
    strunispec
    structdecl
    structdecl-list
    structdeclor
    structdeclor-list
    enumspec
    enumer
    enumer-list
    statassert
    initdeclor
    initdeclor-list
    decl
    decl-list
    label
    stmt
    block-item
    block-item-list
    fundef
    extdecl
    extdecl-list
    transunit
    filepath-transunit-map
    transunit-ensemble)
  ///
  (in-theory (disable (:e deftrans-cases))))

(define deftrans-mk-names
  ((name symbolp))
  :returns (names symbol-alistp)
  (deftrans-mk-names0 name (deftrans-cases))
  :prepwork
  ((define deftrans-mk-names0
     ((name symbolp)
      (cases symbol-listp))
     :returns
     (names symbol-alistp
            :hints (("Goal" :in-theory (enable symbol-alistp)
                            :induct t)))
     (if (endp cases)
         nil
       (cons (cons (mbe :logic (and (symbolp (first cases))
                                    (first cases))
                        :exec (first cases))
                   (acl2::packn-pos (list name '- (first cases)) name))
             (deftrans-mk-names0 name (rest cases))))
     :guard-hints (("Goal" :in-theory (enable atom-listp))))))

(defrulel assoc-equal-of-deftrans-mk-names-under-iff
  (iff (assoc-equal x (deftrans-mk-names name))
       (member-equal x (deftrans-cases)))
  :enable (deftrans-mk-names)
  :prep-lemmas
  ((defrule assoc-equal-of-deftrans-mk-names0-under-iff-when-symbol-listp
     (implies (symbol-listp cases)
              (iff (assoc-equal x (deftrans-mk-names0 name cases))
                   (member-equal x cases)))
     :enable (deftrans-mk-names0
               assoc-equal
               member-equal)
     :induct t)))

(define deftrans-core
  ((name symbolp)
   (extra-args true-listp) ;; list of symbols or define-style guarded args
   (bodies alistp))
  (b* ((names (deftrans-mk-names name))
       (name-exprs/decls/stmts (acl2::packn-pos (list name '-exprs/decls/stmts) name))
       (extra-args-names (deftrans-get-args extra-args)))
    `(progn
       ,(deftrans-defn-ident      names bodies extra-args)
       ,(deftrans-defn-ident-list names bodies extra-args extra-args-names)
       ,(deftrans-defn-const      names bodies extra-args)
       (defines ,name-exprs/decls/stmts
         ,(deftrans-defn-expr                names bodies extra-args extra-args-names)
         ,(deftrans-defn-expr-list           names bodies extra-args extra-args-names)
         ,(deftrans-defn-expr-option         names bodies extra-args extra-args-names)
         ,(deftrans-defn-const-expr          names bodies extra-args extra-args-names)
         ,(deftrans-defn-const-expr-option   names bodies extra-args extra-args-names)
         ,(deftrans-defn-genassoc            names bodies extra-args extra-args-names)
         ,(deftrans-defn-genassoc-list       names bodies extra-args extra-args-names)
         ,(deftrans-defn-member-designor     names bodies extra-args extra-args-names)
         ,(deftrans-defn-type-spec           names bodies extra-args extra-args-names)
         ,(deftrans-defn-spec/qual           names bodies extra-args extra-args-names)
         ,(deftrans-defn-spec/qual-list      names bodies extra-args extra-args-names)
         ,(deftrans-defn-align-spec          names bodies extra-args extra-args-names)
         ,(deftrans-defn-decl-spec           names bodies extra-args extra-args-names)
         ,(deftrans-defn-decl-spec-list      names bodies extra-args extra-args-names)
         ,(deftrans-defn-initer              names bodies extra-args extra-args-names)
         ,(deftrans-defn-initer-option       names bodies extra-args extra-args-names)
         ,(deftrans-defn-desiniter           names bodies extra-args extra-args-names)
         ,(deftrans-defn-desiniter-list      names bodies extra-args extra-args-names)
         ,(deftrans-defn-designor            names bodies extra-args extra-args-names)
         ,(deftrans-defn-designor-list       names bodies extra-args extra-args-names)
         ,(deftrans-defn-declor              names bodies extra-args extra-args-names)
         ,(deftrans-defn-declor-option       names bodies extra-args extra-args-names)
         ,(deftrans-defn-dirdeclor           names bodies extra-args extra-args-names)
         ,(deftrans-defn-absdeclor           names bodies extra-args extra-args-names)
         ,(deftrans-defn-absdeclor-option    names bodies extra-args extra-args-names)
         ,(deftrans-defn-dirabsdeclor        names bodies extra-args extra-args-names)
         ,(deftrans-defn-dirabsdeclor-option names bodies extra-args extra-args-names)
         ,(deftrans-defn-param-declon        names bodies extra-args extra-args-names)
         ,(deftrans-defn-param-declon-list   names bodies extra-args extra-args-names)
         ,(deftrans-defn-paramdeclor         names bodies extra-args extra-args-names)
         ,(deftrans-defn-tyname              names bodies extra-args extra-args-names)
         ,(deftrans-defn-strunispec          names bodies extra-args extra-args-names)
         ,(deftrans-defn-structdecl          names bodies extra-args extra-args-names)
         ,(deftrans-defn-structdecl-list     names bodies extra-args extra-args-names)
         ,(deftrans-defn-structdeclor        names bodies extra-args extra-args-names)
         ,(deftrans-defn-structdeclor-list   names bodies extra-args extra-args-names)
         ,(deftrans-defn-enumspec            names bodies extra-args extra-args-names)
         ,(deftrans-defn-enumer              names bodies extra-args extra-args-names)
         ,(deftrans-defn-enumer-list         names bodies extra-args extra-args-names)
         ,(deftrans-defn-statassert          names bodies extra-args extra-args-names)
         ,(deftrans-defn-initdeclor          names bodies extra-args extra-args-names)
         ,(deftrans-defn-initdeclor-list     names bodies extra-args extra-args-names)
         ,(deftrans-defn-decl                names bodies extra-args extra-args-names)
         ,(deftrans-defn-decl-list           names bodies extra-args extra-args-names)
         ,(deftrans-defn-label               names bodies extra-args extra-args-names)
         ,(deftrans-defn-stmt                names bodies extra-args extra-args-names)
         ,(deftrans-defn-block-item          names bodies extra-args extra-args-names)
         ,(deftrans-defn-block-item-list     names bodies extra-args extra-args-names)
         :hints (("Goal" :in-theory '(deftrans-measure-theory)))
         :verify-guards nil
         ///
         (verify-guards ,(cdr (assoc-eq 'expr names))))
       ,(deftrans-defn-fundef       names bodies extra-args extra-args-names)
       ,(deftrans-defn-extdecl      names bodies extra-args extra-args-names)
       ,(deftrans-defn-extdecl-list names bodies extra-args extra-args-names)
       ,(deftrans-defn-transunit    names bodies extra-args extra-args-names)
       (define ,(cdr (assoc-eq 'filepath-transunit-map names))
         ((map filepath-transunit-mapp)
          ,@extra-args)
         :returns (new-map filepath-transunit-mapp
                           :hyp (filepath-transunit-mapp map))
         (b* (((when (omap::emptyp map)) nil)
              ((mv path tunit) (omap::head map))
              (new-tunit (,(cdr (assoc-eq 'transunit names)) tunit ,@extra-args-names))
              (new-map (,(cdr (assoc-eq 'filepath-transunit-map names)) (omap::tail map) ,@extra-args-names)))
           (omap::update path new-tunit new-map))
         :verify-guards :after-returns)
       (define ,(cdr (assoc-eq 'transunit-ensemble names))
         ((tunits transunit-ensemblep)
          ,@extra-args)
         :returns (new-tunits transunit-ensemblep)
         :short "Transform a translation unit ensemble."
         (b* (((transunit-ensemble tunits) tunits))
           (transunit-ensemble (,(cdr (assoc-eq 'filepath-transunit-map names)) tunits.unwrap ,@extra-args-names))))))
  :guard-hints (("Goal" :in-theory (enable atom-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deftrans-parse-keywords
  ((list true-listp))
  :returns (mv (extra-args true-listp)
               with-output-off
               (bodies alistp))
  (b* ((pairs (take-pairs list))
       (extra-args
         (b* ((lookup (assoc-eq :extra-args pairs)))
           (if (and lookup (true-listp (cdr lookup)))
               (cdr lookup)
             nil)))
       (with-output-off
         (b* ((lookup (assoc-eq :with-output-off pairs)))
           (if lookup
               (cdr lookup)
             '(:other-than summary error))))
       (bodies
         (remove-assoc-eq :extra-args
                          (remove-assoc-eq :with-output-off
                                           pairs))))
    (mv extra-args with-output-off bodies)))

(define deftrans-macro
  ((name symbolp)
   (rest true-listp))
  (b* (((mv extra-args with-output-off bodies)
        (deftrans-parse-keywords rest)))
    `(with-output
       :off ,with-output-off
       :gag-mode t
       ,(deftrans-core name extra-args bodies))))

(defmacro deftrans
  (name
   &rest rest)
  (deftrans-macro name rest))
