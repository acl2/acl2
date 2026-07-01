; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "kestrel/abstract-domains/many-valued-logics/3vl" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "kestrel/utilities/ordinals" :dir :system)
(include-book "std/system/constant-value" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "kestrel/fty/msg" :dir :system)
(include-book "kestrel/fty/msg-list" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")
(include-book "../syntax/purity")
(include-book "../syntax/unambiguity")
(include-book "../syntax/validation-annotations")
(include-book "../syntax/validator")
(include-book "utilities/context-msg")
(include-book "utilities/fresh-ident")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* c$::abstract-syntax-annop-rules)))
(local (in-theory (enable* c$::abstract-syntax-unambp-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation
  struct-type-split
  :default-parent t
  :additional
  ((xdoc::h3
    "Terminology"
    (xdoc::p
     "Various functions are prefixed with ``STS.''
      This is short for ``struct-type-split.''")
    (xdoc::p
     "When we split something, we refer to the ``left'' and ``right'' splits.
      The ``left struct type'' is the modification of the original type
      with the right members removed.
      The name is <emph>not</emph> changed.
      The ``right struct type'' is a new struct type
      with just the right members.
      A ``left object'' is an object with the left struct type
      (possibly with some level of pointers).
      A ``right object'' is an object with the right struct type
      (again, possible with some level of pointers)."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

(define stmts-to-compound
  ((left-stmt stmtp)
   (right-stmt stmtp))
  :returns (stmt stmtp)
  :short "Join two statements into a compound statement."
  :long
  (xdoc::topstring-p
   "This is used to absorb a statement split
    in positions which admit only a single statement,
    such as the branches of an @('if') statement.")
  (c$::make-stmt-compound
    :stmt (c$::make-comp-stmt
            :labels nil
            :items (list (c$::make-block-item-stmt :stmt left-stmt)
                         (c$::make-block-item-stmt :stmt right-stmt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap uid-ident-map
  :key-type c$::uid
  :val-type ident
  :pred uid-ident-mapp)

(fty::defprod sts-split-state
  :short "Collection of data used by @(see sts-split)."
  :long
  (xdoc::topstring-p
   "The @('right-set'), @('right-name'), @('dialect'), and @('ienv') fields
    are expected to remain constant.
    The @('struct-uid') field is constant
    within a single translation unit,
    but is updated for each translation unit
    (see @(tsee sts-split-trans-units)),
    since compatible struct types in different translation units
    have different unique identifiers.
    The @('right-name') field is the tag of the right struct type,
    which is assumed to be globally unique.
    The @('blacklist'), @('ident-map'), and @('warnings') fields
    accumulate.
    The @('warnings') field collects warning messages,
    in reverse chronological order;
    they are printed at the end of the transformation
    (see @(tsee sts-print-warnings)).
    The @('filepath') field is the file path
    of the translation unit currently being transformed;
    it is updated for each translation unit
    (see @(tsee sts-split-trans-units)),
    and is used only to provide context in error messages
    (see @(tsee sts-error-in-translation-unit)).")
  ((struct-uid c$::uid)
   (right-set ident-set)
   (right-name ident)
   (dialect c::dialect)
   (ienv c$::ienv)
   (blacklist ident-set)
   (ident-map uid-ident-map)
   (warnings acl2::msg-list)
   (filepath c$::filepath))
  :pred sts-split-statep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-split-state-add-warning
  ((warning msgp)
   (st sts-split-statep))
  :returns (st$ sts-split-statep)
  :short "Add a warning message to the state."
  (change-sts-split-state
    st
    :warnings (cons (acl2::msg-fix warning)
                    (sts-split-state->warnings st))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-error-in-translation-unit
  ((msg maybe-msgp)
   (st sts-split-statep))
  :returns (msg$ msgp)
  :short "Augment an error message with the file path
          of the translation unit currently being transformed."
  :long
  (xdoc::topstring-p
   "The file path is taken from the @('filepath') field
    of the @(tsee sts-split-state),
    which is set for each translation unit
    in @(tsee sts-split-trans-units).")
  (msg$ "In translation unit ~x0:~%~@1"
        (c$::filepath->string (sts-split-state->filepath st))
        msg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-splittablep
  ((type c$::typep)
   (struct-uid c$::uidp))
  :returns (splittable acl2::3p)
  :short "Recognize a splittable type."
  :long
  (xdoc::topstring
   (xdoc::p
    "A ``splittable'' type,
     for the purpose of the @(see struct-type-split) transformation,
     is a struct type with the expected UID,
     or a pointer to a splittable type.")
   (xdoc::p
    "Since types may be partially or completely unknown,
     we may not be able to precisely resolve whether a type is splittable.
     Therefore, this function returns a @(see acl2::3vl) instead of a boolean.
     In addition to the boolean values,
     a @(see acl2::3vl) value may also be @(':unknown')."))
  (type-case
    type
    :unknown :unknown
    :unknown-builtin nil
    :unknown-scalar :unknown
    :unknown-arithmetic nil
    :struct (c$::uid-equal struct-uid type.uid)
    :pointer (sts-splittablep type.to struct-uid)
    :otherwise nil)
  :measure (c$::type-count type))

(defrule sts-splittablep-type-prescription
  (acl2::3p (sts-splittablep type struct-uid))
  :rule-classes
  ((:type-prescription :typed-term (sts-splittablep type struct-uid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type/type-list-struct-occurs-unsupported-p
  :short "Check whether the split struct type occurs
          in an unsupported context within types."
  (define type-struct-occurs-unsupported-p
    ((type c$::typep)
     (struct-uid c$::uidp))
    :returns (occurs acl2::3p)
    :parents (type/type-list-struct-occurs-unsupported-p)
    :short "Check whether the split struct type occurs in a type
            in an unsupported context."
    :long
    (xdoc::topstring-p
     "We check for occurrences of the split struct type at any depth.
      All occurrences are unsupported,
      except for function parameters of splittable type
      (see @(tsee type-param-list-struct-occurs-unsupported-p)).
      Note that a splittable type
      contains an occurrence of the split struct type by definition,
      so this function reports it as unsupported;
      an occurrence is only really unsupported
      in a type which is not itself splittable.
      Callers are expected to check splittability first
      (see @(tsee sts-check-type)).
      The result is @(':unknown') when it cannot be determined,
      due to unknown types.
      Tagged struct and union types other than the split struct type itself
      are not followed,
      since their members are checked separately,
      via the type completions
      (see @(tsee sts-check-completions)).
      Note that the unique identifier comparison
      applies only to struct types;
      union types cannot be the split struct type,
      but their untagged members are still checked.")
    (type-case
      type
      :unknown :unknown
      :unknown-builtin nil
      :unknown-scalar :unknown
      :unknown-arithmetic nil
      :struct (if (c$::uid-equal struct-uid type.uid)
                  t
                (c$::type-struni-tag/members-case
                  type.tag/members
                  :tagged nil
                  :untagged (type-member-list-struct-occurs-unsupported-p
                              type.tag/members.members
                              struct-uid)))
      :union (c$::type-struni-tag/members-case
               type.tag/members
               :tagged nil
               :untagged (type-member-list-struct-occurs-unsupported-p
                           type.tag/members.members
                           struct-uid))
      :array (type-struct-occurs-unsupported-p type.of struct-uid)
      :pointer (type-struct-occurs-unsupported-p type.to struct-uid)
      :function (acl2::3or
                  (type-struct-occurs-unsupported-p type.ret struct-uid)
                  (type-params-struct-occurs-unsupported-p type.params struct-uid))
      :otherwise nil)
    :measure (c$::type-count type))

  (define type-params-struct-occurs-unsupported-p
    ((params c$::type-params-p)
     (struct-uid c$::uidp))
    :returns (occurs acl2::3p)
    :parents (type/type-list-struct-occurs-unsupported-p)
    :short "Check whether the split struct type occurs
            in function type parameters
            in an unsupported context."
    (c$::type-params-case
      params
      :prototype (type-param-list-struct-occurs-unsupported-p params.params
                                                    struct-uid)
      :old-style (type-param-list-struct-occurs-unsupported-p params.params
                                                    struct-uid)
      :unspecified :unknown)
    :measure (c$::type-params-count params))

  (define type-param-list-struct-occurs-unsupported-p
    ((types c$::type-listp)
     (struct-uid c$::uidp))
    :returns (occurs acl2::3p)
    :parents (type/type-list-struct-occurs-unsupported-p)
    :short "Check whether the split struct type occurs
            in any function parameter type
            in an unsupported context."
    :long
    (xdoc::topstring-p
     "Parameters of splittable type
      (i.e. the split struct type, possibly behind pointers)
      are not unsupported occurrences,
      because such parameters are supported:
      they are split in place,
      in function definitions, function declarations, and call sites.")
    (if (endp types)
        nil
      (acl2::3or
        (b* ((type (first types)))
          (if (eq (sts-splittablep type struct-uid) t)
              nil
            (type-struct-occurs-unsupported-p type struct-uid)))
        (type-param-list-struct-occurs-unsupported-p (rest types) struct-uid)))
    :measure (c$::type-list-count types))

  (define type-member-list-struct-occurs-unsupported-p
    ((members c$::type-struni-member-listp)
     (struct-uid c$::uidp))
    :returns (occurs acl2::3p)
    :parents (type/type-list-struct-occurs-unsupported-p)
    :short "Check whether the split struct type occurs
            in any struct/union member type
            in an unsupported context."
    (if (endp members)
        nil
      (acl2::3or
        (type-struct-occurs-unsupported-p
          (c$::type-struni-member->type (first members))
          struct-uid)
        (type-member-list-struct-occurs-unsupported-p (rest members) struct-uid)))
    :measure (c$::type-struni-member-list-count members))

  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-check-type
  ((type c$::typep)
   (st sts-split-statep))
  :returns (mv (er? maybe-msgp)
               (splitp booleanp))
  :short "Check that a type is consistent with the split,
          and determine whether it is subject to the split."
  :long
  (xdoc::topstring-p
   "The type must either be splittable
    (see @(tsee sts-splittablep)),
    in which case @('splitp') is @('t'),
    or the split struct type must not occur in it
    in an unsupported context,
    in which case @('splitp') is @('nil').
    Any other type
    (e.g. an array of the split struct type,
    or a function type whose return type
    is the split struct type)
    is rejected, since the transformation cannot split it.
    Function parameters of splittable type are an exception:
    they are supported, being split in place
    (see @(tsee type-param-list-struct-occurs-unsupported-p)).
    Unknown types are also rejected,
    since we cannot determine whether
    the split struct type occurs in them.")
  (b* (((reterr) nil)
       (struct-uid (sts-split-state->struct-uid st))
       (dialect (sts-split-state->dialect st))
       (ienv (sts-split-state->ienv st))
       (splittablep (sts-splittablep type struct-uid))
       ((when (eq splittablep :unknown))
        (retmsg$ "The type is unknown, ~
                  so it cannot be determined whether it is splittable.~%~@0"
                 (context-msg-type type ienv dialect)))
       ((when (eq splittablep t))
        (retok t))
       (occurs (type-struct-occurs-unsupported-p type struct-uid))
       ((when (eq occurs :unknown))
        (retmsg$ "It cannot be determined whether ~
                  the split struct type occurs in the type.~%~@0"
                 (context-msg-type type ienv dialect)))
       ((when (eq occurs t))
        (retmsg$ "The split struct type may appear in a type ~
                  only as the struct type itself, ~
                  possibly behind pointers, ~
                  but it occurs in an unsupported context.~%~@0"
                 (context-msg-type type ienv dialect))))
    (retok nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-check-completions
  ((completions c$::type-completions-p)
   (struct-uid c$::uidp))
  :returns (er? maybe-msgp)
  :short "Check that the split struct type does not appear in
          the members of any struct or union type."
  :long
  (xdoc::topstring-p
   "This includes the members of the split struct type itself,
    so self-referential split struct types are rejected.")
  (b* (((when (endp completions))
        nil)
       (entry (first completions))
       ((unless (consp entry))
        (sts-check-completions (rest completions) struct-uid))
       (members (c$::type-struni-member-list-fix (cdr entry)))
       (occurs (type-member-list-struct-occurs-unsupported-p members
                                                              struct-uid))
       ((when (eq occurs :unknown))
        (msg$ "It cannot be determined whether the split struct type ~
               occurs in the members of all struct and union types."))
       ((when (eq occurs t))
        (msg$ "The split struct type may not appear in the members ~
               of any struct or union type ~
               (including the split struct type itself).")))
    (sts-check-completions (rest completions) struct-uid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define desiniter-sts-rightp
  ((desiniter desiniterp)
   (st sts-split-statep))
  :guard (desiniter-annop desiniter)
  :returns (mv (er? maybe-msgp)
               (rightp booleanp))
  :short "Determine whether a designated initializer
          is routed to the right structure type."
  :long
  (xdoc::topstring-p
   "The first designator determines the designated member,
    falling back to the designators recorded by the validator
    when there is no syntactic designation.
    The initializer is routed right
    when the member is in the right member set.")
  (b* (((reterr) nil)
       ((desiniter desiniter) desiniter)
       ((c$::desiniter-vinfo info) desiniter.info)
       (designors (or desiniter.designors info.designors))
       ((unless (and (consp designors)
                     (designor-case (car designors) :dot)))
        (retmsg$ "Could not determine the member designated by an ~
                  initializer of a split structure type.~%~@0"
                 (context-msg-desiniter desiniter
                                        (sts-split-state->dialect st))))
       (name (c$::designor-dot->name (car designors))))
    (retok (and (in name (sts-split-state->right-set st)) t))))

(define struct-declor-sts-rightp
  ((struct-declor struct-declorp)
   (st sts-split-statep))
  :returns (rightp booleanp)
  :short "Determine whether a struct declarator
          is routed to the right structure type."
  :long
  (xdoc::topstring-p
   "The struct declarator is routed right
    when the member it declares is in the right member set.
    Unnamed members (e.g. anonymous bit-fields)
    cannot be listed in the right member set,
    so they always stay in the left struct type.")
  (b* (((struct-declor struct-declor) struct-declor)
       ((unless struct-declor.declor?)
        nil)
       (name (declor->ident struct-declor.declor?)))
    (and (in name (sts-split-state->right-set st)) t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define attrib-sts-split
  ((attrib c$::attribp)
   (st sts-split-statep))
  :guard (c$::attrib-annop attrib)
  :returns (mv (er? maybe-msgp)
               (attrib$ c$::attribp)
               (st$ sts-split-statep))
  :parents (sts-split)
  :short "Transform a GCC attribute."
  :long
  (xdoc::topstring
   "Attribute parameters are not validated,
    so we cannot transform them as we do other items in the clique
    (and it is not clear that we should).
    For now, we leave them as is and log the decision as a warning.")
  (b* ((st (sts-split-state-fix st))
       ((reterr) (c$::attrib-fix attrib) st))
    (c$::attrib-case
      attrib
      :name-only (retok (c$::attrib-fix attrib) st)
      :name-params
      (b* ((st (sts-split-state-add-warning
                 (msg$ "Not transforming attribute parameter.~%~@0"
                       (context-msg-attrib attrib
                                           (sts-split-state->dialect st)))
                 st)))
        (retok (c$::attrib-fix attrib) st)))))

(defines sts-split
  :short "The core splitting phase of STS."

  (define expr-sts-split
    ((expr exprp)
     (st sts-split-statep))
    :guard (expr-annop expr)
    :returns (mv (er? maybe-msgp)
                 (left-expr exprp)
                 (right-expr? expr-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "An expression splits iff it has splittable type.")
     (xdoc::p
      "If the expression is split,
       any effects of the two expressions are <emph>disjoint</emph>
       (and may therefore be reordered).
       If the expression is not split,
       the transformed expression is returned as the @('left-expr').")
     (xdoc::p
      "Splitting an lvalue may produce non-lvalues.
       In particular, the @(':member') and @(':memberp') cases
       may introduce a comma to accommodate effects.
       Therefore, in places where we need an lvalue,
       we explicitly check that the split expressions are still lvalues.
       In C17, lvalues are required as operands
       to certain unary and binary operators,
       which we check accordingly.")
     (xdoc::p
      "Note that these lvalue checks are not yet sufficient,
       because @(tsee c$::expr-syntactic-lvalue-p)
       overapproximates lvalues.
       For instance, a generic selection is considered an lvalue
       when any of its possible result expressions is an lvalue.
       The transformation might rewrite the selected result expression
       such that it is no longer an lvalue
       (e.g. by introducing a comma in a @(':member') case),
       while the overapproximation still judges
       the generic selection to be an lvalue
       due to another result expression.
       In such a case, the transformation would produce invalid code
       without reporting an error.
       Similarly, we do not check that the operand
       of the unary address operator is still well-formed
       (it must be a function designator,
       a dereference or array subscript expression,
       or an lvalue)."))
    (b* ((st (sts-split-state-fix st))
         ((reterr) (expr-fix expr) nil st))
      (expr-case
        expr
        :ident
        (b* (((sts-split-state st) st)
             ((var-vinfo info) expr.info)
             (right-ident? (omap::assoc info.uid st.ident-map)))
          (retok (expr-fix expr)
                 (if right-ident?
                     (make-expr-ident :ident (cdr right-ident?))
                   nil)
                 st))
        :const
        (retok (expr-fix expr) nil st)
        :string
        (retok (expr-fix expr) nil st)
        :paren
        (b* (((erp left right? st)
              (expr-sts-split expr.inner st)))
          (retok (c$::make-expr-paren :inner left)
                 (if right?
                     (c$::make-expr-paren :inner right?)
                   nil)
                 st))
        :gensel
        (b* (((erp left-expr right-expr? st)
              (expr-sts-split expr.control st))
             ((when right-expr?)
              (retmsg$ "Splits are not supported in generic selections.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st))))
             ((erp assocs st)
              (genassoc-list-sts-split expr.assocs st)))
          (retok (make-expr-gensel :control left-expr
                                   :assocs assocs)
                 nil
                 st))
        :arrsub
        (b* (((erp left-arg1 right-arg1? st)
              (expr-sts-split expr.arg1 st))
             ((when right-arg1?)
              (retmsg$ "Splits are not supported in the first subexpression ~
                        of an array subscript expression.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st))))
             ((erp left-arg2 right-arg2? st)
              (expr-sts-split expr.arg2 st)))
          (retok (make-expr-arrsub :arg1 left-arg1
                                   :arg2 left-arg2)
                 (if right-arg2?
                     (make-expr-arrsub :arg1 left-arg1
                                       :arg2 right-arg2?)
                   nil)
                 st))
        :funcall
        (b* (((erp left-fun right-fun? st)
              (expr-sts-split expr.fun st))
             ((when right-fun?)
              (retmsg$ "Splits are not supported in the first subexpression ~
                        of a function call.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st))))
             ((erp args st)
              (expr-list-sts-split expr.args st)))
          (retok (make-expr-funcall :fun left-fun
                                    :args args)
                 nil
                 st))
        :member
        (b* (((erp left-arg right-arg? st)
              (expr-sts-split expr.arg st))
             ((unless right-arg?)
              (retok (make-expr-member :arg left-arg
                                       :name expr.name)
                     nil
                     st))
             (rightp (in expr.name (sts-split-state->right-set st)))
             (expr (if rightp
                     (b* ((member-expr (make-expr-member :arg right-arg?
                                                         :name expr.name)))
                       (if (expr-purep left-arg)
                           member-expr
                         (make-expr-comma :first left-arg
                                          :next member-expr)))
                   (b* ((member-expr (make-expr-member :arg left-arg
                                                       :name expr.name)))
                     (if (expr-purep right-arg?)
                         member-expr
                       (make-expr-comma :first right-arg?
                                        :next member-expr))))))
          (retok expr nil st))
        :memberp
        (b* (((erp left-arg right-arg? st)
              (expr-sts-split expr.arg st))
             ((unless right-arg?)
              (retok (make-expr-memberp :arg left-arg
                                        :name expr.name)
                     nil
                     st))
             (rightp (in expr.name (sts-split-state->right-set st)))
             (expr (if rightp
                       (b* ((memberp-expr
                              (make-expr-memberp :arg right-arg?
                                                 :name expr.name)))
                         (if (expr-purep left-arg)
                             memberp-expr
                           (make-expr-comma :first left-arg
                                            :next memberp-expr)))
                     (b* ((memberp-expr (make-expr-memberp :arg left-arg
                                                           :name expr.name)))
                       (if (expr-purep right-arg?)
                           memberp-expr
                         (make-expr-comma :first right-arg?
                                          :next memberp-expr))))))
          (retok expr nil st))
        :complit
        (b* (((erp splitp left-tyname right-tyname st)
              (tyname-sts-split expr.type st))
             ((erp left-elems right-elems st)
              (desiniter-list-sts-split splitp expr.elems st)))
          (retok (make-expr-complit :type left-tyname
                                    :elems left-elems
                                    :final-comma expr.final-comma)
                 (if splitp
                     (make-expr-complit :type right-tyname
                                        :elems right-elems
                                        :final-comma expr.final-comma)
                   nil)
                 st))
        :unary
        (b* (((erp left-arg right-arg? st)
              (expr-sts-split expr.arg st))
             (left-expr (make-expr-unary :op expr.op
                                         :arg left-arg))
             ((when (and (c$::unop-requires-lvalue-p expr.op)
                         (not (c$::expr-syntactic-lvalue-p left-arg))))
              (retmsg$ "Split expression is no longer an lvalue.~%~@0~%~@1"
                       (context-msg-expr expr
                                         (sts-split-state->dialect st)
                                         :prefix "Original")
                       (context-msg-expr left-expr
                                         (sts-split-state->dialect st)
                                         :prefix "Split")))
             ((unless right-arg?)
              (retok left-expr nil st))
             ((unless (unop-case expr.op '(:address :indir)))
              (retmsg$ "Split is not supported for this unary operator.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st))))
             (right-expr (make-expr-unary :op expr.op
                                          :arg right-arg?))
             ((when (and (c$::unop-requires-lvalue-p expr.op)
                         (not (c$::expr-syntactic-lvalue-p right-arg?))))
              (retmsg$ "Split expression is no longer an lvalue.~%~@0~%~@1"
                       (context-msg-expr expr
                                         (sts-split-state->dialect st)
                                         :prefix "Original")
                       (context-msg-expr right-expr
                                         (sts-split-state->dialect st)
                                         :prefix "Split"))))
          (retok left-expr right-expr st))
        :label-addr
        (retok (expr-fix expr) nil st)
        :sizeof
        (b* (((erp splitp left-type ?right-type st)
              (tyname-sts-split expr.type st))
             ((when splitp)
              (retmsg$ "Splits are not supported in the type name ~
                        of a sizeof expression.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st)))))
          (retok (c$::make-expr-sizeof :type left-type)
                 nil
                 st))
        :alignof
        (b* (((erp splitp left-type ?right-type st)
              (tyname-sts-split expr.type st))
             ((when splitp)
              (retmsg$ "Splits are not supported in the type name ~
                        of an alignof expression.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st)))))
          (retok (make-expr-alignof :type left-type
                                    :uscores expr.uscores)
                 nil
                 st))
        :cast
        (b* (((erp splitp left-type right-type st)
              (tyname-sts-split expr.type st))
             ((erp left-arg right-arg? st)
              (expr-sts-split expr.arg st))
             ((when (xor splitp right-arg?))
              (retmsg$ "INTERNAL ERROR. ~
                        One of (but not both) ~
                        the type name and subexpression ~
                        of a cast was split.~%~@0"
                       (context-msg-expr expr
                                         (sts-split-state->dialect st)))))
          (retok (make-expr-cast :type left-type
                                 :arg left-arg)
                 (if splitp
                     (make-expr-cast :type right-type
                                     :arg right-arg?)
                   nil)
                 st))
        :binary
        (b* (((erp left-arg1 right-arg1? st)
              (expr-sts-split expr.arg1 st))
             ((erp left-arg2 right-arg2? st)
              (expr-sts-split expr.arg2 st))
             (left-expr (make-expr-binary :op expr.op
                                          :arg1 left-arg1
                                          :arg2 left-arg2))
             ((when (and (c$::binop-arg1-requires-lvalue-p expr.op)
                         (not (c$::expr-syntactic-lvalue-p left-arg1))))
              (retmsg$ "Split expression is no longer an lvalue.~%~@0~%~@1"
                       (context-msg-expr expr
                                         (sts-split-state->dialect st)
                                         :prefix "Original")
                       (context-msg-expr left-expr
                                         (sts-split-state->dialect st)
                                         :prefix "Split")))
             ((unless (or right-arg1? right-arg2?))
              (retok left-expr nil st))
             ((unless (binop-case expr.op :asg))
              (retmsg$ "Split is not supported for this binary operator.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st))))
             ((unless (and right-arg1? right-arg2?))
              (retmsg$ "INTERNAL ERROR. ~
                        One of (but not both) ~
                        the two subexpressions ~
                        of a simple assignment was split.~%~@0"
                       (context-msg-expr expr
                                         (sts-split-state->dialect st))))
             (right-expr (make-expr-binary :op expr.op
                                           :arg1 right-arg1?
                                           :arg2 right-arg2?))
             ((unless (c$::expr-syntactic-lvalue-p right-arg1?))
              (retmsg$ "Split expression is no longer an lvalue.~%~@0~%~@1"
                       (context-msg-expr expr
                                         (sts-split-state->dialect st)
                                         :prefix "Original")
                       (context-msg-expr expr
                                         (sts-split-state->dialect st)
                                         :prefix "Split"))))
          (retok left-expr right-expr st))
        :cond
        (b* (((erp left-test right-test? st)
              (expr-sts-split expr.test st))
             ((when right-test?)
              (retmsg$ "Split is not supported in the test ~
                        of a ternary operator.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st))))
             ((erp left-then right-then? st)
              (expr-option-sts-split expr.then st))
             ((erp left-else right-else? st)
              (expr-sts-split expr.else st))
             (left-expr (make-expr-cond :test left-test
                                        :then left-then
                                        :else left-else))
             ((unless (or right-then? right-else?))
              (retok left-expr nil st))
             ((unless right-else?)
              (retmsg$ "INTERNAL ERROR. ~
                        One of (but not both) ~
                        the two subexpressions ~
                        of a ternary expression was split.~%~@0"
                       (context-msg-expr expr
                                         (sts-split-state->dialect st))))
             ((unless (expr-purep left-test))
              (retmsg$ "Cannot split ternary expression with impure test.~%~@0"
                       (context-msg-expr expr
                                         (sts-split-state->dialect st)))))
          (retok left-expr
                 (make-expr-cond :test left-test
                                 :then right-then?
                                 :else right-else?)
                 st))
        :comma
        (b* (((erp left-first right-first? st)
              (expr-sts-split expr.first st))
             ((erp left-next right-next? st)
              (expr-sts-split expr.next st))
             ((when right-next?)
              (retmsg$ "Split is not supported in the second operand ~
                        of a comma operator.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st)))))
          (retok (if right-first?
                     (make-expr-comma
                       :first (make-expr-comma :first left-first
                                               :next right-first?)
                       :next left-next)
                   (make-expr-comma :first left-first
                                    :next left-next))
                 nil
                 st))
        :stmt
        (b* (((erp stmt st)
              (comp-stmt-sts-split expr.stmt st)))
          (retok (c$::make-expr-stmt :stmt stmt) nil st))
        :tycompat
        (b* (((erp splitp1 left-type1 ?right-type1 st)
              (tyname-sts-split expr.type1 st))
             ((erp splitp2 left-type2 ?right-type2 st)
              (tyname-sts-split expr.type2 st))
             ((when (or splitp1 splitp2))
              (retmsg$ "Split is not supported in either operands ~
                        of a __builtin_types_compatible_p call.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st)))))
          (retok (make-expr-tycompat :type1 left-type1
                                     :type2 left-type2)
                 nil
                 st))
        :offsetof
        (b* (((erp splitp left-type ?right-type st)
              (tyname-sts-split expr.type st))
             ((when splitp)
              (retmsg$ "Split is not supported in the first operand ~
                        of a __builtin_offsetof call.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st))))
             ((erp member st)
              (member-designor-sts-split expr.member st)))
          (retok (make-expr-offsetof :type left-type
                                     :member member)
                 nil
                 st))
        :va-arg
        (b* (((erp left-list right-list? st)
              (expr-sts-split expr.list st))
             ((erp splitp left-type ?right-type st)
              (tyname-sts-split expr.type st))
             ((when (or right-list? splitp))
              (retmsg$ "Split is not supported in either operand ~
                        of a __builtin_va_arg call.~%~@0"
                       (context-msg-expr expr (sts-split-state->dialect st)))))
          (retok (make-expr-va-arg :list left-list
                                   :type left-type)
                 nil
                 st))
        :extension
        (b* (((erp left-expr right-expr? st)
              (expr-sts-split expr.expr st)))
          (retok (c$::make-expr-extension :expr left-expr)
                 (if right-expr?
                     (c$::make-expr-extension :expr right-expr?)
                   nil)
                 st))
        :sizeof-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :alignof-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :cast/call-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :cast/mul-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :cast/add-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :cast/sub-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :cast/and-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :cast/logand-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")))
    :measure (expr-count expr))

  (define expr-list-sts-split
    ((exprs expr-listp)
     (st sts-split-statep))
    :guard (expr-list-annop exprs)
    :returns (mv (er? maybe-msgp)
                 (exprs$ expr-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an expression list."
    :long
    (xdoc::topstring-p
     "If an expression in the list is split,
      the two expressions are added to the new list.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil st)
         ((when (endp exprs))
          (retok nil st))
         ((erp left-expr right-expr? st)
          (expr-sts-split (first exprs) st))
         ((erp exprs st)
          (expr-list-sts-split (rest exprs) st)))
      (retok (cons left-expr
                   (if right-expr?
                       (cons right-expr? exprs)
                     exprs))
             st))
    :measure (expr-list-count exprs))

  (define expr-option-sts-split
    ((expr? expr-optionp)
     (st sts-split-statep))
    :guard (expr-option-annop expr?)
    :returns (mv (er? maybe-msgp)
                 (left-expr? expr-optionp)
                 (right-expr? expr-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an optional expression."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st)
         ((unless expr?)
          (retok nil nil st))
         ((erp left-expr right-expr? st)
          (expr-sts-split (expr-option-some->val expr?) st)))
      (retok left-expr right-expr? st))
    :measure (expr-option-count expr?))

  (define const-expr-sts-split
    ((const-expr const-exprp)
     (st sts-split-statep))
    :guard (const-expr-annop const-expr)
    :returns (mv (er? maybe-msgp)
                 (left-const-expr const-exprp)
                 (right-const-expr? const-expr-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a constant expression."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (c$::const-expr-fix const-expr) nil st)
         ((const-expr const-expr) const-expr)
         ((erp left-expr right-expr? st)
          (expr-sts-split const-expr.expr st)))
      (retok (make-const-expr :expr left-expr)
             (if right-expr?
                 (make-const-expr :expr right-expr?)
               nil)
             st))
    :measure (const-expr-count const-expr))

  (define const-expr-option-sts-split
    ((const-expr? const-expr-optionp)
     (st sts-split-statep))
    :guard (const-expr-option-annop const-expr?)
    :returns (mv (er? maybe-msgp)
                 (left-const-expr? const-expr-optionp)
                 (right-const-expr? const-expr-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an optional constant expression."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st)
         ((unless const-expr?)
          (retok nil nil st))
         ((erp left-const-expr right-const-expr? st)
          (const-expr-sts-split (c$::const-expr-option-some->val const-expr?)
                                st)))
      (retok left-const-expr right-const-expr? st))
    :measure (const-expr-option-count const-expr?))

  (define genassoc-sts-split
    ((genassoc genassocp)
     (st sts-split-statep))
    :guard (genassoc-annop genassoc)
    :returns (mv (er? maybe-msgp)
                 (genassoc$ genassocp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a generic association."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (genassoc-fix genassoc) st))
      (genassoc-case
        genassoc
        :type
        (b* (((erp splitp left-type ?right-type st)
              (tyname-sts-split genassoc.type st))
             ((erp left-expr right-expr? st)
              (expr-sts-split genassoc.expr st))
             ((when (or splitp right-expr?))
              (retmsg$ "Split is not supported in a generic association.~%~@0"
                       (context-msg-genassoc genassoc
                                             (sts-split-state->dialect st)))))
          (retok (make-genassoc-type :type left-type
                                     :expr left-expr)
                 st))
        :default
        (b* (((erp left-expr right-expr? st)
              (expr-sts-split genassoc.expr st))
             ((when right-expr?)
              (retmsg$ "Split is not supported in a generic association.~%~@0"
                       (context-msg-genassoc genassoc
                                             (sts-split-state->dialect st)))))
          (retok (c$::make-genassoc-default :expr left-expr)
                 st))))
    :measure (genassoc-count genassoc))

  (define genassoc-list-sts-split
    ((genassocs genassoc-listp)
     (st sts-split-statep))
    :guard (genassoc-list-annop genassocs)
    :returns (mv (er? maybe-msgp)
                 (genassocs$ genassoc-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a generic association list."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (genassoc-list-fix genassocs) st)
         ((when (endp genassocs))
          (retok nil st))
         ((erp genassoc st)
          (genassoc-sts-split (first genassocs) st))
         ((erp genassocs st)
          (genassoc-list-sts-split (rest genassocs) st)))
      (retok (cons genassoc genassocs)
             st))
    :measure (genassoc-list-count genassocs))

  (define member-designor-sts-split
    ((member-designor member-designorp)
     (st sts-split-statep))
    :guard (member-designor-annop member-designor)
    :returns (mv (er? maybe-msgp)
                 (member-designor$ member-designorp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a member designator."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (member-designor-fix member-designor) st))
      (member-designor-case
        member-designor
        :ident (retok (member-designor-fix member-designor) st)
        :dot
        (b* (((erp member st)
              (member-designor-sts-split member-designor.member st)))
          (retok (make-member-designor-dot :member member
                                           :name member-designor.name)
                 st))
        :sub
        (b* (((erp member st)
              (member-designor-sts-split member-designor.member st))
             ((erp left-index right-index? st)
              (expr-sts-split member-designor.index st))
             ((when right-index?)
              (retmsg$ "Splits are not supported in member designators.~%~@0"
                       (context-msg-member-designor
                         member-designor
                         (sts-split-state->dialect st)))))
          (retok (make-member-designor-sub :member member
                                           :index left-index)
                 st))))
    :measure (member-designor-count member-designor))

  (define type-spec-sts-split
    ((type-spec type-specp)
     (st sts-split-statep))
    :guard (type-spec-annop type-spec)
    :returns (mv (er? maybe-msgp)
                 (left-type-spec type-specp)
                 (right-type-spec? type-spec-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a type specifier."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (type-spec-fix type-spec) nil st))
      (type-spec-case
        type-spec
        :void
        (retok (type-spec-fix type-spec) nil st)
        :char
        (retok (type-spec-fix type-spec) nil st)
        :short
        (retok (type-spec-fix type-spec) nil st)
        :int
        (retok (type-spec-fix type-spec) nil st)
        :long
        (retok (type-spec-fix type-spec) nil st)
        :float
        (retok (type-spec-fix type-spec) nil st)
        :double
        (retok (type-spec-fix type-spec) nil st)
        :signed
        (retok (type-spec-fix type-spec) nil st)
        :unsigned
        (retok (type-spec-fix type-spec) nil st)
        :bool
        (retok (type-spec-fix type-spec) nil st)
        :complex
        (retok (type-spec-fix type-spec) nil st)
        :atomic
        (b* (((erp tyname-splitp left-tyname right-tyname st)
              (tyname-sts-split type-spec.type st)))
          (retok (c$::make-type-spec-atomic :type left-tyname)
                 (if tyname-splitp
                     (c$::make-type-spec-atomic :type right-tyname)
                   nil)
                 st))
        :struct
        (b* (((c$::type-spec-struct-vinfo info) type-spec.info)
             (uid (c$::type-struct->uid info.type))
             (splitp (c$::uid-equal uid (sts-split-state->struct-uid st)))
             ((erp left-spec right-spec st)
              (struni-spec-sts-split type-spec.spec splitp st)))
          (retok (c$::make-type-spec-struct :spec left-spec)
                 (if splitp
                     (c$::make-type-spec-struct :spec right-spec)
                   nil)
                 st))
        :union
        (b* (((erp spec - st)
              (struni-spec-sts-split type-spec.spec nil st)))
          (retok (c$::make-type-spec-union :spec spec)
                 nil
                 st))
        :enum
        (b* (((erp spec st)
              (enum-spec-sts-split type-spec.spec st)))
          (retok (c$::make-type-spec-enum :spec spec) nil st))
        :typedef
        ;; A use of a typedef name denoting a splittable type
        ;; is replaced, on the right, by the right typedef name
        ;; recorded in the identifier map, keyed by the typedef's
        ;; unique identifier; the typedef declaration, which is
        ;; processed before any use, populates the map.
        (b* (((type+uid-vinfo info) type-spec.info)
             ((unless (eq (sts-splittablep info.type
                                           (sts-split-state->struct-uid st))
                          t))
              (retok (type-spec-fix type-spec) nil st))
             (right-ident? (omap::assoc info.uid
                                        (sts-split-state->ident-map st)))
             ((unless right-ident?)
              (retmsg$ "INTERNAL ERROR. ~
                        A use of the splittable typedef name ~x0 ~
                        has no associated right name.~%~@1"
                       (c$::type-spec-typedef->name type-spec)
                       (context-msg-type-spec
                         type-spec
                         (sts-split-state->dialect st)))))
          (retok (type-spec-fix type-spec)
                 (c$::make-type-spec-typedef :name (cdr right-ident?))
                 st))
        :int128
        (retok (type-spec-fix type-spec) nil st)
        :locase-float80
        (retok (type-spec-fix type-spec) nil st)
        :locase-float128
        (retok (type-spec-fix type-spec) nil st)
        :float16
        (retok (type-spec-fix type-spec) nil st)
        :float16x
        (retok (type-spec-fix type-spec) nil st)
        :float32
        (retok (type-spec-fix type-spec) nil st)
        :float32x
        (retok (type-spec-fix type-spec) nil st)
        :float64
        (retok (type-spec-fix type-spec) nil st)
        :float64x
        (retok (type-spec-fix type-spec) nil st)
        :float128
        (retok (type-spec-fix type-spec) nil st)
        :float128x
        (retok (type-spec-fix type-spec) nil st)
        :builtin-va-list
        (retok (type-spec-fix type-spec) nil st)
        :struct-empty
        (b* (((c$::type-spec-struct-vinfo info) type-spec.info)
             (uid (c$::type-struct->uid info.type))
             (splitp (c$::uid-equal uid (sts-split-state->struct-uid st)))
             ((erp attribs st)
              (attrib-spec-list-sts-split type-spec.attribs st)))
          (retok (c$::make-type-spec-struct-empty :attribs attribs
                                                  :name? type-spec.name?)
                 (if splitp
                     (c$::make-type-spec-struct-empty
                       :attribs attribs
                       :name? (and type-spec.name?
                                   (sts-split-state->right-name st)))
                   nil)
                 st))
        :typeof-expr
        (b* (((erp left-expr right-expr? st)
              (expr-sts-split type-spec.expr st)))
          (retok (make-type-spec-typeof-expr :expr left-expr
                                             :uscores type-spec.uscores)
                 (if right-expr?
                     (make-type-spec-typeof-expr :expr right-expr?
                                                 :uscores type-spec.uscores)
                   nil)
                 st))
        :typeof-type
        (b* (((erp splitp left-tyname right-tyname st)
              (tyname-sts-split type-spec.type st)))
          (retok (make-type-spec-typeof-type :type left-tyname
                                             :uscores type-spec.uscores)
                 (if splitp
                     (make-type-spec-typeof-type :type right-tyname
                                                 :uscores type-spec.uscores)
                   nil)
                 st))
        :typeof-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :auto-type
        (retmsg$ "The \"auto\" type specifier is not supported.")))
    :measure (type-spec-count type-spec))

  (define spec/qual-sts-split
    ((specqual spec/qual-p)
     (st sts-split-statep))
    :guard (spec/qual-annop specqual)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-spec/qual spec/qual-p)
                 (right-spec/qual spec/qual-p)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a specifier or qualifier."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil (spec/qual-fix specqual) (spec/qual-fix specqual) st))
      (spec/qual-case
        specqual
        :typespec
        (b* (((erp left-spec right-spec? st)
              (type-spec-sts-split specqual.spec st)))
          (retok (if right-spec? t nil)
                 (c$::make-spec/qual-typespec :spec left-spec)
                 (if right-spec?
                     (c$::make-spec/qual-typespec :spec right-spec?)
                   (spec/qual-fix specqual))
                 st))
        :typequal
        (retok nil (spec/qual-fix specqual) (spec/qual-fix specqual) st)
        :align
        (b* (((erp spec st) (align-spec-sts-split specqual.spec st)))
          (retok nil
                 (c$::make-spec/qual-align :spec spec)
                 (c$::make-spec/qual-align :spec spec)
                 st))
        :attrib
        (b* (((erp spec st) (attrib-spec-sts-split specqual.spec st)))
          (retok nil
                 (c$::make-spec/qual-attrib :spec spec)
                 (c$::make-spec/qual-attrib :spec spec)
                 st))))
    :measure (spec/qual-count specqual))

  (define spec/qual-list-sts-split
    ((specquals spec/qual-listp)
     (st sts-split-statep))
    :guard (spec/qual-list-annop specquals)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-spec/qual-list spec/qual-listp)
                 (right-spec/qual-list spec/qual-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a specifier/qualifier list."
    :long
    (xdoc::topstring-p
     "The returned @('splitp') indicates whether
      any specifier in the list split,
      which happens when the list includes
      a type specifier denoting the target struct type.
      The right list is only meaningful in that case;
      elements which do not split
      contribute their left transformation to both lists.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil nil st)
         ((when (endp specquals))
          (retok nil nil nil st))
        ((erp first-splitp left-specqual right-specqual st)
         (spec/qual-sts-split (car specquals) st))
        ((erp rest-splitp left-rest right-rest st)
         (spec/qual-list-sts-split (cdr specquals) st)))
      (retok (or first-splitp rest-splitp)
             (cons left-specqual left-rest)
             (cons (if first-splitp right-specqual left-specqual)
                   right-rest)
             st))
    :measure (spec/qual-list-count specquals))

  (define align-spec-sts-split
    ((align-spec align-specp)
     (st sts-split-statep))
    :guard (align-spec-annop align-spec)
    :returns (mv (er? maybe-msgp)
                 (align-spec$ align-specp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an alignment specifier."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (align-spec-fix align-spec) st))
      (align-spec-case
        align-spec
        :alignas-type
        (b* (((erp splitp left-type ?right-type st)
              (tyname-sts-split align-spec.type st))
             ((when splitp)
              (retmsg$ "Splits are not supported in alignment specifiers.~%~@0"
                       (context-msg-align-spec
                         align-spec
                         (sts-split-state->dialect st)))))
          (retok (c$::make-align-spec-alignas-type :type left-type) st))
        :alignas-expr
        (b* (((erp left-expr right-expr? st)
              (const-expr-sts-split align-spec.expr st))
             ((when right-expr?)
              (retmsg$ "Splits are not supported in alignment specifiers.~%~@0"
                       (context-msg-align-spec
                         align-spec
                         (sts-split-state->dialect st)))))
          (retok (c$::make-align-spec-alignas-expr :expr left-expr) st))
        :alignas-ambig (retmsg$ "Ambiguous ASTs are unsupported.")))
    :measure (align-spec-count align-spec))

  (define decl-spec-sts-split
    ((decl-spec decl-specp)
     (st sts-split-statep))
    :guard (decl-spec-annop decl-spec)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-decl-spec decl-specp)
                 (right-decl-spec decl-specp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a declaration specifier."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil (decl-spec-fix decl-spec) (decl-spec-fix decl-spec) st))
      (decl-spec-case
        decl-spec
        :stoclass
        (retok nil (decl-spec-fix decl-spec) (decl-spec-fix decl-spec) st)
        :typespec
        (b* (((erp left-spec right-spec? st)
              (type-spec-sts-split decl-spec.spec st)))
          (retok (if right-spec? t nil)
                 (c$::make-decl-spec-typespec :spec left-spec)
                 (if right-spec?
                     (c$::make-decl-spec-typespec :spec right-spec?)
                   (decl-spec-fix decl-spec))
                 st))
        :typequal
        (retok nil (decl-spec-fix decl-spec) (decl-spec-fix decl-spec) st)
        :function
        (retok nil (decl-spec-fix decl-spec) (decl-spec-fix decl-spec) st)
        :align
        (b* (((erp spec st) (align-spec-sts-split decl-spec.spec st)))
          (retok nil
                 (c$::make-decl-spec-align :spec spec)
                 (c$::make-decl-spec-align :spec spec)
                 st))
        :attrib
        (b* (((erp spec st) (attrib-spec-sts-split decl-spec.spec st)))
          (retok nil
                 (c$::make-decl-spec-attrib :spec spec)
                 (c$::make-decl-spec-attrib :spec spec)
                 st))
        :stdcall
        (retok nil (decl-spec-fix decl-spec) (decl-spec-fix decl-spec) st)
        :declspec
        (retok nil (decl-spec-fix decl-spec) (decl-spec-fix decl-spec) st)))
    :measure (decl-spec-count decl-spec))

  (define decl-spec-list-sts-split
    ((decl-specs decl-spec-listp)
     (st sts-split-statep))
    :guard (decl-spec-list-annop decl-specs)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-decl-spec-list decl-spec-listp)
                 (right-decl-spec-list decl-spec-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a declaration specifier list."
    :long
    (xdoc::topstring-p
     "The returned @('splitp') indicates whether
      any specifier in the list split,
      which happens when the list includes
      a type specifier denoting the target struct type
      (a definition or a tagged reference).
      The right list is only meaningful in that case;
      elements which do not split
      contribute their left transformation to both lists.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil nil st)
         ((when (endp decl-specs))
          (retok nil nil nil st))
         ((erp first-splitp left-decl-spec right-decl-spec st)
          (decl-spec-sts-split (car decl-specs) st))
         ((erp rest-splitp left-rest right-rest st)
          (decl-spec-list-sts-split (cdr decl-specs) st)))
      (retok (or first-splitp rest-splitp)
             (cons left-decl-spec left-rest)
             (cons (if first-splitp right-decl-spec left-decl-spec)
                   right-rest)
             st))
    :measure (decl-spec-list-count decl-specs))

  (define typequal/attribspec-sts-split
    ((tyqualattrib c$::typequal/attribspec-p)
     (st sts-split-statep))
    :guard (c$::typequal/attribspec-annop tyqualattrib)
    :returns (mv (er? maybe-msgp)
                 (tyqualattrib$ c$::typequal/attribspec-p)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a type qualifier or attribute specifier."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (c$::typequal/attribspec-fix tyqualattrib) st))
      (c$::typequal/attribspec-case
        tyqualattrib
        :type (retok (c$::typequal/attribspec-fix tyqualattrib) st)
        :attrib
        (b* (((erp spec st)
              (attrib-spec-sts-split tyqualattrib.spec st)))
          (retok (c$::make-typequal/attribspec-attrib :spec spec) st))))
    :measure (c$::typequal/attribspec-count tyqualattrib))

  (define typequal/attribspec-list-sts-split
    ((tyqualattribs c$::typequal/attribspec-listp)
     (st sts-split-statep))
    :guard (c$::typequal/attribspec-list-annop tyqualattribs)
    :returns (mv (er? maybe-msgp)
                 (tyqualattribs$ c$::typequal/attribspec-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a type-qualifier/attribute-specifier list."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (c$::typequal/attribspec-list-fix tyqualattribs) st)
         ((when (endp tyqualattribs))
          (retok nil st))
         ((erp head st)
          (typequal/attribspec-sts-split (car tyqualattribs) st))
         ((erp rest st)
          (typequal/attribspec-list-sts-split (cdr tyqualattribs) st)))
      (retok (cons head rest) st))
    :measure (c$::typequal/attribspec-list-count tyqualattribs))

  (define typequal/attribspec-list-list-sts-split
    ((tyqualattribs typequal/attribspec-list-listp)
     (st sts-split-statep))
    :guard (c$::typequal/attribspec-list-list-annop tyqualattribs)
    :returns (mv (er? maybe-msgp)
                 (tyqualattribs$ typequal/attribspec-list-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a list of type-qualifier/attribute-specifier lists."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (c$::typequal/attribspec-list-list-fix tyqualattribs) st)
         ((when (endp tyqualattribs))
          (retok nil st))
         ((erp head st)
          (typequal/attribspec-list-sts-split (car tyqualattribs) st))
         ((erp rest st)
          (typequal/attribspec-list-list-sts-split (cdr tyqualattribs) st)))
      (retok (cons head rest) st))
    :measure (c$::typequal/attribspec-list-list-count tyqualattribs))

  (define initer-sts-split
    ((initer initerp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (initer-annop initer)
    :returns (mv (er? maybe-msgp)
                 (left-initer initerp)
                 (right-initer? initer-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an initializer."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (initer-fix initer) nil st))
      (initer-case
        initer
        :single
        (b* (((erp left-expr right-expr? st)
              (expr-sts-split initer.expr st)))
          (retok (c$::make-initer-single :expr left-expr)
                 (if right-expr?
                     (c$::make-initer-single :expr right-expr?)
                   nil)
                 st))
        :list
        (b* (((erp left-elems right-elems st)
              (desiniter-list-sts-split splitp initer.elems st)))
          (retok (c$::make-initer-list :elems left-elems
                                       :final-comma initer.final-comma)
                 (if splitp
                     (c$::make-initer-list :elems right-elems
                                           :final-comma initer.final-comma)
                   nil)
                 st))))
    :measure (initer-count initer))

  (define initer-option-sts-split
    ((initer? initer-optionp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (initer-option-annop initer?)
    :returns (mv (er? maybe-msgp)
                 (left-initer? initer-optionp)
                 (right-initer? initer-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an optional initializer."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st))
      (initer-option-case
        initer?
        :none (retok nil nil st)
        :some (initer-sts-split (c$::initer-option-some->val initer?)
                                splitp
                                st)))
    :measure (initer-option-count initer?))

  (define desiniter-sts-split
    ((desiniter desiniterp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (desiniter-annop desiniter)
    :returns (mv (er? maybe-msgp)
                 (rightp booleanp)
                 (left-desiniter desiniterp)
                 (right-desiniter desiniterp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a designated initializer."
    :long
    (xdoc::topstring-p
     "When @('splitp') is @('t'),
      the initializer is routed to either
      @('left-desiniter') or @('right-desiniter')
      based on the field it designates;
      @('rightp') in the return indicates which.
      Initializers which are split apart
      are given explicit designations,
      drawn from the validator annotations
      when there is no syntactic designation,
      since the implicit ordering is generally not preserved
      by the partition into left and right initializer lists.
      When @('splitp') is @('nil'), @('left-desiniter') holds the result.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil (desiniter-fix desiniter) (desiniter-fix desiniter) st)
         ((desiniter desiniter) desiniter)
         ((erp designors st)
          (designor-list-sts-split desiniter.designors st))
         ((erp left-initer right-initer? st)
          (initer-sts-split desiniter.initer nil st))
         ((when right-initer?)
          (retmsg$ "Splits are not supported ~
                    within designated initializers.~%~@0"
                   (context-msg-desiniter desiniter
                                          (sts-split-state->dialect st))))
         (new-desiniter (c$::make-desiniter :designors designors
                                            :initer left-initer
                                            :info desiniter.info))
         ((unless splitp)
          (retok nil new-desiniter new-desiniter st))
         ((unless (c$::initer-purep left-initer))
          (retmsg$ "Initializers must be pure when split apart.~%~@0"
                   (context-msg-desiniter desiniter (sts-split-state->dialect st))))
         ((erp rightp) (desiniter-sts-rightp desiniter st))
         ;; Make implicit designations explicit,
         ;; since the implicit ordering is generally not preserved
         ;; by the partition into left and right initializer lists.
         (new-desiniter
           (if designors
               new-desiniter
             (c$::change-desiniter
               new-desiniter
               :designors (c$::desiniter-vinfo->designors desiniter.info)))))
      (retok rightp new-desiniter new-desiniter st))
    :measure (desiniter-count desiniter))

  (define desiniter-list-sts-split
    ((splitp booleanp)
     (desiniter-list desiniter-listp)
     (st sts-split-statep))
    :guard (desiniter-list-annop desiniter-list)
    :returns (mv (er? maybe-msgp)
                 (left-desiniter-list desiniter-listp)
                 (right-desiniter-list desiniter-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a designated initializer list."
    :long
    (xdoc::topstring-p
     "When @('splitp') is @('t'),
      each initializer is routed to either the left or right list
      based on the member it designates.
      When @('splitp') is @('nil'),
      both lists hold the same transformed initializers.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st)
         ((when (endp desiniter-list))
          (retok nil nil st))
         ((erp rightp left-desiniter right-desiniter st)
          (desiniter-sts-split (car desiniter-list) splitp st))
         ((erp left-rest right-rest st)
          (desiniter-list-sts-split splitp (cdr desiniter-list) st))
         ((unless splitp)
          (retok (cons left-desiniter left-rest)
                 (cons right-desiniter right-rest)
                 st)))
      (if rightp
          (retok left-rest
                 (cons right-desiniter right-rest)
                 st)
        (retok (cons left-desiniter left-rest)
               right-rest
               st)))
    :measure (desiniter-list-count desiniter-list))

  (define designor-sts-split
    ((designor designorp)
     (st sts-split-statep))
    :guard (designor-annop designor)
    :returns (mv (er? maybe-msgp)
                 (designor$ designorp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a designator."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (designor-fix designor) st))
      (designor-case
        designor
        :sub
        (b* (((erp left-index right-index? st)
              (const-expr-sts-split designor.index st))
             ((when right-index?)
              (retmsg$ "Splits are not supported in designators.~%~@0"
                       (context-msg-designor designor
                                             (sts-split-state->dialect st))))
             ((erp left-range? right-range? st)
              (const-expr-option-sts-split designor.range? st))
             ((when right-range?)
              (retmsg$ "Splits are not supported in designators.~%~@0"
                       (context-msg-designor designor
                                             (sts-split-state->dialect st)))))
          (retok (make-designor-sub :index left-index :range? left-range?) st))
        :dot (retok (designor-fix designor) st)))
    :measure (designor-count designor))

  (define designor-list-sts-split
    ((designors designor-listp)
     (st sts-split-statep))
    :guard (designor-list-annop designors)
    :returns (mv (er? maybe-msgp)
                 (designors$ designor-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a designator list."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (designor-list-fix designors) st)
         ((when (endp designors))
          (retok nil st))
         ((erp head st)
          (designor-sts-split (car designors) st))
         ((erp rest st)
          (designor-list-sts-split (cdr designors) st)))
      (retok (cons head rest) st))
    :measure (designor-list-count designors))

  (define declor-sts-split
    ((declor declorp)
     (splitp booleanp)
     (uid? c$::uid-optionp)
     (st sts-split-statep))
    :guard (declor-annop declor)
    :returns (mv (er? maybe-msgp)
                 (left-declor declorp)
                 (right-declor? declor-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a declarator."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (declor-fix declor) nil st)
         ((declor declor) declor)
         ((erp pointers st)
          (typequal/attribspec-list-list-sts-split declor.pointers st))
         ((erp splitp left-dirdeclor right-dirdeclor st)
          (dirdeclor-sts-split declor.direct splitp uid? st)))
      (retok (c$::make-declor :pointers pointers
                              :direct left-dirdeclor)
             (if splitp
                 (c$::make-declor :pointers pointers
                                  :direct right-dirdeclor)
               nil)
             st))
    :measure (declor-count declor))

  (define declor-option-sts-split
    ((declor? declor-optionp)
     (splitp booleanp)
     (uid? c$::uid-optionp)
     (st sts-split-statep))
    :guard (declor-option-annop declor?)
    :returns (mv (er? maybe-msgp)
                 (left-declor? declor-optionp)
                 (right-declor? declor-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an optional declarator."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st))
      (declor-option-case
        declor?
        :none (retok nil nil st)
        :some (declor-sts-split (c$::declor-option-some->val declor?)
                                splitp
                                uid?
                                st)))
    :measure (declor-option-count declor?))

  (define dirdeclor-sts-split
    ((dirdeclor dirdeclorp)
     (splitp booleanp)
     (uid? c$::uid-optionp)
     (st sts-split-statep))
    :guard (dirdeclor-annop dirdeclor)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-dirdeclor dirdeclorp)
                 (right-dirdeclor dirdeclorp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a direct declarator."
    :long
    (xdoc::topstring-p
     "When splitting and a @('uid?') is provided,
      the identifier map is extended to associate the unique identifier
      with the newly generated right identifier
      (unless an association already exists, in which case it is reused).")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil (dirdeclor-fix dirdeclor) (dirdeclor-fix dirdeclor) st))
      (dirdeclor-case
        dirdeclor
        :ident
        (b* (((unless splitp)
              (retok nil
                     (dirdeclor-fix dirdeclor)
                     (dirdeclor-fix dirdeclor)
                     st))
             ((unless uid?)
              (retmsg$ "INTERNAL ERROR. ~
                        Attempted to split a declarator ~
                        without a unique identifier.~%~@0"
                       (context-msg-dirdeclor dirdeclor
                                              (sts-split-state->dialect st))))
             ((sts-split-state st) st)
             (lookup (omap::assoc uid? st.ident-map))
             ((when lookup)
              (retok t
                     (dirdeclor-fix dirdeclor)
                     (c$::make-dirdeclor-ident :ident (cdr lookup))
                     st))
             (right-ident (fresh-ident dirdeclor.ident st.blacklist))
             (st (change-sts-split-state
                   st
                   :blacklist (insert right-ident st.blacklist)
                   :ident-map (omap::update uid? right-ident st.ident-map))))
          (retok t
                 (dirdeclor-fix dirdeclor)
                 (c$::make-dirdeclor-ident :ident right-ident)
                 st))
        :paren
        (b* (((erp left-inner right-inner? st)
              (declor-sts-split dirdeclor.inner splitp uid? st))
             (left-dirdeclor (c$::make-dirdeclor-paren :inner left-inner)))
          (retok (if right-inner? t nil)
                 left-dirdeclor
                 (if right-inner?
                     (c$::make-dirdeclor-paren :inner right-inner?)
                   left-dirdeclor)
                 st))
        :array
        (b* (((erp dsplitp left-declor right-declor st)
              (dirdeclor-sts-split dirdeclor.declor splitp uid? st))
             ((erp qualspecs st)
              (typequal/attribspec-list-sts-split dirdeclor.qualspecs st))
             ((erp left-size? right-size? st)
              (expr-option-sts-split dirdeclor.size? st))
             ((when right-size?)
              (retmsg$ "Splits are not supported in array sizes.~%~@0"
                       (context-msg-dirdeclor dirdeclor
                                              (sts-split-state->dialect st))))
             (left-dirdeclor
               (c$::make-dirdeclor-array :declor left-declor
                                         :qualspecs qualspecs
                                         :size? left-size?)))
          (retok dsplitp
                 left-dirdeclor
                 (if dsplitp
                     (c$::make-dirdeclor-array :declor right-declor
                                               :qualspecs qualspecs
                                               :size? left-size?)
                   left-dirdeclor)
                 st))
        :array-static1
        (b* (((erp dsplitp left-declor right-declor st)
              (dirdeclor-sts-split dirdeclor.declor splitp uid? st))
             ((erp qualspecs st)
              (typequal/attribspec-list-sts-split dirdeclor.qualspecs st))
             ((erp left-size right-size? st)
              (expr-sts-split dirdeclor.size st))
             ((when right-size?)
              (retmsg$ "Splits are not supported in array sizes.~%~@0"
                       (context-msg-dirdeclor dirdeclor
                                              (sts-split-state->dialect st))))
             (left-dirdeclor
               (c$::make-dirdeclor-array-static1 :declor left-declor
                                                 :qualspecs qualspecs
                                                 :size left-size)))
          (retok dsplitp
                 left-dirdeclor
                 (if dsplitp
                     (c$::make-dirdeclor-array-static1 :declor right-declor
                                                       :qualspecs qualspecs
                                                       :size left-size)
                   left-dirdeclor)
                 st))
        :array-static2
        (b* (((erp dsplitp left-declor right-declor st)
              (dirdeclor-sts-split dirdeclor.declor splitp uid? st))
             ((erp qualspecs st)
              (typequal/attribspec-list-sts-split dirdeclor.qualspecs st))
             ((erp left-size right-size? st)
              (expr-sts-split dirdeclor.size st))
             ((when right-size?)
              (retmsg$ "Splits are not supported in array sizes.~%~@0"
                       (context-msg-dirdeclor dirdeclor
                                              (sts-split-state->dialect st))))
             (left-dirdeclor
               (c$::make-dirdeclor-array-static2 :declor left-declor
                                                 :qualspecs qualspecs
                                                 :size left-size)))
          (retok dsplitp
                 left-dirdeclor
                 (if dsplitp
                     (c$::make-dirdeclor-array-static2 :declor right-declor
                                                       :qualspecs qualspecs
                                                       :size left-size)
                   left-dirdeclor)
                 st))
        :array-star
        (b* (((erp dsplitp left-declor right-declor st)
              (dirdeclor-sts-split dirdeclor.declor splitp uid? st))
             ((erp qualspecs st)
              (typequal/attribspec-list-sts-split dirdeclor.qualspecs st))
             (left-dirdeclor
               (c$::make-dirdeclor-array-star :declor left-declor
                                              :qualspecs qualspecs)))
          (retok dsplitp
                 left-dirdeclor
                 (if dsplitp
                     (c$::make-dirdeclor-array-star :declor right-declor
                                                    :qualspecs qualspecs)
                   left-dirdeclor)
                 st))
        :function-params
        (b* (((erp dsplitp left-declor right-declor st)
              (dirdeclor-sts-split dirdeclor.declor splitp uid? st))
             ((erp params st)
              (param-declon-list-sts-split dirdeclor.params st))
             (left-dirdeclor
               (c$::make-dirdeclor-function-params
                 :declor left-declor
                 :params params
                 :ellipsis dirdeclor.ellipsis)))
          (retok dsplitp
                 left-dirdeclor
                 (if dsplitp
                     (c$::make-dirdeclor-function-params
                       :declor right-declor
                       :params params
                       :ellipsis dirdeclor.ellipsis)
                   left-dirdeclor)
                 st))
        :function-names
        (b* (((erp dsplitp left-declor right-declor st)
              (dirdeclor-sts-split dirdeclor.declor splitp uid? st))
             (left-dirdeclor
               (c$::make-dirdeclor-function-names :declor left-declor
                                                  :names dirdeclor.names)))
          (retok dsplitp
                 left-dirdeclor
                 (if dsplitp
                     (c$::make-dirdeclor-function-names :declor right-declor
                                                        :names dirdeclor.names)
                   left-dirdeclor)
                 st))))
    :measure (dirdeclor-count dirdeclor))

  (define absdeclor-sts-split
    ((absdeclor absdeclorp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (absdeclor-annop absdeclor)
    :returns (mv (er? maybe-msgp)
                 (left-absdeclor absdeclorp)
                 (right-absdeclor? absdeclor-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an abstract declarator."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (absdeclor-fix absdeclor) nil st)
         ((absdeclor absdeclor) absdeclor)
         ((erp pointers st)
          (typequal/attribspec-list-list-sts-split absdeclor.pointers st))
         ((erp left-direct? right-direct? st)
          (dirabsdeclor-option-sts-split absdeclor.direct? splitp st)))
      (retok (c$::make-absdeclor :pointers pointers
                                 :direct? left-direct?)
             (if right-direct?
                 (c$::make-absdeclor :pointers pointers
                                     :direct? right-direct?)
               nil)
             st))
    :measure (absdeclor-count absdeclor))

  (define absdeclor-option-sts-split
    ((absdeclor? absdeclor-optionp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (absdeclor-option-annop absdeclor?)
    :returns (mv (er? maybe-msgp)
                 (left-absdeclor? absdeclor-optionp)
                 (right-absdeclor? absdeclor-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an optional abstract declarator."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st))
      (absdeclor-option-case
        absdeclor?
        :none (retok nil nil st)
        :some (absdeclor-sts-split (c$::absdeclor-option-some->val absdeclor?)
                                   splitp
                                   st)))
    :measure (absdeclor-option-count absdeclor?))

  (define dirabsdeclor-sts-split
    ((dirabsdeclor dirabsdeclorp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (dirabsdeclor-annop dirabsdeclor)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-dirabsdeclor dirabsdeclorp)
                 (right-dirabsdeclor dirabsdeclorp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a direct abstract declarator."
    (b* ((st (sts-split-state-fix st))
         ((reterr)
          nil
          (dirabsdeclor-fix dirabsdeclor)
          (dirabsdeclor-fix dirabsdeclor)
          st))
      (dirabsdeclor-case
        dirabsdeclor
        :dummy-base
        (retok nil
               (dirabsdeclor-fix dirabsdeclor)
               (dirabsdeclor-fix dirabsdeclor)
               st)
        :paren
        (b* (((erp left-inner right-inner? st)
              (absdeclor-sts-split dirabsdeclor.inner splitp st))
             (left-dirabsdeclor
               (c$::make-dirabsdeclor-paren :inner left-inner)))
          (retok (if right-inner? t nil)
                 left-dirabsdeclor
                 (if right-inner?
                     (c$::make-dirabsdeclor-paren :inner right-inner?)
                   left-dirabsdeclor)
                 st))
        :array
        (b* (((erp left-declor? right-declor? st)
              (dirabsdeclor-option-sts-split dirabsdeclor.declor? splitp st))
             ((erp qualspecs st)
              (typequal/attribspec-list-sts-split dirabsdeclor.qualspecs st))
             ((erp left-size? right-size? st)
              (expr-option-sts-split dirabsdeclor.size? st))
             ((when right-size?)
              (retmsg$ "Splits are not supported in array sizes.~%~@0"
                       (context-msg-dirabsdeclor
                         dirabsdeclor
                         (sts-split-state->dialect st))))
             (left-dirabsdeclor
               (c$::make-dirabsdeclor-array :declor? left-declor?
                                            :qualspecs qualspecs
                                            :size? left-size?)))
          (retok (if right-declor? t nil)
                 left-dirabsdeclor
                 (if right-declor?
                     (c$::make-dirabsdeclor-array :declor? right-declor?
                                                  :qualspecs qualspecs
                                                  :size? left-size?)
                   left-dirabsdeclor)
                 st))
        :array-static1
        (b* (((erp left-declor? right-declor? st)
              (dirabsdeclor-option-sts-split dirabsdeclor.declor? splitp st))
             ((erp qualspecs st)
              (typequal/attribspec-list-sts-split dirabsdeclor.qualspecs st))
             ((erp left-size right-size? st)
              (expr-sts-split dirabsdeclor.size st))
             ((when right-size?)
              (retmsg$ "Splits are not supported in array sizes.~%~@0"
                       (context-msg-dirabsdeclor
                         dirabsdeclor
                         (sts-split-state->dialect st))))
             (left-dirabsdeclor
               (c$::make-dirabsdeclor-array-static1 :declor? left-declor?
                                                    :qualspecs qualspecs
                                                    :size left-size)))
          (retok (if right-declor? t nil)
                 left-dirabsdeclor
                 (if right-declor?
                     (c$::make-dirabsdeclor-array-static1 :declor? right-declor?
                                                          :qualspecs qualspecs
                                                          :size left-size)
                   left-dirabsdeclor)
                 st))
        :array-static2
        (b* (((erp left-declor? right-declor? st)
              (dirabsdeclor-option-sts-split dirabsdeclor.declor? splitp st))
             ((erp qualspecs st)
              (typequal/attribspec-list-sts-split dirabsdeclor.qualspecs st))
             ((erp left-size right-size? st)
              (expr-sts-split dirabsdeclor.size st))
             ((when right-size?)
              (retmsg$ "Splits are not supported in array sizes.~%~@0"
                       (context-msg-dirabsdeclor
                         dirabsdeclor
                         (sts-split-state->dialect st))))
             (left-dirabsdeclor
               (c$::make-dirabsdeclor-array-static2 :declor? left-declor?
                                                    :qualspecs qualspecs
                                                    :size left-size)))
          (retok (if right-declor? t nil)
                 left-dirabsdeclor
                 (if right-declor?
                     (c$::make-dirabsdeclor-array-static2
                       :declor? right-declor?
                       :qualspecs qualspecs
                       :size left-size)
                   left-dirabsdeclor)
                 st))
        :array-star
        (b* (((erp left-declor? right-declor? st)
              (dirabsdeclor-option-sts-split dirabsdeclor.declor? splitp st))
             (left-dirabsdeclor
               (c$::make-dirabsdeclor-array-star :declor? left-declor?)))
          (retok (if right-declor? t nil)
                 left-dirabsdeclor
                 (if right-declor?
                     (c$::make-dirabsdeclor-array-star :declor? right-declor?)
                   left-dirabsdeclor)
                 st))
        :function
        (b* (((erp left-declor? right-declor? st)
              (dirabsdeclor-option-sts-split dirabsdeclor.declor? splitp st))
             ((erp params st)
              (param-declon-list-sts-split dirabsdeclor.params st))
             (left-dirabsdeclor
               (c$::make-dirabsdeclor-function
                 :declor? left-declor?
                 :params params
                 :ellipsis dirabsdeclor.ellipsis)))
          (retok (if right-declor? t nil)
                 left-dirabsdeclor
                 (if right-declor?
                     (c$::make-dirabsdeclor-function
                       :declor? right-declor?
                       :params params
                       :ellipsis dirabsdeclor.ellipsis)
                   left-dirabsdeclor)
                 st))))
    :measure (dirabsdeclor-count dirabsdeclor))

  (define dirabsdeclor-option-sts-split
    ((dirabsdeclor? dirabsdeclor-optionp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (dirabsdeclor-option-annop dirabsdeclor?)
    :returns (mv (er? maybe-msgp)
                 (left-dirabsdeclor? dirabsdeclor-optionp)
                 (right-dirabsdeclor? dirabsdeclor-optionp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an optional direct abstract declarator."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st))
      (dirabsdeclor-option-case
        dirabsdeclor?
        :none (retok nil nil st)
        :some
        (b* (((erp out-splitp left-dirabsdeclor right-dirabsdeclor st)
              (dirabsdeclor-sts-split
                (c$::dirabsdeclor-option-some->val dirabsdeclor?) splitp st)))
          (retok left-dirabsdeclor
                 (if out-splitp right-dirabsdeclor nil)
                 st))))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  (define param-declon-sts-split
    ((param-declon param-declonp)
     (st sts-split-statep))
    :guard (param-declon-annop param-declon)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-param-declon param-declonp)
                 (right-param-declon param-declonp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a parameter declaration."
    (b* ((st (sts-split-state-fix st))
         ((reterr)
          nil
          (param-declon-fix param-declon)
          (param-declon-fix param-declon)
          st)
         ((param-declon param-declon) param-declon)
         ((type-option-vinfo info) param-declon.info)
         ((mv erp splitp)
          (if info.type?
              (sts-check-type info.type? st)
            (mv nil nil)))
         ((when erp)
          (retmsg$ "~@0~%~@1"
                   erp
                   (context-msg-param-declon param-declon
                                             (sts-split-state->dialect st))))
         ((erp - left-specs right-specs st)
          (decl-spec-list-sts-split param-declon.specs st))
         ((erp - left-declor right-declor st)
          (param-declor-sts-split param-declon.declor splitp st))
         ((erp attribs st)
          (attrib-spec-list-sts-split param-declon.attribs st))
         (left-param-declon
           (c$::make-param-declon :specs left-specs
                                  :declor left-declor
                                  :attribs attribs
                                  :info param-declon.info)))
      (retok splitp
             left-param-declon
             (if splitp
                 (c$::make-param-declon :specs right-specs
                                        :declor right-declor
                                        :attribs attribs
                                        :info param-declon.info)
               left-param-declon)
             st))
    :measure (param-declon-count param-declon))

  (define param-declon-list-sts-split
    ((params param-declon-listp)
     (st sts-split-statep))
    :guard (param-declon-list-annop params)
    :returns (mv (er? maybe-msgp)
                 (params$ param-declon-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a parameter declaration list."
    :long
    (xdoc::topstring-p
     "Splits are spliced into the list in-place.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) (param-declon-list-fix params) st)
         ((when (endp params))
          (retok nil st))
         ((erp splitp left right st)
          (param-declon-sts-split (car params) st))
         ((erp rest st)
          (param-declon-list-sts-split (cdr params) st)))
      (if splitp
          (retok (list* left right rest) st)
        (retok (cons left rest) st)))
    :measure (param-declon-list-count params))

  (define param-declor-sts-split
    ((param-declor param-declorp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (param-declor-annop param-declor)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-param-declor param-declorp)
                 (right-param-declor param-declorp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a parameter declarator."
    :long
    (xdoc::topstring-p
     "When @('splitp') is @('t')
      but the parameter declarator contains no identifier to split
      (i.e. it is abstract or absent),
      the right parameter declarator mirrors the left,
      so that the caller may use it for the right parameter declaration.")
    (b* ((st (sts-split-state-fix st))
         ((reterr)
          nil
          (param-declor-fix param-declor)
          (param-declor-fix param-declor)
          st))
      (param-declor-case
        param-declor
        :nonabstract
        (b* (((type+uid-vinfo info) param-declor.info)
             ((erp left-declor right-declor? st)
              (declor-sts-split param-declor.declor
                                splitp
                                (and splitp info.uid)
                                st))
             ((when (xor splitp right-declor?))
              (retmsg$ "INTERNAL ERROR. ~
                        A parameter declarator was split ~
                        contrary to its declared type, or vice versa.~%~@0"
                       (context-msg-param-declor
                         param-declor
                         (sts-split-state->dialect st))))
             (left-param-declor
               (c$::make-param-declor-nonabstract :declor left-declor
                                                  :info param-declor.info)))
          (retok (if right-declor? t nil)
                 left-param-declor
                 (if right-declor?
                     (c$::make-param-declor-nonabstract
                       :declor right-declor?
                       :info param-declor.info)
                   left-param-declor)
                 st))
        :abstract
        (b* (((erp left-absdeclor right-absdeclor? st)
              (absdeclor-sts-split param-declor.declor splitp st)))
          (retok (if right-absdeclor? t nil)
                 (c$::make-param-declor-abstract :declor left-absdeclor)
                 (c$::make-param-declor-abstract
                   :declor (or right-absdeclor? left-absdeclor))
                 st))
        :none
        (retok nil
               (param-declor-fix param-declor)
               (param-declor-fix param-declor)
               st)
        :ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")))
    :measure (param-declor-count param-declor))

  (define tyname-sts-split
    ((tyname tynamep)
     (st sts-split-statep))
    :guard (tyname-annop tyname)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-tyname tynamep)
                 (right-tyname tynamep)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a type name."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil (tyname-fix tyname) (tyname-fix tyname) st)
         ((tyname tyname) tyname)
         ((c$::type-vinfo info) tyname.info)
         ((mv erp splitp)
          (sts-check-type info.type st))
         ((when erp)
          (retmsg$ "~@0~%~@1"
                   erp
                   (context-msg-tyname tyname (sts-split-state->dialect st))))
         ((erp - left-specquals right-specquals st)
          (spec/qual-list-sts-split tyname.specquals st))
         ((erp left-declor? right-declor? st)
          (absdeclor-option-sts-split tyname.declor? splitp st)))
      (retok splitp
             (c$::make-tyname :specquals left-specquals
                              :declor? left-declor?
                              :info tyname.info)
             (if splitp
                 (c$::make-tyname :specquals right-specquals
                                  :declor? (or right-declor? left-declor?)
                                  :info tyname.info)
               (tyname-fix tyname))
             st))
    :measure (tyname-count tyname))

  (define struni-spec-sts-split
    ((struni-spec struni-specp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (struni-spec-annop struni-spec)
    :returns (mv (er? maybe-msgp)
                 (left-struni-spec struni-specp)
                 (right-struni-spec struni-specp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a struct or union specifier."
    :long
    (xdoc::topstring-p
     "When @('splitp') is @('t'),
      we are splitting a definition of the target struct type:
      the members are partitioned into
      the left and right struct or union specifiers,
      and the right specifier is named with
      the right struct type name from the state
      (unless the original specifier is anonymous).
      When @('splitp') is @('nil'),
      @('left-struni-spec') holds the result.")
    (b* ((st (sts-split-state-fix st))
         ((reterr)
          (struni-spec-fix struni-spec)
          (struni-spec-fix struni-spec)
          st)
         ((struni-spec struni-spec) struni-spec)
         ((erp attribs st)
          (attrib-spec-list-sts-split struni-spec.attribs st))
         ((erp left-members right-members st)
          (struct-declon-list-sts-split splitp struni-spec.members st))
         (left-struni-spec
           (c$::make-struni-spec :attribs attribs
                                 :name? struni-spec.name?
                                 :members left-members)))
      (retok left-struni-spec
             (if splitp
                 (c$::make-struni-spec
                   :attribs attribs
                   :name? (and struni-spec.name?
                               (sts-split-state->right-name st))
                   :members right-members)
               left-struni-spec)
             st))
    :measure (struni-spec-count struni-spec))

  (define struct-declon-sts-split
    ((struct-declon struct-declonp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (struct-declon-annop struct-declon)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-struct-declon struct-declonp)
                 (right-struct-declon struct-declonp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a struct declaration."
    :long
    (xdoc::topstring-p
     "When @('splitp') is @('t') and the struct declaration is a member,
      its declarators are routed to the left and right struct declarations
      based on the member names
      (unnamed members always go left;
      see @(tsee struct-declor-sts-rightp));
      either side may end up with no declarators,
      in which case it should be discarded by the caller,
      except that a member declaration
      with no declarators in the first place
      (i.e. an anonymous struct/union member)
      is kept in the left struct declaration.
      The returned @('splitp') indicates whether such a split occurred.")
    (b* ((st (sts-split-state-fix st))
         ((reterr)
          nil
          (struct-declon-fix struct-declon)
          (struct-declon-fix struct-declon)
          st))
      (struct-declon-case
        struct-declon
        :member
        (b* (((erp specquals-splitp left-specquals - st)
              (spec/qual-list-sts-split struct-declon.specquals st))
             ((when specquals-splitp)
              (retmsg$ "INTERNAL ERROR. ~
                        The split struct type occurs in ~
                        a struct member declaration, ~
                        which should have been rejected upstream.~%~@0"
                       (context-msg-struct-declon
                         struct-declon
                         (sts-split-state->dialect st))))
             ((erp left-declors right-declors st)
              (struct-declor-list-sts-split splitp struct-declon.declors st))
             ((erp attribs st)
              (attrib-spec-list-sts-split struct-declon.attribs st))
             (left-struct-declon
               (c$::make-struct-declon-member
                 :extension struct-declon.extension
                 :specquals left-specquals
                 :declors left-declors
                 :attribs attribs)))
          (retok (and splitp t)
                 left-struct-declon
                 (if splitp
                     (c$::make-struct-declon-member
                       :extension struct-declon.extension
                       :specquals left-specquals
                       :declors right-declors
                       :attribs attribs)
                   left-struct-declon)
                 st))
        :statassert
        (b* (((when splitp)
              (retmsg$ "Static assertions are not supported ~
                        within a split structure type.~%~@0"
                       (context-msg-struct-declon
                         struct-declon
                         (sts-split-state->dialect st))))
             ((erp statassert st)
              (statassert-sts-split struct-declon.statassert st))
             (new-struct-declon
               (c$::make-struct-declon-statassert :statassert statassert)))
          (retok nil new-struct-declon new-struct-declon st))
        :empty
        (retok nil
               (struct-declon-fix struct-declon)
               (struct-declon-fix struct-declon)
               st)))
    :measure (struct-declon-count struct-declon))

  (define struct-declon-list-sts-split
    ((splitp booleanp)
     (struct-declons struct-declon-listp)
     (st sts-split-statep))
    :guard (struct-declon-list-annop struct-declons)
    :returns (mv (er? maybe-msgp)
                 (left-struct-declon-list struct-declon-listp)
                 (right-struct-declon-list struct-declon-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a struct declaration list."
    :long
    (xdoc::topstring-p
     "When @('splitp') is @('t'),
      member declarations whose declarators
      were all routed to the other side are dropped.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st)
         ((when (endp struct-declons))
          (retok nil nil st))
         ((erp dsplitp left-struct-declon right-struct-declon st)
          (struct-declon-sts-split (car struct-declons) splitp st))
         ((erp left-rest right-rest st)
          (struct-declon-list-sts-split splitp (cdr struct-declons) st))
         ((unless dsplitp)
          (retok (cons left-struct-declon left-rest)
                 (cons right-struct-declon right-rest)
                 st))
         ;; A member declaration with no declarators in the first place
         ;; (i.e. an anonymous struct/union member or an unnamed bit field)
         ;; stays in the left struct type
         ;; (it cannot be listed in the right member set);
         ;; it is not dropped from the left struct type,
         ;; unlike member declarations
         ;; whose declarators were all routed to the right.
         (orig-emptyp
           (and (struct-declon-case (car struct-declons) :member)
                (atom (c$::struct-declon-member->declors
                        (car struct-declons)))))
         (left-emptyp
           (and (not orig-emptyp)
                (struct-declon-case left-struct-declon :member)
                (atom (c$::struct-declon-member->declors
                        left-struct-declon))))
         (right-emptyp
           (and (struct-declon-case right-struct-declon :member)
                (atom (c$::struct-declon-member->declors
                        right-struct-declon)))))
      (retok (if left-emptyp
                 left-rest
               (cons left-struct-declon left-rest))
             (if right-emptyp
                 right-rest
               (cons right-struct-declon right-rest))
             st))
    :measure (struct-declon-list-count struct-declons))

  (define struct-declor-sts-split
    ((struct-declor struct-declorp)
     (splitp booleanp)
     (st sts-split-statep))
    :guard (struct-declor-annop struct-declor)
    :returns (mv (er? maybe-msgp)
                 (rightp booleanp)
                 (left-struct-declor struct-declorp)
                 (right-struct-declor struct-declorp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a struct declarator."
    :long
    (xdoc::topstring-p
     "When @('splitp') is @('t'),
      the struct declarator is routed to either @('left-struct-declor') or
      @('right-struct-declor') based on the member name;
      @('rightp') in the return indicates which.
      When @('splitp') is @('nil'), @('left-struct-declor') holds the result.")
    (b* ((st (sts-split-state-fix st))
         ((reterr)
          nil
          (struct-declor-fix struct-declor)
          (struct-declor-fix struct-declor)
          st)
         ((struct-declor struct-declor) struct-declor)
         ((erp left-declor? right-declor? st)
          (declor-option-sts-split struct-declor.declor? nil nil st))
         ((when right-declor?)
          (retmsg$ "INTERNAL ERROR. ~
                    A structure declarator was unexpectedly split.~%~@0"
                   (context-msg-struct-declor struct-declor
                                              (sts-split-state->dialect st))))
         ((erp left-expr? right-expr? st)
          (const-expr-option-sts-split struct-declor.expr? st))
         ((when right-expr?)
          (retmsg$ "Splits are not supported in bit-field widths.~%~@0"
                   (context-msg-struct-declor struct-declor
                                              (sts-split-state->dialect st))))
         (new-struct-declor (c$::make-struct-declor :declor? left-declor?
                                                    :expr? left-expr?
                                                    :info struct-declor.info))
         ((unless splitp)
          (retok nil new-struct-declor new-struct-declor st))
         (rightp (struct-declor-sts-rightp new-struct-declor st)))
      (retok rightp new-struct-declor new-struct-declor st))
    :measure (struct-declor-count struct-declor))

  (define struct-declor-list-sts-split
    ((splitp booleanp)
     (struct-declors struct-declor-listp)
     (st sts-split-statep))
    :guard (struct-declor-list-annop struct-declors)
    :returns (mv (er? maybe-msgp)
                 (left-struct-declor-list struct-declor-listp)
                 (right-struct-declor-list struct-declor-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a struct declarator list."
    :long
    (xdoc::topstring-p
     "When @('splitp') is @('t'),
      each struct declarator is routed to either the left or right list
      based on the member name.
      When @('splitp') is @('nil'),
      both lists hold the same transformed struct declarators.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st)
         ((when (endp struct-declors))
          (retok nil nil st))
         ((erp rightp left-struct-declor right-struct-declor st)
          (struct-declor-sts-split (car struct-declors) splitp st))
         ((erp left-rest right-rest st)
          (struct-declor-list-sts-split splitp (cdr struct-declors) st)))
      (cond ((not splitp)
             (retok (cons left-struct-declor left-rest)
                    (cons right-struct-declor right-rest)
                    st))
            (rightp
             (retok left-rest
                    (cons right-struct-declor right-rest)
                    st))
            (t
             (retok (cons left-struct-declor left-rest)
                    right-rest
                    st))))
    :measure (struct-declor-list-count struct-declors))

  (define enum-spec-sts-split
    ((enum-spec enum-specp)
     (st sts-split-statep))
    :guard (enum-spec-annop enum-spec)
    :returns (mv (er? maybe-msgp)
                 (enum-spec$ enum-specp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an enumeration specifier."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (enum-spec-fix enum-spec) st)
         ((enum-spec enum-spec) enum-spec)
         ((erp enumers st)
          (enumer-list-sts-split enum-spec.enumers st)))
      (retok (c$::change-enum-spec enum-spec :enumers enumers) st))
    :measure (enum-spec-count enum-spec))

  (define enumer-sts-split
    ((enumer enumerp)
     (st sts-split-statep))
    :guard (enumer-annop enumer)
    :returns (mv (er? maybe-msgp)
                 (enumer$ enumerp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an enumerator."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (enumer-fix enumer) st)
         ((enumer enumer) enumer)
         ((erp left-value? right-value? st)
          (const-expr-option-sts-split enumer.value? st))
         ((when right-value?)
          (retmsg$ "Splits are not supported in enumerator values.~%~@0"
                   (context-msg-enumer enumer (sts-split-state->dialect st)))))
      (retok (c$::change-enumer enumer :value? left-value?) st))
    :measure (enumer-count enumer))

  (define enumer-list-sts-split
    ((enumers enumer-listp)
     (st sts-split-statep))
    :guard (enumer-list-annop enumers)
    :returns (mv (er? maybe-msgp)
                 (enumers$ enumer-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an enumerator list."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (enumer-list-fix enumers) st)
         ((when (endp enumers))
          (retok nil st))
         ((erp head st)
          (enumer-sts-split (car enumers) st))
         ((erp rest st)
          (enumer-list-sts-split (cdr enumers) st)))
      (retok (cons head rest) st))
    :measure (enumer-list-count enumers))

  (define statassert-sts-split
    ((statassert statassertp)
     (st sts-split-statep))
    :guard (statassert-annop statassert)
    :returns (mv (er? maybe-msgp)
                 (statassert$ statassertp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a static assertion."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (statassert-fix statassert) st)
         ((statassert statassert) statassert)
         ((erp left-test right-test? st)
          (const-expr-sts-split statassert.test st))
         ((when right-test?)
          (retmsg$ "Splits are not supported in static assertions.~%~@0"
                   (context-msg-statassert statassert
                                           (sts-split-state->dialect st)))))
      (retok (c$::change-statassert statassert :test left-test) st))
    :measure (statassert-count statassert))

  (define attrib-list-sts-split
    ((attribs c$::attrib-listp)
     (st sts-split-statep))
    :guard (c$::attrib-list-annop attribs)
    :returns (mv (er? maybe-msgp)
                 (attribs$ c$::attrib-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a GCC attribute list."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (c$::attrib-list-fix attribs) st)
         ((when (endp attribs))
          (retok nil st))
         ((erp head st)
          (attrib-sts-split (car attribs) st))
         ((erp rest st)
          (attrib-list-sts-split (cdr attribs) st)))
      (retok (cons head rest) st))
    :measure (c$::attrib-list-count attribs))

  (define attrib-spec-sts-split
    ((attrib-spec c$::attrib-specp)
     (st sts-split-statep))
    :guard (c$::attrib-spec-annop attrib-spec)
    :returns (mv (er? maybe-msgp)
                 (attrib-spec$ c$::attrib-specp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a GCC attribute specifier."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (c$::attrib-spec-fix attrib-spec) st)
         ((erp attribs st)
          (attrib-list-sts-split (c$::attrib-spec->attribs attrib-spec) st)))
      (retok (c$::change-attrib-spec attrib-spec :attribs attribs) st))
    :measure (c$::attrib-spec-count attrib-spec))

  (define attrib-spec-list-sts-split
    ((attrib-specs attrib-spec-listp)
     (st sts-split-statep))
    :guard (c$::attrib-spec-list-annop attrib-specs)
    :returns (mv (er? maybe-msgp)
                 (attrib-specs$ attrib-spec-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a GCC attribute specifier list."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (c$::attrib-spec-list-fix attrib-specs) st)
         ((when (endp attrib-specs))
          (retok nil st))
         ((erp head st)
          (attrib-spec-sts-split (car attrib-specs) st))
         ((erp rest st)
          (attrib-spec-list-sts-split (cdr attrib-specs) st)))
      (retok (cons head rest) st))
    :measure (c$::attrib-spec-list-count attrib-specs))

  (define init-declor-sts-split
    ((init-declor init-declorp)
     (st sts-split-statep))
    :guard (init-declor-annop init-declor)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-init-declor init-declorp)
                 (right-init-declor init-declorp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an initializer declarator."
    (b* ((st (sts-split-state-fix st))
         ((reterr)
          nil
          (init-declor-fix init-declor)
          (init-declor-fix init-declor)
          st)
         ((init-declor init-declor) init-declor)
         ((c$::init-declor-vinfo info) init-declor.info)
         ((mv erp type-splitp)
          (sts-check-type info.type st))
         ((when erp)
          (retmsg$ "~@0~%~@1"
                   erp
                   (context-msg-init-declor init-declor
                                            (sts-split-state->dialect st))))
         (splitp type-splitp)
         ((when (and splitp init-declor.asm?))
          (retmsg$ "Splits are not supported alongside ~
                    assembler name specifiers.~%~@0"
                   (context-msg-init-declor init-declor
                                            (sts-split-state->dialect st))))
         ((erp left-declor right-declor? st)
          (declor-sts-split init-declor.declor
                            splitp
                            (and splitp info.uid)
                            st))
         ((when (xor splitp right-declor?))
          (retmsg$ "INTERNAL ERROR. ~
                    An initializer declarator was split ~
                    contrary to its declared type, or vice versa.~%~@0"
                   (context-msg-init-declor init-declor
                                            (sts-split-state->dialect st))))
         ((erp attribs st)
          (attrib-spec-list-sts-split init-declor.attribs st))
         ((erp left-initer? right-initer? st)
          (initer-option-sts-split init-declor.initer? splitp st))
         ((when (and right-initer? (not splitp)))
          (retmsg$ "INTERNAL ERROR. ~
                    The initializer of an initializer declarator was split ~
                    contrary to its declared type.~%~@0"
                   (context-msg-init-declor init-declor
                                            (sts-split-state->dialect st))))
         ((when (and splitp left-initer? (not right-initer?)))
          (retmsg$ "Failed to split the initializer of ~
                    an initializer declarator of splittable type.~%~@0"
                   (context-msg-init-declor init-declor
                                            (sts-split-state->dialect st))))
         (left-init-declor
           (c$::make-init-declor :declor left-declor
                                 :asm? init-declor.asm?
                                 :attribs attribs
                                 :initer? left-initer?
                                 :info init-declor.info)))
      (retok splitp
             left-init-declor
             (if (and splitp right-declor?)
                 (c$::make-init-declor :declor right-declor?
                                       :asm? nil
                                       :attribs attribs
                                       :initer? right-initer?
                                       :info init-declor.info)
               left-init-declor)
             st))
    :measure (init-declor-count init-declor))

  (define init-declor-list-sts-split
    ((init-declors init-declor-listp)
     (st sts-split-statep))
    :guard (init-declor-list-annop init-declors)
    :returns (mv (er? maybe-msgp)
                 (left-init-declor-list init-declor-listp)
                 (right-init-declor-list init-declor-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform an initializer declarator list."
    :long
    (xdoc::topstring-p
     "The left list holds the transformed initializer declarators;
      the right list holds the right counterparts
      of just those initializer declarators which split.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil nil st)
         ((when (endp init-declors))
          (retok nil nil st))
         ((erp isplitp left-init-declor right-init-declor st)
          (init-declor-sts-split (car init-declors) st))
         ((erp left-rest right-rest st)
          (init-declor-list-sts-split (cdr init-declors) st)))
      (retok (cons left-init-declor left-rest)
             (if isplitp
                 (cons right-init-declor right-rest)
               right-rest)
             st))
    :measure (init-declor-list-count init-declors))

  (define declon-sts-split
    ((declon declonp)
     (st sts-split-statep))
    :guard (declon-annop declon)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-declon declonp)
                 (right-declon declonp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a declaration."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil (declon-fix declon) (declon-fix declon) st))
      (declon-case
        declon
        :declon
        ;; The declarators are processed before the specifiers
        ;; to determine whether the declaration splits.
        ;; The declaration also splits when the specifiers split,
        ;; i.e. when they include a type specifier
        ;; denoting the target struct type,
        ;; even if there are no declarators.
        (b* (((erp left-declors right-declors st)
              (init-declor-list-sts-split declon.declors st))
             (declors-splitp (and (consp right-declors) t))
             ((erp specs-splitp left-specs right-specs st)
              (decl-spec-list-sts-split declon.specs st))
             (splitp (or declors-splitp specs-splitp))
             (left-declon
               (c$::make-declon-declon :extension declon.extension
                                       :specs left-specs
                                       :declors left-declors)))
          (retok splitp
                 left-declon
                 (if splitp
                     (c$::make-declon-declon :extension declon.extension
                                             :specs right-specs
                                             :declors right-declors)
                   left-declon)
                 st))
        :statassert
        (b* (((erp statassert st)
              (statassert-sts-split declon.statassert st))
             (new-declon (c$::make-declon-statassert :statassert statassert)))
          (retok nil new-declon new-declon st))))
    :measure (declon-count declon))

  (define label-sts-split
    ((label labelp)
     (st sts-split-statep))
    :guard (label-annop label)
    :returns (mv (er? maybe-msgp)
                 (label$ labelp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a label."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (label-fix label) st))
      (label-case
        label
        :name
        (b* (((erp attribs st)
              (attrib-spec-list-sts-split label.attribs st)))
          (retok (make-label-name :name label.name :attribs attribs) st))
        :casexpr
        (b* (((erp left-expr right-expr? st)
              (const-expr-sts-split label.expr st))
             ((when right-expr?)
              (retmsg$ "Splits are not supported in case labels.~%~@0"
                       (context-msg-label label
                                          (sts-split-state->dialect st))))
             ((erp left-range? right-range? st)
              (const-expr-option-sts-split label.range? st))
             ((when right-range?)
              (retmsg$ "Splits are not supported in case labels.~%~@0"
                       (context-msg-label label
                                          (sts-split-state->dialect st)))))
          (retok (make-label-casexpr :expr left-expr :range? left-range?) st))
        :default (retok (label-fix label) st)))
    :measure (label-count label))

  (define stmt-sts-split
    ((stmt stmtp)
     (st sts-split-statep))
    :guard (stmt-annop stmt)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-stmt stmtp)
                 (right-stmt stmtp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a statement."
    :long
    (xdoc::topstring-p
     "Only expression statements (and labeled statements wrapping them)
      propagate splits upward, to be spliced into
      the surrounding block item list.
      A split branch or body of a selection or iteration statement
      is absorbed into a compound statement.
      Splits in control positions
      (tests, @('goto') label expressions, @('return') expressions,
      and @('for') loop initializers and update expressions)
      are not supported.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil (stmt-fix stmt) (stmt-fix stmt) st))
      (stmt-case
        stmt
        :labeled
        (b* (((erp label st)
              (label-sts-split stmt.label st))
             ((erp ssplitp left-inner right-inner st)
              (stmt-sts-split stmt.stmt st))
             (left-stmt (c$::make-stmt-labeled :label label
                                               :stmt left-inner)))
          (retok ssplitp
                 left-stmt
                 (if ssplitp right-inner left-stmt)
                 st))
        :compound
        (b* (((erp comp-stmt st)
              (comp-stmt-sts-split stmt.stmt st))
             (new-stmt (c$::make-stmt-compound :stmt comp-stmt)))
          (retok nil new-stmt new-stmt st))
        :expr
        (b* (((erp left-expr? right-expr? st)
              (expr-option-sts-split stmt.expr? st))
             (left-stmt (c$::make-stmt-expr :expr? left-expr?
                                            :info stmt.info)))
          (retok (if right-expr? t nil)
                 left-stmt
                 (if right-expr?
                     (c$::make-stmt-expr :expr? right-expr?
                                         :info stmt.info)
                   left-stmt)
                 st))
        :null-attrib
        (b* (((erp attrib st)
              (attrib-spec-sts-split stmt.attrib st))
             (new-stmt (c$::make-stmt-null-attrib :attrib attrib)))
          (retok nil new-stmt new-stmt st))
        :if
        (b* (((erp left-test right-test? st)
              (expr-sts-split stmt.test st))
             ((when right-test?)
              (retmsg$ "Splits are not supported in if tests.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp tsplitp left-then right-then st)
              (stmt-sts-split stmt.then st))
             (then (if tsplitp
                       (stmts-to-compound left-then right-then)
                     left-then))
             (new-stmt (c$::make-stmt-if :test left-test :then then)))
          (retok nil new-stmt new-stmt st))
        :ifelse
        (b* (((erp left-test right-test? st)
              (expr-sts-split stmt.test st))
             ((when right-test?)
              (retmsg$ "Splits are not supported in if tests.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp tsplitp left-then right-then st)
              (stmt-sts-split stmt.then st))
             (then (if tsplitp
                       (stmts-to-compound left-then right-then)
                     left-then))
             ((erp esplitp left-else right-else st)
              (stmt-sts-split stmt.else st))
             (else (if esplitp
                       (stmts-to-compound left-else right-else)
                     left-else))
             (new-stmt (c$::make-stmt-ifelse :test left-test
                                             :then then
                                             :else else)))
          (retok nil new-stmt new-stmt st))
        :switch
        (b* (((erp left-target right-target? st)
              (expr-sts-split stmt.target st))
             ((when right-target?)
              (retmsg$ "Splits are not supported in switch targets.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp bsplitp left-body right-body st)
              (stmt-sts-split stmt.body st))
             (body (if bsplitp
                       (stmts-to-compound left-body right-body)
                     left-body))
             (new-stmt (c$::make-stmt-switch :target left-target
                                             :body body)))
          (retok nil new-stmt new-stmt st))
        :while
        (b* (((erp left-test right-test? st)
              (expr-sts-split stmt.test st))
             ((when right-test?)
              (retmsg$ "Splits are not supported in loop tests.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp bsplitp left-body right-body st)
              (stmt-sts-split stmt.body st))
             (body (if bsplitp
                       (stmts-to-compound left-body right-body)
                     left-body))
             (new-stmt (c$::make-stmt-while :test left-test :body body)))
          (retok nil new-stmt new-stmt st))
        :dowhile
        (b* (((erp bsplitp left-body right-body st)
              (stmt-sts-split stmt.body st))
             (body (if bsplitp
                       (stmts-to-compound left-body right-body)
                     left-body))
             ((erp left-test right-test? st)
              (expr-sts-split stmt.test st))
             ((when right-test?)
              (retmsg$ "Splits are not supported in loop tests.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             (new-stmt (c$::make-stmt-dowhile :body body :test left-test)))
          (retok nil new-stmt new-stmt st))
        :for-expr
        (b* (((erp left-init? right-init? st)
              (expr-option-sts-split stmt.init st))
             ((when right-init?)
              (retmsg$ "Splits are not supported in for loop initializers.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp left-test? right-test? st)
              (expr-option-sts-split stmt.test st))
             ((when right-test?)
              (retmsg$ "Splits are not supported in loop tests.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp left-next? right-next? st)
              (expr-option-sts-split stmt.next st))
             ((when right-next?)
              (retmsg$ "Splits are not supported in ~
                        for loop update expressions.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp bsplitp left-body right-body st)
              (stmt-sts-split stmt.body st))
             (body (if bsplitp
                       (stmts-to-compound left-body right-body)
                     left-body))
             (new-stmt (c$::make-stmt-for-expr :init left-init?
                                               :test left-test?
                                               :next left-next?
                                               :body body)))
          (retok nil new-stmt new-stmt st))
        :for-declon
        (b* (((erp dsplitp left-init ?right-init st)
              (declon-sts-split stmt.init st))
             ((when dsplitp)
              (retmsg$ "Splits are not supported in for loop initializers.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp left-test? right-test? st)
              (expr-option-sts-split stmt.test st))
             ((when right-test?)
              (retmsg$ "Splits are not supported in loop tests.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp left-next? right-next? st)
              (expr-option-sts-split stmt.next st))
             ((when right-next?)
              (retmsg$ "Splits are not supported in ~
                        for loop update expressions.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             ((erp bsplitp left-body right-body st)
              (stmt-sts-split stmt.body st))
             (body (if bsplitp
                       (stmts-to-compound left-body right-body)
                     left-body))
             (new-stmt (c$::make-stmt-for-declon :init left-init
                                                 :test left-test?
                                                 :next left-next?
                                                 :body body)))
          (retok nil new-stmt new-stmt st))
        :for-ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")
        :goto
        (retok nil (stmt-fix stmt) (stmt-fix stmt) st)
        :gotoe
        (b* (((erp left-label right-label? st)
              (expr-sts-split stmt.label st))
             ((when right-label?)
              (retmsg$ "Splits are not supported in ~
                        goto label expressions.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             (new-stmt (c$::make-stmt-gotoe :label left-label)))
          (retok nil new-stmt new-stmt st))
        :continue
        (retok nil (stmt-fix stmt) (stmt-fix stmt) st)
        :break
        (retok nil (stmt-fix stmt) (stmt-fix stmt) st)
        :return
        (b* (((erp left-expr? right-expr? st)
              (expr-option-sts-split stmt.expr? st))
             ((when right-expr?)
              (retmsg$ "Splits are not supported in return statements.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             (new-stmt (c$::make-stmt-return :expr? left-expr?
                                             :info stmt.info)))
          (retok nil new-stmt new-stmt st))
        :return-attrib
        (b* (((erp attrib st)
              (attrib-spec-sts-split stmt.attrib st))
             ((erp left-expr right-expr? st)
              (expr-sts-split stmt.expr st))
             ((when right-expr?)
              (retmsg$ "Splits are not supported in return statements.~%~@0"
                       (context-msg-stmt stmt (sts-split-state->dialect st))))
             (new-stmt (c$::make-stmt-return-attrib :attrib attrib
                                                    :expr left-expr)))
          (retok nil new-stmt new-stmt st))
        :asm
        (b* ((st (sts-split-state-add-warning
                   (msg$ "Not transforming assembler statement.~%~@0"
                         (context-msg-stmt stmt (sts-split-state->dialect st)))
                   st)))
          (retok nil (stmt-fix stmt) (stmt-fix stmt) st))))
    :measure (stmt-count stmt))

  (define comp-stmt-sts-split
    ((comp-stmt comp-stmtp)
     (st sts-split-statep))
    :guard (comp-stmt-annop comp-stmt)
    :returns (mv (er? maybe-msgp)
                 (comp-stmt$ comp-stmtp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a compound statement."
    (b* ((st (sts-split-state-fix st))
         ((reterr) (c$::comp-stmt-fix comp-stmt) st)
         ((erp items st)
          (block-item-list-sts-split (c$::comp-stmt->items comp-stmt) st)))
      (retok (c$::change-comp-stmt comp-stmt :items items) st))
    :measure (comp-stmt-count comp-stmt))

  (define block-item-sts-split
    ((block-item block-itemp)
     (st sts-split-statep))
    :guard (block-item-annop block-item)
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (left-block-item block-itemp)
                 (right-block-item block-itemp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a block item."
    (b* ((st (sts-split-state-fix st))
         ((reterr) nil (block-item-fix block-item) (block-item-fix block-item) st))
      (block-item-case
        block-item
        :declon
        (b* (((erp dsplitp left-declon right-declon st)
              (declon-sts-split block-item.declon st))
             (left-block-item
               (c$::make-block-item-declon :declon left-declon
                                           :info block-item.info)))
          (retok dsplitp
                 left-block-item
                 (if dsplitp
                     (c$::make-block-item-declon :declon right-declon
                                                 :info block-item.info)
                   left-block-item)
                 st))
        :stmt
        (b* (((erp ssplitp left-stmt right-stmt st)
              (stmt-sts-split block-item.stmt st))
             (left-block-item
               (c$::make-block-item-stmt :stmt left-stmt
                                         :info block-item.info)))
          (retok ssplitp
                 left-block-item
                 (if ssplitp
                     (c$::make-block-item-stmt :stmt right-stmt
                                               :info block-item.info)
                   left-block-item)
                 st))
        :ambig
        (retmsg$ "Ambiguous ASTs are unsupported.")))
    :measure (block-item-count block-item))

  (define block-item-list-sts-split
    ((block-items block-item-listp)
     (st sts-split-statep))
    :guard (block-item-list-annop block-items)
    :returns (mv (er? maybe-msgp)
                 (block-items$ block-item-listp)
                 (st$ sts-split-statep))
    :parents (sts-split)
    :short "Transform a block item list."
    :long
    (xdoc::topstring-p
     "Splits within block items are spliced in-place.")
    (b* ((st (sts-split-state-fix st))
         ((reterr) (block-item-list-fix block-items) st)
         ((when (endp block-items))
          (retok nil st))
         ((erp splitp left right st)
          (block-item-sts-split (car block-items) st))
         ((erp rest st)
          (block-item-list-sts-split (cdr block-items) st)))
      (if splitp
          (retok (list* left right rest) st)
        (retok (cons left rest) st)))
    :measure (block-item-list-count block-items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable xor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-sts-split
  ((fundef fundefp)
   (st sts-split-statep))
  :guard (c$::fundef-annop fundef)
  :returns (mv (er? maybe-msgp)
               (fundef$ fundefp)
               (st$ sts-split-statep))
  :short "Transform a function definition."
  (b* ((st (sts-split-state-fix st))
       ((reterr) (c$::fundef-fix fundef) st)
       ((fundef fundef) fundef)
       ((when fundef.declons)
        (retmsg$ "K&R-style function definitions are not supported.~%~@0"
                 (context-msg-fundef fundef (sts-split-state->dialect st))))
       ((erp specs-splitp left-specs - st)
        (decl-spec-list-sts-split fundef.specs st))
       ((when specs-splitp)
        (retmsg$ "The split struct type is not supported in ~
                  the return type of a function definition.~%~@0"
                 (context-msg-fundef fundef (sts-split-state->dialect st))))
       ((erp left-declor right-declor? st)
        (declor-sts-split fundef.declor nil nil st))
       ((when right-declor?)
        (retmsg$ "INTERNAL ERROR. ~
                  A function declarator was unexpectedly split.~%~@0"
                 (context-msg-fundef fundef (sts-split-state->dialect st))))
       ((erp attribs st)
        (attrib-spec-list-sts-split fundef.attribs st))
       ((erp body st)
        (comp-stmt-sts-split fundef.body st)))
    (retok (c$::make-fundef :extension fundef.extension
                            :specs left-specs
                            :declor left-declor
                            :asm? fundef.asm?
                            :attribs attribs
                            :declons nil
                            :body body
                            :info fundef.info)
           st)))

(define ext-declon-sts-split
  ((ext-declon ext-declonp)
   (st sts-split-statep))
  :guard (c$::ext-declon-annop ext-declon)
  :returns (mv (er? maybe-msgp)
               (splitp booleanp)
               (left-ext-declon ext-declonp)
               (right-ext-declon ext-declonp)
               (st$ sts-split-statep))
  :short "Transform an external declaration."
  (b* ((st (sts-split-state-fix st))
       ((reterr)
        nil
        (c$::ext-declon-fix ext-declon)
        (c$::ext-declon-fix ext-declon)
        st))
    (ext-declon-case
      ext-declon
      :fundef
      (b* (((erp fundef st)
            (fundef-sts-split ext-declon.fundef st))
           (new-ext-declon (c$::make-ext-declon-fundef :fundef fundef)))
        (retok nil new-ext-declon new-ext-declon st))
      :declon
      (b* (((erp dsplitp left-declon right-declon st)
            (declon-sts-split ext-declon.declon st))
           (left-ext-declon (c$::make-ext-declon-declon :declon left-declon)))
        (retok dsplitp
               left-ext-declon
               (if dsplitp
                   (c$::make-ext-declon-declon :declon right-declon)
                 left-ext-declon)
               st))
      :empty
      (retok nil
             (c$::ext-declon-fix ext-declon)
             (c$::ext-declon-fix ext-declon)
             st)
      :asm
      (b* ((st (sts-split-state-add-warning
                 (msg$ "Not transforming assembler statement.~%~@0"
                       (context-msg-asm-stmt ext-declon.stmt
                                             (sts-split-state->dialect st)))
                 st)))
        (retok nil
               (c$::ext-declon-fix ext-declon)
               (c$::ext-declon-fix ext-declon)
               st)))))

(define trans-item-sts-split
  ((item trans-itemp)
   (st sts-split-statep))
  :guard (c$::trans-item-annop item)
  :returns (mv (er? maybe-msgp)
               (items trans-item-listp)
               (st$ sts-split-statep))
  :short "Transform a translation item."
  :long
  (xdoc::topstring-p
   "An external declaration which splits
    becomes two translation items.")
  (b* ((st (sts-split-state-fix st))
       ((reterr) nil st))
    (trans-item-case
      item
      :declon
      (b* (((erp splitp left-ext-declon right-ext-declon st)
            (ext-declon-sts-split item.declon st)))
        (retok (c$::trans-item-list-declon
                 (if splitp
                     (list left-ext-declon right-ext-declon)
                   (list left-ext-declon)))
               st))
      :include (retmsg$ "#include directives are not supported.")
      :define (retmsg$ "#define directives are not supported.")
      :undef (retmsg$ "#undef directives are not supported.")
      :cond (retmsg$ "Conditional directives are not supported.")
      :line-comment (retok (list (trans-item-fix item)) st)))
  ///

  (more-returns
   (items true-listp
          :rule-classes :type-prescription
          :hints (("Goal"
                   :use trans-item-listp-of-trans-item-sts-split.items
                   :in-theory
                   '(c$::true-listp-when-trans-item-listp-compound-recognizer))))))

(define trans-item-list-sts-split
  ((items trans-item-listp)
   (st sts-split-statep))
  :guard (c$::trans-item-list-annop items)
  :returns (mv (er? maybe-msgp)
               (items$ trans-item-listp)
               (st$ sts-split-statep))
  :short "Transform a translation item list."
  (b* ((st (sts-split-state-fix st))
       ((reterr) nil st)
       ((when (endp items))
        (retok nil st))
       ((erp first-items st)
        (trans-item-sts-split (car items) st))
       ((erp rest-items st)
        (trans-item-list-sts-split (cdr items) st)))
    (retok (append first-items rest-items) st)))

(define trans-unit-sts-split
  ((tunit trans-unitp)
   (st sts-split-statep))
  :guard (c$::trans-unit-annop tunit)
  :returns (mv (er? maybe-msgp)
               (tunit$ trans-unitp)
               (st$ sts-split-statep))
  :short "Transform a translation unit."
  (b* ((st (sts-split-state-fix st))
       ((reterr) (c$::irr-trans-unit) st)
       ((trans-unit tunit) tunit)
       ((erp items st)
        (trans-item-list-sts-split tunit.items st)))
    (retok (make-trans-unit :items items :info tunit.info) st)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-find-tag-info-in-valid-table
  ((tag identp)
   (table c$::valid-tablep))
  :returns (mv (er? maybe-msgp)
               (info? c$::valid-tag-info-optionp
                      :hints
                      (("Goal"
                        :in-theory (enable c$::valid-tag-info-optionp)))))
  :short "Find the validation information of a tag
          in the file scope of a validation table."
  :long
  (xdoc::topstring-p
   "We return @('nil') if the tag is not found at file scope.
    This benign case, in which callers may wish to look elsewhere,
    is distinguished from more serious errors,
    namely ill-formed validation tables,
    which are signaled with an error message.")
  (b* (((reterr) nil)
       (scopes (c$::valid-table->scopes table))
       ((when (endp scopes))
        (retmsg$ "Ill-formed validation table: no scope found."))
       ((unless (endp (rest scopes)))
        (retmsg$ "Ill-formed validation table: ~
                  more than one scope found: ~x0"
                 scopes))
       (scope (first scopes))
       (lookup (assoc-equal (c$::ident-fix tag)
                            (c$::valid-scope->tag scope))))
    (retok (and lookup
                (c$::valid-tag-info-fix (cdr lookup))))))

(define sts-find-struct-uid-search
  ((tag identp)
   (tunits filepath-trans-unit-mapp))
  :guard (c$::filepath-trans-unit-map-annop tunits)
  :returns (mv (er? maybe-msgp)
               (uid c$::uidp)
               (filepath filepathp))
  :short "Search the translation units for a struct type with the given tag."
  (b* (((reterr) (c$::irr-uid) (filepath ""))
       ((when (omap::emptyp tunits))
        (retmsg$ "A struct type with tag ~x0 does not exist."
                 (c$::ident-fix tag)))
       (filepath (c$::filepath-fix (omap::head-key tunits)))
       (tunit (omap::head-val tunits))
       ((erp info?)
        (sts-find-tag-info-in-valid-table
          tag
          (c$::trans-unit-vinfo->table-end (c$::trans-unit->info tunit))))
       ((when (and info?
                   (c$::tag-kind-case (c$::valid-tag-info->kind info?)
                                      :struct)))
        (retok (c$::valid-tag-info->uid info?) filepath)))
    (sts-find-struct-uid-search tag (omap::tail tunits))))

(define sts-find-struct-uid
  ((filepath? c$::filepath-optionp)
   (tag identp)
   (tunits trans-ensemblep))
  :guard (c$::trans-ensemble-annop tunits)
  :returns (mv (er? maybe-msgp)
               (uid c$::uidp)
               (filepath filepathp))
  :short "Find the unique identifier of the struct type with the given tag."
  :long
  (xdoc::topstring-p
   "If @('filepath?') is provided, only that translation unit is consulted.
    Otherwise, the translation units are searched in order,
    and the first with a matching struct type at file scope is used.
    The filepath of the translation unit
    in which the struct type was found is also returned.")
  (b* (((reterr) (c$::irr-uid) (filepath ""))
       (unwrapped-tunits (trans-ensemble->units tunits))
       ((unless filepath?)
        (sts-find-struct-uid-search tag unwrapped-tunits))
       (lookup (omap::assoc filepath? unwrapped-tunits))
       ((unless lookup)
        (retmsg$ "Provided filepath ~x0 does not exist in the ~
                  translation unit ensemble."
                 filepath?))
       (tunit (cdr lookup))
       ((erp info?)
        (sts-find-tag-info-in-valid-table
          tag
          (c$::trans-unit-vinfo->table-end (c$::trans-unit->info tunit))))
       ((unless info?)
        (retmsg$ "The struct tag ~x0 was not found at file scope."
                 (c$::ident-fix tag)))
       ((c$::valid-tag-info info) info?)
       ((unless (c$::tag-kind-case info.kind :struct))
        (retmsg$ "The tag ~x0 names a union type, not a struct type."
                 (c$::ident-fix tag))))
    (retok info.uid (c$::filepath-fix filepath?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-split-trans-units
  ((tag identp)
   (primary-type c$::typep)
   (completions c$::type-completions-p)
   (ienv c$::ienvp)
   (tunits filepath-trans-unit-mapp)
   (st sts-split-statep))
  :guard (c$::filepath-trans-unit-map-annop tunits)
  :returns (mv (er? maybe-msgp)
               (tunits$ filepath-trans-unit-mapp)
               (st$ sts-split-statep))
  :short "Split compatible struct types in the translation units."
  :long
  (xdoc::topstring-p
   "For each translation unit,
    we look up the unique identifier, if any,
    which the tag denotes at file scope.
    If there is one, and its struct type is compatible
    with the primary struct type,
    the translation unit is transformed
    with respect to that unique identifier;
    otherwise, the translation unit is left unchanged.
    The state is threaded through the passes:
    in particular, its ident map ensures that
    declarations of the same external object
    in different translation units
    (which share a unique identifier)
    receive the same right name.
    Note that we assume that at most one struct type
    per translation unit is subject to the split,
    namely the one denoted by the tag at file scope.
    In particular, struct types declared in block scopes
    are not considered:
    a block-scope struct type in another translation unit
    may be compatible with the primary struct type,
    but it is not detected or split
    (see the current limitations in @(see struct-type-split)).
    This holds in C17, in which struct types declared in different scopes
    of the same translation unit are never compatible.
    It does not generally hold in C23,
    in which struct types in different scopes
    of the same translation unit may be compatible;
    we do not support that yet,
    and so @(tsee sts-split-code-ensemble) checks that
    the C standard is C17.")
  (b* (((reterr) nil (sts-split-state-fix st))
       ((when (omap::emptyp tunits))
        (retok nil (sts-split-state-fix st)))
       (filepath (c$::filepath-fix (omap::head-key tunits)))
       (tunit (omap::head-val tunits))
       ((erp info?)
        (sts-find-tag-info-in-valid-table
          tag
          (c$::trans-unit-vinfo->table-end (c$::trans-unit->info tunit))))
       (structp (and info?
                     (c$::tag-kind-case (c$::valid-tag-info->kind info?)
                                        :struct)))
       (uid (if structp
                (c$::valid-tag-info->uid info?)
              (c$::irr-uid)))
       (current-type
         (c$::make-type-struct
           :uid uid
           :tunit? (c$::filepath-fix filepath)
           :tag/members (c$::make-type-struni-tag/members-tagged :tag tag)))
       ((when (or (not structp)
                  (not (c$::type-compatible-p
                         primary-type
                         current-type
                         completions
                         ienv))))
        ;; The tag does not denote a compatible struct type
        ;; in this translation unit, which is left unchanged.
        (b* (((erp rest st)
              (sts-split-trans-units
                tag primary-type completions ienv (omap::tail tunits) st)))
          (retok (omap::update filepath (c$::trans-unit-fix tunit) rest)
                 st)))
       (st (change-sts-split-state st :filepath filepath))
       (msg? (sts-check-completions completions uid))
       ((when msg?)
        (reterr (sts-error-in-translation-unit msg? st)))
       ((mv erp tunit st)
        (trans-unit-sts-split tunit
                              (change-sts-split-state st :struct-uid uid)))
       ((when erp)
        (reterr (sts-error-in-translation-unit erp st)))
       ((erp rest st)
        (sts-split-trans-units
          tag primary-type completions ienv (omap::tail tunits) st)))
    (retok (omap::update filepath tunit rest) st))
  :guard-debug t
  :verify-guards :after-returns
  :guard-hints
  (("Goal" :in-theory (enable c$::filepath-trans-unit-map-annop
                              c$::trans-unit-annop))))

(define sts-split-code-ensemble
  ((tag identp)
   (filepath? c$::filepath-optionp)
   (right-members ident-listp)
   (right-name? ident-optionp)
   (code code-ensemblep))
  :guard (code-ensemble-annop code)
  :returns (mv (er? maybe-msgp)
               (code$ code-ensemblep)
               (warnings acl2::msg-listp))
  :short "Split a struct type in a code ensemble."
  :long
  (xdoc::topstring-p
   "The primary struct type to split is identified by its tag,
    within the translation unit named by @('filepath?') if provided,
    and otherwise within the first translation unit
    defining a struct type with that tag.
    Compatible struct types with the same tag
    in other translation units are also split,
    one translation unit at a time
    (at most one struct type per translation unit may be split;
    see @(tsee sts-split-trans-units)).
    The members in @('right-members') are split off
    into a new right struct type,
    whose tag is a fresh identifier
    based on @('right-name?') if provided,
    and on the original tag otherwise.
    The code ensemble must use the C17 standard,
    since the transformation assumes the C17 rules
    for struct type compatibility.
    After transforming, we re-validate the resulting translation units,
    refreshing their validation annotations
    so that they may be used further.
    We also return the accumulated warnings,
    in reverse chronological order.")
  (b* (((reterr) (c$::irr-code-ensemble) nil)
       ((code-ensemble code) code)
       ;; The transformation assumes the C17 rules
       ;; for struct type compatibility;
       ;; see sts-split-trans-units.
       ((unless (c::standard-case (c$::ienv->std code.ienv) :c17))
        (retmsg$ "Only the C17 standard is currently supported, ~
                  but the code ensemble uses the standard ~x0."
                 (c$::ienv->std code.ienv)))
       ((erp primary-uid primary-filepath)
        (sts-find-struct-uid filepath? tag code.trans-units))
       (info (c$::trans-ensemble->info code.trans-units))
       ;; type-compatible-p accesses the completions with hons-get,
       ;; so they must be a fast alist.
       (completions (make-fast-alist
                      (c$::trans-ensemble-vinfo->completions info)))
       (primary-type
         (c$::make-type-struct
           :uid primary-uid
           :tunit? (c$::filepath-fix primary-filepath)
           :tag/members (c$::make-type-struni-tag/members-tagged :tag tag)))
       (map (trans-ensemble->units code.trans-units))
       (blacklist (filepath-trans-unit-map-collect-idents map))
       (right-name (fresh-ident (or right-name? tag) blacklist))
       (st (make-sts-split-state
             :struct-uid primary-uid
             :right-set (mergesort right-members)
             :right-name right-name
             :dialect (c$::ienv->dialect code.ienv)
             :ienv code.ienv
             :blacklist (insert right-name blacklist)
             :ident-map nil
             :warnings nil
             :filepath (c$::irr-filepath)))
       ((erp map st)
        (sts-split-trans-units tag primary-type completions code.ienv map st))
       (- (fast-alist-free completions))
       (warnings (sts-split-state->warnings st))
       (new-trans-units (c$::change-trans-ensemble code.trans-units
                                                   :units map))
       ;; Re-validate the transformed translation units,
       ;; refreshing their validation annotations for further use.
       ((unless (c$::trans-ensemble-unambp new-trans-units))
        (retmsg$ "Internal error: the transformed code is ambiguous."))
       ((erp new-trans-units)
        (c$::valid-trans-ensemble new-trans-units code.ienv nil))
       ;; TODO: remove once it is proved that validation produces
       ;; an annotated term.
       ((unless (c$::trans-ensemble-annop new-trans-units))
        (retmsg$ "Internal error: the transformed code is invalid.")))
    (retok (change-code-ensemble code :trans-units new-trans-units)
           warnings)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing struct-type-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-split-process-inputs (const-old
                                  const-new
                                  struct-tag
                                  filepath
                                  right-members
                                  new-tag
                                  print-warnings
                                  (wrld plist-worldp))
  :returns (mv (er? maybe-msgp)
               (code code-ensemblep)
               (tag identp)
               (filepath? c$::filepath-optionp)
               (right-members ident-listp)
               (new-tag? ident-optionp)
               (print-warnings$ booleanp)
               (const-new$ symbolp))
  :short "Process the inputs."
  (b* (((reterr) (c$::irr-code-ensemble) (c$::irr-ident) nil nil nil nil nil)
       ((unless (symbolp const-old))
        (retmsg$ "~x0 must be a symbol." const-old))
       (code (acl2::constant-value const-old wrld))
       ((unless (code-ensemblep code))
        (retmsg$ "~x0 must be a code ensemble." const-old))
       ((unless (code-ensemble-annop code))
        (retmsg$ "~x0 must be annotated with validation information."
                 const-old))
       ((unless (stringp struct-tag))
        (retmsg$ "~x0 must be a string." struct-tag))
       (tag (c$::ident struct-tag))
       ((unless (or (not filepath)
                    (stringp filepath)))
        (retmsg$ "~x0 must be nil or a string." filepath))
       (filepath? (and filepath (filepath filepath)))
       ((unless (string-listp right-members))
        (retmsg$ "~x0 must be a list of strings." right-members))
       ((unless (consp right-members))
        (retmsg$ "At least one right member must be specified."))
       (right-members (c$::string-list-map-ident right-members))
       ((unless (or (not new-tag)
                    (stringp new-tag)))
        (retmsg$ "~x0 must be nil or a string." new-tag))
       (new-tag? (and new-tag (c$::ident new-tag)))
       ((unless (booleanp print-warnings))
        (retmsg$ "~x0 must be a boolean." print-warnings))
       ((unless (symbolp const-new))
        (retmsg$ "~x0 must be a symbol." const-new)))
    (retok code tag filepath? right-members new-tag? print-warnings const-new))
  ///

  (defret code-ensemble-annop-of-sts-split-process-inputs.code
    (implies (not er?)
             (code-ensemble-annop code))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation struct-type-split)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-print-warnings-loop ((warnings acl2::msg-listp))
  :short "Print warnings in list order."
  (b* (((when (endp warnings)) nil)
       (- (cw "WARNING: ~@0~%" (first warnings))))
    (sts-print-warnings-loop (rest warnings))))

(define sts-print-warnings ((warnings acl2::msg-listp))
  :short "Print a list of warning messages."
  :long
  (xdoc::topstring-p
   "The warnings are expected in reverse chronological order,
    as accumulated in the @('warnings') field of @(tsee sts-split-state);
    they are printed in chronological order.")
  (sts-print-warnings-loop (reverse warnings)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sts-split-gen-everything
  ((code code-ensemblep)
   (tag identp)
   (filepath? c$::filepath-optionp)
   (right-members ident-listp)
   (new-tag? ident-optionp)
   (print-warnings booleanp)
   (const-new symbolp))
  :guard (code-ensemble-annop code)
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp))
  :short "Generate all the events."
  (b* (((reterr) '(_))
       ((erp code warnings)
        (sts-split-code-ensemble tag filepath? right-members new-tag? code))
       (- (and print-warnings
               (sts-print-warnings warnings)))
       (defconst-event
         `(defconst ,const-new
            ',code)))
    (retok defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-type-split-fn (const-old
                              const-new
                              struct-tag
                              filepath
                              right-members
                              new-tag
                              print-warnings
                              (ctx ctxp)
                              state)
  :returns (mv (erp booleanp :rule-classes :type-prescription)
               (event pseudo-event-formp)
               state)
  :short "Event expansion of @(tsee struct-type-split)."
  (b* (((mv erp code tag filepath? right-members new-tag? print-warnings
            const-new)
        (sts-split-process-inputs const-old
                                  const-new
                                  struct-tag
                                  filepath
                                  right-members
                                  new-tag
                                  print-warnings
                                  (w state)))
       ((when erp)
        (er-soft+ ctx t '(_) "STRUCT-TYPE-SPLIT ERROR: ~@0" erp))
       ((mv erp event)
        (sts-split-gen-everything code
                                  tag
                                  filepath?
                                  right-members
                                  new-tag?
                                  print-warnings
                                  const-new))
       ((when erp)
        (er-soft+ ctx t '(_) "STRUCT-TYPE-SPLIT ERROR: ~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection struct-type-split-macro-definition
  :short "Definition of the @('struct-type-split') macro."
  (defmacro struct-type-split
    (const-old
     const-new
     &key
     struct-tag
     filepath
     right-members
     new-tag
     (print-warnings 't))
    `(make-event (struct-type-split-fn ',const-old
                                       ',const-new
                                       ',struct-tag
                                       ',filepath
                                       ',right-members
                                       ',new-tag
                                       ',print-warnings
                                       'struct-type-split
                                       state))))
