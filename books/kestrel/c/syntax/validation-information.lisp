; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "types")
(include-book "uid")
(include-book "unambiguity")
(include-book "evaluation")
(include-book "macro-tables")

(include-book "kestrel/utilities/messages" :dir :system)

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/fty/nat-option" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (in-theory (enable* abstract-syntax-unambp-rules)))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validation-information
  :parents (validation)
  :short "Information calculated and used by the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @(see validator) calculates and uses information, such as types,
     and annotates the abstract syntax with some of this information.
     Here we introduce fixtypes for this information,
     and operations on those fixtypes.")
   (xdoc::p
    "We also introduce predicates over the abstract syntax,
     to check that the annotations from the validator are present.
     This is not the same as saying that the constructs are validated;
     the predicates just say that information of the right type is present."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum initer-subobjects
  :parents (initer-context)
  :short "Fixtype of initializer subobjects."
  :long
  (xdoc::topstring
   (xdoc::p
    "Subobjects are defined in [C17:6.7.9/17]
     to characterize the meaning of initializers.
     This fixtype follows the standard's notion of subobjects,
     and is used to represent the portion of an object type
     which has not yet been initialized.")
   (xdoc::p
    "The @(':array-index') case represents the elements of an array
     including and following the specified index.
     Optionally, it may include the end of an index range.
     This supports the GCC extension for designator ranges
     (see @(see designor)).
     Eventually, we may wish to extend this case
     to also track the size of the array object.
     This will be necessary to determine
     whether we can advance the array-index without reaching the end.
     Currently, we do not track the length of array @(see types)
     and so never have this information.")
   (xdoc::p
    "The @(':struct') case represents the remaining members of a structure,
     excluding unnamed members [C17:6.7.9/9].
     We require a non-empty list of members.
     (We do not currently have a representation for empty struct types,
     a GCC extension.)")
   (xdoc::p
    "Finally, the @(':union') case considers
     only the first member of the union [C17:6.7.9/20]."))
  ;; TODO: we might consider making this index optional,
  ;;   to reflect the case where we could not evaluate
  ;;   the integer constant expression of the designator.
  ;;   At the moment, we use the unknown initializer subobjects in this case.
  (:array-index ((of type) (index nat) (range? acl2::nat-option)))
  (:struct ((members type-struni-member-list
                     :reqfix (if (endp members)
                                 (list (irr-type-struni-member))
                               members)))
   :require (not (endp members)))
  (:union ((first-member type-struni-member)))
  :pred initer-subobjects-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-initer-subobjects
  :parents (initer-subobjects)
  :short "Irrelevant initializer subobjects."
  :type initer-subobjects-p
  :body (make-initer-subobjects-array-index :of (irr-type) :index 0))

;;;;;;;;;;;;;;;;;;;;

(fty::defoption initer-subobjects-option
  initer-subobjects
  :parents (initer-subobjects)
  :short "Fixtype of optional initializer objects."
  :pred initer-subobjects-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist initer-subobjects-list
  :parents (initer-subobjects)
  :short "Fixtype of a list of initializer subobjects."
  :long
   (xdoc::topstring-p
    "Initializer subobjects are defined in @(tsee initer-subobjects).")
  :elt-type initer-subobjects
  :true-listp t
  :elementp-of-nil nil
  :pred initer-subobjects-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum initer-subobjects-stack
  :parents (initer-subobjects)
  :short "Fixtype of a stack of initializer subobjects."
  :long
  (xdoc::topstring
   (xdoc::p
    "A known stack is represented by a list.
     We also allow an ``unknown'' stack, with no further information.
     This unknown option is necessary
     to deal with imprecision elsewhere in our model
     (e.g. in our typing and constant evaluation).")
   (xdoc::p
    "When an initializer occurs without a designation
     in a brace-enclosed initializer,
     it implicitly initializes the ``next'' subobject after the previous,
     where the standard defines which subobjects follow which others
     [C17:6.7.9/17].
     Our @(tsee initer-subobjects) fixtype represents
     the remaining immediate subobjects of some object type.
     But, because of the implicit way
     we may initialize subobjects recursively [C17:6.7.9/20],
     we must maintain a stack of the subobjects.
     When we ``open'' or ``enter'' the current type
     (i.e. the type returned by (tsee subobjects-stack-peek-type)),
     we push the expanded subobjects to the top of the stack.
     When we initialize all subobjects on the top of the stack,
     we pop it and continue initializing in the parent object.")
   (xdoc::p
    "For example, consider the following initializer.")
   (xdoc::codeblock
     "// Assume this is in translation unit named \"foo.c\""
     "// and `struct foo_s` has UID 0."
     "struct foo_s {"
     "  int x;"
     "  int y;"
     "};"
     ""
     "struct foo_s foo[10] = {"
     "  [5].x = 0,"
     "  1,"
     "};")
   (xdoc::p
    "At the sub-initializer @('1')
     (which initializes the subobject represented by designation @('[5].y')),
     the stack, if known, would be:")
   (xdoc::codeblock
     "(initer-subobjects-stack-known"
     " (list (initer-subobjects-struct"
     "        (list (make-type-struni-member"
     "               :name (ident \"x\")"
     "               :type (type-sint))))"
     "       (make-initer-subobjects-array-index"
     "        :of (make-type-struct"
     "             :uid (uid 0)"
     "             :tunit? (filepath \"foo.c\")"
     "             :tag/members (type-struni-tag/members-tagged (ident \"foo_s\")))"
     "        :index 5)))"))
  (:unknown ())
  (:known ((list initer-subobjects-list)))
  :pred initer-subobjects-stack-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-initer-subobjects-stack
  :parents (initer-subobjects-stack)
  :short "An irrelevant initializer subobjects stack."
  :type initer-subobjects-stack-p
  :body (initer-subobjects-stack-known nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum initer-context
  :short "Fixtype of initializer context."
  :long
  (xdoc::topstring
   (xdoc::p
    "This fixtype stores the type and position information
     required to validate initializers.
     The @(':top') case corresponds to an outermost initializer;
     only the type is stored.
     The @(':stack') case applies when we are at some particular position
     within a brace-enclosed initializer.
     See @(tsee initer-subobjects-stack) for details."))
  (:top ((type type)))
  (:stack ((stack initer-subobjects-stack)))
  :pred initer-context-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-initer-context
  :parents (initer-context)
  :short "An irrelevant initializer context."
  :type initer-context-p
  :body (initer-context-top (irr-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-context-unknown ()
  (initer-context-stack (initer-subobjects-stack-unknown))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-stack-end-p ((stack initer-subobjects-stack-p))
  :returns (yes/no booleanp)
  :parents (initer-subobjects-stack)
  :short "Check whether a subobject stack is definitely at the end."
  :long
  (xdoc::topstring-p
   "This recognizer is underapproximate.
    It returns @('nil') in the @(':unknown') case.")
  (initer-subobjects-stack-case
    stack
    :unknown nil
    :known (endp stack.list))

  ///
  (defrule subobjects-stack-end-p-of-initer-subobjects-stack-known
    (equal (subobjects-stack-end-p (initer-subobjects-stack-known list))
           (endp list)))

  (defrule subobjects-stack-end-p-forward-chaining
    (implies (and (not (subobjects-stack-end-p stack))
                  (initer-subobjects-stack-case stack :known))
             (consp (initer-subobjects-stack-known->list stack)))
    :rule-classes ((:forward-chaining
                    :trigger-terms ((subobjects-stack-end-p stack))))
    :enable subobjects-stack-end-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-context-end-p ((ctx initer-context-p))
  :returns (yes/no booleanp)
  :parents (initer-context)
  :short "Check whether an initializer context is definitely at the end."
  :long
  (xdoc::topstring-p
   "This recognizer, like @(tsee subobjects-stack-end-p),
    is underapproximate.")
  (initer-context-case
    ctx
    :top nil
    :stack (subobjects-stack-end-p ctx.stack))

  ///

  (defrule initer-context-end-p-of-initer-context-top
    (not (initer-context-end-p (initer-context-top type))))

  (defrule initer-context-end-p-forward-chaining
    (implies (and (not (initer-context-end-p ctx))
                  (initer-context-case ctx :stack))
             (not (subobjects-stack-end-p (initer-context-stack->stack ctx))))
    :rule-classes ((:forward-chaining
                    :trigger-terms ((initer-context-end-p ctx))))
    :enable initer-context-end-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-peek-type ((subobjects initer-subobjects-p))
  :returns (type typep)
  :parents (initer-subobjects)
  :short "Get the type of the ``current'' subobject."
  (initer-subobjects-case
    subobjects
    :array-index subobjects.of
    :struct (b* (((type-struni-member member) (first subobjects.members)))
              member.type)
    :union (b* (((type-struni-member member) subobjects.first-member))
             member.type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-stack-peek-type ((stack initer-subobjects-stack-p))
  :guard (not (subobjects-stack-end-p stack))
  :returns (type typep)
  :parents (initer-subobjects-stack)
  :short "Get the type of the ``current'' subobject on the stack."
  (initer-subobjects-stack-case
    stack
    :unknown (type-unknown)
    :known (subobjects-peek-type (initer-subobjects-fix (first stack.list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-context->type ((ctx initer-context-p))
  :guard (not (initer-context-end-p ctx))
  :returns (type typep)
  :parents (initer-context)
  :short "Get the type at the current position in the context."
  (initer-context-case
    ctx
    :top ctx.type
    :stack (subobjects-stack-peek-type ctx.stack))

  ///

  (defrule initer-context->type-of-initer-context-top
    (equal (initer-context->type (initer-context-top type))
           (type-fix type)))

  (defrule initer-context->type-when-case-stack
    (implies (initer-context-case ctx :stack)
             (equal (initer-context->type ctx)
                    (subobjects-stack-peek-type
                      (initer-context-stack->stack ctx))))
    :rule-classes ((:rewrite :backchain-limit-lst (0)))
    :enable initer-context->type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-advance ((subobjects initer-subobjects-p))
  :returns (mv (unknownp booleanp)
               (subobjects? initer-subobjects-optionp))
  :parents (initer-subobjects)
  :short "Advance the subobjects past the current subobject."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('unknownp') return flag indicates
     whether the remaining subobjects are unknown.
     If @('unknownp'), then the @('subobjects?') return value is irrelevant.
     Otherwise, if the @('subobjects?') return is non-@('nil'),
     it represents the remaining subobjects
     after advancing forward one position.
     Finally, if @('unknownp') and @('subobjects?') are both @('nil'),
     There are no remaining subobjects.")
   (xdoc::p
    "When advancing an @(':array-index'),
     the result is always unknown, as we do not currently have the array size,
     and therefore cannot determine
     whether we have reached the end of the array.")
   (xdoc::p
    "To advance a @(':struct'),
     we proceed to the next member in declaration order [C17:6.7.9/17].
     The @(tsee initer-subobjects-struct) members are stored in order,
     so we take the @('cdr') of these members.
     If there are no remaining members,
     then there are no remaining subobjects.")
   (xdoc::p
    "For a @(':union'), only the first named member is considered.
     Therefore, advancing always leads to no remaining subobjects."))
  (initer-subobjects-case
    subobjects
    :array-index (mv t nil)
    :struct (mv nil
                (if (endp (cdr subobjects.members))
                    nil
                  (initer-subobjects-struct (cdr subobjects.members))))
    :union (mv nil nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-list-advance ((list initer-subobjects-listp))
  :guard (not (endp list))
  :returns (mv (unknownp booleanp)
               (new-list initer-subobjects-listp))
  :parents (initer-subobjects-list)
  :short "Advance a list of subobjects past the current subobject."
  :long
  (xdoc::topstring-p
   "First, the subobjects at the head of the list are advanced,
    according to @(tsee subobjects-advance).
    If after advancement, there are no remaining subobjects in the head,
    we advance recursively on the list tail.
    This is necessary since the head of the list represents
    some portion of the subobjects
    of the current subobject of the tail's head.")
  (b* (((mv unknownp subobjects?) (subobjects-advance (first list))))
    (cond ((not (mbt (not (endp list))))
           (mv nil nil))
          (unknownp
           (mv t nil))
          (subobjects?
            (mv nil (cons subobjects?
                          (initer-subobjects-list-fix (rest list)))))
          ((endp (rest list))
           (mv nil nil))
          (t
           (subobjects-list-advance (rest list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-stack-advance ((stack initer-subobjects-stack-p))
  :guard (not (subobjects-stack-end-p stack))
  :returns (new-stack initer-subobjects-stack-p)
  :parents (initer-subobjects-stack)
  :short "Advance a stack of subobjects past the current subobject."
  :long
  (xdoc::topstring-p
   "See (tsee subobjects-list-advance).")
  (initer-subobjects-stack-case
    stack
    :unknown (initer-subobjects-stack-fix stack)
    :known (b* (((mv unknownp new-list)
                 (subobjects-list-advance stack.list)))
             (if unknownp
                 (initer-subobjects-stack-unknown)
               (initer-subobjects-stack-known new-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-from-type ((type typep)
                              (completions type-completions-p))
  :guard (or (type-aggregatep type)
             (type-case type '(:union :unknown)))
  :returns (mv (erp maybe-msgp)
               (unknownp booleanp)
               (subobjects? initer-subobjects-optionp))
  :parents (initer-subobjects)
  :short "Get the subobjects of a type."
  :long
  (xdoc::topstring-p
   "Types are expected be complete.
    An incomplete type may result in an error.")
  (b* (((reterr) nil nil)
       (type (type-fix type))
       (completions (type-completions-fix completions)))
    (type-case
      type
      :struct (b* (((erp members)
                    (type-struni-tag/members->members
                      type.tag/members type.uid completions)
                    :iferr (msg$ "Type ~x0 is incomplete. ~
                                  Therefore, we cannot ~
                                  get the subobjects-stack."
                                 type))
                   (filtered (members-filter-contributers members)))
                (retok nil
                       (if (endp filtered)
                           nil
                         (initer-subobjects-struct filtered))))
      :union (b* (((erp members)
                    (type-struni-tag/members->members
                      type.tag/members type.uid completions)
                    :iferr (msg$ "Type ~x0 is incomplete. ~
                                  Therefore, we cannot ~
                                  get the subobjects-stack."
                                 type))
                  (filtered (members-filter-contributers members)))
               (if (endp filtered)
                   (retmsg$ "Complete union type ~x0 has no named members."
                            type)
                 (retok nil (initer-subobjects-union (car filtered)))))
      :array (retok nil
                    (make-initer-subobjects-array-index
                      :of type.of
                      :index 0))
      :unknown (retok t nil)
      :otherwise (prog2$ (impossible) (retmsg$ "Internal error."))))
  :guard-hints (("Goal" :in-theory (enable type-aggregatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-stack-enter ((stack initer-subobjects-stack-p)
                                (completions type-completions-p))
  :guard (and (not (subobjects-stack-end-p stack))
              (or (type-aggregatep (subobjects-stack-peek-type stack))
                  (type-case (subobjects-stack-peek-type stack) :union)))
  :returns (mv (erp maybe-msgp)
               (new-stack initer-subobjects-stack-p))
  :parents (initer-subobjects-stack)
  :short "Expand the current subobject and push to the stack."
  :long
  (xdoc::topstring-p
   "This gets the type of the current subobject,
    converts the type into subobjects,
    and pushes said subobjects to the top of the stack.")
  (b* (((reterr) (irr-initer-subobjects-stack))
       (type (subobjects-stack-peek-type stack))
       ((erp unknownp subobjects?)
        (subobjects-from-type type completions))
       ((when (or unknownp (not subobjects?)))
        (retok (initer-subobjects-stack-unknown))))
    (retok (initer-subobjects-stack-known
             (cons subobjects? (initer-subobjects-stack-known->list stack)))))
  :guard-hints (("Goal" :in-theory (enable subobjects-stack-peek-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-context-enter ((ctx initer-context-p)
                              (completions type-completions-p))
  :guard (and (not (initer-context-end-p ctx))
              (or (type-aggregatep (initer-context->type ctx))
                  (type-case (initer-context->type ctx) :union)))
  :returns (mv (erp maybe-msgp)
               (stack initer-subobjects-stack-p))
  :parents (initer-context)
  :short "Expand the current subobject and push to the stack."
  :long
  (xdoc::topstring-p
   "If the context represents an outermost initializer
    (and therefore there is no current stack),
    create a new stack and push the new subobjects.")
  (initer-context-case
    ctx
    :top (b* (((reterr) (irr-initer-subobjects-stack))
              ((erp unknownp subobjects?)
               (subobjects-from-type ctx.type completions)))
           (retok (if (and (not unknownp) subobjects?)
                      (initer-subobjects-stack-known
                        (list subobjects?))
                    (initer-subobjects-stack-unknown))))
    :stack (subobjects-stack-enter ctx.stack completions))
  :guard-hints (("Goal" :in-theory (enable initer-context->type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-from-members-lookup ((ident identp)
                                        (is-struct-p booleanp)
                                        (members type-struni-member-listp))
  :returns (mv (erp booleanp)
               (list initer-subobjects-listp))
  :parents (initer-subobjects-stack)
  :short "Lookup the struct/union subobjects at and following a named member."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('is-struct-p') argument indicates whether
     @('members') belong to a struct type.
     If @('is-struct-p') is @('nil'),
     then @('members') must belong instead to a union type.")
   (xdoc::p
    "Like @(tsee type-struni-member-list-lookup),
     this function searches recursively in anonymous structs and unions,
     as the members of these are considered members of the outer struct/union
     [C17:6.7.2.1/13].")
   (xdoc::p
    "The remaining subobjects after a struct member are
     all the named members which follow in declaration order [C17:6.7.9/17],
     excluding the unnamed members [C17:6.7.9/9].")
   (xdoc::p
    "There are no remaining subobjects
     following a union member [C17:6.7.9/20]."))
  (b* (((reterr) (list (irr-initer-subobjects)))
       ((when (endp members))
        (reterr t))
       ((type-struni-member member) (first members))
       ((when member.name?)
        (if (ident-equal ident member.name?)
            (retok (if is-struct-p
                       (list (initer-subobjects-struct
                               (cons (first members)
                                     (members-filter-contributers (rest members)))))
                     (list (initer-subobjects-union (first members)))))
          (subobjects-from-members-lookup ident is-struct-p (rest members))))
       ((mv erp list)
        (type-case
          member.type
          :struct (type-struni-tag/members-case
                    member.type.tag/members
                    :tagged (reterr t)
                    :untagged (subobjects-from-members-lookup
                                ident
                                t
                                member.type.tag/members.members))
          :union (type-struni-tag/members-case
                   member.type.tag/members
                   :tagged (reterr t)
                   :untagged (subobjects-from-members-lookup
                               ident
                               nil
                               member.type.tag/members.members))
          :otherwise (reterr t))))
    (if erp
        (subobjects-from-members-lookup ident is-struct-p (rest members))
      (retok (append list
                     (if is-struct-p
                         (list (initer-subobjects-struct
                                 (cons (first members)
                                       (members-filter-contributers
                                         (rest members)))))
                       (list (initer-subobjects-union (first members))))))))
  :measure (type-struni-member-list-count members)
  :ruler-extenders :all
  ;; Verified below
  :verify-guards nil
  :hooks ((:fix :hints (("Goal" :induct t))))

  ///
  (more-returns
   (list true-listp :rule-classes :type-prescription)
   (list consp
         :rule-classes :type-prescription
         :hints (("Goal" :induct t))))

  (verify-guards subobjects-from-members-lookup))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-to-designor ((subobjects initer-subobjects-p)
                                (ienv ienvp))
  :returns (mv (er? maybe-msgp)
               (desingor? designor-optionp))
  :parents (initer-subobjects)
  :short "Create a designator from an initializer subobjects fixtype object."
  :long
  (xdoc::topstring
   (xdoc::p
    "This conversion is largely straightforward.
     However, it does require creating an integer constant AST node
     from a natural number.
     This is the reason we need the implementation environment
     (to check whether the number will fit).")
   (xdoc::p
    "A non-@('nil') @('erp') value indicates a failure to convert.
     When @('erp') is @('nil'), the operation succeeded.
     When the operation succeeded,
     the @('designor?') return is @('nil') iff
     the subobjects is unnamed
     (i.e., it is an unnamed bit-field or an anonymous struct/union)."))
  (b* (((reterr) nil))
    (initer-subobjects-case
      subobjects
      :array-index (b* ((index-iconst?
                          (nat-to-iconst subobjects.index ienv))
                        ((unless index-iconst?)
                         (retmsg$ "Could not convert natural ~x0 ~
                                   into an integer constant."
                                  subobjects.index))
                        ((erp range-iconst?)
                         (b* (((unless subobjects.range?)
                               (mv nil nil))
                              (range-cexpr?
                               (nat-to-iconst subobjects.range? ienv))
                              ((unless range-cexpr?)
                               (retmsg$ "Could not convert natural ~x0 ~
                                         into an integer constant."
                                        subobjects.range?)))
                           (retok range-cexpr?)))
                        (index-cexpr
                          (make-const-expr
                            :expr (make-expr-const
                                    :const (const-int index-iconst?))))
                        (range-cexpr?
                          (and range-iconst?
                               (make-const-expr
                                 :expr (make-expr-const
                                         :const (const-int range-iconst?))))))
                     (retok (make-designor-sub
                              :index index-cexpr
                              :range? range-cexpr?)))
      :struct (b* (((type-struni-member member) (first subobjects.members)))
                (retok (if member.name?
                           (make-designor-dot :name member.name?)
                         nil)))
      :union (b* (((type-struni-member member) subobjects.first-member))
               (retok (if member.name?
                          (make-designor-dot :name member.name?)
                        nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-list-to-designors ((list initer-subobjects-listp)
                                      (ienv ienvp))
  :guard (not (endp list))
  :returns (designors designor-listp)
  :parents (initer-subobjects-list)
  :short "Create a designator list from a list of initializer subobjects."
  :long
  (xdoc::topstring-p
   "A return value of @('nil') indicates a failure to convert.")
  (b* (((unless (mbt (not (endp list))))
        nil)
       ((mv er? designor?)
        (subobjects-to-designor (first list) ienv))
       ((when er?)
        ;; For now, we do nothing with the error message.
        nil)
       ((unless designor?)
        ;; An unnamed subobject cannot be the at the top of the stack.
        nil))
    (if (endp (rest list))
        (list designor?)
      (subobjects-list-to-designors-loop (rest list) ienv (list designor?))))
  :prepwork
  ((define subobjects-list-to-designors-loop ((list initer-subobjects-listp)
                                              (ienv ienvp)
                                              (acc designor-listp))
     :guard (not (endp list))
     :returns (designors designor-listp)
     (b* (((unless (mbt (not (endp list))))
           nil)
          ((mv er? designor?)
           (subobjects-to-designor (first list) ienv))
          ((when er?)
           ;; For now, we do nothing with the error message.
           nil)
          (acc (if designor?
                   (cons designor? (designor-list-fix acc))
                 (designor-list-fix acc))))
       (if (endp (rest list))
           acc
         (subobjects-list-to-designors-loop (rest list) ienv acc))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subobjects-stack-to-designors ((stack initer-subobjects-stack-p)
                                       (ienv ienvp))
  :guard (not (subobjects-stack-end-p stack))
  :returns (designors designor-listp)
  :parents (initer-subobjects-stack)
  :short "Create a designator list from a stack of initializer subobjects."
  :long
  (xdoc::topstring-p
   "A return value of @('nil') indicates a failure to convert.")
  (initer-subobjects-stack-case
    stack
    :unknown nil
    :known (subobjects-list-to-designors stack.list ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: This evaluates the expression, which might be a bit expensive. Ideally
;; we would be annotating expressions with values as we go.
(define expr-null-pointer-constp ((expr exprp) (type typep) (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check whether an expression of a given type is potentially a null
          pointer constant [C17:6.3.2.3/3]."
  :long
  (xdoc::topstring-p
   "A null pointer constant is an integer constant expression with value 0
    or a cast of such an expression to a void pointer [C17:6.3.2.3/3].
    This check is currently overapproximate.
    Our evaluation may yield an unknown value,
    in which case we consider the expression
    to possibly be a null pointer constant.
    Similarly, we don't check that the expression
    is an integer constant expression
    or a cast of an integer constant expression to a void pointer.")
  (type-case
   type
   :unknown t
   :pointer (b* (((unless (or (type-case type.to :void)
                              (type-case type.to :unknown)))
                  nil)
                 (val (const-eval-expr expr ienv)))
              (value-case
                val
                :unknown t
                :pointer (pointer-case
                           val.get
                           :unknown t
                           :non-null nil
                           :null t)
                :otherwise nil))
   :otherwise (b* (((unless (type-integerp type))
                    nil)
                   (val (const-eval-expr expr ienv))
                   ((when (value-case val :unknown))
                    t)
                   (int? (value-to-integer val)))
                (or (not int?)
                    (equal int? 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-expr-null-pointer-constp ((const-expr const-exprp)
                                        (type typep)
                                        (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Check whether a constant expression of a given type is potentially a
          null pointer constant [C17:6.3.2.3/3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee expr-null-pointer-constp)."))
  (b* (((const-expr const-expr) const-expr))
    (expr-null-pointer-constp const-expr.expr type ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum linkage
  :short "Fixtype of linkages."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are three kinds of linkages: external, internal, and none
     [C17:6.2.2/1]."))
  (:external ())
  (:internal ())
  (:none ())
  :pred linkagep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-linkage
  :short "An irrelevant linkage."
  :type linkagep
  :body (linkage-none))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption linkage-option
  linkage
  :short "Fixtype of optional linkages."
  :long
  (xdoc::topstring
   (xdoc::p
    "Linkages are defined in @(tsee linkage)."))
  :pred linkage-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum lifetime
  :short "Fixtype of lifetimes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This represents a storage duration [C17:6.2.4],
     but only three kinds, excluding the allocated kind.
     We use the term `lifetime' because it is just one word,
     and also to avoid implying that there are only three storage durations,
     when there are in fact four.
     Since a storage duration defines the kind of lifetime of an object,
     one could argue that there are four kinds of lifetimes too;
     however, for practicality, we need a fixtype for
     only these three kinds of lifetimes (or storage durations),
     and so we use the term `lifetime'.
     This must be thought as the possible kinds of lifetime of declared objects;
     allocated objects are not declared, but just created via library calls."))
  (:static ())
  (:thread ())
  (:auto ())
  :pred lifetimep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-lifetime
  :short "An irrelevant lifetime."
  :type lifetimep
  :body (lifetime-auto))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption lifetime-option
  lifetime
  :short "Fixtype of optional lifetimes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lifetimes are defined in @(tsee lifetime)."))
  :pred lifetime-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum valid-defstatus
  :short "Fixtype of definition statuses for validation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to objects and functions, which may be
     undefined, defined, or tentatively defined [C17:6.7/5] [C17:6.9.2],
     with the latter actually only applying to objects, not functions."))
  (:undefined ())
  (:tentative ())
  (:defined ())
  :pred valid-defstatusp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum valid-ord-info
  :short "Fixtype of validation information about ordinary identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Ordinary identifiers [C17:6.2.3/1] denote
     objects, functions, enumeration constants, and @('typedef') names;
     Ordinary identifiers form their own name space.
     The other entities denoted by identifiers [C17:6.2.1/1]
     are in other name spaces, disjoint from the one of ordinary identifiers.")
   (xdoc::p
    "This fixtype formalizes the information about ordinary identifiers
     tracked by our current validator.
     Since our model of types includes both object and function types,
     the information for both objects and functions includes (different) types;
     that information also includes the linkage [C17:6.2.2],
     as well as definition status (see @(tsee valid-defstatus)).
     We also assign a "
    (xdoc::seetopic "uid" "unique identifier")
    ". For enumeration constants names,
     for now we only track that they are enumeration constants.
     For @('typedef') names, we track the type corresponding to its
     definition.")
   (xdoc::p
    "We will refine this fixtype as we refine our validator."))
  (:objfun ((type type)
            (linkage linkage)
            (defstatus valid-defstatus)
            (uid uid)))
  (:enumconst ())
  (:typedef ((def type)))
  :pred valid-ord-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-ord-info-option
  valid-ord-info
  :short "Fixtype of
          optional validation information about ordinary identifiers."
  :pred valid-ord-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist valid-ord-scope
  :short "Fixtype of validation scopes of ordinary identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers have scopes [C17:6.2.1], which the validator tracks.
     In each scope, for each name space,
     each identifier must have one meaning (if any) [C17:6.2.1/2].
     Thus, we use an alist from identifiers
     to the validation information about ordinary identifiers,
     to track each scope in the name space of ordinary identifiers."))
  :key-type ident
  :val-type valid-ord-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred valid-ord-scopep
  :prepwork ((set-induction-depth-limit 1))
  ///

  (defrule valid-ord-infop-of-cdr-assoc-when-valid-ord-scopep
    (implies (and (valid-ord-scopep scope)
                  (assoc-equal ident scope))
             (valid-ord-infop (cdr (assoc-equal ident scope))))
    :induct t
    :enable (valid-ord-scopep assoc-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum tag-kind
  :short "Fixtype of the different kinds of tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now, we include cases for just @(':struct') and @(':union').
     We omit @(':enum'), whose tags are not yet being tracked."))
  (:struct ())
  (:union ())
  :pred tag-kindp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-tag-info
  :short "Fixtype of validation information about tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "Tags [C17:6.2.3/1] identify a structure, union, or enumeration type.
     Tags form their own name space,
     disambiguated by the @('struct'), @('union'), or @('enum') keywords.")
   (xdoc::p
    "We store the @(tsee tag-kind)
     and the @(see UID) associated with the tag
     in the current scope.
     The @(see UID) can be used to lookup the completion
     under a separate @(tsee type-completions) map."))
  ((kind tag-kind)
   (uid uid))
  :pred valid-tag-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-tag-info-option
  valid-tag-info
  :short "Fixtype of optional validation information about tags."
  :pred valid-tag-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist valid-tag-scope
  :short "Fixtype of validation scopes of tags."
  :long
  (xdoc::topstring
   (xdoc::p
    "The same tag may refer to different types in different scopes.
     Therefore, we use an alist from identifiers
     to the validation information for tags
     to track the meaning of tags in each scope."))
  :key-type ident
  :val-type valid-tag-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred valid-tag-scopep
  :prepwork ((set-induction-depth-limit 1))
  ///

  (defrule valid-tag-infop-of-cdr-assoc-when-valid-tag-scopep
    (implies (and (valid-tag-scopep scope)
                  (assoc-equal ident scope))
             (valid-tag-infop (cdr (assoc-equal ident scope))))
    :induct t
    :enable (valid-tag-scopep assoc-equal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-scope
  :short "Fixtype of validation scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers have scopes [C17:6.2.1], which the validator tracks.
     This fixtype contains all the information about a scope,
     which considers the name space of ordinary identifiers
     and the name space of tags."))
  ((ord valid-ord-scope)
   (tag valid-tag-scope))
  :pred valid-scopep
  ///

  (defrule alistp-of-valid-scope->ord
    (alistp (valid-scope->ord x))
    :enable alistp-when-valid-ord-scopep-rewrite)

  (defrule alistp-of-valid-scope->tag
    (alistp (valid-scope->tag x))
    :enable alistp-when-valid-tag-scopep-rewrite))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist valid-scope-list
  :short "Fixtype of lists of validation scopes."
  :elt-type valid-scope
  :true-listp t
  :elementp-of-nil nil
  :pred valid-scope-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-ext-info
  :short "Fixtype of validation information about identifiers with external
          linkage."
  :long
  (xdoc::topstring
   (xdoc::p
    "We store the following information about identifiers
     with external linkage for the purpose of validation
     across unrelated scopes and across different translation units
     (by ``unrelated,'' we mean neither scope is nested within the other).")
   (xdoc::p
    "Each declaration of a given identifier with external linkage
     must agree on the type [C17:6.2.2/2] [C17:6.2.7/2].
     Therefore, we store the type to check type compatibility
     of any declaration after the first.")
   (xdoc::p
    "We also store the set of translation units
     (represented by their @(see filepath)s)
     in which the identifier has been declared.
     This is used to ensure the same identifier has not been declared
     with both internal and external linkage in the same translation unit
     [C17:6.2.2/7].")
   (xdoc::p
    "Finally, we store a "
    (xdoc::seetopic "uid" "unique identifier")
    " for the object.
     All identifiers of the same name with external linkage
     refer to the same object and therefore possess
     the same unique identifier.")
   (xdoc::p
    "Eventually, we may wish to store a boolean flag indicating
     whether the identifier has been externally defined.
     This would be used to ensure
     that externally linked identifiers are defined at most once
     (or exactly once, if the identifier is used in an expression) [C17:6.9/5].
     For now, we conservatively allow any number of definitions."))
  ((type type)
   (declared-in filepath-set)
   (uid uid))
  :pred valid-ext-infop)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-ext-info-option
  valid-ext-info
  :short "Fixtype of optional validation information
          about identifiers with external linkage."
  :pred valid-ext-info-optionp)

;;;;;;;;;;;;;;;;;;;;

(fty::defomap valid-externals
  :short "Fixtype of validation information associated with identifiers with
          external linkage."
  :key-type ident
  :val-type valid-ext-info
  :pred valid-externalsp
  ///

  (defrule valid-ext-info-optionp-of-cdr-assoc-when-valid-externalsp
    (implies (valid-externalsp externals)
             (valid-ext-info-optionp (cdr (omap::assoc ident externals))))
    :induct t
    :enable (valid-externalsp omap::assoc valid-ext-info-optionp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod valid-table
  :short "Fixtype of validation tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validation table is a collection of validation information
     for a single translation unit.")
   (xdoc::p
    "The @('filepath') field stores the name of the translation unit.")
   (xdoc::p
    "Scopes are treated in a stack-like manner [C17:6.2.1].
     Thus, a validation table contains a list (i.e. stack) of scopes.
     The stack grows from right to left:
     the leftmost scope is the top, and the rightmost scope is the bottom;
     in other words, in the nesting of scopes in the stack,
     the leftmost scope is the innermost,
     and the rightmost scope is the outermost
     (i.e. the file scope [C17:6.2.1/4].)")
   (xdoc::p
    "The @('macros') field stores the macro table."))
  ((filepath filepath)
   (scopes valid-scope-list)
   (macros macro-table))
  :pred valid-tablep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-valid-table
  :short "An irrelevant validation table."
  :type valid-tablep
  :body (valid-table (irr-filepath) nil (irr-macro-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption valid-table-option
  valid-table
  :short "Fixtype of optional validation tables."
  :pred valid-table-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod iconst-info
  :short "Fixtype of validation information for integer constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to integer constants,
     i.e. the @(tsee iconst) constructs.
     The information consists of the type of the constant
     (which for now we do not constrain to be an integer type),
     and the numeric value of the constant, as an ACL2 natural number."))
  ((type type)
   (value nat))
  :pred iconst-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var-info
  :short "Fixtype of validation information for variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that the validator adds to variables,
     i.e. identifiers used as expressions,
     i.e. the @(':ident') case of @(tsee expr).
     The information for a variable consists of
     the type and linkage of the object denoted by the variable,
     as well as the variable's"
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((type type)
   (linkage linkage)
   (uid uid))
  :pred var-infop)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-var-info
  :short "An irrelevant validation information for variables."
  :type var-infop
  :body (make-var-info :type (irr-type)
                       :linkage (irr-linkage)
                       :uid (irr-uid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define coerce-var-info (x)
  :returns (info var-infop)
  :short "Coerce a value to @(tsee var-info)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used when the value is expected to have that type.
     We raise a hard error if that is not the case."))
  (if (var-infop x)
      x
    (prog2$ (raise "Internal error: ~x0 does not satisfy VAR-INFOP." x)
            (irr-var-info)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-const-info
  :short "Fixtype of validation information for constant expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations
     that the validator adds to constant expressions,
     i.e. the @('const') case of @(tsee expr).
     The information for a constant consists of the type."))
  ((type type))
  :pred expr-const-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-string-info
  :short "Fixtype of validation information for string literal expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations
     that the validator adds to string literal expressions,
     i.e. the @('string') case of @(tsee expr).
     The information for a string literal consists of the type."))
  ((type type))
  :pred expr-string-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-arrsub-info
  :short "Fixtype of validation information for array subscript expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations
     that the validator adds to array subscript expressions,
     i.e. the @('arrsub') case of @(tsee expr).
     The information for an array subscript consists of the type."))
  ((type type))
  :pred expr-arrsub-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-funcall-info
  :short "Fixtype of validation information for function call expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations
     that the validator adds to function call expressions,
     i.e. the @('funcall') case of @(tsee expr).
     The information for a function call consists of the type."))
  ((type type))
  :pred expr-funcall-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-unary-info
  :short "Fixtype of validation information for unary expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to unary expressions,
     i.e. the @(':unary') case of @(tsee expr).
     The information for a unary expression consists of its type."))
  ((type type))
  :pred expr-unary-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-binary-info
  :short "Fixtype of validation information for binary expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to binary expressions,
     i.e. the @(':binary') case of @(tsee expr).
     The information for a binary expression consists of its type."))
  ((type type))
  :pred expr-binary-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod const-expr-info
  :short "Fixtype of validation information for constant expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to constant expressions,
     i.e. the @(tsee const-expr) fixtype.
     The information for a constant expression consists of
     its value after evaluation."))
  ((value valuep))
  :pred const-expr-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod desiniter-info
  :short "Fixtype of validation information for initializers with optional
          designations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to initializers with optional designations,
     i.e. the @(tsee desiniter) fixtype.
     The information for a initializers with optional designations consists of
     an optional designation.
     When a designation is not present in the syntax,
     the validator may add a designation here
     corresponding to the implicitly initialized subobject."))
  ((designors designor-list))
  :pred desiniter-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod param-declon-info
  :short "Fixtype of validation information for parameter declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to parameter declarations.
     The information consists of the optional type of the declared parameter.
     The type is absent for the special @('(void)') syntax
     that denotes an empty parameter list,
     where the single parameter declaration
     does not actually declare a parameter."))
  ((type type-option))
  :pred param-declon-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod param-declor-nonabstract-info
  :short "Fixtype of validation information for
          non-abstract parameter declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to non-abstract parameter declarators,
     i.e. the @(tsee param-declor) fixtype with kind @(':nonabstract').
     The information consists of the type of the declared identifier and a "
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((type type)
   (uid uid))
  :pred param-declor-nonabstract-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tyname-info
  :short "Fixtype of validation information for type names."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to type names,
     i.e. the @(tsee tyname) fixtype.
     The information for a type name consists of its denoted type."))
  ((type type))
  :pred tyname-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod init-declor-info
  :short "Fixtype of validation information for initializer declarators."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to initializer declarators,
     i.e. the @(tsee init-declor) fixtype.")
   (xdoc::p
    "The information for an initializer declarator consists of
     the type of (or denoted by) the declared identifier,
     a flag saying whether the identifier is a @('typdef') or not
     (if the flag is @('t') the type is the one denoted by the identifier),
     and an "
    (xdoc::seetopic "uid-option" "optional unique identifier")
    ". Currently, we only assign unique identifiers to
     ordinary identifiers representing an object or function.
     Therefore, only initializer declarators corresponding
     to those such identifiers are annotated with unique identifiers.
     Initializer declarators which correspond to @('typedef') declarations
     are not annotated with a unique identifier."))
  ((type type)
   (typedefp bool)
   (uid? uid-option))
  :pred init-declor-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fundef-info
  :short "Fixtype of validation information for function definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to function definitions.
     The information consists of
     the type of the function (not just the result; the function type),
     and a "
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((type type)
   (uid uid))
  :pred fundef-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod trans-unit-info
  :short "Fixtype of validation information for translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to translation units.
     The information consists of
     the final validation table for the translation unit.
     The table @('scopes') is expected to be a singleton,
     representing the file-scope at the end of the translation unit."))
  ((table-end valid-table))
  :pred trans-unit-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod trans-ensemble-info
  :short "Fixtype of validation information for translation ensembles."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the annotations that
     the validator adds to translation ensembles.
     The information consists of
     the validation information related to identifiers with external linkage,
     the map of structure and union type UIDs to their members,
     and the next unused "
    (xdoc::seetopic "uid" "unique identifier")
    "."))
  ((externals valid-externals)
   (completions type-completions)
   (next-uid uidp))
  :pred trans-ensemble-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (std::make-define-config :no-function nil)

  (fty::deffold-reduce annop
    :short "Definition of the predicates that check whether
            the abstract syntax is annotated with validation information."
    :long
    (xdoc::topstring
     (xdoc::p
      "We use @(tsee fty::deffold-reduce) to define these predicates concisely.")
     (xdoc::p
      "The @(':default') value is @('t'),
       meaning that there are no constraints by default.")
     (xdoc::p
      "The @(':combine') operator is @(tsee and),
       because we need to check all the constructs, recursively.")
     (xdoc::p
      "We override the predicate for
       the constructs for which the validator adds information.")
     (xdoc::p
      "Since for now the validator accepts GCC attribute and other extensions
       without actually checking them and their constituents,
       we also have the annotation predicates accept those constructs,
       by overriding those cases to return @('t').")
     (xdoc::p
      "The validator operates on unambiguous abstract syntax,
       which satisfies the @(see unambiguity) predicates.
       Ideally, the annotation predicates should use
       the unambiguity predicates as guards,
       but @(tsee fty::deffold-reduce) does not support that feature yet.
       Thus, for now we add run-time checks, in the form of @(tsee raise),
       for the cases in which the unambiguity predicates do not hold;
       note that @(tsee raise) is logically @('nil'),
       so the annotation predicates are false on ambiguous constructs."))
    :types (ident
            ident-list
            ident-option
            iconst
            iconst-option
            const
            const-option
            attrib-name
            exprs/decls/stmts
            fundef
            ext-declon
            ext-declon-list
            hash-if/elif-expr
            hash-if/ifdef/ifndef
            trans-items
            trans-unit
            filepath-trans-unit-map
            trans-ensemble
            code-ensemble)
    :result booleanp
    :default t
    :combine and
    :override
    ((iconst (iconst-infop (iconst->info iconst)))
     (expr :ident (var-infop expr.info))
     (expr :const (and (const-annop expr.const)
                       (expr-const-infop expr.info)))
     (expr :string (expr-string-infop expr.info))
     (expr :arrsub (and (expr-annop expr.arg1)
                        (expr-annop expr.arg2)
                        (expr-arrsub-infop expr.info)))
     (expr :funcall (and (expr-annop expr.fun)
                         (expr-list-annop expr.args)
                         (expr-funcall-infop expr.info)))
     (expr :unary (and (expr-annop expr.arg)
                       (expr-unary-infop expr.info)))
     (expr :sizeof-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
     (expr :alignof-ambig (raise "Internal error: ambiguous ~x0."
                                 (expr-fix expr)))
     (expr :binary (and (expr-annop expr.arg1)
                        (expr-annop expr.arg2)
                        (expr-binary-infop expr.info)))
     (expr :cast/call-ambig (raise "Internal error: ambiguous ~x0."
                                   (expr-fix expr)))
     (expr :cast/mul-ambig (raise "Internal error: ambiguous ~x0."
                                  (expr-fix expr)))
     (expr :cast/add-ambig (raise "Internal error: ambiguous ~x0."
                                  (expr-fix expr)))
     (expr :cast/sub-ambig (raise "Internal error: ambiguous ~x0."
                                  (expr-fix expr)))
     (expr :cast/and-ambig (raise "Internal error: ambiguous ~x0."
                                  (expr-fix expr)))
     (expr :cast/logand-ambig (raise "Internal error: ambiguous ~x0."
                                     (expr-fix expr)))
     (const-expr (and (expr-annop (const-expr->expr const-expr))
                      (const-expr-infop (const-expr->info const-expr))))
     (desiniter (and (designor-list-annop (desiniter->designors desiniter))
                     (initer-annop (desiniter->initer desiniter))
                     (desiniter-infop (desiniter->info desiniter))))
     (type-spec :typeof-ambig (raise "Internal error: ambiguous ~x0."
                                     (type-spec-fix type-spec)))
     (align-spec :alignas-ambig (raise "Internal error: ambiguous ~x0."
                                       (align-spec-fix align-spec)))
     (dirabsdeclor :dummy-base (raise "Internal error: ~
                                       dummy base case of ~
                                       direct abstract declarator."))
     (tyname (and (spec/qual-list-annop (tyname->specquals tyname))
                  (absdeclor-option-annop (tyname->declor? tyname))
                  (tyname-infop (tyname->info tyname))))
     (param-declon (and (decl-spec-list-annop
                          (param-declon->specs param-declon))
                        (param-declor-annop (param-declon->declor param-declon))
                        (attrib-spec-list-annop
                          (param-declon->attribs param-declon))
                        (param-declon-infop (param-declon->info param-declon))))
     (param-declor :nonabstract (and (declor-annop
                                      (param-declor-nonabstract->declor
                                       param-declor))
                                     (param-declor-nonabstract-infop
                                      (param-declor-nonabstract->info
                                       param-declor))))
     (attrib t)
     (attrib-spec t)
     (init-declor (and (declor-annop (init-declor->declor init-declor))
                       (initer-option-annop (init-declor->initer? init-declor))
                       (init-declor-infop (init-declor->info init-declor))))
     (asm-output t)
     (asm-input t)
     (asm-stmt t)
     (stmt :for-ambig (raise "Internal error: ambiguous ~x0."
                             (stmt-fix stmt)))
     (block-item :ambig (raise "Internal error: ambiguous ~x0."
                               (block-item-fix block-item)))
     (amb-expr/tyname (raise "Internal error: ambiguous ~x0."
                             (amb-expr/tyname-fix amb-expr/tyname)))
     (amb-declor/absdeclor (raise "Internal error: ambiguous ~x0."
                                  (amb-declor/absdeclor-fix
                                   amb-declor/absdeclor)))
     (amb-declon/stmt (raise "Internal error: ambiguous ~x0."
                             (amb-declon/stmt-fix amb-declon/stmt)))
     (fundef (and (decl-spec-list-annop (fundef->specs fundef))
                  (declor-annop (fundef->declor fundef))
                  (declon-list-annop (fundef->declons fundef))
                  (comp-stmt-annop (fundef->body fundef))
                  (fundef-infop (fundef->info fundef))))
     (trans-unit (and (trans-item-list-annop (trans-unit->items trans-unit))
                      (trans-unit-infop (trans-unit->info trans-unit))))
     (trans-ensemble (and (filepath-trans-unit-map-annop
                           (trans-ensemble->units trans-ensemble))
                          (trans-ensemble-infop
                           (trans-ensemble->info
                            trans-ensemble)))))
    :name abstract-syntax-annop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection abstract-syntax-anno-additional-theorems
  :short "Additional theorems about the annotation predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are in addition to the ones
     generated by @(tsee fty::deffold-reduce).
     These are needed for actual proofs involving the annotation predicates.
     In particular, @(tsee fty::deffold-reduce) does not generate theorems
     for constructs in the @(':override') input;
     so we must supply theorems for those cases."))

  ;; The following theorems are not auto-generated by FTY::DEFFOLD-REDUCE
  ;; because the corresponding constructs are in the :OVERRIDE input.

  ;; theorems about constructors:

  (defruled iconst-annop-of-iconst
    (equal (iconst-annop (iconst core suffix? info))
           (iconst-infop info))
    :enable iconst-annop)

  (defruled expr-annop-of-expr-ident
    (equal (expr-annop (expr-ident ident info))
           (var-infop info))
    :enable expr-annop)

  (defruled expr-annop-of-expr-const
    (equal (expr-annop (expr-const const info))
           (and (const-annop const)
                (expr-const-infop info)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-string
    (equal (expr-annop (expr-string strings info))
           (expr-string-infop info))
    :enable expr-annop)

  (defruled expr-annop-of-expr-arrsub
    (equal (expr-annop (expr-arrsub arg1 arg2 info))
           (and (expr-annop arg1)
                (expr-annop arg2)
                (expr-arrsub-infop info)))
    :expand (expr-annop (expr-arrsub arg1 arg2 info)))

  (defruled expr-annop-of-expr-funcall
    (equal (expr-annop (expr-funcall fun args info))
           (and (expr-annop fun)
                (expr-list-annop args)
                (expr-funcall-infop info)))
    :expand (expr-annop (expr-funcall fun args info)))

  (defruled expr-annop-of-expr-unary
    (equal (expr-annop (expr-unary op arg info))
           (and (expr-annop arg)
                (expr-unary-infop info)))
    :expand (expr-annop (expr-unary op arg info)))

  (defruled expr-annop-of-expr-binary
    (equal (expr-annop (expr-binary op arg1 arg2 info))
           (and (expr-annop arg1)
                (expr-annop arg2)
                (expr-binary-infop info)))
    :expand (expr-annop (expr-binary op arg1 arg2 info)))

  (defruled const-expr-annop-of-const-expr
    (equal (const-expr-annop (const-expr expr info))
           (and (expr-annop expr)
                (const-expr-infop info)))
    :expand (const-expr-annop (const-expr expr info)))

  (defruled desiniter-annop-of-desiniter
    (equal (desiniter-annop (desiniter designors initer info))
           (and (designor-list-annop designors)
                (initer-annop initer)
                (desiniter-infop info)))
    :expand (desiniter-annop (desiniter designors initer info))
    :enable identity)

  (defruled tyname-annop-of-tyname
    (equal (tyname-annop (tyname specquals declor? info))
           (and (spec/qual-list-annop specquals)
                (absdeclor-option-annop declor?)
                (tyname-infop info)))
    :expand (tyname-annop (tyname specquals declor? info)))

  (defruled param-declon-annop-of-param-declon
    (equal (param-declon-annop (param-declon specs declor attribs info))
           (and (decl-spec-list-annop specs)
                (param-declor-annop declor)
                (attrib-spec-list-annop attribs)
                (param-declon-infop info)))
    :expand (param-declon-annop (param-declon specs declor attribs info)))

  (defruled param-declor-annop-of-param-declor-nonabstract
    (equal (param-declor-annop (param-declor-nonabstract declor info))
           (and (declor-annop declor)
                (param-declor-nonabstract-infop info)))
    :expand (param-declor-annop (param-declor-nonabstract declor info)))

  (defruled init-declor-annop-of-init-declor
    (equal (init-declor-annop (init-declor declor asm? attribs initer? info))
           (and (declor-annop declor)
                (initer-option-annop initer?)
                (init-declor-infop info)))
    :expand (init-declor-annop (init-declor declor asm? attribs initer? info)))

  (defruled fundef-annop-of-fundef
    (equal (fundef-annop
            (fundef extension specs declor asm? attribs declons body info))
           (and (decl-spec-list-annop specs)
                (declor-annop declor)
                (declon-list-annop declons)
                (comp-stmt-annop body)
                (fundef-infop info)))
    :expand (fundef-annop
             (fundef extension specs declor asm? attribs declons body info)))

  (defruled trans-unit-annop-of-trans-unit
    (equal (trans-unit-annop (trans-unit items info))
           (and (trans-item-list-annop items)
                (trans-unit-infop info)))
    :expand (trans-unit-annop (trans-unit items info)))

  (defruled trans-ensemble-annop-of-trans-ensemble
    (equal (trans-ensemble-annop
            (trans-ensemble units resolved-includes info))
           (and (filepath-trans-unit-map-annop units)
                (trans-ensemble-infop info)))
    :expand (trans-ensemble-annop
             (trans-ensemble units resolved-includes info)))

  ;; theorems about accessors:

  (defruled iconst-infop-of-iconst->info
    (implies (iconst-annop iconst)
             (iconst-infop (iconst->info iconst)))
    :enable iconst-annop)

  (defruled var-infop-of-expr-ident->info
    (implies (and (expr-annop expr)
                  (expr-case expr :ident))
             (var-infop (expr-ident->info expr)))
    :enable expr-annop)

  (defruled const-annop-of-expr-const->const
    (implies (and (expr-annop expr)
                  (expr-case expr :const))
             (const-annop (expr-const->const expr)))
    :enable expr-annop)

  (defruled expr-const-infop-of-expr-const->info
    (implies (and (expr-annop expr)
                  (expr-case expr :const))
             (expr-const-infop (expr-const->info expr)))
    :enable expr-annop)

  (defruled expr-string-infop-of-expr-string->info
    (implies (and (expr-annop expr)
                  (expr-case expr :string))
             (expr-string-infop (expr-string->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-arrsub->arg1
    (implies (and (expr-annop expr)
                  (expr-case expr :arrsub))
             (expr-annop (expr-arrsub->arg1 expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-arrsub->arg2
    (implies (and (expr-annop expr)
                  (expr-case expr :arrsub))
             (expr-annop (expr-arrsub->arg2 expr)))
    :enable expr-annop)

  (defruled expr-arrsub-infop-of-expr-arrsub->info
    (implies (and (expr-annop expr)
                  (expr-case expr :arrsub))
             (expr-arrsub-infop (expr-arrsub->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-funcall->fun
    (implies (and (expr-annop expr)
                  (expr-case expr :funcall))
             (expr-annop (expr-funcall->fun expr)))
    :enable expr-annop)

  (defruled expr-list-annop-of-expr-funcall->args
    (implies (and (expr-annop expr)
                  (expr-case expr :funcall))
             (expr-list-annop (expr-funcall->args expr)))
    :enable expr-annop)

  (defruled expr-funcall-infop-of-expr-funcall->info
    (implies (and (expr-annop expr)
                  (expr-case expr :funcall))
             (expr-funcall-infop (expr-funcall->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-unary->arg
    (implies (and (expr-annop expr)
                  (expr-case expr :unary))
             (expr-annop (expr-unary->arg expr)))
    :enable expr-annop)

  (defruled expr-unary-infop-of-expr-unary->info
    (implies (and (expr-annop expr)
                  (expr-case expr :unary))
             (expr-unary-infop (expr-unary->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-binary->arg1
    (implies (and (expr-annop expr)
                  (expr-case expr :binary))
             (expr-annop (expr-binary->arg1 expr)))
    :enable expr-annop)

  (defruled expr-annop-of-expr-binary->arg2
    (implies (and (expr-annop expr)
                  (expr-case expr :binary))
             (expr-annop (expr-binary->arg2 expr)))
    :enable expr-annop)

  (defruled expr-binary-infop-of-expr-binary->info
    (implies (and (expr-annop expr)
                  (expr-case expr :binary))
             (expr-binary-infop (expr-binary->info expr)))
    :enable expr-annop)

  (defruled expr-annop-of-const-expr->expr
    (implies (const-expr-annop const-expr)
             (expr-annop (const-expr->expr const-expr)))
    :enable const-expr-annop)

  (defruled const-expr-infop-of-const-expr->info
    (implies (const-expr-annop const-expr)
             (const-expr-infop (const-expr->info const-expr)))
    :enable const-expr-annop)

  (defruled designor-list-annop-of-desiniter->designors
    (implies (desiniter-annop desiniter)
             (designor-list-annop (desiniter->designors desiniter)))
    :enable desiniter-annop)

  (defruled initer-annop-of-desiniter->initer
    (implies (desiniter-annop desiniter)
             (initer-annop (desiniter->initer desiniter)))
    :enable desiniter-annop)

  (defruled desiniter-infop-of-desiniter->info
    (implies (desiniter-annop desiniter)
             (desiniter-infop (desiniter->info desiniter)))
    :enable desiniter-annop)

  (defruled declor-annop-of-init-declor->declor
    (implies (init-declor-annop init-declor)
             (declor-annop (init-declor->declor init-declor)))
    :enable init-declor-annop)

  (defruled initer-option-annop-of-init-declor->initer?
    (implies (init-declor-annop init-declor)
             (initer-option-annop (init-declor->initer? init-declor)))
    :enable init-declor-annop)

  (defruled init-declor-infop-of-init-declor->info
    (implies (init-declor-annop init-declor)
             (init-declor-infop (init-declor->info init-declor)))
    :enable init-declor-annop)

  (defruled spec/qual-list-annop-of-tyname->specquals
    (implies (tyname-annop tyname)
             (spec/qual-list-annop (tyname->specquals tyname)))
    :enable tyname-annop)

  (defruled absdeclor-option-annop-of-tyname->declor?
    (implies (tyname-annop tyname)
             (absdeclor-option-annop (tyname->declor? tyname)))
    :enable tyname-annop)

  (defruled tyname-infop-of-tyname->info
    (implies (tyname-annop tyname)
             (tyname-infop (tyname->info tyname)))
    :enable tyname-annop)

  (defruled decl-spec-list-annop-of-param-declon->specs
    (implies (param-declon-annop param-declon)
             (decl-spec-list-annop (param-declon->specs param-declon)))
    :enable param-declon-annop)

  (defruled param-declor-annop-of-param-declon->declor
    (implies (param-declon-annop param-declon)
             (param-declor-annop (param-declon->declor param-declon)))
    :enable param-declon-annop)

  (defruled attrib-spec-list-annop-of-param-declon->attribs
    (implies (param-declon-annop param-declon)
             (attrib-spec-list-annop (param-declon->attribs param-declon)))
    :enable param-declon-annop)

  (defruled param-declon-infop-of-param-declon->info
    (implies (param-declon-annop param-declon)
             (param-declon-infop (param-declon->info param-declon)))
    :enable param-declon-annop)

  (defruled declor-annop-of-param-declor-nonabstract->declor
    (implies (and (param-declor-annop param-declor)
                  (param-declor-case param-declor :nonabstract))
             (declor-annop (param-declor-nonabstract->declor param-declor)))
    :enable param-declor-annop)

  (defruled param-declor-nonabstract-infop-of-param-declor-nonabstract->info
    (implies (and (param-declor-annop param-declor)
                  (param-declor-case param-declor :nonabstract))
             (param-declor-nonabstract-infop
              (param-declor-nonabstract->info param-declor)))
    :enable param-declor-annop)

  (defruled decl-spec-list-annop-of-fundef->specs
    (implies (fundef-annop fundef)
             (decl-spec-list-annop (fundef->specs fundef)))
    :enable fundef-annop)

  (defruled declor-annop-of-fundef->declor
    (implies (fundef-annop fundef)
             (declor-annop (fundef->declor fundef)))
    :enable fundef-annop)

  (defruled declon-list-annop-of-fundef->declons
    (implies (fundef-annop fundef)
             (declon-list-annop (fundef->declons fundef)))
    :enable fundef-annop)

  (defruled comp-stmt-annop-of-fundef->body
    (implies (fundef-annop fundef)
             (comp-stmt-annop (fundef->body fundef)))
    :enable fundef-annop)

  (defruled fundef-infop-of-fundef->info
    (implies (fundef-annop fundef)
             (fundef-infop (fundef->info fundef)))
    :enable fundef-annop)

  (defruled trans-item-list-annop-of-trans-unit->items
    (implies (trans-unit-annop trans-unit)
             (trans-item-list-annop (trans-unit->items trans-unit)))
    :enable trans-unit-annop)

  (defruled trans-unit-annop-of-cdr-assoc
    (implies (and (filepath-trans-unit-map-annop map)
                  (filepath-trans-unit-mapp map)
                  (omap::assoc filepath map))
             (trans-unit-annop (cdr (omap::assoc filepath map))))
    :induct t
    :enable (omap::assoc
             filepath-trans-unit-map-annop))

  (defruled trans-unit-infop-of-trans-unit->info
    (implies (trans-unit-annop trans-unit)
             (trans-unit-infop (trans-unit->info trans-unit)))
    :enable trans-unit-annop)

  (defruled filepath-trans-unit-map-annop-of-trans-ensemble->units
    (implies (trans-ensemble-annop ensemble)
             (filepath-trans-unit-map-annop (trans-ensemble->units ensemble)))
    :enable trans-ensemble-annop)

  (defruled trans-ensemble-infop-of-trans-ensemble->info
    (implies (trans-ensemble-annop ensemble)
             (trans-ensemble-infop (trans-ensemble->info ensemble)))
    :enable trans-ensemble-annop)

  ;; Add the above theorems to the rule set.

  (add-to-ruleset
   abstract-syntax-annop-rules
   '(iconst-annop-of-iconst
     expr-annop-of-expr-ident
     expr-annop-of-expr-const
     expr-annop-of-expr-string
     expr-annop-of-expr-arrsub
     expr-annop-of-expr-funcall
     expr-annop-of-expr-unary
     expr-annop-of-expr-binary
     const-expr-annop-of-const-expr
     desiniter-annop-of-desiniter
     tyname-annop-of-tyname
     param-declon-annop-of-param-declon
     param-declor-annop-of-param-declor-nonabstract
     param-declor-nonabstract-infop-of-param-declor-nonabstract->info
     init-declor-annop-of-init-declor
     fundef-annop-of-fundef
     trans-unit-annop-of-trans-unit
     trans-ensemble-annop-of-trans-ensemble
     iconst-infop-of-iconst->info
     var-infop-of-expr-ident->info
     const-annop-of-expr-const->const
     expr-const-infop-of-expr-const->info
     expr-string-infop-of-expr-string->info
     expr-annop-of-expr-arrsub->arg1
     expr-annop-of-expr-arrsub->arg2
     expr-arrsub-infop-of-expr-arrsub->info
     expr-annop-of-expr-funcall->fun
     expr-list-annop-of-expr-funcall->args
     expr-funcall-infop-of-expr-funcall->info
     expr-annop-of-expr-unary->arg
     expr-unary-infop-of-expr-unary->info
     expr-annop-of-expr-binary->arg1
     expr-annop-of-expr-binary->arg2
     expr-binary-infop-of-expr-binary->info
     expr-annop-of-const-expr->expr
     const-expr-infop-of-const-expr->info
     designor-list-annop-of-desiniter->designors
     initer-annop-of-desiniter->initer
     desiniter-infop-of-desiniter->info
     declor-annop-of-init-declor->declor
     initer-option-annop-of-init-declor->initer?
     init-declor-infop-of-init-declor->info
     spec/qual-list-annop-of-tyname->specquals
     absdeclor-option-annop-of-tyname->declor?
     tyname-infop-of-tyname->info
     declor-annop-of-param-declor-nonabstract->declor
     decl-spec-list-annop-of-param-declon->specs
     param-declor-annop-of-param-declon->declor
     attrib-spec-list-annop-of-param-declon->attribs
     param-declon-infop-of-param-declon->info
     decl-spec-list-annop-of-fundef->specs
     declor-annop-of-fundef->declor
     declon-list-annop-of-fundef->declons
     comp-stmt-annop-of-fundef->body
     fundef-infop-of-fundef->info
     trans-item-list-annop-of-trans-unit->items
     trans-unit-annop-of-cdr-assoc
     trans-unit-infop-of-trans-unit->info
     filepath-trans-unit-map-annop-of-trans-ensemble->units
     trans-ensemble-infop-of-trans-ensemble->info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-type ((expr exprp))
  :guard (and (expr-unambp expr)
              (expr-annop expr))
  :returns (type typep)
  :short "Type of an expression, from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type is calculated from
     the validation information present in the expression,
     without performing any type calculation
     of the kind performed by the validator
     (e.g. this function does not attempt to calculate
     the type of a binary expression based on
     the operator and the types of the operands).
     If there is not enough information,
     the unknown type is returned.")
   (xdoc::p
    "For a conditional information,
     we look at the types of the two branches,
     and if they have exactly the same type,
     we return that type, otherwise we return the unkwnon type.
     If there is no `then' branch, we also return the unknown type.
     This is an approximation."))
  (expr-case
   expr
   :ident (var-info->type expr.info)
   :const (expr-const-info->type expr.info)
   :string (expr-string-info->type expr.info)
   :paren (expr-type expr.inner)
   :gensel (type-unknown)
   :arrsub (expr-arrsub-info->type expr.info)
   :funcall (expr-funcall-info->type expr.info)
   :member (type-unknown)
   :memberp (type-unknown)
   :complit (type-unknown)
   :unary (expr-unary-info->type expr.info)
   :label-addr (type-pointer (type-void))
   :sizeof (type-unknown)
   :alignof (type-unknown)
   :cast (tyname-info->type (tyname->info expr.type))
   :binary (expr-binary-info->type expr.info)
   :cond (b* (((when (expr-option-case expr.then :none)) (type-unknown))
              (expr.then (expr-option-some->val expr.then))
              (then-type (expr-type expr.then))
              (else-type (expr-type expr.else)))
           (if (equal then-type else-type)
               then-type ; = else-type
             (type-unknown)))
   :comma (expr-type expr.next)
   :stmt (type-unknown)
   :tycompat (type-unknown)
   :offsetof (type-unknown)
   :va-arg (type-unknown)
   :extension (expr-type expr.expr)
   :otherwise (prog2$ (impossible) (type-unknown)))
  :measure (expr-count expr)
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-type ((initer initerp))
  :guard (and (initer-unambp initer)
              (initer-annop initer))
  :returns (type typep)
  :short "Type of an initializer, from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only cover the case of a single initializer,
     for which we return the type of the underlying expression.
     We return the unknown type for a non-single initializer for now."))
  (initer-case
   initer
   :single (expr-type initer.expr)
   :list (type-unknown))
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines stmts-types
  :short "Types of statements and related entities,
          from the validation information."

  (define stmt-types ((stmt stmtp))
    :guard (and (stmt-unambp stmt)
                (stmt-annop stmt))
    :returns (types type-option-setp)
    :parents (validation-information stmts-types)
    :short "Types of a statement, from the validation information."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return a set of optional types:
       a @('nil') means that the statement's may terminate
       without a @('return') (e.g. an expression statement);
       a @('void') means that the statement may terminate
       with a @('return') without an expression;
       and a non-@('void') type means that the statemetn may terminate
       with a @('return') with an expression of that type.")
     (xdoc::p
      "Similarly to @(tsee expr-type),
       the types calculated by this function are an approximation.
       We return the empty set in cases that we do not handle yet.
       This is adequate for the current use of this function,
       but it will need to be suitably extended."))
    (stmt-case
     stmt
     :labeled (stmt-types stmt.stmt)
     :compound (comp-stmt-types stmt.stmt)
     :expr (set::insert nil nil)
     :null-attrib (set::insert nil nil)
     :if (set::insert nil (stmt-types stmt.then))
     :ifelse (set::union (stmt-types stmt.then)
                         (stmt-types stmt.else))
     :switch nil
     :while (set::insert nil (stmt-types stmt.body))
     :dowhile (set::insert nil (stmt-types stmt.body))
     :for-expr nil
     :for-declon nil
     :for-ambig (impossible)
     :goto nil
     :gotoe nil
     :continue nil
     :break nil
     :return (expr-option-case
              stmt.expr?
              :some (set::insert (expr-type stmt.expr?.val) nil)
              :none (set::insert (type-void) nil))
     :return-attrib (set::insert (expr-type stmt.expr) nil)
     :asm nil)
    :measure (stmt-count stmt))

  (define comp-stmt-types ((cstmt comp-stmtp))
    :guard (and (comp-stmt-unambp cstmt)
                (comp-stmt-annop cstmt))
    :returns (types type-option-setp)
    :parents (validation-information stmts-types)
    :short "Types of a compound statement, from the validation information."
    (block-item-list-types (comp-stmt->items cstmt))
    :measure (comp-stmt-count cstmt))

  (define block-item-types ((item block-itemp))
    :guard (and (block-item-unambp item)
                (block-item-annop item))
    :returns (types type-option-setp)
    :parents (validation-information stmts-types)
    :short "Types of a block item, from the validation information."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return a set of optional types, as in @(tsee stmt-types):
       see the documentation of that function for a rationale."))
    (block-item-case
     item
     :declon (set::insert nil nil)
     :stmt (stmt-types item.stmt)
     :ambig (impossible))
    :measure (block-item-count item))

  (define block-item-list-types ((items block-item-listp))
    :guard (and (block-item-list-unambp items)
                (block-item-list-annop items))
    :returns (types type-option-setp)
    :parents (validation-information stmts-types)
    :short "Types of a list of block items, from the validation information."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return a set of optional types, as in @(tsee stmt-types):
       see the documentation of that function for a rationale.")
     (xdoc::p
      "If the list is empty, we return the singleton set with @('nil').
       If the list is not empty,
       we take the union of the types of the first and remaining block items,
       but first we remove @('nil') from the first set (if present).
       The removal is because,
       if the first block item terminates without @('return'),
       the whole list of block items does not necessarily do so;
       it happens only if the rest of the block items in the list does,
       which is accounted for in the set of optional types
       for the rest of the list."))
    (b* (((when (endp items)) (set::insert nil nil))
         (item-types (block-item-types (car items)))
         (items-types (block-item-list-types (cdr items))))
      (set::union (set::delete nil item-types) items-types))
    :measure (block-item-list-count items))

  :verify-guards :after-returns

  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules)))

  ///

  (fty::deffixequiv-mutual stmts-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-types ((fundef fundefp))
  :guard (and (fundef-unambp fundef)
              (fundef-annop fundef))
  :returns (types type-setp
                  :hints
                  (("Goal"
                    :in-theory
                    (enable
                     type-setp-when-type-option-setp-and-nil-not-member))))
  :short "Types of the values returned by a function,
          from the validation information."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set of possible types returned by the function is
     the set of possible types returned by the body,
     roughly speaking.
     More precisely, the latter is a set of optional types,
     where @('nil') means that the body terminates without a @('return').
     For a function, this is equivalent to a @('return') without expression.
     Thus, we turn the @('nil') in the set of types, if any, into @('void') type,
     obtaining the set of types (not optional types) of the function's result.
     We use that in the theorem about the function,
     which says that the result,
     which is an optional value in our formal semantics,
     has a type in the set;
     we use @(tsee c::type-of-value-option) to map values to their types,
     and @('nil') to @('void').")
   (xdoc::p
    "Although a function definition has one return type (possibly @('void')),
     its body may return values of slightly different types,
     possibly subject to conversions.
     However, our formal semantics of C does not cover those conversions yet,
     so we adopt the more general view here."))
  (b* ((types (comp-stmt-types (fundef->body fundef)))
       (types (if (set::in nil types)
                  (set::insert (type-void) (set::delete nil types))
                types)))
    types)
  :guard-hints (("Goal" :in-theory (enable* abstract-syntax-annop-rules))))
