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
(include-book "abstract-syntax-operations")

(include-book "kestrel/fty/nat-option" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ initializer-validation
  :parents (validation)
  :short "Material for validating initializers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validating initializers is complicated in C.
     It involves going through sub-objects of objects."))
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
  (:array-index ((of type) (index nat) (range? nat-option)))
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
                   (filtered (members-filter-contributors members)))
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
                  (filtered (members-filter-contributors members)))
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
                                     (members-filter-contributors (rest members)))))
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
                                       (members-filter-contributors
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
