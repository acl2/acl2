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

(include-book "read-write-variables")
(include-book "../language/pointer-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-symbolic-computation-states
  :parents (atc-event-and-code-generation)
  :short "Canonical representation of
          the computation states for the symbolic execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting from a generic (symbolic) computation state,
     a symbolic execution starting with @(tsee exec-fun)
     will push a frame (for the function),
     possibly read variables,
     possibly create new variables,
     possibly write existing variables,
     possibly enter new scopes,
     possibly exit existing scopes,
     and eventually pop the frame.
     Just one frame is pushed and then popped
     because the symbolic execution is compositional w.r.t. functions,
     i.e. the symbolic execution rewrites function calls in function bodies
     using the theorems about the called functions.")
   (xdoc::p
    "The dynamic semantics functions that perform the above actions,
     namely @(tsee push-frame), @(tsee enter-scope), @(tsee create-var), etc.,
     go into the frame stack component of the computation state,
     via the @(tsee compustate->frames) accessor.
     That would lead to a complex symbolic term for the computation state.")
   (xdoc::p
    "Instead, we pull the ``additions'' to the computation state,
     i.e. the added frames, scopes, and variables,
     out of the computation state via the functions
     @(tsee add-frame), @(tsee enter-scope), and @(tsee add-var):
     the first and third one are defined below,
     while the second one is from the dynamic semantics of C.
     These three functions are defined to
     push the frames, scopes, and variables into the computation state,
     but we leave these functions disabled during symbolic execution,
     so that the symbolic computation states has these additions explicit.
     Thus, the symbolic computation state is
     a sequence of applications of those three functions
     to an initial symbolic computation state @('<compst>'):")
   (xdoc::codeblock
    "(add-var ... (enter-scope (add-var ... (add-frame ... <compst>)...)")
   (xdoc::p
    "The reason for introducing a new function @(tsee add-var),
     instead of just using @(tsee create-var) (and leaving it disabled),
     is that @(tsee add-var) unconditionally satisfies certain properties
     that @(tsee create-var) satisfies when it does not return an error:
     @(tsee add-var) unconditionally returns a computation state,
     and always ensures that the added variable is in the computation state.
     During symbolic execution,
     @(tsee create-var) is replaced with @(tsee add-var)
     via a rule that requires @(tsee create-var) to not return an error:
     in a way, @(tsee add-var) ``caches'' the aforementioned properties.
     This leads to simpler rules on this kind of computation states:
     for example, when @(tsee read-var) appears applied to @(tsee add-var)
     during symbolic execution,
     if the two variables are equal,
     we can readily rewrite this term to the value in @(tsee add-var),
     because that function guarantees the variable to exist with that value.
     In contrast, if @(tsee read-var) appeared applied to @(tsee create-var),
     additional hypotheses would be needed (and would have to be discharged)
     saying that @(tsee create-var) succeeds.")
   (xdoc::p
    "For a similar reason, we introduce a function @(tsee update-var)
     that replaces @(tsee write-var) when the latter succeeds,
     and that is easier and more efficient to manipulate
     during symbolic execution.")
   (xdoc::p
    "Given these canonical representations of computation states,
     we prove theorems that describe
     the effect of @(tsee push-frame) and other functions
     on computation states of this form,
     where the effect is another state in that form.
     These theorems are enabled during symbolic execution,
     and manipulate the computation state.")
   (xdoc::p
    "In the presence of C loops,
     which are represented by ACL2 recursive functions,
     we generate theorems that describe the execution of the loops
     starting from generic (symbolic) computation states.
     The execution of a loop does not push a new frame,
     because the loop executes in the frame of the enclosing C function.
     In this case, the initial generic computation state
     includes part of the frame of the enclosing C function;
     the execution of the loop may add new scopes and variables,
     so in this case the symbolic computation state looks like")
   (xdoc::codeblock
    "(add-var ... (add-var ... (enter-scope <compst>)...)")
   (xdoc::p
    "In fact, the innermost function there
     must be @(tsee enter-scope) (it cannot be @(tsee add-var)),
     because the loops we generate have compound statements as bodies,
     which create new scopes.")
   (xdoc::p
    "The initial symbolic computation state @('<compst>')
     contains the initial part of the frame
     of the function that contains the loop;
     the loop extends the frame with @(tsee enter-scope) and @(tsee add-var)
     as shown above.
     But the structure of the initial part of the frame
     is not known in the symbolic execution for the loop itself:
     it is just the initial @('<compst>').
     However, the loop may access variables in that initial part of the frame:
     the theorem generated for the loop includes hypotheses
     saying that @(tsee read-var) applied to @('<compst>')
     for certain variables (i.e. identifiers)
     yields values of certain C types:
     this way, any of these @(tsee read-var) calls
     arising during symbolic execution will match those hypotheses.
     A loop may write to those variables:
     in this case, after replacing @(tsee write-var) with @(tsee update-var)
     right away as explained earlier,
     the @(tsee update-var) will go through
     all the @(tsee add-var) and @(tsee enter-scope) layers shown above,
     and reach @('<compst>'), where it is not further reducible.
     This may happen for several different variables,
     leading to states of the form")
   (xdoc::codeblock
    "(...
      (add-var (enter-scope ... (update-var ... (update-var ... <compst>)...)")
   (xdoc::p
    "Below we introduce rules to order these @(tsee update-var)s
     according to the variables,
     maintaining a canonical form.")
   (xdoc::p
    "Note that this form of the computation states
     serves to represent side effects performed by the loop
     on the initial computation state.
     The same approach is used to generate proofs for
     more general side effects, e.g. on the heap, as explained below.")
   (xdoc::p
    "A computation state has a heap,
     whose objects (particularly arrays and structures)
     may be updated during the symbolic execution.
     We represent these updates via the function @(tsee update-object),
     which is similar to @(tsee write-object)
     but always satisfies additional properties:
     the relation between @(tsee update-object) and @(tsee write-object)
     is similar to the one between @(tsee update-var) and @(tsee write-var)
     and to the one between @(tsee add-var) and @(tsee create-var),
     explained above.")
   (xdoc::p
    "Heap objects may be updated by C functions and C loops,
     so they need to be incorporated in both of
     the symbolic computation state representations described above.
     We push the @(tsee update-object) past all the other functions,
     leading to states of the form")
   (xdoc::codeblock
    "(... (add-frame (update-object ... (update-object ... <compst>)...)")
   (xdoc::p
    "for C functions and of the form")
   (xdoc::codeblock
    "(... (enter-scope (update-object ... (update-object ... <compst>)...)")
   (xdoc::p
    "for C loops.
     We order the @(tsee update-object) calls
     according to their first argument (i.e. the object designator).
     Note that for a C function this first argument is
     @(tsee value-pointer->designator) applied to an ACL2 variable,
     while for a C loop it is
     @(tsee value-pointer->designator) applied to
     a @('(read-var <identifier> ...)').
     These two kinds of first arguments never appear together,
     i.e. in the same theorem,
     because each theorem is for either a C function or a C loop.
     We prove rules that order @(tsee update-object)s
     according to the symbols,
     which apply to proofs of theorems of C functions;
     and we prove rules that order @(tsee update-object)s
     according to the identifiers,
     which apply to proofs of theorems of C loops.")
   (xdoc::p
    "Objects in static storage are treated similarly to objects in the heap.
     Instead of @(tsee write-object) and @(tsee update-object),
     we use @(tsee write-static-var) and @(tsee update-static-var).
     In a canonical computation state,
     we order @(tsee update-static-var) calls
     before @(tsee update-object) calls.")
   (xdoc::p
    "After introducing the ACL2 functions
     that represent the canonical symbolic computation states,
     we provide theorems expressing how
     functions like @(tsee push-frame) transform those computation states,
     maintaining their canonical form."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-frame ((fun identp) (compst compustatep))
  :returns (new-compst compustatep)
  :short (xdoc::topstring
          "Add a frame to a "
          (xdoc::seetopic "atc-symbolic-computation-states"
                          "canonical representation of computation states")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "This adds a frame with an empty scope."))
  (push-frame (make-frame :function fun :scopes (list nil))
              compst)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var ((var identp) (val valuep) (compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (new-compst compustatep)
  :short (xdoc::topstring
          "Add a variable to a "
          (xdoc::seetopic "atc-symbolic-computation-states"
                          "canonical representation of computation states")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee create-var),
     but it only operates on computation states with frames
     (so that the variable is added to the top scope of the top frame,
     and not to the static storage),
     and it never returns an error:
     it always adds the variable to the current scope.
     If there are frames,
     and the variable does not already exist in the current scope,
     this is equivalent to @(tsee create-var), as proved later.")
   (xdoc::p
    "The reason for only operating on computation states with frames
     is that, during symbolic execution, we always have frames,
     because we are executing code in some function.
     Thus, during symbolic execution we are only interested in
     creating variables in the top scope of the top frame,
     never in static storage.
     In contrast, @(tsee create-var) is a more general function,
     that creates variables in both automatic and static storage."))
  (b* ((frame (top-frame compst))
       (scopes (frame->scopes frame))
       (scope (car scopes))
       (new-scope (omap::update (ident-fix var)
                                (remove-flexible-array-member val)
                                scope))
       (new-scopes (cons new-scope (cdr scopes)))
       (new-frame (change-frame frame :scopes new-scopes))
       (new-compst (push-frame new-frame (pop-frame compst))))
    new-compst)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-in-scopes-p ((var identp) (scopes scope-listp))
  :returns (yes/no booleanp)
  :short "Check if a variable is in a list of scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an auxiliary function, used by others below."))
  (b* (((when (endp scopes)) nil)
       (var-val (omap::assoc (ident-fix var) (scope-fix (car scopes))))
       ((when (consp var-val)) t))
    (var-in-scopes-p var (cdr scopes)))
  :hooks (:fix)
  ///

  (defruled var-in-scopes-p-when-valuep-of-read-auto-var-aux
    (implies (valuep (read-auto-var-aux var scopes))
             (var-in-scopes-p var scopes))
    :induct t
    :enable read-auto-var-aux)

  (defruled var-in-scopes-p-when-read-auto-var-aux
    (implies (read-auto-var-aux var scopes)
             (var-in-scopes-p var scopes))
    :induct t
    :enable read-auto-var-aux)

  (defruled not-var-in-scopes-p-when-not-read-auto-var-aux
    (implies (not (read-auto-var-aux var scopes))
             (not (var-in-scopes-p var scopes)))
    :induct t
    :enable read-auto-var-aux
    :prep-lemmas
    ((defrule lemma
       (implies (and (scopep x)
                     (consp (omap::assoc k x)))
                (cdr (omap::assoc k x)))
       :use valuep-of-cdr-of-assoc-scopep
       :disable valuep-of-cdr-of-assoc-scopep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-var ((var identp) (val valuep) (compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (new-compst compustatep)
  :short (xdoc::topstring
          "Update a variable in a "
          (xdoc::seetopic "atc-symbolic-computation-states"
                          "canonical representation of computation states")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee write-var), but it does not return an error.
     First, if we do not find the variable in automatic storage,
     we add it to static storage unconditionally:
     this ensures that the variable is always there,
     which simplifies other rules;
     we check that the variable is actually there
     when we turn @(tsee write-var) into @(tsee update-var),
     in another rule.
     Second, we do not check the type of the new value
     against the type of the old value if the variable is found,
     and instead we unconditionally overwrite the old value with the new value:
     this ensures that the new value is always there,
     which simplified other rules;
     we check that the types match
     when we turn @(tsee write-var) into @(tsee update-var),
     in another rule.")
   (xdoc::p
    "The guard requires at least one frame.
     This is adequate,
     since we only use this function during symbolic execution,
     when we are executing some function's code,
     and so there must be always some frame.
     (Actually, given that this function is only used for symbolic execution,
     it does not need to be guard-verified;
     the same applies to @(tsee add-frame) and @(tsee add-var),
     but for now we keep them guard-verified.)"))
  (b* ((frame (top-frame compst))
       (scopes (frame->scopes frame))
       (autop (var-in-scopes-p var scopes))
       ((when autop)
        (b* ((new-scopes (update-var-aux var val scopes))
             (new-frame (change-frame frame :scopes new-scopes)))
          (push-frame new-frame (pop-frame compst))))
       (static (compustate->static compst))
       (new-static (omap::update (ident-fix var)
                                 (remove-flexible-array-member val)
                                 static)))
    (change-compustate compst :static new-static))
  :hooks (:fix)

  :prepwork
  ((define update-var-aux ((var identp) (val valuep) (scopes scope-listp))
     :returns (new-scopes scope-listp)
     :parents nil
     (b* (((when (endp scopes)) nil)
          (scope (scope-fix (car scopes)))
          (pair (omap::assoc (ident-fix var) scope))
          ((when (consp pair))
           (cons (omap::update (ident-fix var)
                               (remove-flexible-array-member val)
                               scope)
                 (scope-list-fix (cdr scopes)))))
       (cons scope (update-var-aux var val (cdr scopes))))
     :hooks (:fix)
     ///
     (defret consp-of-update-var-aux
       (equal (consp new-scopes)
              (consp scopes))
       :hints (("Goal" :induct t)))
     (defruled var-in-scopes-p-of-update-var-aux
       (iff (c::var-in-scopes-p var (c::update-var-aux var2 val scopes))
            (c::var-in-scopes-p var scopes))
       :induct t
       :enable var-in-scopes-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-static-var ((var identp) (val valuep) (compst compustatep))
  :returns (new-compst compustatep)
  :short (xdoc::topstring
          "Update a variable in static storage in a "
          (xdoc::seetopic "atc-symbolic-computation-states"
                          "canonical representation of computation states")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee update-var),
     but for variables in static storage.
     It is equivalent to @(tsee write-static-var)
     when the latter does not return an error."))
  (b* ((static (compustate->static compst))
       (new-static (omap::update (ident-fix var)
                                 (remove-flexible-array-member val)
                                 static))
       (new-compst (change-compustate compst :static new-static)))
    new-compst)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define objdesign->base-address ((objdes objdesignp))
  :returns (addr addressp)
  :short "Base address of an object designator."
  :long
  (xdoc::topstring
   (xdoc::p
    "We find the top-level object by recursion.
     If it is an address, we return it, since it is the base address.
     If it is a variable, for now we just return a dummy address:
     for now this function is only used with object designators
     that have addresses at the top level,
     so this is adequate;
     this will be properly generalized at some point."))
  (objdesign-case objdes
                  :static (address 0)
                  :auto (address 0)
                  :alloc objdes.get
                  :element (objdesign->base-address objdes.super)
                  :member (objdesign->base-address objdes.super))
  :measure (objdesign-count objdes)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-object ((objdes objdesignp) (val valuep) (compst compustatep))
  :returns (new-compst compustatep)
  :short (xdoc::topstring
          "Update an object in a "
          (xdoc::seetopic "atc-symbolic-computation-states"
                          "canonical representation of computation states")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee write-object),
     but it does not return an error,
     and it only really handles top-level object designators,
     by taking the base address of the object designators,
     which is what we need for now.
     We update the heap with the new object regardless of
     whether an old object at that address exists or not,
     and whether, if it exists, its type matches the new object.
     This way, @(tsee update-object) always guarantees that
     the object goes into the heap,
     thus simplifying rules about it.
     When we replace @(tsee write-object)
     with @(tsee update-object),
     we ensure that all the conditions mentioned above hold,
     so in a way @(tsee update-object) caches the fact that
     those conditions are satisfied."))
  (b* ((addr (objdesign->base-address objdes))
       (heap (compustate->heap compst))
       (new-heap (omap::update addr (value-fix val) heap))
       (new-compst (change-compustate compst :heap new-heap)))
    new-compst)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-autop ((var identp) (compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (yes/no booleanp)
  :short "Check if a variable is found in automatic storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "This checks whether the variable is in the scopes of the top frame.
     Thus, it only looks in the currently accessible (by variable names)
     automatic storage; it does not look in other frames.")
   (xdoc::p
    "This predicate serves to establish, when negated,
     that a variable is found in static storage, and not in automatic storage.
     Rules for this process are given later."))
  (var-in-scopes-p var (frame->scopes (top-frame compst)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-push-frame-rules
  :short "Rules about @(tsee push-frame)."
  :long
  (xdoc::topstring
   (xdoc::p
    "In @(tsee exec-fun), a scope is initialized
     and a frame is pushed with that scope.
     Here we provide two theorems to turn that into a canonical representation.
     Assuming that @(tsee init-scope) is rewritten
     to a nest of @(tsee omap::update) calls
     (as it is, because we use rules for @(tsee init-scope) that do that),
     the two theorems below move the variables into @(tsee add-var) calls,
     and finally turn @(tsee push-frame) into @(tsee add-frame).")
   (xdoc::p
    "During symbolic execution,
     the values stored into a scope never have flexible array members.
     This is because @(tsee init-scope) removes them, if present.
     During symbolic execution, these values will satisfy that predicate,
     making the application of @(tsee remove-flexible-array-member)
     in the @(tsee omap::update) nest disappear,
     which justifies its absence
     in the left side of @('push-frame-of-one-nonempty-scope')."))

  (defruled push-frame-of-one-empty-scope
    (equal (push-frame (frame fun (list nil)) compst)
           (add-frame fun compst))
    :enable add-frame)

  (defruled push-frame-of-one-nonempty-scope
    (implies (and (identp var)
                  (valuep val)
                  (scopep scope)
                  (not (flexible-array-member-p val)))
             (equal (push-frame (frame fun (list (omap::update var val scope)))
                                compst)
                    (add-var var
                             val
                             (push-frame (frame fun (list scope)) compst))))
    :enable (push-frame
             top-frame
             pop-frame
             add-var
             compustate-frames-number))

  (defval *atc-push-frame-rules*
    '(push-frame-of-one-empty-scope
      push-frame-of-one-nonempty-scope)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-pop-frame-rules
  :short "Rules about @(tsee pop-frame)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about @(tsee pop-frame)
     remove all the @(tsee add-var) and @(tsee enter-scope) calls
     until they reach @(tsee add-frame),
     with which @(tsee pop-frame) neutralizes.
     No rules are needed for
     computation states that start with @(tsee update-var)
     because these only occur when executing loops,
     which do not pop frames."))

  (defruled pop-frame-of-add-frame
    (implies (compustatep compst)
             (equal (pop-frame (add-frame fun compst))
                    compst))
    :enable (pop-frame add-frame))

  (defruled pop-frame-of-enter-scope
    (equal (pop-frame (enter-scope compst))
           (pop-frame compst))
    :enable (pop-frame
             enter-scope
             push-frame))

  (defruled pop-frame-of-add-var
    (equal (pop-frame (add-var var val compst))
           (pop-frame compst))
    :enable (pop-frame
             add-var
             push-frame))

  (defruled pop-frame-of-exit-scope
    (equal (pop-frame (exit-scope compst))
           (pop-frame compst))
    :enable (pop-frame
             exit-scope
             push-frame))

  (defruled pop-frame-of-if*
    (equal (pop-frame (if* a b c))
           (if* a (pop-frame b) (pop-frame c)))
    :enable if*)

  (defval *atc-pop-frame-rules*
    '(pop-frame-of-add-frame
      pop-frame-of-enter-scope
      pop-frame-of-add-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-enter-scope-rules
  :short "Rules about @(tsee enter-scope)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We do not provide any theorem about @(tsee enter-scope),
     as it is part of the canonical representation of computation states.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exit-scope-rules
  :short "Rules about @(tsee exit-scope)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about @(tsee exit-scope)
     cancel it with @(tsee enter-scope)
     and move it past @(tsee add-var).
     No rule for @(tsee add-frame) is needed
     because that case should never happen in the symbolic execution.
     No rule is needed for computation states that start with @(tsee update-var)
     because @(tsee update-var) is always pushed past @(tsee enter-scope)."))

  (defruled exit-scope-of-enter-scope-when-compustatep
    (implies (and (compustatep compst)
                  (> (compustate-frames-number compst) 0))
             (equal (exit-scope (enter-scope compst))
                    compst))
    :enable (enter-scope
             exit-scope
             push-frame
             top-frame
             pop-frame
             compustate-frames-number
             len))

  (defruled exit-scope-of-add-var
    (equal (exit-scope (add-var var val compst))
           (exit-scope compst))
    :enable (exit-scope add-var))

  (defruled exit-scope-of-if*
    (equal (exit-scope (if* a b c))
           (if* a (exit-scope b) (exit-scope c)))
    :enable if*)

  (defval *atc-exit-scope-rules*
    '(exit-scope-of-enter-scope-when-compustatep
      exit-scope-of-add-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-create-var-rules
  :short "Rules about @(tsee create-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem about @(tsee create-var) turns that into @(tsee add-var),
     provided that the variable can be created,
     which we check via the function @('create-var-okp') introduced below,
     and also provided that there are frames.
     The latter condition is motivated by the fact that,
     during symbolic execution, we always have frames,
     because we are always executing code in some function;
     thus, we only need to replace @(tsee create-var) with @(tsee add-var)
     when there are frames.
     Additional theorems about @('create-var-okp')
     go through the layers of the computation states to check this condition.
     No rule is needed for @('create-var-ok') on @(tsee update-var),
     because @(tsee update-var) is pushed past the first @(see enter-scope)."))

  (define create-var-okp ((var identp) (compst compustatep))
    :guard (> (compustate-frames-number compst) 0)
    :returns (yes/no booleanp)
    :parents nil
    (b* ((frame (top-frame compst))
         (scopes (frame->scopes frame))
         (scope (car scopes)))
      (not (consp (omap::assoc (ident-fix var) scope))))
    :hooks (:fix))

  (defruled create-var-okp-of-add-frame
    (create-var-okp var (add-frame fun compst))
    :enable (create-var-okp add-frame))

  (defruled create-var-okp-of-enter-scope
    (create-var-okp var (enter-scope compst))
    :enable (create-var-okp enter-scope))

  (defruled create-var-okp-of-add-var
    (equal (create-var-okp var (add-var var2 val compst))
           (and (not (equal (ident-fix var)
                            (ident-fix var2)))
                (create-var-okp var compst)))
    :enable (create-var-okp add-var))

  (defruled create-var-okp-of-update-var
    (equal (create-var-okp var (update-var var2 val compst))
           (create-var-okp var compst))
    :enable (create-var-okp
             update-var
             update-var-aux
             var-in-scopes-p
             push-frame
             pop-frame
             top-frame)
    :expand (update-var-aux var2
                            val
                            (frame->scopes (car (compustate->frames compst)))))

  (defruled create-var-okp-of-update-object
    (equal (create-var-okp var (update-object objdes val compst))
           (create-var-okp var compst))
    :enable (create-var-okp update-object top-frame))

  (defruled create-var-to-add-var
    (implies (and (create-var-okp var compst)
                  (> (compustate-frames-number compst) 0))
             (equal (create-var var val compst)
                    (add-var var val compst)))
    :enable (create-var add-var create-var-okp))

  (defval *atc-create-var-rules*
    '(create-var-to-add-var
      create-var-okp-of-add-frame
      create-var-okp-of-enter-scope
      create-var-okp-of-add-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-write-var-rules
  :short "Rules about @(tsee write-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem about @(tsee write-var) turns it into @(tsee update-var),
     similarly to @(tsee create-var) being turned into @(tsee add-var).
     The condition for the replacemenet is captured by @('write-var-okp'),
     for which we supply rules to go through the computation state layers.
     When the computation state (meta) variable is reached,
     it must be the case that there are hypotheses available
     saying that reading the variable yields a value:
     this happens for loop proofs, for variables created outside the loop,
     which are therefore not visible as @(tsee add-var)s.
     The rule is used as last resort,
     only if the computation state is an ACL2 variable
     (as enforced by the @(tsee syntaxp) hypothesis).")
   (xdoc::p
    "We also include the executable counterpart of @(tsee typep)
     in the list of rules related to @(tsee write-var).
     This is needed to discharge some @(tsee typep) hypotheses
     that arise during symbolic execution and are applied to quoted constants.
     We may arrange things in the future so that
     these quoted constants do not arise
     and thus there is no need for the executable counterpart of @(tsee typep)
     to be included in the list of rules here.")
   (xdoc::p
    "Also see @(tsee atc-write-static-var-rules)
     for a rule that relates @('write-var-okp') and @(tsee add-frame)."))

  (define write-var-okp ((var identp) (val valuep) (compst compustatep))
    :guard (> (compustate-frames-number compst) 0)
    :returns (yes/no booleanp)
    :parents nil
    (b* ((scopes (frame->scopes (top-frame compst)))
         (autop (var-in-scopes-p var scopes))
         ((when autop) (write-var-aux-okp var val scopes))
         (static (compustate->static compst))
         (pair (omap::assoc (ident-fix var) static)))
      (and (consp pair)
           (equal (type-of-value (cdr pair))
                  (type-of-value val))))
    :hooks (:fix)
    :prepwork
    ((define write-var-aux-okp ((var identp) (val valuep) (scopes scope-listp))
       :returns (yes/no booleanp)
       :parents nil
       (b* (((when (endp scopes)) nil)
            (scope (scope-fix (car scopes)))
            (pair (omap::assoc (ident-fix var) scope))
            ((when (consp pair))
             (equal (type-of-value (cdr pair))
                    (type-of-value val))))
         (write-var-aux-okp var val (cdr scopes)))
       :hooks (:fix))))

  (defruled write-var-okp-of-enter-scope
    (equal (write-var-okp var val (enter-scope compst))
           (write-var-okp var val compst))
    :enable (write-var-okp
             write-var-aux-okp
             var-in-scopes-p
             enter-scope
             push-frame
             pop-frame
             top-frame))

  (defruled write-var-okp-of-add-var
    (equal (write-var-okp var val (add-var var2 val2 compst))
           (if (equal (ident-fix var)
                      (ident-fix var2))
               (equal (type-of-value val2)
                      (type-of-value val))
             (write-var-okp var val compst)))
    :enable (write-var-okp
             write-var-aux-okp
             var-in-scopes-p
             add-var
             push-frame
             pop-frame
             top-frame))

  (defruled write-var-okp-of-update-var
    (equal (write-var-okp var val (update-var var2 val2 compst))
           (if (equal (ident-fix var)
                      (ident-fix var2))
               (equal (type-of-value val2)
                      (type-of-value val))
             (write-var-okp var val compst)))
    :enable (write-var-okp
             update-var
             top-frame
             push-frame
             pop-frame
             var-in-scopes-p-of-update-var-aux)
    :prep-lemmas
    ((defrule lemma1
       (implies (and (var-in-scopes-p var scopes)
                     (var-in-scopes-p var2 scopes))
                (equal (write-var-aux-okp var
                                          val
                                          (update-var-aux var2 val2 scopes))
                       (if (equal (ident-fix var)
                                  (ident-fix var2))
                           (equal (type-of-value val2)
                                  (type-of-value val))
                         (write-var-aux-okp var val scopes))))
       :induct t
       :enable (var-in-scopes-p
                write-var-aux-okp
                update-var-aux))
     (defrule lemma2
       (implies (or (not (var-in-scopes-p var scopes))
                    (not (var-in-scopes-p var2 scopes)))
                (equal (write-var-aux-okp var
                                          val
                                          (update-var-aux var2 val2 scopes))
                       (write-var-aux-okp var val scopes)))
       :induct t
       :enable (var-in-scopes-p
                write-var-aux-okp
                update-var-aux))))

  (defruled write-var-okp-of-update-static-var
    (implies (not (equal (ident-fix var)
                         (ident-fix var2)))
             (equal (write-var-okp var val (update-static-var var2 val2 compst))
                    (write-var-okp var val compst)))
    :enable (write-var-okp
             update-static-var
             top-frame))

  (defruled write-var-okp-of-update-object
    (equal (write-var-okp var val (update-object objdes obj compst))
           (write-var-okp var val compst))
    :enable (write-var-okp
             update-object
             top-frame))

  (defruled write-var-okp-when-valuep-of-read-var
    (implies (and (syntaxp (symbolp compst))
                  (> (compustate-frames-number compst) 0)
                  (equal old-val (read-var var compst))
                  (valuep old-val))
             (equal (write-var-okp var val compst)
                    (equal (type-of-value val)
                           (type-of-value old-val))))
    :enable (write-var-okp
             read-var
             read-auto-var
             read-static-var
             var-in-scopes-p-when-valuep-of-read-auto-var-aux
             not-var-in-scopes-p-when-not-read-auto-var-aux)
    :prep-lemmas
    ((defrule lemma
       (implies (and (equal old-val (read-auto-var-aux var scopes))
                     (valuep old-val))
                (equal (write-var-aux-okp var val scopes)
                       (equal (type-of-value val)
                              (type-of-value old-val))))
       :induct t
       :enable (write-var-aux-okp
                read-auto-var-aux))))

  (defruled write-var-to-update-var
    (implies (and (> (compustate-frames-number compst) 0)
                  (write-var-okp var val compst))
             (equal (write-var var val compst)
                    (update-var var val compst)))
    :enable (write-var-okp
             write-var
             write-auto-var
             write-static-var
             update-var
             errorp
             push-frame
             pop-frame
             top-frame)
    :prep-lemmas
    ((defrule lemma1
       (implies (write-var-aux-okp var val scopes)
                (equal (write-auto-var-aux var val scopes)
                       (update-var-aux var val scopes)))
       :induct (update-var-aux var val scopes)
       :enable (write-var-aux-okp
                write-auto-var-aux
                update-var-aux
                errorp
                endp))
     (defrule lemma2
       (implies (and (consp scopes)
                     (consp (write-auto-var-aux var val scopes)))
                (var-in-scopes-p var scopes))
       :induct t
       :enable (var-in-scopes-p write-auto-var-aux))))

  (defruled write-var-to-write-static-var
    (implies (not (var-autop var compst))
             (equal (write-var var val compst)
                    (write-static-var var val compst)))
    :enable write-var
    :prep-lemmas
    ((defrule not-write-auto-var-when-not-var-autop
       (implies (not (var-autop var compst))
                (not (write-auto-var var val compst)))
       :enable (write-auto-var var-autop)
       :prep-lemmas
       ((defrule not-write-auto-var-aux-when-not-var-in-scopes-p
          (implies (not (var-in-scopes-p var scopes))
                   (not (write-auto-var-aux var val scopes)))
          :induct t
          :enable (var-in-scopes-p write-auto-var-aux))))))

  (defval *atc-write-var-rules*
    '(write-var-to-update-var
      write-var-okp-of-enter-scope
      write-var-okp-of-add-var
      write-var-okp-of-update-var
      write-var-okp-of-update-static-var
      write-var-okp-of-update-object
      write-var-okp-when-valuep-of-read-var
      (:e typep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-read-var-rules
  :short "Rules about @(tsee read-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems below about @(tsee read-var) are a bit different
     because @(tsee read-var) does not return a state, but a value instead.")
   (xdoc::p
    "The first theorem turns @(tsee read-var) into @(tsee read-static-var)
     when we encounter @(tsee add-frame):
     since @(tsee add-frame) adds no variables in automatic storage,
     the variable must be in static storage.")
   (xdoc::p
    "The second theorem skips over @(tsee enter-scope).")
   (xdoc::p
    "The third theorem
     either returns the value of the encountered variable or skips over it,
     based on whether the names coincide or not.")
   (xdoc::p
    "The fourth theorem serves for variables read in loops
     that are declared outside the scope of the loop,
     i.e. that are represented as @(tsee update-var)s:
     if the two variables are the same, the value is returned;
     otherwise, we skip over the @(tsee update-var)
     in search for the variable.")
   (xdoc::p
    "The fifth and sixth theorem describe the effect of @(tsee read-var)
     when it encounters @(tsee update-static-var),
     which happens with C loops
     (not with C functions, because an @(tsee add-frame)
     would have been encountered first,
     turning @(tsee read-var) into @(tsee read-static-var)).
     If the variable names differ, we skip over the @(tsee update-static-var).
     If the variable names are the same,
     the two functions cancel and we return the value,
     but only if the variable is not found in automatic storage.")
   (xdoc::p
    "The seventh theorem serves to move past object updates.")
   (xdoc::p
    "The eight theorem turns @(tsee read-var) into @(tsee read-static-var)
     when the variable is not found in automatic storage.
     This is used in the proofs for loops,
     which do not use the rule @('read-var-of-add-frame')."))

  (defruled read-var-of-add-frame
    (equal (read-var var (add-frame fun compst))
           (read-static-var var compst))
    :enable (read-var
             read-auto-var
             read-auto-var-aux
             read-static-var
             add-frame
             push-frame
             top-frame))

  (defruled read-var-of-enter-scope
    (implies (> (compustate-frames-number compst) 0)
             (equal (read-var var (enter-scope compst))
                    (read-var var compst)))
    :enable (read-var
             read-auto-var
             read-auto-var-aux
             read-static-var
             enter-scope
             push-frame
             pop-frame
             top-frame
             compustate-frames-number
             len))

  (defruled read-var-of-add-var
    (equal (read-var var (add-var var2 val compst))
           (if (equal (ident-fix var)
                      (ident-fix var2))
               (remove-flexible-array-member val)
             (read-var var compst)))
    :enable (read-var
             read-auto-var
             read-auto-var-aux
             read-static-var
             add-var
             compustate-frames-number
             push-frame
             pop-frame
             top-frame
             len))

  (defruled read-var-of-update-var
    (equal (read-var var (update-var var2 val2 compst))
           (if (equal (ident-fix var)
                      (ident-fix var2))
               (remove-flexible-array-member val2)
             (read-var var compst)))
    :enable (read-var
             read-auto-var
             read-static-var
             update-var
             push-frame
             pop-frame
             top-frame
             compustate-frames-number
             var-in-scopes-p-when-read-auto-var-aux
             var-in-scopes-p
             len)
    :cases ((var-in-scopes-p var
                             (frame->scopes (car (compustate->frames compst)))))
    :prep-lemmas
    ((defrule lemma1
       (implies (and (var-in-scopes-p var scopes)
                     (var-in-scopes-p var2 scopes))
                (equal (read-auto-var-aux var (update-var-aux var2 val2 scopes))
                       (if (equal (ident-fix var)
                                  (ident-fix var2))
                           (remove-flexible-array-member val2)
                         (read-auto-var-aux var scopes))))
       :induct t
       :enable (var-in-scopes-p
                read-auto-var-aux
                update-var-aux))
     (defrule lemma2
       (implies (or (not (var-in-scopes-p var scopes))
                    (not (var-in-scopes-p var2 scopes)))
                (equal (read-auto-var-aux var (update-var-aux var2 val2 scopes))
                       (read-auto-var-aux var scopes)))
       :induct t
       :enable (var-in-scopes-p
                read-auto-var-aux
                update-var-aux))))

  (defruled read-var-of-update-static-var-different
    (implies (not (equal (ident-fix var)
                         (ident-fix var2)))
             (equal (read-var var (update-static-var var2 val compst))
                    (read-var var compst)))
    :enable (read-var
             read-static-var
             read-auto-var
             update-static-var
             top-frame))

  (defruled read-var-of-update-static-var-same
    (implies (not (var-autop var compst))
             (equal (read-var var (update-static-var var val compst))
                    (remove-flexible-array-member val)))
    :enable (read-var
             read-auto-var
             read-static-var
             var-autop
             update-static-var
             top-frame
             var-in-scopes-p-when-valuep-of-read-auto-var-aux))

  (defruled read-var-of-update-object
    (implies (> (compustate-frames-number compst) 0)
             (equal (read-var var (update-object objdes obj compst))
                    (read-var var compst)))
    :enable (read-var
             read-auto-var
             read-static-var
             update-object
             top-frame
             compustate-frames-number))

  (defruled read-var-to-read-static-var
    (implies (not (var-autop var compst))
             (equal (read-var var compst)
                    (read-static-var var compst)))
    :enable (var-autop
             read-var
             read-auto-var
             var-in-scopes-p-when-read-auto-var-aux))

  (defruled read-var-of-if*
    (equal (read-var var (if* a b c))
           (if* a (read-var var b) (read-var var c)))
    :enable if*)

  (defval *atc-read-var-rules*
    '(read-var-of-add-frame
      read-var-of-enter-scope
      read-var-of-add-var
      read-var-of-update-var
      read-var-of-update-static-var-different
      read-var-of-update-static-var-same
      read-var-of-update-object
      read-var-to-read-static-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-write-static-var-rules
  :short "Rules about @(tsee write-static-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are analogous to the ones for @(tsee write-var).
     We introduce a predicate saying when @(tsee write-static-var)
     is equivalent to @(tsee update-static-var),
     and rules to show that the predicate holds.
     The second-to-last rule states the equivalence.")
   (xdoc::p
    "The last rule is more about @('write-var-okp')
     than about @('write-static-var-okp'),
     but we put it here because
     the definition and rules for @('write-var-okp')
     come before the ones for @('write-static-var-okp')
     (we could reorder things at some point).
     This rule serves to reduce
     @('write-var-ok') to @('write-static-var-okp')
     when we have a frame with no variables."))

  (define write-static-var-okp ((var identp) (val valuep) (compst compustatep))
    :returns (yes/no booleanp)
    :parents nil
    (b* ((static (compustate->static compst))
         (pair (omap::assoc (ident-fix var) static)))
      (and (consp pair)
           (equal (type-of-value (cdr pair))
                  (type-of-value val))))
    :hooks (:fix))

  (defruled write-static-var-okp-of-add-frame
    (equal (write-static-var-okp var val (add-frame fun compst))
           (write-static-var-okp var val compst))
    :enable (write-static-var-okp
             add-frame
             push-frame))

  (defruled write-static-var-okp-of-enter-scope
    (equal (write-static-var-okp var val (enter-scope compst))
           (write-static-var-okp var val compst))
    :enable (write-static-var-okp
             enter-scope
             push-frame
             pop-frame))

  (defruled write-static-var-okp-of-add-var
    (equal (write-static-var-okp var val (add-var var2 val2 compst))
           (write-static-var-okp var val compst))
    :enable (write-static-var-okp
             add-var
             push-frame
             pop-frame))

  (defruled write-static-var-okp-of-update-var
    (implies (not (equal (ident-fix var)
                         (ident-fix var2)))
             (equal (write-static-var-okp var val (update-var var2 val2 compst))
                    (write-static-var-okp var val compst)))
    :enable (write-static-var-okp
             update-var
             push-frame
             pop-frame))

  (defruled write-static-var-okp-of-update-static-var
    (equal (write-static-var-okp var val (update-static-var var2 val2 compst))
           (if (equal (ident-fix var)
                      (ident-fix var2))
               (equal (type-of-value val2)
                      (type-of-value val))
             (write-static-var-okp var val compst)))
    :enable (write-static-var-okp
             update-static-var))

  (defruled write-static-var-okp-of-update-object
    (equal (write-static-var-okp var val (update-object objdes obj compst))
           (write-static-var-okp var val compst))
    :enable (write-static-var-okp
             update-object))

  (defruled write-static-var-okp-when-valuep-of-read-static-var
    (implies (and (syntaxp (symbolp compst))
                  (equal old-val (read-static-var var compst))
                  (valuep old-val))
             (equal (write-static-var-okp var val compst)
                    (equal (type-of-value val)
                           (type-of-value old-val))))
    :enable (write-static-var-okp
             read-static-var))

  (defruled write-static-var-to-update-static-var
    (implies (write-static-var-okp var val compst)
             (equal (write-static-var var val compst)
                    (update-static-var var val compst)))
    :enable (write-static-var
             write-static-var-okp
             update-static-var))

  (defruled write-var-okp-of-add-frame
    (equal (write-var-okp var val (add-frame fun compst))
           (write-static-var-okp var val (add-frame fun compst)))
    :enable (write-var-okp
             write-static-var-okp
             add-frame
             var-in-scopes-p))

  (defval *atc-write-static-var-rules*
    '(write-static-var-okp-of-add-frame
      write-static-var-okp-of-enter-scope
      write-static-var-okp-of-add-var
      write-static-var-okp-of-update-var
      write-static-var-okp-of-update-static-var
      write-static-var-okp-of-update-object
      write-static-var-okp-when-valuep-of-read-static-var
      write-static-var-to-update-static-var
      write-var-okp-of-add-frame)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-read-static-var-rules
  :short "Rules about @(tsee read-static-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are somewhat similar to the ones about @(tsee read-var).
     We go through the frame, the scopes, and the added (automatic) variables.
     We also go through the updated variables,
     provided that the names are distinct;
     this will have to be refined soon.
     We also go through object updates,
     which currently are only for objects in the heap
     (see @(tsee update-object))."))

  (defruled read-static-var-of-add-frame
    (equal (read-static-var var (add-frame fun compst))
           (read-static-var var compst))
    :enable (read-static-var
             add-frame
             push-frame)
    :disable omap::assoc-when-assoc-tail)

  (defruled read-static-var-of-enter-scope
    (equal (read-static-var var (enter-scope compst))
           (read-static-var var compst))
    :enable (read-static-var
             enter-scope
             push-frame
             pop-frame)
    :disable omap::assoc-when-assoc-tail)

  (defruled read-static-var-of-add-var
    (equal (read-static-var var (add-var var2 val compst))
           (read-static-var var compst))
    :enable (read-static-var
             add-var
             push-frame
             pop-frame)
    :disable omap::assoc-when-assoc-tail)

  (defruled read-static-var-of-update-var
    (implies (not (equal (ident-fix var)
                         (ident-fix var2)))
             (equal (read-static-var var (update-var var2 val compst))
                    (read-static-var var compst)))
    :enable (read-static-var
             update-var
             push-frame
             pop-frame)
    :disable omap::assoc-when-assoc-tail)

  (defruled read-static-var-of-update-static-var
    (equal (read-static-var var (update-static-var var2 val compst))
           (if (equal (ident-fix var)
                      (ident-fix var2))
               (remove-flexible-array-member val)
             (read-static-var var compst)))
    :enable (read-static-var update-static-var))

  (defruled read-static-var-of-update-object
    (equal (read-static-var var (update-object objdes val compst))
           (read-static-var var compst))
    :enable (read-static-var
             update-object)
    :disable omap::assoc-when-assoc-tail)

  (defval *atc-read-static-var-rules*
    '(read-static-var-of-add-frame
      read-static-var-of-enter-scope
      read-static-var-of-add-var
      read-static-var-of-update-var
      read-static-var-of-update-static-var
      read-static-var-of-update-object)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-update-var-rules
  :short "Rules about @(tsee update-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about @(tsee update-var) push them into the states,
     sometimes combining them into @(tsee add-var)s.")
   (xdoc::p
    "The first theorem turns @(tsee update-var) into @(tsee update-static-var)
     when reaching @(tsee add-frame):
     at that point, there are no more accessible variables (by name)
     in automatic storage.")
   (xdoc::p
    "The second theorem pushes @(tsee update-var) into @(tsee enter-scope).")
   (xdoc::p
    "The third theorem combines @(tsee update-var) with @(tsee add-var)
     if the variable is the same, otherwise it pushes @(tsee update-var) in.")
   (xdoc::p
    "The fourth theorem overwrites an @(tsee update-var)
     with an @(tsee update-var) for the same variable.")
   (xdoc::p
    "The fifth theorem is used to arrange a nest of @(tsee update-var)s
     in alphabetical order of the variable names:
     it swaps two @(tsee update-var)s when the outer one
     has an larger variable than the inner one.
     Note that we need to disable loop stoppers for this rule,
     otherwise ACL2 may not apply it based on the written value terms,
     which are irrelevant to this normalization
     based on alphabetical order.
     Note the @(tsee syntaxp) hypotheses
     that require the identifiers (i.e. variable names)
     to have the form described in @(see atc-identifier-rules).")
   (xdoc::p
    "Finally, the sixth theorem serves to simplify the case in which
     a variable is written with its current value;
     this case may occur when proving the base case of a loop.
     This theorem is phrased perhaps more generally than expected,
     with two different computation state variables,
     instead of the simpler form in @('update-var-of-read-var-same-lemma'):
     the reason is that sometimes during symbolic execution
     a pattern arises of the form
     @('(update-var var (read-var var compst) <other-compst>)'),
     where @('<other-compst>') is a term
     that is not just the @('compst') variable:
     the rule binds @('compst1') to that.
     This theorem has a @(tsee syntaxp) hypothesis
     requiring the computation state argument of @(tsee read-var)
     to be a variable;
     this may not be actually necessary,
     but for now we include it just to make sure."))

  (defruled update-var-of-add-frame
    (equal (update-var var val (add-frame fun compst))
           (add-frame fun (update-static-var var val compst)))
    :enable (update-var
             update-static-var
             add-frame
             push-frame
             pop-frame
             top-frame
             var-in-scopes-p))

  (defruled update-var-of-enter-scope
    (equal (update-var var val (enter-scope compst))
           (enter-scope (update-var var val compst)))
    :enable (update-var
             update-var-aux
             enter-scope
             push-frame
             pop-frame
             top-frame
             var-in-scopes-p))

  (defruled update-var-of-add-var
    (equal (update-var var val (add-var var2 val2 compst))
           (if (equal (ident-fix var)
                      (ident-fix var2))
               (add-var var2 val compst)
             (add-var var2 val2 (update-var var val compst))))
    :enable (update-var
             update-var-aux
             add-var
             push-frame
             pop-frame
             top-frame
             var-in-scopes-p))

  (defruled update-var-of-update-var-same
    (equal (update-var var val (update-var var val2 compst))
           (update-var var val compst))
    :enable (update-var
             update-var-aux
             push-frame
             pop-frame
             top-frame
             var-in-scopes-p-of-update-var-aux)
    :prep-lemmas
    ((defrule lemma
       (equal (update-var-aux var val (update-var-aux var val2 scopes))
              (update-var-aux var val scopes))
       :induct t
       :enable update-var-aux)))

  (defruled update-var-of-update-var-less
    (implies (and (syntaxp (and (consp var2)
                                (eq (car var2) 'ident)
                                (quotep (cadr var2))))
                  (syntaxp (and (consp var)
                                (eq (car var) 'ident)
                                (quotep (cadr var))))
                  (<< (ident-fix var2)
                      (ident-fix var))
                  (> (compustate-frames-number compst) 0))
             (equal (update-var var val (update-var var2 val2 compst))
                    (update-var var2 val2 (update-var var val compst))))
    :rule-classes ((:rewrite :loop-stopper nil))
    :enable (update-var
             <<
             push-frame
             pop-frame
             top-frame
             var-in-scopes-p-of-update-var-aux)
    :prep-lemmas
    ((defrule lemma
       (implies
        (not (equal (ident-fix var)
                    (ident-fix var2)))
        (equal (update-var-aux var val (update-var-aux var2 val2 scopes))
               (update-var-aux var2 val2 (update-var-aux var val scopes))))
       :induct t
       :enable update-var-aux)))

  (defruled update-var-of-read-var-same
    (implies (and (syntaxp (symbolp compst))
                  (compustatep compst1)
                  (> (compustate-frames-number compst1) 0)
                  (valuep (read-var var compst))
                  (not (flexible-array-member-p (read-var var compst)))
                  (equal (read-var var compst)
                         (read-var var compst1)))
             (equal (update-var var (read-var var compst) compst1)
                    compst1))
    :use (:instance update-var-of-read-var-same-lemma (compst compst1))
    :prep-lemmas
    ((defruled update-var-aux-of-read-auto-var-aux-same
       (implies (and (valuep (read-auto-var-aux var scopes))
                     (not (flexible-array-member-p
                           (read-auto-var-aux var scopes))))
                (equal (update-var-aux var (read-auto-var-aux var scopes) scopes)
                       (scope-list-fix scopes)))
       :induct t
       :enable (read-auto-var-aux
                update-var-aux
                len))
     (defruled update-var-of-read-var-same-lemma
       (implies (and (compustatep compst)
                     (> (compustate-frames-number compst) 0)
                     (valuep (read-var var compst))
                     (not (flexible-array-member-p (read-var var compst))))
                (equal (update-var var (read-var var compst) compst)
                       compst))
       :enable (read-var
                read-auto-var
                read-static-var
                update-var
                update-var-aux-of-read-auto-var-aux-same
                top-frame
                push-frame
                pop-frame
                compustate-frames-number
                var-in-scopes-p-when-valuep-of-read-auto-var-aux
                not-var-in-scopes-p-when-not-read-auto-var-aux
                len))))

  (defval *atc-update-var-rules*
    '(update-var-of-add-frame
      update-var-of-enter-scope
      update-var-of-add-var
      update-var-of-update-var-same
      update-var-of-update-var-less
      update-var-of-read-var-same)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-write-object-rules
  :short "Rules about @(tsee write-object)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem about @(tsee write-object) turns it into @(tsee update-object),
     similarly to how @(tsee write-var) is turned into @(tsee update-var).
     The condition for the replacement is captured by @('write-object-okp'),
     for which we supply rules to go through all the computation state layers.
     When the computation state (meta) variable is reached,
     it must be the case that there are hypotheses available
     saying that reading the object
     yields a value of appropriate type and length.
     The rule is used as last resort,
     only if the computation state is an ACL2 variable
     (as enforced by the @(tsee syntaxp) hypothesis).")
   (xdoc::p
    "For now we only support top-level object designators,
     but we plan to extend things to other object designators.")
   (xdoc::p
    "Since @(tsee update-object) takes the base address,
     the rules @('write-object-okp-of-update-object-same')
     and @('write-object-okp-when-valuep-of-read-object')
     need the hypothesis that the object designator is a top-level one.")
   (xdoc::p
    "We include the rule for commutativity of @(tsee object-disjointp),
     so it does not matter the order of the disjoint objects
     in the hypotheses of the rules vs. the available hypothesis
     during the symbolic execution
     (i.e. commutativity normalizes them, via its loop stopper)."))

  (define write-object-okp ((objdes objdesignp)
                            (val valuep)
                            (compst compustatep))
    :returns (yes/no booleanp)
    :parents nil
    (b* (((unless (objdesign-case objdes :alloc)) nil)
         (addr (objdesign-alloc->get objdes))
         (heap (compustate->heap compst))
         (addr+obj (omap::assoc addr heap))
         ((unless (consp addr+obj)) nil)
         (obj (cdr addr+obj))
         ((unless (equal (type-of-value val)
                         (type-of-value obj)))
          nil))
      t)
    :hooks (:fix))

  (defruled write-object-okp-of-add-frame
    (equal (write-object-okp objdes val (add-frame fun compst))
           (write-object-okp objdes val compst))
    :enable (write-object-okp
             add-frame
             push-frame))

  (defruled write-object-okp-of-enter-scope
    (equal (write-object-okp objdes val (enter-scope compst))
           (write-object-okp objdes val compst))
    :enable (write-object-okp
             enter-scope
             push-frame
             pop-frame))

  (defruled write-object-okp-of-add-var
    (equal (write-object-okp objdes val (add-var var val2 compst))
           (write-object-okp objdes val compst))
    :enable (write-object-okp
             add-var
             push-frame
             pop-frame))

  (defruled write-object-okp-of-update-var
    (equal (write-object-okp objdes val (update-var var val2 compst))
           (write-object-okp objdes val compst))
    :enable (write-object-okp
             update-var
             push-frame
             pop-frame))

  (defruled write-object-okp-of-update-object-same
    (implies
     (equal (objdesign-kind objdes) :alloc)
     (equal (write-object-okp objdes val (update-object objdes val2 compst))
            (equal (type-of-value val)
                   (type-of-value val2))))
    :enable (write-object-okp
             update-object
             objdesign->base-address))

  (defruled write-object-okp-of-update-object-disjoint
    (implies
     (object-disjointp objdes objdes2)
     (equal (write-object-okp objdes val (update-object objdes2 val2 compst))
            (write-object-okp objdes val compst)))
    :enable (write-object-okp
             update-object
             object-disjointp
             objdesign->base-address))

  (defruled write-object-okp-when-valuep-of-read-object
    (implies (and (syntaxp (symbolp compst))
                  (equal (objdesign-kind objdes) :alloc)
                  (equal old-val (read-object objdes compst))
                  (valuep old-val))
             (equal (write-object-okp objdes val compst)
                    (equal (type-of-value val)
                           (type-of-value old-val))))
    :enable (write-object-okp
             read-object))

  (defruled write-object-okp-of-if*-val
    (implies (and (write-object-okp objdes b compst)
                  (write-object-okp objdes c compst))
             (write-object-okp objdes (if* a b c) compst))
    :enable if*)

  (defruled write-object-okp-when-valuep-of-read-object-no-syntaxp
    (implies (and (equal (objdesign-kind objdes) :alloc)
                  (equal old-val (read-object objdes compst))
                  (valuep old-val))
             (equal (write-object-okp objdes val compst)
                    (equal (type-of-value val)
                           (type-of-value old-val))))
    :enable (write-object-okp-when-valuep-of-read-object))

  (defruled write-object-to-update-object
    (implies (write-object-okp objdes val compst)
             (equal (write-object objdes val compst)
                    (update-object objdes val compst)))
    :enable (write-object
             write-object-okp
             update-object
             objdesign->base-address))

  (defruled write-object-of-objdesign-static
    (equal (write-object (objdesign-static var) val compst)
           (write-static-var var val compst))
    :enable (write-object
             write-static-var))

  (defval *atc-write-object-rules*
    '(write-object-to-update-object
      write-object-okp-of-add-frame
      write-object-okp-of-enter-scope
      write-object-okp-of-add-var
      write-object-okp-of-update-var
      write-object-okp-of-update-object-same
      write-object-okp-of-update-object-disjoint
      write-object-okp-when-valuep-of-read-object
      write-object-of-objdesign-static
      object-disjointp-commutative
      valuep-when-uchar-arrayp
      valuep-when-schar-arrayp
      valuep-when-ushort-arrayp
      valuep-when-sshort-arrayp
      valuep-when-uint-arrayp
      valuep-when-sint-arrayp
      valuep-when-ulong-arrayp
      valuep-when-slong-arrayp
      valuep-when-ullong-arrayp
      valuep-when-sllong-arrayp
      value-kind-when-uchar-arrayp
      value-kind-when-schar-arrayp
      value-kind-when-ushort-arrayp
      value-kind-when-sshort-arrayp
      value-kind-when-uint-arrayp
      value-kind-when-sint-arrayp
      value-kind-when-ulong-arrayp
      value-kind-when-slong-arrayp
      value-kind-when-ullong-arrayp
      value-kind-when-sllong-arrayp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-read-object-rules
  :short "Rules about @(tsee read-object)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about @(tsee read-object)
     skip over all the functions that represent the computation states,
     except for possibly @(tsee update-object):
     this is similar to the interaction
     between @(tsee read-var) and @(tsee update-var).")
   (xdoc::p
    "The last theorem is a bit different.
     It lets us replace @(tsee read-object)
     with the more specific @(tsee read-static-var)
     when the object designator is for a static variable.")
   (xdoc::p
    "We include the rule for commutativity of @(tsee object-disjointp),
     so it does not matter the order of the disjoint objects
     in the hypotheses of the rules vs. the available hypothesis
     during the symbolic execution
     (i.e. commutativity normalizes them, via its loop stopper)."))

  (defruled read-object-of-add-frame
    (implies (or (equal (objdesign-kind objdes) :alloc)
                 (equal (objdesign-kind objdes) :static))
             (equal (read-object objdes (add-frame fun compst))
                    (read-object objdes compst)))
    :enable (add-frame
             push-frame
             read-object))

  (defruled read-object-of-enter-scope
    (implies (equal (objdesign-kind objdes) :alloc)
             (equal (read-object objdes (enter-scope compst))
                    (read-object objdes compst)))
    :enable (enter-scope
             push-frame
             pop-frame
             read-object))

  (defruled read-object-of-add-var
    (implies (equal (objdesign-kind objdes) :alloc)
             (equal (read-object objdes (add-var var val compst))
                    (read-object objdes compst)))
    :enable (add-var
             push-frame
             pop-frame
             read-object))

  (defruled read-object-of-update-var
    (implies (equal (objdesign-kind objdes) :alloc)
             (equal (read-object objdes (update-var var val compst))
                    (read-object objdes compst)))
    :enable (update-var
             push-frame
             pop-frame
             read-object))

  (defruled read-object-of-update-object-same
    (implies (equal (objdesign-kind objdes) :alloc)
             (equal (read-object objdes (update-object objdes val compst))
                    (value-fix val)))
    :enable (read-object
             update-object
             objdesign->base-address))

  (defruled read-object-of-update-object-disjoint
    (implies (object-disjointp objdes objdes2)
             (equal (read-object objdes (update-object objdes2 val compst))
                    (read-object objdes compst)))
    :enable (read-object
             update-object
             object-disjointp
             objdesign->base-address))

  (defruled read-object-of-objdesign-static
    (equal (read-object (objdesign-static var) compst)
           (read-static-var var compst))
    :enable (read-object
             read-static-var))

  (defruled read-object-of-value-pointer->designator-of-if*
    (equal (read-object (value-pointer->designator ptr) (if* a b c))
           (if* a
                (read-object (value-pointer->designator ptr) b)
                (read-object (value-pointer->designator ptr) c)))
    :enable if*)

  (defval *atc-read-object-rules*
    '(read-object-of-add-frame
      read-object-of-enter-scope
      read-object-of-add-var
      read-object-of-update-var
      read-object-of-update-object-same
      read-object-of-update-object-disjoint
      read-object-of-objdesign-static
      pointer-valid->get-of-pointer-valid
      object-disjointp-commutative)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-update-object-rules
  :short "Rules about @(tsee update-object)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We have rules to unconditionally push @(tsee update-object)
     through all the layers except @(tsee update-object).")
   (xdoc::p
    "When @(tsee update-object) is applied to @(tsee update-object),
     we have rules similar to the ones for @(tsee update-var).
     If the two object designators are the same, we overwrite the object.
     When the object designators differ,
     we swap the @(tsee update-var)s
     if the right pointer is smaller than the left one,
     where smaller is a syntactic check:
     when the two pointer arguments are symbols
     (which happens in the proofs of C functions),
     we compare the symbols;
     when the two pointer arguments are @(tsee read-var) calls
     (which happens in the proofs of C loops),
     we compare the identifier terms,
     which boils down to comparing the variable names.
     Either way, we normalize the nests of @(tsee update-object) calls
     by ordering them according to the pointer.
     We are talking about pointers here, and not object designators,
     because, as mentioned in @(see atc-symbolic-computation-states),
     during symbolic execution the object designators in question
     have the form @('(value-pointer->designator <pointer>)'),
     which is what the @(tsee syntaxp) hypotheses below are based on.")
   (xdoc::p
    "We also include a rule saying that
     updating an object with the existing one is a no-op.
     This is similar to @('update-var-of-read-var').
     In particular, it uses two possibly different computation states,
     for the reasons explained for @('update-var-of-read-var').")
   (xdoc::p
    "We include the rule for commutativity of @(tsee object-disjointp),
     so it does not matter the order of the disjoint objects
     in the hypotheses of the rules vs. the available hypothesis
     during the symbolic execution
     (i.e. commutativity normalizes them, via its loop stopper)."))

  (defruled update-object-of-add-frame
    (equal (update-object objdes obj (add-frame fun compst))
           (add-frame fun (update-object objdes obj compst)))
    :enable (update-object
             add-frame
             push-frame))

  (defruled update-object-of-enter-scope
    (equal (update-object objdes obj (enter-scope compst))
           (enter-scope (update-object objdes obj compst)))
    :enable (update-object
             enter-scope
             push-frame
             pop-frame
             top-frame))

  (defruled update-object-of-add-var
    (equal (update-object objdes obj (add-var var val compst))
           (add-var var val (update-object objdes obj compst)))
    :enable (update-object
             add-var
             push-frame
             pop-frame
             top-frame))

  (defruled update-object-of-update-var
    (equal (update-object objdes obj (update-var var val compst))
           (update-var var val (update-object objdes obj compst)))
    :enable (update-object
             update-var
             push-frame
             pop-frame
             top-frame))

  (defruled update-object-of-update-static-var
    (equal (update-object objdes obj (update-static-var var val compst))
           (update-static-var var val (update-object objdes obj compst)))
    :enable (update-object update-static-var))

  (defruled update-object-of-update-object-same
    (equal (update-object objdes obj (update-object objdes obj2 compst))
           (update-object objdes obj compst))
    :enable update-object)

  (defruled update-object-of-update-object-less-symbol
    (implies
     (and (syntaxp (and (ffn-symb-p objdes 'value-pointer->designator)
                        (ffn-symb-p objdes2 'value-pointer->designator)
                        (b* ((ptr (fargn objdes 1))
                             (ptr2 (fargn objdes2 1)))
                          (and (symbolp ptr)
                               (symbolp ptr2)
                               (symbol< ptr2 ptr)))))
          (object-disjointp objdes objdes2))
     (equal (update-object objdes obj (update-object objdes2 obj2 compst))
            (update-object objdes2 obj2 (update-object objdes obj compst))))
    :rule-classes ((:rewrite :loop-stopper nil))
    :enable (update-object
             object-disjointp
             objdesign->base-address))

  (defruled update-object-of-update-object-less-ident
    (implies
     (and (syntaxp (and (ffn-symb-p objdes 'value-pointer->designator)
                        (ffn-symb-p objdes2 'value-pointer->designator)
                        (b* ((ptr (fargn objdes 1))
                             (ptr2 (fargn objdes2 1)))
                          (and (ffn-symb-p ptr 'read-var)
                               (ffn-symb-p ptr2 'read-var)
                               (<< (fargn ptr2 1)
                                   (fargn ptr 1))))))
          (object-disjointp objdes objdes2))
     (equal (update-object objdes obj (update-object objdes2 obj2 compst))
            (update-object objdes2 obj2 (update-object objdes obj compst))))
    :rule-classes ((:rewrite :loop-stopper nil))
    :enable (update-object
             object-disjointp
             objdesign->base-address))

  (defruled update-object-of-read-object-same
    (implies (and (syntaxp (symbolp compst))
                  (compustatep compst1)
                  (equal (objdesign-kind objdes) :alloc)
                  (valuep (read-object objdes compst))
                  (equal (read-object objdes compst)
                         (read-object objdes compst1)))
             (equal (update-object objdes (read-object objdes compst) compst1)
                    compst1))
    :enable (read-object
             update-object
             objdesign->base-address))

  (defruled update-object-of-if*-val
    (equal (update-object objdes (if* a b c) compst)
           (if* a
                (update-object objdes b compst)
                (update-object objdes c compst)))
    :enable if*)

  (defval *atc-update-object-rules*
    '(update-object-of-add-frame
      update-object-of-enter-scope
      update-object-of-add-var
      update-object-of-update-var
      update-object-of-update-static-var
      update-object-of-update-object-same
      update-object-of-update-object-less-symbol
      update-object-of-update-object-less-ident
      update-object-of-read-object-same
      object-disjointp-commutative)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-update-static-var-rules
  :short "Rules about @(tsee update-static-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are similar to the ones for
     @(tsee update-var) and @(tsee update-object)."))

  (defruled update-static-var-of-add-frame
    (equal (update-static-var var val (add-frame fun compst))
           (add-frame fun (update-static-var var val compst)))
    :enable (update-static-var
             add-frame
             push-frame))

  (defruled update-static-var-of-enter-scope
    (equal (update-static-var var val (enter-scope compst))
           (enter-scope (update-static-var var val compst)))
    :enable (update-static-var
             enter-scope
             push-frame
             pop-frame
             top-frame))

  (defruled update-static-var-of-add-var
    (equal (update-static-var var val (add-var var2 val2 compst))
           (add-var var2 val2 (update-static-var var val compst)))
    :enable (update-static-var
             add-var
             push-frame
             pop-frame
             top-frame))

  (defruled update-static-var-of-update-var
    (implies (not (equal (ident-fix var)
                         (ident-fix var2)))
             (equal (update-static-var var val (update-var var2 val2 compst))
                    (update-var var2 val2 (update-static-var var val compst))))
    :enable (update-static-var
             update-var
             push-frame
             pop-frame
             top-frame))

  (defruled update-static-var-of-update-static-var-same
    (equal (update-static-var var val (update-static-var var val2 compst))
           (update-static-var var val compst))
    :enable update-static-var)

  (defruled update-static-var-of-update-static-var-less
    (implies (and (syntaxp (and (consp var2)
                                (eq (car var2) 'ident)
                                (quotep (cadr var2))))
                  (syntaxp (and (consp var)
                                (eq (car var) 'ident)
                                (quotep (cadr var))))
                  (<< (ident-fix var2)
                      (ident-fix var)))
             (equal
              (update-static-var var val (update-static-var var2 val2 compst))
              (update-static-var var2 val2 (update-static-var var val compst))))
    :rule-classes ((:rewrite :loop-stopper nil))
    :enable (update-static-var
             <<))

  (defruled update-static-var-of-read-static-var-same
    (implies (and (syntaxp (symbolp compst))
                  (compustatep compst1)
                  (valuep (read-static-var var compst))
                  (not (flexible-array-member-p (read-static-var var compst)))
                  (equal (read-static-var var compst)
                         (read-static-var var compst1)))
             (equal (update-static-var var (read-static-var var compst) compst1)
                    compst1))
    :enable (update-static-var
             read-static-var
             identity)
    :disable omap::assoc-when-assoc-tail
    :use (:instance update-static-var-of-read-static-var-same-lemma
                    (compst compst1))
    :prep-lemmas
    ((defruled update-static-var-of-read-static-var-same-lemma
       (implies (and (compustatep compst)
                     (valuep (read-static-var var compst))
                     (not (flexible-array-member-p
                           (read-static-var var compst))))
                (equal (update-static-var var
                                          (read-static-var var compst)
                                          compst)
                       compst))
       :enable (read-static-var
                update-static-var
                top-frame
                push-frame
                pop-frame))))

  (defruled update-static-var-of-if*-val
    (equal (update-static-var var (if* a b c) compst)
           (if* a
                (update-static-var var b compst)
                (update-static-var var c compst)))
    :enable if*)

  (defval *atc-update-static-var-rules*
    '(update-static-var-of-add-frame
      update-static-var-of-enter-scope
      update-static-var-of-add-var
      update-static-var-of-update-var
      update-static-var-of-update-static-var-same
      update-static-var-of-update-static-var-less
      update-static-var-of-read-static-var-same)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-var-autop-rules
  :short "Rules about @(tsee var-autop)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These serve to discharge the @(tsee var-autop) hypothesis
     in "
    (xdoc::seetopic "atc-read-var-rules"
                    "rule @('read-var-of-update-static-var-same')")
    "."))

  (defruled var-autop-of-add-frame
    (not (var-autop var (add-frame fun compst)))
    :enable (var-autop add-frame var-in-scopes-p))

  (defruled var-autop-of-enter-scope
    (equal (var-autop var (enter-scope compst))
           (var-autop var compst))
    :enable (var-autop enter-scope var-in-scopes-p))

  (defruled var-autop-of-add-var
    (equal (var-autop var (add-var var2 val compst))
           (or (equal (ident-fix var)
                      (ident-fix var2))
               (var-autop var compst)))
    :enable (var-autop add-var var-in-scopes-p))

  (defruled var-autop-of-update-var
    (equal (var-autop var (update-var var2 val compst))
           (var-autop var compst))
    :enable (var-autop
             update-var
             top-frame
             push-frame)
    :prep-lemmas
    ((defrule lemma
       (equal (var-in-scopes-p var (update-var-aux var2 val scopes))
              (var-in-scopes-p var scopes))
       :induct t
       :enable (var-in-scopes-p update-var-aux))))

  (defruled var-autop-of-update-static-var
    (equal (var-autop var (update-static-var var2 val compst))
           (var-autop var compst))
    :enable (var-autop update-static-var top-frame))

  (defruled var-autop-of-update-object
    (equal (var-autop var (update-object objdes obj compst))
           (var-autop var compst))
    :enable (var-autop update-object top-frame))

  (defval *atc-var-autop-rules*
    '(var-autop-of-add-frame
      var-autop-of-enter-scope
      var-autop-of-add-var
      var-autop-of-update-var
      var-autop-of-update-static-var
      var-autop-of-update-object)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-compustate-frames-number-rules
  :short "Rules about @(tsee compustate-frames-number)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first four theorems about @(tsee compustate-frames-number)
     serve to discharge the hypotheses about it being not 0
     in some of the other theorems.
     These are all immediately discharged,
     because the functions used to represent the symbolic execution states
     satisfy that condition
     (by design, for @(tsee add-var) and @(tsee update-var)).")
   (xdoc::p
    "The last theorems serve to skip over @(tsee update-object) calls."))

  (defruled compustate-frames-number-of-add-frame-not-zero
    (> (compustate-frames-number (add-frame fun compst)) 0)
    :enable add-frame)

  (defruled compustate-frames-number-of-enter-scope-not-zero
    (> (compustate-frames-number (enter-scope compst)) 0)
    :enable enter-scope)

  (defruled compustate-frames-number-of-add-var-not-zero
    (> (compustate-frames-number (add-var var val compst)) 0)
    :enable add-var)

  (defruled compustate-frames-number-of-update-var
    (equal (compustate-frames-number (update-var var val compst))
           (compustate-frames-number compst))
    :enable (update-var
             compustate-frames-number
             push-frame
             pop-frame
             top-frame
             var-in-scopes-p
             len))

  (defruled compustate-frames-number-of-update-static-var
    (equal (compustate-frames-number (update-static-var var val compst))
           (compustate-frames-number compst))
    :enable (update-static-var
             compustate-frames-number
             push-frame
             pop-frame
             top-frame
             var-in-scopes-p))

  (defruled compustate-frames-number-of-update-object
    (equal (compustate-frames-number (update-object objdes obj compst))
           (compustate-frames-number compst))
    :enable (update-object
             compustate-frames-number))

  (defval *atc-compustate-frames-number-rules*
    '(compustate-frames-number-of-add-frame-not-zero
      compustate-frames-number-of-enter-scope-not-zero
      compustate-frames-number-of-add-var-not-zero
      compustate-frames-number-of-update-var
      compustate-frames-number-of-update-static-var
      compustate-frames-number-of-update-object)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-symbolic-computation-state-rules*
  :short "List of rules for symbolic computation states."
  (append *atc-push-frame-rules*
          *atc-pop-frame-rules*
          *atc-exit-scope-rules*
          *atc-create-var-rules*
          *atc-write-var-rules*
          *atc-read-var-rules*
          *atc-write-static-var-rules*
          *atc-read-static-var-rules*
          *atc-update-var-rules*
          *atc-write-object-rules*
          *atc-read-object-rules*
          *atc-update-object-rules*
          *atc-update-static-var-rules*
          *atc-var-autop-rules*
          *atc-compustate-frames-number-rules*))
