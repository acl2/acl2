; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "computation-states")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-symbolic-computation-states
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
     namely @(tsee push-frame), @tsee enter-scope), @(tsee create-var), etc.,
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
     a sequence of applications of the three functions below
     to an initial symbolic computation state @('<compst>'):")
   (xdoc::codeblock
    "(add-var ... (enter-scope (add-var ... (add-frame ... <compst>)...)")
   (xdoc::p
    "The reason for introducing a new function @(tsee add-var),
     instead of just using @(tsee create-var) (leaving it disabled),
     is that @(tsee add-var) unconditionally satisfies certain properties
     that @(tsee create-var) satisfies when it does not return an error:
     @(tsee add-var) unconditionally returns a computation state,
     and always ensured that the added variable is in the computation state.
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
     so in this case the symbolic computtion state looks like")
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
     arising during symbolic execution match those hypotheses.
     A loop may write to those variables:
     in this case, after replacing @(tsee write-var) with @(tsee update-var)
     right away as explained earlier,
     the @(tsee update-var) will go through
     all the @(tsee add-var) and @(tsee enter-scope) layers shown above,
     and reach @('<compst>'), where it is not further reducible.
     This may happen for several different variables,
     leading to states of the form")
   (xdoc::codeblock
    "(... (enter-scope (add-var (update-var ... (update-var ... <compst>)...)")
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
     whose arrays may be updated during the symbolic execution.
     We represent these updates via the function @(tsee update-array),
     which is similar to @(tsee write-array)
     but always satisfies additional properties:
     the relation between @(tsee update-array) and @(tsee write-array)
     is similar to the one between @(tsee update-var) and @(tsee write-var)
     and to the one between @(tsee add-var) and @(tsee create-var),
     explained above.")
   (xdoc::p
    "Arrays may be updated by C functions and C loops,
     so they need to be incorporated in both of
     the symbolic computation state representations described above.
     We push the @(tsee update-array) past all the other functions,
     leading to states of the form")
   (xdoc::codeblock
    "(... (add-frame (update-array ... (update-array ... <compst>)...)")
   (xdoc::p
    "for C functions and of the form")
   (xdoc::codeblock
    "(... (enter-scope (add-var ... (update-array ... <compst>)...)")
   (xdoc::p
    "for C loops.
     We order the @(tsee update-array) calls
     according to their first argument (i.e. the pointer).
     Note that for a C functions this first argument is an ACL2 variable,
     while for a C loop it is a @('(read-var <identifier> ...)').
     These two kinds of first arguments never appear together.
     We prove rules that order according to the symbols,
     which apply to proofs of theorems of C functions,
     and we prove rules that order according to the identifiers,
     which apply to proofs of theorems of C loops.")
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
    "This is like @(tsee create-var), but it does not return an error:
     it always adds the variable to the current scope.
     If the variable does not already exist in the current scope,
     this is equivalent to @(tsee create-var), as proved later."))
  (b* ((frame (top-frame compst))
       (scopes (frame->scopes frame))
       (scope (car scopes))
       (new-scope (omap::update (ident-fix var) (value-fix val) scope))
       (new-scopes (cons new-scope (cdr scopes)))
       (new-frame (change-frame frame :scopes new-scopes))
       (new-compst (push-frame new-frame (pop-frame compst))))
    new-compst)
  :hooks (:fix))

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
     First, its guard requires at least one frame,
     so we always get a frame via @(tsee top-frame).
     (Actually, given that this function is only used for symbolic execution,
     it does not need to be guard-verified;
     the same applies to @(tsee add-frame) and @(tsee add-var),
     but for now we keep them guard-verified.)
     Second, as we go through the scopes,
     when we reach the outermost scope without finding the variable,
     we add it to that scope anyhow:
     this ensures that the variable is always there,
     which simplifies other rules;
     we check that the variable is actually there
     when we turn @(tsee write-var) into @(tsee update-var),
     in another rule.
     Third, we do not check the type of the new value
     against the type of the old value if the variable exists,
     and instead we unconditionally overwrite the old value with the new value:
     this ensures that the new value is always there,
     which simplified other rules;
     we check that the types match
     when we turn @(tsee write-var) into @(tsee update-var),
     in another rule."))
  (b* ((frame (top-frame compst))
       (scopes (frame->scopes frame))
       (new-scopes (update-var-aux var val scopes))
       (new-frame (change-frame frame :scopes new-scopes)))
    (push-frame new-frame (pop-frame compst)))
  :hooks (:fix)

  :prepwork
  ((define update-var-aux ((var identp) (val valuep) (scopes scope-listp))
     :returns (new-scopes scope-listp)
     :parents nil
     (b* (((when (endp scopes)) nil)
          (scope (scope-fix (car scopes)))
          (pair (omap::in (ident-fix var) scope))
          ((when (or (consp pair)
                     (endp (cdr scopes))))
           (cons (omap::update (ident-fix var) (value-fix val) scope)
                 (scope-list-fix (cdr scopes)))))
       (cons scope (update-var-aux var val (cdr scopes))))
     :hooks (:fix)
     ///
     (defret consp-of-update-var-aux
       (equal (consp new-scopes)
              (consp scopes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-array ((ptr pointerp) (array arrayp) (compst compustatep))
  :guard (not (pointer-nullp ptr))
  :returns (new-compst compustatep)
  :short (xdoc::topstring
          "Update an array in a "
          (xdoc::seetopic "atc-symbolic-computation-states"
                          "canonical representation of computation states")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee write-array), but it does not return an error.
     First, the guard requires the pointer to be non-null,
     which ensures that we always get an address (via @(tsee address-fix)).
     Second, we update the heap with the new array regardless of
     whether an old array at that address exists or not,
     and whether, if it exists, its type and length match the new array;
     we do not consider the type of the pointer either here.
     This way, @(tsee update-array) always guarantees that
     the array goes into the heap,
     thus simplifying rules about it.
     When we replace @(tsee write-array) with @(tsee update-array)
     we ensure that all the conditions mentioned above hold,
     so in a way @(tsee update-array) caches the fact that
     those conditions are satisfied."))
  (b* ((address (address-fix (pointer->address? ptr)))
       (heap (compustate->heap compst))
       (new-heap (omap::update address (array-fix array) heap))
       (new-compst (change-compustate compst :heap new-heap)))
    new-compst)
  :guard-hints (("Goal" :in-theory (enable pointer-nullp)))
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
     (as it is, because we use openers for @(tsee init-scope)),
     the two theorems below move the variables into @(tsee add-var) calls,
     and finally turn @(tsee push-frame) into @(tsee add-frame)."))

  (defruled push-frame-of-one-empty-scope
    (equal (push-frame (frame fun (list nil)) compst)
           (add-frame fun compst))
    :enable add-frame)

  (defruled push-frame-of-one-nonempty-scope
    (implies (and (identp var)
                  (valuep val)
                  (scopep scope))
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

  (defruled exit-scope-of-enter-scope
    (implies (and (compustatep compst)
                  (not (equal (compustate-frames-number compst) 0)))
             (equal (exit-scope (enter-scope compst))
                    compst))
    :enable (enter-scope
             exit-scope
             push-frame
             top-frame
             pop-frame
             compustate-frames-number))

  (defruled exit-scope-of-add-var
    (equal (exit-scope (add-var var val compst))
           (exit-scope compst))
    :enable (exit-scope add-var))

  (defval *atc-exit-scope-rules*
    '(exit-scope-of-enter-scope
      exit-scope-of-add-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-create-var-rules
  :short "Rules about @(tsee create-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem about @(tsee create-var) turns that into @(tsee add-var),
     provided that the variable can be created,
     which we check via the function @('create-var-okp') introduced below.
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
      (not (consp (omap::in (ident-fix var) scope))))
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

  (defruled create-var-to-add-var
    (implies (create-var-okp var compst)
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
     Here we need to include a rule for @(tsee update-var),
     because @('write-var-okp') may need to go through all the layers.
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
     to be included in the list of rules here."))

  (define write-var-okp ((var identp) (type typep) (compst compustatep))
    :guard (> (compustate-frames-number compst) 0)
    :returns (yes/no booleanp)
    :parents nil
    (write-var-aux-okp var type (frame->scopes (top-frame compst)))
    :hooks (:fix)
    :prepwork
    ((define write-var-aux-okp ((var identp) (type typep) (scopes scope-listp))
       :returns (yes/no booleanp)
       :parents nil
       (b* (((when (endp scopes)) nil)
            (scope (scope-fix (car scopes)))
            (pair (omap::in (ident-fix var) scope))
            ((when (consp pair))
             (equal (type-of-value (cdr pair))
                    (type-fix type))))
         (write-var-aux-okp var type (cdr scopes)))
       :hooks (:fix))))

  (defruled write-var-okp-of-enter-scope
    (equal (write-var-okp var type (enter-scope compst))
           (write-var-okp var type compst))
    :enable (write-var-okp
             write-var-aux-okp
             enter-scope))

  (defruled write-var-okp-of-add-var
    (implies (typep type)
             (equal (write-var-okp var type (add-var var2 val2 compst))
                    (if (equal (ident-fix var)
                               (ident-fix var2))
                        (equal (type-of-value val2)
                               type)
                      (write-var-okp var type compst))))
    :enable (write-var-okp
             write-var-aux-okp
             add-var))

  (defruled write-var-okp-of-update-var
    (implies (typep type)
             (equal (write-var-okp var type (update-var var2 val2 compst))
                    (if (equal (ident-fix var)
                               (ident-fix var2))
                        (equal (type-of-value val2)
                               type)
                      (write-var-okp var type compst))))
    :enable (write-var-okp
             update-var)
    :prep-lemmas
    ((defrule lemma
       (implies (and (typep type)
                     (consp scopes))
                (equal (write-var-aux-okp var
                                          type
                                          (update-var-aux var2
                                                          val2
                                                          scopes))
                       (if (equal (ident-fix var)
                                  (ident-fix var2))
                           (equal (type-of-value val2)
                                  type)
                         (write-var-aux-okp var type scopes))))
       :enable (write-var-aux-okp
                update-var-aux))))

  (defruled write-var-okp-when-valuep-of-read-var
    (implies (and (syntaxp (symbolp compst))
                  (equal val (read-var var compst))
                  (valuep val)
                  (typep type))
             (equal (write-var-okp var type compst)
                    (equal (type-of-value val)
                           type)))
    :enable (write-var-okp
             read-var)
    :prep-lemmas
    ((defrule lemma
       (implies (and (equal val (read-var-aux var scopes))
                     (valuep val)
                     (typep type))
                (equal (write-var-aux-okp var type scopes)
                       (equal (type-of-value val)
                              type)))
       :enable (write-var-aux-okp
                read-var-aux))))

  (defruled write-var-to-update-var
    (implies (and (not (equal (compustate-frames-number compst) 0))
                  (write-var-okp var (type-of-value val) compst))
             (equal (write-var var val compst)
                    (update-var var val compst)))
    :enable (write-var-okp
             write-var
             update-var
             errorp)
    :prep-lemmas
    ((defrule lemma
       (implies (write-var-aux-okp var (type-of-value val) scopes)
                (equal (write-var-aux var val scopes)
                       (update-var-aux var val scopes)))
       :enable (write-var-aux-okp
                write-var-aux
                update-var-aux
                errorp))))

  (defval *atc-write-var-rules*
    '(write-var-to-update-var
      write-var-okp-of-enter-scope
      write-var-okp-of-add-var
      write-var-okp-of-update-var
      write-var-okp-when-valuep-of-read-var
      (:e typep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-read-var-rules
  :short "Rules about @(tsee read-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems below about @(tsee read-var) are a bit different
     because @(tsee read-var) does not return a state, but a value instead.
     The first theorem skips over @(tsee enter-scope).
     The second theorem
     either returns the value of the encountered variable or skips over it,
     based on whether the names coincide or not.
     There is no theorem for @(tsee add-frame) because this situation
     never happens during the symbolic execution.
     The third theorem serves for variables read in loops
     that are declared outside the scope of the loop,
     i.e. that are represented as @(tsee update-var)s:
     if the two variables are the same, the value is returned;
     otherwise, we skip over the @(tsee update-var)
     in search for the variable."))

  (defruled read-var-of-enter-scope
    (implies (not (equal (compustate-frames-number compst) 0))
             (equal (read-var var (enter-scope compst))
                    (read-var var compst)))
    :enable (read-var
             read-var-aux
             enter-scope))

  (defruled read-var-of-add-var
    (implies (not (equal (compustate-frames-number compst) 0))
             (equal (read-var var (add-var var2 val compst))
                    (if (equal (ident-fix var)
                               (ident-fix var2))
                        (value-fix val)
                      (read-var var compst))))
    :enable (read-var
             read-var-aux
             add-var
             compustate-frames-number
             push-frame
             top-frame))

  (defruled read-var-of-update-var
    (implies (not (equal (compustate-frames-number compst) 0))
             (equal (read-var var (update-var var2 val2 compst))
                    (if (equal (ident-fix var)
                               (ident-fix var2))
                        (value-fix val2)
                      (read-var var compst))))
    :enable (read-var
             update-var)
    :prep-lemmas
    ((defrule lemma
       (implies (consp scopes)
                (equal (read-var-aux var (update-var-aux var2 val2 scopes))
                       (if (equal (ident-fix var)
                                  (ident-fix var2))
                           (value-fix val2)
                         (read-var-aux var scopes))))
       :enable (read-var-aux
                update-var-aux))))

  (defval *atc-read-var-rules*
    '(read-var-of-enter-scope
      read-var-of-add-var
      read-var-of-update-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-update-var-rules
  :short "Rules about @(tsee update-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about @(tsee update-var) push them into the states,
     sometimes combining them into @(tsee add-var)s.
     The first theorem pushes @(tsee update-var) into @(tsee enter-scope).
     The second theorem combines @(tsee update-var) with @(tsee add-var)
     if the variable is the same, otherwise it pushes @(tsee update-var) in.
     There is no rule for @(tsee add-frame) because that does not happen.
     The third theorem overwrites an @(tsee update-var)
     with an @(tsee update-var) for the same variable.
     The fourth theorem is used to arrange a nest of @(tsee update-var)s
     in alphabetical order of the variable names:
     it swaps two @(tsee update-var)s when the outer one
     has an larger variable than the inner one.
     Note that we need to disable loop stoppers for this rule,
     otherwise ACL2 may not apply it based on the written value terms,
     which are irrelevant to this normalization
     based on alphabetical order.
     Note the @(tsee syntaxp) hypotheses
     that require the identifiers (i.e. variable names)
     to have the form described in @(see atc-identifier-rules).
     Finally, the fifth theorem serves to simplify the case in which
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
     This fifth theorem has a @(tsee syntaxp) hypothesis
     requiring the computation state argument of @(tsee read-var)
     to be a variable;
     this may not be actually necessary,
     but for now we include it just to make sure."))

  (defruled update-var-of-enter-scope
    (equal (update-var var val (enter-scope compst))
           (enter-scope (update-var var val compst)))
    :enable (update-var
             update-var-aux
             enter-scope))

  (defruled update-var-of-add-var
    (equal (update-var var val (add-var var2 val2 compst))
           (if (equal (ident-fix var)
                      (ident-fix var2))
               (add-var var2 val compst)
             (add-var var2 val2 (update-var var val compst))))
    :enable (update-var
             update-var-aux
             add-var))

  (defruled update-var-of-update-var-same
    (equal (update-var var val (update-var var val2 compst))
           (update-var var val compst))
    :enable (update-var
             update-var-aux)
    :prep-lemmas
    ((defrule lemma
       (equal (update-var-aux var val (update-var-aux var val2 scopes))
              (update-var-aux var val scopes))
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
                  (not (equal (compustate-frames-number compst) 0)))
             (equal (update-var var val (update-var var2 val2 compst))
                    (update-var var2 val2 (update-var var val compst))))
    :rule-classes ((:rewrite :loop-stopper nil))
    :enable (update-var
             <<)
    :prep-lemmas
    ((defrule lemma
       (implies (not (equal (ident-fix var)
                            (ident-fix var2)))
                (equal (update-var-aux var val (update-var-aux var2 val2 scopes))
                       (update-var-aux var2 val2 (update-var-aux var val scopes))))
       :enable update-var-aux)))

  (defruled update-var-of-read-var-same
    (implies (and (syntaxp (symbolp compst))
                  (compustatep compst1)
                  (valuep (read-var var compst))
                  (equal (read-var var compst)
                         (read-var var compst1)))
             (equal (update-var var (read-var var compst) compst1)
                    compst1))
    :use (:instance update-var-of-read-var-same-lemma (compst compst1))
    :prep-lemmas
    ((defruled update-var-aux-of-read-var-aux-same
       (implies (valuep (read-var-aux var scopes))
                (equal (update-var-aux var (read-var-aux var scopes) scopes)
                       (scope-list-fix scopes)))
       :enable (read-var-aux
                update-var-aux
                omap::update-of-cdr-of-in-when-in)
       :prep-lemmas
       ((defruled omap::update-of-cdr-of-in-when-in
          (implies (consp (omap::in k m))
                   (equal (omap::update k (cdr (omap::in k m)) m)
                          m))
          :induct (omap::in k m)
          :enable omap::in)))
     (defruled update-var-of-read-var-same-lemma
       (implies (and (compustatep compst)
                     (valuep (read-var var compst)))
                (equal (update-var var (read-var var compst) compst)
                       compst))
       :enable (read-var
                update-var
                update-var-aux-of-read-var-aux-same
                top-frame
                push-frame
                pop-frame
                compustate-frames-number))))

  (defval *atc-update-var-rules*
    '(update-var-of-enter-scope
      update-var-of-add-var
      update-var-of-update-var-same
      update-var-of-update-var-less
      update-var-of-read-var-same)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-write-array-rules
  :short "Rules about @(tsee write-array)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem about @(tsee write-array) turns it into @(tsee update-var),
     similarly to how @(tsee write-var) is turned into @(tsee update-var).
     The condition for the replacement is captured by @('write-array-okp'),
     for which we supply rules to go through all the computation state layers.
     Here we need to include a rule for @(tsee update-var),
     because @('write-var-okp') may need to go through all the layers.
     When the computation state (meta) variable is reached,
     it must be the case that there are hypotheses available
     saying that reading the array
     yields an array of appropriate type and length.
     The rule is used as last resort,
     only if the computation state is an ACL2 variable
     (as enforced by the @(tsee syntaxp) hypothesis)."))

  (define write-array-okp ((ptr pointerp)
                           (type typep)
                           (len natp)
                           (compst compustatep))
    :returns (yes/no booleanp)
    :parents nil
    (b* ((address (pointer->address? ptr))
         (reftype (pointer->reftype ptr))
         (heap (compustate->heap compst))
         ((when (not address)) nil)
         (address+array (omap::in address heap))
         ((unless (consp address+array)) nil)
         (array (cdr address+array))
         ((unless (equal reftype
                         (type-of-array-element array)))
          nil)
         ((unless (equal (type-fix type)
                         (type-of-array-element array)))
          nil)
         ((unless (equal (nfix len)
                         (array-length array)))
          nil))
      t)
    :hooks (:fix))

  (defruled write-array-okp-of-add-frame
    (equal (write-array-okp ptr type len (add-frame fun compst))
           (write-array-okp ptr type len compst))
    :enable (write-array-okp
             add-frame
             push-frame))

  (defruled write-array-okp-of-enter-scope
    (equal (write-array-okp ptr type len (enter-scope compst))
           (write-array-okp ptr type len compst))
    :enable (write-array-okp
             enter-scope
             push-frame
             pop-frame))

  (defruled write-array-okp-of-add-var
    (equal (write-array-okp ptr type len (add-var var val compst))
           (write-array-okp ptr type len compst))
    :enable (write-array-okp
             add-var
             push-frame
             pop-frame))

  (defruled write-array-okp-of-update-var
    (equal (write-array-okp ptr type len (update-var var val compst))
           (write-array-okp ptr type len compst))
    :enable (write-array-okp
             update-var
             push-frame
             pop-frame))

  (defruled write-array-okp-when-arrayp-of-read-array
    (implies (and (syntaxp (symbolp compst))
                  (equal array (read-array ptr compst))
                  (arrayp array)
                  (typep type)
                  (natp len))
             (equal (write-array-okp ptr type len compst)
                    (and (equal (type-of-array-element array)
                                type)
                         (equal (array-length array)
                                len))))
    :enable (write-array-okp read-array arrayp))

  (defruled write-array-to-update-array
    (implies (write-array-okp ptr
                              (type-of-array-element array)
                              (array-length array)
                              compst)
             (equal (write-array ptr array compst)
                    (update-array ptr array compst)))
    :enable (write-array write-array-okp update-array))

  (defval *atc-write-array-rules*
    '(write-array-okp-of-add-frame
      write-array-okp-of-enter-scope
      write-array-okp-of-add-var
      write-array-okp-of-update-var
      write-array-okp-when-arrayp-of-read-array
      write-array-to-update-array)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-read-array-rules
  :short "Rules about @(tsee read-array)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about @(tsee read-array)
     skip over all the functions that represent the computation states,
     except for possibly @(tsee update-array):
     this is similar to the interaction
     between @(tsee read-var) and @(tsee update-var),
     with some complications motivated by
     the possibility that pointers may be null
     and the additional type information contained in pointers.")
   (xdoc::p
    "These complications in the @('read-array-of-update-array') rule
     suggests that,
     while the current model of pointers (see @(tsee pointer))
     seems adequate to represent pointer values in C,
     we should change @(tsee read-array), @(tsee write-array), and maybe others
     to operate directly on addresses:
     this way, we avoid concerns about null pointers and pointer types.
     We will investigate this soon."))

  (defruled read-array-of-add-frame
    (equal (read-array ptr (add-frame fun compst))
           (read-array ptr compst))
    :enable (add-frame push-frame read-array))

  (defruled read-array-of-enter-scope
    (equal (read-array ptr (enter-scope compst))
           (read-array ptr compst))
    :enable (enter-scope
             push-frame
             pop-frame
             read-array))

  (defruled read-array-of-add-var
    (equal (read-array ptr (add-var var val compst))
           (read-array ptr compst))
    :enable (add-var
             push-frame
             pop-frame
             read-array))

  (defruled read-array-of-update-var
    (equal (read-array ptr (update-var var val compst))
           (read-array ptr compst))
    :enable (update-var
             push-frame
             pop-frame
             read-array))

  (defruled read-array-of-update-array
    (implies (and (not (pointer-nullp ptr))
                  (not (pointer-nullp ptr2))
                  (equal (type-of-array-element array)
                         (pointer->reftype ptr)))
             (equal (read-array ptr (update-array ptr2 array compst))
                    (if (equal (pointer->address? ptr)
                               (pointer->address? ptr2))
                        (array-fix array)
                      (read-array ptr compst))))
    :enable (read-array
             update-array
             pointer-nullp))

  (defval *atc-read-array-rules*
    '(read-array-of-add-frame
      read-array-of-enter-scope
      read-array-of-add-var
      read-array-of-update-var
      read-array-of-update-array)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-update-array-rules
  :short "Rules about @(tsee update-array)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We have rules to unconditionally push @(tsee update-array)
     through all the layers except @(tsee update-array).")
   (xdoc::p
    "When @(tsee update-array) is applied to @(tsee update-array),
     we have rules similar to the ones for @(tsee update-var).
     If the two pointers have the same address, we overwrite the array.
     When the two pointers are not null and have different addresses,
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
     Either way, we normalize the nests of @(tsee update-array) calls
     by ordering them according to the pointer.")
   (xdoc::p
    "As observed in @(see atc-read-array-rules),
     it should be possible to simplify some of these rules
     by changing @(tsee read-array) and @(tsee write-array),
     and consequently @(tsee update-array),
     to operate directly on addresses rather than pointers.")
   (xdoc::p
    "We also include a rule saying that
     updating an array with the existing one is a no-op.
     This is similar to @('update-var-of-read-var').
     In particular, it uses two possibly different computation states,
     for the reasons explained for @('update-var-of-read-var')."))

  (defruled update-array-of-add-frame
    (equal (update-array ptr array (add-frame fun compst))
           (add-frame fun (update-array ptr array compst)))
    :enable (update-array
             add-frame
             push-frame))

  (defruled update-array-of-enter-scope
    (equal (update-array ptr array (enter-scope compst))
           (enter-scope (update-array ptr array compst)))
    :enable (update-array
             enter-scope
             push-frame
             pop-frame
             top-frame))

  (defruled update-array-of-add-var
    (equal (update-array ptr array (add-var var val compst))
           (add-var var val (update-array ptr array compst)))
    :enable (update-array
             add-var
             push-frame
             pop-frame
             top-frame))

  (defruled update-array-of-update-var
    (equal (update-array ptr array (update-var var val compst))
           (update-var var val (update-array ptr array compst)))
    :enable (update-array
             update-var
             push-frame
             pop-frame
             top-frame))

  (defruled update-array-of-update-array-same
    (equal (update-array ptr array (update-array ptr array2 compst))
           (update-array ptr array compst))
    :enable update-array)

  (defruled update-array-of-update-array-less-symbol
    (implies (and (syntaxp (and (symbolp ptr)
                                (symbolp ptr2)
                                (symbol< ptr2 ptr)))
                  (not (pointer-nullp ptr))
                  (not (pointer-nullp ptr2))
                  (not (equal (pointer->address? ptr)
                              (pointer->address? ptr2))))
             (equal (update-array ptr array (update-array ptr2 array2 compst))
                    (update-array ptr2 array2 (update-array ptr array compst))))
    :enable (update-array
             pointer-nullp))

  (defruled update-array-of-update-array-less-ident
    (implies (and (syntaxp (and (acl2::ffn-symb-p ptr 'read-var)
                                (acl2::ffn-symb-p ptr2 'read-var)
                                (<< (fargn ptr2 1)
                                    (fargn ptr 1))))
                  (not (pointer-nullp ptr))
                  (not (pointer-nullp ptr2))
                  (not (equal (pointer->address? ptr)
                              (pointer->address? ptr2))))
             (equal (update-array ptr array (update-array ptr2 array2 compst))
                    (update-array ptr2 array2 (update-array ptr array compst))))
    :enable (update-array
             pointer-nullp))

  (defruled update-array-of-read-array-same
    (implies (and (syntaxp (symbolp compst))
                  (not (pointer-nullp ptr))
                  (compustatep compst1)
                  (arrayp (read-array ptr compst))
                  (equal (read-array ptr compst)
                         (read-array ptr compst1)))
             (equal (update-array ptr (read-array ptr compst) compst1)
                    compst1))
    :enable (read-array
             update-array
             pointer-nullp
             arrayp
             omap::update-of-cdr-of-in-when-in)
    :prep-lemmas
    ((defruled omap::update-of-cdr-of-in-when-in
       (implies (consp (omap::in k m))
                (equal (omap::update k (cdr (omap::in k m)) m)
                       m))
       :induct (omap::in k m)
       :enable omap::in)))

  (defval *atc-update-array-rules*
    '(update-array-of-add-frame
      update-array-of-enter-scope
      update-array-of-add-var
      update-array-of-update-var
      update-array-of-update-array-same
      update-array-of-update-array-less-symbol
      update-array-of-update-array-less-ident
      update-array-of-read-array-same)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-compustate-frames-number-rules
  :short "Rules about @(tsee compustate-frames-number)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorems about @(tsee compustate-frames-number)
     serve to discharge the hypotheses about it being not 0
     in some of the other theorems below.
     These are all immediately discharged,
     because the functions used to represent the symbolic execution states
     satisfy that condition
     (by design, for @(tsee add-var) and @(tsee update-var))."))

  (defruled compustate-frames-number-of-add-frame-not-zero
    (not (equal (compustate-frames-number (add-frame fun compst)) 0))
    :enable add-frame)

  (defruled compustate-frames-number-of-enter-scope-not-zero
    (not (equal (compustate-frames-number (enter-scope compst)) 0))
    :enable enter-scope)

  (defruled compustate-frames-number-of-add-var-not-zero
    (not (equal (compustate-frames-number (add-var var val compst)) 0))
    :enable add-var)

  (defruled compustate-frames-number-of-update-var-not-zero
    (not (equal (compustate-frames-number (update-var var val compst)) 0))
    :enable update-var)

  (defval *atc-compustate-frames-number-rules*
    '(compustate-frames-number-of-add-frame-not-zero
      compustate-frames-number-of-enter-scope-not-zero
      compustate-frames-number-of-add-var-not-zero
      compustate-frames-number-of-update-var-not-zero)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-symbolic-computation-state-rules*
  :short "List of rules for symbolic computation states."
  (append *atc-push-frame-rules*
          *atc-pop-frame-rules*
          *atc-exit-scope-rules*
          *atc-create-var-rules*
          *atc-write-var-rules*
          *atc-read-var-rules*
          *atc-update-var-rules*
          *atc-write-array-rules*
          *atc-read-array-rules*
          *atc-update-array-rules*
          *atc-compustate-frames-number-rules*))
