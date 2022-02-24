; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "type-annotation")

(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-array-analysis
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          single-threadedness analysis of Java primitive arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to generate Java code
     that correctly destructively updates (primitive) arrays,
     we perform a " (xdoc::seetopic "acl2::stobj" "stobj") "-like analysis
     to establish that arrays are treated single-threadedly
     in the ACL2 functions that are translated to Java.")
   (xdoc::p
    "Unlike the other pre-translation steps,
     this analysis does not modify the ACL2 function bodies.
     However, this analysis is best carried out
     between the type annotation pre-translation step
     and the variable reuse pre-translation step.
     The reason why this analysis should be carried out
     after the type annotation step
     is that we need the type annotations to determine where the arrays are,
     and subject them to the analysis.
     The reason why this analysis should be carried before
     the variable reuse step
     is that this step may mark and differentiate array variables
     that the analysis needs to ensure that they denote the same array
     and that the array is treated single-threadedly.")
   (xdoc::p
    "This array analysis is similar to ACL2's stobj analysis
     in the sense that it imposes the same draconian constraints
     on the use of arrays,
     namely that the same name is consistently used for each array,
     that functions with array inputs are passed those names,
     that every array possibly modified by a function
     is bound to the same name and is also returned by the surrounding function,
     and so on.")
   (xdoc::p
    "However, this array analysis also differs from the stobj analysis,
     because stobjs are global variables
     whose names must be consistently used by all the functions
     that manipulate them.
     In contrast, (representations of) Java arrays in ACL2 functions
     do not have global names, but their names are local to the functions.
     Consider a function @('f') that takes two arrays as inputs
     and returns them (possibly modified) as outputs,
     and a function @('g') that takes two array inputs @('a') and @('b')
     and calls @('g') with them:
     we need to know how the two array outputs of @('g')
     correspond to the array inputs of @('g'),
     so that we can check that @('f') properly binds
     the possibly modified array @('a') to the variable @('a')
     and the possibly modified array @('b') to the variable @('b').
     In ACL2's stobj analysis, @('g') will have the @('stobjs-out') property
     that says which results are which stobjs, using their global names
     (except the case in which @('g') is
     the same as or mutually recursive with @('f'),
     in which case ACL2 presumably uses the non-recursive branches of the clique
     to determine the output stobjs of the functions).
     In our array analysis, we need something like the @('stobjs-out') property:
     we do that beforehand (i.e. before the array analysis) via
     @(tsee atj-main-function-type) and @(tsee atj-other-function-type),
     which allow the specification of output array names.
     But since array names are not global as pointed out above,
     output array names in the ATJ function type tables alone do not suffice.
     We need to take into account the ``mapping'' between input array names
     (which are the formal parameters of a function)
     and the output array names.
     For the example @('f') above,
     perhaps its two array formal arguments are @('x') and @('y'):
     based on which output array has name @('x') vs. @('y'),
     we can determine the mapping.
     Thus, when we analyze @('g'), which passes @('a') and @('b') to @('f'),
     we match @('a') and @('b') to @('x') and @('y'),
     and we determine which results of @('f')
     must be bound to @('a') and @('b') in @('g').
     Note that this approach works also if @('g')
     is mutually recursive with or the same as @('f')
     (in the latter case the variables @('a') and @('b')
     would be the same as @('x') and @('y') then),
     because all functions must have type and array name information
     before the array analysis takes place.
     If the type and array name information is incorrect/inconsistent,
     the array analysis will reveal that.")
   (xdoc::p
    "Another complication of this array analysis,
     which does not happen with stobjs,
     is that some functions may create new arrays (directly or indirectly).
     These are arrays not passed as inputs, but returned as outputs afresh.
     As such, they do not correspond to any inputs,
     so there is no name mapping.
     This is why
     @(tsee atj-main-function-type) and @(tsee atj-other-function-type)
     allow unnamed array outputs,
     whose meaning is that they must be newly created arrays;
     the array analysis checks that.
     If @('f') returns new arrays,
     and @('g') calls @('f'),
     then the array analysis must ensure that these new arrays
     are bound to variables distinct from each other
     and from the ones of the input arrays.
     In contrast, stobjs are not really created by functions;
     they are declared, essentially as global variables,
     and created beforehand."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-analyze-arrays-in-term
  :short "Array analysis of ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The array analysis assigns to each term a non-empty list of array names,
     corresponding to the array types returned by the term.
     Recall that the type annotation pre-translation step
     assigns a non-empty list of ATJ types to every term;
     the list is a singleton if the term is single-valued,
     otherwise the list's length is the number of results returned by the term.
     Some of these result types may be (Java primitive) arrays:
     in that case, the array analysis assigns
     array names to the corresponding results,
     while it assigns @('nil') to non-array results:
     the list of symbols inferred by the array analysis
     has always the same length as
     the list of types inferred by the type annotations,
     i.e. every term's result gets an array name.
     The array names are the names of the variables that hold the arrays.
     When a term returns a newly created array
     that is not yet bound to any variable,
     its array name, inferred by array analysis, is @('nil').
     All of this is, of course,
     related to the array names that can be specified in
     @(tsee atj-main-function-type) and @(tsee atj-other-function-type):
     see their documentation and implementation.")
   (xdoc::p
    "As the array analysis calculates these array names for terms,
     it also checks that arrays are treated single-threadedly,
     similarly to stobjs.
     The constraints to be satisfied are fairly draconian, like stobjs.
     Each modified array must be
     always bound to the same array name inside a function.
     Different functions may use different names,
     also because array variables are not global.
     A function that takes an array argument can only be passed an array name,
     not a term whose value is an array.
     The exact constraints are explained below.
     If any of these constraints is not satisfied,
     the array analysis fails,
     causing an error that stops the analysis and ATJ.
     Currently these are hard errors,
     but they are distinct from the `internal errors'
     that are so indicated in the error messages of some ATJ code.
     The internal errors are expected to never happen;
     if they do, the reason is an implementation bug.
     On the other hand, errors from the array analysis are expected to happen:
     they are a form of input validation,
     but one that is ``semantically deep'' and can only be performed
     during pre-translation, and not as part of input processing.")
   (xdoc::p
    "Recall that this array analysis takes place
     after the type annotations.
     Thus, terms are unwrapped as they are analyzed.")
   (xdoc::p
    "Besides the list of array names,
     the analysis of a term also returns the list of types of the term.
     This is simply obtained from the type annotations,
     but it is used by the array analysis,
     and so returning it explicitly is useful in the recursive calls
     of the analysis code.")
   (xdoc::p
    "If the term being analyzed is a variable,
     we look at its type.
     Since we handle @(tsee mv-let) specially (see below),
     we expect that all the variables that we encounter ``directly''
     (i.e. not the @(tsee mv-let) variable @('mv'))
     will have singleton type lists:
     we use @(tsee atj-type-list-to-type)
     to convert singletons to single types,
     which causes an error should the type list not be a singleton
     (this would be an implementation error).
     If the type of the variable is an array,
     the result of the array analysis is
     the singleton list with the name of the variable.
     Otherwise, the result of the array analysis is
     the singleton list with @('nil').")
   (xdoc::p
    "If the term being analyzed is a quoted constant,
     we return the singleton list with @('nil').
     A quoted constant is never an array:
     a quoted constant always has an @(':acl2') type,
     according to the type annotations.")
   (xdoc::p
    "If the term being analyzed is neither a variable nor a quoted constant,
     we check whether it is a (type-annotated) @(tsee mv-let) call.
     This is handled by the separate function @('atj-analyze-arrays-in-mv-let'),
     whose first result is a boolean flag that indicates success of failure.
     In case of success,
     the calling function @('atj-analyze-arrays-in-term')
     forwards the second result of @('atj-analyze-arrays-in-mv-let');
     in case of failure, @('atj-analyze-arrays-in-term')
     handles the other kinds of function calls,
     including calls of lambda expressions other than @(tsee mv-let)s,
     which are already handled by @('atj-analyze-arrays-in-mv-let').
     The handling of @(tsee mv-let) calls is explained later;
     first we explain the handling of the other kinds of function calls.")
   (xdoc::p
    "If the term being analyzed is an @(tsee if) call,
     we recursively analyze its three arguments.
     If the test returns an array, the analysis fails:
     we do not allow arrays as @(tsee if) tests.
     The `then' and `else' branches must have the same inferred arrays,
     otherwise the analysis fails;
     that is, no matter which branch is taken,
     the same arrays must be returned.")
   (xdoc::p
    "If the term being analyzed is a call of a function other than @(tsee if),
     we recursively analyze all the arguments.
     We do so with a separate function, @('atj-analyze-arrays-in-args'),
     mutually recursive with @('atj-analyze-arrays-in-term').
     Each of these arguments must be necessarily single-valued
     (see also @(tsee atj-type-annotate-term)),
     so the two lists returned by @('atj-analyze-arrays-in-args')
     are interpreted differently from @('atj-analyze-arrays-in-term'):
     the former are the concatenations of the singleton lists
     inferred for each of the arguments,
     while the latter are lists that apply to the whole term.
     The array analysis fails if two of arguments have the same array name:
     this situation means that the same array is aliased (in Java)
     and possibly subjected to different modifications through the aliases.
     We pass a flag to @('atj-analyze-arrays-in-term') indicating whether
     the function called is a lambda expression or a named function:
     in the latter case, we also ensure that arguments of array types
     are variables, and not other function calls
     (note that they cannot be quoted constants).
     That is, we disallow ``nested'' calls of functions that return arrays.
     For example,
     if @('f') returns an array and @('g') takes an array of the same type,
     we disallow calls @('(g ... (f ...) ...)').
     Instead, one must assign each array returned by a named function
     to some variable, and only pass such variables to names functions.
     In the example of @('f') and @('g') just above,
     one must have @('(let (... (a (f ...)) ...) (g ... a ...))')
     for code generation to proceed.
     It is thus important that the restriction of being variables
     only applies to the array arguments of named functions,
     and not to the array arguments of lambda expressions;
     otherwise, the @(tsee let) form would be illegal as well.
     Recall that we are dealing with annotated terms here:
     so, when we say `variable' here, we really mean
     a call of a (conversion) function on a variable.
     This constraint on array arguments of named functions being variables,
     is not needed for the safety of destructive array updates;
     however, it is useful to simplify
     the subsequent ``inlining'' of array writing functions
     done in ATJ's post-translation.
     Note that stobjs have similar restrictions in ACL2.")
   (xdoc::p
    "If the term being analyzed is an @(tsee mv) call,
     we just return the list of array arguments.
     This is a multi-valued term.")
   (xdoc::p
    "If the term being analyzed is a call of
     an array creation function in @(tsee *atj-jprimarr-new-init-fns*),
     we return a singleton list with @('nil'),
     because it is a newly created, and thus still unnamed, array.")
   (xdoc::p
    "If the term being analyzed is a call
     of a function other than @(tsee if) and @(tsee mv),
     we look up its formals, function type, and output arrays.
     The function type is chosen based on the types of the arguments,
     in the same way as in @(tsee atj-type-annotate-term).
     We match the array formal parameters of the function
     to the array names inferred for the actual arguments
     (see the discussion in @(tsee atj-pre-translation-array-analysis)),
     creating an alist.
     Then we go through the function's output arrays
     (whose names match the array formal parameters
     that may be modified by the function and returned,
     and we use the alist mentioned just above
     to compute the output arrays of the call.
     For example, suppose that we have a call of @('f'),
     and that @('f') has two array formal parameters @('x') and @('y').
     Suppose that the array names inferred
     for the corresponding actual arguments are @('a') and @('b').
     Then we construct first the alist @('((x . a) (y. b))'),
     and then we go through the output arrays of $('f'),
     which may include @('x') and @('y') (not necessarily in that order),
     and for each element of the list we generate
     @('a') if the element is @('x'),
     @('b') if the element is @('y'),
     and @('nil') otherwise.
     The latter @('nil') may indicate
     either a non-array result
     or an array newly created by @('f') (directly or indirectly).
     Note that all of this works also when @('a') and/or @('b') is @('nil'),
     which means that we are passing newly created arrays to @('f'):
     the results corresponding to @('x') and @('y') may then be @('nil'),
     which indicates arrays that have been
     newly created, possibly modified, and not given names yet
     (names are given then they are bound to variables).")
   (xdoc::p
    "If the term being analyzed is a call of a lambda expression
     (but not of the @(tsee mv-let) form, which is explained below),
     we ensure that each array argument with a non-@('nil') name
     is assigned (in the sense of @(tsee let))
     to a variable with the same name:
     the variables are the formal parameters of the lambda expression.
     That is, we go through argument arrays and lambda's formal parameters,
     and ensure that they match as just explained.
     This is an important constraint checked by the array analysis,
     namely that (within each function), each array has a unique name.
     One cannot ``rename'' an array, just like one cannot ``rename'' a stobj:
     a stobj has the same name everywhere (not only within each function).
     It is of course permitted to assign non-arrays to variables liberally.
     Then we return the result of recursively analyzing
     the body of the lambda expression.
     Note that, because of the array naming consistency checks explained above,
     in the body of the lambda expressions the arrays have
     the same names as they did outside the body.
     Some newly created arrays outside the body may have a name inside the body,
     so that their single-threaded use can be checked inside the body.")
   (xdoc::p
    "To handle @(tsee mv-let), we decompose it into its constituents.
     We recursively analyze the subterm that returns a multiple value,
     obtaining a list of output arrays.
     We ensure that all the non-@('nil') elements of this list
     are bound to some variable in the @(tsee mv-let);
     we ensure that by going through the list,
     with a variable that holds the current position in the list,
     and checking that for every non-@('nil') element
     its position is among the indices returned by
     the decomposition of the @(tsee mv-let).
     If some named array were modified and then dropped
     (i.e. not assigned to any variable by the @(tsee mv-let)),
     then its modifications could not be returned
     and it would mean that it may not be used single-threadedly.
     As we perform the above check that no arrays are dropped,
     we also check that the arrays with non-@('nil') names
     are assigned to variables with the same names,
     as with other lambda expressions.
     Then, as with other lambda expressions, we return the result
     of recursively analyzing the body of the @(tsee mv-let)."))

  (define atj-analyze-arrays-in-term ((term pseudo-termp) (wrld plist-worldp))
    :returns (mv (arrays symbol-listp)
                 (types atj-type-listp))
    (b* ((wrapped-term term)
         ((mv term & dst-types) (atj-type-unwrap-term term))
         ((when (pseudo-term-case term :null))
          (raise "Internal error: null term.")
          (mv (list nil) (list (atj-type-irrelevant))))
         ((when (pseudo-term-case term :var))
          (b* ((typed-var (pseudo-term-var->name term))
               ((mv var types) (atj-type-unannotate-var typed-var))
               (type (atj-type-list-to-type types)))
            (if (atj-type-case type :jprimarr)
                (mv (list var) (list type))
              (mv (list nil) dst-types))))
         ((when (pseudo-term-case term :quote))
          (mv (list nil) dst-types))
         ((mv success arrays types)
          (atj-analyze-arrays-in-mv-let wrapped-term wrld))
         ((when success) (mv arrays types))
         (fn (pseudo-term-call->fn term))
         ((when (eq fn 'if))
          (b* ((args (pseudo-term-call->args term))
               ((unless (and (consp args)
                             (consp (cdr args))
                             (consp (cddr args))))
                (raise "Internal error: ~
                        IF call ~x0 does not have three arguments."
                       term)
                (mv (list nil) (list (atj-type-irrelevant))))
               (test (first args))
               (then (second args))
               (else (third args))
               ((mv & test-types) (atj-analyze-arrays-in-term test wrld))
               ((mv then-arrays then-types) (atj-analyze-arrays-in-term then
                                                                        wrld))
               ((mv else-arrays else-types) (atj-analyze-arrays-in-term else
                                                                        wrld))
               ((unless (= (len then-types) (len else-types)))
                (raise "Internal error: ~
                        the branches of ~x0 have ~
                        different numbers of types ~x1 and ~x2."
                       term then-types else-types)
                (mv (list nil) (list (atj-type-irrelevant))))
               (test-type (atj-type-list-to-type test-types))
               ((when (atj-type-case test-type :jprimarr))
                (raise "Array analysis failure: ~
                        an array cannot be used as the test of ~x0."
                       term)
                (mv (list nil) (list (atj-type-irrelevant))))
               ((unless (equal then-arrays else-arrays))
                (raise "Array analysis failure: ~
                        the branches of ~x0 have ~
                        different arrays ~x1 and ~x2."
                       term then-arrays else-arrays)
                (mv (list nil) (list (atj-type-irrelevant)))))
            (mv then-arrays dst-types)))
         (args (pseudo-term-call->args term))
         ((mv arg-arrays arg-types)
          (atj-analyze-arrays-in-args args (pseudo-lambda-p fn) wrld))
         ((unless (no-duplicatesp-eq (remove-eq nil arg-arrays)))
          (raise "Array analysis failure: ~
                  the arguments of the call ~x0 ~
                  contain duplicate arrays ~x1."
                 term (remove-eq nil arg-arrays))
          (mv (list nil) (list (atj-type-irrelevant))))
         ((when (and (eq fn 'mv)
                     (>= (len args) 2))) ; always true
          (mv arg-arrays arg-types))
         ((when (atj-jprimarr-new-init-fn-p fn))
          (mv (list nil)
              (list (atj-type-jprimarr
                     (atj-jprimarr-new-init-fn-to-ptype fn)))))
         ((when (pseudo-term-case term :fncall))
          (b* ((formals (formals+ fn wrld))
               ((unless (= (len arg-arrays) (len formals)))
                (raise "Internal error: ~
                        the number of formals ~x0 of ~x1 differs from ~
                        the number of inferred argument arrays ~x2."
                       formals fn arg-arrays)
                (mv (list nil) (list (atj-type-irrelevant))))
               (fn-info (atj-get-function-type-info fn t wrld))
               (main-fn-type (atj-function-type-info->main fn-info))
               (other-fn-types (atj-function-type-info->others fn-info))
               (all-fn-types (cons main-fn-type other-fn-types))
               (fn-type? (atj-function-type-of-min-input-types arg-types
                                                               all-fn-types))
               (fn-type (or fn-type? main-fn-type))
               (fn-out-arrays (atj-function-type->arrays fn-type))
               ((unless (consp fn-out-arrays))
                (raise "Internal error: ~
                        empty list of output arrays for ~x0."
                       fn)
                (mv (list nil) (list (atj-type-irrelevant))))
               (in-arrays
                (atj-analyze-arrays-input-alist formals arg-arrays arg-types))
               (out-arrays
                (atj-analyze-arrays-output-list fn-out-arrays in-arrays)))
            (mv out-arrays dst-types)))
         (formals (pseudo-lambda->formals fn))
         (formals (atj-type-unannotate-vars formals))
         (- (atj-analyze-arrays-check-lambda arg-arrays formals)))
      (atj-analyze-arrays-in-term (pseudo-lambda->body fn) wrld))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-ANALYZE-ARRAYS-MV-LET decreases:
    :measure (two-nats-measure (pseudo-term-count term) 1))

  (define atj-analyze-arrays-in-args ((args pseudo-term-listp)
                                      (lambdap booleanp)
                                      (wrld plist-worldp))
    :returns (mv (arrays (and (symbol-listp arrays)
                              (equal (len arrays) (len args))))
                 (types (and (atj-type-listp types)
                             (equal (len types) (len args)))))
    (b* (((when (endp args)) (mv nil nil))
         (arg (car args))
         ((mv arrays types) (atj-analyze-arrays-in-term arg wrld))
         (array (car arrays))
         (type (atj-type-list-to-type types))
         ((when (and (not lambdap)
                     (not (null array))
                     (not (atj-type-wrapped-variable-p arg))))
          (raise "Array analysis failure: ~
                  the non-variable array ~x0 is passed to a named function."
                 arg)
          (mv (repeat (len args) nil)
              (repeat (len args) (atj-type-acl2 (atj-atype-value)))))
         ((mv more-arrays more-types) (atj-analyze-arrays-in-args (cdr args)
                                                                  lambdap
                                                                  wrld)))
      (mv (cons array more-arrays)
          (cons type more-types)))
    :measure (two-nats-measure (pseudo-term-list-count args) 0))

  (define atj-analyze-arrays-in-mv-let ((term pseudo-termp) (wrld plist-worldp))
    :returns (mv (success booleanp)
                 (arrays symbol-listp)
                 (types atj-type-listp))
    (b* (((mv mv-let-p & mv-term vars indices body-term)
          (atj-check-annotated-mv-let-call term))
         ((unless mv-let-p) (mv nil nil nil))
         ((unless ; temporary check for termination, will be removed:
              (and (< (pseudo-term-count mv-term)
                      (pseudo-term-count term))
                   (< (pseudo-term-count body-term)
                      (pseudo-term-count term))))
          (raise "Internal error: ~
                  one or both of the terms ~x0 and ~x1 ~
                  are not smaller than the term ~x2."
                 mv-term body-term term)
          (mv nil nil nil))
         ((mv mv-arrays &) (atj-analyze-arrays-in-term mv-term wrld))
         ((when (= (len mv-arrays) 1)) (mv nil nil nil))
         (vars (atj-type-unannotate-vars vars))
         (- (atj-analyze-arrays-check-mv-lambda mv-arrays 0 vars indices))
         ((mv arrays types)
          (atj-analyze-arrays-in-term body-term wrld)))
      (mv t arrays types))
    :measure (two-nats-measure (pseudo-term-count term) 0))

  :prepwork

  ((define atj-analyze-arrays-input-alist ((formals symbol-listp)
                                           (arg-arrays symbol-listp)
                                           (arg-types atj-type-listp))
     :guard (and (= (len arg-arrays) (len formals))
                 (= (len arg-types) (len formals)))
     :returns (alist symbol-symbol-alistp :hyp (and (symbol-listp formals)
                                                    (symbol-listp arg-arrays)))
     :parents nil
     (cond ((endp formals) nil)
           ((atj-type-case (car arg-types) :jprimarr)
            (acons (car formals)
                   (car arg-arrays)
                   (atj-analyze-arrays-input-alist (cdr formals)
                                                   (cdr arg-arrays)
                                                   (cdr arg-types))))
           (t (atj-analyze-arrays-input-alist (cdr formals)
                                              (cdr arg-arrays)
                                              (cdr arg-types))))
     :prepwork ((local (include-book "std/lists/len" :dir :system))))

   (define atj-analyze-arrays-output-list ((fn-out-arrays symbol-listp)
                                           (in-arrays symbol-symbol-alistp))
     :returns (list symbol-listp :hyp :guard)
     :parents nil
     (cond ((endp fn-out-arrays) nil)
           (t (cons (cdr (assoc-eq (car fn-out-arrays) in-arrays))
                    (atj-analyze-arrays-output-list (cdr fn-out-arrays)
                                                    in-arrays))))
     ///
     (more-returns
      (list consp
            :hyp (consp fn-out-arrays)
            :rule-classes :type-prescription))
     (defret len-of-atj-analyze-arrays-output-list
       (equal (len list)
              (len fn-out-arrays))))

   (define atj-analyze-arrays-check-lambda ((arg-arrays symbol-listp)
                                            (formals symbol-listp))
     :guard (= (len formals) (len arg-arrays))
     :returns (nothing null)
     :parents nil
     (b* (((when (endp arg-arrays)) nil)
          (arg-array (car arg-arrays))
          ((when (not arg-array))
           (atj-analyze-arrays-check-lambda (cdr arg-arrays) (cdr formals)))
          ((when (eq arg-array (car formals)))
           (atj-analyze-arrays-check-lambda (cdr arg-arrays) (cdr formals))))
       (raise "Array analysis failure: ~
               cannot assign the array ~x0 to the variable ~x1."
              arg-array (car formals))))

   (define atj-analyze-arrays-check-mv-lambda ((mv-arrays symbol-listp)
                                               (mv-index natp)
                                               (vars symbol-listp)
                                               (indices nat-listp))
     :guard (= (len vars) (len indices))
     :returns (nothing null)
     :parents nil
     (b* (((when (endp mv-arrays)) nil)
          (mv-array (car mv-arrays))
          ((when (not mv-array))
           (atj-analyze-arrays-check-mv-lambda (cdr mv-arrays)
                                               (1+ mv-index)
                                               vars
                                               indices))
          (pos-of-index (index-of mv-index indices))
          ((unless (natp pos-of-index))
           (raise "Array analysis failure: ~
                   the array ~x0 must be assigned to a variable."
                  mv-array))
          (var-at-pos (nth pos-of-index vars))
          ((unless (eq var-at-pos mv-arrays))
           (raise "Array analysis failure: ~
                   the array ~x0 is assigned to variable ~x1."
                  mv-array var-at-pos)))
       (atj-analyze-arrays-check-mv-lambda (cdr mv-arrays)
                                           (1+ mv-index)
                                           vars
                                           indices))
     :prepwork ((local
                 (include-book "std/typed-lists/symbol-listp" :dir :system))))

   (local (in-theory (disable pseudo-termp))))

  :verify-guards nil ; done below

  ///

  (defret-mutual consp-of-atj-analyze-arrays-in-term.arrays
    (defret consp-of-atj-analyze-arrays-in-term.arrays
      (consp arrays)
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-term)
    (defret consp-of-atj-analyze-arrays-in-args.arrays
      (consp arrays)
      :hyp (consp args)
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-args)
    (defret consp-of-atj-analyze-arrays-in-mv-let.arrays
      (consp arrays)
      :hyp (mv-nth 0 (atj-analyze-arrays-in-mv-let term wrld))
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-mv-let))

  (defret-mutual consp-of-atj-analyze-arrays-in-term.types
    (defret consp-of-atj-analyze-arrays-in-term.types
      (consp types)
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-term)
    (defret consp-of-atj-analyze-arrays-in-args.types
      (consp types)
      :hyp (consp args)
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-args)
    (defret consp-of-atj-analyze-arrays-in-mv-let.types
      (consp types)
      :hyp (mv-nth 0 (atj-analyze-arrays-in-mv-let term wrld))
      :rule-classes :type-prescription
      :fn atj-analyze-arrays-in-mv-let))

  (local (include-book "std/typed-lists/symbol-listp" :dir :system))

  (verify-guards atj-analyze-arrays-in-term
    :hints (("Goal"
             :in-theory
             (enable len-of-atj-check-annotated-mv-let.vars/indices)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-analyze-arrays-in-formals+body ((formals symbol-listp)
                                            (body pseudo-termp)
                                            (out-arrays symbol-listp)
                                            (wrld plist-worldp))
  :returns (nothing null)
  :short "Array analysis of ACL2 function bodies."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top level of the array analysis.
     We analyze the body of the function,
     and compare the inferred arrays
     with the ones declared for the function
     (via @(tsee atj-main-function-type) and @(tsee atj-other-function-type)).
     The inferred arrays must be the same as the declared ones,
     except that the inferred ones may have names for newly created arrays.
     More precisely, for each position in the lists:
     if the declared array name at that position is not @('nil')
     then the inferred array name at that position must be the same;
     if the declared array name at that position is @('nil'),
     then the inferred array name at that position may be either @('nil')
     or a new array name that is not among the function's formal parameters.
     In the latter case, it means that the function body has
     directly or indirectly created a new array and assigned it to a variable,
     which is then returned as result of array analysis,
     but the declared array names are only the ones
     that match some formal parameter names.")
   (xdoc::p
    "These checks tie the intraprocedural array analysis
     (performed by @(tsee atj-analyze-arrays-in-term))
     with the output arrays assigned by the user to the functions.
     Recall that
     @(tsee atj-main-function-type) and @(tsee atj-other-function-type)
     check the correctness of the declared types
     but not of the declared output arrays,
     aside from relatively simple constraints such as the fact that
     the non-@('nil') output arrays are unique,
     correspond to some formal parameters with the same array types,
     etc.
     By checking that the inferred arrays are consistent with the declared ones,
     which are used to analyze the callers of the function,
     we ensure that all the arrays potentially modified by the function
     are returned by the function,
     so that the callers have to receive them and return them as well.
     This is similar to ACL2's stobj analysis.")
   (xdoc::p
    "This @('atj-analyze-arrays-in-formals+body') returns nothing,
     but its execution stops with a hard error if the array analysis fails."))
  (b* (((mv arrays &) (atj-analyze-arrays-in-term body wrld))
       ((unless (= (len arrays) (len out-arrays)))
        (raise "Internal error: ~
                the length of the inferred arrays ~x0 ~
                differs from the length of the declared arrays ~x1."
               arrays out-arrays))
       (pass
        (atj-analyze-arrays-in-formals+body-aux formals arrays out-arrays)))
    (if pass
        nil
      (raise "Array analysis failure: ~
              the function with formals ~x0 and body ~x1 ~
              returns the inferred arrays ~x2, ~
              which are inconsistent with the declared arrays ~x3."
             formals body arrays out-arrays)))

  :prepwork
  ((define atj-analyze-arrays-in-formals+body-aux ((formals symbol-listp)
                                                   (inferred symbol-listp)
                                                   (declared symbol-listp))
     :guard (= (len inferred) (len declared))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp inferred)
         (b* ((inf (car inferred))
              (decl (car declared)))
           (and (or (eq inf decl)
                    (and (null decl)
                         (not (member-eq inf formals))))
                (atj-analyze-arrays-in-formals+body-aux formals
                                                        (cdr inferred)
                                                        (cdr declared))))))))
