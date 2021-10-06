; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defflatsum" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defresult

  :parents (fty-extensions fty)

  :short "Introduce a fixtype for good and error results."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This is an experimental tool for now.")

    (xdoc::p
     "It is common for functions to return error results in certain cases.
      Otherwise, the function returns a good (i.e. non-error) result.")

    (xdoc::p
     "In ACL2, an approach is to have the function return multiple results:
      an error result (@('nil') if there is no error),
      and a good result that is irrelevant if the error result is non-@('nil');
      for instance, this is the idiom of "
     (xdoc::seetopic "acl2::error-triple" "error triples")
     ". Another approach is to have the function return
      either an error result or a good result,
      which requires error and good results to be disjoint.")

    (xdoc::p
     "The two approaches have relative advantages and disadvantages.
      An advantage of the first approach is that
      disjointness of error and good results is not required
      and that each result has always the same type.
      However, a disadvantage is that
      even though the good result is irrelevant
      when the error result is non-@('nil'),
      some good result must be nonetheless returned,
      which might be accidentally used as nothing could prevent that.
      The second approach avoids this issue,
      because if there is an error result then there is no good result at all;
      the downside is that the result may have two different types.
      Since disjunctions are awkward in rewrite rules,
      it is beneficial to always introduce a type for
      the union of good and error results,
      and use that as the return type of the function.
      But then one needs rules to handle the inherent disjunction.")

    (xdoc::p
     "When calling functions that may return error results
      (whether the first or second approach above is used),
      it is common to check whether the returned result is an error one,
      and in that case also return an error,
      otherwise continuing the computation if the return result is a good one.
      When using the error triple idiom,
      ACL2 provides @(tsee er-let*) to handle this pattern,
      which propagates the error triples unchanged;
      @(tsee b*) provides the "
     (xdoc::seetopic "acl2::patbind-er" "@('er') binder")
     ", which expands into @(tsee er-let*).
      As an aside, note that, when verifying return type theorems,
      using @(tsee er-let*) works when the (irrelevant) good result
      returned by a callee with an error result
      also belongs to the type of the good results returned by the caller;
      otherwise, one must explicitly check for the error
      and return an appropriate triple,
      or perhaps use a more complex macro or binder.")

    (xdoc::p
     "The @('defresult') macro provides support for the second approach above.
      Given a fixtype of good results,
      it introduces a fixtype of good and error results,
      where the fixtype of error results is @(tsee resulterr),
      which is provided along with @('defresult').
      This macro also generates rules
      to reason about the disjunction of good and error results.
      Along with @('defresult'),
      a @(tsee b*) binder @(tsee patbind-ok) is provided
      to support the check-and-propagate-error pattern described above.")

    (xdoc::p
     "The @(tsee patbind-ok) binder assumes that
      @('__function__') is bound to the enclosing function name.
      This happens automatically when using @(tsee define).
      As explained in @(tsee patbind-ok),
      as errors are propagated from callee to caller,
      the name of the callee is added to
      a call stack trace in the error result.")

    (xdoc::p
     "The fixtype of good and error results introduced by @('defresult')
      is similar to an instance of Rust's polymorphic type @('Result').
      However, while the Rust type is parameterized over
      both the good and error result types,
      in @('defresult') errors always have the same type.
      Nonetheless, @(tsee resulterr) is defined to
      allow any ACL2 value to be contained in an error result,
      so the lack of parameterization over the type of errors
      does not limit expressivity."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defresult type"
     "           :ok ..."
     "           :pred ..."
     "           :fix ..."
     "           :equiv ..."
     "           :parents ..."
     "           :short ..."
     "           :long ..."
     "           :prepwork ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':type')"
     (xdoc::p
      "A symbol that specifies the name of the new fixtype."))

    (xdoc::desc
     "@(':ok')"
     (xdoc::p
      "A symbol that specifies the fixtype of the good results.
       Let @('ok') be the recognizer of this fixtype."))

    (xdoc::desc
     "@(':pred')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's recognizer.
       If this is @('nil') (the default),
       the name of the recognizer is @('type') followed by @('-p')."))

    (xdoc::desc
     "@(':fix')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's fixer.
       If this is @('nil') (the default),
       the name of the fixer is @('type') followed by @('-fix')."))

    (xdoc::desc
     "@(':equiv')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's equivalence.
       If this is @('nil') (the default),
       the name of the equivalence is @('type') followed by @('-equiv')."))

    (xdoc::desc
     (list
      "@(':parents')"
      "@(':short')"
      "@(':long')")
     (xdoc::p
      "These, if present, are added to
       the XDOC topic generated for the fixtype."))

    (xdoc::desc
     "@(':prepwork')"
     (xdoc::p
      "A list of preparatory event forms.
       See the `" xdoc::*evmac-section-generated-title* "' section.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    defresult

    (xdoc::p
     "The fixtype specified by @(':ok')
      must be disjoint from @(tsee resulterr).
      Currently this is not quite explicated
      as an applicability condition as in other event macros,
      but the macro will fail if the disjointness cannot be proved."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('type')"
     (xdoc::p
      "The fixtype of good and error results."))

    (xdoc::desc
     "@('pred')"
     (xdoc::p
      "The recognizer for the fixtype @('type')."))

    (xdoc::desc
     "@('fix')"
     (xdoc::p
      "The fixer for the fixtype @('type')."))

    (xdoc::desc
     "@('equiv')"
     (xdoc::p
      "The equivalence for the fixtype @('type')."))

    (xdoc::desc
     "@('pred-when-ok')"
     (xdoc::p
      "A theorem asserting that
       a value in the fixtype specified by @(':ok')
       is also in the fixtype @('type'):")
     (xdoc::codeblock
      "(implies (ok x)"
      "         (pred x))"))

    (xdoc::desc
     "@('pred-when-resulterrp')"
     (xdoc::p
      "A theorem asserting that
       a value in the fixtype @(tsee resulterrp)
       is also in the fixtype @('type'):")
     (xdoc::codeblock
      "(implies (resulterrp x)"
      "         (pred x))"))

    (xdoc::desc
     "@('ok-when-pred-and-not-error')"
     (xdoc::p
      "A theorem asserting that
       a value in the fixtype @('type')
       that is not in the fixtype @('resulterr')
       is in the fixtype specified by @(':ok'):")
     (xdoc::codeblock
      "(implies (and (pred x)"
      "              (not (resulterrp x)))"
      "         (ok x))")
     (xdoc::p
      "This theorem is disabled by default,
       because it backchains from @('ok') to @('pred'),
       where the former may be used without any reference to the latter."))

    (xdoc::p
     "The above events are preceded by
      the events specified in @(':prepwork'), if any.")

    (xdoc::p
     "Currently the fixtype @('type') and the first two theorems above
      are generated via @(tsee defflatsum),
      but this may change in the future.
      Users should not rely on the generation of @(tsee defflatsum),
      but just on the generation of the items described above."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprod resulterr
  :short "Fixtype of error results."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the fixtype of error results for @(tsee defresult);
     see the introduction of @(tsee defresult) for background and motivation.")
   (xdoc::p
    "An error result consists of some unconstrained information
     and of a list of symbols that should be normally function names.
     This list is treated like a call stack trace by @(tsee patbind-ok).
     The stack's top is the @(tsee car) of the list."))
  ((info acl2::any)
   (stack acl2::symbol-list))
  :tag :error
  :pred resulterrp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption resulterr-option
  resulterr
  :short "Fixtype of optional error results."
  :long
  (xdoc::topstring
   (xdoc::p
    "This can be used for results that
     either are errors or carry no information otherwise.
     That is, @('nil') is the good result."))
  :pred resulterr-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmacro+
 err (x)
 :short "Return an error result with a singleton stack."
 :long
 (xdoc::topstring
  (xdoc::p
   "This macro constructs an error result of fixtype @(tsee resulterr)
    with the specified information
    and with the current function name as singleton stack.")
  (xdoc::p
   "This assumes that @('__function__') is bound to the function name,
    which happens automatically with @(tsee define)."))
 `(make-resulterr :info ,x :stack (list __function__)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmacro+
 err-push (error)
 :short "Push the current function onto the stack of an error result."
 :long
 (xdoc::topstring
  (xdoc::p
   "This is useful when receiving an error result from a called function,
     to add the caller to the stack before propagating the error.
     This addition is handled automatically when using @(tsee patbind-ok),
     but when that binder cannot be used for some reason,
     then this @('err-push') macro is handy.")
  (xdoc::p
   "This assumes that @('__function__') is bound to the current function name,
     which is automatically the case when using @(tsee define)."))
 `(b* ((error ,error)
       (stack (resulterr->stack error))
       (new-stack (cons __function__ stack)))
    (change-resulterr error :stack new-stack)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder ok
  :short "@(tsee b*) binder for checking and propagating
          error results of fixtype @(tsee resulterr)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is somewhat similar to @(tsee acl2::patbind-er),
     but it is for " (xdoc::seetopic "defresult" "result types") ".")
   (xdoc::p
    "It checks whether the value of the bound term is an error,
     returning a slightly modified error if the check succeeds.
     Otherwise, the binder proceeds with the rest of the computation.
     The aforementioned modification of the error consists in
     pushing the current function's name
     onto the stack component of the error;
     this binder assumes that @('__function__') is bound to the function name,
     which is automatically the case when using @(tsee define).")
   (xdoc::p
    "This binder is used as follows:")
   (xdoc::codeblock
    "(b* (..."
    "     ((ok <pattern>) <term>)"
    "     ...)"
    "  ...)")
   (xdoc::p
    "Note that the argument of @('(ok ...)')
     may be a supported single-valued @(tsee b*) pattern,
     e.g. @('(ok (cons x y))').")
   (xdoc::p
    "In order to support such a pattern,
     we generate an initial binding to a variable,
     which we test whether it is an error or not,
     and then a second binding of the pattern to the variable if not.
     As done in other binders that come with @(tsee b*),
     we pick a name for the first variable
     that is unlikely to occur in code."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* ((patbinder-ok-fresh-variable-for-result ,(car acl2::forms))
        ((when (resulterrp patbinder-ok-fresh-variable-for-result))
         (err-push patbinder-ok-fresh-variable-for-result))
        (,(car args) patbinder-ok-fresh-variable-for-result))
     ,acl2::rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defresult-macro-definition
  :short "Definition of @(tsee defresult)."
  :long (xdoc::topstring-@def "defresult")

  (defmacro defresult (type
                       &key
                       ok
                       pred
                       fix
                       equiv
                       (parents 'nil parents?)
                       short
                       long
                       prepwork)
    `(make-event (defresult-fn
                   ',type
                   ',ok
                   ',pred
                   ',fix
                   ',equiv
                   ',parents
                   ',parents?
                   ',short
                   ',long
                   ',prepwork
                   (w state))))

  (define defresult-fn (type
                        ok
                        pred
                        fix
                        equiv
                        parents
                        parents?
                        short
                        long
                        prepwork
                        (wrld plist-worldp))
    :returns event ; PSEUDO-EVENT-FORMP
    :mode :program
    (b* ((fty-table (get-fixtypes-alist wrld))
         (fty-info (find-fixtype ok fty-table))
         (ok-pred (fixtype->pred fty-info))
         (type-pred (or pred (add-suffix type "-P")))
         (type-fix (or fix (add-suffix type "-FIX")))
         (type-equiv (or equiv (add-suffix type "-EQUIV")))
         (ok-pred-when-type-pred-and-not-resulterr
          (acl2::packn-pos (list ok-pred '-when- type-pred '-and-not-resulterrp)
                           type)))
      `(encapsulate ()
         ,@prepwork
         (defflatsum ,type
           ,@(and parents? (list :parents parents))
           ,@(and short (list :short short))
           ,@(and long (list :long long))
           (:ok ,ok)
           (:err resulterr)
           :pred ,type-pred
           :fix ,type-fix
           :equiv ,type-equiv)
         (defruled ,ok-pred-when-type-pred-and-not-resulterr
           (implies (and (,type-pred x)
                         (not (resulterrp x)))
                    (,ok-pred x))
           :enable ,type-pred)))))
