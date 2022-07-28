; FTY Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
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

  :short "Introduce a fixtype for good results and error results."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This is an experimental tool for now.")

    (xdoc::p
     "It is common for a function to return an error result in certain cases.
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
      which might be accidentally used, as nothing could prevent that.
      The second approach avoids this issue,
      because if there is an error result then there is no good result at all;
      the downside is that the result may have two different types.
      Since disjunctions are awkward in rewrite rules,
      it is beneficial to always introduce a type for
      the union of good and error results,
      and use that as the return type of the function.
      But then one needs rules to handle the inherent disjunction.")

    (xdoc::p
     "When functions naturally return multiple results (via @(tsee mv)),
      the second approach adds an error result,
      while the first approach could be applied to one of the results
      (e.g. the ``main'' one, if there is such a thing).
      Better yet from a conceptual point of view,
      the function can be made to return a single result
      that is either an error or a tuple of the good results.
      This is less efficient than multiple results,
      but it may be more appropriate for a higher-level specification function,
      where issues of efficiency should be secondary,
      and where it may be more important that, in case of error,
      no dummy results are returned, so they cannot be accidentally used.
      The term `tuple' above is used in a broad sense:
      it does not have to be a list of values;
      it could be a value of a @(tsee fty::defprod) type.
      The claim above that
      issues of efficiency should be secondary in specification functions
      fits in a vision in which tools like "
     (xdoc::seetopic "apt::apt" "APT")
     " are used to turn possibly inefficient or even non-executable functions
      into efficient ones.
      When instead, for expediency, a compromise is sought
      in which the same function is used for specification and execution,
      then other considerations may apply,
      and the second approach above may be preferable to the first one.
      Nonetheless, there are applications where the first approach fits well.")

    (xdoc::p
     "When calling functions that may return error results
      (whether the first or second approach above is used),
      it is common to check whether the returned result is an error one,
      and in that case also return an error,
      otherwise continuing the computation if the returned result is a good one.
      When using the error triple idiom,
      ACL2 provides @(tsee er-let*) to handle this pattern,
      which propagates the error triples unchanged;
      @(tsee b*) provides the "
     (xdoc::seetopic "acl2::patbind-er" "@('er') binder")
     ", which expands into something like @(tsee er-let*).
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
      where the fixtype of error results is @(tsee reserr)
      (from the first three letters of each of the two words of `result error'),
      which is provided along with @('defresult').
      This macro also generates rules
      to reason about the disjunction of good and error results.
      Along with @('defresult'),
      a @(tsee b*) binder @(tsee patbind-ok) is provided
      to support the check-and-propagate-error pattern described above.")

    (xdoc::p
     "When using @(tsee define),
      which provides automatic binding of @('__function__')
      to the current function symbol,
      it may be useful to automatically incorporate this information
      into the error result.
      To this end, a macro @(tsee reserrf) is provided
      that automatically adds the function information
      to the information passed explicitly as input to the macro.
      A macro @(tsee reserrf-push) is also provided
      to add function and other information
      to an error of the form
      returned by @(tsee reserrf) or @(tsee reserrf-push),
      resulting in a stack of error information
      corresponding to the call stack.
      The @(tsee patbind-ok) binder automates the check-and-propagation
      of errors that include function information.
      This may be very useful for debugging,
      or in general to provide informative error information.
      It may be less useful for higher-level specifications,
      in which errors are just errors that do not carry much information
      (as producing and consuming that information
      may detract from the clarity and conciseness of the specification).
      Therefore, we plan to introduce a simpler version of
      the @(tsee patbind-ok) binder that just does
      error checking and propagation, without function information;
      this will be also usable in code not written with @(tsee define).")

    (xdoc::p
     "The fact that the same error result type, namely @(tsee reserr),
      is used in all the result types introduced by @('defresult')
      is crucial to supporting the kind of error propagation explained above:
      the same type of error result may be returned
      by any function that returns a type defined via @('defresult'),
      even if the good result types are different.
      It is also crucial that the result type is defined
      as a flat, and not tagged, union of good and error results:
      otherwise, error results would have to be unwrapped and wrapped
      depending on the result types of the callee and caller.")

    (xdoc::p
     "The fixtype of good and error results introduced by @('defresult')
      is similar to an instance of Rust's polymorphic type @('Result').
      However, while the Rust type is parameterized over
      both the good and error result types,
      in @('defresult') errors always have the same type.
      Nonetheless, @(tsee reserr) is defined to
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
      must be disjoint from @(tsee reserr).
      Currently this is not quite explicated
      as an applicability condition as in other event macros,
      but the macro will fail if the disjointness cannot be proved.
      The @(':prepwork') option may be used to add events
      to help the proofs (e.g. lemmas and rule enablements);
      these events should be normally made local."))

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
     "@('pred-when-reserrp')"
     (xdoc::p
      "A theorem asserting that
       a value in the fixtype @(tsee reserrp)
       is also in the fixtype @('type'):")
     (xdoc::codeblock
      "(implies (reserrp x)"
      "         (pred x))"))

    (xdoc::desc
     "@('ok-when-pred-and-not-error')"
     (xdoc::p
      "A theorem asserting that
       a value in the fixtype @('type')
       that is not in the fixtype @('reserr')
       is in the fixtype specified by @(':ok'):")
     (xdoc::codeblock
      "(implies (and (pred x)"
      "              (not (reserrp x)))"
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

(defprod reserr
  :parents (defresult)
  :short "Fixtype of error results."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the fixtype of error results for @(tsee defresult);
     see the introduction of @(tsee defresult) for background and motivation.")
   (xdoc::p
    "An error result consists of some unconstrained information,
     wrapped with @(':error') to make it distinct from any good value
     (assuming that good values do not have the form @('(:error ...)'),
     a condition that seems reasonably easy to satisfy)."))
  ((info acl2::any))
  :tag :error
  :pred reserrp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defoption reserr-option
  reserr
  :parents (defresult)
  :short "Fixtype of optional error results."
  :long
  (xdoc::topstring
   (xdoc::p
    "This can be used for results that
     either are errors or carry no information otherwise.
     That is, @('nil') is the (only) good result."))
  :pred reserr-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmacro+
 reserrf (info)
 :parents (defresult)
 :short "Return an error result with a singleton stack."
 :long
 (xdoc::topstring
  (xdoc::p
   "This macro constructs an error result of fixtype @(tsee reserr)
    with the specified information @('info'),
    accompanied by the name of the current function @('fn'),
    as a doublet @('(fn info)').
    A singleton list with this doublet is returned.
    This is a singleton stack, in the sense explained in @(tsee defresult).")
  (xdoc::p
   "This assumes that @('__function__') is bound to the function name,
    which happens automatically with @(tsee define).")
  (xdoc::p
   "This macro is a bit like the @('reserr') constructor
    of the fixtype @(tsee reserr),
    but the @('f') in the name conveys that
    it adds the name of the function to the infomation passed as argument."))
 `(make-reserr :info (list (list __function__ ,info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmacro+
 reserrf-push (error &optional info)
 :parents (defresult)
 :short "Push the current function onto the stack of an error result,
         optionally with additional information."
 :long
 (xdoc::topstring
  (xdoc::p
   "This is useful when receiving an error result from a called function,
    to add the caller to the stack, and possibly more information,
    before propagating the error.
    This addition is handled automatically when using @(tsee patbind-ok),
    actually using @('nil') as extra information;
    when that binder cannot be used for some reason,
    or when additional information must be pushed,
    then this @('reserrf-push') macro may come handy.")
  (xdoc::p
   "This assumes that @('__function__') is bound to the current function name,
    which is automatically the case when using @(tsee define)."))
 `(b* ((stack (reserr->info ,error)))
    (reserr (cons (list __function__ ,info) stack))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder ok
  :parents (defresult)
  :short "@(tsee b*) binder for checking and propagating
          error results of fixtype @(tsee reserr)."
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
     onto the stack component of the error,
     without (i.e. with @('nil') additional information;
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
     a test of whether it is an error or not,
     and then a second binding of the pattern to the variable if not.
     As done in other binders that come with @(tsee b*),
     we pick a name for the first variable
     that is unlikely to occur in code."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* ((patbinder-ok-fresh-variable-for-result ,(car acl2::forms))
        ((when (reserrp patbinder-ok-fresh-variable-for-result))
         (reserrf-push patbinder-ok-fresh-variable-for-result))
        (,(car args) patbinder-ok-fresh-variable-for-result))
     ,acl2::rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defresult-macro-definition
  :parents (defresult)
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
         (ok-pred-when-type-pred-and-not-reserr
          (acl2::packn-pos (list ok-pred '-when- type-pred '-and-not-reserrp)
                           type)))
      `(encapsulate ()
         ,@prepwork
         (defflatsum ,type
           ,@(and parents? (list :parents parents))
           ,@(and short (list :short short))
           ,@(and long (list :long long))
           (:ok ,ok)
           (:err reserr)
           :pred ,type-pred
           :fix ,type-fix
           :equiv ,type-equiv)
         (defruled ,ok-pred-when-type-pred-and-not-reserr
           (implies (and (,type-pred x)
                         (not (reserrp x)))
                    (,ok-pred x))
           :enable ,type-pred)))))
