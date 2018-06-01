; APT Domain Restriction Transformation -- Reference Documentation
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc restrict

  :parents (reference)

  :short "APT domain restriction transformation:
          restrict the effective domain of a function."

  :long

  (xdoc::topapp

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Even though functions are total in ACL2
     (i.e. their domain is always the whole ACL2 universe of values),
     the guard of a function can be regarded as its effective domain
     (i.e. where it is well-defined).
     This transformation adds restrictions to the guard,
     and wraps the body with a test for the restrictions,
     which may enable further optimizations
     by taking advantage of the added restrictions.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "General Form")

   (xdoc::code
    "(restrict old"
    "          restriction"
    "          &key"
    "          :undefined       ; default :undefined"
    "          :new-name        ; default :auto"
    "          :new-enable      ; default :auto"
    "          :thm-name        ; default :auto"
    "          :thm-enable      ; default t"
    "          :non-executable  ; default :auto"
    "          :verify-guards   ; default :auto"
    "          :hints           ; default nil"
    "          :print           ; default :result"
    "          :show-only       ; default nil"
    "  )")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('old')"
    (xdoc::p
     "Denotes the target function to transform.")
    (xdoc::p
     "It must be the name of a function,
      or a <see topic='@(url acl2::numbered-names)'>numbered name</see>
      with a wildcard index that
      <see topic='@(url resolve-numbered-name-wildcard)'>resolves</see>
      to the name of a function.
      In the rest of this documentation page, for expository convenience,
      it is assumed that @('old') is the name of the denoted function.")
    (xdoc::p
     "@('old') must
      be in logic mode,
      be defined,
      have at least one formal argument,
      return a non-<see topic='@(url mv)'>multiple</see> value, and
      have no input or output <see topic='@(url acl2::stobj)'>stobjs</see>.
      If @('old') is recursive, it must
      be singly (not mutually) recursive,
      not have a @(':?') measure (see @(':measure') in @(tsee xargs)), and
      not occur in its own <see topic='@(url tthm)'>termination theorem</see>
      (i.e. not occur in the tests and arguments of its own recursive calls).
      If the @(':verify-guards') input is @('t'),
      @('old') must be guard-verified.")
    (xdoc::p
     "In the rest of this documentation page:")
    (xdoc::ul
     (xdoc::li
      "Let @('x1'), ..., @('xn') be the formal arguments of @('old'),
       where @('n') &gt; 0.")
     (xdoc::li
      "Let @('old-guard<x1,...,xn>') be the guard term of @('old').")
     (xdoc::li
      "If @('old') is not recursive, let
       @({
         old-body<x1,...,xn>
       })
       be the body of @('old').")
     (xdoc::li
      "If @('old') is recursive, let
       @({
         old-body<x1,...,xn,
                  (old update1-x1<x1,...,xn>
                       ...
                       update1-xn<x1,...,xn>)
                  ...
                  (old updatem-x1<x1,...,xn>
                       ...
                       updatem-xn<x1,...,xn>)>
       })
       be the body of @('old'),
       where @('m') &gt; 0 is the number of recursive calls
       in the body of @('old')
       and each @('updatej-xi<x1,...,xn>') is
       the @('i')-th actual argument passed to the @('j')-th recursive call.
       Furthermore,
       let @('contextj<x1,...,xn>') be the context (i.e. controlling tests)
       in which the @('j')-th recursive call occurs.")))

   (xdoc::desc
    "@('restriction')"
    (xdoc::p
     "Denotes the restricting predicate for the domain of @('old'),
      i.e. the predicate that will be added to the guard
      and as the test that wraps the body.")
    (xdoc::p
     "It must be a term
      that includes no free variables other than @('x1'), ..., @('xn'),
      that only calls logic-mode functions,
      that returns a non-<see topic='@(url mv)'>multiple</see> value,
      and that has no output <see topic='@(url acl2::stobj)'>stobjs</see>.
      If the generated function is guard-verified
      (which is determined by the @(':verify-guards') input; see below),
      then the term must only call guard-verified functions,
      except possibly in the @(':logic') subterms of @(tsee mbe)s
      and via @(tsee ec-call).
      The term must not include any calls to @('old').")
    (xdoc::p
     "The term denotes the predicate @('(lambda (x1 ... xn) restriction)').")
    (xdoc::p
     "In order to highlight the dependence on @('x1'), ..., @('xn'),
      in the rest of this documentation page,
      @('restriction<x1,...,xn>') is used for @('restriction')."))

   (xdoc::desc
    "@(':undefined') &mdash; default @(':undefined')"
    (xdoc::p
     "Denotes the value that the generated new function must return
      outside of the domain restriction.")
    (xdoc::p
     "It must be a term
      that includes no free variables other than @('x1'), ..., @('xn'),
      that only calls logic-mode functions,
      that returns a non-<see topic='@(url mv)'>multiple</see> value,
      and that has no output <see topic='@(url acl2::stobj)'>stobjs</see>.
      The term must not include any calls to @('old').")
    (xdoc::p
     "Even if the generated function is guard-verified
      (which is determined by the @(':verify-guards') input; see below),
      the term may call non-guard-verified functions
      outside of the @(':logic') subterms of @(tsee mbe)s
      and not via @(tsee ec-call).
      Since the term is governed by the negation of the guard
      (see the generated new function, below),
      the verification of its guards always succeeds trivially.")
    (xdoc::p
     "In the rest of this documentation page,
      let @('undefined') be this term."))

   (xdoc::desc
    "@(':new-name') &mdash; default @(':auto')"
    (xdoc::p
     "Determines the name of the generated new function:")
    (xdoc::ul
     (xdoc::li
      "@(':auto'),
       to use the <see topic='@(url acl2::numbered-names)'>numbered name</see>
       obtained by <see topic='@(url next-numbered-name)'>incrementing</see>
       the index of @('old').")
     (xdoc::li
      "Any other symbol
       (that is not in the main Lisp package and that is not a keyword),
       to use as the name of the function."))
    (xdoc::p
     "In the rest of this documentation page, let @('new') be this function."))

   (xdoc::desc
    "@(':new-enable') &mdash; default @(':auto')"
    (xdoc::p
     "Determines whether @('new') is enabled:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable it.")
     (xdoc::li
      "@('nil'), to disable it.")
     (xdoc::li
      "@(':auto'), to enable it iff @('old') is enabled.")))

   (xdoc::desc
    "@(':thm-name') &mdash; default @(':auto')"
    (xdoc::p
     "Determines the name of the theorem that relates @('old') to @('new'):")
    (xdoc::ul
     (xdoc::li
      "@(':auto'),
       to use the <see topic='@(url acl2::paired-names)'>paired name</see>
       obtaining by <see topic='@(url make-paired-name)'>pairing</see>
       the name of @('old') and the name of @('new'),
       putting the result into the same package as @('new').")
     (xdoc::li
      "Any other symbol
       (that is not in the main Lisp package and that is not a keyword),
       to use as the name of the theorem."))
    (xdoc::p
     "In the rest of this documentation page,
      let @('old-to-new') be this theorem."))

   (xdoc::desc
    "@(':thm-enable') &mdash; default @('t')"
    (xdoc::p
     "Determines whether @('old-to-new') is enabled:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to enable it.")
     (xdoc::li
      "@('nil'), to disable it.")))

   (xdoc::desc
    "@(':non-executable') &mdash; default @(':auto')"
    (xdoc::p
     "Determines whether @('new') is
      <see topic='@(url acl2::non-executable)'>non-executable</see>:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to make it non-executable.")
     (xdoc::li
      "@('nil'), to not make it non-executable.")
     (xdoc::li
      "@(':auto'), to make it non-executable iff @('old') is non-executable.")))

   (xdoc::desc
    "@(':verify-guards') &mdash; default @(':auto')"
    (xdoc::p
     "Determines whether @('new') is guard-verified:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to guard-verify it.")
     (xdoc::li
      "@('nil'), to not guard-verify it.")
     (xdoc::li
      "@(':auto'), to guard-verify it iff @('old') is guard-verified.")))

   (xdoc::desc
    "@(':hints') &mdash; default @('nil')"
    (xdoc::p
     "Hints to prove the applicability conditions below.")
    (xdoc::p
     "It must be a
      <see topic='@(url keyword-value-listp)'>keyword-value list</see>
      @('(appcond1 hints1 ... appcondp hintsp)')
      where each @('appcondk') is a keyword
      that names one of the applicability conditions below,
      and each @('hintsk') consists of hints as may appear
      just after @(':hints') in a @(tsee defthm).
      The hints @('hintsk') are used
      to prove applicability condition @('appcondk').")
    (xdoc::p
     "The @('appcond1'), ..., @('appcondp') names must be all distinct.")
    (xdoc::p
     "An @('appcondk') is allowed in the @(':hints') input iff
      the named applicability condition is present, as specified below."))

   (xdoc::desc
    "@(':print') &mdash; default @(':result')"
    (xdoc::p
     "A <see topic='@(url print-specifier)'>print specifier</see>."))

   (xdoc::desc
    "@(':show-only') &mdash; default @('nil')"
    (xdoc::p
     "Determines whether the event expansion of @('restrict')
      is submitted to ACL2 or just printed on the screen:")
    (xdoc::ul
     (xdoc::li
      "@('nil'), to submit it.")
     (xdoc::li
      "@('t'), to just print it.
       In this case:
       the event expansion is printed even if @(':print') is @('nil');
       the generated function and theorem are not printed separately
       (other than their appearance in the event expansion),
       even if @(':print') is @(':result') or @(':info') or @(':all');
       no ACL2 output is printed even if @(':print') is @(':all')
       (because the event expansion is not submitted).
       If the call to @('restrict') is redundant
       (see the `Redundancy' section below),
       the event expansion generated by the existing call is printed.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Applicability Conditions")

   (xdoc::p
    "The following conditions must be proved
     in order for the transformation to apply.")

   (xdoc::desc
    "@(':restriction-of-rec-calls')"
    (xdoc::p
     "@('(lambda (x1 ... xn) restriction<x1,...,xn>)')
      is preserved across the recursive calls of @('old'):")
    (xdoc::code
     "(implies restriction<x1,...,xn>"
     "         (and (implies context1<x1,...,xn>"
     "                       restriction<update1-x1<x1,...,xn>,"
     "                                   ...,"
     "                                   update1-xn<x1,...,xn>>)"
     "              ..."
     "              (implies contextm<x1,...,xn>"
     "                       restriction<updatem-x1<x1,...,xn>,"
     "                                   ...,"
     "                                   updatem-xn<x1,...,xn>>)))")
    (xdoc::p
     "This applicability condition is present iff @('old') is recursive."))

   (xdoc::desc
    "@(':restriction-guard')"
    (xdoc::p
     "The restricting predicate is well-defined (according to its guard)
      on every value in the guard of @('old'):")
    (xdoc::code
     "(implies old-guard<x1,...,xn>"
     "         restriction-guard<x1,...,xn>)")
    (xdoc::p
     "where @('restriction-guard<x1,...,xn>') is
      the guard obligation of @('restriction<x1,...,xn>').")
    (xdoc::p
     "This applicability condition is present iff
      the generated function is guard-verified
      (which is determined by the @(':verify-guards') input; see above)."))

   (xdoc::desc
    "@(':restriction-boolean')"
    (xdoc::p
     "The restricting predicate is boolean-valued:")
    (xdoc::code
     "(booleanp restriction<x1,...,xn>)"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Generated Function and Theorem")

   (xdoc::desc
    "@('new')"
    (xdoc::p
     "Domain-restricted version of @('old'):")
    (xdoc::code
     ";; when old is not recursive:"
     "(defun new (x1 ... xn)"
     "  (if (mbt restriction<x1,...,xn>)"
     "      old-body<x1,...,xn>"
     "    undefined))"
     ""
     ";; when old is recursive:"
     "(defun new (x1 ... xn)"
     "  (if (mbt restriction<x1,...,xn>)"
     "      old-body<x1,...,xn,"
     "               (new update1-x1<x1,...,xn>"
     "                    ..."
     "                    update1-xn<x1,...,xn>)"
     "               ..."
     "               (new updatem-x1<x1,...,xn>"
     "                    ..."
     "                    updatem-xn<x1,...,xn>)>"
     "    undefined))")
    (xdoc::p
     "If @('old') is recursive,
      the measure term and well-founded relation of @('new')
      are the same as @('old').")
    (xdoc::p
     "The guard is @('(and old-guard<x1,...,xn> restriction<x1,...,xn>)'),
      where @('old-guard<x1,...,xn>') is the guard term of @('old').")
    (xdoc::p
     "Since the restriction test follows from the guard,
      the test is wrapped by @(tsee mbt).
      Since @(tsee mbt) requires its argument to be @('t')
      (not just non-@('nil')),
      the applicability condition @(':restriction-boolean') ensures that
      the restriction test is @('t') when it is non-@('nil')."))

   (xdoc::desc
    "@('old-to-new')"
    (xdoc::p
     "Theorem that relates @('old') to @('new'):")
    (xdoc::code
     "(defthm old-to-new"
     "  (implies restriction<x1,...,xn>"
     "           (equal (old x1 ... xn)"
     "                  (new x1 ... xn))))"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Redundancy")

   (xdoc::p
    "A call to @('restrict') is redundant if and only if
     it is identical to a previous successful call to @('restrict')
     whose @(':show-only') is not @('t'),
     except that the two calls may differ in
     their @(':print') and @(':show-only') options.
     These options do not affect the generated function and theorem,
     and thus they are ignored for the purpose of redundancy.")

   (xdoc::p
    "A call to @('restrict') whose @(':show-only') is @('t')
     does not generate any event.
     No successive call may be redundant with such a call.")))
