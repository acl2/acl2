; APT Tail Recursion Transformation -- Reference Documentation
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/event-macros/xdoc-constructors" :dir :system)
(include-book "utilities/xdoc-constructors")
(include-book "tailrec")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc tailrec

  :parents (reference)

  :short "APT tail recursion transformation:
          turn a recursive function that is not tail-recursive
          into an equivalent tail-recursive function."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Under certain conditions,
      the computations performed by
      a recursive function that is not tail-recursive
      can be re-arranged so that they can be performed
      by a tail-recursive function
      whose arguments do not grow in the same way as the call stack
      of the original function.
      A tail-recursive function can be compiled into an imperative loop
      that does not run out of space due to the call stack growth."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form-auto tailrec)

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must
       be in logic mode,
       be defined,
       return a non-<see topic='@(url mv)'>multiple</see> value,
       have no input or output <see topic='@(url acl2::stobj)'>stobjs</see>,
       be singly (not mutually) recursive, and
       not have a @(':?') measure.
       If the @(':verify-guards') input of @('tailrec') is @('t'),
       @('old') must be guard-verified.")
     (xdoc::p
      "With the body in <see topic='@(url acl2::term)'>translated</see> form,
       and after expanding all lambda expressions (i.e. @(tsee let)s),
       the function must have the form")
     (xdoc::codeblock
      "(defun old (x1 ... xn)"
      "  (if test<x1,...,xn>"
      "      base<x1,...,xn>"
      "    combine<nonrec<x1,...,xn>,"
      "            (old update-x1<x1,...,xn>"
      "                 ..."
      "                 update-xn<x1,...,xn>)>))")
     (xdoc::p
      "where:")
     (xdoc::ul
      (xdoc::li
       "The term @('test<x1,...,xn>') does not call @('old').
        This term computes the exit test of the recursion.")
      (xdoc::li
       "The term @('base<x1,...,xn>') does not call @('old').
        This term computes the base value of the recursion.
        If the @(':variant') input of @('tailrec')
        is @(':monoid') or @(':monoid-alt'),
        the term @('base<x1,...,xn>') must be ground,
        i.e. actually not contain any of the @('xi') variables.")
      (xdoc::li
       "The term
        @('combine<nonrec<x1,...,xn>,
                   (old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)>')
        contains one or more identical calls to @('old'),
        namely @('(old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)'),
        where each @('update-xi<x1,...,xn>') is a term
        that does not call @('old').
        Let @('combine<nonrec<x1,...,xn>,r>') be the result of
        replacing @('(old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)')
        with a fresh variable @('r').")
      (xdoc::li
       "The term @('combine<nonrec<x1,...,xn>,r>') is not just @('r')
        (otherwise @('old') would already be tail-recursive).")
      (xdoc::li
       "The term @('combine<nonrec<x1,...,xn>,r>')
        is not a call of @(tsee if).")
      (xdoc::li
       "All the occurrences of @('x1'), ..., @('xn')
        in @('combine<nonrec<x1,...,xn>,r>')
        are within a subterm @('nonrec<x1,...,xn>') where @('r') does not occur.
        This means that if @('combine<q,r>') is
        the result of replacing all the occurrences of @('nonrec<x1,...,xn>')
        with a fresh variable @('q'),
        then no @('xi') occurs in @('combine<q,r>').
        The term @('combine<q,r>') represents a binary operator
        that combines @('nonrec<x1,...,xn>')
        (which does not involve the recursive call to @('old'))
        with the result of the recursive call to @('old').
        The constraints just given may be satisfied
        by multiple subterms @('nonrec<x1,...,xn>')
        of @('combine<nonrec<x1,...,xn>,r>'):
        the exact @('nonrec<x1,...,xn>') is determined
        via the procedure described in Section
        `Decomposition of the Recursive Branch' below.")))

    (xdoc::desc
     "@(':variant') &mdash; default @(':monoid')"
     (xdoc::p
      "Indicates the variant of the transformation to use:")
     (xdoc::ul
      (xdoc::li
       "@(':monoid'), for the monoidal variant,
        where the applicability conditions below imply
        the algebraic structure of a monoid (i.e. associativity and identity)
        for the combination operator.")
      (xdoc::li
       "@(':monoid-alt'), for the alternative monoidal variant,
        where the applicability conditions below also imply
        the algebraic structure of a monoid (i.e. associativity and identity)
        for the combination operator.")
      (xdoc::li
       "@(':assoc'), for the associative variant,
        where the applicability conditions below imply
        the algebraic structure of a semigroup (i.e. associativity only)
        for the combination operator."))
     (xdoc::p
      "The associative variant of the transformation is more widely applicable,
       but the monoidal and alternative monoidal variants
       yield simpler functions.
       The applicability conditions for the alternative monoidal variant
       are neither stronger nor weaker than the ones for the monoidal variant,
       so these two variants apply to different cases."))

    (xdoc::desc
     "@(':domain') &mdash; default @(':auto')"
     (xdoc::p
      "Denotes the domain (i.e. predicate) @('domain')
       over which the combination operator @('combine<q,r>')
       must satisfy some of the applicability conditions below.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "The name of a logic-mode unary function
        that returns a non-<see topic='@(url mv)'>multiple</see> value
        and that has no
        input or output <see topic='@(url acl2::stobj)'>stobjs</see>.
        If the functions generated by @('tailrec') are guard-verified
        (which is determined by the @(':verify-guards') input of @('tailrec');
        see below),
        then the @(':domain') function must be guard-verified as well.
        The @(':domain') function must be distinct from @('old').")
      (xdoc::li
       "A unary closed lambda expression
        that only references logic-mode functions,
        that returns a non-<see topic='@(url mv)'>multiple</see> value
        and that has no
        input or output <see topic='@(url acl2::stobj)'>stobjs</see>.
        As an abbreviation, the name @('mac') of a macro stands for
        the lambda expression @('(lambda (z1 z2 ...) (mac z1 z2 ...))'),
        where @('z1'), @('z2'), ... are the required parameters of @('mac');
        that is, a macro name abbreviates its eta-expansion
        (considering only the macro's required parameters).
        If the functions generated by @('tailrec') are guard-verified
        (which is determined by the @(':verify-guards') input of @('tailrec');
        see below),
        then the body of the lambda expression
        must only call guard-verified functions,
        except possibly in the @(':logic') subterms of @(tsee mbe)s
        and via @(tsee ec-call).
        The lambda expression must not include any calls to @('old').")
      (xdoc::li
       "@(':auto'), to automatically infer a domain
        as described in Section `Automatic Inference of a Domain' below."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('domain') be the function or lambda expression."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-wrapper-name)

    (xdoc::desc-apt-input-wrapper-enable)

    (xdoc::desc-apt-input-thm-name t)

    (xdoc::desc-apt-input-thm-enable t)

    (xdoc::desc-apt-input-non-executable t)

    (xdoc::desc-apt-input-verify-guards t)

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print tailrec)

    (xdoc::evmac-input-show-only tailrec)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::h4 "Decomposition of the Recursive Branch")

    (xdoc::p
     "Replace every occurrence of the recursive call
      @('(old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)')
      in the recursive branch
      @('combine<nonrec<x1,...,xn>,
                 (old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)>')
      of @('old')
      with a fresh variable @('r'),
      obtaining @('combine<nonrec<x1,...,xn>,r>').")

    (xdoc::p
     "Try to find the maximal and leftmost subterm @('nr')
      of @('combine<nonrec<x1,...,xn>,r>')
      such that @('r') does not occur in @('nr')
      and such that all the occurrences of @('x1'), ..., @('xn')
      in @('combine<nonrec<x1,...,xn>,r>')
      occur within occurrences of @('nr') in @('combine<nonrec<x1,...,xn>,r>').
      The latter constraint is equivalent to saying that
      after replacing all the occurrences of @('nr')
      in @('combine<nonrec<x1,...,xn>,r>')
      with a fresh variable @('q'),
      the resulting term will have only @('r') and @('q') as free variables.")

    (xdoc::p
     "If such a term @('nr') exists,
      that term is @('nonrec<x1,...,xn>'),
      and @('combine<q,r>') is the result of replacing
      every occurrence of @('nonrec<x1,...,xn>')
      in @('combine<nonrec<x1,...,xn>,r>')
      with @('q').")

    (xdoc::p
     "If such a term @('nr') does not exist, decomposition fails.")

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::h4 "Automatic Inference of a Domain")

    (xdoc::p
     "Consider the following conditions:")

    (xdoc::ol
     (xdoc::li
      "The @(':variant') input of @('tailrec')
       is @(':monoid') or @(':monoid-alt').")
     (xdoc::li
      "The term @('combine<q,r>') (described above)
       has the form @('(op q r)') or @('(op r q)'),
       where @('op') is a named function, with formals @('y1') and @('y2').")
     (xdoc::li
      "The guard term of @('op') has the form @('(and (dom y1) (dom y2))'),
       where @('dom') is a named function."))

    (xdoc::p
     "If all the above coditions hold, the inferred domain is @('dom').
      Otherwise, the inferred domain is @('(lambda (x) t)'),
      i.e. the domain consisting of all values.")

    (xdoc::p
     "This domain inference is a heuristic.
      It has no impact on soundness,
      since the user could supply any domain anyhow.
      Inferring a tigther domain than the one consisting of all values
      may be helpful to prove left and right identity,
      which may not hold over all values
      (e.g. left and right identity of addition).
      On the other hand, associativity may hold over all values
      (e.g. associativity of addition),
      particularly when the combination operator fixes its arguments.
      Given that using a tighter domain than all values
      involves additional applicability conditions below,
      it seems most useful to attempt to infer a tighter domain
      only for the monoidal and alternative monoidal variants,
      and use the domain of all values for the associative variant."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    tailrec

    (xdoc::desc
     "@(':domain-of-base')"
     (xdoc::p
      "The base computation always returns values in the domain:")
     (xdoc::codeblock
      "(implies test<x1,...,xn>"
      "         (domain base<x1,...,xn>))"))

    (xdoc::desc
     "@(':domain-of-nonrec')"
     (xdoc::p
      "The non-recursive operand of the combination operator
       always returns values in the domain,
       when the exit test of the recursion fails:")
     (xdoc::codeblock
      "(implies (not test<x1,...,xn>)"
      "         (domain nonrec<x1,...,xn>))")
     (xdoc::p
      "This applicability condition is present iff
       the @(':variant') input of @('tailrec')
       is @(':monoid') or @(':assoc')."))

    (xdoc::desc
     "@(':domain-of-combine')"
     (xdoc::p
      "The domain is closed under the combination operator:")
     (xdoc::codeblock
      "(implies (and (domain u)"
      "              (domain v))"
      "         (domain combine<u,v>))")
     (xdoc::p
      "This applicability condition is present iff
       the @(':variant') input of @('tailrec')
       is @(':monoid') or @(':assoc')."))

    (xdoc::desc
     "@(':domain-of-combine-uncond')"
     (xdoc::p
      "The combination operator unconditionally returns values in the domain:")
     (xdoc::codeblock
      "(domain combine<u,v>)")
     (xdoc::p
      "This applicability condition is present iff
       the @(':variant') input of @('tailrec') is @(':monoid-alt')."))

    (xdoc::desc
     "@(':combine-associativity')"
     (xdoc::p
      "The combination operator is associative over the domain:")
     (xdoc::codeblock
      "(implies (and (domain u)"
      "              (domain v)"
      "              (domain w))"
      "         (equal combine<u,combine<v,w>>"
      "                combine<combine<u,v>,w>))")
     (xdoc::p
      "This applicability condition is present iff
       the @(':variant') input of @('tailrec')
       is @(':monoid') or @(':assoc')."))

    (xdoc::desc
     "@(':combine-associativity-uncond')"
     (xdoc::p
      "The combination operator is unconditionally associative:")
     (xdoc::codeblock
      "(equal combine<u,combine<v,w>>"
      "      combine<combine<u,v>,w>)")
     (xdoc::p
      "This applicability condition is present iff
       the @(':variant') input of @('tailrec') is @(':monoid-alt')."))

    (xdoc::desc
     "@(':combine-left-identity')"
     (xdoc::p
      "The base value of the recursion
      is left identity of the combination operator:")
     (xdoc::codeblock
      "(implies (and test<x1,...,xn>"
      "             (domain u))"
      "        (equal combine<base<x1...,xn>,u>"
      "               u))")
     (xdoc::p
      "This applicability condition is present iff
       the @(':variant') input of @('tailrec') is
       @(':monoid') or @(':monoid-alt')."))

    (xdoc::desc
     "@(':combine-right-identity')"
     (xdoc::p
      "The base value of the recursion
      is right identity of the combination operator:")
     (xdoc::codeblock
      "(implies (and test<x1,...,xn>"
      "             (domain u))"
      "        (equal combine<u,base<x1...,xn>>"
      "               u))")
     (xdoc::p
      "This applicability condition is present iff
       the @(':variant') input of @('tailrec') is
       @(':monoid') or @(':monoid-alt')."))

    (xdoc::desc
     "@(':domain-guard')"
     (xdoc::p
      "The domain is well-defined (according to its guard) on every value:")
     (xdoc::codeblock
      "domain-guard<z>")
     (xdoc::p
      "where @('domain-guard<z>') is the guard term of @('domain')
       if @('domain') is a function name,
       while it is the guard obligation of @('domain')
       if @('domain') is a lambda expression.")
     (xdoc::p
      "This applicability condition is present iff
       the functions generated by @('tailrec') are guard-verified
       (which is determined by
       the @(':verify-guards') input of @('tailrec'))."))

    (xdoc::desc
     "@(':combine-guard')"
     (xdoc::p
      "The combination operator is well-defined (according to its guard)
       on every value in the domain:")
     (xdoc::codeblock
      "(implies (and (domain q)"
      "             (domain r))"
      "        combine-guard<q,r>)")
     (xdoc::p
      "where @('combine-guard<q,r>') is
       the guard obligation of @('combine<q,r>').")
     (xdoc::p
      "This applicability condition is present iff
       the functions generated by @('tailrec') are guard-verified
       (which is determined by
       the @(':verify-guards') input of @('tailrec'))."))

    (xdoc::desc
     "@(':domain-of-nonrec-when-guard')"
     (xdoc::p
      "The non-recursive operand of the combination operator
       returns values in the domain,
       when the exit test of the recursion fails,
       and under the guard of @('old'):")
     (xdoc::codeblock
      "(implies (and old-guard<x1,...,xn>"
      "             (not test<x1,...,xn>))"
      "        (domain nonrec<x1,...,xn>))")
     (xdoc::p
      "where @('old-guard<x1,...,xn>') is the guard term of @('old').")
     (xdoc::p
      "This applicability condition is present iff
       the functions generated by @('tailrec') are guard-verified
       (which is determined by the @(':verify-guards') input of @('tailrec'))
       and the @(':variant') input of @('tailrec') is @(':monoid-alt')."))

    (xdoc::p
     "When present,
      @(':combine-left-identity') and @(':combine-right-identity'),
      together with
      either @(':combine-associativity') or @(':combine-associativity-uncond')
      (one of them is always present),
      and together with
      either @(':domain-of-combine') or @(':domain-of-combine-uncond')
      (one of them is always present),
      mean that the domain has the algebraic structure of a monoid,
      with the combination operator as the binary operator
      and with the base value of the recursion as identity.
      When @(':combine-left-identity') and @(':combine-right-identity')
      are absent,
      the domain has the algebraic structure of a semigroup."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Tail-recursive equivalent of @('old'):")
     (xdoc::codeblock
      ";; when the :variant input of tailrec is :monoid or :monoid-alt:"
      "(defun new (x1 ... xn r)"
      "  (if test<x1,...,xn>"
      "      r"
      "    (new update-x1<x1,...,xn>"
      "         ..."
      "         update-xn<x1,...,xn>"
      "         combine<r,nonrec<x1,...,xn>>)))"
      ""
      ";; when the :variant input of tailrec is :assoc:"
      "(defun new (x1 ... xn r)"
      "  (if test<x1,...,xn>"
      "      combine<r,base<x1,...,xn>>"
      "    (new update-x1<x1,...,xn>"
      "         ..."
      "         update-xn<x1,...,xn>"
      "         combine<r,nonrec<x1,...,xn>>)))")
     (xdoc::p
      "The measure term and well-founded relation of @('new')
       are the same as @('old').")
     (xdoc::p
      "The guard is @('(and old-guard<x1,...,xn> (domain r))'),
       where @('old-guard<x1,...,xn>') is the guard term of @('old')."))

    (xdoc::desc
     "@('wrapper')"
     (xdoc::p
      "Non-recursive wrapper of @('new'):")
     (xdoc::codeblock
      ";; when the :variant input of tailrec is :monoid or :monoid-alt:"
      "(defun wrapper (x1 ... xn)"
      "  (new x1 ... xn base<x1,...,xn>))"
      ""
      ";; when the :variant input tailrec is :assoc:"
      "(defun wrapper (x1 ... xn)"
      "  (if test<x1,...,xn>"
      "      base<x1,...,xn>"
      "    (new update-x1<x1,...,xn>"
      "         ..."
      "         update-xn<x1,...,xn>"
      "         nonrec<x1,...,xn>)))")
     (xdoc::p
      "The guard is the same as @('old')."))

    (xdoc::desc
     "@('old-to-wrapper')"
     (xdoc::p
      "Theorem that relates @('old') to @('wrapper'):")
     (xdoc::codeblock
      "(defthm old-to-wrapper"
      "  (equal (old x1 ... xn)"
      "         (wrapper x1 ... xn)))")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy tailrec)))
