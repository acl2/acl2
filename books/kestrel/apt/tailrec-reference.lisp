; APT Tail Recursion Transformation -- Reference Documentation
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc tailrec

  :parents (reference)

  :short "APT tail recursion transformation:
          turn a recursive function that is not tail-recursive
          into an equivalent tail-recursive function."

  :long

  "<h3>
   Introduction
   </h3>

   <p>
   Under certain conditions,
   the computations performed by
   a recursive function that is not tail-recursive
   can be re-arranged so that they can be performed
   by a tail-recursive function
   whose arguments do not grow in the same way as the call stack
   of the original function.
   A tail-recursive function can be compiled into an imperative loop
   that does not run out of space due to the call stack growth.
   </p>

   <h3>
   General Form
   </h3>

   @({
     (tailrec old
              &key
              :variant         ; default :monoid
              :domain          ; default :auto
              :new-name        ; default :auto
              :new-enable      ; default :auto
              :wrapper-name    ; default :auto
              :wrapper-enable  ; default t
              :thm-name        ; default :auto
              :thm-enable      ; default t
              :non-executable  ; default :auto
              :verify-guards   ; default :auto
              :hints           ; default nil
              :print           ; default :result
              :show-only       ; default nil
       )
   })

   <h3>
   Inputs
   </h3>

   <p>
   @('old')
   </p>

     <blockquote>

     <p>
     Denotes the target function to transform.
     </p>

     <p>
     It must be the name of a function,
     or a <see topic='@(url acl2::numbered-names)'>numbered name</see>
     with a wildcard index that
     <see topic='@(url resolve-numbered-name-wildcard)'>resolves</see>
     to the name of a function.
     In the rest of this documentation page, for expository convenience,
     it is assumed that @('old') is the name of the denoted function.
     </p>

     <p>
     @('old') must
     be in logic mode,
     be defined,
     return a non-<see topic='@(url mv)'>multiple</see> value,
     have no input or output <see topic='@(url acl2::stobj)'>stobjs</see>,
     be singly (not mutually) recursive, and
     not have a @(':?') measure.
     If the @(':verify-guards') input of @('tailrec') is @('t'),
     @('old') must be guard-verified.
     </p>

     <p>
     With the body in <see topic='@(url acl2::term)'>translated</see> form,
     and after expanding all lambda expressions (i.e. @(tsee let)s),
     the function must have the form
     </p>

     @({
       (defun old (x1 ... xn)
         (if test<x1,...,xn>
             base<x1,...,xn>
           combine<nonrec<x1,...,xn>,
                   (old update-x1<x1,...,xn>
                        ...
                        update-xn<x1,...,xn>)>))
     })

     <p>
     where:
     </p>

     <ul>

       <li>
       The term @('test<x1,...,xn>') does not call @('old').
       This term computes the exit test of the recursion.
       </li>

       <li>
       The term @('base<x1,...,xn>') does not call @('old').
       This term computes the base value of the recursion.
       If the @(':variant') input of @('tailrec')
       is @(':monoid') or @(':monoid-alt'),
       the term @('base<x1,...,xn>') must be ground,
       i.e. actually not contain any of the @('xi') variables.
       </li>

       <li>
       The term
       @('combine<nonrec<x1,...,xn>,
                  (old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)>')
       contains one or more identical calls to @('old'),
       namely @('(old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)'),
       where each @('update-xi<x1,...,xn>') is a term
       that does not call @('old').
       Let @('combine<nonrec<x1,...,xn>,r>') be the result of
       replacing @('(old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)')
       with a fresh variable @('r').
       </li>

       <li>
       The term @('combine<nonrec<x1,...,xn>,r>') is not just @('r')
       (otherwise @('old') would already be tail-recursive).
       </li>

       <li>
       The term @('combine<nonrec<x1,...,xn>,r>') does not call @(tsee if).
       </li>

       <li>
       All the occurrences of @('x1'), ..., @('xn')
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
       `Decomposition of the Recursive Branch' below.
       </li>

     </ul>

     </blockquote>

   <p>
   @(':variant') &mdash; default @(':monoid')
   </p>

     <blockquote>

     <p>
     Indicates the variant of the transformation to use:
     </p>

     <ul>

       <li>
       @(':monoid'), for the monoidal variant,
       where the applicability conditions below imply
       the algebraic structure of a monoid (i.e. associativity and identity)
       for the combination operator.
       </li>

       <li>
       @(':monoid-alt'), for the alternative monoidal variant,
       where the applicability conditions below also imply
       the algebraic structure of a monoid (i.e. associativity and identity)
       for the combination operator.
       </li>

       <li>
       @(':assoc'), for the associative variant,
       where the applicability conditions below imply
       the algebraic structure of a semigroup (i.e. associativity only)
       for the combination operator.
       </li>

     </ul>

     <p>
     The associative variant of the transformation is more widely applicable,
     but the monoidal and alternative monoidal variants yield simpler functions.
     The applicability conditions for the alternative monoidal variant
     are neither stronger nor weaker than the ones for the monoidal variant,
     so these two variants apply to different cases.
     </p>

     </blockquote>

   <p>
   @(':domain') &mdash; default @(':auto')
   </p>

     <blockquote>

     <p>
     Denotes the domain (i.e. predicate) @('domain')
     over which the combination operator @('combine<q,r>')
     must satisfy some of the applicability conditions below.
     </p>

     <p>
     It must be one of the following:
     </p>

     <ul>

       <li>
       The name of a logic-mode unary function
       that returns a non-<see topic='@(url mv)'>multiple</see> value
       and that has no
       input or output <see topic='@(url acl2::stobj)'>stobjs</see>.
       If the functions generated by @('tailrec') are guard-verified
       (which is determined by the @(':verify-guards') input of @('tailrec');
       see below),
       then the @(':domain') function must be guard-verified as well.
       The @(':domain') function must be distinct from @('old').
       </li>

       <li>
       A unary closed lambda expression
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
       The lambda expression must not include any calls to @('old').
       </li>

       <li>
       @(':auto'), to automatically infer a domain
       as described in Section `Automatic Inference of a Domain' below.
       </li>

     </ul>

     <p>
     In the rest of this documentation page,
     let @('domain') be the function or lambda expression.
     </p>

     </blockquote>

   <p>
   @(':new-name') &mdash; default @(':auto')
   </p>

     <blockquote>

     <p>
     Determines the name of the generated new function:
     </p>

     <ul>

       <li>
       @(':auto'),
       to use the <see topic='@(url acl2::numbered-names)'>numbered name</see>
       obtained by <see topic='@(url next-numbered-name)'>incrementing</see>
       the index of @('old').
       </li>

       <li>
       Any other symbol
       (that is not in the main Lisp package and that is not a keyword),
       to use as the name of the function.
       </li>

     </ul>

     <p>
     In the rest of this documentation page, let @('new') be this function.
     </p>

     </blockquote>

   <p>
   @(':new-enable') &mdash; default @(':auto')
   </p>

     <blockquote>

     <p>
     Determines whether @('new') is enabled:
     </p>

     <ul>

       <li>
       @('t'), to enable it.
       </li>

       <li>
       @('nil'), to disable it.
       </li>

       <li>
       @(':auto'), to enable it iff @('old') is enabled.
       </li>

     </ul>

     </blockquote>

   <p>
   @(':wrapper-name') &mdash; default @(':auto')
   </p>

     <blockquote>

     <p>
     Determines the name of the generated wrapper function:
     </p>

     <ul>

       <li>
       @(':auto'),
       to use the concatenation of the name of @('new') with @('-wrapper').
       </li>

       <li>
       Any other symbol
       (that is not in the main Lisp package and that is not a keyword),
       to use as the name of the function.
       </li>

     </ul>

     <p>
     In the rest of this documentation page, let @('wrapper') be this function.
     </p>

     </blockquote>

   <p>
   @(':wrapper-enable') &mdash; default @('t')
   </p>

     <blockquote>

     <p>
     Determines whether @('wrapper') is enabled:
     </p>

     <ul>

       <li>
       @('t'), to enable it.
       </li>

       <li>
       @('nil'), to disable it.
       </li>

     </ul>

     </blockquote>

   <p>
   @(':thm-name') &mdash; default @(':auto')
   </p>

     <blockquote>

     <p>
     Determines the name of the theorem that relates @('old') to @('wrapper'):
     </p>

     <ul>

       <li>
       @(':auto'),
       to use the <see topic='@(url acl2::paired-names)'>paired name</see>
       obtaining by <see topic='@(url make-paired-name)'>pairing</see>
       the name of @('old') and the name of @('new'),
       putting the result into the same package as @('new').
       </li>

       <li>
       Any other symbol
       (that is not in the main Lisp package and that is not a keyword),
       to use as the name of the theorem.
       </li>

     </ul>

     <p>
     In the rest of this documentation page,
     let @('old-to-wrapper') be this theorem.
     </p>

     </blockquote>

   <p>
   @(':thm-enable') &mdash; default @('t')
   </p>

     <blockquote>

     <p>
     Determines whether @('old-to-wrapper') is enabled:
     </p>

     <ul>

       <li>
       @('t'), to enable it.
       </li>

       <li>
       @('nil'), to disable it.
       </li>

     </ul>

     </blockquote>

   <p>
   @(':non-executable') &mdash; default @(':auto')
   </p>

     <blockquote>

     <p>
     Determines whether @('new') and @('wrapper') are
     <see topic='@(url acl2::non-executable)'>non-executable</see>:
     </p>

     <ul>

       <li>
       @('t'), to make them non-executable.
       </li>

       <li>
       @('nil'), to not make them non-executable.
       </li>

       <li>
       @(':auto'), to make them non-executable iff @('old') is non-executable.
       </li>

     </ul>

     </blockquote>

   <p>
   @(':verify-guards') &mdash; default @(':auto')
   </p>

     <blockquote>

     <p>
     Determines whether  @('new') and @('wrapper') are guard-verified:
     </p>

     <ul>

       <li>
       @('t'), to guard-verify them.
       </li>

       <li>
       @('nil'), to not guard-verify them.
       </li>

       <li>
       @(':auto'), to guard-verify them iff @('old') is guard-verified.
       </li>

     </ul>

     </blockquote>

   <p>
   @(':hints') &mdash; default @('nil')
   </p>

     <blockquote>

     <p>
     Hints to prove the applicability conditions below.
     </p>

     <p>
     It must be a
     <see topic='@(url keyword-value-listp)'>keyword-value list</see>
     @('(appcond1 hints1 ... appcondp hintsp)')
     where each @('appcondk') is a keyword
     that names one of the applicability conditions below,
     and each @('hintsk') consists of hints as may appear
     just after @(':hints') in a @(tsee defthm).
     The hints @('hintsk') are used
     to prove applicability condition @('appcondk').
     </p>

     <p>
     The @('appcond1'), ..., @('appcondp') names must be all distinct.
     </p>

     <p>
     An @('appcondk') is allowed in the @(':hints') input iff
     the named applicability condition is present, as specified below.
     </p>

     </blockquote>

   <p>
   @(':print') &mdash; default @(':result')
   </p>

     <blockquote>

     <p>
     A <see topic='@(url print-specifier)'>print specifier</see>
     to control the output printed on the screen.
     </p>

     </blockquote>

   <p>
   @(':show-only') &mdash; default @('nil')
   </p>

     <blockquote>

     <p>
     Determines whether the events generated by @('tailrec')
     should be submitted or only shown on the screen:
     </p>

     <ul>

       <li>
       @('nil'), to submit the events.
       </li>

       <li>
       @('t'), to only show the events.
       </li>

     </ul>

     </blockquote>

   <h4>
   Decomposition of the Recursive Branch
   </h4>

   <p>
   Replace every occurrence of the recursive call
   @('(old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)')
   in the recursive branch
   @('combine<nonrec<x1,...,xn>,
              (old update-x1<x1,...,xn> ... update-xn<x1,...,xn>)>')
   of @('old')
   with a fresh variable @('r'),
   obtaining @('combine<nonrec<x1,...,xn>,r>').
   </p>

   <p>
   Try to find the maximal and leftmost subterm @('nr')
   of @('combine<nonrec<x1,...,xn>,r>')
   such that @('r') does not occur in @('nr')
   and such that all the occurrences of @('x1'), ..., @('xn')
   in @('combine<nonrec<x1,...,xn>,r>')
   occur within occurrences of @('nr') in @('combine<nonrec<x1,...,xn>,r>').
   The latter constraint is equivalent to saying that
   after replacing all the occurrences of @('nr')
   in @('combine<nonrec<x1,...,xn>,r>')
   with a fresh variable @('q'),
   the resulting term will have only @('r') and @('q') as free variables.
   </p>

   <p>
   If such a term @('nr') exists,
   that term is @('nonrec<x1,...,xn>'),
   and @('combine<q,r>') is the result of replacing
   every occurrence of @('nonrec<x1,...,xn>')
   in @('combine<nonrec<x1,...,xn>,r>')
   with @('q').
   </p>

   <p>
   If such a term @('nr') does not exist, decomposition fails.
   </p>

   <h4>
   Automatic Inference of a Domain
   </h4>

   <p>
   Let @('combine<q,r>') be the term described above.
   </p>

   <p>
   If @('combine<q,r>') has the form @('(op q r)') or @('(op r q)'),
   where @('op') is a named function with formals @('y1') and @('y2'),
   and the guard term of @('op') has the form @('(and (dom y1) (dom y2))'),
   where @('dom') is a named function,
   then @('dom') is the inferred domain.
   That is, if the combination operator is
   ``well-defined'' (according to its guard) on a domain,
   we use that as the domain over which
   the combination operator must satisfy
   some of the applicability conditions below.
   </p>

   <p>
   Otherwise, the inferred domain is @('(lambda (x) t)').
   That is, the domain consists of all values.
   </p>

   <h3>
   Applicability Conditions
   </h3>

   <p>
   The following conditions must be proved
   in order for the transformation to apply.
   </p>

   <p>
   @(':domain-of-base')
   </p>

     <blockquote>

     <p>
     The base computation always returns values in the domain:
     </p>

     @({
       (implies test<x1,...,xn>
                (domain base<x1,...,xn>))
     })

     </blockquote>

   <p>
   @(':domain-of-nonrec')
   </p>

     <blockquote>

     <p>
     The non-recursive operand of the combination operator
     always returns values in the domain,
     when the exit test of the recursion fails:
     </p>

     @({
       (implies (not test<x1,...,xn>)
                (domain nonrec<x1,...,xn>))
     })

     <p>
     This applicability condition is present iff
     the @(':variant') input of @('tailrec') is @(':monoid') or @(':assoc').
     </p>

     </blockquote>

   <p>
   @(':domain-of-combine')
   </p>

     <blockquote>

     <p>
     The domain is closed under the combination operator:
     </p>

     @({
       (implies (and (domain u)
                     (domain v))
                (domain combine<u,v>))
     })

     <p>
     This applicability condition is present iff
     the @(':variant') input of @('tailrec') is @(':monoid') or @(':assoc').
     </p>

     </blockquote>

   <p>
   @(':domain-of-combine-uncond')
   </p>

     <blockquote>

     <p>
     The combination operator unconditionally returns values in the domain:
     </p>

     @({
       (domain combine<u,v>)
     })

     <p>
     This applicability condition is present iff
     the @(':variant') input of @('tailrec') is @(':monoid-alt').
     </p>

     </blockquote>

   <p>
   @(':combine-associativity')
   </p>

     <blockquote>

     <p>
     The combination operator is associative over the domain:
     </p>

     @({
       (implies (and (domain u)
                     (domain v)
                     (domain w))
                (equal combine<u,combine<v,w>>
                       combine<combine<u,v>,w>))
     })

     <p>
     This applicability condition is present iff
     the @(':variant') input of @('tailrec') is @(':monoid') or @(':assoc').
     </p>

     </blockquote>

   <p>
   @(':combine-associativity-uncond')
   </p>

     <blockquote>

     <p>
     The combination operator is unconditionally associative:
     </p>

     @({
       (equal combine<u,combine<v,w>>
              combine<combine<u,v>,w>)
     })

     <p>
     This applicability condition is present iff
     the @(':variant') input of @('tailrec') is @(':monoid-alt').
     </p>

     </blockquote>

   <p>
   @(':combine-left-identity')
   </p>

     <blockquote>

     <p>
     The base value of the recursion
     is left identity of the combination operator:
     </p>

     @({
       (implies (and test<x1,...,xn>
                     (domain u))
                (equal combine<base<x1...,xn>,u>
                       u))
     })

     <p>
     This applicability condition is present iff
     the @(':variant') input of @('tailrec') is
     @(':monoid') or @(':monoid-alt').
     </p>

     </blockquote>

   <p>
   @(':combine-right-identity')
   </p>

     <blockquote>

     <p>
     The base value of the recursion
     is right identity of the combination operator:
     </p>

     @({
       (implies (and test<x1,...,xn>
                     (domain u))
                (equal combine<u,base<x1...,xn>>
                       u))
     })

     <p>
     This applicability condition is present iff
     the @(':variant') input of @('tailrec') is
     @(':monoid') or @(':monoid-alt').
     </p>

     </blockquote>

   <p>
   @(':domain-guard')
   </p>

     <blockquote>

     <p>
     The domain is well-defined (according to its guard) on every value:
     </p>

     @({
       domain-guard<z>
     })

     <p>
     where @('domain-guard<z>') is the guard term of @('domain')
     if @('domain') is a function name,
     while it is the guard obligation of @('domain')
     if @('domain') is a lambda expression.
     </p>

     <p>
     This applicability condition is present iff
     the functions generated by @('tailrec') are guard-verified
     (which is determined by the @(':verify-guards') input of @('tailrec')).
     </p>

     </blockquote>

   <p>
   @(':combine-guard')
   </p>

     <blockquote>

     <p>
     The combination operator is well-defined (according to its guard)
     on every value in the domain:
     </p>

     @({
       (implies (and (domain q)
                     (domain r))
                combine-guard<q,r>)
     })

     <p>
     where @('combine-guard<q,r>') is
     the guard obligation of @('combine<q,r>').
     </p>

     <p>
     This applicability condition is present iff
     the functions generated by @('tailrec') are guard-verified
     (which is determined by the @(':verify-guards') input of @('tailrec')).
     </p>

     </blockquote>

   <p>
   @(':domain-of-nonrec-when-guard')
   </p>

     <blockquote>

     <p>
     The non-recursive operand of the combination operator
     returns values in the domain,
     when the exit test of the recursion fails,
     and under the guard of @('old'):
     </p>

     @({
       (implies (and old-guard<x1,...,xn>
                     (not test<x1,...,xn>))
                (domain nonrec<x1,...,xn>))
     })

     <p>
     where @('old-guard<x1,...,xn>') is the guard term of @('old').
     </p>

     <p>
     This applicability condition is present iff
     the functions generated by @('tailrec') are guard-verified
     (which is determined by the @(':verify-guards') input of @('tailrec'))
     and the @(':variant') input of @('tailrec') is @(':monoid-alt').
     </p>

     </blockquote>

   <p>
   When present, @(':combine-left-identity') and @(':combine-right-identity'),
   together with
   either @(':combine-associativity') or @(':combine-associativity-uncond')
   (one of them is always present),
   and together with
   either @(':domain-of-combine') or @(':domain-of-combine-uncond')
   (one of them is always present),
   mean that the domain has the algebraic structure of a monoid,
   with the combination operator as the binary operator
   and with the base value of the recursion as identity.
   When @(':combine-left-identity') and @(':combine-right-identity') are absent,
   the domain has the algebraic structure of a semigroup.
   </p>

   <h3>
   Generated Functions and Theorems
   </h3>

   <p>
   @('new')
   </p>

     <blockquote>

     <p>
     Tail-recursive equivalent of @('old'):
     </p>

     @({
       ;; when the :variant input of tailrec is :monoid or :monoid-alt:
       (defun new (x1 ... xn r)
         (if test<x1,...,xn>
             r
           (new update-x1<x1,...,xn>
                ...
                update-xn<x1,...,xn>
                combine<r,nonrec<x1,...,xn>>)))

       ;; when the :variant input of tailrec is :assoc:
       (defun new (x1 ... xn r)
         (if test<x1,...,xn>
             combine<r,base<x1,...,xn>>
           (new update-x1<x1,...,xn>
                ...
                update-xn<x1,...,xn>
                combine<r,nonrec<x1,...,xn>>)))
     })

     <p>
     The measure term and well-founded relation of @('new')
     are the same as @('old').
     </p>

     <p>
     The guard is @('(and old-guard<x1,...,xn> (domain r))'),
     where @('old-guard<x1,...,xn>') is the guard term of @('old').
     </p>

     </blockquote>

   <p>
   @('wrapper')
   </p>

     <blockquote>

     <p>
     Non-recursive wrapper of @('new'):
     </p>

     @({
       ;; when the :variant input of tailrec is :monoid or :monoid-alt:
       (defun wrapper (x1 ... xn)
         (new x1 ... xn base<x1,...,xn>))

       ;; when the :variant input tailrec is :assoc:
       (defun wrapper (x1 ... xn)
         (if test<x1,...,xn>
             base<x1,...,xn>
           (new update-x1<x1,...,xn>
                ...
                update-xn<x1,...,xn>
                nonrec<x1,...,xn>)))
     })

     <p>
     The guard is the same as @('old').
     </p>

     </blockquote>

   <p>
   @('old-to-wrapper')
   </p>

     <blockquote>

     <p>
     Theorem that relates @('old') to @('wrapper'):
     </p>

     @({
       (defthm old-to-wrapper
         (equal (old x1 ... xn)
                (wrapper x1 ... xn)))
     })

     </blockquote>")
