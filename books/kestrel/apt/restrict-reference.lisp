; APT Domain Restriction Transformation -- Reference Documentation
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
(include-book "restrict")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc restrict

  :parents (reference)

  :short "APT domain restriction transformation:
          restrict the effective domain of a function."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Even though functions are total in ACL2
      (i.e. their domain is always the whole ACL2 universe of values),
      the guard of a function can be regarded as its effective domain
      (i.e. where it is well-defined).
      This transformation adds restrictions to the guard,
      and wraps the body with a test for the restrictions,
      which may enable further optimizations
      by taking advantage of the added restrictions."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form-auto restrict)

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
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

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-thm-name nil)

    (xdoc::desc-apt-input-thm-enable nil)

    (xdoc::desc-apt-input-non-executable nil)

    (xdoc::desc-apt-input-verify-guards nil)

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print restrict)

    (xdoc::evmac-input-show-only restrict))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    restrict

    (xdoc::desc
     "@(':restriction-of-rec-calls')"
     (xdoc::p
      "@('(lambda (x1 ... xn) restriction<x1,...,xn>)')
       is preserved across the recursive calls of @('old'):")
     (xdoc::codeblock
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
     (xdoc::codeblock
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
     (xdoc::codeblock
      "(booleanp restriction<x1,...,xn>)")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Domain-restricted version of @('old'):")
     (xdoc::codeblock
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
     (xdoc::codeblock
      "(defthm old-to-new"
      "  (implies restriction<x1,...,xn>"
      "           (equal (old x1 ... xn)"
      "                  (new x1 ... xn))))")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy restrict)))
