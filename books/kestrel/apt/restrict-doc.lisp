; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "utilities/xdoc-constructors")

; (depends-on "design-notes/restrict.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *restrict-design-notes*
  (xdoc::&& "@('restrict') "
            (xdoc::ahref "res/kestrel-apt-design-notes/restrict.pdf"
                         "design notes")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc restrict

  :parents (apt)

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
      by taking advantage of the added restrictions.")

    (xdoc::apt-design-notes-ref restrict))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(restrict old"
     "          restriction"
     "          :undefined          ; default :undefined"
     "          :new-name           ; default :auto"
     "          :new-enable         ; default :auto"
     "          :old-to-new-name    ; default from table"
     "          :old-to-new-enable  ; default from table"
     "          :new-to-old-name    ; default from table"
     "          :new-to-old-enable  ; default from table"
     "          :verify-guards      ; default :auto"
     "          :hints              ; default nil"
     "          :print              ; default :result"
     "          :show-only          ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must
       be in logic mode,
       be " (xdoc::seetopic "acl2::function-definedness" "defined") ",
       have at least one formal argument,
       return a non-" (xdoc::seetopic "mv" "multiple") " value, and
       have no input or output " (xdoc::seetopic "acl2::stobj" "stobjs") "."
      "If @('old') is recursive, it must
       be singly (not mutually) recursive and
       not have a @(':?') measure (see @(':measure') in @(tsee xargs)).
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
                   (old update1-x1<x1,...,xn,old>
                        ...
                        update1-xn<x1,...,xn,old>)
                   ...
                   (old updatem-x1<x1,...,xn,old>
                        ...
                        updatem-xn<x1,...,xn,old>)>
        })
        be the body of @('old'),
        where @('m') &gt; 0 is the number of recursive calls
        in the body of @('old')
        and each @('updatej-xi<x1,...,xn,old>') is
        the @('i')-th actual argument passed to the @('j')-th recursive call.
        Furthermore,
        let @('contextj<x1,...,xn,old>') be the context (i.e. controlling tests)
        in which the @('j')-th recursive call occurs.
        The dependency of @('updatej-xi<...,old>') and @('contextj<...,old>')
        on @('old') only applies to so-called `reflexive functions',
        i.e. functions that occur in their own termination theorem."))
     (xdoc::p
      "In the " *restrict-design-notes* ",
       @('old') is denoted by @($f$).
       When @('old') is not recursive,
       @('old-body<x1,...,xn>') is denoted by @($e(\\overline{x})$).
       When @('old') is recursive,
       the design notes use
       a single non-recursive branch @($b(\\overline{x})$)
       controlled by @($a(\\overline{x})$)
       and a single recursive branch
       @($c(\\overline{x},f(\\overline{d}(\\overline{x})))$)
       controlled by the negation of @($a(\\overline{x})$):
       this is a representative recursive structure,
       but the transformation handles
       multiple non-recursive and recursive branches,
       and also recursive functions that occur in their termination theorem;
       in this representative recursive structure,
       @('update-xi<x1,...,xn>') is denoted by @($d_i(\\overline{x})$)
       and @('context<x1,...,xn>') is denoted by
       the negation of @($a(\\overline{x})$)."))

    (xdoc::desc
     "@('restriction')"
     (xdoc::p
      "Denotes the restricting predicate for the domain of @('old'),
       i.e. the predicate that will be added to the guard
       and as the test that wraps the body.")
     (xdoc::p
      "The special value @(':guard') can be used to denote the guard predicate itself.")
     (xdoc::evmac-desc-term
      :free-vars "@('x1'), ..., @('xn')"
      :1res t
      :guard "the generated function is guard-verified
              (which is determined by the @(':verify-guards') input; see below)"
      :dont-call "@('old')")
     (xdoc::p
      "The term denotes the predicate @('(lambda (x1 ... xn) restriction)').")
     (xdoc::p
      "In order to highlight the dependence on @('x1'), ..., @('xn'),
       in the rest of this documentation page,
       @('restriction<x1,...,xn>') is used for @('restriction').")
     (xdoc::p
      "In the " *restrict-design-notes* ",
       @('(lambda (x1 ... xn) restriction<x1,...,xn>)') is denoted by @($R$)."))

    (xdoc::desc
     "@(':undefined') &mdash; default @(':undefined')"
     (xdoc::p
      "Denotes the value that the generated new function must return
       outside of the domain restriction.")
     (xdoc::evmac-desc-term
      :free-vars "@('x1'), ..., @('xn')"
      :1res t
      :guard nil
      :dont-call "@('old')")
     (xdoc::p
      "Even if the generated function is guard-verified
       (which is determined by the @(':verify-guards') input; see below),
       the term may call non-guard-verified functions.
       Since the term is governed by the negation of the guard
       (see the generated new function, below),
       the verification of its guards always succeeds trivially.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('undefined') be this term."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-old-to-new-name)

    (xdoc::desc-apt-input-old-to-new-enable)

    (xdoc::desc-apt-input-new-to-old-name)

    (xdoc::desc-apt-input-new-to-old-enable)

    (xdoc::desc-apt-input-verify-guards :plural-functions nil)

    (xdoc::evmac-input-hints)

    (xdoc::evmac-input-print restrict)

    (xdoc::evmac-input-show-only restrict))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    restrict

    (xdoc::evmac-appcond
     ":restriction-of-rec-calls"
     (xdoc::&&
      (xdoc::p
       "@('(lambda (x1 ... xn) restriction<x1,...,xn>)')
        is preserved across the recursive calls of @('old'):")
      (xdoc::codeblock
       "(implies restriction<x1,...,xn>"
       "         (and (implies context1<x1,...,xn,?f>"
       "                       restriction<update1-x1<x1,...,xn,?f>,"
       "                                   ...,"
       "                                   update1-xn<x1,...,xn,?f>>)"
       "              ..."
       "              (implies contextm<x1,...,xn,?f>"
       "                       restriction<updatem-x1<x1,...,xn,?f>,"
       "                                   ...,"
       "                                   updatem-xn<x1,...,xn,?f>>)))")
      (xdoc::p
       "where @('?f') is an @('n')-ary stub that replaces @('old')
        (this only applies to reflexive functions; see above)."))
     :design-notes *restrict-design-notes*
     :design-notes-appcond "@($\\mathit{Rd}$)"
     :presence "@('old') is recursive")

    (xdoc::evmac-appcond
     ":restriction-guard"
     (xdoc::&&
      (xdoc::p
       "The restricting predicate is well-defined (according to its guard)
        on every value in the guard of @('old'):")
      (xdoc::codeblock
       "(implies old-guard<x1,...,xn>"
       "         restriction-guard<x1,...,xn>)")
      (xdoc::p
       "where @('restriction-guard<x1,...,xn>') is
        the guard obligation of @('restriction<x1,...,xn>')."))
     :design-notes *restrict-design-notes*
     :design-notes-appcond "@($\\mathit{GR}$)"
     :presence "the generated function is guard-verified
                (which is determined by the @(':verify-guards') input;
                see above)"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Domain-restricted version of @('old'):")
     (xdoc::codeblock
      ";; when old is not recursive:"
      "(defun new (x1 ... xn)"
      "  (if (mbt$ restriction<x1,...,xn>)"
      "      old-body<x1,...,xn>"
      "    undefined))"
      ""
      ";; when old is recursive:"
      "(defun new (x1 ... xn)"
      "  (if (mbt$ restriction<x1,...,xn>)"
      "      old-body<x1,...,xn,"
      "               (new update1-x1<x1,...,xn,new>"
      "                    ..."
      "                    update1-xn<x1,...,xn,new>)"
      "               ..."
      "               (new updatem-x1<x1,...,xn,new>"
      "                    ..."
      "                    updatem-xn<x1,...,xn,new>)>"
      "    undefined))")
     (xdoc::p
      "If @('old') is recursive,
       the measure term and well-founded relation of @('new')
       are the same as @('old').")
     (xdoc::p
      "The guard is @('(and old-guard<x1,...,xn> restriction<x1,...,xn>)').")
     (xdoc::p
      "Since the restriction test follows from the guard,
       the test is wrapped by @(tsee mbt$).
       The use of @(tsee mbt$), as opposed to @(tsee mbt),
       avoids requiring @('restriction') to be boolean-valued.")
     (xdoc::p
      "In the " *restrict-design-notes* ",
       @('new') is denoted by @($f'$)."))

    (xdoc::desc
     "@('old-to-new')"
     (xdoc::p
      "Theorem that relates @('old') to @('new'):")
     (xdoc::codeblock
      "(defthm old-to-new"
      "  (implies restriction<x1,...,xn>"
      "           (equal (old x1 ... xn)"
      "                  (new x1 ... xn))))")
     (xdoc::p
      "In the " *restrict-design-notes* ",
       @('old-to-new') is denoted by @($\\mathit{ff}'$)."))

    (xdoc::desc
     "@('new-to-old')"
     (xdoc::p
      "Theorem that relates @('new') to @('old'):")
     (xdoc::codeblock
      "(defthm new-to-old"
      "  (implies restriction<x1,...,xn>"
      "           (equal (new x1 ... xn)"
      "                  (old x1 ... xn))))")
     (xdoc::p
      "In the " *restrict-design-notes* ",
       @('new-to-old') is denoted by @($f'f$)."))

    (xdoc::p
     "A theory invariant is also generated to prevent
      both @('new-to-old') and @('old-to-new')
      from being enabled at the same time."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy restrict)))
