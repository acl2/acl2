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

; (depends-on "design-notes/parteval.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *parteval-design-notes*
  (xdoc::&& "@('parteval') "
            (xdoc::ahref "res/kestrel-apt-design-notes/parteval.pdf"
                         "design notes")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc parteval

  :parents (apt)

  :short "APT partial evaluation transformation:
          specialize a function by setting one or more parameters
          to specified constant values."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Partial evaluation is a well-known program transformation technique.
      This APT transformation realizes this technique in ACL2.
      Partial evaluation is a broad topic;
      the current version of this APT transformation is relatively simple,
      but will be extended in the future.")

    (xdoc::p
     "This partial evaluation transformation specializes an ACL2 function
      by setting some of its parameters to specified constant values,
      and eliminating such parameters from the function.
      In partial evaluation terminology,
      the parameters that are set to constant values are <i>static</i>,
      while the remaining parameters are <i>dynamic</i>.")

    (xdoc::p
     "This transformation is related to @(tsee restrict),
      which also specializes a function,
      but does not change its parameters.")

    (xdoc::p
     "The " *parteval-design-notes* ", which use "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "this notation")
     ", provide the mathematical concepts and template proofs
      upon which this transformation is based.
      These notes should be read alongside this reference documentation,
      which refers to them in some places."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(parteval old"
     "          static"
     "          :new-name       ; default :auto"
     "          :new-enable     ; default :auto"
     "          :thm-name       ; default :auto"
     "          :thm-enable     ; default t"
     "          :verify-guards  ; default :auto"
     "          :untranslate    ; default :nice"
     "          :print          ; default :result"
     "          :show-only      ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must
       be in logic mode,
       be " (xdoc::seetopic "acl2::function-definedness" "defined") ",
       return a non-<see topic='@(url mv)'>multiple</see> value, and
       have no input or output <see topic='@(url acl2::stobj)'>stobjs</see>.
       If the @(':verify-guards') input is @('t'),
       @('old') must be guard-verified.")
     (xdoc::p
      "In the rest of this documentation page:")
     (xdoc::ul
      (xdoc::li
       "Let @('x1'), ..., @('xn'), @('y1'), ..., @('ym') be
        the formal parameters of @('old'),
        where @('n') @($\\geq$) 0 and @('m') &gt; 0.")
      (xdoc::li
       "Let @('old-guard<x1,...,xn,y1,...,ym>') be the guard term of @('old').")
      (xdoc::li
       "Let @('old-body<x1,...,xn,y1,...,ym>') be the body of @('old')."))
     (xdoc::p
      "The current implementation distinguishes the following three cases:")
     (xdoc::ol
      (xdoc::li
       "@('old') is not recursive.
        In this case, let its body be
        @('old-body<x1,...,xn,y1,...,ym>').")
      (xdoc::li
       "@('old') is recursive,
        @('y1'), ..., @('ym') are unchanged in all the recursive calls,
        and @('old') does not occur in its termination theorem.
        In this case, let its body be"
       (xdoc::codeblock
        "old-body<x1,...,xn,y1,...,ym,"
        "         (old update1-x1<x1,...,xn,y1,...,ym>"
        "              ..."
        "              update1-xn<x1,...,xn,y1,...,ym>"
        "              y1 ... ym)"
        "         ..."
        "         (old updatep-x1<x1,...,xn,y1,...,ym>"
        "              ..."
        "              updatep-xn<x1,...,xn,y1,...,ym>"
        "              y1 ... ym)>"))
      (xdoc::li
       "@('old') is recursive but it does not satisfy
        some of the conditions in case 2 above."))
     (xdoc::p
      "In the " *parteval-design-notes* ",
       @('old') is denoted by @($f$)."))

    (xdoc::desc
     "@('static')"
     (xdoc::p
      "Specifies the static parameters of @('old'),
       along with the constant values to assign to these parameters.")
     (xdoc::p
      "It must be a non-empty list of doublets @('((y1 c1) ... (ym cm))').
       Each @('yj') must be a parameter of @('old').
       The @('y1'), ..., @('ym') must be all distinct.
       Each @('cj') must be a ground term
       that only calls logic-mode functions,
       that returns a non-<see topic='@(url mv)'>multiple</see> value,
       and that has no output <see topic='@(url acl2::stobj)'>stobjs</see>.
       If the generated function is guard-verified
       (which is determined by the @(':verify-guards') input; see below),
       then each @('cj') must only call guard-verified functions,
       except possibly in the @(':logic') subterms of @(tsee mbe)s
       and via @(tsee ec-call).
       Each @('cj') must not include any calls to @('old').")
     (xdoc::p
      "The transformation specializes @('old')
       by setting each @('yj') to the value of the term @('cj').")
     (xdoc::p
      "In this documentation page, for expository convenience,
       the static parameters @('y1'), ..., @('ym')
       come after the dynamic parameters @('x1'), ..., @('xn').
       However, this is not required:
       static and dynamic parameters can be intermixed in any way.")
     (xdoc::p
      "In the " *parteval-design-notes* ",
       @('cj') is denoted by @($\\widetilde{y}_j$),
       for @($1 \\leq j \\leq m$)."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-thm-name :never)

    (xdoc::desc-apt-input-thm-enable
     :never
     (xdoc::p
      "If @('old') has the form of case 3 above
       and @('new') is enabled (as determined by the @(':new-enable') input),
       then @(':thm-enable') cannot be @('t')."))

    (xdoc::desc-apt-input-verify-guards :plural-functions nil)

    (xdoc::desc-apt-input-untranslate)

    (xdoc::evmac-input-print parteval)

    (xdoc::evmac-input-show-only parteval))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Specialized version of @('old'),
       where cases 1, 2, and 3 refer to the description of @('old') above:")
     (xdoc::codeblock
      ";; case 1:"
      "(defun new (x1 ... xn)"
      "  old-body<x1,...,xn,c1,...,cm>)"
      ""
      ";; case 2:"
      "(defun new (x1 ... xn)"
      "  old-body<x1,...,xn,c1,...,cm,"
      "           (new update1-x1<x1,...,xn,c1,...,cm>"
      "                ..."
      "                update1-xn<x1,...,xn,c1,...,cm>)"
      "           ..."
      "           (new updatep-x1<x1,...,xn,c1,...,cm>"
      "                ..."
      "                updatep-xn<x1,...,xn,c1,...,cm>)>)"
      ""
      ";; case 3:"
      "(defun new (x1 ... xn)"
      "  (old x1 ... xn c1 ... cm))")
     (xdoc::p
      "The guard is @('old-guard<x1,...,xn,c1,...cm>').")
     (xdoc::p
      "In case 2, the measure is the same as @('old').")
     (xdoc::p
      "In case 3, the new function is not recursive.
       This is simple, preliminary approach;
       support for more forms of recursive functions (besides case 2)
       may be added in the future.")
     (xdoc::p
      "In the " *parteval-design-notes* ",
       @('new') is denoted by @($f'$)."))

    (xdoc::desc
     "@('old-to-new')"
     (xdoc::p
      "Theorem that relates @('old') to @('new'):")
     (xdoc::codeblock
      "(defthm old-to-new"
      "  (implies (and (equal y1 c1)"
      "                ..."
      "                (equal ym cm)"
      "           (equal (old x1 ... xn y1 ... ym)"
      "                  (new x1 ... xn)))")
     (xdoc::p
      "In the " *parteval-design-notes* ",
       @('old-to-new') is denoted by @($\\mathit{ff}'$).")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy parteval)))
