; APT Partial Evaluation Transformation -- Reference Documentation
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/event-macros/xdoc-constructors" :dir :system)
(include-book "utilities/xdoc-constructors")
(include-book "parteval")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc parteval

  :parents (reference)

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
      the current version of this APT transformation is very simple,
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
      but does not change its parameters."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form-auto parteval)

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must
       be in logic mode,
       be defined,
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
       "Let @('old-body<x1,...,xn,y1,...,ym>') be the body of @('old').")))

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
       static and dynamic parameters can be intermixed in any way."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-thm-name nil)

    (xdoc::desc-apt-input-thm-enable
     nil
     (xdoc::p
      "If @('old') is recursive
       and @('new') is enabled (as determined by the @(':new-enable') input),
       then @(':thm-enable') cannot be @('t')."))

    (xdoc::desc-apt-input-verify-guards nil)

    (xdoc::evmac-input-print parteval)

    (xdoc::evmac-input-show-only parteval))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Specialized version of @('old'):")
     (xdoc::@code
      ";; when old is not recursive:"
      "(defun new (x1 ... xn)"
      "  old-body<x1,...,xn,c1,...,cm>)"
      ""
      ";; when old is recursive:"
      "(defun new (x1 ... xn)"
      "  (old x1 ... xn c1 ... cm))")
     (xdoc::p
      "The guard is @('old-guard<x1,...,xn,c1,...cm>')."))

    (xdoc::desc
     "@('old-to-new')"
     (xdoc::p
      "Theorem that relates @('old') to @('new'):")
     (xdoc::@code
      "(defthm old-to-new"
      "  (implies (and (equal y1 c1)"
      "                ..."
      "                (equal ym cm)"
      "           (equal (old x1 ... xn y1 ... ym)"
      "                  (new x1 ... xn)))")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-redundancy parteval)))
