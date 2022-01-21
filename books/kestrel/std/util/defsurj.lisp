; Standard Utilities Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmapping")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defsurj-implementation
  :parents (defsurj)
  :short "Implementation of @(tsee defsurj)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We implement @(tsee defsurj) as a thin wrapper of @(tsee defmapping).
     We also provide a programmatic interface
     to retrieve surjective mappings from the "
    (xdoc::seetopic "defmapping-table" "@('defmapping') table")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defsurj-lookup ((name symbolp) (wrld plist-worldp))
  :returns (info? "A @(tsee maybe-defmapping-infop).")
  :verify-guards nil
  :short "Return the information for the @(tsee defsurj) specified by name,
          or @('nil') if there is no @(tsee defsurj) with that name."
  :long
  (xdoc::topstring-p
   "This is a wrapper of @(tsee defmapping-lookup)
    that makes sure that the @($\\alpha$) conversion is a surjection
    (and also that the right inverse @($\\beta$) conversion is an injection),
    i.e. that it has the @(':alpha-of-beta') theorem.
    It causes an error if that is not the case.")
  (b* ((info (defmapping-lookup name wrld))
       ((when (not info)) nil)
       ((when (not (defmapping-info->alpha-of-beta info)))
        (raise "The mapping ~x0 does not have the :ALPHA-OF-BETA theorem."
               name)))
    info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defsurj-macro-definition
  :short "Definition of the @(tsee defsurj) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call @(tsee defmapping-fn),
     passing @('t') as @(':alpha-of-beta-thm')
     and @('nil') as @(':beta-of-alpha-thm').
     Furthermore, we set the context to reference @(tsee defsurj).")
   (xdoc::@def "defsurj"))
  (defmacro defsurj (&whole
                     call
                     ;; mandatory inputs:
                     name
                     doma
                     domb
                     alpha
                     beta
                     ;; optional inputs:
                     &key
                     (unconditional 'nil)
                     (guard-thms 't)
                     (thm-names 'nil)
                     (thm-enable 'nil)
                     (hints 'nil)
                     (print ':result)
                     (show-only 'nil))
    `(make-event-terse (defmapping-fn
                         ',name
                         ',doma
                         ',domb
                         ',alpha
                         ',beta
                         nil ; BETA-OF-ALPHA-THM
                         t ; ALPHA-OF-BETA-THM
                         ',guard-thms
                         ',unconditional
                         ',thm-names
                         ',thm-enable
                         ',hints
                         ',print
                         ',show-only
                         ',call
                         (cons 'defsurj ',name)
                         state)
                       :suppress-errors ,(not print))))
