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

(defxdoc+ definj-implementation
  :parents (definj)
  :short "Implementation of @(tsee definj)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We implement @(tsee definj) as a thin wrapper of @(tsee defmapping).
     We also provide a programmatic interface
     to retrieve injective mappings from the "
    (xdoc::seetopic "defmapping-table" "@('defmapping') table")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definj-lookup ((name symbolp) (wrld plist-worldp))
  :returns (info? "A @(tsee maybe-defmapping-infop).")
  :verify-guards nil
  :short "Return the information for the @(tsee definj) specified by name,
          or @('nil') if there is no @(tsee definj) with that name."
  :long
  (xdoc::topstring-p
   "This is a wrapper of @(tsee defmapping-lookup)
    that makes sure that the @($\\alpha$) conversion is an injection
    (and also that the left inverse @($\\beta$) conversion is a surjection),
    i.e. that it has the @(':beta-of-alpha') theorem.
    It causes an error if that is not the case.")
  (b* ((info (defmapping-lookup name wrld))
       ((when (not info)) nil)
       ((when (not (defmapping-info->beta-of-alpha info)))
        (raise "The mapping ~x0 does not have the :BETA-OF-ALPHA theorem."
               name)))
    info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection definj-macro-definition
  :short "Definition of the @(tsee definj) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call @(tsee defmapping-fn),
     passing @('t') as @(':alpha-of-beta-thm')
     and @('nil') as @(':beta-of-alpha-thm').
     Furthermore, we set the context to reference @(tsee definj).")
   (xdoc::@def "definj"))
  (defmacro definj (&whole
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
                         t ; BETA-OF-ALPHA-THM
                         nil ; ALPHA-OF-BETA-THM
                         ',guard-thms
                         ',unconditional
                         ',thm-names
                         ',thm-enable
                         ',hints
                         ',print
                         ',show-only
                         ',call
                         (cons 'definj ',name)
                         state)
                       :suppress-errors ,(not print))))
