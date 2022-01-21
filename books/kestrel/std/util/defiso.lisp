; Standard Utilities Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmapping")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defiso-implementation
  :parents (defiso)
  :short "Implementation of @(tsee defiso)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We implement @(tsee defiso) as a thin wrapper of @(tsee defmapping).
     We also provide a programmatic interface
     to retrieve isomorphic mappings from the "
    (xdoc::seetopic "defmapping-table" "@('defmapping') table")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defiso-lookup ((name symbolp) (wrld plist-worldp))
  :returns (info? "A @(tsee maybe-defmapping-infop).")
  :verify-guards nil
  :short "Return the information for the @(tsee defiso) specified by name,
          or @('nil') if there is no @(tsee defiso) with that name."
  :long
  (xdoc::topstring-p
   "This is a wrapper of @(tsee defmapping-lookup)
    that makes sure that the mapping is an isomorphism,
    i.e. that it has
    both the @(':beta-of-alpha') and @(':alpha-of-beta') theorems.
    It causes an error if that is not the case.")
  (b* ((info (defmapping-lookup name wrld))
       ((when (not info)) nil)
       ((when (not (defmapping-info->beta-of-alpha info)))
        (raise "The mapping ~x0 does not have the :BETA-OF-ALPHA theorem."
               name))
       ((when (not (defmapping-info->alpha-of-beta info)))
        (raise "The mapping ~x0 does not have the :ALPHA-OF-BETA theorem."
               name)))
    info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defiso-macro-definition
  :short "Definition of the @(tsee defiso) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call @(tsee defmapping-fn),
     passing @('t') as
     both @(':beta-of-alpha-thm') and @(':alpha-of-beta-thm').
     Furthermore, we set the context to reference @(tsee defiso).")
   (xdoc::@def "defiso"))
  (defmacro defiso (&whole
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
                         t ; ALPHA-OF-BETA-THM
                         ',guard-thms
                         ',unconditional
                         ',thm-names
                         ',thm-enable
                         ',hints
                         ',print
                         ',show-only
                         ',call
                         (cons 'defiso ',name)
                         state)
                       :suppress-errors ,(not print))))
