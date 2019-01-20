; Event Macros -- XDOC Constructors
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ xdoc::evmac-constructors
  :parents (event-macros xdoc::constructors)
  :short "Utilities to construct <see topic='@(url xdoc)'>XDOC</see> strings
          to document <see topic='@(url event-macros)'>event macros</see>."
  :long
  (xdoc::topapp
   (xdoc::p
    "The @('xdoc::evmac-section-...') utilities construct level-3 sections.
     They are relatively thin wrappers,
     which precede their arguments with specific level-3 headings."))
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-intro
  :short "Construct the introduction section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::def "xdoc::evmac-section-intro"))
  (defmacro xdoc::evmac-section-intro (&rest content)
    `(xdoc::app
      (xdoc::h3 "Introduction")
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-form
  :short "Construct the general form section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::def "xdoc::evmac-section-form"))
  (defmacro xdoc::evmac-section-form (&rest content)
    `(xdoc::app
      (xdoc::h3 "General Form")
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-inputs
  :short "Construct the inputs section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::def "xdoc::evmac-section-inputs"))
  (defmacro xdoc::evmac-section-inputs (&rest content)
    `(xdoc::app
      (xdoc::h3 "Inputs")
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-appconds
  :short "Construct the applicability conditions section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::def "xdoc::evmac-section-appconds"))
  (defmacro xdoc::evmac-section-appconds (&rest content)
    `(xdoc::app
      (xdoc::h3 "Applicability Conditions")
      ,@content)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::evmac-section-generated
  :short "Construct the generated function(s) and theorem(s) section
          of the reference documentation of an event macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "The two parameters indicate how many functions and theorems are listed
     (none, one, more than one).
     These are used to customize the section title.")
   (xdoc::def "xdoc::evmac-section-generated"))
  (defmacro xdoc::evmac-section-generated (fns thms &rest content)
    (declare (xargs :guard (and (member-eq fns '(:none :one :many))
                                (member-eq thms '(:none :one :many))
                                (not (and (eq fns :none)
                                          (eq thms :none))))))
    (b* ((fn-word (if (eq fns :many) "Functions" "Function"))
         (thm-word (if (eq thms :many) "Theorems" "Theorem"))
         (title (cond ((eq fns :none) (concatenate 'string
                                                   "Generated "
                                                   thm-word))
                      ((eq thms :none) (concatenate 'string
                                                    "Generated "
                                                    fn-word))
                      (t (concatenate 'string
                                      "Generated "
                                      fn-word
                                      " and "
                                      thm-word)))))
      `(xdoc::app (xdoc::h3 ,title)
                  ,@content))))
