; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

; Based on deffold-reduce-doc.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defmake-self

  :parents (fold)

  :short "Defining ``make-self'' functions for fixtypes."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This macro automates the creation of ``make-self'' functions on fixtypes.
      A ``make-self'' function is one which takes a value of a particular
      fixtype and returns a standard constructor form which would evaluate to
      the input value.")
    (xdoc::p
     "The primary motivation for introducing such functions is to produce
      more legible forms which are consistent across different layouts."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defmake-self type"
     "              :parents    ...  ; no default"
     "              :short      ...  ; no default"
     "              :long       ...  ; no default"
     "              :print      ...  ; default :result"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('type')"
     (xdoc::p
      "The name of the type or clique for which to create the ``make-self''
       functions. ``Make-self'' functions will also be generated for all the
       necessary type dependencies."))

    (xdoc::desc
     (list
      "@(':parents')"
      "@(':short')"
      "@(':long')")
     (xdoc::p
      "These, if present, are added to the generated XDOC topic
       described in the Section `Generated Events' below."))

    (xdoc::desc
     "@(':print')"
     (xdoc::p
      "Controls how much information is printed. This is a @(see
       apt::print-specifier). On @('nil') or @(':error'), only error messages
       are printed. On @(':result') (the default) or @(':info'), the events to
       be submitted are printed, in addition to error messages. Finally, all
       information is printed under @(':all').")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('make-self-<clique-name>')"
     (xdoc::p
      "An XDOC topic whose name is obtained by adding,
       at the end of the symbol @('make-self-'),
       the name of the (possibly singleton) clique
       to which the @('type') input belongs.
       If any of the @(':parents'), @(':short'), or @(':long') inputs
       are provided, they are added to this XDOC topic.
       This XDOC topic is generated with @(tsee acl2::defxdoc+),
       with @(':order-topics t'),
       so that the other generated events (described below),
       which all have this XDOC topic as parent,
       are listed in order as subtopics."))

    (xdoc::desc
     "@('<type>-<make-self')"
     (xdoc::p
      "For each type @('<type>') in the same clique specified by the
       @('type') input, as well as all type dependencies,
       a ``make-self'' function for that type.")))))
