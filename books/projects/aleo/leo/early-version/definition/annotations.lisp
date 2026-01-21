; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "identifiers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ annotations
  :parents (abstract-syntax)
  :short "Leo annotations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo supports annotations for function declarations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod annotation
  :short "Fixtype of Leo annotations."
  :long
  (xdoc::topstring
   (xdoc::p
    "An annotation consists of an annotation name,
     which is an identifier preceded by @('@')."))
  ((name identifier))
  :pred annotationp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist annotation-list
  :short "Fixtype of lists of Leo annotations."
  :elt-type annotation
  :true-listp t
  :elementp-of-nil nil
  :pred annotation-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult annotation-result
  :short "Fixtype of errors and Leo annotations."
  :ok annotation
  :pred annotation-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult annotation-list-result
  :short "Fixtype of errors and lists of Leo annotations."
  :ok annotation-list
  :pred annotation-list-resultp)
