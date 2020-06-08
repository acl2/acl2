; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "identifiers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ package-names
  :parents (syntax)
  :short "Java package names [JLS:6.5]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod package-name
  :short "Fixtype of package names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar rule for @('package-name') in [JLS:6.5] defines a package name
     as a dot-separated non-empty sequence of identifiers.")
   (xdoc::p
    "We formalize this as a list of identifiers,
     and we tag that (via @(tsee fty::defprod))
     so that it can be distinguished from other lists of identifiers."))
  ((identifiers identifier-list))
  :layout :list
  :tag :package-name
  :pred package-namep)
