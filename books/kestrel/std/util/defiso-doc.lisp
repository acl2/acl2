; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defiso
  :parents (std::std/util-extensions std/util defmapping)
  :short "Establish an isomorphic mapping between two domains."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(tsee defmapping) where
     the @(':beta-of-alpha-thm') and @(':alpha-of-beta-thm') inputs are @('t').
     See the documentation of @(tsee defmapping).")))
