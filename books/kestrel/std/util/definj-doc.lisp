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

(defxdoc definj
  :parents (std::std/util-extensions std/util defmapping)
  :short "Establish an injective mapping between two domains."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(tsee defmapping) where
     the @(':beta-of-alpha-thm') input is @('t').
     See the documentation of @(tsee defmapping).")
   (xdoc::p
    "Here `injective' refers to the @($\\alpha$) conversion.
     Its left inverse conversion @($\\beta$) is surjective.")))
