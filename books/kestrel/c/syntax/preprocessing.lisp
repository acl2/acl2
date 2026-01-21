; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "external-preprocessing")
(include-book "preprocessor")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessing
  :parents (syntax-for-tools)
  :short "Preprocessing for our C syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide an interface to invoke external C preprocessors.")
   (xdoc::p
    "We have also just started developing our own C preprocessor.
     This is very much work in progress."))
  :order-subtopics (external-preprocessing
                    preprocessor))
