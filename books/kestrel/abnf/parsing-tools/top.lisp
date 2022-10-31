; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "primitives-seq")
(include-book "primitives-defresult")
(include-book "generators")
(include-book "defdefparse")
(include-book "defdefparse-doc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parsing-tools
  :parents (abnf)
  :short "Some tools to build parsers for ABNF-defined languages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide some parsing primitives
     that may be useful as parts of larger parsers.
     We also provide some (very preliminary)
     parsing generation tools."))
  :order-subtopics t)
