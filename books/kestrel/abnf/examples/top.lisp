; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "uri")
(include-book "http")
(include-book "imf")
(include-book "smtp")
(include-book "imap")
(include-book "json")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ examples
  :parents (abnf)
  :short "Some real-world examples of ABNF grammars."
  :long
  (xdoc::topstring-p
   "We take some real-world ABNF grammars,
    copied and pasted from official standards,
    and show that they are successfully processed by the "
   (xdoc::seetopic "grammar-parser" "parser")
   " and "
   (xdoc::seetopic "concrete-to-abstract-syntax" "abstractor")
   ". We also demonstrate the use of
    some @(see operations) on these grammars.")
  :order-subtopics t)
