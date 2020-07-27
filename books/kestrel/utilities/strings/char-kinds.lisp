; String Utilities
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alpha-digit-chars")
(include-book "alpha-digit-dash-chars")
(include-book "alpha-digit-uscore-dollar-chars")
(include-book "alpha-uscore-dollar-chars")
(include-book "nondigit-chars")
(include-book "printable-chars")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc character-kinds
  :parents (string-utilities)
  :short "Predicates that characterize various kinds of characters,
          and true lists thereof.")
