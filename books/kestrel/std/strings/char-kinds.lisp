; Standard Strings Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "letter-chars")
(include-book "letter-digit-chars")
(include-book "letter-digit-dash-chars")
(include-book "letter-digit-uscore-chars")
(include-book "letter-digit-uscore-dollar-chars")
(include-book "letter-uscore-dollar-chars")
(include-book "nondigit-chars")
(include-book "printable-chars")
(include-book "ucletter-chars")
(include-book "lcletter-chars")
(include-book "ucletter-digit-chars")
(include-book "lcletter-digit-chars")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc character-kinds
  :parents (std/strings-extensions std/strings)
  :short "Predicates that characterize various kinds of characters,
          and lists of such characters.")
