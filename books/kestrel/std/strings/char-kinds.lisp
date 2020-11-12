; Standard Strings Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "letter-char-p")
;; (include-book "bin-digit-char-p")
;; (include-book "dec-digit-char-p")
;; (include-book "hex-digit-char-p")
;; (include-book "oct-digit-char-p")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc character-kinds
  :parents (std/strings-extensions std/strings)
  :short "Predicates that characterize various kinds of characters,
          and lists of such characters.")
