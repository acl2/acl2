; Top file for strings-light library
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "length")
(include-book "downcase")
(include-book "upcase")
(include-book "split-chars")
(include-book "split-chars-repeatedly")
(include-book "split-string")
(include-book "split-string-repeatedly")
(include-book "split-string-last")
(include-book "reverse")
(include-book "decimal-digits")
(include-book "parse-binary-digits")
(include-book "parse-decimal-digits")
(include-book "string-ends-withp")
(include-book "string-starts-withp")
(include-book "add-prefix-to-strings")
(include-book "strip-prefix-from-string")
(include-book "strip-suffix-from-string")
(include-book "strip-suffix-from-strings") ; or move to typed-lists-light
(include-book "strcar")
(include-book "strcdr")
(include-book "strnthcdr")
(include-book "subseq")
(include-book "strings-starting-with")
