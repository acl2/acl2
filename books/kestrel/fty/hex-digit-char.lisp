; FTY Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/hex" :dir :system)
(include-book "std/util/deffixer" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hex-digit-char
  :parents (hex-digit-char-p)
  :short "Fixtype of hexadecimal digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (std::deffixer hex-digit-char-fix
    :pred hex-digit-char-p
    :body-fix #\0
    :parents (hex-digit-char)
    :short "Fixer for @(tsee hex-digit-char).")

  (fty::deffixtype hex-digit-char
    :pred hex-digit-char-p
    :fix hex-digit-char-fix
    :equiv hex-digit-char-equiv
    :define t
    :forward t))
