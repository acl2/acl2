; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "kestrel/std/util/deffixer" :dir :system)
(include-book "std/strings/hex" :dir :system)

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
