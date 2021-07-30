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
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dec-digit-char
  :parents (dec-digit-char-p)
  :short "Fixtype of decimal digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (std::deffixer dec-digit-char-fix
    :pred dec-digit-char-p
    :body-fix #\0
    :parents (dec-digit-char)
    :short "Fixer for @(tsee dec-digit-char).")

  (fty::deffixtype dec-digit-char
    :pred dec-digit-char-p
    :fix dec-digit-char-fix
    :equiv dec-digit-char-equiv
    :define t
    :forward t))
