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
(include-book "std/strings/octal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection oct-digit-char
  :parents (oct-digit-char-p)
  :short "Fixtype of octal digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (std::deffixer oct-digit-char-fix
    :pred oct-digit-char-p
    :body-fix #\0
    :parents (oct-digit-char)
    :short "Fixer for @(tsee oct-digit-char).")

  (fty::deffixtype oct-digit-char
    :pred oct-digit-char-p
    :fix oct-digit-char-fix
    :equiv oct-digit-char-equiv
    :define t
    :forward t))
