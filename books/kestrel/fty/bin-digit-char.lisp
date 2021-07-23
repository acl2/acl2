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
(include-book "std/strings/binary" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bin-digit-char
  :short "Fixtype of binary digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a type introduced by @(tsee fty::deffixtype)."))

  (std::deffixer bin-digit-char-fix
    :pred bin-digit-char-p
    :body-fix #\0
    :parents (bin-digit-char)
    :short "Fixer for @(tsee bin-digit-char).")

  (fty::deffixtype bin-digit-char
    :pred bin-digit-char-p
    :fix bin-digit-char-fix
    :equiv bin-digit-char-equiv
    :define t
    :forward t))
