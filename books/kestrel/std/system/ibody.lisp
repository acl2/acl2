; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ibody ((fn symbolp) (wrld plist-worldp))
  :returns (body "An untranslated term.")
  :mode :program
  :parents (std/system/function-queries)
  :short "Retrieve the untranslated body of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as introduced (hence the @('i') in the name) by the user."))
  (car (last (logical-defun fn wrld))))
