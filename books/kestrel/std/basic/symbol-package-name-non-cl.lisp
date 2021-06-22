; Standard Basic Library
;
; Copyright (C) 2017 Regents of the University of Texas
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-package-name-non-cl ((sym symbolp))
  :returns (pkg stringp)
  :enabled t
  :parents (std/basic-extensions std/basic)
  :short "The @(tsee symbol-package-name) of a symbol,
          but not @('\"COMMON-LISP\"')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is just @(tsee symbol-package-name),
     except that it never returns @('\"COMMON-LISP\"'):
     if the @(tsee symbol-package-name) is @('\"COMMON-LISP\"'),
     we return @('\"ACL2\"') instead.")
   (xdoc::p
    "Example:")
   (xdoc::codeblock
    "ACL2 !>(symbol-package-name-non-cl 'car)"
    "\"ACL2\""
    "ACL2 !>(symbol-package-name 'car)"
    "\"COMMON-LISP\""
    "ACL2 !>")
   (xdoc::p
    "This utility may be useful to obtain, from an existing symbol,
     a package name into whose package we want to intern a symbol
     for a new function name,
     which cannot be interned into the @('\"COMMON-LISP\"') package."))
  (fix-pkg (symbol-package-name sym)))
