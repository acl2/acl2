; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../integer-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-sint-from-boolean
  :short "Rules about @(tsee sint-from-boolean."
  :long
  (xdoc::topstring
   (xdoc::p
    "We expand @(tsee sint-from-boolean),
     because it is really just an abbreviation.
     In fact, we want to expose its @(tsee if) structure
     in the symbolic execution."))

  (defval *atc-sint-from-boolean*
    '(sint-from-boolean)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-boolean-from-sint
  :short "Rules about @(tsee boolean-from-sint)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also have two rules to simplify applications of
     @(tsee boolean-from-sint) to @('(sint 0)') and @('(sint 1)').
     These applications appear during symbolic execution,
     because in C certain ``boolean'' expressions produce those @('int') values,
     and @(tsee boolean-from-sint) is used to turn those into ACL2 booleans,
     which are uses in @(tsee if)s,
     and thus we clearly want to simplify those application
     to @('t') and @('nil'), which further simplifies the @(tsee if)s."))

  (defruled boolean-from-sint-of-0
    (equal (boolean-from-sint (sint 0)) nil))

  (defruled boolean-from-sint-of-1
    (equal (boolean-from-sint (sint 1)) t))

  (defval *atc-boolean-from-sint*
    '(boolean-from-sint-of-0
      boolean-from-sint-of-1)))
