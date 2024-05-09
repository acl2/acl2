; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../representation/integer-operations")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-sint-from-boolean
  :short "Rules about @(tsee sint-from-boolean)."
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
    "We also have two rules
     to simplify applications of @(tsee boolean-from-sint)
     to @('(sint-from-integer 0)') and @('(sint-from-integer 1)').
     These applications appear during symbolic execution,
     because in C certain ``boolean'' expressions produce those @('int') values,
     and @(tsee boolean-from-sint) is used to turn those into ACL2 booleans,
     which are uses in @(tsee if)s,
     and thus we clearly want to simplify those application
     to @('t') and @('nil'), which further simplifies the @(tsee if)s."))

  (defruled boolean-from-sint-of-0
    (equal (boolean-from-sint (sint-from-integer 0)) nil))

  (defruled boolean-from-sint-of-1
    (equal (boolean-from-sint (sint-from-integer 1)) t))

  (defval *atc-boolean-from-sint*
    '(boolean-from-sint-of-0
      boolean-from-sint-of-1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-lognot-sint-rules
  :short "Rules about @(tsee lognot) applied to the signed integer 0 or 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "We have two rules
     to simplify applications of @(tsee lognot-sint)
     to @('(sint-from-integer 0)') and @('(sint-from-integer 1)').
     Terms of this form may arise in the process of simplifying
     C non-strict expressions involving @('&&') and @('||')."))

  (defruled lognot-sint-of-0
    (equal (lognot-sint (sint-from-integer 0))
           (sint-from-integer 1)))

  (defruled lognot-sint-of-1
    (equal (lognot-sint (sint-from-integer 1))
           (sint-from-integer 0)))

  (defval *atc-lognot-sint-rules*
    '(lognot-sint-of-0
      lognot-sint-of-1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-boolean-fron/to-sint-rules
  :short "Rules about the interaction of
          @(tsee boolean-from-sint) and @(tsee sint-from-boolean)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are actually not used in the old-style big symbolic execution,
     but rather in the new-style modular compositional proofs."))

  (defruled boolean-from-sint-of-sint-from-boolean
    (implies (booleanp x)
             (equal (boolean-from-sint (sint-from-boolean x))
                    x))
    :enable (sint-from-boolean
             boolean-from-sint)))
