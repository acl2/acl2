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

(include-book "../../language/computation-states")
(include-book "../arrays")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-not-error-rules
  :short "Rules about things of certain types not being errors."

  (defruled not-errorp-when-scopep
    (implies (scopep x)
             (not (errorp x)))
    :enable (errorp scopep))

  (defruled not-errorp-when-scope-listp
    (implies (scope-listp x)
             (not (errorp x)))
    :enable errorp)

  (defruled not-errorp-when-schar-arrayp
    (implies (schar-arrayp x)
             (not (errorp x)))
    :enable (errorp schar-arrayp))

  (defruled not-errorp-when-uchar-arrayp
    (implies (uchar-arrayp x)
             (not (errorp x)))
    :enable (errorp uchar-arrayp))

  (defruled not-errorp-when-sshort-arrayp
    (implies (sshort-arrayp x)
             (not (errorp x)))
    :enable (errorp sshort-arrayp))

  (defruled not-errorp-when-ushort-arrayp
    (implies (ushort-arrayp x)
             (not (errorp x)))
    :enable (errorp ushort-arrayp))

  (defruled not-errorp-when-sint-arrayp
    (implies (sint-arrayp x)
             (not (errorp x)))
    :enable (errorp sint-arrayp))

  (defruled not-errorp-when-uint-arrayp
    (implies (uint-arrayp x)
             (not (errorp x)))
    :enable (errorp uint-arrayp))

  (defruled not-errorp-when-slong-arrayp
    (implies (slong-arrayp x)
             (not (errorp x)))
    :enable (errorp slong-arrayp))

  (defruled not-errorp-when-ulong-arrayp
    (implies (ulong-arrayp x)
             (not (errorp x)))
    :enable (errorp ulong-arrayp))

  (defruled not-errorp-when-sllong-arrayp
    (implies (sllong-arrayp x)
             (not (errorp x)))
    :enable (errorp sllong-arrayp))

  (defruled not-errorp-when-ullong-arrayp
    (implies (ullong-arrayp x)
             (not (errorp x)))
    :enable (errorp ullong-arrayp))

  (defruled not-errorp-when-booleanp
    (implies (booleanp x)
             (not (errorp x)))
    :enable errorp)

  (defval *atc-not-error-rules*
    '(;; proved above:
      not-errorp-when-scopep
      not-errorp-when-scope-listp
      not-errorp-when-schar-arrayp
      not-errorp-when-uchar-arrayp
      not-errorp-when-sshort-arrayp
      not-errorp-when-ushort-arrayp
      not-errorp-when-sint-arrayp
      not-errorp-when-uint-arrayp
      not-errorp-when-slong-arrayp
      not-errorp-when-ulong-arrayp
      not-errorp-when-sllong-arrayp
      not-errorp-when-ullong-arrayp
      not-errorp-when-booleanp
      ;; proved elsewhere:
      not-errorp-when-valuep
      not-errorp-when-value-listp
      not-errorp-when-compustatep)))
