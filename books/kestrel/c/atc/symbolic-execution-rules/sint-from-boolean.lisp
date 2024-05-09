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

(include-book "../test-star")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-sint-from-boolean-rules
  :short "Rules about @(tsee sint-from-boolean)."

  (defruled sint-from-boolean-when-true
    (implies x
             (equal (sint-from-boolean x)
                    (sint-from-integer 1))))

  (defruled sint-from-boolean-when-true-test*
    (implies (test* x)
             (equal (sint-from-boolean x)
                    (sint-from-integer 1)))
    :enable test*)

  (defruled sint-from-boolean-when-false
    (implies (not x)
             (equal (sint-from-boolean x)
                    (sint-from-integer 0))))

  (defruled sint-from-boolean-when-false-test*
    (implies (test* (not x))
             (equal (sint-from-boolean x)
                    (sint-from-integer 0)))
    :enable test*))
