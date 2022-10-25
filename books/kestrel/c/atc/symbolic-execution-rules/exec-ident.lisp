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

(include-book "../execution")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-ident-rules
  :short "Rules for executing identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use a binding hypothesis to read the variable's value,
     and we rewrite @(tsee exec-ident) differently
     based on whether the value is an array or not."))

  (defruled exec-ident-open
    (implies (equal val (read-var id compst))
             (equal (exec-ident id compst)
                    (if (value-case val :array)
                        (value-pointer (objdesign-variable id)
                                       (value-array->elemtype val))
                      val)))
    :enable (exec-ident value-kind errorp))

  (defval *atc-exec-ident-rules*
    '(exec-ident-open)))
