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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-exec-expr-call-rules
  :short "Rules for @(tsee exec-expr-call)."

  (defruled exec-expr-call-open
    (implies (and (not (zp limit))
                  (equal vals (exec-expr-pure-list args compst))
                  (value-listp vals))
             (equal (exec-expr-call fun args compst fenv limit)
                    (exec-fun fun vals compst fenv (1- limit))))
    :enable exec-expr-call)

  (defval *atc-exec-expr-call-rules*
    '(exec-expr-call-open)))
