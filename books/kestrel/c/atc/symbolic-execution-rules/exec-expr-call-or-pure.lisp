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

(defsection atc-exec-expr-call-or-pure-rules
  :short "Rules for @(tsee exec-expr-call-or-pure)."

  (defruled exec-expr-call-or-pure-when-pure
    (implies (and (syntaxp (quotep e))
                  (not (equal (expr-kind e) :call))
                  (not (zp limit))
                  (compustatep compst))
             (equal (exec-expr-call-or-pure e compst fenv limit)
                    (mv (exec-expr-pure e compst)
                        compst)))
    :enable exec-expr-call-or-pure)

  (defruled exec-expr-call-of-pure-when-call
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :call)
                  (not (zp limit)))
             (equal (exec-expr-call-or-pure e compst fenv limit)
                    (exec-expr-call (expr-call->fun e)
                                    (expr-call->args e)
                                    compst
                                    fenv
                                    (1- limit))))
    :enable exec-expr-call-or-pure)

  (defval *atc-exec-expr-call-or-pure-rules*
    '(exec-expr-call-or-pure-when-pure
      exec-expr-call-of-pure-when-call
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args))))
