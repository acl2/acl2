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

(defsection atc-exec-expr-call-or-asg-rules
  :short "Rules for @(tsee exec-expr-call-or-asg)."

  (defruled exec-expr-call-or-asg-when-call
    (implies (and (syntaxp (quotep e))
                  (equal (expr-kind e) :call)
                  (not (zp limit))
                  (equal val?+compst1
                         (exec-expr-call (expr-call->fun e)
                                         (expr-call->args e)
                                         compst
                                         fenv
                                         (1- limit)))
                  (equal val? (mv-nth 0 val?+compst1))
                  (equal compst1 (mv-nth 1 val?+compst1))
                  (value-optionp val?))
             (equal (exec-expr-call-or-asg e compst fenv limit)
                    compst1))
    :enable exec-expr-call-or-asg)

  (defruled exec-expr-call-or-asg-when-asg
    (implies (and (syntaxp (quotep e))
                  (not (equal (expr-kind e) :call))
                  (not (zp limit))
                  (compustatep compst))
             (equal (exec-expr-call-or-asg e compst fenv limit)
                    (exec-expr-asg e compst fenv (1- limit))))
    :enable exec-expr-call-or-asg)

  (defval *atc-exec-expr-call-or-asg-rules*
    '(exec-expr-call-or-asg-when-call
      exec-expr-call-or-asg-when-asg
      (:e expr-kind)
      (:e expr-call->fun)
      (:e expr-call->args))))
