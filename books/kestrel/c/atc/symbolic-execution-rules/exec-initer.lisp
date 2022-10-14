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

(defsection atc-exec-initer-rules
  :short "Rules for @(tsee exec-initer)."

  (defruled exec-initer-when-single
    (implies (and (syntaxp (quotep initer))
                  (equal (initer-kind initer) :single)
                  (not (zp limit))
                  (equal expr (initer-single->get initer))
                  (equal val+compst1
                         (exec-expr-call-or-pure expr compst fenv (1- limit)))
                  (equal val (mv-nth 0 val+compst1))
                  (equal compst1 (mv-nth 1 val+compst1))
                  (valuep val))
             (equal (exec-initer initer compst fenv limit)
                    (mv (init-value-single val) compst1)))
    :enable exec-initer)

  (defval *atc-exec-initer-rules*
    '(exec-initer-when-single
      (:e initer-kind)
      (:e initer-single->get))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-init-value-to-value-rules
  :short "Rules for @(tsee init-value-to-value)."

  (defruled init-value-to-value-when-single
    (implies (and (valuep val)
                  (equal (type-of-value val)
                         type))
             (equal (init-value-to-value type (init-value-single val))
                    val))
    :enable init-value-to-value)

  (defval *atc-init-value-to-value-rules*
    '(init-value-to-value-when-single)))
