; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/dynamic-semantics")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

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
