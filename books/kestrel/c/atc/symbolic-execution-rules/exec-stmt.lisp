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

(defsection atc-exec-stmt-rules
  :short "Rules for @(tsee exec-stmt)."

  (defruled exec-stmt-when-compound
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :compound)
                  (not (zp limit))
                  (equal val?+compst1
                         (exec-block-item-list (stmt-compound->items s)
                                               (enter-scope compst)
                                               fenv
                                               (1- limit)))
                  (equal val? (mv-nth 0 val?+compst1))
                  (equal compst1 (mv-nth 1 val?+compst1))
                  (value-optionp val?))
             (equal (exec-stmt s compst fenv limit)
                    (mv val? (exit-scope compst1))))
    :enable exec-stmt)

  (defruled exec-stmt-when-expr
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :expr)
                  (not (zp limit))
                  (equal compst1
                         (exec-expr-call-or-asg (stmt-expr->get s)
                                                compst
                                                fenv
                                                (1- limit)))
                  (compustatep compst1))
             (equal (exec-stmt s compst fenv limit)
                    (mv nil compst1)))
    :enable exec-stmt)

  (defruled exec-stmt-when-if
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :if)
                  (not (zp limit))
                  (compustatep compst)
                  (equal arg1 (exec-expr-pure (stmt-if->test s) compst))
                  (valuep arg1)
                  (equal test (test-value arg1))
                  (booleanp test))
             (equal (exec-stmt s compst fenv limit)
                    (if test
                        (exec-stmt (stmt-if->then s) compst fenv (1- limit))
                      (mv nil compst))))
    :enable exec-stmt)

  (defruled exec-stmt-when-ifelse
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :ifelse)
                  (not (zp limit))
                  (equal arg1 (exec-expr-pure (stmt-ifelse->test s) compst))
                  (valuep arg1)
                  (equal test (test-value arg1))
                  (booleanp test))
             (equal (exec-stmt s compst fenv limit)
                    (if test
                        (exec-stmt (stmt-ifelse->then s) compst fenv (1- limit))
                      (exec-stmt (stmt-ifelse->else s) compst fenv (1- limit)))))
    :enable exec-stmt)

  (defruled exec-stmt-when-while
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :while)
                  (not (zp limit)))
             (equal (exec-stmt s compst fenv limit)
                    (exec-stmt-while (stmt-while->test s)
                                     (stmt-while->body s)
                                     compst
                                     fenv
                                     (1- limit))))
    :enable exec-stmt)

  (defruled exec-stmt-when-return
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :return)
                  (not (zp limit))
                  (equal e (stmt-return->value s))
                  e
                  (equal val+compst1
                         (exec-expr-call-or-pure e compst fenv (1- limit)))
                  (equal val (mv-nth 0 val+compst1))
                  (equal compst1 (mv-nth 1 val+compst1))
                  (valuep val))
             (equal (exec-stmt s compst fenv limit)
                    (mv val compst1)))
    :enable exec-stmt)

  (defval *atc-exec-stmt-rules*
    '(exec-stmt-when-compound
      exec-stmt-when-expr
      exec-stmt-when-if
      exec-stmt-when-ifelse
      exec-stmt-when-while
      exec-stmt-when-return
      (:e stmt-kind)
      (:e stmt-compound->items)
      (:e stmt-expr->get)
      (:e stmt-if->test)
      (:e stmt-if->then)
      (:e stmt-ifelse->test)
      (:e stmt-ifelse->then)
      (:e stmt-ifelse->else)
      (:e stmt-while->test)
      (:e stmt-while->body)
      (:e stmt-return->value))))
