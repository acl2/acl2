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

(defsection atc-exec-fun-rules
  :short "Rules for @(tsee exec-fun)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proofs generated by ATC are modularized
     so that there is one theorem per non-recursive target function.
     So we generally do not expand calls of @(tsee exec-fun),
     except in the theorem for the function in question.
     We rely on the fact that the correctness theorems
     for the functions called by the function in question
     come after the following rule in the ACL2 history
     (because they are generated by ATC as part of the generated events),
     and thus take precedence over this rule:
     in other words, given theorems for the called functions,
     this rule is expected to apply only on the function in question,
     i.e. the one whose correctness theorem is being proved.
     Note that these theorems are generated only for non-recursive functions;
     the recursive functions represent loops,
     and their correctness theorems do not involve @(tsee exec-fun)."))

  (defruled exec-fun-open
    (implies (and (not (zp limit))
                  (equal info (fun-env-lookup fun fenv))
                  info
                  (equal scope (init-scope (fun-info->params info) args))
                  (scopep scope)
                  (equal val?+compst1
                         (exec-block-item-list (fun-info->body info)
                                               (push-frame (make-frame
                                                            :function fun
                                                            :scopes (list
                                                                     scope))
                                                           compst)
                                    fenv
                                    (1- limit)))
                  (equal val? (mv-nth 0 val?+compst1))
                  (equal compst1 (mv-nth 1 val?+compst1))
                  (value-optionp val?)
                  (equal (type-of-value-option val?)
                         (tyname-to-type (fun-info->result info))))
             (equal (exec-fun fun args compst fenv limit)
                    (mv val? (pop-frame compst1))))
    :enable exec-fun)

  (defval *atc-exec-fun-rules*
    '(exec-fun-open
      (:e fun-info->params)
      (:e fun-info->result)
      (:e fun-info->body))))
