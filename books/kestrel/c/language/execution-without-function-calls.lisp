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

(include-book "dynamic-semantics")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ execution-without-function-calls
  :parents (dynamic-semantics)
  :short "Properties about execution without function calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that, when executing code without function calls,
     the function environment has no effect:
     execution gives the same results with different function environments."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-without-calls
  :short "Execution not involving function calls is
          independent from the function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We express this by saying that
     when the execution functions are applied to constructs
     (expressions, statements, etc.)
     that do not contain function calls,
     they always yield the same results
     given any two arbitrary function environments."))

  (defthm-exec-flag
    (defthm exec-expr-call-without-calls
      t
      :rule-classes nil
      :flag exec-expr-call)
    (defthm exec-expr-call-or-pure-without-calls
      (implies (expr-nocallsp e)
               (equal (exec-expr-call-or-pure e compst fenv limit)
                      (exec-expr-call-or-pure e compst fenv1 limit)))
      :rule-classes nil
      :flag exec-expr-call-or-pure)
    (defthm exec-expr-asg-without-calls
      (implies (expr-nocallsp e)
               (equal (exec-expr-asg e compst fenv limit)
                      (exec-expr-asg e compst fenv1 limit)))
      :rule-classes nil
      :flag exec-expr-asg)
    (defthm exec-expr-call-or-asg-without-calls
      (implies (expr-nocallsp e)
               (equal (exec-expr-call-or-asg e compst fenv limit)
                      (exec-expr-call-or-asg e compst fenv1 limit)))
      :rule-classes nil
      :flag exec-expr-call-or-asg)
    (defthm exec-fun-without-calls
      t
      :rule-classes nil
      :flag exec-fun)
    (defthm exec-stmt-without-calls
      (implies (stmt-nocallsp s)
               (equal (exec-stmt s compst fenv limit)
                      (exec-stmt s compst fenv1 limit)))
      :rule-classes nil
      :flag exec-stmt)
    (defthm exec-stmt-while-without-calls
      (implies (and (expr-nocallsp test)
                    (stmt-nocallsp body))
               (equal (exec-stmt-while test body compst fenv limit)
                      (exec-stmt-while test body compst fenv1 limit)))
      :rule-classes nil
      :flag exec-stmt-while)
    (defthm exec-initer-without-calls
      (implies (initer-nocallsp initer)
               (equal (exec-initer initer compst fenv limit)
                      (exec-initer initer compst fenv1 limit)))
      :rule-classes nil
      :flag exec-initer)
    (defthm exec-obj-declon-without-calls
      (implies (obj-declon-nocallsp declon)
               (equal (exec-obj-declon declon compst fenv limit)
                      (exec-obj-declon declon compst fenv1 limit)))
      :rule-classes nil
      :flag exec-obj-declon)
    (defthm exec-block-item-without-calls
      (implies (block-item-nocallsp item)
               (equal (exec-block-item item compst fenv limit)
                      (exec-block-item item compst fenv1 limit)))
      :rule-classes nil
      :flag exec-block-item)
    (defthm exec-block-item-list-without-calls
      (implies (block-item-list-nocallsp items)
               (equal (exec-block-item-list items compst fenv limit)
                      (exec-block-item-list items compst fenv1 limit)))
      :rule-classes nil
      :flag exec-block-item-list)
    :hints (("Goal"
             :in-theory (enable exec-expr-call
                                exec-expr-call-or-pure
                                exec-expr-asg
                                exec-expr-call-or-asg
                                exec-stmt
                                exec-stmt-while
                                exec-initer
                                exec-obj-declon
                                exec-block-item
                                exec-block-item-list
                                expr-nocallsp
                                expr-list-nocallsp
                                expr-option-nocallsp
                                initer-nocallsp
                                initer-option-nocallsp
                                obj-declon-nocallsp
                                stmt-nocallsp
                                obj-declon-nocallsp
                                block-item-nocallsp
                                block-item-list-nocallsp
                                expr-option-some->val
                                initer-option-some->val
                                obj-declon-to-ident+scspec+tyname+init)))))
