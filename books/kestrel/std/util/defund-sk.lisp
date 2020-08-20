; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defund-sk-implementation
  :parents (defund-sk)
  :short "Implementation of @(tsee defund-sk)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the inputs to @(tsee defun-sk) unchanged,
     and let @(tsee defun-sk) catch all the errors.
     We do no need to perform any input validation here.")
   (xdoc::p
    "However, in order to generate the event
     to disable the function and the rewrite rules,
     we need to retrieve some information from the inputs.
     In doing so, we can assume the inputs to be correct,
     because if they are not,
     the generated event will fail at the @(tsee defun-sk),
     without reaching the disabling event.")
   (xdoc::p
    "First, we need to find whether @(':constrain') is
     @('nil') (which is also the default), @('t'), or another symbol.
     If it is @('nil'), we disable the name of the function.
     Otherwise, we disable the definition rule,
     whose name is determined by the value of @(':constrain'):
     if @('t'), the name of the rule is
     the function name followed by @('-definition');
     otherwise, its value is the name of the definition rule.")
   (xdoc::p
    "Second, in order to disable the rewrite rule,
     we need to find out if there is a @(':thm-name') option.
     If there is, and its value is not @('nil'),
     that is the name of the rule to disable.
     If there is no @(':thm-name') option or its value is @('nil'),
     then we need to find the quantifier (universal or existential)
     in order to determine the rule name.
     If the quantifier is universal,
     the rule name is obtained by adding @('-necc') after the function name;
     if the quantifier is existential,
     the rule name is obtained by adding @('-suff') after the function name."))

  (defun defund-sk-names-to-disable (name rest)
    (declare (xargs :mode :program))
    (mv-let (erp dcls-and-body keyword-alist)
      (partition-rest-and-keyword-args rest *defun-sk-keywords*)
      (if erp
          (mv nil nil)
        (let* ((constrain (cdr (assoc-eq :constrain keyword-alist)))
               (thm-name (cdr (assoc-eq :thm-name keyword-alist)))
               (name/defrule
                (cond ((eq constrain nil) name)
                      ((eq constrain t) (add-suffix name "-DEFINITION"))
                      (t constrain)))
               (rwrule (or thm-name
                           (let* ((body (car (last dcls-and-body)))
                                  (quantifier (car body)))
                             (if (eq quantifier 'forall)
                                 (add-suffix name "-NECC")
                               (add-suffix name "-SUFF"))))))
          (mv name/defrule rwrule)))))

  (defun defund-sk-fn (name args rest)
    (declare (xargs :mode :program))
    (mv-let (name/defrule rwrule)
      (defund-sk-names-to-disable name rest)
      `(progn
         (defun-sk ,name ,args ,@rest)
         (in-theory (disable ,name/defrule ,rwrule)))))

  (defmacro defund-sk (name args &rest rest)
    `(make-event (defund-sk-fn ',name ',args ',rest))))
