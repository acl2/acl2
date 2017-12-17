; SOFT (Second-Order Functions and Theorems) -- Package
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "SOFT" (append *std-pkg-symbols*
                       '(body
                         control-screen-output
                         cw-event
                         defchoose-body
                         defchoose-bound-vars
                         defchoose-strengthen
                         defpun
                         defun-sk-check
                         defun-sk-info->bound-vars
                         defun-sk-info->matrix
                         defun-sk-info->quantifier
                         defun-sk-info->rewrite-kind
                         defun-sk-info->rewrite-name
                         defun-sk-info->strengthen
                         defun-sk-info->witness
                         defun-sk-quantifier-p
                         er-soft+
                         fail-event
                         fargs
                         flambdap
                         fn-symb
                         formals
                         function-symbol-listp
                         guard-verified-p
                         impossible
                         keywords-of-keyword-value-list
                         lambda-body
                         lambda-formals
                         make-event-terse
                         make-lambda
                         maybe-msgp
                         measure
                         o<
                         pseudo-event-formp
                         pseudo-event-form-listp
                         recursivep
                         remove-keyword
                         restore-output
                         restore-output?
                         restrict-alist
                         strip-keyword-list
                         symbol-symbol-alistp
                         ubody
                         variablep
                         well-founded-relation)))
