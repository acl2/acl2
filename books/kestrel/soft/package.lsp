; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "SOFT" (append *std-pkg-symbols*
                       '(*t*
                         arity+
                         body
                         control-screen-output
                         cw-event
                         defchoose-body
                         defchoose-bound-vars
                         defchoose-strengthen
                         defchoosep
                         definedp
                         defmacro+
                         defpun
                         defun-sk-bound-vars
                         defun-sk-definition-name
                         defun-sk-matrix
                         defun-sk-p
                         defun-sk-quantifier
                         defun-sk-quantifier-p
                         defun-sk-rewrite-kind
                         defun-sk-rewrite-name
                         defun-sk-strengthen
                         defun-sk-witness
                         defxdoc+
                         ensure-list-has-no-duplicates$
                         ensure-symbol-is-fresh-event-name$
                         ensure-value-is-boolean$
                         ensure-value-is-function-name$
                         ensure-value-is-symbol$
                         ensure-value-is-symbol-list$
                         er-soft+
                         evmac-input-print-p
                         evmac-prepare-proofs
                         evmac-process-input-print
                         evmac-process-input-show-only
                         fail-event
                         fargs
                         flambdap
                         fn-symb
                         formals
                         function-symbol-listp
                         fundef-enabledp
                         guard-verified-p
                         guard-verified-p+
                         impossible
                         irecursivep
                         keywords-of-keyword-value-list
                         lambda-body
                         lambda-formals
                         logicp
                         make-event-terse
                         make-lambda
                         maybe-msgp
                         maybe-pseudo-event-formp
                         measure
                         o<
                         packn-pos
                         pseudo-event-form-listp
                         pseudo-event-formp
                         recursivep
                         remove-keyword
                         restore-output
                         restore-output?
                         restrict-alist
                         run-when
                         strip-keyword-list
                         symbol-symbol-alistp
                         table-alist+
                         ubody
                         uguard
                         variablep
                         well-founded-relation
                         well-founded-relation+)))
