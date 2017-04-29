; SOFT ('Second-Order Functions and Theorems') -- Package
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file defines a package for SOFT ('Second-Order Functions and Theorems').

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "SOFT" (append *std-pkg-symbols*
                       '(body
                         defchoose-body
                         defchoose-bound-vars
                         defchoose-strengthen
                         defun-sk-check
                         defun-sk-info->bound-vars
                         defun-sk-info->matrix
                         defun-sk-info->quantifier
                         defun-sk-info->rewrite-kind
                         defun-sk-info->rewrite-name
                         defun-sk-info->strengthen
                         defun-sk-info->witness
                         defun-sk-quantifier-p
                         fargs
                         flambdap
                         fn-symb
                         formals
                         lambda-body
                         lambda-formals
                         make-lambda
                         measure
                         o<
                         recursivep
                         restrict-alist
                         strip-keyword-list
                         variablep
                         well-founded-relation)))
