; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/soft/defunvar" :dir :system)
(include-book "kestrel/soft/defun2" :dir :system)
(include-book "kestrel/soft/defund2" :dir :system)
(include-book "kestrel/soft/defun-sk2" :dir :system)
(include-book "kestrel/soft/defund-sk2" :dir :system)
(include-book "kestrel/std/system/pseudo-event-formp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains event generators that depend on SOFT.
; These are in this separate file so that event-generation.lisp
; does not have to depend on SOFT too.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (xdoc::set-default-parents event-macro-event-generators))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-generate-soft-defunvar ((name symbolp) (arity natp))
  :returns (event pseudo-event-formp)
  :short "Generate a SOFT function variable with specified name and arity."
  `(soft::defunvar ,name ,(repeat arity '*) => *))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-generate-soft-defun2 ((name symbolp)
                                    &key
                                    ((formals symbol-listp) ':absent)
                                    ((guard "A term.") 't)
                                    ((body "A term.") ':absent)
                                    ((verify-guards booleanp) ':absent)
                                    ((enable booleanp) ':absent)
                                    ((guard-hints true-listp) 'nil)
                                    ((measure "A term.") 'nil)
                                    ((hints true-listp) 'nil))
  :returns (mv (loc-event pseudo-event-formp)
               (event pseudo-event-formp))
  :short "Generate a SOFT @('defun2') or @('defund2') function definition
          with the specified attributes."
  (b* (((when (eq formals :absent))
        (raise "Internal error: :FORMALS not supplied.")
        (mv '(irrelevant) '(irrelevant)))
       ((when (eq body :absent))
        (raise "Internal error: :BODY not supplied.")
        (mv '(irrelevant) '(irrelevant)))
       ((when (eq verify-guards :absent))
        (raise "Internal error: :VERIFY-GUARDS not supplied.")
        (mv '(irrelevant) '(irrelevant)))
       ((when (eq enable :absent))
        (raise "Internal error: :ENABLE not supplied.")
        (mv '(irrelevant) '(irrelevant)))
       (macro (if enable 'soft::defun2 'soft::defund2))
       (measure-decl (and measure (list :measure measure)))
       (hints-decl (and measure hints (list :hints hints)))
       (guard-decl (list :guard guard))
       (verify-guards-decl (list :verify-guards verify-guards))
       (guard-hints-decl (and guard-hints (list :guard-hints guard-hints)))
       (loc-event `(local
                    (,macro ,name ,formals
                            (declare (xargs ,@measure-decl
                                            ,@hints-decl
                                            ,@guard-decl
                                            ,@verify-guards-decl
                                            ,@guard-hints-decl))
                            ,body)))
       (event `(,macro ,name ,formals
                       (declare (xargs ,@measure-decl
                                       ,@guard-decl
                                       ,@verify-guards-decl))
                       ,body)))
    (mv loc-event event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-generate-soft-defun-sk2 ((name symbolp)
                                       &key
                                       ((formals symbol-listp) ':absent)
                                       ((guard "A term.") 't)
                                       ((body "A term.") ':absent)
                                       ((verify-guards booleanp) ':absent)
                                       ((enable booleanp) ':absent)
                                       ((guard-hints true-listp) 'nil)
                                       ((rewrite "A term
                                                  or @(':direct')
                                                  or @(':default').")
                                        ':default))
  :returns (mv (loc-event pseudo-event-formp)
               (event pseudo-event-formp))
  :short "Generate a SOFT @('defun-sk2') or @('defund-sk2') function definition
          with the specified attributes."
  (b* (((when (eq formals :absent))
        (raise "Internal error: :FORMALS not supplied.")
        (mv '(irrelevant) '(irrelevant)))
       ((when (eq body :absent))
        (raise "Internal error: :BODY not supplied.")
        (mv '(irrelevant) '(irrelevant)))
       ((when (eq verify-guards :absent))
        (raise "Internal error: :VERIFY-GUARDS not supplied.")
        (mv '(irrelevant) '(irrelevant)))
       ((when (eq enable :absent))
        (raise "Internal error: :ENABLE not supplied.")
        (mv '(irrelevant) '(irrelevant)))
       (macro (if enable 'soft::defun-sk2 'soft::defund-sk2))
       (guard-decl (list :guard guard))
       (verify-guards-decl (list :verify-guards verify-guards))
       (guard-hints-decl (and guard-hints (list :guard-hints guard-hints)))
       (loc-event `(local
                    (,macro ,name ,formals
                            (declare (xargs ,@guard-decl
                                            ,@verify-guards-decl
                                            ,@guard-hints-decl))
                            ,body
                            :rewrite ,rewrite)))
       (event `(,macro ,name ,formals
                       (declare (xargs ,@guard-decl
                                       ,@verify-guards-decl))
                       ,body
                       :rewrite ,rewrite)))
    (mv loc-event event)))
