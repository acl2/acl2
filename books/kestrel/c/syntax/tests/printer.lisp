; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../printer")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define printer-test-render-expr ((expr exprp))
  :returns (string stringp)
  :verify-guards nil
  (b* ((dialect (c::make-dialect :std (c::standard-c17)))
       (pstate (init-pristate (default-priopt) dialect))
       (pstate (print-expr expr (expr-priority-expr) pstate)))
    (acl2::nats=>string (rev (pristate->bytes-rev pstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *printer-test-ident*
  (make-expr-ident :ident (ident "x") :info nil))

(acl2::assert-equal
 (printer-test-render-expr
  (make-expr-unary
   :op (unop-plus)
   :arg (make-expr-unary
         :op (unop-plus)
         :arg *printer-test-ident*
         :info nil)
   :info nil))
 "+ +x")

(acl2::assert-equal
 (printer-test-render-expr
  (make-expr-unary
   :op (unop-plus)
   :arg (make-expr-unary
         :op (unop-preinc)
         :arg *printer-test-ident*
         :info nil)
   :info nil))
 "+ ++x")

(acl2::assert-equal
 (printer-test-render-expr
  (make-expr-unary
   :op (unop-minus)
   :arg (make-expr-unary
         :op (unop-minus)
         :arg *printer-test-ident*
         :info nil)
   :info nil))
 "- -x")

(acl2::assert-equal
 (printer-test-render-expr
  (make-expr-unary
   :op (unop-minus)
   :arg (make-expr-unary
         :op (unop-predec)
         :arg *printer-test-ident*
         :info nil)
   :info nil))
 "- --x")
