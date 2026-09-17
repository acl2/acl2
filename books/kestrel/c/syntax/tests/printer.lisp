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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; __extension__ has unary priority and takes a cast expression as operand.

(acl2::assert-equal
 (printer-test-render-expr
  (expr-extension
   (make-expr-unary :op (unop-minus) :arg *printer-test-ident*)))
 "__extension__ -x")

(acl2::assert-equal
 (printer-test-render-expr
  (expr-extension
   (make-expr-cast
    :type (make-tyname :specquals (list (spec/qual-typespec (type-spec-int))))
    :arg *printer-test-ident*)))
 "__extension__ (int) x")

(acl2::assert-equal
 (printer-test-render-expr
  (expr-extension
   (make-expr-binary :op (binop-add)
                     :arg1 *printer-test-ident*
                     :arg2 *printer-test-ident*)))
 "__extension__ (x + x)")

(acl2::assert-equal
 (printer-test-render-expr
  (expr-extension
   (make-expr-funcall :fun *printer-test-ident* :args nil)))
 "__extension__ x()")

(acl2::assert-equal
 (printer-test-render-expr
  (make-expr-funcall :fun (expr-extension *printer-test-ident*) :args nil))
 "(__extension__ x)()")

(acl2::assert-equal
 (printer-test-render-expr
  (make-expr-arrsub :arg1 (expr-extension *printer-test-ident*)
                    :arg2 *printer-test-ident*))
 "(__extension__ x)[x]")

(acl2::assert-equal
 (printer-test-render-expr
  (make-expr-unary :op (unop-postinc)
                   :arg (expr-extension *printer-test-ident*)))
 "(__extension__ x)++")
