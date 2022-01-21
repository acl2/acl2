; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

(include-book "kestrel/utilities/trans-eval-error-triple" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These examples also serve to validate our formalization of C operators,
; by testing their results against the ones from the corresponding C code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Represent an integer as a constant int expression.
; Since C integer constants are non-negative,
; we need to use unary minus on the negated integer when it is negative.

(defun integer-to-sint-expr (x)
  (if (>= x 0)
      `(c::sint-dec-const ,x)
    `(c::minus-sint (c::sint-dec-const ,(- x)))))

; Name of the ACL2 function that models a unary or binary operator
; and name of the C function to test the operator.
; The index is for the test number
; (just a number to distinguish the tests for an operator).

(defun afn-cfn-unary (op index)
  (let* ((afn (packn-pos (list op '-sint) (pkg-witness "C")))
         (cfn (intern (str::cat
                       (substitute #\_
                                   #\-
                                   (str::downcase-string (symbol-name afn)))
                       "_test"
                       (str::nat-to-dec-string index))
                      "ACL2")))
    (mv afn cfn)))

(defun afn-cfn-binary (op index)
  (let* ((afn (packn-pos (list op '-sint-sint) (pkg-witness "C")))
         (cfn (intern (str::cat
                       (substitute #\_
                                   #\-
                                   (str::downcase-string (symbol-name afn)))
                       "_test"
                       (str::nat-to-dec-string index))
                      "ACL2")))
    (mv afn cfn)))

; Generate an ACL2 function that compares (with ==)
; (i) an expression that applies a unary operator to a constant expression
; to (ii) a constant expression obtained by calculating the result in ACL2.

(defun gen-sint-unary-test-fn (op index arg state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((mv afn cfn) (afn-cfn-unary op index))
       (arg-expr (integer-to-sint-expr arg))
       ((er (cons & res)) (trans-eval `(,afn (c::sint ,arg)) 'test state nil))
       (res (c::sint->get res))
       (res-expr (integer-to-sint-expr res)))
    (value
     `(defun ,cfn ()
        (declare (xargs :guard t))
        (c::eq-sint-sint (,afn ,arg-expr) ,res-expr)))))

(defmacro gen-sint-unary-test (op index arg)
  `(make-event (gen-sint-unary-test-fn ',op ',index ',arg state)))

; Generate an ACL2 function that compares (with ==)
; (i) an expression that applies a binary operator to two constant expressions
; to (ii) a constant expression obtained by calculating the result in ACL2.

(defun gen-sint-binary-test-fn (op index arg1 arg2 state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((mv afn cfn) (afn-cfn-binary op index))
       (arg1-expr (integer-to-sint-expr arg1))
       (arg2-expr (integer-to-sint-expr arg2))
       ((er (cons & res)) (trans-eval `(,afn (c::sint ,arg1) (c::sint ,arg2))
                                      'test
                                      state
                                      nil))
       (res (c::sint->get res))
       (res-expr (integer-to-sint-expr res)))
    (value
     `(defun ,cfn ()
        (declare (xargs :guard t))
        (c::eq-sint-sint (,afn ,arg1-expr ,arg2-expr) ,res-expr)))))

(defmacro gen-sint-binary-test (op index arg1 arg2)
  `(make-event (gen-sint-binary-test-fn ',op ',index ',arg1 ',arg2 state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-unary-test plus 1 0)

(gen-sint-unary-test plus 2 10)

(gen-sint-unary-test plus 3 -10)

(gen-sint-unary-test plus 4 88234932)

(gen-sint-unary-test plus 5 -7278838)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-unary-test minus 1 0)

(gen-sint-unary-test minus 2 10)

(gen-sint-unary-test minus 3 -10)

(gen-sint-unary-test minus 4 88234932)

(gen-sint-unary-test minus 5 -7278838)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-unary-test bitnot 1 0)

(gen-sint-unary-test bitnot 2 10)

(gen-sint-unary-test bitnot 3 -10)

(gen-sint-unary-test bitnot 4 88234932)

(gen-sint-unary-test bitnot 5 -7278838)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-unary-test lognot 1 0)

(gen-sint-unary-test lognot 2 10)

(gen-sint-unary-test lognot 3 -10)

(gen-sint-unary-test lognot 4 88234932)

(gen-sint-unary-test lognot 5 -7278838)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test add 1 133 9292)

(gen-sint-binary-test add 2 -1111 934923)

(gen-sint-binary-test add 3 27373 -9)

(gen-sint-binary-test add 4 -77222 -2222)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test sub 1 133 9292)

(gen-sint-binary-test sub 2 -1111 934923)

(gen-sint-binary-test sub 3 27373 -9)

(gen-sint-binary-test sub 4 -77222 -2222)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test mul 1 133 9292)

(gen-sint-binary-test mul 2 -1111 76)

(gen-sint-binary-test mul 3 27373 -9)

(gen-sint-binary-test mul 4 -77222 -222)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test div 1 133 9292)

(gen-sint-binary-test div 2 -1111 934923)

(gen-sint-binary-test div 3 27373 -9)

(gen-sint-binary-test div 4 -77222 -2222)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test rem 1 133 9292)

(gen-sint-binary-test rem 2 -1111 934923)

(gen-sint-binary-test rem 3 27373 -9)

(gen-sint-binary-test rem 4 -77222 -2222)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test shl 1 3339303 0)

(gen-sint-binary-test shl 2 1 30)

(gen-sint-binary-test shl 3 255 8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test shr 1 3339303 0)

(gen-sint-binary-test shr 2 2000000000 30)

(gen-sint-binary-test shr 3 2000000 8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test lt 1 -44493 828282)

(gen-sint-binary-test lt 2 -11 -166)

(gen-sint-binary-test lt 3 1 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test gt 1 -44493 828282)

(gen-sint-binary-test gt 2 -11 -166)

(gen-sint-binary-test gt 3 1 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test le 1 -44493 828282)

(gen-sint-binary-test le 2 -11 -166)

(gen-sint-binary-test le 3 1 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test ge 1 -44493 828282)

(gen-sint-binary-test ge 2 -11 -166)

(gen-sint-binary-test ge 3 1 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test eq 1 -44493 828282)

(gen-sint-binary-test eq 2 -11 -166)

(gen-sint-binary-test eq 3 1 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test ne 1 -44493 828282)

(gen-sint-binary-test ne 2 -11 -166)

(gen-sint-binary-test ne 3 1 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test bitand 1 133 9292)

(gen-sint-binary-test bitand 2 -1111 934923)

(gen-sint-binary-test bitand 3 27373 -9)

(gen-sint-binary-test bitand 4 -77222 -2222)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test bitxor 1 133 9292)

(gen-sint-binary-test bitxor 2 -1111 934923)

(gen-sint-binary-test bitxor 3 27373 -9)

(gen-sint-binary-test bitxor 4 -77222 -2222)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test bitior 1 133 9292)

(gen-sint-binary-test bitior 2 -1111 934923)

(gen-sint-binary-test bitior 3 27373 -9)

(gen-sint-binary-test bitior 4 -77222 -2222)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |plus_sint_test1|
        |plus_sint_test2|
        |plus_sint_test3|
        |plus_sint_test4|
        |plus_sint_test5|
        |minus_sint_test1|
        |minus_sint_test2|
        |minus_sint_test3|
        |minus_sint_test4|
        |minus_sint_test5|
        |bitnot_sint_test1|
        |bitnot_sint_test2|
        |bitnot_sint_test3|
        |bitnot_sint_test4|
        |bitnot_sint_test5|
        |lognot_sint_test1|
        |lognot_sint_test2|
        |lognot_sint_test3|
        |lognot_sint_test4|
        |lognot_sint_test5|
        |add_sint_sint_test1|
        |add_sint_sint_test2|
        |add_sint_sint_test3|
        |add_sint_sint_test4|
        |sub_sint_sint_test1|
        |sub_sint_sint_test2|
        |sub_sint_sint_test3|
        |sub_sint_sint_test4|
        |mul_sint_sint_test1|
        |mul_sint_sint_test2|
        |mul_sint_sint_test3|
        |mul_sint_sint_test4|
        |div_sint_sint_test1|
        |div_sint_sint_test2|
        |div_sint_sint_test3|
        |div_sint_sint_test4|
        |rem_sint_sint_test1|
        |rem_sint_sint_test2|
        |rem_sint_sint_test3|
        |rem_sint_sint_test4|
        |shl_sint_sint_test1|
        |shl_sint_sint_test2|
        |shl_sint_sint_test3|
        |shr_sint_sint_test1|
        |shr_sint_sint_test2|
        |shr_sint_sint_test3|
        |lt_sint_sint_test1|
        |lt_sint_sint_test2|
        |lt_sint_sint_test3|
        |gt_sint_sint_test1|
        |gt_sint_sint_test2|
        |gt_sint_sint_test3|
        |le_sint_sint_test1|
        |le_sint_sint_test2|
        |le_sint_sint_test3|
        |ge_sint_sint_test1|
        |ge_sint_sint_test2|
        |ge_sint_sint_test3|
        |eq_sint_sint_test1|
        |eq_sint_sint_test2|
        |eq_sint_sint_test3|
        |ne_sint_sint_test1|
        |ne_sint_sint_test2|
        |ne_sint_sint_test3|
        |bitand_sint_sint_test1|
        |bitand_sint_sint_test2|
        |bitand_sint_sint_test3|
        |bitand_sint_sint_test4|
        |bitxor_sint_sint_test1|
        |bitxor_sint_sint_test2|
        |bitxor_sint_sint_test3|
        |bitxor_sint_sint_test4|
        |bitior_sint_sint_test1|
        |bitior_sint_sint_test2|
        |bitior_sint_sint_test3|
        |bitior_sint_sint_test4|
        :output-file "operators.c")
