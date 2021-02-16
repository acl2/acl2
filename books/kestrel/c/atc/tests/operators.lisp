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
      `(c::sint-const ,x)
    `(c::sint-minus (c::sint-const ,(- x)))))

; Name of the ACL2 function that models a unary or binary operator
; and name of the C function to test the operator.
; The index is for the test number
; (just a number to distinguish the tests for an operator).

(defun afn-cfn (op index)
  (let* ((afn (packn-pos (list 'sint- op) (pkg-witness "C")))
         (cfn (intern (str::cat
                       (substitute #\_
                                   #\-
                                   (str::downcase-string (symbol-name afn)))
                       "_test"
                       (str::natstr index))
                      "ACL2")))
    (mv afn cfn)))

; Generate an ACL2 function that compares (with ==)
; (i) an expression that applies a unary operator to a constant expression
; to (ii) a constant expression obtained by calculating the result in ACL2.

(defun gen-sint-unary-test-fn (op index arg state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((mv afn cfn) (afn-cfn op index))
       (arg-expr (integer-to-sint-expr arg))
       ((er (cons & res)) (trans-eval `(,afn (c::sint ,arg)) 'test state nil))
       (res (c::sint->get res))
       (res-expr (integer-to-sint-expr res)))
    (value
     `(defun ,cfn ()
        (declare (xargs :guard t))
        (c::sint-eq (,afn ,arg-expr) ,res-expr)))))

(defmacro gen-sint-unary-test (op index arg)
  `(make-event (gen-sint-unary-test-fn ',op ',index ',arg state)))

; Generate an ACL2 function that compares (with ==)
; (i) an expression that applies a binary operator to two constant expressions
; to (ii) a constant expression obtained by calculating the result in ACL2.

(defun gen-sint-binary-test-fn (op index arg1 arg2 state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((mv afn cfn) (afn-cfn op index))
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
        (c::sint-eq (,afn ,arg1-expr ,arg2-expr) ,res-expr)))))

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

(gen-sint-binary-test shl-sint 1 3339303 0)

(gen-sint-binary-test shl-sint 2 1 30)

(gen-sint-binary-test shl-sint 3 255 8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test shr-sint 1 3339303 0)

(gen-sint-binary-test shr-sint 2 2000000000 30)

(gen-sint-binary-test shr-sint 3 2000000 8)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test logand 1 0 0)

(gen-sint-binary-test logand 2 0 1)

(gen-sint-binary-test logand 3 1 0)

(gen-sint-binary-test logand 4 1 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-sint-binary-test logor 1 0 0)

(gen-sint-binary-test logor 2 0 1)

(gen-sint-binary-test logor 3 1 0)

(gen-sint-binary-test logor 4 1 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |sint_plus_test1|
        |sint_plus_test2|
        |sint_plus_test3|
        |sint_plus_test4|
        |sint_plus_test5|
        |sint_minus_test1|
        |sint_minus_test2|
        |sint_minus_test3|
        |sint_minus_test4|
        |sint_minus_test5|
        |sint_bitnot_test1|
        |sint_bitnot_test2|
        |sint_bitnot_test3|
        |sint_bitnot_test4|
        |sint_bitnot_test5|
        |sint_lognot_test1|
        |sint_lognot_test2|
        |sint_lognot_test3|
        |sint_lognot_test4|
        |sint_lognot_test5|
        |sint_add_test1|
        |sint_add_test2|
        |sint_add_test3|
        |sint_add_test4|
        |sint_sub_test1|
        |sint_sub_test2|
        |sint_sub_test3|
        |sint_sub_test4|
        |sint_mul_test1|
        |sint_mul_test2|
        |sint_mul_test3|
        |sint_mul_test4|
        |sint_div_test1|
        |sint_div_test2|
        |sint_div_test3|
        |sint_div_test4|
        |sint_rem_test1|
        |sint_rem_test2|
        |sint_rem_test3|
        |sint_rem_test4|
        |sint_shl_sint_test1|
        |sint_shl_sint_test2|
        |sint_shl_sint_test3|
        |sint_shr_sint_test1|
        |sint_shr_sint_test2|
        |sint_shr_sint_test3|
        |sint_lt_test1|
        |sint_lt_test2|
        |sint_lt_test3|
        |sint_gt_test1|
        |sint_gt_test2|
        |sint_gt_test3|
        |sint_le_test1|
        |sint_le_test2|
        |sint_le_test3|
        |sint_ge_test1|
        |sint_ge_test2|
        |sint_ge_test3|
        |sint_eq_test1|
        |sint_eq_test2|
        |sint_eq_test3|
        |sint_ne_test1|
        |sint_ne_test2|
        |sint_ne_test3|
        |sint_bitand_test1|
        |sint_bitand_test2|
        |sint_bitand_test3|
        |sint_bitand_test4|
        |sint_bitxor_test1|
        |sint_bitxor_test2|
        |sint_bitxor_test3|
        |sint_bitxor_test4|
        |sint_bitior_test1|
        |sint_bitior_test2|
        |sint_bitior_test3|
        |sint_bitior_test4|
        |sint_logand_test1|
        |sint_logand_test2|
        |sint_logand_test3|
        |sint_logand_test4|
        |sint_logor_test1|
        |sint_logor_test2|
        |sint_logor_test3|
        |sint_logor_test4|
        :output-file "operators.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o operators operators.c operators-test.c
  ./operators

|#
