; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "../../leo/execution")
(include-book "../../testing/test-json2ast")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains some tests of the formalized Leo semantics.

; This file predates the leo-acl2 Leo parser and syntax abstractor,
; but as of 2022-05-28, the defconst *file-sub-mul-mul* has been updated
; so that this checks out:
#||
(equal *file-sub-mul-mul*
       (abs-file (parse-from-string "function multiply(x: i32, y: i32) -> i32 {
    return x * y;
}
function subtract(x: i32, y: i32) -> i32 {
    return x - y;
}
function main(a: i32, b: i32, c: i32) -> i32 {
    return subtract(multiply(a, b), multiply(a, c));
}")))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Leo program in add_simple.leo:

#|
function main() -> u8 {
    return 1u8 + 1u8
}
|#

; Load JSON representation of Leo program in add_simple.json:

(make-event
 (b* (((mv & file state)
       (jsonfile-to-formal "add_simple.json" state)))
   (acl2::value `(defconst *file-one-plus-one* ',file))))

; Run Leo program in ACL2:

; run main() (with no arguments):
(assert-equal (exec-file-main *file-one-plus-one*
                              nil
                              :edwards-bls12
                              1000)
              (value-result-ok (value-u8 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Leo program in add_simple_2.leo:

#|
function main(a: u16, b: u16) -> u16 {
    return a + b
}
|#

; Load JSON representation of Leo program in add_simple_2.json:

(make-event
 (b* (((mv & file state)
       (jsonfile-to-formal "add_simple_2.json" state)))
   (acl2::value `(defconst *file-a-plus-b* ',file))))

; Run Leo program in ACL2:

; run main(100, 200):
(assert-equal (exec-file-main *file-a-plus-b*
                              (list (value-u16 100)
                                    (value-u16 200))
                              :edwards-bls12
                              1000)
              (value-result-ok (value-u16 300)))

; run main(3, 7):
(assert-equal (exec-file-main *file-a-plus-b*
                              (list (value-u16 3)
                                    (value-u16 7))
                              :edwards-bls12
                              1000)
              (value-result-ok (value-u16 10)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A Leo program with multiple functions:

#|
function multiply(x: i32, y: i32) -> i32 {
    return x * y;
}
function subtract(x: i32, y: i32) -> i32 {
    return x - y;
}
function main(a: i32, b: i32, c: i32) -> i32 {
    return subtract(multiply(a, b), multiply(a, c));
}
|#

; Manually construct ACL2 abstract syntax representation of the program above:

(defconst *file-sub-mul-mul*
  (b* ((a (make-expression-var/const :name (identifier "a")))
       (b (make-expression-var/const :name (identifier "b")))
       (c (make-expression-var/const :name (identifier "c")))
       (x (make-expression-var/const :name (identifier "x")))
       (y (make-expression-var/const :name (identifier "y")))
       (x*y (make-expression-binary :op (binop-mul)
                                    :arg1 x
                                    :arg2 y))
       (x-y (make-expression-binary :op (binop-sub)
                                    :arg1 x
                                    :arg2 y))
       (mul-a-b (make-expression-free-call :fun (identifier "multiply")
                                           :args (list a b)))
       (mul-a-c (make-expression-free-call :fun (identifier "multiply")
                                           :args (list a c)))
       (sub-mul-mul (make-expression-free-call :fun (identifier "subtract")
                                               :args (list mul-a-b mul-a-c)))
       (return-x*y (statement-return x*y))
       (return-x-y (statement-return x-y))
       (return-sub-mul-mul (statement-return sub-mul-mul))
       (multiply-body (list return-x*y))
       (subtract-body (list return-x-y))
       (main-body (list return-sub-mul-mul))
       (x-input (make-funparam :name (identifier "x")
                               :sort (make-var/const-sort-private)
                               :type (type-signed (bitsize-32))))
       (y-input (make-funparam :name (identifier "y")
                               :sort (make-var/const-sort-private)
                               :type (type-signed (bitsize-32))))
       (a-input (make-funparam :name (identifier "a")
                               :sort (make-var/const-sort-private)
                               :type (type-signed (bitsize-32))))
       (b-input (make-funparam :name (identifier "b")
                               :sort (make-var/const-sort-private)
                               :type (type-signed (bitsize-32))))
       (c-input (make-funparam :name (identifier "c")
                               :sort (make-var/const-sort-private)
                               :type (type-signed (bitsize-32))))
       (multiply-function (make-fundecl :name (identifier "multiply")
                                        :inputs (list x-input y-input)
                                        :output (type-signed (bitsize-32))
                                        :body multiply-body))
       (subtract-function (make-fundecl :name (identifier "subtract")
                                        :inputs (list x-input y-input)
                                        :output (type-signed (bitsize-32))
                                        :body subtract-body))
       (main-function (make-fundecl :name (identifier "main")
                                    :inputs (list a-input b-input c-input)
                                    :output (type-signed (bitsize-32))
                                    :body main-body)))
    (file (list (make-topdecl-function :get multiply-function)
                (make-topdecl-function :get subtract-function)
                (make-topdecl-function :get main-function)))))

; Run Leo program in ACL2:

; run main(10, 20, 30):
(assert-equal (exec-file-main *file-sub-mul-mul*
                              (list (value-i32 10)
                                    (value-i32 20)
                                    (value-i32 30))
                              :edwards-bls12
                              1000)
              (value-result-ok (value-i32 -100)))

; run main(-10, -20, -30):
(assert-equal (exec-file-main *file-sub-mul-mul*
                              (list (value-i32 -10)
                                    (value-i32 -20)
                                    (value-i32 -30))
                              :edwards-bls12
                              1000)
              (value-result-ok (value-i32 -100)))

; run main(123, 456, 789):
(assert-equal (exec-file-main *file-sub-mul-mul*
                              (list (value-i32 123)
                                    (value-i32 456)
                                    (value-i32 789))
                              :edwards-bls12
                              1000)
              (value-result-ok (value-i32 -40959)))
