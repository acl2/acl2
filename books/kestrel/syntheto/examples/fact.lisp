; Syntheto base level theory
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "../base-theory")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; factorial: A simple transformation example. Version without introducing nat as a separate type

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


#|
function factorial (n:int) assumes n >= 0 returns (out:int) ensures out > 0 {
  if (n == 0) {
    return 1;
  }
  else {
    return n * factorial(n - 1)
    }
}
|#

(defconst *function-factorial*
  (make-toplevel-function
   :get
   (make-function-definition
    :header
    (make-function-header
     :name (make-identifier :name "factorial")
     :inputs (list (make-typed-variable :name (make-identifier :name "n")
                                        :type (make-type-integer)))
     :outputs (list (make-typed-variable :name (make-identifier :name "out")
                                         :type (make-type-integer))))
    :precondition
    (make-expression-binary
     :operator (make-binary-op-ge)
     :left-operand
     (make-expression-variable :name (make-identifier :name "n"))
     :right-operand
     (make-expression-literal :get (make-literal-integer :value 0)))
    :postcondition
    (make-expression-binary
     :operator (binary-op-gt)
     :left-operand (make-expression-variable :name (make-identifier :name "out"))
     :right-operand (make-expression-literal :get (literal-integer 0)))
    :definer
    (make-function-definer-regular
     :body
     (make-expression-if
      :test (make-expression-binary
             :operator (make-binary-op-eq)
             :left-operand
             (make-expression-variable :name (make-identifier :name "n"))
             :right-operand
             (make-expression-literal :get (make-literal-integer :value 0)))
      :then (make-expression-literal :get (make-literal-integer :value 1))
      :else
      (make-expression-binary
       :operator (make-binary-op-mul)
       :left-operand (make-expression-variable :name (make-identifier :name "n"))
       :right-operand
       (make-expression-call
        :function (make-identifier :name "factorial")
        :arguments
        (list
         (make-expression-binary
          :operator (make-binary-op-sub)
          :left-operand (make-expression-variable :name (make-identifier :name "n"))
          :right-operand (make-expression-literal :get (make-literal-integer :value 1)))))))))))

(process-syntheto-toplevel *function-factorial*)

#|
factorial_t =
  transform factorial 
    by tail_recursion {new_parameter_name = r}

(apt::tailrec syndef::|factorial|
              :new-name syndef::|factorial_t|
              :accumulator syndef::|r|)
|#

(defconst *tailrec-transform-factorial*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "factorial_t")
         :old-function-name (make-identifier :name "factorial")
         :transform-name "tail_recursion"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "new_parameter_name")
                           :value (transform-argument-value-identifier (make-identifier :name "rr")))))))

(process-syntheto-toplevel *tailrec-transform-factorial*)

(defconst *tailrec-transform-factorial-wrapper*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "factorial_t2")
         :old-function-name (make-identifier :name "factorial")
         :transform-name "tail_recursion"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "new_parameter_name")
                           :value (transform-argument-value-identifier (make-identifier :name "r")))
                          (make-transform-argument
                           :name (make-identifier :name "wrapper_name")
                           :value (transform-argument-value-identifier (make-identifier :name "factorial_top")))
                          (make-transform-argument
                           :name (make-identifier :name "make_wrapper?")
                           :value (make-transform-argument-value-bool :val t))))))

(process-syntheto-toplevel *tailrec-transform-factorial-wrapper*)

(defconst *rename-param-transform-factorial*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "factorial_t1")
         :old-function-name (make-identifier :name "factorial_t")
         :transform-name "rename_param"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "old")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "rr")))
                          (make-transform-argument
                           :name (make-identifier :name "new")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "val")))))))

(process-syntheto-toplevel *rename-param-transform-factorial*)

; Add test case for failed transformation
