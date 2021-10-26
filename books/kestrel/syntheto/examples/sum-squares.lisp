(in-package "SYNTHETO")

(include-book "../base-theory")
(include-book "std/testing/must-eval-to" :dir :system)

#|
function sum_squares(n: int) assumes n >= 0 returns (sum: int) ensures sum >= 0 {
  if(n == 0) {
    return 0
    }
  else {
  return n * n + sum_squares(n - 1)
  }
}
|#

(defconst *function-sum_squares*
  (make-toplevel-function
   :get
   (make-function-definition
    :header
    (make-function-header
     :name (make-identifier :name "sum_squares")
     :inputs (list (make-typed-variable :name (make-identifier :name "n")
                                        :type (make-type-integer)))
     :outputs (list (make-typed-variable :name (make-identifier :name "sum")
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
       :operator (binary-op-ge)
       :left-operand (make-expression-variable :name (make-identifier :name "sum"))
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
      :then (make-expression-literal :get (make-literal-integer :value 0))
      :else
      (make-expression-binary
       :operator (make-binary-op-add)
       :left-operand
       (make-expression-binary
        :operator (make-binary-op-mul)
        :left-operand
        (make-expression-variable :name (make-identifier :name "n"))
        :right-operand
        (make-expression-variable :name (make-identifier :name "n")))
       :right-operand
       (make-expression-call
         :function (make-identifier :name "sum_squares")
         :arguments
         (list
          (make-expression-binary
           :operator (make-binary-op-sub)
           :left-operand
           (make-expression-variable :name (make-identifier :name "n"))
           :right-operand
           (make-expression-literal :get (make-literal-integer :value 1)))))))))))

(process-syntheto-toplevel *function-sum_squares*)

#|
function sum_squares_1 =
  transform sum_squares
    by tail_recursion {new_parameter_name = result}
|#

(defconst *tailrec-transform-sum_squares*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "sum_squares_1")
         :old-function-name (make-identifier :name "sum_squares")
         :transform-name "tail_recursion"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "new_parameter_name")
                           :value (transform-argument-value-identifier (make-identifier :name "result")))))))

(acl2::must-eval-to
 (process-syntheto-toplevel *tailrec-transform-sum_squares*)
 '(make-outcome-transformation-success
   :message "sum_squares_1"
   :toplevels
   (list
    (make-toplevel-function
     :get
     (make-function-definition
      :header (make-function-header :name (make-identifier :name "sum_squares_1")
                                    :inputs (list (make-typed-variable :name (make-identifier :name "n")
                                                                       :type (make-type-integer))
                                                  (make-typed-variable :name (make-identifier :name "result")
                                                                       :type (make-type-integer)))
                                    :outputs (list (make-typed-variable :name (make-identifier :name "sum")
                                                                        :type (make-type-integer))))
      :precondition nil
      :postcondition nil
      :definer
      (make-function-definer-regular
       :body
       (make-expression-if
        :test (make-expression-binary :operator (make-binary-op-eq)
                                      :left-operand (make-expression-variable :name (make-identifier :name "n"))
                                      :right-operand (make-expression-literal :get (make-literal-integer :value 0)))
        :then (make-expression-variable :name (make-identifier :name "result"))
        :else
        (make-expression-call
         :function (make-identifier :name "sum_squares_1")
         :types (list)
         :arguments
         (list (make-expression-binary :operator (make-binary-op-sub)
                                       :left-operand (make-expression-variable :name (make-identifier :name "n"))
                                       :right-operand (make-expression-literal :get (make-literal-integer :value 1)))
               (make-expression-binary
                :operator (make-binary-op-add)
                :left-operand
                (make-expression-binary :operator (make-binary-op-mul)
                                        :left-operand (make-expression-variable :name (make-identifier :name "n"))
                                        :right-operand (make-expression-variable :name (make-identifier :name "n")))
                :right-operand (make-expression-variable :name (make-identifier :name "result"))))))
       :measure nil)))))
 :with-output-off nil)

(process-syntheto-toplevel *tailrec-transform-sum_squares*)

#|
function sum_squares_2 =
  transform sum_squares
    by finite_difference {expression = n * n,
                          new_parameter_name = n_sq,
                          simplify = true}
|#

(defconst *finite_difference-transform-sum_squares*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "sum_squares_2")
         :old-function-name (make-identifier :name "sum_squares")
         :transform-name "finite_difference"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "expression")
                           :value (make-transform-argument-value-term
                                   :get (make-expression-binary
                                         :operator (make-binary-op-mul)
                                         :left-operand
                                         (make-expression-variable :name (make-identifier :name "n"))
                                         :right-operand
                                         (make-expression-variable :name (make-identifier :name "n")))))
                          (make-transform-argument
                           :name (make-identifier :name "new_parameter_name")
                           :value (transform-argument-value-identifier (make-identifier :name "n_sq")))
                          (make-transform-argument
                           :name (make-identifier :name "simplify")
                           :value (make-transform-argument-value-bool :val t))
                          ))))

(acl2::must-eval-to
 (process-syntheto-toplevel *finite_difference-transform-sum_squares*)
 '(make-outcome-transformation-success
   :message "sum_squares_2"
   :toplevels
   (list
    (make-toplevel-function
     :get
     (make-function-definition
      :header (make-function-header :name (make-identifier :name "sum_squares_2")
                                    :inputs (list (make-typed-variable :name (make-identifier :name "n")
                                                                       :type (make-type-integer))
                                                  (make-typed-variable :name (make-identifier :name "n_sq")
                                                                       :type (make-type-integer)))
                                    :outputs (list (make-typed-variable :name (make-identifier :name "sum")
                                                                        :type (make-type-integer))))
      :precondition
      (make-expression-binary
       :operator (make-binary-op-eq)
       :left-operand (make-expression-variable :name (make-identifier :name "n_sq"))
       :right-operand
       (make-expression-binary :operator (make-binary-op-mul)
                               :left-operand (make-expression-variable :name (make-identifier :name "n"))
                               :right-operand (make-expression-variable :name (make-identifier :name "n"))))
      :postcondition nil
      :definer
      (make-function-definer-regular
       :body
       (make-expression-if
        :test (make-expression-binary :operator (make-binary-op-eq)
                                      :left-operand (make-expression-variable :name (make-identifier :name "n"))
                                      :right-operand (make-expression-literal :get (make-literal-integer :value 0)))
        :then (make-expression-literal :get (make-literal-integer :value 0))
        :else
        (make-expression-binary
         :operator (make-binary-op-add)
         :left-operand (make-expression-variable :name (make-identifier :name "n_sq"))
         :right-operand
         (make-expression-call
          :function (make-identifier :name "sum_squares_2")
          :types (list)
          :arguments
          (list
           (make-expression-binary :operator (make-binary-op-sub)
                                   :left-operand (make-expression-variable :name (make-identifier :name "n"))
                                   :right-operand (make-expression-literal :get (make-literal-integer :value 1)))
           (make-expression-binary
            :operator (make-binary-op-add)
            :left-operand (make-expression-literal :get (make-literal-integer :value 1))
            :right-operand
            (make-expression-binary
             :operator (make-binary-op-add)
             :left-operand (make-expression-unary :operator (make-unary-op-minus)
                                                  :operand (make-expression-variable :name (make-identifier :name "n")))
             :right-operand
             (make-expression-binary
              :operator (make-binary-op-add)
              :left-operand (make-expression-unary :operator (make-unary-op-minus)
                                                   :operand (make-expression-variable :name (make-identifier :name "n")))
              :right-operand (make-expression-variable :name (make-identifier :name "n_sq")))))))))
       :measure nil)))))
 :with-output-off nil)

(process-syntheto-toplevel *finite_difference-transform-sum_squares*)

#|
function sum_squares_3 =
  transform sum_squares_1
    by finite_difference {expression = n * n,
                          new_parameter_name = n_sq,
                          simplify = true}
|#

(acl2::must-eval-to
 (process-syntheto-toplevel
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "sum_squares_3")
         :old-function-name (make-identifier :name "sum_squares_1")
         :transform-name "finite_difference"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "expression")
                           :value (make-transform-argument-value-term
                                   :get (make-expression-binary
                                         :operator (make-binary-op-mul)
                                         :left-operand
                                         (make-expression-variable :name (make-identifier :name "n"))
                                         :right-operand
                                         (make-expression-variable :name (make-identifier :name "n")))))
                          (make-transform-argument
                           :name (make-identifier :name "new_parameter_name")
                           :value (transform-argument-value-identifier (make-identifier :name "n_sq")))
                          (make-transform-argument
                           :name (make-identifier :name "simplify")
                           :value (make-transform-argument-value-bool :val t))
                          ))))
 '(make-outcome-transformation-success
   :message "sum_squares_3"
   :toplevels
   (list
    (make-toplevel-function
     :get
     (make-function-definition
      :header (make-function-header :name (make-identifier :name "sum_squares_3")
                                    :inputs (list (make-typed-variable :name (make-identifier :name "n")
                                                                       :type (make-type-integer))
                                                  (make-typed-variable :name (make-identifier :name "result")
                                                                       :type (make-type-integer))
                                                  (make-typed-variable :name (make-identifier :name "n_sq")
                                                                       :type (make-type-integer)))
                                    :outputs (list (make-typed-variable :name (make-identifier :name "sum")
                                                                        :type (make-type-integer))))
      :precondition
      (make-expression-binary
       :operator (make-binary-op-eq)
       :left-operand (make-expression-variable :name (make-identifier :name "n_sq"))
       :right-operand
       (make-expression-binary :operator (make-binary-op-mul)
                               :left-operand (make-expression-variable :name (make-identifier :name "n"))
                               :right-operand (make-expression-variable :name (make-identifier :name "n"))))
      :postcondition nil
      :definer
      (make-function-definer-regular
       :body
       (make-expression-if
        :test (make-expression-binary :operator (make-binary-op-eq)
                                      :left-operand (make-expression-variable :name (make-identifier :name "n"))
                                      :right-operand (make-expression-literal :get (make-literal-integer :value 0)))
        :then (make-expression-variable :name (make-identifier :name "result"))
        :else
        (make-expression-call
         :function (make-identifier :name "sum_squares_3")
         :types (list)
         :arguments
         (list
          (make-expression-binary :operator (make-binary-op-sub)
                                  :left-operand (make-expression-variable :name (make-identifier :name "n"))
                                  :right-operand (make-expression-literal :get (make-literal-integer :value 1)))
          (make-expression-binary :operator (make-binary-op-add)
                                  :left-operand (make-expression-variable :name (make-identifier :name "n_sq"))
                                  :right-operand (make-expression-variable :name (make-identifier :name "result")))
          (make-expression-binary
           :operator (make-binary-op-add)
           :left-operand (make-expression-literal :get (make-literal-integer :value 1))
           :right-operand
           (make-expression-binary
            :operator (make-binary-op-add)
            :left-operand (make-expression-unary :operator (make-unary-op-minus)
                                                 :operand (make-expression-variable :name (make-identifier :name "n")))
            :right-operand
            (make-expression-binary
             :operator (make-binary-op-add)
             :left-operand (make-expression-unary :operator (make-unary-op-minus)
                                                  :operand (make-expression-variable :name (make-identifier :name "n")))
             :right-operand (make-expression-variable :name (make-identifier :name "n_sq"))))))))
       :measure nil)))))
 :with-output-off nil)
