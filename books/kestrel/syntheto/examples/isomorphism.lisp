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

#|
subtype nat {
  x:int | x >= 0
}

function add1(x: nat) returns (y: nat | y > 0) {
  return x + 1;
}

function id(x: nat) returns (y: nat) {
  return x;
}

function add1_2 =
  transform add1
    by isomorphism {parameter = x,
                    new_parameter_name = xx,
                    old_type = nat,
                    new_type = nat,
                    old_to_new = id,
                    new_to_old = id,
                    simplify = true}
|#

(defconst *subtype-nat*
  (let ((x (identifier "x")))
    (toplevel-type
     (make-type-definition
      :name (identifier "nat")
      :body
      (type-definer-subset
       (make-type-subset
        :supertype (type-integer)
        :variable x
        :restriction
        (make-expression-binary
         :operator (binary-op-ge)
         :left-operand
         (make-expression-variable :name x)
         :right-operand
         (make-expression-literal :get (literal-integer 0)))))))))

(process-syntheto-toplevel *subtype-nat*)

(defthm syndef::|nat-P|-is-nat
  (equal (syndef::|nat-P| x)
         (natp x))
  :hints (("Goal" :in-theory (enable syndef::|nat-P|))))

(defconst *function-add1*
  (make-toplevel-function
   :get
   (make-function-definition
    :header
    (make-function-header
     :name (make-identifier :name "add1")
     :inputs (list (make-typed-variable :name (make-identifier :name "x")
                                        :type (type-defined (identifier "nat"))))
     :outputs (list (make-typed-variable :name (make-identifier :name "y")
                                         :type (type-defined (identifier "nat")))))
    :postcondition
    (make-expression-binary
     :operator (binary-op-gt)
     :left-operand (make-expression-variable :name (make-identifier :name "y"))
     :right-operand (make-expression-literal :get (literal-integer 0)))
    :definer
    (make-function-definer-regular
     :body
     (make-expression-binary
      :operator (make-binary-op-add)
      :left-operand (make-expression-variable :name (make-identifier :name "x"))
      :right-operand (make-expression-literal :get (make-literal-integer :value 1)))))))

(process-syntheto-toplevel *function-add1*)

(defconst *function-id*
  (make-toplevel-function
   :get
   (make-function-definition
    :header
    (make-function-header
     :name (make-identifier :name "id")
     :inputs (list (make-typed-variable :name (make-identifier :name "x")
                                        :type (type-defined (identifier "nat"))))
     :outputs (list (make-typed-variable :name (make-identifier :name "y")
                                         :type (type-defined (identifier "nat")))))
    :definer
    (make-function-definer-regular
     :body
     (make-expression-variable :name (make-identifier :name "x"))))))

(process-syntheto-toplevel *function-id*)

(in-theory (enable syndef::|id|))

(defconst *function-add1_a*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "add1_a")
         :old-function-name (make-identifier :name "add1")
         :transform-name "isomorphism"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "parameter")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "x")))
                          (make-transform-argument
                           :name (make-identifier :name "new_parameter_name")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "xx")))
                          (make-transform-argument
                           :name (make-identifier :name "old_type")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "nat")))
                          (make-transform-argument
                           :name (make-identifier :name "new_type")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "nat")))
                          (make-transform-argument
                           :name (make-identifier :name "old_to_new")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "id")))
                          (make-transform-argument
                           :name (make-identifier :name "new_to_old")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "id")))
                          (make-transform-argument
                           :name (make-identifier :name "simplify")
                           :value (make-transform-argument-value-bool :val t))))))

(process-syntheto-toplevel *function-add1_a*)
