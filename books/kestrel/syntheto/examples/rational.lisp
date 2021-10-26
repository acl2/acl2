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

; An example for the 2020-12-08 site visit demo.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we build the ASTs for the Syntheto top-level constructs
; (manually here, but they will come from the IDE through the bridge).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; subtype positive {
;;   x: int | x > 0
;; }

(defconst *subtype-positive*
  (let ((x (make-identifier :name "x")))
    (toplevel-type
     (make-type-definition
      :name (make-identifier :name "positive")
      :body
      (type-definer-subset
       (make-type-subset
        :supertype (type-integer)
        :variable x
        :restriction
        (make-expression-binary
         :operator (binary-op-gt)
         :left-operand
         (make-expression-variable :name x)
         :right-operand
         (make-expression-literal :get (literal-integer 0)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; struct mytype {
;;   y: positive
;;   | y > 0
;; }

(defconst *struct-mytype*
  (let ((y (make-identifier :name "y")))
    (toplevel-type
     (make-type-definition
      :name (make-identifier :name "mytype")
      :body
      (type-definer-product
       (make-type-product
        :fields
        (list (make-field :name y
                          :type (make-type-defined :name (make-identifier :name "positive"))))
        :invariant
        (make-expression-binary
         :operator (binary-op-gt)
         :left-operand
         (make-expression-variable :name y)
         :right-operand
         (make-expression-literal :get (literal-integer 0)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /* Define functions */
;; function gcd (x:int, y:int) assumes x >= 0 && y >= 0 returns (out:int) ensures out >= 0 {
;;   if (x == 0) {
;;     return y;
;;   }
;;   else {
;;     if (y == 0) {
;;       return x;
;;     }
;;     else {
;;       if (x < y) {
;;         return gcd (x, y % x);
;;       }
;;       else {
;;         return gcd (x % y, y);
;;       }
;;     }
;;   }
;; }

(defconst *function-gcd*
  (make-toplevel-function
   :get
   (make-function-definition
    :header
    (make-function-header
     :name (make-identifier :name "gcd")
     :inputs (list (make-typed-variable :name (make-identifier :name "x")
                                        :type (make-type-integer))
                   (make-typed-variable :name (make-identifier :name "y")
                                        :type (make-type-integer)))
     :outputs (list (make-typed-variable :name (make-identifier :name "out")
                                         :type (make-type-integer))))
    :precondition
    (make-expression-binary
     :operator (make-binary-op-and)
     :left-operand
     (make-expression-binary
      :operator (make-binary-op-ge)
      :left-operand
      (make-expression-variable :name (make-identifier :name "x"))
      :right-operand
      (make-expression-literal :get (make-literal-integer :value 0)))
     :right-operand
     (make-expression-binary
      :operator (make-binary-op-ge)
      :left-operand
      (make-expression-variable :name (make-identifier :name "y"))
      :right-operand
      (make-expression-literal :get (make-literal-integer :value 0))))
    :postcondition
    (make-expression-binary
       :operator (binary-op-ge)
       :left-operand (make-expression-variable :name (make-identifier :name "out"))
       :right-operand (make-expression-literal :get (literal-integer 0)))
    :definer
    (make-function-definer-regular
     :measure (make-expression-binary
             :operator (make-binary-op-add)
             :left-operand
             (make-expression-variable :name (make-identifier :name "x"))
             :right-operand
             (make-expression-variable :name (make-identifier :name "y")))
     :body
     (make-expression-if
      :test (make-expression-binary
             :operator (make-binary-op-eq)
             :left-operand
             (make-expression-variable :name (make-identifier :name "x"))
             :right-operand
             (make-expression-literal :get (make-literal-integer :value 0)))
      :then (make-expression-variable :name (make-identifier :name "y"))
      :else
      (make-expression-if
       :test (make-expression-binary
              :operator (make-binary-op-eq)
              :left-operand
              (make-expression-variable :name (make-identifier :name "y"))
              :right-operand
              (make-expression-literal :get (make-literal-integer :value 0)))
       :then (make-expression-variable :name (make-identifier :name "x"))
       :else
       (make-expression-if
        :test
        (make-expression-binary
         :operator (make-binary-op-lt)
         :left-operand
         (make-expression-variable :name (make-identifier :name "x"))
         :right-operand
         (make-expression-variable :name (make-identifier :name "y")))
        :then
        (make-expression-call
         :function (make-identifier :name "gcd")
         :arguments
         (list
          (make-expression-variable :name (make-identifier :name "x"))
          (make-expression-binary
           :operator (make-binary-op-rem)
           :left-operand
           (make-expression-variable :name (make-identifier :name "y"))
           :right-operand
           (make-expression-variable :name (make-identifier :name "x")))))
        :else
        (make-expression-call
         :function (make-identifier :name "gcd")
         :arguments
         (list
          (make-expression-binary
           :operator (make-binary-op-rem)
           :left-operand
           (make-expression-variable :name (make-identifier :name "x"))
           :right-operand
           (make-expression-variable :name (make-identifier :name "y")))
          (make-expression-variable :name (make-identifier :name "y")))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; function abs(x:int) returns (a:int) ensures a >= 0 {
;;   if(x >= 0) {
;;     return x;
;;   }
;;   else {
;;     return -x;
;;   }
;; }

(defconst *function-abs*
  (let ((x (make-identifier :name "x"))
        (a (make-identifier :name "a")))
    (toplevel-function
     (make-function-definition
      :header
      (make-function-header
       :name (make-identifier :name "abs")
       :inputs (list (make-typed-variable :name x :type (type-integer)))
       :outputs (list (make-typed-variable :name a :type (type-integer))))
      :precondition nil
      :postcondition
      (make-expression-binary
       :operator (binary-op-ge)
       :left-operand (make-expression-variable :name a)
       :right-operand (make-expression-literal :get (literal-integer 0)))
      :definer
      (make-function-definer-regular
       :body
       (make-expression-if
        :test
        (make-expression-binary
         :operator (binary-op-ge)
         :left-operand (make-expression-variable :name x)
         :right-operand (make-expression-literal :get (literal-integer 0)))
        :then
        (make-expression-variable :name x)
        :else
        (make-expression-unary
         :operator (unary-op-minus)
         :operand (make-expression-variable :name x))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Version of abs with bad post-condition

;; function abs_bad(x:int) returns (a:int) ensures a > 0 {
;;   if(x >= 0) {
;;     return x;
;;   }
;;   else {
;;     return -x;
;;   }
;; }

(defconst *function-abs-bad-1*
  (let ((x (make-identifier :name "x"))
        (a (make-identifier :name "a")))
    (toplevel-function
     (make-function-definition
      :header
      (make-function-header
       :name (make-identifier :name "abs_bad")
       :inputs (list (make-typed-variable :name x :type (type-integer)))
       :outputs (list (make-typed-variable :name a :type (type-integer))))
      :precondition nil
      :postcondition
      (make-expression-binary
       :operator (binary-op-gt)
       :left-operand (make-expression-variable :name a)
       :right-operand (make-expression-literal :get (literal-integer 0)))
      :definer
      (make-function-definer-regular
       :body
       (make-expression-if
        :test
        (make-expression-binary
         :operator (binary-op-ge)
         :left-operand (make-expression-variable :name x)
         :right-operand (make-expression-literal :get (literal-integer 0)))
        :then
        (make-expression-variable :name x)
        :else
        (make-expression-unary
         :operator (unary-op-minus)
         :operand (make-expression-variable :name x))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Version of abs with bad post-condition

;; function abs_bad(x:int) returns (a:positive) {
;;   if(x >= 0) {
;;     return x;
;;   }
;;   else {
;;     return -x;
;;   }
;; }

(defconst *function-abs-bad-2*
  (let ((x (make-identifier :name "x"))
        (a (make-identifier :name "a")))
    (toplevel-function
     (make-function-definition
      :header
      (make-function-header
       :name (make-identifier :name "abs_bad")
       :inputs (list (make-typed-variable :name x :type (type-integer)))
       :outputs (list (make-typed-variable :name a :type (make-type-defined :name (make-identifier :name "positive")))))
      :precondition nil
      :postcondition nil
      :definer
      (make-function-definer-regular
       :body
       (make-expression-if
        :test
        (make-expression-binary
         :operator (binary-op-ge)
         :left-operand (make-expression-variable :name x)
         :right-operand (make-expression-literal :get (literal-integer 0)))
        :then
        (make-expression-variable :name x)
        :else
        (make-expression-unary
         :operator (unary-op-minus)
         :operand (make-expression-variable :name x))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; struct rational {
;;   numerator:int,
;;   denominator:positive
;;   | gcd (abs(numerator), abs(denominator)) == 1
;; }

(defconst *struct-rational*
  (let ((numerator (make-identifier :name "numerator"))
        (denominator (make-identifier :name "denominator")))
    (toplevel-type
     (make-type-definition
      :name (make-identifier :name "rational")
      :body
      (type-definer-product
       (make-type-product
        :fields
        (list (make-field :name numerator
                          :type (type-integer))
              (make-field :name denominator
                          :type (make-type-defined :name (make-identifier :name "positive"))))
        :invariant
        (make-expression-binary
         :operator (binary-op-eq)
         :left-operand
         (make-expression-call
          :function (make-identifier :name "gcd")
          :arguments
          (list (make-expression-call
                 :function (make-identifier :name "abs")
                 :arguments
                 (list (make-expression-variable :name numerator)))
                (make-expression-call
                 :function (make-identifier :name "abs")
                 :arguments
                 (list (make-expression-variable :name denominator)))))
         :right-operand
         (make-expression-literal :get (literal-integer 1)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; function lt(x:rational, y:rational) returns (b:bool) {
;;   return x.numerator * y.denominator < y.numerator * x.denominator;
;; }

(defconst *function-lt*
  (make-toplevel-function
   :get (make-function-definition
         :header (make-function-header
                  :name (make-identifier :name "lt")
                  :inputs (list
                           (make-typed-variable :name (make-identifier :name "x")
                                                :type (make-type-defined
                                                       :name (make-identifier :name "rational")))
                           (make-typed-variable :name (make-identifier :name "y")
                                                :type (make-type-defined
                                                       :name (make-identifier :name "rational"))))
                  :outputs (list (make-typed-variable :name
                                                      (make-identifier :name "b")
                                                      :type (make-type-boolean))))
         :precondition nil :postcondition nil
         :definer
         (make-function-definer-regular
          :body (make-expression-binary
                 :operator (make-binary-op-lt)
                 :left-operand (make-expression-binary
                                :operator (make-binary-op-mul)
                                :left-operand (make-expression-product-field
                                               :type (make-identifier :name "rational")
                                               :target (make-expression-variable :name (make-identifier :name "x"))
                                               :field (make-identifier :name "numerator"))
                                :right-operand (make-expression-product-field
                                                :type (make-identifier :name "rational")
                                                :target (make-expression-variable :name (make-identifier :name "y"))
                                                :field (make-identifier :name "denominator")))
                 :right-operand (make-expression-binary
                                 :operator (make-binary-op-mul)
                                 :left-operand (make-expression-product-field
                                                :type (make-identifier :name "rational")
                                                :target (make-expression-variable :name (make-identifier :name "y"))
                                                :field (make-identifier :name "numerator"))
                                 :right-operand (make-expression-product-field
                                                 :type (make-identifier :name "rational")
                                                 :target (make-expression-variable :name (make-identifier :name "x"))
                                                 :field (make-identifier :name "denominator"))))))))


(defconst *rename-param-transform-lt*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "lt__1")
         :old-function-name (make-identifier :name "lt")
         :transform-name "rename_param"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "old")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "x")))
                          (make-transform-argument
                           :name (make-identifier :name "new")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "n")))))))

; (process-syntheto-toplevel *rename-param-transform-lt*)


;; function lteq(x:rational, y:rational) returns (b:bool) {
;;   return x.numerator * y.denominator <= y.numerator * x.denominator;
;; }

(defconst *function-lteq*
  (make-toplevel-function
   :get (make-function-definition
         :header (make-function-header
                  :name (make-identifier :name "lteq")
                  :inputs (list
                           (make-typed-variable :name (make-identifier :name "x")
                                                :type (make-type-defined
                                                       :name (make-identifier :name "rational")))
                           (make-typed-variable :name (make-identifier :name "y")
                                                :type (make-type-defined
                                                       :name (make-identifier :name "rational"))))
                  :outputs (list (make-typed-variable :name
                                                      (make-identifier :name "b")
                                                      :type (make-type-boolean))))
         :precondition nil :postcondition nil
         :definer
         (make-function-definer-regular
          :body (make-expression-binary
                 :operator (make-binary-op-le)
                 :left-operand (make-expression-binary
                                :operator (make-binary-op-mul)
                                :left-operand (make-expression-product-field
                                               :type (make-identifier :name "rational")
                                               :target (make-expression-variable :name (make-identifier :name "x"))
                                               :field (make-identifier :name "numerator"))
                                :right-operand (make-expression-product-field
                                                :type (make-identifier :name "rational")
                                                :target (make-expression-variable :name (make-identifier :name "y"))
                                                :field (make-identifier :name "denominator")))
                 :right-operand (make-expression-binary
                                 :operator (make-binary-op-mul)
                                 :left-operand (make-expression-product-field
                                                :type (make-identifier :name "rational")
                                                :target (make-expression-variable :name (make-identifier :name "y"))
                                                :field (make-identifier :name "numerator"))
                                 :right-operand (make-expression-product-field
                                                 :type (make-identifier :name "rational")
                                                 :target (make-expression-variable :name (make-identifier :name "x"))
                                                 :field (make-identifier :name "denominator"))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; function ordered(x:seq<rational>) returns (out:bool) {
;;   if(is_empty(x)) {
;;     return true;
;;   }
;;   else {
;;     if(is_empty(rest(x))) {
;;       return true;
;;     }
;;     else {
;;       return lteq (first(x), first(rest(x))) && ordered(rest(x));
;;     }
;;   }
;; }

(defconst *function-ordered*
  (make-toplevel-function
   :get
   (make-function-definition
    :header
    (make-function-header
     :name (make-identifier :name "ordered")
     :inputs
     (list
      (make-typed-variable
       :name (make-identifier :name "x")
       :type
       (make-type-sequence
        :element
        (make-type-defined :name (make-identifier :name "rational")))))
     :outputs (list (make-typed-variable :name (make-identifier :name "out")
                                         :type (make-type-boolean))))
    :precondition nil
    :postcondition nil
    :definer
    (make-function-definer-regular
     :body
     (make-expression-if
      :test
      (make-expression-call
       :function (make-identifier :name "is_empty")
       :types (list (make-type-sequence
                     :element (make-type-defined :name (make-identifier :name "rational"))))
       :arguments
       (list (make-expression-variable :name (make-identifier :name "x"))))
      :then
      (make-expression-literal :get (make-literal-boolean :value t))
      :else
      (make-expression-if
       :test
       (make-expression-call
        :function (make-identifier :name "is_empty")
        :types (list (make-type-sequence
                      :element (make-type-defined :name (make-identifier :name "rational"))))
        :arguments
        (list
         (make-expression-call
          :function (make-identifier :name "rest")
          :types (list (make-type-sequence
                        :element (make-type-defined :name (make-identifier :name "rational"))))
          :arguments
          (list
           (make-expression-variable :name (make-identifier :name "x"))))))
       :then
       (make-expression-literal :get (make-literal-boolean :value t))
       :else
       (make-expression-binary
        :operator (make-binary-op-and)
        :left-operand
        (make-expression-call
         :function (make-identifier :name "lteq")
         :arguments
         (list
          (make-expression-call
           :function (make-identifier :name "first")
           :types (list (make-type-sequence
                         :element (make-type-defined :name (make-identifier :name "rational"))))
           :arguments
           (list (make-expression-variable :name (make-identifier :name "x"))))
          (make-expression-call
           :function (make-identifier :name "first")
           :types (list (make-type-sequence
                         :element (make-type-defined :name (make-identifier :name "rational"))))
           :arguments
           (list
            (make-expression-call
             :function (make-identifier :name "rest")
             :types (list (make-type-sequence
                           :element (make-type-defined :name (make-identifier :name "rational"))))
             :arguments (list (make-expression-variable
                               :name (make-identifier :name "x"))))))))
        :right-operand
        (make-expression-call
         :function (make-identifier :name "ordered")
         :arguments
         (list
          (make-expression-call
           :function (make-identifier :name "rest")
           :types (list (make-type-sequence
                         :element (make-type-defined :name (make-identifier :name "rational"))))
           :arguments
           (list (make-expression-variable
                  :name (make-identifier :name "x")))))))))))))

(defconst *rename-param-transform-ordered*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "ordered__1")
         :old-function-name (make-identifier :name "ordered")
         :transform-name "rename_param"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "old")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "x")))
                          (make-transform-argument
                           :name (make-identifier :name "new")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "l")))))))

; (process-syntheto-toplevel *rename-param-transform-ordered*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; /* Define Theorems on the functions */
;; theorem lteq_reflexive
;;   forall(x:rational) lteq(x,x)

(defconst *theorem-lteq-reflexive*
  (toplevel-theorem
   (make-theorem
    :name (make-identifier :name "lteq_reflexive")
    :variables (list (make-typed-variable
                      :name (make-identifier :name "x")
                      :type (make-type-defined :name (make-identifier :name "rational"))))
    :formula
    (make-expression-call
     :function (make-identifier :name "lteq")
     :types nil
     :arguments
     (list (make-expression-variable :name (make-identifier :name "x"))
           (make-expression-variable :name (make-identifier :name "x")))))))

(defconst *theorem-lt-reflexive-bad*
  (toplevel-theorem
   (make-theorem
    :name (make-identifier :name "lt_reflexive_not")
    :variables (list (make-typed-variable
                      :name (make-identifier :name "x")
                      :type (make-type-defined :name (make-identifier :name "rational"))))
    :formula
    (make-expression-call
     :function (make-identifier :name "lt")
     :types nil
     :arguments
     (list (make-expression-variable :name (make-identifier :name "x"))
           (make-expression-variable :name (make-identifier :name "x")))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; function permutation(x:seq<rational>, y:seq<rational>) returns (b:bool) {
;;   if (is_empty(x)) {
;;     return is_empty(y);
;;   } else {
;;     return member (first(x), y) &&
;;            permutation (rest(x), remove_first(first(x), y));
;;   }
;; }

(defconst *function-permutation*
  (let ((x (make-identifier :name "x"))
        (y (make-identifier :name "y"))
        (b (make-identifier :name "b"))
        (seq<rational> (type-sequence (make-type-defined :name (make-identifier :name "rational")))))
    (toplevel-function
     (make-function-definition
      :header
      (make-function-header
       :name (make-identifier :name "permutation")
       :inputs (list (make-typed-variable :name x :type seq<rational>)
                     (make-typed-variable :name y :type seq<rational>))
       :outputs (list (make-typed-variable :name b :type (type-boolean))))
      :precondition nil
      :postcondition nil
      :definer
      (make-function-definer-regular
       :body
       (make-expression-if
        :test
        (make-expression-call
         :function (make-identifier :name "is_empty")
         :types (list seq<rational>)
         :arguments (list (make-expression-variable :name x)))
        :then
        (make-expression-call
         :function (make-identifier :name "is_empty")
         :types (list seq<rational>)
         :arguments (list (make-expression-variable :name y)))
        :else
        (make-expression-binary
         :operator (binary-op-and)
         :left-operand
         (make-expression-call
          :function (make-identifier :name "member")
          :types (list seq<rational>)
          :arguments
          (list (make-expression-call
                 :function (make-identifier :name "first")
                 :types (list seq<rational>)
                 :arguments (list (make-expression-variable :name x)))
                (make-expression-variable :name y)))
         :right-operand
         (make-expression-call
          :function (make-identifier :name "permutation")
          :types nil
          :arguments
          (list
           (make-expression-call
            :function (make-identifier :name "rest")
            :types (list seq<rational>)
            :arguments (list (make-expression-variable :name x)))
           (make-expression-call
            :function (make-identifier :name "remove_first")
            :types (list seq<rational>)
            :arguments
            (list (make-expression-call
                   :function (make-identifier :name "first")
                   :types (list seq<rational>)
                   :arguments (list (make-expression-variable :name x)))
                  (make-expression-variable :name y))))))))))))

(defconst *rename-param-transform-permutation*
  (make-toplevel-transform
   :get (make-transform
         :new-function-name (make-identifier :name "permutation__1")
         :old-function-name (make-identifier :name "permutation")
         :transform-name "rename_param"
         :arguments (list (make-transform-argument
                           :name (make-identifier :name "old")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "x")))
                          (make-transform-argument
                           :name (make-identifier :name "new")
                           :value (make-transform-argument-value-identifier :name (make-identifier :name "s1")))))))

;(process-syntheto-toplevel *rename-param-transform-permutation*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; specification sort_spec
;; (function sort (input:seq<rational>) returns (output:seq<rational>)) {
;;   return ordered(output) && permutation(output,input);
;; }

(defconst *specification-sort-spec*
  (let ((input (make-identifier :name "input"))
        (output (make-identifier :name "output"))
        (seq<rational> (type-sequence (make-type-defined :name (make-identifier :name "rational")))))
    (toplevel-specification
     (make-function-specification
      :name (make-identifier :name "sort_spec")
      :functions
      (list (make-function-header
             :name (make-identifier :name "sort")
             :inputs (list (make-typed-variable :name input
                                                :type seq<rational>))
             :outputs (list (make-typed-variable :name output
                                                 :type seq<rational>))))
      :specifier
      (make-function-specifier-input-output
       :relation
       (make-expression-binary
        :operator (binary-op-and)
        :left-operand
        (make-expression-call
         :function (make-identifier :name "ordered")
         :types nil
         :arguments (list (make-expression-variable :name output)))
        :right-operand
        (make-expression-call
         :function (make-identifier :name "permutation")
         :types nil
         :arguments (list (make-expression-variable :name output)
                          (make-expression-variable :name input)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *events*
  (list *subtype-positive*
        *struct-mytype*
        *function-gcd*
        *function-abs*
        *struct-rational*
        *function-lteq*
        *function-lt*
        *theorem-lteq-reflexive*
        *function-ordered*
        *function-permutation*
        *specification-sort-spec*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we process the ASTs above.

(assert-event (b* ((ctxt (make-context))
                   ((mv err? obligs)
                    (check-toplevel-list *events* ctxt))
                   (- (cw "~x0~%" obligs)))
                (equal err? nil)))

(process-syntheto-toplevel *events*)
