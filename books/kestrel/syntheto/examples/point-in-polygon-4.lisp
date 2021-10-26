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
struct point {
  x: int,
  y: int
}

struct edge {
  p1: point,
  p2: point
}
|#

(process-syntheto-toplevel
 (make-toplevel-type
  :get (make-type-definition
        :name (make-identifier :name "point")
        :body (make-type-definer-product
               :get (make-type-product
                     :fields (list (make-field
                                    :name (make-identifier :name "x")
                                    :type (make-type-integer))
                                   (make-field
                                    :name (make-identifier :name "y")
                                    :type (make-type-integer)))
                     :invariant nil)))))

(process-syntheto-toplevel
 (make-toplevel-type
  :get (make-type-definition
        :name (make-identifier :name "edge")
        :body (make-type-definer-product
               :get (make-type-product
                     :fields (list (make-field
                                    :name (make-identifier :name "p1")
                                    :type (make-type-defined
                                           :name (make-identifier :name "point")))
                                   (make-field
                                    :name (make-identifier :name "p2")
                                    :type (make-type-defined
                                           :name (make-identifier :name "point"))))
                     :invariant nil)))))

#|
function even(i:int) returns (b:bool) {
  return i % 2 == 0;
}

function odd(i:int) returns (b:bool) {
  return !even(i);
}

theorem odd_of_plus_1
  forall (i:int)
    odd(1+i) == !odd(i)

function natp(i:int) returns (b:bool) {
  return i >= 0;
}

function max(x: int, y: int) returns (m: int) {
  if (y > x) {
    return y;
  }
  else {
  return x;
  }
}

function min(x: int, y: int) returns (m: int) {
  if (y < x) {
    return y;
  }
  else {
  return x;
  }
}
function max_x(vertices: seq<point>) returns (m: int) ensures m >= 0 {
  if (is_empty(vertices)) {
   return 0;
  }
  else {
    let v1: point = first(vertices);
    return max(v1.x,
               max_x(rest(vertices)));
  }
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "even")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "i")
                                :type (make-type-integer)))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-binary
                         :operator (make-binary-op-eq)
                         :left-operand (make-expression-binary
                                        :operator (make-binary-op-rem)
                                        :left-operand (make-expression-variable
                                                       :name (make-identifier :name "i"))
                                        :right-operand (make-expression-literal
                                                        :get (make-literal-integer
                                                              :value 2)))
                         :right-operand (make-expression-literal
                                         :get (make-literal-integer
                                               :value 0)))))))

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "odd")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "i")
                                :type (make-type-integer)))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-unary
                         :operator (make-unary-op-not)
                         :operand (make-expression-call
                                   :function (make-identifier :name "even")
                                   :types (list)
                                   :arguments (list (make-expression-variable
                                                     :name (make-identifier :name "i")))))
                  :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "odd_of_plus_1")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "i")
                          :type (make-type-integer)))
        :formula (make-expression-binary
                  :operator (make-binary-op-eq)
                  :left-operand (make-expression-call
                                 :function (make-identifier :name "odd")
                                 :types (list)
                                 :arguments (list (make-expression-binary
                                                   :operator (make-binary-op-add)
                                                   :left-operand (make-expression-literal
                                                                   :get (make-literal-integer
                                                                         :value 1))
                                                   :right-operand (make-expression-variable
                                                                  :name (make-identifier :name "i")))))
                  :right-operand (make-expression-unary
                                  :operator (make-unary-op-not)
                                  :operand (make-expression-call
                                            :function (make-identifier :name "odd")
                                            :types (list)
                                            :arguments (list (make-expression-variable
                                                              :name (make-identifier :name "i")))))))))

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "natp")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "i")
                                :type (make-type-integer)))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-binary
                         :operator (make-binary-op-ge)
                         :left-operand (make-expression-variable
                                        :name (make-identifier :name "i"))
                         :right-operand (make-expression-literal
                                         :get (make-literal-integer
                                               :value 0)))))))

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "max")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "x")
                                :type (make-type-integer))
                               (make-typed-variable
                                :name (make-identifier :name "y")
                                :type (make-type-integer)))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "m")
                                 :type (make-type-integer))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-if
                         :test (make-expression-binary
                                :operator (make-binary-op-gt)
                                :left-operand (make-expression-variable
                                               :name (make-identifier :name "y"))
                                :right-operand (make-expression-variable
                                                :name (make-identifier :name "x")))
                         :then (make-expression-variable
                                :name (make-identifier :name "y"))
                         :else (make-expression-variable
                                :name (make-identifier :name "x")))
                  :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "min")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "x")
                                :type (make-type-integer))
                               (make-typed-variable
                                :name (make-identifier :name "y")
                                :type (make-type-integer)))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "m")
                                 :type (make-type-integer))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-if
                         :test (make-expression-binary
                                :operator (make-binary-op-lt)
                                :left-operand (make-expression-variable
                                               :name (make-identifier :name "y"))
                                :right-operand (make-expression-variable
                                                :name (make-identifier :name "x")))
                         :then (make-expression-variable
                                :name (make-identifier :name "y"))
                         :else (make-expression-variable
                                :name (make-identifier :name "x")))
                  :measure nil)))) 

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "max_x")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "vertices")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "m")
                                 :type (make-type-integer))))
        :precondition nil
        :postcondition (make-expression-binary
                        :operator (make-binary-op-ge)
                        :left-operand (make-expression-variable
                                       :name (make-identifier :name "m"))
                        :right-operand (make-expression-literal
                                        :get (make-literal-integer
                                              :value 0)))
        :definer (make-function-definer-regular
                  :body (make-expression-if
                         :test (make-expression-call
                                :function (make-identifier :name "is_empty")
                                :types (list (make-type-sequence
                                              :element (make-type-defined
                                                        :name (make-identifier :name "point"))))
                                :arguments (list (make-expression-variable
                                                  :name (make-identifier :name "vertices"))))
                         :then (make-expression-literal
                                :get (make-literal-integer
                                      :value 0))
                         :else (make-expression-bind
                                :variables (list (make-typed-variable
                                                  :name (make-identifier :name "v1")
                                                  :type (make-type-defined
                                                         :name (make-identifier :name "point"))))
                                :value (make-expression-call
                                        :function (make-identifier :name "first")
                                        :types (list (make-type-sequence
                                                      :element (make-type-defined
                                                                :name (make-identifier :name "point"))))
                                        :arguments (list (make-expression-variable
                                                          :name (make-identifier :name "vertices"))))
                                :body (make-expression-call
                                       :function (make-identifier :name "max")
                                       :types (list)
                                       :arguments (list (make-expression-product-field
                                                         :type (make-identifier :name "point")
                                                         :target (make-expression-variable
                                                                  :name (make-identifier :name "v1"))
                                                         :field (make-identifier :name "x"))
                                                        (make-expression-call
                                                         :function (make-identifier :name "max_x")
                                                         :types (list)
                                                         :arguments (list (make-expression-call
                                                                           :function (make-identifier :name "rest")
                                                                           :types (list (make-type-sequence
                                                                                         :element (make-type-defined
                                                                                                   :name (make-identifier :name "point"))))
                                                                           :arguments (list (make-expression-variable
                                                                                             :name (make-identifier :name "vertices"))))))))))
                  :measure nil))))


#|
function connected(e1:edge, e2:edge) returns (b:bool) {
  return e1.p2 == e2.p1;
}

function path_p(edges:seq<edge>) returns (b:bool) {
  return length(edges) <= 1
        || (connected(first(edges), first(rest(edges)))
             && path_p(rest(edges)));
}

theorem path_p_rest
  forall(edges:seq<edge>)
    !is_empty(edges) && path_p(edges)
      ==> path_p(rest(edges))
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "connected")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "e1")
                                :type (make-type-defined
                                       :name (make-identifier :name "edge")))
                               (make-typed-variable
                                :name (make-identifier :name "e2")
                                :type (make-type-defined
                                       :name (make-identifier :name "edge"))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-binary
                         :operator (make-binary-op-eq)
                         :left-operand (make-expression-product-field
                                        :type (make-identifier :name "edge")
                                        :target (make-expression-variable
                                                 :name (make-identifier :name "e1"))
                                        :field (make-identifier :name "p2"))
                         :right-operand (make-expression-product-field
                                         :type (make-identifier :name "edge")
                                         :target (make-expression-variable
                                                  :name (make-identifier :name "e2"))
                                         :field (make-identifier :name "p1")))
                  :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "path_p")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "edges")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "edge")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer
        (make-function-definer-regular
         :body (make-expression-binary
                :operator (make-binary-op-or)
                :left-operand (make-expression-binary
                               :operator (make-binary-op-lt)
                               :left-operand (make-expression-call
                                              :function (make-identifier :name "length")
                                              :types (list (make-type-sequence
                                                            :element (make-type-defined
                                                                      :name (make-identifier :name "edge"))))
                                              :arguments (list (make-expression-variable
                                                                :name (make-identifier :name "edges"))))
                               :right-operand (make-expression-literal
                                               :get (make-literal-integer
                                                     :value 2)))
                :right-operand
                (make-expression-binary
                 :operator (make-binary-op-and)
                 :left-operand (make-expression-call
                                :function (make-identifier :name "connected")
                                :types (list)
                                :arguments (list (make-expression-call
                                                  :function (make-identifier :name "first")
                                                  :types (list (make-type-sequence
                                                                :element (make-type-defined
                                                                          :name (make-identifier :name "edge"))))
                                                  :arguments (list (make-expression-variable
                                                                    :name (make-identifier :name "edges"))))
                                                 (make-expression-call
                                                  :function (make-identifier :name "first")
                                                  :types (list (make-type-sequence
                                                                :element (make-type-defined
                                                                          :name (make-identifier :name "edge"))))
                                                  :arguments (list (make-expression-call
                                                                    :function (make-identifier :name "rest")
                                                                    :types (list (make-type-sequence
                                                                                  :element (make-type-defined
                                                                                            :name (make-identifier :name "edge"))))
                                                                    :arguments (list (make-expression-variable
                                                                                      :name (make-identifier :name "edges"))))))))
                 :right-operand (make-expression-call
                                 :function (make-identifier :name "path_p")
                                 :types (list)
                                 :arguments (list (make-expression-call
                                                   :function (make-identifier :name "rest")
                                                   :types (list (make-type-sequence
                                                                 :element (make-type-defined
                                                                           :name (make-identifier :name "edge"))))
                                                   :arguments (list (make-expression-variable
                                                                     :name (make-identifier :name "edges"))))))))
         :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "path_p_rest")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "edges")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "edge")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-binary
                                 :operator (make-binary-op-and)
                                 :left-operand (make-expression-unary
                                                :operator (make-unary-op-not)
                                                :operand (make-expression-call
                                                          :function (make-identifier :name "is_empty")
                                                          :types (list (make-type-sequence
                                                                        :element (make-type-defined
                                                                                  :name (make-identifier :name "edge"))))
                                                          :arguments (list (make-expression-variable
                                                                            :name (make-identifier :name "edges")))))
                                 :right-operand (make-expression-call
                                                 :function (make-identifier :name "path_p")
                                                 :types (list)
                                                 :arguments (list (make-expression-variable
                                                                   :name (make-identifier :name "edges")))))
                  :right-operand (make-expression-call
                                  :function (make-identifier :name "path_p")
                                  :types (list)
                                  :arguments (list (make-expression-call
                                                    :function (make-identifier :name "rest")
                                                    :types (list (make-type-sequence
                                                                  :element (make-type-defined
                                                                            :name (make-identifier :name "edge"))))
                                                    :arguments (list (make-expression-variable
                                                                      :name (make-identifier :name "edges"))))))))))

#|
// Given a list of points, return the list of edges
// that connect the points in sequence
function path(vertices:seq<point>) returns (p:seq<edge>) ensures path_p(p) {
  if (is_empty(vertices) || is_empty(rest(vertices))) {
    return empty;
  }
  else {
    let e: edge = edge(p1=first(vertices), p2=first(rest(vertices)));
    return add(e, path(rest(vertices)));
  }
}

theorem not_empty_path
  forall(vertices:seq<point>)
    !is_empty(vertices) && !is_empty(rest(vertices))
      ==> !is_empty(path(vertices))

theorem length_path
  forall(vertices:seq<point>)
    !is_empty(vertices)
      ==> length(path(vertices)) == length(vertices) - 1
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "path")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "vertices")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "p")
                                 :type (make-type-sequence
                                        :element (make-type-defined
                                                  :name (make-identifier :name "edge"))))))
        :precondition nil
        :postcondition (make-expression-call
                        :function (make-identifier :name "path_p")
                        :types (list)
                        :arguments (list (make-expression-variable
                                          :name (make-identifier :name "p"))))
        :definer
        (make-function-definer-regular
         :body (make-expression-if
                :test (make-expression-binary
                       :operator (make-binary-op-or)
                       :left-operand (make-expression-call
                                      :function (make-identifier :name "is_empty")
                                      :types (list (make-type-sequence
                                                    :element (make-type-defined
                                                              :name (make-identifier :name "point"))))
                                      :arguments (list (make-expression-variable
                                                        :name (make-identifier :name "vertices"))))
                       :right-operand (make-expression-call
                                       :function (make-identifier :name "is_empty")
                                       :types (list (make-type-sequence
                                                     :element (make-type-defined
                                                               :name (make-identifier :name "point"))))
                                       :arguments (list (make-expression-call
                                                         :function (make-identifier :name "rest")
                                                         :types (list (make-type-sequence
                                                                       :element (make-type-defined
                                                                                 :name (make-identifier :name "point"))))
                                                         :arguments (list (make-expression-variable
                                                                           :name (make-identifier :name "vertices")))))))
                :then (make-expression-call
                       :function (make-identifier :name "empty")
                       :types (list (make-type-sequence
                                     :element (make-type-defined
                                               :name (make-identifier :name "edge"))))
                       :arguments (list))
                :else (make-expression-bind
                       :variables (list (make-typed-variable
                                         :name (make-identifier :name "e")
                                         :type (make-type-defined
                                                :name (make-identifier :name "edge"))))
                       :value (make-expression-product-construct
                               :type (make-identifier :name "edge")
                               :fields (list (make-initializer
                                              :field (make-identifier :name "p1")
                                              :value (make-expression-call
                                                      :function (make-identifier :name "first")
                                                      :types (list (make-type-sequence
                                                                    :element (make-type-defined
                                                                              :name (make-identifier :name "point"))))
                                                      :arguments (list (make-expression-variable
                                                                        :name (make-identifier :name "vertices")))))
                                             (make-initializer
                                              :field (make-identifier :name "p2")
                                              :value (make-expression-call
                                                      :function (make-identifier :name "first")
                                                      :types (list (make-type-sequence
                                                                    :element (make-type-defined
                                                                              :name (make-identifier :name "point"))))
                                                      :arguments (list (make-expression-call
                                                                        :function (make-identifier :name "rest")
                                                                        :types (list (make-type-sequence
                                                                                      :element (make-type-defined
                                                                                                :name (make-identifier :name "point"))))
                                                                        :arguments (list (make-expression-variable
                                                                                          :name (make-identifier :name "vertices")))))))))
                       :body (make-expression-call
                              :function (make-identifier :name "add")
                              :types (list (make-type-sequence
                                            :element (make-type-defined
                                                      :name (make-identifier :name "edge"))))
                              :arguments (list (make-expression-variable
                                                :name (make-identifier :name "e"))
                                               (make-expression-call
                                                :function (make-identifier :name "path")
                                                :types (list)
                                                :arguments (list (make-expression-call
                                                                  :function (make-identifier :name "rest")
                                                                  :types (list (make-type-sequence
                                                                                :element (make-type-defined
                                                                                          :name (make-identifier :name "point"))))
                                                                  :arguments (list (make-expression-variable
                                                                                    :name (make-identifier :name "vertices"))))))))))
         :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "not_empty_path")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-binary
                                 :operator (make-binary-op-and)
                                 :left-operand (make-expression-unary
                                                :operator (make-unary-op-not)
                                                :operand (make-expression-call
                                                          :function (make-identifier :name "is_empty")
                                                          :types (list (make-type-sequence
                                                                        :element (make-type-defined
                                                                                  :name (make-identifier :name "point"))))
                                                          :arguments (list (make-expression-variable
                                                                            :name (make-identifier :name "vertices")))))
                                 :right-operand (make-expression-unary
                                                 :operator (make-unary-op-not)
                                                 :operand (make-expression-call
                                                           :function (make-identifier :name "is_empty")
                                                           :types (list (make-type-sequence
                                                                         :element (make-type-defined
                                                                                   :name (make-identifier :name "point"))))
                                                           :arguments (list (make-expression-call
                                                                             :function (make-identifier :name "rest")
                                                                             :types (list (make-type-sequence
                                                                                           :element (make-type-defined
                                                                                                     :name (make-identifier :name "point"))))
                                                                             :arguments (list (make-expression-variable
                                                                                               :name (make-identifier :name "vertices"))))))))
                  :right-operand (make-expression-unary
                                  :operator (make-unary-op-not)
                                  :operand (make-expression-call
                                            :function (make-identifier :name "is_empty")
                                            :types (list (make-type-sequence
                                                          :element (make-type-defined
                                                                    :name (make-identifier :name "edge"))))
                                            :arguments (list (make-expression-call
                                                              :function (make-identifier :name "path")
                                                              :types (list)
                                                              :arguments (list (make-expression-variable
                                                                                :name (make-identifier :name "vertices")))))))))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "length_path")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-unary
                                 :operator (make-unary-op-not)
                                 :operand (make-expression-call
                                           :function (make-identifier :name "is_empty")
                                           :types (list (make-type-sequence
                                                         :element (make-type-defined
                                                                   :name (make-identifier :name "point"))))
                                           :arguments (list (make-expression-variable
                                                             :name (make-identifier :name "vertices")))))
                  :right-operand (make-expression-binary
                                  :operator (make-binary-op-eq)
                                  :left-operand (make-expression-call
                                                 :function (make-identifier :name "length")
                                                 :types (list (make-type-sequence
                                                               :element (make-type-defined
                                                                         :name (make-identifier :name "edge"))))
                                                 :arguments (list (make-expression-call
                                                                   :function (make-identifier :name "path")
                                                                   :types (list)
                                                                   :arguments (list (make-expression-variable
                                                                                     :name (make-identifier :name "vertices"))))))
                                  :right-operand (make-expression-binary
                                                  :operator (make-binary-op-sub)
                                                  :left-operand (make-expression-call
                                                                 :function (make-identifier :name "length")
                                                                 :types (list (make-type-sequence
                                                                               :element (make-type-defined
                                                                                         :name (make-identifier :name "point"))))
                                                                 :arguments (list (make-expression-variable
                                                                                   :name (make-identifier :name "vertices"))))
                                                  :right-operand (make-expression-literal
                                                                  :get (make-literal-integer
                                                                        :value 1))))))))


#|
function points2_p (vertices:seq<point>) returns (b: bool) {
  return is_empty(vertices) || !is_empty(rest(vertices));
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "points2_p")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "vertices")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-binary
                         :operator (make-binary-op-or)
                         :left-operand (make-expression-call
                                        :function (make-identifier :name "is_empty")
                                        :types (list (make-type-sequence
                                                      :element (make-type-defined
                                                                :name (make-identifier :name "point"))))
                                        :arguments (list (make-expression-variable
                                                          :name (make-identifier :name "vertices"))))
                         :right-operand (make-expression-unary
                                         :operator (make-unary-op-not)
                                         :operand (make-expression-call
                                                   :function (make-identifier :name "is_empty")
                                                   :types (list (make-type-sequence
                                                                 :element (make-type-defined
                                                                           :name (make-identifier :name "point"))))
                                                   :arguments (list (make-expression-call
                                                                     :function (make-identifier :name "rest")
                                                                     :types (list (make-type-sequence
                                                                                   :element (make-type-defined
                                                                                             :name (make-identifier :name "point"))))
                                                                     :arguments (list (make-expression-variable
                                                                                       :name (make-identifier :name "vertices"))))))))
                  :measure nil))))

#|
function path_vertices(edges:seq<edge>) returns (vertices:seq<point>) ensures points2_p(vertices) {
  if (is_empty(edges)) {
    return empty;
  }
  else {
  let e:edge = first(edges);
  if (is_empty(rest(edges))) {
    return add(e.p1, add(e.p2, empty));
  }
  else {
    return add(e.p1, path_vertices(rest(edges)));
  }
  }
}

/* Inversion Theorems */
theorem path_vertices_of_path
  forall(vertices:seq<point>)
    points2_p(vertices)
      ==> path_vertices(path(vertices)) == vertices

theorem path_of_path_vertices
  forall(edges:seq<edge>)
    path_p(edges)
      ==> path(path_vertices(edges)) == edges
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "path_vertices")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "edges")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "edge")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "vertices")
                                 :type (make-type-sequence
                                        :element (make-type-defined
                                                  :name (make-identifier :name "point"))))))
        :precondition nil
        :postcondition (make-expression-call
                        :function (make-identifier :name "points2_p")
                        :types (list)
                        :arguments (list (make-expression-variable
                                          :name (make-identifier :name "vertices"))))
        :definer
        (make-function-definer-regular
         :body (make-expression-if
                :test (make-expression-call
                       :function (make-identifier :name "is_empty")
                       :types (list (make-type-sequence
                                     :element (make-type-defined
                                               :name (make-identifier :name "edge"))))
                       :arguments (list (make-expression-variable
                                         :name (make-identifier :name "edges"))))
                :then (make-expression-call
                       :function (make-identifier :name "empty")
                       :types (list (make-type-sequence
                                     :element (make-type-defined
                                               :name (make-identifier :name "point"))))
                       :arguments (list))
                :else (make-expression-bind
                       :variables (list (make-typed-variable
                                         :name (make-identifier :name "e")
                                         :type (make-type-defined
                                                :name (make-identifier :name "edge"))))
                       :value (make-expression-call
                               :function (make-identifier :name "first")
                               :types (list (make-type-sequence
                                             :element (make-type-defined
                                                       :name (make-identifier :name "edge"))))
                               :arguments (list (make-expression-variable
                                                 :name (make-identifier :name "edges"))))
                       :body (make-expression-if
                              :test (make-expression-call
                                     :function (make-identifier :name "is_empty")
                                     :types (list (make-type-sequence
                                                   :element (make-type-defined
                                                             :name (make-identifier :name "edge"))))
                                     :arguments (list (make-expression-call
                                                       :function (make-identifier :name "rest")
                                                       :types (list (make-type-sequence
                                                                     :element (make-type-defined
                                                                               :name (make-identifier :name "edge"))))
                                                       :arguments (list (make-expression-variable
                                                                         :name (make-identifier :name "edges"))))))
                              :then (make-expression-call
                                     :function (make-identifier :name "add")
                                     :types (list (make-type-sequence
                                                   :element (make-type-defined
                                                             :name (make-identifier :name "point"))))
                                     :arguments (list (make-expression-product-field
                                                       :type (make-identifier :name "edge")
                                                       :target (make-expression-variable
                                                                :name (make-identifier :name "e"))
                                                       :field (make-identifier :name "p1"))
                                                      (make-expression-call
                                                       :function (make-identifier :name "add")
                                                       :types (list (make-type-sequence
                                                                     :element (make-type-defined
                                                                               :name (make-identifier :name "point"))))
                                                       :arguments (list (make-expression-product-field
                                                                         :type (make-identifier :name "edge")
                                                                         :target (make-expression-variable
                                                                                  :name (make-identifier :name "e"))
                                                                         :field (make-identifier :name "p2"))
                                                                        (make-expression-call
                                                                         :function (make-identifier :name "empty")
                                                                         :types (list (make-type-sequence
                                                                                       :element (make-type-defined
                                                                                                 :name (make-identifier :name "point"))))
                                                                         :arguments (list))))))
                              :else (make-expression-call
                                     :function (make-identifier :name "add")
                                     :types (list (make-type-sequence
                                                   :element (make-type-defined
                                                             :name (make-identifier :name "point"))))
                                     :arguments (list (make-expression-product-field
                                                       :type (make-identifier :name "edge")
                                                       :target (make-expression-variable
                                                                :name (make-identifier :name "e"))
                                                       :field (make-identifier :name "p1"))
                                                      (make-expression-call
                                                       :function (make-identifier :name "path_vertices")
                                                       :types (list)
                                                       :arguments (list (make-expression-call
                                                                         :function (make-identifier :name "rest")
                                                                         :types (list (make-type-sequence
                                                                                       :element (make-type-defined
                                                                                                 :name (make-identifier :name "edge"))))
                                                                         :arguments (list (make-expression-variable
                                                                                           :name (make-identifier :name "edges")))))))))))
         :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "path_vertices_of_path")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-call
                                 :function (make-identifier :name "points2_p")
                                 :types (list)
                                 :arguments (list (make-expression-variable
                                                   :name (make-identifier :name "vertices"))))
                  :right-operand (make-expression-binary
                                  :operator (make-binary-op-eq)
                                  :left-operand (make-expression-call
                                                 :function (make-identifier :name "path_vertices")
                                                 :types (list)
                                                 :arguments (list (make-expression-call
                                                                   :function (make-identifier :name "path")
                                                                   :types (list)
                                                                   :arguments (list (make-expression-variable
                                                                                     :name (make-identifier :name "vertices"))))))
                                  :right-operand (make-expression-variable
                                                  :name (make-identifier :name "vertices")))))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "path_of_path_vertices")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "edges")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "edge")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-call
                                 :function (make-identifier :name "path_p")
                                 :types (list)
                                 :arguments (list (make-expression-variable
                                                   :name (make-identifier :name "edges"))))
                  :right-operand (make-expression-binary
                                  :operator (make-binary-op-eq)
                                  :left-operand (make-expression-call
                                                 :function (make-identifier :name "path")
                                                 :types (list)
                                                 :arguments (list (make-expression-call
                                                                   :function (make-identifier :name "path_vertices")
                                                                   :types (list)
                                                                   :arguments (list (make-expression-variable
                                                                                     :name (make-identifier :name "edges"))))))
                                  :right-operand (make-expression-variable
                                                  :name (make-identifier :name "edges")))))))

#|
function append_first(vertices:seq<point>) assumes !is_empty(vertices) 
  returns (s: seq<point>) ensures points2_p(s) {
  return append(vertices, add(first(vertices), empty));
}
// Given a list of points, return the list of edges
// that connect the points in sequence, then connect
// the last point to the first point.
function edges(vertices: seq<point>) returns (p: seq<edge>) ensures path_p(p) {
  if (is_empty(vertices)) {
    return empty;
  }
  else {
    return path(append_first(vertices));
  }
}

theorem path_vertices_of_edges
  forall(vertices:seq<point>)
   !is_empty(vertices)
    ==> path_vertices(edges(vertices)) == append_first(vertices)
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "append_first")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "vertices")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "s")
                                 :type (make-type-sequence
                                        :element (make-type-defined
                                                  :name (make-identifier :name "point"))))))
        :precondition (make-expression-unary
                       :operator (make-unary-op-not)
                       :operand (make-expression-call
                                 :function (make-identifier :name "is_empty")
                                 :types (list (make-type-sequence
                                               :element (make-type-defined
                                                         :name (make-identifier :name "point"))))
                                 :arguments (list (make-expression-variable
                                                   :name (make-identifier :name "vertices")))))
        :postcondition (make-expression-call
                        :function (make-identifier :name "points2_p")
                        :types (list)
                        :arguments (list (make-expression-variable
                                          :name (make-identifier :name "s"))))
        :definer (make-function-definer-regular
                  :body (make-expression-call
                         :function (make-identifier :name "append")
                         :types (list (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point"))))
                         :arguments (list (make-expression-variable
                                           :name (make-identifier :name "vertices"))
                                          (make-expression-call
                                           :function (make-identifier :name "add")
                                           :types (list (make-type-sequence
                                                         :element (make-type-defined
                                                                   :name (make-identifier :name "point"))))
                                           :arguments (list (make-expression-call
                                                             :function (make-identifier :name "first")
                                                             :types (list (make-type-sequence
                                                                           :element (make-type-defined
                                                                                     :name (make-identifier :name "point"))))
                                                             :arguments (list (make-expression-variable
                                                                               :name (make-identifier :name "vertices"))))
                                                            (make-expression-call
                                                             :function (make-identifier :name "empty")
                                                             :types (list (make-type-sequence
                                                                           :element (make-type-defined
                                                                                     :name (make-identifier :name "point"))))
                                                             :arguments (list))))))
                  :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "edges")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "vertices")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "p")
                                 :type (make-type-sequence
                                        :element (make-type-defined
                                                  :name (make-identifier :name "edge"))))))
        :precondition nil
        :postcondition (make-expression-call
                        :function (make-identifier :name "path_p")
                        :types (list)
                        :arguments (list (make-expression-variable
                                          :name (make-identifier :name "p"))))
        :definer (make-function-definer-regular
                  :body (make-expression-if
                         :test (make-expression-call
                                :function (make-identifier :name "is_empty")
                                :types (list (make-type-sequence
                                              :element (make-type-defined
                                                        :name (make-identifier :name "point"))))
                                :arguments (list (make-expression-variable
                                                  :name (make-identifier :name "vertices"))))
                         :then (make-expression-call
                                :function (make-identifier :name "empty")
                                :types (list (make-type-sequence
                                              :element (make-type-defined
                                                        :name (make-identifier :name "edge"))))
                                :arguments (list))
                         :else (make-expression-call
                                :function (make-identifier :name "path")
                                :types (list)
                                :arguments (list (make-expression-call
                                                  :function (make-identifier :name "append_first")
                                                  :types (list)
                                                  :arguments (list (make-expression-variable
                                                                    :name (make-identifier :name "vertices")))))))
                  :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "path_vertices_of_edges")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-unary
                                 :operator (make-unary-op-not)
                                 :operand (make-expression-call
                                           :function (make-identifier :name "is_empty")
                                           :types (list (make-type-sequence
                                                         :element (make-type-defined
                                                                   :name (make-identifier :name "point"))))
                                           :arguments (list (make-expression-variable
                                                             :name (make-identifier :name "vertices")))))
                  :right-operand (make-expression-binary
                                  :operator (make-binary-op-eq)
                                  :left-operand (make-expression-call
                                                 :function (make-identifier :name "path_vertices")
                                                 :types (list)
                                                 :arguments (list (make-expression-call
                                                                   :function (make-identifier :name "edges")
                                                                   :types (list)
                                                                   :arguments (list (make-expression-variable
                                                                                     :name (make-identifier :name "vertices"))))))
                                  :right-operand (make-expression-call
                                                  :function (make-identifier :name "append_first")
                                                  :types (list)
                                                  :arguments (list (make-expression-variable
                                                                    :name (make-identifier :name "vertices")))))))))


#|
// Orientation of an ordered triplet of points in the plane can be
//   . clockwise
//   . counterclockwise, or
//   . colinear
// It can be computed by the sign of the expression
//   (p2.y - p1.y) * (p3.x - p2.x) - (p3.y - p2.y) * (p2.y - p1.x)
// If the expression is positive, the orientation is counterclockwise
// If the expression is 0, the orientation is collinear
// If the expression is negative the orientation is counterclockwise
// (See https://www.geeksforgeeks.org/orientation-3-ordered-points/
// for some explanations on this concept)

variant orientation {clockwise, counterclockwise, colinear}
|#

(process-syntheto-toplevel
 (make-toplevel-type
  :get (make-type-definition
        :name (make-identifier :name "orientation")
        :body (make-type-definer-sum
               :get (make-type-sum
                     :alternatives (list (make-alternative
                                          :name (make-identifier :name "clockwise")
                                          :product (make-type-product
                                                    :fields (list)
                                                    :invariant nil))
                                         (make-alternative
                                          :name (make-identifier :name "counterclockwise")
                                          :product (make-type-product
                                                    :fields (list)
                                                    :invariant nil))
                                         (make-alternative
                                          :name (make-identifier :name "colinear")
                                          :product (make-type-product
                                                    :fields (list)
                                                    :invariant nil))))))))

#|
function orientation3(p1: point, p2: point, p3: point) returns (o: orientation) {
  if (p1 == p2 || p2 == p3 || p2 == p3) {
    return orientation.colinear;
  }
  else {
    let e: int = (p2.y - p1.y) * (p3.x - p2.x) - (p3.y - p2.y) * (p2.y - p1.x);
    if (e < 0) {
      return orientation.counterclockwise;
    }
    else {if (e == 0) {
      return orientation.colinear;
    }
    else {
      return orientation.clockwise;
    }}}
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "orientation3")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "p1")
                                :type (make-type-defined
                                       :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p2")
                                :type (make-type-defined
                                       :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p3")
                                :type (make-type-defined
                                       :name (make-identifier :name "point"))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "o")
                                 :type (make-type-defined
                                        :name (make-identifier :name "orientation")))))
        :precondition nil
        :postcondition nil
        :definer
        (make-function-definer-regular
         :body (make-expression-if
                :test (make-expression-binary
                       :operator (make-binary-op-or)
                       :left-operand (make-expression-binary
                                      :operator (make-binary-op-or)
                                      :left-operand (make-expression-binary
                                                     :operator (make-binary-op-eq)
                                                     :left-operand (make-expression-variable
                                                                    :name (make-identifier :name "p1"))
                                                     :right-operand (make-expression-variable
                                                                     :name (make-identifier :name "p2")))
                                      :right-operand (make-expression-binary
                                                      :operator (make-binary-op-eq)
                                                      :left-operand (make-expression-variable
                                                                     :name (make-identifier :name "p2"))
                                                      :right-operand (make-expression-variable
                                                                      :name (make-identifier :name "p3"))))
                       :right-operand (make-expression-binary
                                       :operator (make-binary-op-eq)
                                       :left-operand (make-expression-variable
                                                      :name (make-identifier :name "p2"))
                                       :right-operand (make-expression-variable
                                                       :name (make-identifier :name "p3"))))
                :then (make-expression-sum-construct
                       :type (make-identifier :name "orientation")
                       :alternative (make-identifier :name "colinear")
                       :fields (list))
                :else
                (make-expression-bind
                 :variables (list (make-typed-variable
                                   :name (make-identifier :name "e")
                                   :type (make-type-integer)))
                 :value (make-expression-binary
                         :operator (make-binary-op-sub)
                         :left-operand (make-expression-binary
                                        :operator (make-binary-op-mul)
                                        :left-operand (make-expression-binary
                                                       :operator (make-binary-op-sub)
                                                       :left-operand (make-expression-product-field
                                                                      :type (make-identifier :name "point")
                                                                      :target (make-expression-variable
                                                                               :name (make-identifier :name "p2"))
                                                                      :field (make-identifier :name "y"))
                                                       :right-operand (make-expression-product-field
                                                                       :type (make-identifier :name "point")
                                                                       :target (make-expression-variable
                                                                                :name (make-identifier :name "p1"))
                                                                       :field (make-identifier :name "y")))
                                        :right-operand (make-expression-binary
                                                        :operator (make-binary-op-sub)
                                                        :left-operand (make-expression-product-field
                                                                       :type (make-identifier :name "point")
                                                                       :target (make-expression-variable
                                                                                :name (make-identifier :name "p3"))
                                                                       :field (make-identifier :name "x"))
                                                        :right-operand (make-expression-product-field
                                                                        :type (make-identifier :name "point")
                                                                        :target (make-expression-variable
                                                                                 :name (make-identifier :name "p2"))
                                                                        :field (make-identifier :name "x"))))
                         :right-operand (make-expression-binary
                                         :operator (make-binary-op-mul)
                                         :left-operand (make-expression-binary
                                                        :operator (make-binary-op-sub)
                                                        :left-operand (make-expression-product-field
                                                                       :type (make-identifier :name "point")
                                                                       :target (make-expression-variable
                                                                                :name (make-identifier :name "p3"))
                                                                       :field (make-identifier :name "y"))
                                                        :right-operand (make-expression-product-field
                                                                        :type (make-identifier :name "point")
                                                                        :target (make-expression-variable
                                                                                 :name (make-identifier :name "p2"))
                                                                        :field (make-identifier :name "y")))
                                         :right-operand (make-expression-binary
                                                         :operator (make-binary-op-sub)
                                                         :left-operand (make-expression-product-field
                                                                        :type (make-identifier :name "point")
                                                                        :target (make-expression-variable
                                                                                 :name (make-identifier :name "p2"))
                                                                        :field (make-identifier :name "y"))
                                                         :right-operand (make-expression-product-field
                                                                         :type (make-identifier :name "point")
                                                                         :target (make-expression-variable
                                                                                  :name (make-identifier :name "p1"))
                                                                         :field (make-identifier :name "x")))))
                 :body (make-expression-if
                        :test (make-expression-binary
                               :operator (make-binary-op-lt)
                               :left-operand (make-expression-variable
                                              :name (make-identifier :name "e"))
                               :right-operand (make-expression-literal
                                               :get (make-literal-integer
                                                     :value 0)))
                        :then (make-expression-sum-construct
                               :type (make-identifier :name "orientation")
                               :alternative (make-identifier :name "counterclockwise")
                               :fields (list))
                        :else (make-expression-if
                               :test (make-expression-binary
                                      :operator (make-binary-op-eq)
                                      :left-operand (make-expression-variable
                                                     :name (make-identifier :name "e"))
                                      :right-operand (make-expression-literal
                                                      :get (make-literal-integer
                                                            :value 0)))
                               :then (make-expression-sum-construct
                                      :type (make-identifier :name "orientation")
                                      :alternative (make-identifier :name "colinear")
                                      :fields (list))
                               :else (make-expression-sum-construct
                                      :type (make-identifier :name "orientation")
                                      :alternative (make-identifier :name "clockwise")
                                      :fields (list))))))
         :measure nil))))
#|
function collinear(p1: point, p2: point, p3: point) returns (b:bool) {
  return orientation3(p1,p2,p3) == orientation.colinear;
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "collinear")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "p1")
                                :type (make-type-defined :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p2")
                                :type (make-type-defined :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p3")
                                :type (make-type-defined :name (make-identifier :name "point"))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-binary
                         :operator (make-binary-op-eq)
                         :left-operand
                         (make-expression-call
                          :function (make-identifier :name "orientation3")
                          :types (list)
                          :arguments (list (make-expression-variable
                                            :name (make-identifier :name "p1"))
                                           (make-expression-variable
                                            :name (make-identifier :name "p2"))
                                           (make-expression-variable
                                            :name (make-identifier :name "p3"))))
                         :right-operand
                         (make-expression-sum-construct
                          :type (make-identifier :name "orientation")
                          :alternative (make-identifier :name "colinear")
                          :fields (list)))))))

 

#|
function on_segment(p1: point, p2: point, p3: point) returns (b: bool) {
  return p3.x >= min(p1.x, p2.x)
           && p3.x <= max(p1.x, p2.x)
           && p3.y >= min(p1.y, p2.y)
           && p3.y <= max(p1.y, p2.y);
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "on_segment")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "p1")
                                :type (make-type-defined
                                       :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p2")
                                :type (make-type-defined
                                       :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p3")
                                :type (make-type-defined
                                       :name (make-identifier :name "point"))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer
        (make-function-definer-regular
         :body (make-expression-binary
                :operator (make-binary-op-and)
                :left-operand
                (make-expression-binary
                 :operator (make-binary-op-and)
                 :left-operand
                 (make-expression-binary
                  :operator (make-binary-op-and)
                  :left-operand (make-expression-binary
                                 :operator (make-binary-op-ge)
                                 :left-operand (make-expression-product-field
                                                :type (make-identifier :name "point")
                                                :target (make-expression-variable
                                                         :name (make-identifier :name "p3"))
                                                :field (make-identifier :name "x"))
                                 :right-operand (make-expression-call
                                                 :function (make-identifier :name "min")
                                                 :types (list)
                                                 :arguments (list (make-expression-product-field
                                                                   :type (make-identifier :name "point")
                                                                   :target (make-expression-variable
                                                                            :name (make-identifier :name "p1"))
                                                                   :field (make-identifier :name "x"))
                                                                  (make-expression-product-field
                                                                   :type (make-identifier :name "point")
                                                                   :target (make-expression-variable
                                                                            :name (make-identifier :name "p2"))
                                                                   :field (make-identifier :name "x")))))
                  :right-operand (make-expression-binary
                                  :operator (make-binary-op-le)
                                  :left-operand (make-expression-product-field
                                                 :type (make-identifier :name "point")
                                                 :target (make-expression-variable
                                                          :name (make-identifier :name "p3"))
                                                 :field (make-identifier :name "x"))
                                  :right-operand (make-expression-call
                                                  :function (make-identifier :name "max")
                                                  :types (list)
                                                  :arguments (list (make-expression-product-field
                                                                    :type (make-identifier :name "point")
                                                                    :target (make-expression-variable
                                                                             :name (make-identifier :name "p1"))
                                                                    :field (make-identifier :name "x"))
                                                                   (make-expression-product-field
                                                                    :type (make-identifier :name "point")
                                                                    :target (make-expression-variable
                                                                             :name (make-identifier :name "p2"))
                                                                    :field (make-identifier :name "x"))))))
                 :right-operand (make-expression-binary
                                 :operator (make-binary-op-ge)
                                 :left-operand (make-expression-product-field
                                                :type (make-identifier :name "point")
                                                :target (make-expression-variable
                                                         :name (make-identifier :name "p3"))
                                                :field (make-identifier :name "y"))
                                 :right-operand (make-expression-call
                                                 :function (make-identifier :name "min")
                                                 :types (list)
                                                 :arguments (list (make-expression-product-field
                                                                   :type (make-identifier :name "point")
                                                                   :target (make-expression-variable
                                                                            :name (make-identifier :name "p1"))
                                                                   :field (make-identifier :name "y"))
                                                                  (make-expression-product-field
                                                                   :type (make-identifier :name "point")
                                                                   :target (make-expression-variable
                                                                            :name (make-identifier :name "p2"))
                                                                   :field (make-identifier :name "y"))))))
                :right-operand (make-expression-binary
                                :operator (make-binary-op-le)
                                :left-operand (make-expression-product-field
                                               :type (make-identifier :name "point")
                                               :target (make-expression-variable
                                                        :name (make-identifier :name "p3"))
                                               :field (make-identifier :name "y"))
                                :right-operand (make-expression-call
                                                :function (make-identifier :name "max")
                                                :types (list)
                                                :arguments (list (make-expression-product-field
                                                                  :type (make-identifier :name "point")
                                                                  :target (make-expression-variable
                                                                           :name (make-identifier :name "p1"))
                                                                  :field (make-identifier :name "y"))
                                                                 (make-expression-product-field
                                                                  :type (make-identifier :name "point")
                                                                  :target (make-expression-variable
                                                                           :name (make-identifier :name "p2"))
                                                                  :field (make-identifier :name "y"))))))
         :measure nil))))

#|
// return true when edge1 and edge1 intersect
// see https://www.geeksforgeeks.org/check-if-two-given-line-segments-intersect/
function edge_points_intersect(p11:point, p12:point, p21:point, p22:point) returns (b: bool) {
  let o1: orientation = orientation3(p11, p12, p21);
  let o2: orientation = orientation3(p11, p12, p22);
  let o3: orientation = orientation3(p21, p22, p11);
  let o4: orientation = orientation3(p21, p22, p12);
  return ((o1 != o2 && o3 != o4)   // Non colinear case
           // Special cases
           || (o1 == orientation.colinear && on_segment(p11, p12, p21))
           || (o2 == orientation.colinear && on_segment(p11, p12, p22))
           || (o3 == orientation.colinear && on_segment(p21, p22, p11))
           || (o4 == orientation.colinear && on_segment(p21, p22, p12)));
}

function edges_intersect(edge1: edge, edge2: edge) returns (b: bool) {
  return edge_points_intersect(edge1.p1, edge1.p2, edge2.p1, edge2.p2);
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "edge_points_intersect")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "p11")
                                :type (make-type-defined
                                       :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p12")
                                :type (make-type-defined
                                       :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p21")
                                :type (make-type-defined
                                       :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "p22")
                                :type (make-type-defined
                                       :name (make-identifier :name "point"))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer
        (make-function-definer-regular
         :body (make-expression-bind
                :variables (list (make-typed-variable
                                  :name (make-identifier :name "o1")
                                  :type (make-type-defined
                                         :name (make-identifier :name "orientation"))))
                :value (make-expression-call
                        :function (make-identifier :name "orientation3")
                        :types (list)
                        :arguments (list (make-expression-variable
                                          :name (make-identifier :name "p11"))
                                         (make-expression-variable
                                          :name (make-identifier :name "p12"))
                                         (make-expression-variable
                                          :name (make-identifier :name "p21"))))
                :body
                (make-expression-bind
                 :variables (list (make-typed-variable
                                   :name (make-identifier :name "o2")
                                   :type (make-type-defined
                                          :name (make-identifier :name "orientation"))))
                 :value (make-expression-call
                         :function (make-identifier :name "orientation3")
                         :types (list)
                         :arguments (list (make-expression-variable
                                           :name (make-identifier :name "p11"))
                                          (make-expression-variable
                                           :name (make-identifier :name "p12"))
                                          (make-expression-variable
                                           :name (make-identifier :name "p22"))))
                 :body
                 (make-expression-bind
                  :variables (list (make-typed-variable
                                    :name (make-identifier :name "o3")
                                    :type (make-type-defined
                                           :name (make-identifier :name "orientation"))))
                  :value (make-expression-call
                          :function (make-identifier :name "orientation3")
                          :types (list)
                          :arguments (list (make-expression-variable
                                            :name (make-identifier :name "p21"))
                                           (make-expression-variable
                                            :name (make-identifier :name "p22"))
                                           (make-expression-variable
                                            :name (make-identifier :name "p11"))))
                  :body
                  (make-expression-bind
                   :variables (list (make-typed-variable
                                     :name (make-identifier :name "o4")
                                     :type (make-type-defined
                                            :name (make-identifier :name "orientation"))))
                   :value (make-expression-call
                           :function (make-identifier :name "orientation3")
                           :types (list)
                           :arguments (list (make-expression-variable
                                             :name (make-identifier :name "p21"))
                                            (make-expression-variable
                                             :name (make-identifier :name "p22"))
                                            (make-expression-variable
                                             :name (make-identifier :name "p12"))))
                   :body
                   (make-expression-binary
                    :operator (make-binary-op-or)
                    :left-operand
                    (make-expression-binary
                     :operator (make-binary-op-or)
                     :left-operand
                     (make-expression-binary
                      :operator (make-binary-op-or)
                      :left-operand
                      (make-expression-binary
                       :operator (make-binary-op-or)
                       :left-operand
                       (make-expression-binary
                        :operator (make-binary-op-and)
                        :left-operand (make-expression-binary
                                       :operator (make-binary-op-ne)
                                       :left-operand (make-expression-variable
                                                      :name (make-identifier :name "o1"))
                                       :right-operand (make-expression-variable
                                                       :name (make-identifier :name "o2")))
                        :right-operand (make-expression-binary
                                        :operator (make-binary-op-ne)
                                        :left-operand (make-expression-variable
                                                       :name (make-identifier :name "o3"))
                                        :right-operand (make-expression-variable
                                                        :name (make-identifier :name "o4"))))
                       :right-operand (make-expression-binary
                                       :operator (make-binary-op-and)
                                       :left-operand (make-expression-binary
                                                      :operator (make-binary-op-eq)
                                                      :left-operand (make-expression-variable
                                                                     :name (make-identifier :name "o1"))
                                                      :right-operand (make-expression-sum-construct
                                                                      :type (make-identifier :name "orientation")
                                                                      :alternative (make-identifier :name "colinear")
                                                                      :fields (list)))
                                       :right-operand (make-expression-call
                                                       :function (make-identifier :name "on_segment")
                                                       :types (list)
                                                       :arguments (list (make-expression-variable
                                                                         :name (make-identifier :name "p11"))
                                                                        (make-expression-variable
                                                                         :name (make-identifier :name "p12"))
                                                                        (make-expression-variable
                                                                         :name (make-identifier :name "p21"))))))
                      :right-operand (make-expression-binary
                                      :operator (make-binary-op-and)
                                      :left-operand (make-expression-binary
                                                     :operator (make-binary-op-eq)
                                                     :left-operand (make-expression-variable
                                                                    :name (make-identifier :name "o2"))
                                                     :right-operand (make-expression-sum-construct
                                                                     :type (make-identifier :name "orientation")
                                                                     :alternative (make-identifier :name "colinear")
                                                                     :fields (list)))
                                      :right-operand (make-expression-call
                                                      :function (make-identifier :name "on_segment")
                                                      :types (list)
                                                      :arguments (list (make-expression-variable
                                                                        :name (make-identifier :name "p11"))
                                                                       (make-expression-variable
                                                                        :name (make-identifier :name "p12"))
                                                                       (make-expression-variable
                                                                        :name (make-identifier :name "p22"))))))
                     :right-operand
                     (make-expression-binary
                      :operator (make-binary-op-and)
                      :left-operand (make-expression-binary
                                     :operator (make-binary-op-eq)
                                     :left-operand (make-expression-variable
                                                    :name (make-identifier :name "o3"))
                                     :right-operand (make-expression-sum-construct
                                                     :type (make-identifier :name "orientation")
                                                     :alternative (make-identifier :name "colinear")
                                                     :fields (list)))
                      :right-operand
                      (make-expression-call
                       :function (make-identifier :name "on_segment")
                       :types (list)
                       :arguments (list (make-expression-variable
                                         :name (make-identifier :name "p21"))
                                        (make-expression-variable
                                         :name (make-identifier :name "p22"))
                                        (make-expression-variable
                                         :name (make-identifier :name "p11"))))))
                    :right-operand (make-expression-binary
                                    :operator (make-binary-op-and)
                                    :left-operand (make-expression-binary
                                                   :operator (make-binary-op-eq)
                                                   :left-operand (make-expression-variable
                                                                  :name (make-identifier :name "o4"))
                                                   :right-operand (make-expression-sum-construct
                                                                   :type (make-identifier :name "orientation")
                                                                   :alternative (make-identifier :name "colinear")
                                                                   :fields (list)))
                                    :right-operand (make-expression-call
                                                    :function (make-identifier :name "on_segment")
                                                    :types (list)
                                                    :arguments (list (make-expression-variable
                                                                      :name (make-identifier :name "p21"))
                                                                     (make-expression-variable
                                                                      :name (make-identifier :name "p22"))
                                                                     (make-expression-variable
                                                                      :name (make-identifier :name "p12"))))))))))
         :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "edges_intersect")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "edge1")
                                :type (make-type-defined
                                       :name (make-identifier :name "edge")))
                               (make-typed-variable
                                :name (make-identifier :name "edge2")
                                :type (make-type-defined
                                       :name (make-identifier :name "edge"))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-call
                         :function (make-identifier :name "edge_points_intersect")
                         :types (list)
                         :arguments (list (make-expression-product-field
                                           :type (make-identifier :name "edge")
                                           :target (make-expression-variable
                                                    :name (make-identifier :name "edge1"))
                                           :field (make-identifier :name "p1"))
                                          (make-expression-product-field
                                           :type (make-identifier :name "edge")
                                           :target (make-expression-variable
                                                    :name (make-identifier :name "edge1"))
                                           :field (make-identifier :name "p2"))
                                          (make-expression-product-field
                                           :type (make-identifier :name "edge")
                                           :target (make-expression-variable
                                                    :name (make-identifier :name "edge2"))
                                           :field (make-identifier :name "p1"))
                                          (make-expression-product-field
                                           :type (make-identifier :name "edge")
                                           :target (make-expression-variable
                                                    :name (make-identifier :name "edge2"))
                                           :field (make-identifier :name "p2"))))
                  :measure nil))))  

#|
// return true when no three adjacent points in a list are collinear
function adjacent_three_points_not_collinear(vertices: seq<point>) returns (b: bool) {
  if (is_empty(vertices) || is_empty(rest(vertices)) || is_empty(rest(rest(vertices)))) {
    return true;
  }
  else {
    return ! collinear(first(vertices),
                       first(rest(vertices)),
                       first(rest(rest(vertices))))
            && (adjacent_three_points_not_collinear(rest(vertices)));
  }
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "adjacent_three_points_not_collinear")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "vertices")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer
        (make-function-definer-regular
         :body (make-expression-if
                :test (make-expression-binary
                       :operator (make-binary-op-or)
                       :left-operand (make-expression-binary
                                      :operator (make-binary-op-or)
                                      :left-operand (make-expression-call
                                                     :function (make-identifier :name "is_empty")
                                                     :types (list (make-type-sequence
                                                                   :element (make-type-defined
                                                                             :name (make-identifier :name "point"))))
                                                     :arguments (list (make-expression-variable
                                                                       :name (make-identifier :name "vertices"))))
                                      :right-operand (make-expression-call
                                                      :function (make-identifier :name "is_empty")
                                                      :types (list (make-type-sequence
                                                                    :element (make-type-defined
                                                                              :name (make-identifier :name "point"))))
                                                      :arguments (list (make-expression-call
                                                                        :function (make-identifier :name "rest")
                                                                        :types (list (make-type-sequence
                                                                                      :element (make-type-defined
                                                                                                :name (make-identifier :name "point"))))
                                                                        :arguments (list (make-expression-variable
                                                                                          :name (make-identifier :name "vertices")))))))
                       :right-operand (make-expression-call
                                       :function (make-identifier :name "is_empty")
                                       :types (list (make-type-sequence
                                                     :element (make-type-defined
                                                               :name (make-identifier :name "point"))))
                                       :arguments (list (make-expression-call
                                                         :function (make-identifier :name "rest")
                                                         :types (list (make-type-sequence
                                                                       :element (make-type-defined
                                                                                 :name (make-identifier :name "point"))))
                                                         :arguments (list (make-expression-call
                                                                           :function (make-identifier :name "rest")
                                                                           :types (list (make-type-sequence
                                                                                         :element (make-type-defined
                                                                                                   :name (make-identifier :name "point"))))
                                                                           :arguments (list (make-expression-variable
                                                                                             :name (make-identifier :name "vertices")))))))))
                :then (make-expression-literal
                       :get (make-literal-boolean
                             :value t))
                :else
                (make-expression-binary
                 :operator (make-binary-op-and)
                 :left-operand
                 (make-expression-unary
                  :operator (make-unary-op-not)
                  :operand (make-expression-call
                            :function (make-identifier :name "collinear")
                            :types (list)
                            :arguments (list (make-expression-call
                                              :function (make-identifier :name "first")
                                              :types (list (make-type-sequence
                                                            :element (make-type-defined
                                                                      :name (make-identifier :name "point"))))
                                              :arguments (list (make-expression-variable
                                                                :name (make-identifier :name "vertices"))))
                                             (make-expression-call
                                              :function (make-identifier :name "first")
                                              :types (list (make-type-sequence
                                                            :element (make-type-defined
                                                                      :name (make-identifier :name "point"))))
                                              :arguments (list (make-expression-call
                                                                :function (make-identifier :name "rest")
                                                                :types (list (make-type-sequence
                                                                              :element (make-type-defined
                                                                                        :name (make-identifier :name "point"))))
                                                                :arguments (list (make-expression-variable
                                                                                  :name (make-identifier :name "vertices"))))))
                                             (make-expression-call
                                              :function (make-identifier :name "first")
                                              :types (list (make-type-sequence
                                                            :element (make-type-defined
                                                                      :name (make-identifier :name "point"))))
                                              :arguments
                                              (list (make-expression-call
                                                     :function (make-identifier :name "rest")
                                                     :types (list (make-type-sequence
                                                                   :element (make-type-defined
                                                                             :name (make-identifier :name "point"))))
                                                     :arguments (list (make-expression-call
                                                                       :function (make-identifier :name "rest")
                                                                       :types (list (make-type-sequence
                                                                                     :element (make-type-defined
                                                                                               :name (make-identifier :name "point"))))
                                                                       :arguments (list (make-expression-variable
                                                                                         :name (make-identifier :name "vertices")))))))))))
                 :right-operand (make-expression-call
                                 :function (make-identifier :name "adjacent_three_points_not_collinear")
                                 :types (list)
                                 :arguments (list (make-expression-call
                                                   :function (make-identifier :name "rest")
                                                   :types (list (make-type-sequence
                                                                 :element (make-type-defined
                                                                           :name (make-identifier :name "point"))))
                                                   :arguments (list (make-expression-variable
                                                                     :name (make-identifier :name "vertices"))))))))
         :measure nil))))

#|
function edge_does_not_intersect_edges(edge0: edge, edges: seq<edge>) returns (b: bool) {
  if (is_empty(edges)) {
    return true;
  }
  else {
    return ! edges_intersect(edge0, first(edges))
            && edge_does_not_intersect_edges(edge0, rest(edges));
  }
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "edge_does_not_intersect_edges")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "edge0")
                                :type (make-type-defined
                                       :name (make-identifier :name "edge")))
                               (make-typed-variable
                                :name (make-identifier :name "edges")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "edge")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-if
                         :test (make-expression-call
                                :function (make-identifier :name "is_empty")
                                :types (list (make-type-sequence
                                              :element (make-type-defined
                                                        :name (make-identifier :name "edge"))))
                                :arguments (list (make-expression-variable
                                                  :name (make-identifier :name "edges"))))
                         :then (make-expression-literal
                                :get (make-literal-boolean
                                      :value t))
                         :else (make-expression-binary
                                :operator (make-binary-op-and)
                                :left-operand (make-expression-unary
                                               :operator (make-unary-op-not)
                                               :operand (make-expression-call
                                                         :function (make-identifier :name "edges_intersect")
                                                         :types (list)
                                                         :arguments (list (make-expression-variable
                                                                           :name (make-identifier :name "edge0"))
                                                                          (make-expression-call
                                                                           :function (make-identifier :name "first")
                                                                           :types (list (make-type-sequence
                                                                                         :element (make-type-defined
                                                                                                   :name (make-identifier :name "edge"))))
                                                                           :arguments (list (make-expression-variable
                                                                                             :name (make-identifier :name "edges")))))))
                                :right-operand (make-expression-call
                                                :function (make-identifier :name "edge_does_not_intersect_edges")
                                                :types (list)
                                                :arguments (list (make-expression-variable
                                                                  :name (make-identifier :name "edge0"))
                                                                 (make-expression-call
                                                                  :function (make-identifier :name "rest")
                                                                  :types (list (make-type-sequence
                                                                                :element (make-type-defined
                                                                                          :name (make-identifier :name "edge"))))
                                                                  :arguments (list (make-expression-variable
                                                                                    :name (make-identifier :name "edges"))))))))
                  :measure nil))))

#|
// return true when no two non-adjacent edges in a list intersect
function non_adjacent_edges_do_not_intersect(edges: seq<edge>) returns (b: bool) {
  if (is_empty(edges) || is_empty(rest(edges)) || is_empty(rest(rest(edges)))) {
    return true;
  }
  else {if (edge_does_not_intersect_edges(first(edges), rest(rest(edges)))) {
    return non_adjacent_edges_do_not_intersect(rest(edges));
  }
  else {
    return false;
  }}
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "non_adjacent_edges_do_not_intersect")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "edges")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "edge")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer
        (make-function-definer-regular
         :body (make-expression-if
                :test (make-expression-binary
                       :operator (make-binary-op-or)
                       :left-operand (make-expression-binary
                                      :operator (make-binary-op-or)
                                      :left-operand (make-expression-call
                                                     :function (make-identifier :name "is_empty")
                                                     :types (list (make-type-sequence
                                                                   :element (make-type-defined
                                                                             :name (make-identifier :name "edge"))))
                                                     :arguments (list (make-expression-variable
                                                                       :name (make-identifier :name "edges"))))
                                      :right-operand (make-expression-call
                                                      :function (make-identifier :name "is_empty")
                                                      :types (list (make-type-sequence
                                                                    :element (make-type-defined
                                                                              :name (make-identifier :name "edge"))))
                                                      :arguments (list (make-expression-call
                                                                        :function (make-identifier :name "rest")
                                                                        :types (list (make-type-sequence
                                                                                      :element (make-type-defined
                                                                                                :name (make-identifier :name "edge"))))
                                                                        :arguments (list (make-expression-variable
                                                                                          :name (make-identifier :name "edges")))))))
                       :right-operand (make-expression-call
                                       :function (make-identifier :name "is_empty")
                                       :types (list (make-type-sequence
                                                     :element (make-type-defined
                                                               :name (make-identifier :name "edge"))))
                                       :arguments (list (make-expression-call
                                                         :function (make-identifier :name "rest")
                                                         :types (list (make-type-sequence
                                                                       :element (make-type-defined
                                                                                 :name (make-identifier :name "edge"))))
                                                         :arguments (list (make-expression-call
                                                                           :function (make-identifier :name "rest")
                                                                           :types (list (make-type-sequence
                                                                                         :element (make-type-defined
                                                                                                   :name (make-identifier :name "edge"))))
                                                                           :arguments (list (make-expression-variable
                                                                                             :name (make-identifier :name "edges")))))))))
                :then (make-expression-literal
                       :get (make-literal-boolean
                             :value t))
                :else (make-expression-if
                       :test (make-expression-call
                              :function (make-identifier :name "edge_does_not_intersect_edges")
                              :types (list)
                              :arguments (list (make-expression-call
                                                :function (make-identifier :name "first")
                                                :types (list (make-type-sequence
                                                              :element (make-type-defined
                                                                        :name (make-identifier :name "edge"))))
                                                :arguments (list (make-expression-variable
                                                                  :name (make-identifier :name "edges"))))
                                               (make-expression-call
                                                :function (make-identifier :name "rest")
                                                :types (list (make-type-sequence
                                                              :element (make-type-defined
                                                                        :name (make-identifier :name "edge"))))
                                                :arguments (list (make-expression-call
                                                                  :function (make-identifier :name "rest")
                                                                  :types (list (make-type-sequence
                                                                                :element (make-type-defined
                                                                                          :name (make-identifier :name "edge"))))
                                                                  :arguments (list (make-expression-variable
                                                                                    :name (make-identifier :name "edges"))))))))
                       :then (make-expression-call
                              :function (make-identifier :name "non_adjacent_edges_do_not_intersect")
                              :types (list)
                              :arguments (list (make-expression-call
                                                :function (make-identifier :name "rest")
                                                :types (list (make-type-sequence
                                                              :element (make-type-defined
                                                                        :name (make-identifier :name "edge"))))
                                                :arguments (list (make-expression-variable
                                                                  :name (make-identifier :name "edges"))))))
                       :else (make-expression-literal
                              :get (make-literal-boolean
                                    :value nil))))
         :measure nil)))) 

#|
// A simple polygon is built from a sequence of n (>= 3) distinct vertices
//   v_1, v_2, ..., v_n
// by connecting the vertices in order and then connecting the last vertex
// with the first vertex, forming a closed polygonal chain of n edges
//   (v_1, v_2), (v_2, v_3), ...., (v_n-1, v_n), (v_n, v_1)
// Additionally,
// - adjacent three points must not be collinear, and
// - non-adjacent edges must not intersect
function simple_polygon(vertices: seq<point>) returns (b: bool) {
  return length(vertices) >= 3
          // Maybe need condition that no two points repeated
          // with possible exception that the first and last points are the same
          && adjacent_three_points_not_collinear(vertices)
          && non_adjacent_edges_do_not_intersect(edges(vertices));
}

theorem simple_polygon_implies_not_empty
  forall (vertices: seq<point>)
    simple_polygon(vertices)
      ==> !is_empty(vertices)
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "simple_polygon")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "vertices")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "b")
                                 :type (make-type-boolean))))
        :precondition nil
        :postcondition nil
        :definer (make-function-definer-regular
                  :body (make-expression-binary
                         :operator (make-binary-op-and)
                         :left-operand (make-expression-binary
                                        :operator (make-binary-op-and)
                                        :left-operand (make-expression-binary
                                                       :operator (make-binary-op-ge)
                                                       :left-operand (make-expression-call
                                                                      :function (make-identifier :name "length")
                                                                      :types (list (make-type-sequence
                                                                                    :element (make-type-defined
                                                                                              :name (make-identifier :name "point"))))
                                                                      :arguments (list (make-expression-variable
                                                                                        :name (make-identifier :name "vertices"))))
                                                       :right-operand (make-expression-literal
                                                                       :get (make-literal-integer
                                                                             :value 3)))
                                        :right-operand (make-expression-call
                                                        :function (make-identifier :name "adjacent_three_points_not_collinear")
                                                        :types (list)
                                                        :arguments (list (make-expression-variable
                                                                          :name (make-identifier :name "vertices")))))
                         :right-operand (make-expression-call
                                         :function (make-identifier :name "non_adjacent_edges_do_not_intersect")
                                         :types (list)
                                         :arguments (list (make-expression-call
                                                           :function (make-identifier :name "edges")
                                                           :types (list)
                                                           :arguments (list (make-expression-variable
                                                                             :name (make-identifier :name "vertices")))))))
                  :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier
               :name "simple_polygon_implies_not_empty")
        :variables (list (make-typed-variable
                          :name (make-identifier
                                 :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier
                                                  :name "point")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-call
                                 :function (make-identifier
                                            :name "simple_polygon")
                                 :types (list)
                                 :arguments (list (make-expression-variable
                                                   :name (make-identifier
                                                          :name "vertices"))))
                  :right-operand (make-expression-unary
                                  :operator (make-unary-op-not)
                                  :operand (make-expression-call
                                            :function (make-identifier
                                                       :name "is_empty")
                                            :types (list (make-type-sequence
                                                          :element (make-type-defined
                                                                    :name (make-identifier
                                                                           :name "point"))))
                                            :arguments (list (make-expression-variable
                                                              :name (make-identifier
                                                                     :name "vertices")))))))))

#|
/* number of times edge0 crosses  edges */
function crossings_count_aux(edge0: edge, edges: seq<edge>) assumes path_p(edges)
  returns (n: int) ensures n >= 0 {
  if (is_empty(edges)) {
    return 0;
  }
  else {if (edges_intersect(edge0, first(edges))) {
    return 1 + crossings_count_aux(edge0, rest(edges));
  }
  else {
   return crossings_count_aux(edge0, rest(edges));
  }}
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "crossings_count_aux")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "edge0")
                                :type (make-type-defined
                                       :name (make-identifier :name "edge")))
                               (make-typed-variable
                                :name (make-identifier :name "edges")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "edge")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "n")
                                 :type (make-type-integer))))
        :precondition (make-expression-call
                       :function (make-identifier :name "path_p")
                       :types (list)
                       :arguments (list (make-expression-variable
                                         :name (make-identifier :name "edges"))))
        :postcondition (make-expression-binary
                        :operator (make-binary-op-ge)
                        :left-operand (make-expression-variable
                                       :name (make-identifier :name "n"))
                        :right-operand (make-expression-literal
                                        :get (make-literal-integer
                                              :value 0)))
        :definer
        (make-function-definer-regular
         :body (make-expression-if
                :test (make-expression-call
                       :function (make-identifier :name "is_empty")
                       :types (list (make-type-sequence
                                     :element (make-type-defined
                                               :name (make-identifier :name "edge"))))
                       :arguments (list (make-expression-variable
                                         :name (make-identifier :name "edges"))))
                :then (make-expression-literal
                       :get (make-literal-integer
                             :value 0))
                :else (make-expression-if
                       :test (make-expression-call
                              :function (make-identifier :name "edges_intersect")
                              :types (list)
                              :arguments (list (make-expression-variable
                                                :name (make-identifier :name "edge0"))
                                               (make-expression-call
                                                :function (make-identifier :name "first")
                                                :types (list (make-type-sequence
                                                              :element (make-type-defined
                                                                        :name (make-identifier :name "edge"))))
                                                :arguments (list (make-expression-variable
                                                                  :name (make-identifier :name "edges"))))))
                       :then (make-expression-binary
                              :operator (make-binary-op-add)
                              :left-operand (make-expression-literal
                                             :get (make-literal-integer
                                                   :value 1))
                              :right-operand (make-expression-call
                                              :function (make-identifier :name "crossings_count_aux")
                                              :types (list)
                                              :arguments (list (make-expression-variable
                                                                :name (make-identifier :name "edge0"))
                                                               (make-expression-call
                                                                :function (make-identifier :name "rest")
                                                                :types (list (make-type-sequence
                                                                              :element (make-type-defined
                                                                                        :name (make-identifier :name "edge"))))
                                                                :arguments (list (make-expression-variable
                                                                                  :name (make-identifier :name "edges")))))))
                       :else (make-expression-call
                              :function (make-identifier :name "crossings_count_aux")
                              :types (list)
                              :arguments (list (make-expression-variable
                                                :name (make-identifier :name "edge0"))
                                               (make-expression-call
                                                :function (make-identifier :name "rest")
                                                :types (list (make-type-sequence
                                                              :element (make-type-defined
                                                                        :name (make-identifier :name "edge"))))
                                                :arguments (list (make-expression-variable
                                                                  :name (make-identifier :name "edges"))))))))
         :measure nil))))

#|
/* Number of times a ray starting from the given point crosses the edges of a polygon */
function crossings_count(p: point, polygon: seq<point>) assumes simple_polygon(polygon)
  returns (n: int) ensures n >=0 {
  let pm:point = point(x=max_x(polygon) + 1, y=p.y);
  let e:edge = edge(p1 = p, p2 = pm);
  return crossings_count_aux(e,edges(polygon));
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "crossings_count")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "p")
                                :type (make-type-defined
                                       :name (make-identifier :name "point")))
                               (make-typed-variable
                                :name (make-identifier :name "polygon")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "n")
                                 :type (make-type-integer))))
        :precondition (make-expression-call
                       :function (make-identifier :name "simple_polygon")
                       :types (list)
                       :arguments (list (make-expression-variable
                                         :name (make-identifier :name "polygon"))))
        :postcondition (make-expression-binary
                        :operator (make-binary-op-ge)
                        :left-operand (make-expression-variable
                                       :name (make-identifier :name "n"))
                        :right-operand (make-expression-literal
                                        :get (make-literal-integer
                                              :value 0)))
        :definer
        (make-function-definer-regular
         :body (make-expression-bind
                :variables (list (make-typed-variable
                                  :name (make-identifier :name "pm")
                                  :type (make-type-defined
                                         :name (make-identifier :name "point"))))
                :value (make-expression-product-construct
                        :type (make-identifier :name "point")
                        :fields (list (make-initializer
                                       :field (make-identifier :name "x")
                                       :value (make-expression-binary
                                               :operator (make-binary-op-add)
                                               :left-operand (make-expression-call
                                                              :function (make-identifier :name "max_x")
                                                              :types (list)
                                                              :arguments (list (make-expression-variable
                                                                                :name (make-identifier :name "polygon"))))
                                               :right-operand (make-expression-literal
                                                               :get (make-literal-integer
                                                                     :value 1))))
                                      (make-initializer
                                       :field (make-identifier :name "y")
                                       :value (make-expression-product-field
                                               :type (make-identifier :name "point")
                                               :target (make-expression-variable
                                                        :name (make-identifier :name "p"))
                                               :field (make-identifier :name "y")))))
                :body (make-expression-bind
                       :variables (list (make-typed-variable
                                         :name (make-identifier :name "e")
                                         :type (make-type-defined
                                                :name (make-identifier :name "edge"))))
                       :value (make-expression-product-construct
                               :type (make-identifier :name "edge")
                               :fields (list (make-initializer
                                              :field (make-identifier :name "p1")
                                              :value (make-expression-variable
                                                      :name (make-identifier :name "p")))
                                             (make-initializer
                                              :field (make-identifier :name "p2")
                                              :value (make-expression-variable
                                                      :name (make-identifier :name "pm")))))
                       :body (make-expression-call
                              :function (make-identifier :name "crossings_count_aux")
                              :types (list)
                              :arguments (list (make-expression-variable
                                                :name (make-identifier :name "e"))
                                               (make-expression-call
                                                :function (make-identifier :name "edges")
                                                :types (list)
                                                :arguments (list (make-expression-variable
                                                                  :name (make-identifier :name "polygon"))))))))
         :measure nil))))


#|
/* Top-level function */
function point_in_polygon(p: point, polygon: seq<point>) assumes simple_polygon(polygon)
  returns (b: bool) {
  return odd(crossings_count(p,polygon));
}
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get(make-function-definition
       :header (make-function-header
                :name (make-identifier :name "point_in_polygon")
                :inputs (list (make-typed-variable
                               :name (make-identifier :name "p")
                               :type (make-type-defined
                                      :name (make-identifier :name "point")))
                              (make-typed-variable
                               :name (make-identifier :name "polygon")
                               :type (make-type-sequence
                                      :element (make-type-defined
                                                :name (make-identifier :name "point")))))
                :outputs (list (make-typed-variable
                                :name (make-identifier :name "b")
                                :type (make-type-boolean))))
       :precondition (make-expression-call
                      :function (make-identifier :name "simple_polygon")
                      :types (list)
                      :arguments (list (make-expression-variable
                                        :name (make-identifier :name "polygon"))))
       :postcondition nil
       :definer (make-function-definer-regular
                 :body (make-expression-call
                        :function (make-identifier :name "odd")
                        :types (list)
                        :arguments (list (make-expression-call
                                          :function (make-identifier :name "crossings_count")
                                          :types (list)
                                          :arguments (list (make-expression-variable
                                                            :name (make-identifier :name "p"))
                                                           (make-expression-variable
                                                            :name (make-identifier :name "polygon"))))))
                 :measure nil))))



#|
// Introduced because syntheto doesn't currently have conditional expressions
function rest1(vertices:seq<point>) assumes !(is_empty(vertices) || is_empty(rest(vertices))) 
  returns (vs:seq<point>)  ensures points2_p(vs) {
  if (is_empty(rest(rest(vertices)))) {
    empty;}
  else {
    rest(vertices);
    }
}

/* Simplification Rules */

theorem length_rest1_decreases
  forall(vertices:seq<point>)
    !(is_empty(vertices) || is_empty(rest(vertices)))
     ==> length(rest1(vertices)) < length(vertices)

theorem path_vertices_of_rest_of_path_non_empty
  forall(vertices:seq<point>)
    !(is_empty(vertices) || is_empty(rest(vertices)))
     ==> path_vertices(rest(path(vertices))) == rest1(vertices)

theorem length_path_rest1_decreases
  forall(vertices:seq<point>)
    !(is_empty(vertices) || is_empty(rest(vertices)))
     ==> 1 + length(path(rest1(vertices)))< length(vertices)
|#

(process-syntheto-toplevel
 (make-toplevel-function
  :get (make-function-definition
        :header (make-function-header
                 :name (make-identifier :name "rest1")
                 :inputs (list (make-typed-variable
                                :name (make-identifier :name "vertices")
                                :type (make-type-sequence
                                       :element (make-type-defined
                                                 :name (make-identifier :name "point")))))
                 :outputs (list (make-typed-variable
                                 :name (make-identifier :name "vs")
                                 :type (make-type-sequence
                                        :element (make-type-defined
                                                  :name (make-identifier :name "point"))))))
        :precondition (make-expression-unary
                       :operator (make-unary-op-not)
                       :operand (make-expression-binary
                                 :operator (make-binary-op-or)
                                 :left-operand (make-expression-call
                                                :function (make-identifier :name "is_empty")
                                                :types (list (make-type-sequence
                                                              :element (make-type-defined
                                                                        :name (make-identifier :name "point"))))
                                                :arguments (list (make-expression-variable
                                                                  :name (make-identifier :name "vertices"))))
                                 :right-operand (make-expression-call
                                                 :function (make-identifier :name "is_empty")
                                                 :types (list (make-type-sequence
                                                               :element (make-type-defined
                                                                         :name (make-identifier :name "point"))))
                                                 :arguments (list (make-expression-call
                                                                   :function (make-identifier :name "rest")
                                                                   :types (list (make-type-sequence
                                                                                 :element (make-type-defined
                                                                                           :name (make-identifier :name "point"))))
                                                                   :arguments (list (make-expression-variable
                                                                                     :name (make-identifier :name "vertices"))))))))
        :postcondition (make-expression-call
                        :function (make-identifier :name "points2_p")
                        :types (list)
                        :arguments (list (make-expression-variable
                                          :name (make-identifier :name "vs"))))
        :definer (make-function-definer-regular
                  :body (make-expression-if
                         :test (make-expression-call
                                :function (make-identifier :name "is_empty")
                                :types (list (make-type-sequence
                                              :element (make-type-defined
                                                        :name (make-identifier :name "point"))))
                                :arguments (list (make-expression-call
                                                  :function (make-identifier :name "rest")
                                                  :types (list (make-type-sequence
                                                                :element (make-type-defined
                                                                          :name (make-identifier :name "point"))))
                                                  :arguments (list (make-expression-call
                                                                    :function (make-identifier :name "rest")
                                                                    :types (list (make-type-sequence
                                                                                  :element (make-type-defined
                                                                                            :name (make-identifier :name "point"))))
                                                                    :arguments (list (make-expression-variable
                                                                                      :name (make-identifier :name "vertices"))))))))
                         :then (make-expression-call
                                :function (make-identifier :name "empty")
                                :types (list (make-type-sequence
                                              :element (make-type-defined
                                                        :name (make-identifier :name "point"))))
                                :arguments (list))
                         :else (make-expression-call
                                :function (make-identifier :name "rest")
                                :types (list (make-type-sequence
                                              :element (make-type-defined
                                                        :name (make-identifier :name "point"))))
                                :arguments (list (make-expression-variable
                                                  :name (make-identifier :name "vertices")))))
                  :measure nil))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "length_rest1_decreases")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-unary
                                 :operator (make-unary-op-not)
                                 :operand (make-expression-binary
                                           :operator (make-binary-op-or)
                                           :left-operand (make-expression-call
                                                          :function (make-identifier :name "is_empty")
                                                          :types (list (make-type-sequence
                                                                        :element (make-type-defined
                                                                                  :name (make-identifier :name "point"))))
                                                          :arguments (list (make-expression-variable
                                                                            :name (make-identifier :name "vertices"))))
                                           :right-operand (make-expression-call
                                                           :function (make-identifier :name "is_empty")
                                                           :types (list (make-type-sequence
                                                                         :element (make-type-defined
                                                                                   :name (make-identifier :name "point"))))
                                                           :arguments (list (make-expression-call
                                                                             :function (make-identifier :name "rest")
                                                                             :types (list (make-type-sequence
                                                                                           :element (make-type-defined
                                                                                                     :name (make-identifier :name "point"))))
                                                                             :arguments (list (make-expression-variable
                                                                                               :name (make-identifier :name "vertices"))))))))
                  :right-operand (make-expression-binary
                                  :operator (make-binary-op-lt)
                                  :left-operand (make-expression-call
                                                 :function (make-identifier :name "length")
                                                 :types (list (make-type-sequence
                                                               :element (make-type-defined
                                                                         :name (make-identifier :name "point"))))
                                                 :arguments (list (make-expression-call
                                                                   :function (make-identifier :name "rest1")
                                                                   :types (list)
                                                                   :arguments (list (make-expression-variable
                                                                                     :name (make-identifier :name "vertices"))))))
                                  :right-operand (make-expression-call
                                                  :function (make-identifier :name "length")
                                                  :types (list (make-type-sequence
                                                                :element (make-type-defined
                                                                          :name (make-identifier :name "point"))))
                                                  :arguments (list (make-expression-variable
                                                                    :name (make-identifier :name "vertices")))))))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "path_vertices_of_rest_of_path_non_empty")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point")))))
        :formula (make-expression-binary
                  :operator (make-binary-op-implies)
                  :left-operand (make-expression-unary
                                 :operator (make-unary-op-not)
                                 :operand (make-expression-binary
                                           :operator (make-binary-op-or)
                                           :left-operand (make-expression-call
                                                          :function (make-identifier :name "is_empty")
                                                          :types (list (make-type-sequence
                                                                        :element (make-type-defined
                                                                                  :name (make-identifier :name "point"))))
                                                          :arguments (list (make-expression-variable
                                                                            :name (make-identifier :name "vertices"))))
                                           :right-operand (make-expression-call
                                                           :function (make-identifier :name "is_empty")
                                                           :types (list (make-type-sequence
                                                                         :element (make-type-defined
                                                                                   :name (make-identifier :name "point"))))
                                                           :arguments (list (make-expression-call
                                                                             :function (make-identifier :name "rest")
                                                                             :types (list (make-type-sequence
                                                                                           :element (make-type-defined
                                                                                                     :name (make-identifier :name "point"))))
                                                                             :arguments (list (make-expression-variable
                                                                                               :name (make-identifier :name "vertices"))))))))
                  :right-operand (make-expression-binary
                                  :operator (make-binary-op-eq)
                                  :left-operand (make-expression-call
                                                 :function (make-identifier :name "path_vertices")
                                                 :types (list)
                                                 :arguments (list (make-expression-call
                                                                   :function (make-identifier :name "rest")
                                                                   :types (list (make-type-sequence
                                                                                 :element (make-type-defined
                                                                                           :name (make-identifier :name "edge"))))
                                                                   :arguments (list (make-expression-call
                                                                                     :function (make-identifier :name "path")
                                                                                     :types (list)
                                                                                     :arguments (list (make-expression-variable
                                                                                                       :name (make-identifier :name "vertices"))))))))
                                  :right-operand (make-expression-call
                                                  :function (make-identifier :name "rest1")
                                                  :types (list)
                                                  :arguments (list (make-expression-variable
                                                                    :name (make-identifier :name "vertices")))))))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "length_path_rest1_decreases")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point")))))
        :formula
        (make-expression-binary
         :operator (make-binary-op-implies)
         :left-operand (make-expression-unary
                        :operator (make-unary-op-not)
                        :operand (make-expression-binary
                                  :operator (make-binary-op-or)
                                  :left-operand (make-expression-call
                                                 :function (make-identifier :name "is_empty")
                                                 :types (list (make-type-sequence
                                                               :element (make-type-defined
                                                                         :name (make-identifier :name "point"))))
                                                 :arguments (list (make-expression-variable
                                                                   :name (make-identifier :name "vertices"))))
                                  :right-operand (make-expression-call
                                                  :function (make-identifier :name "is_empty")
                                                  :types (list (make-type-sequence
                                                                :element (make-type-defined
                                                                          :name (make-identifier :name "point"))))
                                                  :arguments (list (make-expression-call
                                                                    :function (make-identifier :name "rest")
                                                                    :types (list (make-type-sequence
                                                                                  :element (make-type-defined
                                                                                            :name (make-identifier :name "point"))))
                                                                    :arguments (list (make-expression-variable
                                                                                      :name (make-identifier :name "vertices"))))))))
         :right-operand
         (make-expression-binary
          :operator (make-binary-op-lt)
          :left-operand (make-expression-binary
                         :operator (make-binary-op-add)
                         :left-operand (make-expression-literal
                                        :get (make-literal-integer :value 1))
                         :right-operand (make-expression-call
                                         :function (make-identifier :name "length")
                                         :types (list (make-type-sequence
                                                       :element (make-type-defined
                                                                 :name (make-identifier :name "edge"))))
                                         :arguments (list (make-expression-call
                                                           :function (make-identifier :name "path")
                                                           :types (list)
                                                           :arguments (list (make-expression-call
                                                                             :function (make-identifier :name "rest1")
                                                                             :types (list)
                                                                             :arguments (list (make-expression-variable
                                                                                               :name (make-identifier :name "vertices")))))))))
          :right-operand (make-expression-call
                          :function (make-identifier :name "length")
                          :types (list (make-type-sequence
                                        :element (make-type-defined
                                                  :name (make-identifier :name "point"))))
                          :arguments (list (make-expression-variable
                                            :name (make-identifier :name "vertices")))))))))

#|
theorem is_empty_path
  forall(vertices:seq<point>)
    is_empty(path(vertices)) == (is_empty(vertices) || is_empty(rest(vertices)))
|#

(process-syntheto-toplevel
  (make-toplevel-theorem
   :get (make-theorem
         :name (make-identifier :name "is_empty_path")
         :variables (list (make-typed-variable
                           :name (make-identifier
                                  :name "vertices")
                           :type (make-type-sequence
                                  :element (make-type-defined
                                            :name (make-identifier
                                                   :name "point")))))
         :formula (make-expression-binary
                   :operator (make-binary-op-eq)
                   :left-operand (make-expression-call
                                  :function (make-identifier
                                             :name "is_empty")
                                  :types (list (make-type-sequence
                                                :element (make-type-defined
                                                          :name (make-identifier
                                                                 :name "edge"))))
                                  :arguments (list (make-expression-call
                                                    :function (make-identifier
                                                               :name "path")
                                                    :types (list)
                                                    :arguments (list (make-expression-variable
                                                                      :name (make-identifier
                                                                             :name "vertices"))))))
                   :right-operand (make-expression-binary
                                   :operator (make-binary-op-or)
                                   :left-operand (make-expression-call
                                                  :function (make-identifier
                                                             :name "is_empty")
                                                  :types (list (make-type-sequence
                                                                :element (make-type-defined
                                                                          :name (make-identifier
                                                                                 :name "point"))))
                                                  :arguments (list (make-expression-variable
                                                                    :name (make-identifier
                                                                           :name "vertices"))))
                                   :right-operand (make-expression-call
                                                   :function (make-identifier
                                                              :name "is_empty")
                                                   :types (list (make-type-sequence
                                                                 :element (make-type-defined
                                                                           :name (make-identifier
                                                                                  :name "point"))))
                                                   :arguments (list (make-expression-call
                                                                     :function (make-identifier
                                                                                :name "rest")
                                                                     :types (list (make-type-sequence
                                                                                   :element (make-type-defined
                                                                                             :name (make-identifier
                                                                                                    :name "point"))))
                                                                     :arguments (list (make-expression-variable
                                                                                       :name (make-identifier
                                                                                              :name "vertices")))))))))))
#|
theorem p1_first_path
  forall(vertices:seq<point>, path1:edge)
    !is_empty(vertices) && !is_empty(rest(vertices))
      && path1 == first(path(vertices))
     ==> path1.p1 == first(vertices)

theorem p2_first_path
  forall(vertices:seq<point>, path1:edge)
    !is_empty(vertices) && !is_empty(rest(vertices))
      && path1 == first(path(vertices))
     ==> path1.p2 == first(rest(vertices))
|#

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "p1_first_path")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point"))))
                         (make-typed-variable
                          :name (make-identifier :name "path1")
                          :type (make-type-defined
                                 :name (make-identifier :name "edge"))))
        :formula
        (make-expression-binary
         :operator (make-binary-op-implies)
         :left-operand
         (make-expression-binary
          :operator (make-binary-op-and)
          :left-operand (make-expression-binary
                         :operator (make-binary-op-and)
                         :left-operand (make-expression-unary
                                        :operator (make-unary-op-not)
                                        :operand (make-expression-call
                                                  :function (make-identifier :name "is_empty")
                                                  :types (list (make-type-sequence
                                                                :element (make-type-defined
                                                                          :name (make-identifier :name "point"))))
                                                  :arguments (list (make-expression-variable
                                                                    :name (make-identifier :name "vertices")))))
                         :right-operand (make-expression-unary
                                         :operator (make-unary-op-not)
                                         :operand (make-expression-call
                                                   :function (make-identifier :name "is_empty")
                                                   :types (list (make-type-sequence
                                                                 :element (make-type-defined
                                                                           :name (make-identifier :name "point"))))
                                                   :arguments (list (make-expression-call
                                                                     :function (make-identifier :name "rest")
                                                                     :types (list (make-type-sequence
                                                                                   :element (make-type-defined
                                                                                             :name (make-identifier :name "point"))))
                                                                     :arguments (list (make-expression-variable
                                                                                       :name (make-identifier :name "vertices"))))))))
          :right-operand (make-expression-binary
                          :operator (make-binary-op-eq)
                          :left-operand (make-expression-variable
                                         :name (make-identifier :name "path1"))
                          :right-operand (make-expression-call
                                          :function (make-identifier :name "first")
                                          :types (list (make-type-sequence
                                                        :element (make-type-defined
                                                                  :name (make-identifier :name "edge"))))
                                          :arguments (list (make-expression-call
                                                            :function (make-identifier :name "path")
                                                            :types (list)
                                                            :arguments (list (make-expression-variable
                                                                              :name (make-identifier :name "vertices"))))))))
         :right-operand
         (make-expression-binary
          :operator (make-binary-op-eq)
          :left-operand (make-expression-product-field
                         :type (make-identifier :name "edge")
                         :target (make-expression-variable
                                  :name (make-identifier :name "path1"))
                         :field (make-identifier :name "p1"))
          :right-operand (make-expression-call
                          :function (make-identifier :name "first")
                          :types (list (make-type-sequence
                                        :element (make-type-defined
                                                  :name (make-identifier :name "point"))))
                          :arguments (list (make-expression-variable
                                            :name (make-identifier :name "vertices")))))))))

(process-syntheto-toplevel
 (make-toplevel-theorem
  :get (make-theorem
        :name (make-identifier :name "p2_first_path")
        :variables (list (make-typed-variable
                          :name (make-identifier :name "vertices")
                          :type (make-type-sequence
                                 :element (make-type-defined
                                           :name (make-identifier :name "point"))))
                         (make-typed-variable
                          :name (make-identifier :name "path1")
                          :type (make-type-defined
                                 :name (make-identifier :name "edge"))))
        :formula
        (make-expression-binary
         :operator (make-binary-op-implies)
         :left-operand (make-expression-binary
                        :operator (make-binary-op-and)
                        :left-operand (make-expression-binary
                                       :operator (make-binary-op-and)
                                       :left-operand (make-expression-unary
                                                      :operator (make-unary-op-not)
                                                      :operand (make-expression-call
                                                                :function (make-identifier :name "is_empty")
                                                                :types (list (make-type-sequence
                                                                              :element (make-type-defined
                                                                                        :name (make-identifier :name "point"))))
                                                                :arguments (list (make-expression-variable
                                                                                  :name (make-identifier :name "vertices")))))
                                       :right-operand (make-expression-unary
                                                       :operator (make-unary-op-not)
                                                       :operand (make-expression-call
                                                                 :function (make-identifier :name "is_empty")
                                                                 :types (list (make-type-sequence
                                                                               :element (make-type-defined
                                                                                         :name (make-identifier :name "point"))))
                                                                 :arguments (list (make-expression-call
                                                                                   :function (make-identifier :name "rest")
                                                                                   :types (list (make-type-sequence
                                                                                                 :element (make-type-defined
                                                                                                           :name (make-identifier :name "point"))))
                                                                                   :arguments (list (make-expression-variable
                                                                                                     :name (make-identifier :name "vertices"))))))))
                        :right-operand (make-expression-binary
                                        :operator (make-binary-op-eq)
                                        :left-operand (make-expression-variable
                                                       :name (make-identifier :name "path1"))
                                        :right-operand (make-expression-call
                                                        :function (make-identifier :name "first")
                                                        :types (list (make-type-sequence
                                                                      :element (make-type-defined
                                                                                :name (make-identifier :name "edge"))))
                                                        :arguments (list (make-expression-call
                                                                          :function (make-identifier :name "path")
                                                                          :types (list)
                                                                          :arguments (list (make-expression-variable
                                                                                            :name (make-identifier :name "vertices"))))))))
         :right-operand (make-expression-binary
                         :operator (make-binary-op-eq)
                         :left-operand (make-expression-product-field
                                        :type (make-identifier :name "edge")
                                        :target (make-expression-variable
                                                 :name (make-identifier :name "path1"))
                                        :field (make-identifier :name "p2"))
                         :right-operand (make-expression-call
                                         :function (make-identifier :name "first")
                                         :types (list (make-type-sequence
                                                       :element (make-type-defined
                                                                 :name (make-identifier :name "point"))))
                                         :arguments (list (make-expression-call
                                                                     :function (make-identifier :name "rest")
                                                                     :types (list (make-type-sequence
                                                                                   :element (make-type-defined
                                                                                             :name (make-identifier :name "point"))))
                                                                     :arguments (list (make-expression-variable
                                                                                       :name (make-identifier :name "vertices")))))))))))

#|
/* Derivation */

function crossings_count_aux_1 =
  transform crossings_count_aux 
    by tail_recursion {new_parameter_name = count}
|#

(process-syntheto-toplevel
 (make-toplevel-transform
  :get (make-transform
        :new-function-name (make-identifier :name "crossings_count_aux_1")
        :old-function-name (make-identifier :name "crossings_count_aux")
        :transform-name "tail_recursion"
        :arguments (list (make-transform-argument
                          :name (make-identifier :name "new_parameter_name")
                          :value (make-transform-argument-value-identifier
                                  :name (make-identifier :name "count")))))))
#|
function crossings_count_aux_2 =
  transform crossings_count_aux_1
    by restrict {predicate = natp(count)}
|#

(process-syntheto-toplevel
 (make-toplevel-transform
  :get (make-transform
        :new-function-name (make-identifier :name "crossings_count_aux_2")
        :old-function-name (make-identifier :name "crossings_count_aux_1")
        :transform-name "restrict"
        :arguments (list (make-transform-argument
                          :name (make-identifier :name "predicate")
                          :value (make-transform-argument-value-term
                                  :get (make-expression-call
                                        :function (make-identifier :name "natp")
                                        :types (list)
                                        :arguments (list (make-expression-variable :name (make-identifier :name "count"))))))))))

#|
function crossings_count_aux_3 =
  transform crossings_count_aux_2
    by isomorphism {parameter = edges,
                    new_parameter_name = vertices,
                    old_type = path_p,
                    new_type = points2_p,
                    old_to_new = path_vertices,
                    new_to_old = path,
                    simplify = true}
|#

(process-syntheto-toplevel
 (make-toplevel-transform
  :get (make-transform
        :new-function-name (make-identifier :name "crossings_count_aux_3")
        :old-function-name (make-identifier :name "crossings_count_aux_2")
        :transform-name "isomorphism"
        :arguments (list (make-transform-argument
                          :name (make-identifier :name "parameter")
                          :value (make-transform-argument-value-identifier
                                  :name (make-identifier :name "edges")))
                         (make-transform-argument
                          :name (make-identifier :name "new_parameter_name")
                          :value (make-transform-argument-value-identifier
                                  :name (make-identifier :name "vertices")))
                         (make-transform-argument
                          :name (make-identifier :name "old_type")
                          :value (make-transform-argument-value-identifier
                                  :name (make-identifier :name "path_p")))
                         (make-transform-argument
                          :name (make-identifier :name "new_type")
                          :value (make-transform-argument-value-identifier
                                  :name (make-identifier :name "points2_p")))
                         (make-transform-argument
                          :name (make-identifier :name "old_to_new")
                          :value (make-transform-argument-value-identifier
                                  :name (make-identifier :name "path_vertices")))
                         (make-transform-argument
                          :name (make-identifier :name "new_to_old")
                          :value (make-transform-argument-value-identifier
                                  :name (make-identifier :name "path")))
                         (make-transform-argument
                          :name (make-identifier :name "simplify")
                          :value (make-transform-argument-value-bool
                                  :val t))))))

#|
function crossings_count_aux_4 =
  transform crossings_count_aux_3
    by wrap_output {wrap_function = odd}
|#

;; (process-syntheto-toplevel
;;  (make-toplevel-transform
;;   :get (make-transform
;;         :new-function-name (make-identifier :name "crossings_count_aux_4")
;;         :old-function-name (make-identifier :name "crossings_count_aux_3")
;;         :transform-name "wrap_output"
;;         :arguments (list (make-transform-argument
;;                           :name (make-identifier :name "wrap_function")
;;                           :value (make-transform-argument-value-identifier
;;                                   :name (make-identifier :name "odd")))))))
#|
function crossings_count_aux_5 =
  transform crossings_count_aux_4
    by finite_difference {expression = odd(count),
                          new_parameter_name = count_odd,
                          simplify = true}
|#

;; (process-syntheto-toplevel
;;  (make-toplevel-transform
;;   :get (make-transform
;;         :new-function-name (make-identifier :name "crossings_count_aux_5")
;;         :old-function-name (make-identifier :name "crossings_count_aux_4")
;;         :transform-name "finite_difference"
;;         :arguments (list (make-transform-argument
;;                           :name (make-identifier :name "expression")
;;                           :value (make-transform-argument-value-term
;;                                   :get (make-expression-call
;;                                         :function (make-identifier :name "odd")
;;                                         :types (list)
;;                                         :arguments (list (make-expression-variable :name (make-identifier :name "count"))))))
;;                          (make-transform-argument
;;                           :name (make-identifier :name "new_parameter_name")
;;                           :value (transform-argument-value-identifier (make-identifier :name "count_odd")))
;;                          (make-transform-argument
;;                           :name (make-identifier :name "simplify")
;;                           :value (make-transform-argument-value-bool :val t))
;;                          ))))
#|
function crossings_count_aux_6 =
  transform crossings_count_aux_5
    by drop_irrelevant_param {parameter = count}
|#

;; (process-syntheto-toplevel
;;  (make-toplevel-transform
;;   :get (make-transform
;;         :new-function-name (make-identifier :name "crossings_count_aux_6")
;;         :old-function-name (make-identifier :name "crossings_count_aux_5")
;;         :transform-name "drop_irrelevant_parameter"
;;         :arguments (list (make-transform-argument
;;                           :name (make-identifier :name "parameter")
;;                           :value (transform-argument-value-identifier (make-identifier :name "count")))))))

#|
function crossings_count_1 =
  transform crossings_count
    by wrap_output {wrap_function = odd,
                    simplify = true}
|#

(process-syntheto-toplevel
 (make-toplevel-transform
  :get (make-transform
        :new-function-name (make-identifier :name "crossings_count_1")
        :old-function-name (make-identifier :name "crossings_count")
        :transform-name "wrap_output"
        :arguments (list (make-transform-argument
                          :name (make-identifier :name "wrap_function")
                          :value (make-transform-argument-value-identifier
                                  :name (make-identifier :name "odd")))))))
#|
function crossings_count_2 =
  transform crossings_count_1
    by simplify
|#

(process-syntheto-toplevel
 (make-toplevel-transform
  :get (make-transform
        :new-function-name (make-identifier :name "crossings_count_2")
        :old-function-name (make-identifier :name "crossings_count_1")
        :transform-name "simplify"
        :arguments (list))))

#|
function point_in_polygon_final =
  transform point_in_polygon
    by simplify
|#

(process-syntheto-toplevel
 (make-toplevel-transform
  :get (make-transform
        :new-function-name (make-identifier :name "point_in_polygon_final")
        :old-function-name (make-identifier :name "point_in_polygon")
        :transform-name "simplify"
        :arguments ())))
