(in-package "SYNTHETO")

(include-book "rational")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; theorem lteq_antisymmetric
;;   forall(x:rational,y:rational) lteq(x,y) && lteq(y,x) ==> x == y

(defconst *theorem-lteq-antisymmetric*
  (toplevel-theorem
   (make-theorem
    :name (identifier "lteq_antisymmetric")
    :variables (list (make-typed-variable
                      :name (identifier "x")
                      :type (type-defined (identifier "rational")))
                     (make-typed-variable
                      :name (identifier "y")
                      :type (type-defined (identifier "rational"))))
    :formula
    (make-expression-binary
     :operator (binary-op-implies)
     :left-operand
     (make-expression-binary
      :operator (binary-op-and)
      :left-operand
      (make-expression-call
       :function (identifier "lteq")
       :types nil
       :arguments
       (list (make-expression-variable :name (identifier "x"))
             (make-expression-variable :name (identifier "y"))))
      :right-operand
      (make-expression-call
       :function (identifier "lteq")
       :types nil
       :arguments
       (list (make-expression-variable :name (identifier "y"))
             (make-expression-variable :name (identifier "x")))))
     :right-operand
     (make-expression-binary
      :operator (binary-op-eq)
      :left-operand (make-expression-variable :name (identifier "x"))
      :right-operand (make-expression-variable :name (identifier "y")))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; theorem lteq_transitive
;;   forall(x:rational,y:rational,z:rational) lteq(x,y) && lteq(y,z)==>lteq(x,z)

(defconst *theorem-lteq-transitive*
  (toplevel-theorem
   (make-theorem
    :name (identifier "lteq_transitive")
    :variables (list (make-typed-variable
                      :name (identifier "x")
                      :type (type-defined (identifier "rational")))
                     (make-typed-variable
                      :name (identifier "y")
                      :type (type-defined (identifier "rational")))
                     (make-typed-variable
                      :name (identifier "z")
                      :type (type-defined (identifier "rational"))))
    :formula
    (make-expression-binary
     :operator (binary-op-implies)
     :left-operand
     (make-expression-binary
      :operator (binary-op-and)
      :left-operand
      (make-expression-call
       :function (identifier "lteq")
       :types nil
       :arguments
       (list (make-expression-variable :name (identifier "x"))
             (make-expression-variable :name (identifier "y"))))
      :right-operand
      (make-expression-call
       :function (identifier "lteq")
       :types nil
       :arguments
       (list (make-expression-variable :name (identifier "y"))
             (make-expression-variable :name (identifier "z")))))
     :right-operand
     (make-expression-call
      :function (identifier "lteq")
      :types nil
      :arguments
      (list (make-expression-variable :name (identifier "y"))
            (make-expression-variable :name (identifier "z"))))))))
