
(in-package "ACL2")

(defn gentle-binary-append (x y)
  (mbe :logic
       (binary-append x y)
       :exec
       (if (atom x)
           y
         (cons (car x) (gentle-binary-append (cdr x) y)))))

(defmacro gentle-append (x y &rest rst)
  (xxxjoin 'gentle-binary-append (cons x (cons y rst))))

(add-macro-alias gentle-append gentle-binary-append)
(add-binop gentle-append gentle-binary-append)

(defmacro ap (&rest r)
  `(gentle-append . ,r))

(add-macro-alias ap gentle-binary-append)
(add-binop ap gentle-binary-append)
