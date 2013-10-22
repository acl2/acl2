(in-package "ACL2")

#|

  variables.lisp
  ~~~~~~~~~~~~~~

In this book, we define macros for accessing and updating the variables in our
bakery implementation. The variables are presented as fields of a record
structure.

|#

(include-book "records")

(defmacro choosing (x) `(<- ,x :choosing))
(defmacro status   (x) `(<- ,x :status))
(defmacro current  (x) `(<- ,x :current))
(defmacro pos      (x) `(<- ,x :pos))
(defmacro temp     (x) `(<- ,x :temp))
(defmacro loc      (x) `(<- ,x :loc))
(defmacro indices  (x) `(<- ,x :indices))
(defmacro procs    (x) `(<- ,x :procs))
(defmacro queue    (x) `(<- ,x :queue))
(defmacro maxval   (x) `(<- ,x :maxval))
(defmacro bucket   (x) `(<- ,x :bucket))
(defmacro get-go   (x) `(<- ,x :go))

(defmacro >st (&rest upds) `(update st  ,@upds))
(defmacro >p  (&rest upds) `(update p   ,@upds))
(defmacro >_  (&rest upds) `(update nil ,@upds))
