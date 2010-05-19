(in-package "FAST-SETS")
(include-book "sets")

(defun add (x Y)
  (if (in x Y)
      Y
    (cons x Y)))

(defun set-union (X Y)
  (cond ((endp X) Y)
        ((in (car X) Y)
         (set-union (cdr X) Y))
        (t (set-union (cdr X) (cons (car X) Y)))))

(defun intersect-aux (X Y Z)
  (cond ((endp X) Z)
        ((in (car X) Y)
         (intersect-aux (cdr X) Y (cons (car X) Z)))
        (t (intersect-aux (cdr X) Y Z))))

(defun intersect (X Y)
  (intersect-aux X Y nil))

(defun minus-t (X Y Z)
  (cond ((endp X) Z)
        ((in (car X) Y)
         (minus-t (cdr X) Y Z))
        (t (minus-t (cdr X) Y (cons (car X) Z)))))

(defun minus (X Y)
  (minus-t X Y nil))

(defun set-complement (X U)
  (minus U X))

(defun remove-dups (X)
  (set-union X nil))

(defun cardinality (X)
  (len (remove-dups X)))
