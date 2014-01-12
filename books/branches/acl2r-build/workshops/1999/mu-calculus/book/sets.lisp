(in-package "SET") ;; 2014-01-02: Changed from SETS by Jared to avoid conflict with std/sets

; Checks for set containment, i.e., is a in X?
(defun in (a X)
  (cond ((endp X) nil)
        ((equal a (car X)) t)
        (t (in a (cdr X)))))

; Subset, i.e., X =< Y
(defun =< (X Y)
  (cond ((endp X) t)
        (t (and (in (car X) Y)
                (=< (cdr X) Y)))))

; Set equality, i.e., X == Y
(defun == (X Y)
  (and (=< X Y)
       (=< Y X)))

; set union, i.e., X U Y
(defun set-union (X Y)
  (if (endp X)
      Y
    (cons (car X) (set-union (cdr X) Y))))

; Set intersection, i.e., X & Y
(defun intersect (X Y)
  (cond ((endp X) nil)
        ((in (car X) Y)
         (cons (car X) (intersect (cdr X) Y)))
        (t (intersect (cdr X) Y))))

; Set minus, i.e.,  X - Y
(defun minus (X Y)
  (cond ((endp X) nil)
        ((in (car X) Y)
         (minus (cdr X) Y))
        (t (cons (car X) (minus (cdr X) Y)))))

; complement set X, i.e., U - X
(defun set-complement (X U)
  (minus U X))

; Remove duplicates in X
(defun remove-dups (X)
  (cond ((endp X) nil)
        ((in (car X) (cdr X))
         (remove-dups (cdr X)))
        (t (cons (car X)
                 (remove-dups (cdr X))))))

; Cardinality of X, i.e., |X|
(defun cardinality (X)
  (len (remove-dups X)))

(defun s< (X Y)
  (and (=< X Y) (not (=< Y X))))

