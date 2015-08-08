#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

;; The following book contains the defintion of del.
;; We load this book, to prevent mutliple defintions,
;; of the same function.
(include-book "meta/term-defuns" :dir :system)


(defun permp (left right)
  (or (and (endp left) (endp right))
      (and (consp left)
           (member-equal (car left) right)
           (permp (cdr left) (del (car left) right)))))



(defthm permp-reflexive
  (permp x x))
(defthm del-different-element-preserves-member
  (implies (not (equal a b))
           (iff (member-equal a (del b x))
                (member-equal a x))))


(defthm del-commutes
  (equal (del a (del b c)) (del b (del a c))))
(defthm del-same-member-preserves-permp
  (implies (and (member-equal x a)
                (member-equal x b)
                (permp a b))
           (permp (del x a)
                  (del x b))))
(defthm permp-implies-member-iff
  (implies (permp x y)
           (iff (member-equal a x)
                (member-equal a y))))
(defthm permp-transitive
  (implies (and (permp x y)
                (permp y z))
           (permp x z)))

(in-theory (disable permp-implies-member-iff))
(defthm cons-del-permutation-of-original
  (implies (and (member-equal a y)
        (permp (cons a (del a y)) x))
       (permp y x)))
(defthm permp-symmetric
  (implies (permp x y)
       (permp y x)))
(defthm member-of-append-iff-member-of-operand
  (iff (member-equal a (append x y))
       (or (member-equal a x)
           (member-equal a y))))
(defequiv permp)
(defcong permp permp (append x y) 2)
(defcong permp permp (append x y) 1)
(defcong permp permp (del a x) 2)
(defcong permp permp (cons a x) 2)
(defcong permp iff (member-equal a x) 2)#|ACL2s-ToDo-Line|#

