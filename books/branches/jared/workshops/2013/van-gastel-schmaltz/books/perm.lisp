#|$ACL2s-Preamble$;
(begin-book t :ttags :all);$ACL2s-Preamble$|#

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
(defthm permp-implies-member-iff
  (implies (permp x y)
           (iff (member-equal a x)
                (member-equal a y))))
(defthm del-commutes
  (equal (del a (del b c)) (del b (del a c))))
(defthm del-same-member-preserves-permp
  (implies (and (member-equal x a)
                (member-equal x b)
                (permp a b))
           (permp (del x a)
                  (del x b))))
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
(defcong permp iff (member-equal a x) 2)

(defthm permp-append-cons
  (permp (append x (cons a y))
         (cons a (append x y))))
(local (defthm member-remove-equal
         (iff (member-equal a (remove-equal b x))
              (and (member-equal a x)
                   (not (equal a b))))))
(defcong permp permp (remove-equal a x) 2)
(defcong permp equal (subsetp x y) 1)
(defcong permp equal (subsetp x y) 2)
(defthm succesful-del-preserves-permp
  (implies (and (member c ch1)
                  (member c ch2))
           (equal (permp (del c ch1)
                         (del c ch2))
                  (permp ch1 ch2))))
(defthm unsuccesful-del-preserves-set
  (implies (not (member c ch1))
           (equal (del c ch1)
                  ch1)))
(defthm del-preserves-permp
  (implies (equal (member c ch1)
                  (member c ch2))
           (equal (permp (del c ch1)
                         (del c ch2))
                  (permp ch1 ch2)))
  :hints (("Goal"
           :cases ((and (member c ch1) (member c ch2)) (and (not (member c ch1)) (not (member c ch2))))
           ))
  )#|ACL2s-ToDo-Line|#


