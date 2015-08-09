(in-package "ACL2")
(include-book "defung")

; notice that this is the same definition used in sets.lisp
(defun in (a X)
  (declare (xargs :guard (true-listp X)))
  (cond ((endp X) nil)
        ((equal a (car X)) t)
        (t (in a (cdr X)))))

(defung remove-el (a X)
  (declare (xargs :guard (true-listp X)))
  ((implies (true-listp X) (true-listp (remove-el a X))))
  (cond ((endp X) nil)
        ((equal a (car X)) (cdr X))
        (t (cons (car X) (remove-el a (cdr X))))))

(defun perm (X Y)
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (cond ((endp X) (endp Y))
        (t (and (in (car X) Y)
                (perm (cdr X) (remove-el (car X) Y))))))

(defthm remove-el-in
  (implies (not (equal a b))
           (equal (in a (remove-el b X))
                  (in a X))))

(defthm remove-el-swap
  (equal (remove-el a (remove-el b X))
         (remove-el b (remove-el a X))))

(local
 (defthm perm-reflexive
   (perm X X)))

(local
 (defthm perm-remove
   (implies (perm X Y)
            (perm (remove-el a X) (remove-el a Y)))))

(local
 (defthm car-perm
   (implies (and (consp X)
                 (not (in (car X) Y)))
            (not (perm Y X)))))

(local
 (defthm perm-symmetric
   (implies (perm X Y)
            (perm Y X))
   :hints (("Goal"
            :induct (perm Y X))
           ("Subgoal *1/2''"
            :use ((:instance perm-remove (a (car Y))))))))

(local
 (defthm perm-in
   (implies (and (perm X Y)
                 (in a X))
            (in a Y))
   :rule-classes ((:forward-chaining :trigger-terms ((in a X) (in a Y))))))

(local
 (defthm perm-transitive
   (implies (and (perm X Y) (perm Y Z))
            (perm X Z))))

; Exercise 6, part 1
(defequiv perm)

(defthm perm-remove-el-app
  (implies (in a X)
           (equal (remove-el a (append X Y))
                  (append (remove-el a X) Y))))

(defcong perm perm (remove-el a X) 2)

(defcong perm perm (append X Y) 1)

(defcong perm perm (cons X Y) 2)

(defthm perm-app-cons
  (perm (append X (cons a Y))
        (cons a (append X Y))))
