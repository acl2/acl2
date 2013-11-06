#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; Multicons Function
;; Jared Davis 
;; 
;; We introduce the notion of augmenting a set of lists by consing a new
;; element onto the front of each list.  For example, given the set { (a1 c),
;; (a2 b), (a2 c) }, we might multicons x onto the set to produce a new set
;; which is { (x a1 b), (x a1 c), (x a2 b), (x a2 c) }.
;;
;; I got a little crazy and went to some effort to show that you can just use
;; conses in order to construct the new set.  I thought originally that this
;; would be a lot more efficient than the insert-based version below, because
;; it replaces an "insert sort like" operation with simple conses.  
;;
;; On further consideration, I think the insert would always be sticking its
;; element at the front of the set, and so it would just be a small constant
;; overhead.  So, there is probably not much of an efficiency advantage to all
;; of our effort.  On the other hand, it is certainly some constant factor more
;; efficient.

(in-package "SET")
(include-book "sets")
(include-book "listsets")

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

(defund multicons (a X)
  (declare (xargs :guard (setp X)
                  :verify-guards nil))
  (mbe :logic (if (empty X)
                  (emptyset)
                (insert (cons a (head X))
                        (multicons a (tail X))))
       :exec (if (atom X)
                 nil
               (cons (cons a (car X))
                     (multicons a (cdr X))))))

(local (in-theory (enable multicons)))

(defthm multicons-set
  (setp (multicons a X)))

(defthm listsetp-of-multicons
  (equal (listsetp (multicons a X))
         (all<true-listp> X))
  :hints(("Goal" :in-theory (enable listsetp))))

(defthm multicons-in
  (equal (in path (multicons a X))
         (and (consp path)
              (equal (car path) a)
              (in (cdr path) X)))
  :hints(("Goal" :induct (multicons a X))))

(local (defun multicons-list (a X)
         (declare (xargs :guard t))
         (if (atom X)
             nil
           (cons (cons a (car X))
                 (multicons-list a (cdr X))))))

(local (defthm in-list-multicons-list
         (equal (in-list path (multicons-list a X))
                (and (consp path)
                     (equal (car path) a)
                     (in-list (cdr path) X)))))

(local (defun weakly-ordered-p (x)
         (if (endp x)
             (null x)
           (or (null (cdr x))
               (and (consp (cdr x))
                    (lexorder (car x) (cadr x))
                    (weakly-ordered-p (cdr x)))))))

(local (defthm lexorder-cons
         (equal (lexorder (cons x a) 
                          (cons x b))
                (lexorder a b))
         :hints(("Goal" :in-theory (enable lexorder)))))

(local (defthm multicons-list-weakly-ordered
         (implies (weakly-ordered-p X)
                  (weakly-ordered-p (multicons-list a X)))))

(local (defthm member-equal-elim
         (iff (member-equal a x)
              (in-list a x))))

(local (defthm multicons-list-no-duplicates
         (implies (no-duplicatesp-equal X)
                  (no-duplicatesp-equal (multicons-list a X)))))

(local (defthm setp-redefinition
         (equal (setp x)
                (and (no-duplicatesp-equal x)
                     (weakly-ordered-p x)))
         :hints(("Goal"
                 :induct (setp x)
                 :in-theory (enable setp 
                                    tail
                                    sfix
                                    empty
                                    head
                                    <<
                                    lexorder)))))

(local (defthm setp-multicons-list
         (implies (setp X)
                  (setp (multicons-list a X)))))

(local (defthm in-multicons-list
         (implies (setp X)
                  (equal (in path (multicons-list a X))
                         (and (consp path)
                              (equal (car path) a)
                              (in (cdr path) X))))
         :hints(("Goal" 
                 :in-theory (disable in-list-multicons-list)
                 :use (:instance in-list-multicons-list)))))

(local (defthm lemma
         (implies (and (setp X)
                       (empty X))
                  (equal X nil))
         :rule-classes nil
         :hints(("Goal" :in-theory (enable setp empty)))))

(local (defthm main-lemma
         (implies (setp X)
                  (equal (multicons a X)
                         (multicons-list a X)))
         :hints(("Goal" :in-theory (disable setp-redefinition)
                 :use (:instance lemma)))))

(verify-guards multicons
               :hints(("Goal" :use (:instance main-lemma))))
