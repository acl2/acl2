#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "LIST")

(include-book "subsetp")

;; We just use ACL2's remove

(defthm remove-equal-reduction
  (equal (remove-equal a x)
         (remove a x)))

(defthm remove-remove
  (equal (remove a (remove b x))
         (remove b (remove a x))))

(defthm remove-cons
  (equal (remove a (cons b x))
         (if (equal a b)
             (remove a x)
           (cons b (remove a x)))))

(defthm remove-append
  (equal (remove x (append a b))
         (append (remove x a)
                 (remove x b))))

(defthm non-increasing-remove
  (<= (acl2-count (remove a x)) (acl2-count x)))

(defthm decreasing-remove
  (implies
   (list::memberp a x)
   (< (acl2-count (remove a x)) (acl2-count x)))
  :rule-classes (:linear))

(defcong equiv equal (remove a x) 2
  :hints (("Goal" :induct (len-len-induction x-equiv x))))

(defthm memberp-remove
  (equal (memberp a (remove b x))
         (if (equal a b) nil
           (memberp a x))))

(defthm not-memberp-remove-forward
  (not (list::memberp a (remove a list)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((remove a list)))))

(defthm memberp-remove-implies-member
  (implies
   (and
    (list::memberp a (remove b list))
    (not (equal a b)))
   (list::memberp a list))
  :rule-classes (:forward-chaining))

(defthm memberp-implies-memberp-remove
  (implies
   (and
    (list::memberp a list)
    (not (equal a key)))
   (list::memberp a (remove key list)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((remove key list)))))

(defthm remove-reducton
  (implies
   (not (memberp a x))
   (equal (remove a x)
          (fix x))))

(defthm subset-remove-reduction-2
  (implies
   (not (memberp a x))
   (equal (subsetp x (remove a y))
          (subsetp x y))))

(defthm subset-remove-reduction-1
  (implies
   (memberp a y)
   (equal (subsetp (remove a x) y)
          (subsetp x y))))
          
;;
;; remove-list : a means of removing multiple elements of a list
;;

(defun remove-list (x y)
  (if (consp y)
      (if (memberp (car y) x)
	  (remove-list x (cdr y))
	(cons (car y) (remove-list x (cdr y))))
    nil))

(defcong equiv equiv (remove-list x y) 2
  :hints (("Goal" :induct (len-len-induction y-equiv y))))

(defcong equiv equal (remove-list x y) 1)

(defthm remove-list-remove
  (equal (remove-list x (remove a y))
         (remove a (remove-list x y))))

(defthm remove-list-remove-list
  (equal (remove-list a (remove-list b x))
         (remove-list b (remove-list a x))))

(defthm remove-list-cons-1
  (equal (remove-list (cons a x) y)
         (remove a (remove-list x y))))

(defthm remove-list-cons-2
  (equal (remove-list x (cons a y))
         (if (memberp a x)
             (remove-list x y)
           (cons a (remove-list x y)))))

(defthm remove-list-append-1
  (equal (remove-list (append a b) x)
         (remove-list b (remove-list a x)))
  :hints (("Goal" :in-theory (enable append))))

(defthm remove-list-append-2
  (equal (remove-list a (append x y))
         (append (remove-list a x)
                 (remove-list a y))))

(defthm memberp-remove-list
  (equal (memberp a (remove-list x y))
         (if (memberp a x) nil
           (memberp a y))))

(defthm memberp-remove-list-implies
  (implies
   (memberp a (remove-list x y))
   (and (not (memberp a x))
	(memberp a y)))
  :rule-classes (:forward-chaining))

(defthm not-memberp-remove-list-implies-1
  (implies
   (and
    (not (memberp a (remove-list x y)))
    (memberp a y))
   (memberp a x))
  :rule-classes (:forward-chaining))

(defthm not-memberp-remove-list-implies-2
  (implies
   (and
    (not (memberp a (remove-list x y)))
    (not (memberp a x)))
   (not (memberp a y)))
  :rule-classes (:forward-chaining))

(defthm implies-memberp-remove-list
  (implies
   (and (not (memberp a x))
	(memberp a y))
   (memberp a (remove-list x y)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((remove-list x y)))))

(defthm implies-not-memberp-remove-list-1
  (implies
   (memberp a x)
   (not (memberp a (remove-list x y))))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((remove-list x y)))))

(defthm implies-not-memberp-remove-list-2
  (implies
   (not (memberp a y))
   (not (memberp a (remove-list x y))))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((remove-list x y)))))

(defthm remove-list-remove-reduction-1
  (implies
   (not (memberp a y))
   (list::equiv (remove-list (remove a x) y)
                (remove-list x y))))

(defthm remove-list-remove-reduction-1-alt
  (implies
   (not (memberp a y))
   (equal (remove-list (remove a x) y)
          (remove-list x y))))

(defthm remove-list-remove-reduction-2
  (implies
   (memberp a x)
   (equal (remove-list x (remove a y))
          (remove-list x y))))

(defthm subset-remove-list
  (list::subsetp (remove-list y x) x)
  :rule-classes ((:forward-chaining :trigger-terms ((remove-list y x)))))

;; 

(defthm remove-list-superset-reduction
  (implies
   (subsetp x y)
   (list::equiv (remove-list y x)
                nil)))

;;
;; Is this what we want to do? 
;;

(defthm subsetp-cons-2
  (equal (subsetp x (cons a y))
         (subsetp (remove a x) y)))

(local
 (defthm memberp-append-fwd
   (implies
    (memberp a (append x y))
    (or (memberp a x)
        (memberp a y)))
   :rule-classes (:forward-chaining)))

(defthmd subsetp-append-2
  (equal (subsetp x (append y z))
         (and (subsetp (remove-list y x) z)
              (subsetp (remove-list z x) y))))

(defthm subsetp-remove
  (subsetp (remove a x) x)
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((remove a x)))))

(defthm subsetp-remove-list
  (subsetp (remove-list a x) x)
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((remove-list a x)))))

(defthm superset-remove-list-id
  (equiv (remove-list x x) nil))

(defthm remove-list-remove-definition
  (equal (remove-list x y)
	 (if (consp x)
	     (remove (car x) (remove-list (cdr x) y))
	   (fix y)))
  :rule-classes (:definition))

(in-theory (disable remove-list-remove-definition))
