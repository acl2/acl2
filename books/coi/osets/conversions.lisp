#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
(in-package "SET")

(include-book "sets")
(include-book "set" :dir :lists) ;is this okay?

;;This stuff is taken from set-order.lisp.

;;
;; Some simple conversion functions between lists and sets.
;;

(defun set::2list (set)
  (declare (type (satisfies setp) set))
  (if (empty set) nil
    (cons (head set)
          (set::2list (tail set)))))

(defthm true-listp-2list
  (true-listp (set::2list set)))

(defun list::2set (list)
  (declare (type t list))
  (if (consp list)
      (insert (car list)
              (list::2set (cdr list)))
    nil))

(defthm setp-2set
  (setp (list::2set list)))


;new stuff

(defthm car-of-2LIST
  (equal (CAR (SET::|2LIST| set))
         (if (set::empty set)
             nil
           (set::head set))))

(defthm cdr-of-2list
  (equal (CDR (SET::|2LIST| set))
         (if (set::empty set)
             nil
           (SET::|2LIST| (set::tail set))))
  :hints (("Goal" :in-theory (enable SET::|2LIST|))))

(defthm consp-of-2list
  (equal (CONSP (SET::|2LIST| set))
         (not (set::empty set))))


;expensive?
;move
(defthm sfix-when-not-setp
  (implies (not (setp s)) 
           (equal (sfix s)
                  nil))
  :hints (("Goal" :in-theory (enable sfix))))

;bzo do the other inverse?
(defthm 2set-of-2list
  (equal (list::2set (2list s))
         (sfix s))
  :hints (("Goal" :in-theory (enable set::empty))))


;where should this go?
(defthm in-of-2set
  (equal (set::in a (list::2set lst))
         (list::memberp a lst)))

(defthm memberp-of-2list
  (equal (list::memberp a (2list set))
         (set::in a set)))

(defthm 2set-rewrap
  (equal (set::insert (car lst) (list::2set (cdr lst)))
         (if (consp lst)
             (list::2set lst)
           (set::insert nil (set::emptyset))
           )))

(in-theory (disable LIST::2set)) 

(theory-invariant (incompatible (:rewrite 2set-rewrap) (:definition LIST::2set)))

(defthm 2set-of-cons
  (equal (list::2set (cons a x))
         (set::insert a (list::2set x)))
  :hints (("Goal" :in-theory (e/d (list::2set) (set::2set-rewrap)))))

(defcong list::setequiv equal (list::2set list) 1)

(defthm remove-2list
  (list::setequiv (list::remove a (2list set))
                  (2list (delete a set))))

(defthm delete-2set
  (equal (delete a (list::2set list))
         (list::2set (list::remove a list))))

(defthm empty-2set
  (equal (empty (list::2set list))
         (not (consp list)))
  :hints (("Goal" :in-theory (e/d (list::2set)
                                  (|2SET-REWRAP|)))))

(defthm consp-2list
  (equal (consp (2list set))
         (not (empty set))))

