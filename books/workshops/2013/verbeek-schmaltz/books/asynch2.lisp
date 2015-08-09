#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "ordinals/lexicographic-ordering" :dir :system)

;; Moore's seq macro
(defmacro seq (stobj &rest rst)
  (cond ((endp rst) stobj)
        ((endp (cdr rst)) (car rst))
        (t `(let ((,stobj ,(car rst)))
             (seq ,stobj ,@(cdr rst))))))
;; Remove all elements in x from y, then return y
(defun remove-list (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (if (endp x)
    y
    (remove-equal (car x) (remove-list (cdr x) y))))
;; Returns t iff all elements in x are lists with length >= n
(defun A-len->= (x n)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))))
  (if (endp x)
    t
    (and (>= (len (car x)) n)
         (A-len->= (cdr x) n))))
;; the strip-cars function
(defun cars (x)
  (declare (xargs :guard (and (true-listp x)
                              (A-len->= x 1))))
  (if (endp x)
    nil
    (cons (caar x) (cars (cdr x)))))
;; Returns t iff all elements are non-empty lists
(defun A-cons (a x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
    nil
    (cons (cons a (car x))
          (A-cons a (cdr x)))))
;; Returns the powerset if the given set
(defun powerset (s)
  (declare (xargs :guard (true-listp s)))
  (cond ((endp s)
         '(nil))
        (t
         (append (powerset (cdr s))
                 (A-cons (car s) (powerset (cdr s)))))))
;; Returns t iff x and y are disjoint
(defun not-in (x y)
  (if (endp x)
    t
    (and (not (member-equal (car x) y))
         (not-in (cdr x) y))))
;; Returns all the second element, i.e., the second projection
(defun cadrs (x)
  (declare (xargs :guard (and (true-listp x)
                              (A-len->= x 2))))
  (if (endp x)
    nil
    (cons (cadar x) (cadrs (cdr x)))))
;; Returns the list of elements after the last occurence of a
;; E.g.: (equals (skip-to-last '(1 2 3 4 1 2 3 4) 2) '(3 4))
(defun skip-to-last (x a)
  (cond ((endp x)
         nil)
        ((member-equal a x)
         (skip-to-last (cdr x) a))
        (t
         x)))
;; Returns t iff all elements in x are true-lists
(defun A-true-listp (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
    t
    (and (true-listp (car x))
         (A-true-listp (cdr x)))))
;; Returns the nth projection of x
;; E.g.: (equals (proj 1 '((0 1 2 3) (0 1 2) (0 1 2 3 4))) '(1 1 1))
(defun proj (n x)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (A-true-listp x))))
  (if (endp x)
    nil
    (cons (nth n (car x)) (proj n (cdr x)))))
;; Transforms the given object to a true-list
(defun fix-true-listp (x)
  (declare (xargs :guard t))
  (cond ((equal x nil)
         nil)
        ((atom x)
         nil)
        ((endp x)
         nil)
        (t
         (cons (car x) (fix-true-listp (cdr x))))))
;; Given a path from a to b, remove all cycles in the path.
;; This always yields another path from a to b, but without duplicates (see theorem no-dups-find-simple-path)
(defun find-simple-path (path)
  (cond ((endp path)
         nil)
        ((equal (car (last path)) (car path))
         ;; If the entire path is a cycle, return a path containing only the current object
         ;; This removes the cycle
         (list (car path)))
        (t
         ;; Otherwise find the last occurence of the current object and from there search a simple path
         (cons (car path) (find-simple-path (skip-to-last path (car path)))))))
;; Returns the union of all lists in x
(defun uni (x)
  (if (endp x)
    nil
    (append (car x) (uni (cdr x)))))



;; Some trivial heorems
(defthm lem-remove-equal-<
  (implies (case-split (member-equal a x))
           (< (len (remove-equal a x))
              (len x))))
(defthm member-remove-list
  (iff (member-equal a (remove-list x y))
       (and (member-equal a y)
            (not (member-equal a x)))))
(defthm last-append
  (equal (car (last (append x y)))
         (cond ((consp y)
                (car (last y)))
               (t
                (car (last x))))))
(defthm car-append
  (equal (car (append x y))
         (cond ((consp x)
                (car x))
               (t
                (car y)))))
(defthm member-append
  (iff (member-equal a (append x y))
       (or (member-equal a x)
           (member-equal a y))))

(defthm member-remove
  (iff (member-equal a (remove-equal b x))
       (if (equal a b)
         nil
         (member-equal a x))))




(defthm no-dups-append
  (equal (no-duplicatesp-equal (append x y))
         (and (no-duplicatesp-equal x)
              (no-duplicatesp-equal y)
              (not-in x y))))
(defthm not-in-singleton
  (equal (not-in x (list a))
         (not (member-equal a x))))
(defthm subsetp-expand
  (implies (subsetp x y)
           (subsetp x (cons a y))))
(defthm subsetp-reflexive
  (subsetp x x))



(defthm subsetp-append-l
  (equal (subsetp (append x y) z)
         (and (subsetp x z)
              (subsetp y z))))
(defthm subsetp-append-r-1
  (implies (subsetp x y)
           (subsetp x (append y z))))
(defthm subsetp-append-r-2
  (implies (subsetp x z)
           (subsetp x (append y z))))
(defthm not-in-cons-r
  (equal (not-in x (cons a y))
         (and (not-in x y)
              (not (member-equal a x)))))
(defthm not-in-nil
  (not-in x nil))


(defthm last-is-member
  (iff (member-equal (car (last x)) x)
       (consp x)))

(defthm last-skipt-to-last
  (equal (car (last (skip-to-last x a)))
         (if (equal (car (last x)) a)
           nil
           (car (last x)))))
(defthm member-skip-to-last
  (implies (member-equal a (skip-to-last x b))
           (member-equal a x)))
(defthm not-member-skip-to-last
  (not (member-equal a (skip-to-last x a))))


(defthm spec-of-A-len->=
  (implies (and (A-len->= x n)
                (member-equal a x))
           (>= (len a) n))
  :rule-classes :linear)
(defthm spec-of-proj
  (implies (member-equal a x)
           (member-equal (nth n a)
                         (proj n x))))

(defthm spec-of-A-true-listp
  (implies (and (A-true-listp x)
                (member-equal a x))
           (true-listp a)))
(defthm member-key-->member-assoc
  (implies (member-equal a (cars x))
           (member-equal (assoc a x) x)))
(defthm spec-of-A-len->=1
  (implies (and (A-len->= x 1)
                (member-equal a x))
           (consp a)))
(defthm member-nth-of-proj
  (implies (member-equal a x)
           (member-equal (nth n a) (proj n x))))
(defthm len-remove-equal
  (<= (len (remove-equal a x))
      (len x))
  :rule-classes :linear)

(defthm spec-of-eqlable-listp
  (implies (and (eqlable-listp x)
                (member-equal a x))
           (eqlablep a)))

(defthm car-find-simple-path
  (equal (car (find-simple-path path))
         (car path)))
(defthm consp-find-simple-path
  (iff (consp (find-simple-path path))
       (consp path)))
(defthm last-find-simple-path
  (equal (car (last (find-simple-path path)))
         (car (last path))))
(defthm member-find-simple-path
  (implies (member-equal a (find-simple-path path))
           (member-equal a path)))
(defthm no-dups-find-simple-path
  (no-duplicatesp-equal (find-simple-path path))
  :hints (("Subgoal *1/3" :use (:instance member-find-simple-path
                                (a (car path))
                                (path (skip-to-last path (car path)))))))#|ACL2s-ToDo-Line|#

